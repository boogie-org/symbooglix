//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Boogie;
using BPLType = Microsoft.Boogie.Type;
using System.Linq;
using System.Collections.Immutable;
using System.Numerics;

namespace Symbooglix
{
    public class MapProxy
    {
        public BigInteger CopyOnWriteOwnerKey {get; private set;}
        private Expr ExpressionRepresentation;
        BPLType MapType;
        public readonly int NumberOfIndices;
        // FIXME: Make this user specifiable
        private static IExprBuilder Builder = new ConstantFoldingExprBuilder(new SimpleExprBuilder(/*immutable=*/ true));

        class MapKey
        {
            public List<Expr> Indices;

            public MapKey(IList<Expr> indices)
            {
                if (indices.Count == 0)
                    throw new ArgumentException("Must have at least one index expression");

                this.Indices = new List<Expr>(indices.Count);
                foreach (var index in indices)
                    this.Indices.Add(index);
            }

            public override bool Equals(object obj)
            {
                if (obj == null)
                    return false;

                if (!( obj is MapKey ))
                    return false;

                var other = (MapKey) obj;

                return this.Indices.SequenceEqual(other.Indices);
            }

            public override int GetHashCode()
            {
                int h = 0;
                foreach (var arg in Indices) {
                    h = (97*h) + arg.GetHashCode();
                }
                return h;
            }
        }

        // For cheap Copy-on-write
        ImmutableDictionary<MapKey,Expr>.Builder StoresAtConcreteIndices; // Stores at concrete locations that can be quickly looked up
        ImmutableDictionary<MapKey,Expr>.Builder UnflushedStores; // Stores not yet flushed to the ExpressionRepresentation

        // Stores at symbolic indices that we statically know cannot alias
        ImmutableDictionary<MapKey,Expr>.Builder StoresAtSymbolicNonAliasingIndices;
        Variable SymVariable ; // FIXME: Type should be SymbolicVariable

        public MapProxy(Expr initialValue, BigInteger copyOnWriteOwnerKey)
        {
            this.MapType = initialValue.Type;
            this.CopyOnWriteOwnerKey = copyOnWriteOwnerKey;

            if (!this.MapType.IsMap)
                throw new ArgumentException("Must be map type");

            this.ExpressionRepresentation = initialValue;

            // Precompute the number of indicies required to perform a read or write
            NumberOfIndices = ComputeIndicesRequireToDirectlyIndex(this.MapType);

            // Setup StoresAtConcreteIndicies storage
            var initialMap = ImmutableDictionary<MapKey,Expr>.Empty;
            StoresAtConcreteIndices = initialMap.ToBuilder();
            UnflushedStores = initialMap.ToBuilder();
            StoresAtSymbolicNonAliasingIndices = initialMap.ToBuilder();
            SymVariable = null;
        }

        public static int ComputeIndicesRequireToDirectlyIndex(BPLType mapType)
        {
            if (!mapType.IsMap)
                throw new ArgumentException("argument must be a map type");

            int numberOfIndices = 0;
            BPLType coDomainTy = mapType;
            do
            {
                var asMapTy = coDomainTy.AsMap;
                numberOfIndices += asMapTy.Arguments.Count;
                coDomainTy = asMapTy.Result;
            } while (coDomainTy.IsMap);
            return numberOfIndices;
        }

        // We should probably lock other places too
        // but this one is especially risky because multiple IVariableStores may have
        // a handle to us and trigger flushing simultaneously. This must happen sequentially
        private void FlushUnflushedStores()
        {
            lock (UnflushedStores)
            {
                foreach (var mapping in UnflushedStores)
                {
                    DirectWrite(mapping.Key.Indices, mapping.Value);
                }
                UnflushedStores.Clear();
                Debug.Assert(UnflushedStores.Count == 0);
            }
        }

        private void DropConcreteStores()
        {
            StoresAtConcreteIndices.Clear();
            Debug.Assert(StoresAtConcreteIndices.Count == 0);
        }

        private void DropSymbolicNonAliasingStores()
        {
            StoresAtSymbolicNonAliasingIndices.Clear();
            Debug.Assert(StoresAtSymbolicNonAliasingIndices.Count == 0);
            SymVariable = null;
        }

        private bool AreConcrete(IList<Expr> indices)
        {
            foreach (var index in indices)
            {
                var asLiteral = ExprUtil.AsLiteral(index);
                if (asLiteral == null)
                    return false;
            }
            return true;
        }

        private bool AreKnownSymbolicNonAliasingIndices(IList<Expr> indices)
        {
            if (StoresAtSymbolicNonAliasingIndices.Count == 0)
                return false;

            if (StoresAtSymbolicNonAliasingIndices.ContainsKey(new MapKey(indices)))
                return true;

            return false;
        }

        // Only returns true if the indices definitely only alias up to one indice stored
        // in StoresAtSymbolicNonAliasingIndices. i.e.
        //
        // returns true iff
        //
        // the indices do not alias anything in StoresAtSymbolicNonAliasingIndices
        // OR
        // the indices alias a single element in StoresAtSymbolicNonAliasingIndices
        // which ok because this tells us which element to overwrite.
        //
        // Note that if this method returns false it means that the indices "might" alias.
        private bool AliasesZeroOrOneSymbolicNonAliasingIndices(IList<Expr> indices)
        {
            if (indices.Count > 1)
            {
                // Our alias analysis is very primitive and we only allow a single index
                return false;
            }

            var indexExpr = indices[0];
            // Analysis: We consider the follow expressions to not alias
            // <sym_var>
            // <constant> + <sym_var>
            //
            // Note sym_var must be the same


            // Try single variable
            var asId = ExprUtil.AsIdentifer(indexExpr);
            if (asId != null)
            {
                if (SymVariable == null)
                {
                    // We haven't picked a variable for use in our non aliasing symbolci expressions yet
                    // use this one
                    Debug.Assert(StoresAtSymbolicNonAliasingIndices.Count == 0);
                    SymVariable = asId.Decl;
                    return true;
                }
                else
                {
                    // We have an existing symbolic variable that we are using
                    if (SymVariable.Equals(asId.Decl))
                    {
                        return true;
                    }
                    return false;
                }
            }

            // We are relying on the expression simplification of the expression builder to always
            // but the constant on the left child
            // <constant> + <sym_var>
            var asAdd = ExprUtil.AsAdd(indexExpr);
            if (asAdd != null)
            {
                var lhsAsLit = ExprUtil.AsLiteral(asAdd.Args[0]);
                if (lhsAsLit != null)
                {
                    var rhsAsId = ExprUtil.AsIdentifer(asAdd.Args[1]);
                    if (rhsAsId != null)
                    {
                        if (SymVariable == null)
                        {
                            // We haven't picked a variable for use in our non aliasing symbolci expressions yet
                            // use this one
                            Debug.Assert(StoresAtSymbolicNonAliasingIndices.Count == 0);
                            SymVariable = rhsAsId.Decl;
                            return true;
                        }
                        else
                        {
                            // We have an existing symbolic variable that we are using
                            if (SymVariable.Equals(rhsAsId.Decl))
                            {
                                return true;
                            }
                            return false;
                        }
                    }
                }
            }

            // The indicies might alias something we already have stored.
            return false;
        }

        // Might avoid map store flushing
        public Expr ReadMapAt(IList<Expr> indices)
        {
            TypeCheckIndices(indices);

            if (AreConcrete(indices))
            {
                Expr storedValue = null;
                var mapKey = new MapKey(indices);
                StoresAtConcreteIndices.TryGetValue(mapKey, out storedValue);

                if (storedValue != null)
                {
                    // We have a hit! Return the stored value
                    return storedValue;
                }
            }
            else if (AreKnownSymbolicNonAliasingIndices(indices))
            {
                // We have this symbolic location already stored
                var mapKey = new MapKey(indices);
                return StoresAtSymbolicNonAliasingIndices[mapKey];
            }

            // Reading from a location in the map we don't have stored
            // so we need to flush all stores and return the full expression.
            // Note we aren't doing a write so we can keep the stores in
            // StoresAtConcreteIndices and StoresAtSymbolicNonAliasingIndices
            // for future look up.
            // (by not calling DropConcreteStores() and DropSymbolicNonAliasingStores())
            FlushUnflushedStores();

            // Build map selects to access the location symbolically
            var groupedIndices = GroupIndices(indices);
            var result = ExpressionRepresentation;
            for (int index = 0; index < groupedIndices.Count; ++index)
            {
                result = Builder.MapSelect(result, groupedIndices[index].ToArray());
            }
            return result;
        }



        private enum CurrentMode
        {
            NONE,
            CONCRETE_STORE,
            SYMBOLIC_NON_ALIASING_STORE
        }

        private CurrentMode GetCurrentMode()
        {
            if (StoresAtConcreteIndices.Count == 0 && StoresAtSymbolicNonAliasingIndices.Count == 0)
                return CurrentMode.NONE;

            if (StoresAtConcreteIndices.Count > 0 && StoresAtSymbolicNonAliasingIndices.Count > 0)
                throw new InvalidOperationException("StoresAtConcreteIndices and StoresAtSymbolicNonAliasingIndices cannot both be active at the same time");

            if (StoresAtConcreteIndices.Count > 0)
                return CurrentMode.CONCRETE_STORE;

            if (StoresAtSymbolicNonAliasingIndices.Count > 0)
                return CurrentMode.SYMBOLIC_NON_ALIASING_STORE;

            throw new InvalidOperationException("Unreachable");
        }

        // Might avoid map store flushing
        public void WriteMapAt(IList<Expr> indices, Expr value)
        {
            TypeCheckIndices(indices);

            if (AreConcrete(indices))
            {
                if (GetCurrentMode() == CurrentMode.SYMBOLIC_NON_ALIASING_STORE)
                {
                    // Can't be in both modes simultaneously so flush any unflushed stores
                    // left from StoresAtSymbolicNonAliasingIndices
                    // FIXME: We could optimise to avoid doing this but we don't right now
                    // because we could end up with a mix of concrete and symbolic indices
                    // in the store and we might not flush them in the right order
                    FlushUnflushedStores();

                    // Drop the stores they won't be valid anymore
                    DropSymbolicNonAliasingStores();
                    Debug.Assert(GetCurrentMode() == CurrentMode.NONE);
                }

                // Don't create map store expressions, just store directly which can be retrieved by
                // ReadMapAt()
                var mapKey = new MapKey(indices);
                StoresAtConcreteIndices[mapKey] = value;
                UnflushedStores[mapKey] = value;
                Debug.Assert(GetCurrentMode() == CurrentMode.CONCRETE_STORE);
                return;
            }
            else if (AliasesZeroOrOneSymbolicNonAliasingIndices(indices))
            {
                if (GetCurrentMode() == CurrentMode.CONCRETE_STORE)
                {
                    // Can't be in both modes simultaneously so flush any unflushed stores
                    // left from StoresAtConcreteIndices
                    // FIXME: We could optimise to avoid doing this but we don't right now
                    // because we could end up with a mix of concrete and symbolic indices
                    // in the store and we might not flush them in the right order
                    FlushUnflushedStores();

                    // Drop concrete stores, we can't have them around simultaneously
                    DropConcreteStores();
                }

                // Don't create map store expression, just store directly which can be retrieved
                // by ReadMapAt()
                var mapKey = new MapKey(indices);
                StoresAtSymbolicNonAliasingIndices[mapKey] = value;
                UnflushedStores[mapKey] = value;
                Debug.Assert(GetCurrentMode() == CurrentMode.SYMBOLIC_NON_ALIASING_STORE);
                return;
            }

            // Writing to a symbolic index. We need to flush all unflushed stores, drop the stores
            // and then store the new value
            FlushUnflushedStores();
            DropConcreteStores(); // The stores are no longer valid so drop them
            DropSymbolicNonAliasingStores(); // The stores are no longer valid so drop them
            DirectWrite(indices, value);
        }

        private void TypeCheckIndices(IList<Expr> indices)
        {
            // We implicitly assume that the client will index all the way into the variable and not partially
            if (indices.Count != NumberOfIndices)
                throw new ExprTypeCheckException("Incorrect number of indices. Expected " +
                                                 NumberOfIndices.ToString() + " but received " +
                                                 indices.Count);
            int index = 0;
            BPLType currentType = this.MapType;
            do
            {
                var asMapType = currentType.AsMap;
                foreach (var indexType in asMapType.Arguments)
                {
                    if (!indexType.Equals(indices[index].Type))
                        throw new ExprTypeCheckException("Type mismatch at index " +
                                                         index.ToString() + " expected type " +
                                                         indexType.ToString() + " but was type " +
                                                         indices[index].Type);
                    ++index;
                }
                currentType = asMapType.Result;
            } while (currentType.IsMap);
        }

        private List<List<Expr>> GroupIndices(IList<Expr> indices)
        {

            // Build indices grouping, e.g. for a map variable m
            // m[5,4][3]  is { {5,4}, {3} }
            // m[5][4] is { {5}, {4} }
            List<List<Expr>> groupedIndices = new List<List<Expr>>();

            int index = 0;
            List<Expr> currentList = null;
            BPLType currentType = this.MapType;
            Debug.Assert(currentType.IsMap);
            // Walk the type to build up the grouping
            do
            {
                var asMapType = currentType.AsMap;
                currentList = new List<Expr>(asMapType.MapArity);
                for (int i=0; i < asMapType.MapArity; ++i)
                {
                    var theIndexExpr = indices[index];
                    if (!theIndexExpr.Type.Equals(asMapType.Arguments[i]))
                        throw new ExprTypeCheckException("During direct write the indicies");

                    currentList.Add(indices[index]);
                    ++index;
                }
                groupedIndices.Add(currentList);
                currentType = asMapType.Result;
            } while (currentType.IsMap);
            Debug.Assert(index == indices.Count);

            return groupedIndices;
        }

        private void DirectWrite(IList<Expr> indices, Expr value)
        {
            var groupedIndices = GroupIndices(indices);

            // Build the MapStores bottom up
            /* Example
             * var m:[int][int][int]bool;
             *
             * Assignment m[1][2][3] := false
             * has the following form as mapstore/mapselect expressions
             * m[ 1:= m[1][ 2:= m[1][2][3 := false]]]
             *
             * As a tree this looks like.
             * NOTE:
             * (mapstore <map to base store on> <index>... <value to store>)
             * (mapselect <map to read> <index>...)
             * <index> may repreat several times (this is why groupedIndices was computed)
             *
             *      mapstore
             *     /    |    \
             *   m      1     \
             *                 \
             *                  \
             *                 mapstore
             *                /    |     \
             *               /     2      \
             *           mapselect         \
             *          /     |             \
             *         m      1              \
             *                               mapstore
             *                             /     |   \
             *                     mapselect     3   false
             *                    /    |
             *             mapselect   2
             *            /   |
             *           m    1
             */
            Expr result = value;
            for (int groupIndex = groupedIndices.Count - 1; groupIndex >= 0; --groupIndex)
            {
                // Build the Mapselects necessary for map variables with nested maps
                Expr readFromMap = ExpressionRepresentation;
                for (int mapSelectIndex = 0; mapSelectIndex < groupIndex; ++mapSelectIndex)
                {
                    readFromMap = Builder.MapSelect(readFromMap, groupedIndices[mapSelectIndex].ToArray());
                }
                result = Builder.MapStore(readFromMap, result, groupedIndices[groupIndex].ToArray());
            }

            ExpressionRepresentation = result;
        }

        // Will force map store flush
        public Expr Read()
        {
            FlushUnflushedStores();
            return ExpressionRepresentation;
        }

        public void Write(Expr newValue)
        {
            if (!newValue.Type.Equals(this.MapType))
                throw new ArgumentException("newValue must have correct map type");

            // The stores are no longer valid so drop them all
            DropConcreteStores();
            DropSymbolicNonAliasingStores();

            UnflushedStores.Clear(); // We don't want unflushed stores to ever get flushed onto the new expression
            Debug.Assert(UnflushedStores.Count == 0);
            Debug.Assert(StoresAtConcreteIndices.Count == 0);
            ExpressionRepresentation = newValue;
            Debug.Assert(GetCurrentMode() == CurrentMode.NONE);
        }

        public MapProxy Clone(BigInteger newOwnerCopyOnWriteKey)
        {
            var other = (MapProxy) this.MemberwiseClone();

            // These should be a very lightweight copies
            var copySACI = StoresAtConcreteIndices.ToImmutable();
            other.StoresAtConcreteIndices = copySACI.ToBuilder();

            var copyUFS = UnflushedStores.ToImmutable();
            other.UnflushedStores = copyUFS.ToBuilder();

            var copySASNAI = StoresAtSymbolicNonAliasingIndices.ToImmutable();
            other.StoresAtSymbolicNonAliasingIndices = copySASNAI.ToBuilder();

            other.CopyOnWriteOwnerKey = newOwnerCopyOnWriteKey;
            return other;
        }
    }
}

