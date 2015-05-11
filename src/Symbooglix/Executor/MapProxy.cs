using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Boogie;
using BPLType = Microsoft.Boogie.Type;
using System.Linq;
using System.Collections.Immutable;

namespace Symbooglix
{
    public class MapProxy
    {
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

        public MapProxy(Expr initialValue)
        {
            this.MapType = initialValue.Type;

            if (!this.MapType.IsMap)
                throw new ArgumentException("Must be map type");

            this.ExpressionRepresentation = initialValue;

            // Precompute the number of indicies required to perform a read or write
            NumberOfIndices = ComputeIndicesRequireToDirectlyIndex(this.MapType);

            // Setup StoresAtConcreteIndicies storage
            var initialMap = ImmutableDictionary<MapKey,Expr>.Empty;
            StoresAtConcreteIndices = initialMap.ToBuilder();
            UnflushedStores = initialMap.ToBuilder();
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

        private void FlushUnflushedStores()
        {
            foreach (var mapping in UnflushedStores)
            {
                DirectWrite(mapping.Key.Indices, mapping.Value);
            }
            UnflushedStores.Clear();
            Debug.Assert(UnflushedStores.Count == 0);
        }

        private void DropConcreteStores()
        {
            StoresAtConcreteIndices.Clear();
            Debug.Assert(StoresAtConcreteIndices.Count == 0);
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

            // Reading from a location in the map we don't have stored
            // so we need to flush all stores and return the full expression.
            // Note we aren't doing a write so we can keep the stores however
            // (by not calling DropConcreteStores())
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

        // Might avoid map store flushing
        public void WriteMapAt(IList<Expr> indices, Expr value)
        {
            TypeCheckIndices(indices);

            if (AreConcrete(indices))
            {
                // Don't create store expressions, just store directly which can be retrieved by
                // ReadMapAt()
                var mapKey = new MapKey(indices);
                StoresAtConcreteIndices[mapKey] = value;
                UnflushedStores[mapKey] = value;
                return;
            }

            // Writing to a symbolic index. We need to flush all stores, empty the stores
            // then store the new value
            FlushUnflushedStores();
            DropConcreteStores(); // The stores are no longer valid so drop them
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

            DropConcreteStores(); // The stores are no longer valid so drop them all
            UnflushedStores.Clear(); // We don't want unflushed stores to ever get flushed onto the new expression
            Debug.Assert(UnflushedStores.Count == 0);
            Debug.Assert(StoresAtConcreteIndices.Count == 0);
            ExpressionRepresentation = newValue;
        }

        public MapProxy Clone()
        {
            var other = (MapProxy) this.MemberwiseClone();

            // This should be a very lightweight copy
            var copySACI = StoresAtConcreteIndices.ToImmutable();
            other.StoresAtConcreteIndices = copySACI.ToBuilder();

            var copyUFS = UnflushedStores.ToImmutable();
            other.UnflushedStores = copyUFS.ToBuilder();

            return other;
        }
    }
}

