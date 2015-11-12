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
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;
using System.Collections.Immutable;
using System.Numerics;
using System.Diagnostics;


namespace Symbooglix
{
    public interface IVariableStore : IEnumerable<KeyValuePair<Variable,Expr>>
    {
        // FIXME: Change name
        void Add(Variable v, Expr initialValue);
        // FIXME: Change name
        bool ContainsKey(Variable v);
        IEnumerable<Variable> Keys { get; }
        IVariableStore Clone();

        int Count { get; }

        // Direct Read and Write.
        // Avoid using this for maps if possible
        // TODO: Remove this. This is here to make refactoring easier but eventually
        Expr this [Variable v]
        {
            get;
            set;
        }

        // Note here that the indicies are ordered as they would be used
        // to perform an access syntactically in Boogie (i.e. left to right)
        // e.g. if the access is m[0][1] then the indicies should be {0, 1}.
        Expr ReadMap(Variable mapVariable, IList<Expr> indicies);
        void WriteMap(Variable mapVariable, IList<Expr> indicies, Expr value);
        void MapCopy(Variable dest, Variable src, IVariableStore srcStore);
    }

    public class SimpleVariableStore : IVariableStore
    {
        private ImmutableDictionary<Variable, Expr>.Builder BasicTypeVariableStore;
        private ImmutableDictionary<Variable, MapProxy>.Builder MapTypeVariableStore;
        private BigInteger CopyOnWriteKey; // Epoch counter for MapProxy objects

        public SimpleVariableStore()
        {
            var emptyDict = ImmutableDictionary<Variable, Expr>.Empty;
            BasicTypeVariableStore = emptyDict.ToBuilder();
            var emptyMPDict = ImmutableDictionary<Variable, MapProxy>.Empty;
            MapTypeVariableStore = emptyMPDict.ToBuilder();
            CopyOnWriteKey = new BigInteger(0);
        }

        private bool IsMapVariable(Variable v)
        {
            return v.TypedIdent.Type.IsMap;
        }

        private void TypeCheckDirectAssign(Variable v, Expr initialValue)
        {
            if (initialValue == null)
                throw new ArgumentException("assignment cannot be null");

            if (!v.TypedIdent.Type.Equals(initialValue.Type))
                throw new ExprTypeCheckException("Variable type and expression type do not match");
        }

        public void Add(Variable v, Expr initialValue)
        {
            TypeCheckDirectAssign(v, initialValue);

            if (IsMapVariable(v))
            {
                var mp = new MapProxy(initialValue, this.CopyOnWriteKey);
                MapTypeVariableStore.Add(v, mp);
            }
            else
                BasicTypeVariableStore.Add(v, initialValue);
        }

        public bool ContainsKey(Variable v)
        {
            if (IsMapVariable(v))
                return MapTypeVariableStore.ContainsKey(v);
            else
                return BasicTypeVariableStore.ContainsKey(v);
        }

        public IEnumerable<Variable> Keys
        {
            get
            {
                return BasicTypeVariableStore.Keys.Concat(MapTypeVariableStore.Keys);
            }
        }

        public IVariableStore Clone()
        {
            var that = (SimpleVariableStore) this.MemberwiseClone();

            // Expressions are immutable so no cloning is necessary.
            var copyBasicTypeVariableStore = this.BasicTypeVariableStore.ToImmutable();
            that.BasicTypeVariableStore = copyBasicTypeVariableStore.ToBuilder();

            var copyMapTypeVariableStore = this.MapTypeVariableStore.ToImmutable();
            that.MapTypeVariableStore = copyMapTypeVariableStore.ToBuilder();

            // Note we delay cloning the MapStore objects until an attempt is made to write to one of them.
            // This requires that we be must be very careful and make sure that any public interface that allows
            // writing to the MapProxy triggers a clone of the MapStore.
            //
            // Now that a copy has been performed we need to increment to CopyOnWrite key of this and that
            // so any MapStore objects we created before cloning will be copied if an attempt is
            // made to write to them (using one of the IVariable interfaces) from this or that.
            ++this.CopyOnWriteKey;
            ++that.CopyOnWriteKey;

            return that;
        }

        public Expr ReadMap(Variable mapVariable, IList<Expr> indicies)
        {
            if (!IsMapVariable(mapVariable))
                throw new ArgumentException("expected map variable");

            MapProxy mapProxyObj = null;
            MapTypeVariableStore.TryGetValue(mapVariable, out mapProxyObj);

            if (mapProxyObj == null)
                throw new KeyNotFoundException("map variable not in store");

            return mapProxyObj.ReadMapAt(indicies);
        }

        public void WriteMap(Variable mapVariable, IList<Expr> indicies, Expr value)
        {
            if (!IsMapVariable(mapVariable))
                throw new ArgumentException("expected map variable");

            MapProxy mapProxyObj = null;
            MapTypeVariableStore.TryGetValue(mapVariable, out mapProxyObj);

            if (mapProxyObj == null)
                throw new KeyNotFoundException("map variable not in store");

            if (mapProxyObj.CopyOnWriteOwnerKey != this.CopyOnWriteKey)
            {
                // Perform copy
                var newMp = mapProxyObj.Clone(this.CopyOnWriteKey);
                MapTypeVariableStore[mapVariable] = newMp;
                mapProxyObj = newMp;
            }
            Debug.Assert(mapProxyObj.CopyOnWriteOwnerKey == this.CopyOnWriteKey);
            mapProxyObj.WriteMapAt(indicies, value);
        }

        public void MapCopy(Variable dest, Variable src, IVariableStore srcStore)
        {
            if (!IsMapVariable(dest))
                throw new ArgumentException("dest is not a map variable");

            if (!IsMapVariable(src))
                throw new ArgumentException("src is not a map variable");

            if (!dest.TypedIdent.Type.Equals(src.TypedIdent.Type))
                throw new ArgumentException("src and dest type do not match");

            if (!MapTypeVariableStore.ContainsKey(dest))
                throw new ArgumentException("destination variable not in store");

            if (!srcStore.ContainsKey(src))
                throw new ArgumentException("src is not in srcStore");

            if (Object.ReferenceEquals(dest, src))
            {
                // Copying to self shouldn't do anything.
                return;
            }

            if (srcStore is SimpleVariableStore)
            {
                // We can peak into the internals
                var srcInternalsMaps = ( srcStore as SimpleVariableStore ).MapTypeVariableStore;

                // Clone the internal representation of the map to avoid causing any flushes
                var mapProxyClone = srcInternalsMaps[src].Clone(this.CopyOnWriteKey);
                this.MapTypeVariableStore[dest] = mapProxyClone;
                Debug.Assert(this.MapTypeVariableStore[dest].CopyOnWriteOwnerKey == this.CopyOnWriteKey);
            }
            else
            {
                // Do potentially the expensive way (may trigger a flush of map stores)
                this[dest] = srcStore[src];
            }
        }

        // Warning: This will trigger map store flushes
        public IEnumerator<KeyValuePair<Variable, Expr>> GetEnumerator()
        {
            foreach (var pair in BasicTypeVariableStore)
                yield return pair;

            foreach (var pair in MapTypeVariableStore)
            {
                var flushedExpr = pair.Value.Read();
                yield return new KeyValuePair<Variable, Expr>(pair.Key, flushedExpr);
            }
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
        {
            return GetEnumerator();
        }

        public int Count
        {
            get
            {
                return BasicTypeVariableStore.Count + MapTypeVariableStore.Count;
            }
        }

        // Avoid using this for maps. It will force map store flushes
        public Expr this[Variable v]
        {
            get
            {
                if (IsMapVariable(v))
                {
                    return MapTypeVariableStore[v].Read();
                }
                else
                    return BasicTypeVariableStore[v];
            }
            set
            {
                TypeCheckDirectAssign(v, value);
                if (IsMapVariable(v))
                {
                    if (MapTypeVariableStore.ContainsKey(v))
                    {
                        var mp = MapTypeVariableStore[v];
                        if (mp.CopyOnWriteOwnerKey != this.CopyOnWriteKey)
                        {
                            // Make copy
                            var newMp = mp.Clone(this.CopyOnWriteKey);
                            MapTypeVariableStore[v] = newMp;
                        }
                        MapTypeVariableStore[v].Write(value);
                    }
                    else
                    {
                        MapTypeVariableStore[v] = new MapProxy(value, this.CopyOnWriteKey);
                    }
                    Debug.Assert(MapTypeVariableStore[v].CopyOnWriteOwnerKey == this.CopyOnWriteKey);
                }
                else
                    BasicTypeVariableStore[v] = value;
            }
        }
    }
}

