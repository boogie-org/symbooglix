using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;


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

        Expr ReadMap(Variable mapVariable, IList<Expr> indicies);
        void WriteMap(Variable mapVariable, IList<Expr> indicies, Expr value);
        void MapCopy(Variable dest, Variable src, IVariableStore srcStore);
    }

    public class SimpleVariableStore : IVariableStore
    {
        private Dictionary<Variable, Expr> BasicTypeVariableStore;
        private Dictionary<Variable, MapProxy> MapTypeVariableStore;

        public SimpleVariableStore()
        {
            BasicTypeVariableStore = new Dictionary<Variable, Expr>();
            MapTypeVariableStore = new Dictionary<Variable, MapProxy>();
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
                MapTypeVariableStore.Add(v, new MapProxy(initialValue));
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
            that.BasicTypeVariableStore = new Dictionary<Variable, Expr>(this.BasicTypeVariableStore);

            // Clone the MapProxies
            that.MapTypeVariableStore = new Dictionary<Variable, MapProxy>(this.MapTypeVariableStore.Count);
            foreach (var pair in this.MapTypeVariableStore)
            {
                that.MapTypeVariableStore.Add(pair.Key, pair.Value.Clone());
            }
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
                var mapProxyClone = srcInternalsMaps[src].Clone();
                this.MapTypeVariableStore[dest] = mapProxyClone;
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
                    MapTypeVariableStore[v].Write(value);
                }
                else
                    BasicTypeVariableStore[v] = value;
            }
        }
    }
}

