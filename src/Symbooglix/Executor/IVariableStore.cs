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
        Expr WriteMap(Variable mapVariable, IList<Expr> indicies, Expr value);
    }

    public class SimpleVariableStore : IVariableStore
    {
        private Dictionary<Variable, Expr> BasicTypeVariableStore;
        private Dictionary<Variable, Expr> MapTypeVariableStore;

        public SimpleVariableStore()
        {
            BasicTypeVariableStore = new Dictionary<Variable, Expr>();
            MapTypeVariableStore = new Dictionary<Variable, Expr>();
        }

        private bool IsMapVariable(Variable v)
        {
            return v.TypedIdent.Type.IsMap;
        }

        private void TypeCheckDirectAssign(Variable v, Expr initialValue)
        {
            // FIXME: This is necessary because the executor assigns nulls to locals
            // this bad and should be fixed
            if (initialValue == null)
                return;

            if (!v.TypedIdent.Type.Equals(initialValue.Type))
                throw new ExprTypeCheckException("Variable type and expression type do not match");
        }

        public void Add(Variable v, Expr initialValue)
        {
            TypeCheckDirectAssign(v, initialValue);

            if (IsMapVariable(v))
                MapTypeVariableStore.Add(v, initialValue);
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
            that.BasicTypeVariableStore = new Dictionary<Variable, Expr>(this.BasicTypeVariableStore);
            that.MapTypeVariableStore = new Dictionary<Variable, Expr>(this.MapTypeVariableStore);
            return that;
        }

        public Expr ReadMap(Variable mapVariable, IList<Expr> indicies)
        {
            throw new NotImplementedException();
        }

        public Expr WriteMap(Variable mapVariable, IList<Expr> indicies, Expr value)
        {
            throw new NotImplementedException();
        }

        public IEnumerator<KeyValuePair<Variable, Expr>> GetEnumerator()
        {
            foreach (var pair in BasicTypeVariableStore)
                yield return pair;

            foreach (var pair in MapTypeVariableStore)
                yield return pair;
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

        public Expr this[Variable v]
        {
            get
            {
                if (IsMapVariable(v))
                    return MapTypeVariableStore[v];
                else
                    return BasicTypeVariableStore[v];
            }
            set
            {
                TypeCheckDirectAssign(v, value);
                if (IsMapVariable(v))
                    MapTypeVariableStore[v] = value;
                else
                    BasicTypeVariableStore[v] = value;
            }
        }
    }
}

