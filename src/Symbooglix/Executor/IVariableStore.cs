using System;
using Microsoft.Boogie;
using System.Collections.Generic;


namespace Symbooglix
{
    public interface IVariableStore : IEnumerable<KeyValuePair<Variable,Expr>>
    {
        // FIXME: Change name
        void Add(Variable v, Expr initialValue);
        // FIXME: Change name
        bool ContainsKey(Variable v);
        Dictionary<Variable, Expr>.KeyCollection Keys { get; }
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
        private Dictionary<Variable, Expr> Store;

        public SimpleVariableStore()
        {
            Store = new Dictionary<Variable, Expr>();
        }

        public void Add(Variable v, Expr initialValue)
        {
            Store.Add(v, initialValue);
        }

        public bool ContainsKey(Variable v)
        {
            return Store.ContainsKey(v);
        }

        public Dictionary<Variable, Expr>.KeyCollection Keys
        {
            get
            {
                return Store.Keys;
            }
        }

        public IVariableStore Clone()
        {
            var that = (SimpleVariableStore) this.MemberwiseClone();
            that.Store = new Dictionary<Variable, Expr>(this.Store);
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
            return Store.GetEnumerator();
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
        {
            return Store.GetEnumerator();
        }

        public int Count
        {
            get
            {
                return Store.Count;
            }
        }

        public Expr this[Variable v]
        {
            get
            {
                return Store[v];
            }
            set
            {
                Store[v] = value;
            }
        }
    }
}

