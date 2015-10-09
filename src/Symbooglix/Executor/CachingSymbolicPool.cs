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
using System.Diagnostics;

namespace Symbooglix
{
    // FIXME: This design is Broken. See the tests
    public class CachingSymbolicPool : ISymbolicPool
    {
        private SimpleSymbolicPool Pool;

        // Compare Variables based on equality
        class VariableRefComparer : IEqualityComparer<Variable>
        {
            public bool Equals(Variable x, Variable y)
            {
                return Object.ReferenceEquals(x, y);
            }

            public int GetHashCode(Variable obj)
            {
                return System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(obj);
            }
        }

        // Compare the Tuple keys we use in a reference like way for the first item HavocCmd or Procedure but the
        // second item (the int) by value
        class TupleVariableRefComparer<T> : IEqualityComparer<Tuple<T,int>>  where T: class
        {
            public bool Equals(Tuple<T, int> x, Tuple<T, int> y)
            {
                if (x == null)
                {
                    if (y == null)
                        return true;
                    else
                        return false;
                }

                if (x.Item2 != y.Item2)
                    return false;

                Debug.Assert(x.Item2 == y.Item2);
                return Object.ReferenceEquals(x.Item1, y.Item1);
            }

            public int GetHashCode(Tuple<T, int> obj)
            {
                if (obj == null)
                    return 0;
                else
                    return 97*(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(obj.Item1)) + obj.Item2;
            }
        }



        private Dictionary<Variable, SymbolicVariableStack> VariableStacks;
        private Dictionary<Tuple<HavocCmd,int>, SymbolicVariableStack> HavocCmdStacks;
        private Dictionary<Tuple<Procedure,int>, SymbolicVariableStack> ModsetStacks;
        public int Requests { get; private set; }

        public CachingSymbolicPool()
        {
            Pool = new SimpleSymbolicPool();
            // Make sure the dictionaries only do reference comparisons
            VariableStacks = new Dictionary<Variable, SymbolicVariableStack>(new VariableRefComparer());
            HavocCmdStacks = new Dictionary<Tuple<HavocCmd, int>, SymbolicVariableStack>(new TupleVariableRefComparer<HavocCmd>());
            ModsetStacks = new Dictionary<Tuple<Procedure, int>, SymbolicVariableStack>(new TupleVariableRefComparer<Procedure>());
            Requests = 0;
        }

        public SymbolicVariable GetFreshSymbolic(Variable Origin, ExecutionState owner)
        {
            ++Requests;
            SymbolicVariableStack varStack = null;
            try
            {
                varStack = VariableStacks[Origin];
            }
            catch (KeyNotFoundException)
            {
                // XXX: This is a little misleading the "Pool" doesn't use the owner argument
                // so the SymbolicVariableStack doesn't known about this owner
                varStack = new SymbolicVariableStack( () => Pool.GetFreshSymbolic(Origin, null));
                VariableStacks.Add(Origin, varStack);
            }

            return varStack.GetVariable(owner);
        }

        public SymbolicVariable GetFreshSymbolic(HavocCmd havocCmd, int varsIndex, ExecutionState owner)
        {
            ++Requests;
            SymbolicVariableStack havocVarStack = null;
            var key = Tuple.Create(havocCmd, varsIndex);
            try
            {
                havocVarStack = HavocCmdStacks[key];
            }
            catch (KeyNotFoundException)
            {
                // XXX: This is a little misleading the "Pool" doesn't use the owner argument
                // so the SymbolicVariableStack doesn't known about this owner
                havocVarStack = new SymbolicVariableStack( () => Pool.GetFreshSymbolic(havocCmd, varsIndex, null));
                HavocCmdStacks.Add(key, havocVarStack);
            }

            return havocVarStack.GetVariable(owner);
        }

        // Maybe use Modset instead of Procedure??
        public SymbolicVariable GetFreshSymbolic(Procedure proc, int modSetIndex, ExecutionState owner)
        {
            ++Requests;
            SymbolicVariableStack modsetVarStack = null;
            var key = Tuple.Create(proc, modSetIndex);
            try
            {
                modsetVarStack = ModsetStacks[key];
            }
            catch (KeyNotFoundException)
            {
                // XXX: This is a little misleading the "Pool" doesn't use the owner argument
                // so the SymbolicVariableStack doesn't known about this owner
                modsetVarStack = new SymbolicVariableStack( () => Pool.GetFreshSymbolic(proc, modSetIndex, null));
                ModsetStacks.Add(key, modsetVarStack);
            }

            return modsetVarStack.GetVariable(owner);
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("name : \"{0}\"", this.GetType().ToString());
            TW.WriteLine("constructs: {0}", this.Count);
            TW.WriteLine("requests: {0}", this.Requests);
            TW.WriteLine("variable_stacks: {0}", this.VariableStacks.Count);
            TW.WriteLine("havoc_stacks: {0}", this.HavocCmdStacks.Count);
            TW.WriteLine("modset_stacks: {0}", this.ModsetStacks.Count);
        }

        public int Count
        {
            get
            {
                // This the number of actual constructs
                return Pool.Count;
            }
        }

        // This represents a stack of symbolic variables which should be associated
        // with a single symbolic variable creation site in the Boogie program.
        internal class SymbolicVariableStack
        {
            public delegate SymbolicVariable MkSymbolicVariableDel();
            private MkSymbolicVariableDel MkSymbolicVariable;

            // This linked list represents the history of the created SymbolicVariables.
            // ExecutionState's effectively share this history by pointing at various nodes
            // in the linked list.
            LinkedList<SymbolicVariable> LL;

            // This maps Execution state IDs to a position in the linked list
            // The state ID is used in substitutation for a Weak reference for simplicity
            // FIXME: Use weakref instead of stateID.
            Dictionary<int, LinkedListNode<SymbolicVariable>> StackPointers;

            public int Count
            {
                get
                {
                    return StackPointers.Count;
                }
            }

            // The passed in delegate should create a fresh symbolic variable
            public SymbolicVariableStack(MkSymbolicVariableDel mkSymDel)
            {
                Debug.Assert(mkSymDel != null);
                MkSymbolicVariable = mkSymDel;
                LL = new LinkedList<SymbolicVariable>();
                StackPointers = new Dictionary<int, LinkedListNode<SymbolicVariable>>();
            }

            public SymbolicVariable GetVariable(ExecutionState owner)
            {
                int stateId = owner.Id;

                // A Symbolic Variable has never been created before
                if (LL.Count == 0)
                {
                    Debug.Assert(!StackPointers.ContainsKey(stateId));
                    var newNode = LL.AddFirst(this.MkSymbolicVariable());
                    StackPointers[stateId] = newNode;
                    return newNode.Value;
                }

                // Symbolic Variables are available for use.
                if (StackPointers.ContainsKey(stateId))
                {
                    // This state has asked for a symbolic variable previously
                    // see if there is a newer value we can get
                    var nodeToUse = StackPointers[stateId];

                    if (nodeToUse.Next == null)
                    {
                        // There isn't a newer Symbolic Variable so make one
                        var newNode = LL.AddLast(this.MkSymbolicVariable());
                        StackPointers[stateId] = newNode;
                        return newNode.Value;
                    }
                    else
                    {
                        // There is an existing newer symbolic variable in the list
                        // use it
                        nodeToUse = nodeToUse.Next;
                        StackPointers[stateId] = nodeToUse;
                        return nodeToUse.Value;
                    }
                }
                else
                {
                    // This state has never asked for a symbolic variable from us before
                    // Give it the first node.
                    var nodeToUse = LL.First;
                    StackPointers.Add(stateId, nodeToUse);
                    return nodeToUse.Value;
                }
            }
        }
    }


}

