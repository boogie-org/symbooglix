using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace symbooglix
{

    public class Executor : IExecutorHandler
    {
        public enum HandlerAction 
        { 
            CONTINUE, // Allow execution of other handlers for this event
            STOP // Do not execute any more handlers for this event
        };
        
        public Executor(Program prog, IStateScheduler scheduler)
        { 
            this.prog = prog;
            stateScheduler = scheduler;
            symbolicPool = new SymbolicPool();
            preEventHandlers = new List<IExecutorHandler>();
            postEventHandlers = new List<IExecutorHandler>();
            breakPointHandlers = new List<IBreakPointHandler>();
        }

        private IStateScheduler stateScheduler;
        public  ExecutionState currentState
        {
            get;
            private set;
        }
        private Program prog;
        private ExecutionState initialState; // Represents a state that has not entered any procedures
        private List<IExecutorHandler> preEventHandlers;
        private List<IExecutorHandler> postEventHandlers;
        private List<IBreakPointHandler> breakPointHandlers;
        private SymbolicPool symbolicPool;
        private bool hasBeenPrepared = false;

        public bool prepare()
        {
            // Create initial execution state
            initialState = new ExecutionState();

            // Load Globals
            var GVs = prog.TopLevelDeclarations.OfType<GlobalVariable>();
            foreach (GlobalVariable gv in GVs)
            {
                // Make symbolic initially
                // FIXME: We should probably check if globals are set to constant value first
                var s = symbolicPool.getFreshSymbolic(gv.TypedIdent);
                initialState.mem.globals.Add(gv, s.expr);
                initialState.symbolics.Add(s);
            }

            // FIXME: Load axioms

            // FIXME: Initialise constants from axioms

            hasBeenPrepared = true;
            return true;
        }

        public void registerPreEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            preEventHandlers.Add(handler);
        }

        public void unregisterPreEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(preEventHandlers.Contains(handler));
            preEventHandlers.Remove(handler);
        }

        public void registerPostEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            postEventHandlers.Add(handler);
        }

        public void unregisterPostEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(postEventHandlers.Contains(handler));
            postEventHandlers.Remove(handler);
        }

        public void registerBreakPointHandler(IBreakPointHandler handler)
        {
            Debug.Assert(handler != null);
            breakPointHandlers.Add(handler);
        }

        public void unregisterBreakPointHandler(IBreakPointHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(breakPointHandlers.Contains(handler));
            breakPointHandlers.Remove(handler);
        }

        public bool run(Implementation entryPoint)
        {
            if (!hasBeenPrepared)
                prepare();

            // FIXME: Clone initialState so we can deal with execution at a different entry point later on
            currentState = initialState;

            stateScheduler.addState(currentState);
            
            // FIXME: Check entry point is in prog?


            // Push entry point onto stack frame
            // FIXME: handle requires
            enterProcedure(entryPoint,null, this);

            while (stateScheduler.getNumberOfStates() != 0)
            {
                currentState = stateScheduler.getNextState();
                currentState.getCurrentStackFrame().currentInstruction.MoveNext();
                executeInstruction();
            }
            Console.WriteLine("Finished executing all states");

            return true;
        }

        public void terminate()
        {
            Console.WriteLine("Terminating early");
            Console.WriteLine("FIXME: Save state information");
            stateScheduler.removeAll(s => true);
            Debug.Assert(stateScheduler.getNumberOfStates() == 0);
        }

        private void executeInstruction()
        {
            Absy currentInstruction = currentState.getCurrentStackFrame().currentInstruction.Current;
            if (currentInstruction == null)
                throw new NullReferenceException("Instruction was null");

            HandlerAction action = HandlerAction.CONTINUE;
            // Invoke pre-event handlers
            foreach (IExecutorHandler h in preEventHandlers)
            {
                action = currentInstruction.visitCmd(h, this);
                if (action == HandlerAction.STOP)
                    return;
            }

            // Ignore the action returned from ourself
            currentInstruction.visitCmd(this, this); // Use double dispatch

            // Invoke post-event handlers
            foreach (IExecutorHandler h in postEventHandlers)
            {
                action = currentInstruction.visitCmd(h, this);
                if (action == HandlerAction.STOP)
                    return;
            }
        }

        protected void handleBreakPoints(PredicateCmd cmd) // FIXME: Support calls too!
        {
            string breakPointName = QKeyValue.FindStringAttribute(cmd.Attributes, "symbooglix_bp");
            if (breakPointName == null)
                return;

            HandlerAction action = HandlerAction.CONTINUE;
            foreach (IBreakPointHandler h in breakPointHandlers)
            {
                action = h.handleBreakPoint(breakPointName, this);
                if (action == HandlerAction.STOP)
                    return;
            }
        }

        public void makeSymbolic(Variable v)
        {
            Debug.Assert(currentState.isInScopeVariable(v));
            var s = symbolicPool.getFreshSymbolic(v.TypedIdent);
            currentState.symbolics.Add(s);
            currentState.assignToVariableInScope(v, s.expr);
        }

        public bool isSymbolic(Variable v)
        {
            // FIXME: Find a better way to do this?
            Debug.Assert(currentState.isInScopeVariable(v), "Variable is not in scope");
            Expr e = currentState.getInScopeVariableExpr(v);
            Debug.Assert(e != null , "Expression for variable is NULL");
            var fsv = new FindSymbolicsVisitor(symbolicPool);
            fsv.Visit(e);
            return fsv.symbolics.Count != 0;
        }


        // if procedureParams == null then parameters will be assumed to be fresh symbolics
        // otherwise procedureParams should be a listof Expr for the procedure.
        // Note there is not need to make a copy of these Expr because a Boogie
        // procedure is not allowed to modify passed in parameters.
        public HandlerAction enterProcedure(Implementation p, List<Expr> procedureParams, Executor executor)
        {
            // FIXME: The boundary between Executor and ExecutionState is
            // unclear, who should do the heavy lifting?
            currentState.enterProcedure(p);

            // FIXME: We should check there are no name clashes between
            // existing program variables and symbolics

            // Load procedure in parameters on to stack
            if (procedureParams == null)
            {
                // Give all parameters fresh symbolics
                foreach (Variable v in p.InParams)
                {
                    // Just make symbolic for now
                    var s = symbolicPool.getFreshSymbolic(v.TypedIdent);
                    currentState.getCurrentStackFrame().locals.Add(v, s.expr);
                    currentState.symbolics.Add(s);
                }
            }
            else
            {
                // Push expr for param on to stack.
                Debug.Assert(procedureParams.Count == p.InParams.Count);

                foreach (var tuple in p.InParams.Zip(procedureParams))
                {
                    currentState.getCurrentStackFrame().locals.Add(tuple.Item1, tuple.Item2);
                }

            }

            // Load procedure out parameters on to stack
            foreach(Variable v in p.OutParams)
            {
                // Make symbolic
                var s = symbolicPool.getFreshSymbolic(v.TypedIdent);
                currentState.getCurrentStackFrame().locals.Add(v, s.expr);
                currentState.symbolics.Add(s);
            }

            // Load procedure's declared locals on to stack
            foreach(Variable v in p.LocVars)
            {
                // Make symbolic
                var s = symbolicPool.getFreshSymbolic(v.TypedIdent);
                currentState.getCurrentStackFrame().locals.Add(v, s.expr);
                currentState.symbolics.Add(s);
            }

            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(ReturnCmd c, Executor executor)
        {
            // Pass Parameters to Caller
            if (currentState.mem.stack.Count > 1)
            {
                StackFrame callingSF = currentState.mem.stack.ElementAt(currentState.mem.stack.Count - 2);
                CallCmd caller = (CallCmd) callingSF.currentInstruction.Current;
                Debug.Assert(caller is CallCmd);

                // Assign return parameters
                Debug.Assert(caller.Proc.OutParams.Count == caller.Outs.Count);
                foreach (var tuple in caller.Outs.Zip(currentState.getCurrentStackFrame().procedure.OutParams))
                {
                    // Get return value
                    Expr value = currentState.getInScopeVariableExpr(tuple.Item2);
                    Debug.Assert(value != null);

                    // Assign
                    currentState.assignToVariableInStack(callingSF, tuple.Item1.Decl, value);
                }

            }

            // Pop stack frame
            currentState.leaveProcedure();

            if (currentState.finished())
            {
                stateScheduler.removeState(currentState);
            }

            return HandlerAction.CONTINUE;
     
        }


        public HandlerAction handle(AssignCmd c, Executor executor)
        {
            // FIXME: Handle map assignments

            VariableMapRewriter r = new VariableMapRewriter(currentState); 
            foreach(var lhsrhs in c.Lhss.Zip(c.Rhss))
            {
                // Check assignment allow
                Debug.Assert(lhsrhs.Item1.DeepAssignedVariable.IsMutable);

                // Check lhs is actually in scope
                if (! currentState.isInScopeVariable(lhsrhs.Item1.DeepAssignedIdentifier))
                    throw new IndexOutOfRangeException("Lhs of assignment not in scope"); // FIXME: Wrong type of exception

                // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                var rvalue = (Expr)r.Visit(lhsrhs.Item2);

                currentState.assignToVariableInScope(lhsrhs.Item1.DeepAssignedVariable, rvalue);

                Debug.WriteLine("Assignment : " + lhsrhs.Item1.DeepAssignedIdentifier + " := " + rvalue);
            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssertCmd c, Executor executor)
        {
            handleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(currentState);
            var dupAndrw = (Expr) r.Visit(c.Expr);
            Debug.WriteLine("Assert : " + dupAndrw);

            // TODO: fork with true and negated assertions and solve

            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssumeCmd c, Executor executor)
        {
            handleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(currentState);
            var dupAndrw = (Expr) r.Visit(c.Expr);
            Debug.WriteLine("Assume : " + dupAndrw);

            // TODO: Check assumption

            currentState.cm.addConstraint(dupAndrw);
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(GotoCmd c, Executor executor)
        {
            // TODO fork state per block

            // TODO look ahead for assumes
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(CallCmd c, Executor executor)
        {
            var args = new List<Expr>();
            var reWritter = new VariableMapRewriter(currentState);

            // Find corresponding implementation
            var implementations = prog.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Proc == c.Proc);
            Debug.Assert(implementations.Count() == 1);
            Implementation imp = implementations.First();

            foreach (Expr e in c.Ins)
            {
                args.Add( (Expr) reWritter.Visit(e) );
            }

            HandlerAction action = HandlerAction.CONTINUE;
            foreach (IExecutorHandler h in preEventHandlers)
            {
                action = h.enterProcedure(imp, args, this);
                if (action == HandlerAction.STOP)
                    break;
            }

            // We have slightly different semantics here to the handle() methods. Clients cannot block enterProcedure()
            enterProcedure(imp, args, this);
            foreach (IExecutorHandler h in postEventHandlers)
            {
                action = h.enterProcedure(imp, args, this);
                if (action == HandlerAction.STOP)
                    break;
            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssertEnsuresCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssertRequiresCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(HavocCmd c, Executor executor)
        {
            Debug.WriteLine("Havoc : " + c.ToString().TrimEnd('\n'));
            foreach (IdentifierExpr idExpr in c.Vars)
            {
                makeSymbolic(idExpr.Decl);
            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(YieldCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

    }
}

