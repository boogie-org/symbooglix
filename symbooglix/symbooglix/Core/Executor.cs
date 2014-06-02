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
            terminationHandlers = new List<ITerminationHandler>();
            CFT = new ConstantFoldingTraverser();
            UseConstantFolding = false;
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
        private List<ITerminationHandler> terminationHandlers;
        private SymbolicPool symbolicPool;
        private bool hasBeenPrepared = false;
        public ConstantFoldingTraverser CFT;

        public bool UseConstantFolding
        {
            get;
            set;
        }


        public bool prepare()
        {
            // Create initial execution state
            initialState = new ExecutionState();

            // Load Globals
//            var GVs = prog.TopLevelDeclarations.OfType<GlobalVariable>();
//            foreach (GlobalVariable gv in GVs)
//            {
//                var s = symbolicPool.getFreshSymbolic(gv.TypedIdent);
//                initialState.mem.globals.Add(gv, s.expr);
//                initialState.symbolics.Add(s);
//            }

            // Load Global Variables and Constants
            var GVs = prog.TopLevelDeclarations.OfType<Variable>().Where(g => g is GlobalVariable || g is Constant);
            var axioms = prog.TopLevelDeclarations.OfType<Axiom>();
            var axiomsToSkip = new HashSet<Axiom>();
            foreach (Variable gv in GVs)
            {
                bool initialised = false;
                foreach (var axiom in axioms)
                {
                    // See if we have constant assignments we can apply
                    LiteralExpr literal = null;
                    if (FindLiteralAssignment.find(axiom.Expr, gv, out literal))
                    {
                        Debug.Assert(literal != null);
                        // Make concrete
                        initialState.mem.globals.Add(gv, literal);
                        initialised = true;
                        Debug.WriteLine("Using axiom to do assignment to global " + gv + " := " + literal);
                        axiomsToSkip.Add(axiom);
                        break;
                    }
                }

                if (!initialised)
                {
                    // Make symbolic
                    var s = symbolicPool.getFreshSymbolic(gv.TypedIdent);
                    Debug.Assert(!initialState.mem.globals.ContainsKey(gv), "Cannot insert global that is already in memory");
                    initialState.mem.globals.Add(gv, s.expr);
                    initialState.symbolics.Add(s);
                }
            }

            // Add the axioms as path constraints
            foreach (var axiom in axioms)
            {
                if (axiomsToSkip.Contains(axiom))
                    continue;

                var VMR = new VariableMapRewriter(initialState);
                VMR.ReplaceGlobalsOnly = true; // The stackframe doesn't exist yet!
                Expr constraint = (Expr) VMR.Visit(axiom.Expr);
                initialState.cm.addConstraint(constraint);
                Debug.WriteLine("Adding constraint : " + constraint);
            }
             


            hasBeenPrepared = true;

            // FIXME: check constraints are consistent!

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

        public void registerTerminationHandler(ITerminationHandler handler)
        {
            Debug.Assert(handler != null);
            terminationHandlers.Add(handler);
        }

        public void unregisterTerminationHandler(ITerminationHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(terminationHandlers.Contains(handler));
            terminationHandlers.Remove(handler);
        }

        public void run(Implementation entryPoint)
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

            var oldState = currentState;
            while (stateScheduler.getNumberOfStates() != 0)
            {
                currentState = stateScheduler.getNextState();
                Debug.WriteLineIf(oldState != currentState, "[Switching context]");
                oldState = currentState;

                currentState.getCurrentStackFrame().currentInstruction.MoveNext();
                executeInstruction();
            }
            Console.WriteLine("Finished executing all states");

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

        public void makeConcrete(Variable v, LiteralExpr literal)
        {
            Debug.Assert(currentState.isInScopeVariable(v));
            Debug.Assert(isSymbolic(v), "Tried to concretise something that is already concrete!");
            currentState.assignToVariableInScope(v, literal);

            // FIXME: 
            // We can't remove this from the ExecutionState's set
            // of symbolic variables because it may of been propagated into other variables
            // We need a way of knowing if a symbolic has been propagated
            // and if not we should remove it
        }

        public bool isSymbolic(Variable v)
        {
            // FIXME: Find a better way to do this?
            Debug.Assert(currentState.isInScopeVariable(v), "Variable is not in scope");
            Expr e = currentState.getInScopeVariableExpr(v);
            Debug.Assert(e != null , "Expression for variable is NULL");
            var fsv = new FindSymbolicsVisitor(currentState);
            fsv.Visit(e);
            return fsv.symbolics.Count != 0;
        }


        // if procedureParams == null then parameters will be assumed to be fresh symbolics
        // otherwise procedureParams should be a listof Expr for the procedure.
        // Note there is not need to make a copy of these Expr because a Boogie
        // procedure is not allowed to modify passed in parameters.
        public HandlerAction enterProcedure(Implementation p, List<Expr> procedureParams, Executor executor)
        {
            // FIXME: We iterate over the requires statements quite a few times. It would be nice to rewrite this function
            // to minimise the number of times we do that.

            // FIXME: The boundary between Executor and ExecutionState is
            // unclear, who should do the heavy lifting?
            currentState.enterProcedure(p);

            // FIXME: We should check there are no name clashes between
            // existing program variables and symbolics

            // Load procedure in parameters on to stack
            if (procedureParams == null)
            {
                // Try to see if we can make constant
                // HACK: This is absolutely disgusting! The parameters on the procedure
                // and implementation are different instances which causes problems
                // because requires statements refer to the procedure parameters but
                // our executor needs to work with the implementation parameters :(
                foreach (var v in p.Proc.InParams.Zip(p.InParams))
                {
                    // See if there is a <identifer> == <literal> type expression in the requires statements
                    // if so don't make that identifier symbolic and instead give it the literal value
                    bool variableIsContant = false;
                    foreach (Requires r in p.Proc.Requires)
                    {
                        LiteralExpr literal = null;
                        if (FindLiteralAssignment.find(r.Condition, v.Item1, out literal))
                        {
                            Debug.Assert(literal != null);
                            Debug.WriteLine("Not making parameter symbolic and instead doing " + v.Item2 + " : = " + literal);
                            currentState.getCurrentStackFrame().locals.Add(v.Item2, literal);
                            variableIsContant = true;
                            break;                     
                        }
                    }

                    if (variableIsContant)
                        continue; // Already assigned

                    // Make parameter symbolics
                    // Just make symbolic for now
                    var s = symbolicPool.getFreshSymbolic(v.Item2.TypedIdent);
                    currentState.getCurrentStackFrame().locals.Add(v.Item2, s.expr);
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

            // Load procedure's requires statements as constraints.
            // We need to rewrite this expression before storing it because it may refer to 
            // procedure arguments rather than the implementation arguments which are confusingly
            // different instances of the same object
            var VR = new VariableRewriter();
            foreach (var VariablePair in p.InParams.Zip(p.Proc.InParams))
            {
                // Map Procedure InParams to Implementation InParams
                VR.VariableMap.Add(VariablePair.Item2, VariablePair.Item1);
            }
            foreach (Requires r in p.Proc.Requires)
            {
                Expr constraint = (Expr) VR.Visit(r.Condition);
                currentState.cm.addConstraint(constraint);
            }

            // Concretise globals if explicitly set in requires statements
            foreach (Requires r in p.Proc.Requires)
            {
                Variable MightBeGlobal = null;
                LiteralExpr literal = null;
                if (FindLiteralAssignment.findAnyVariable(r.Condition, out MightBeGlobal, out literal))
                {
                    if (currentState.mem.globals.ContainsKey(MightBeGlobal))
                    {
                        Debug.WriteLine("Concretising global '{0}'", MightBeGlobal);
                        // currentState.mem.globals[MightBeGlobal] = literal; // FIXME: Is this faster?
                        makeConcrete(MightBeGlobal, literal);
                    }
                }
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

            // FIXME: Check ensures condition cannot fail! fork both ways is possible

            // Pop stack frame
            currentState.leaveProcedure();

            if (currentState.finished())
            {
                // Notify any handlers that this state terminated without error
                foreach (var handler in terminationHandlers)
                {
                    handler.handleSuccess(currentState);
                }

                stateScheduler.removeState(currentState);
            }

            return HandlerAction.CONTINUE;
     
        }


        public HandlerAction handle(AssignCmd c, Executor executor)
        {
            int index=0;
            VariableMapRewriter r = new VariableMapRewriter(currentState);
            // FIXME: Should we zip asSimpleAssignCmd lhs and rhs instead?
            foreach(var lhsrhs in c.Lhss.Zip(c.Rhss))
            {
           
                Variable lvalue = lhsrhs.Item1.DeepAssignedVariable;
                Expr rvalue = null;

                // Check assignment allow
                Debug.Assert(lvalue.IsMutable, "lvalue is not mutable!");

                // Check lhs is actually in scope
                if (! currentState.isInScopeVariable(lvalue))
                    throw new IndexOutOfRangeException("Lhs of assignment not in scope"); // FIXME: Wrong type of exception

                if (lhsrhs.Item1 is SimpleAssignLhs)
                {
                    // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                    rvalue = (Expr) r.Visit(lhsrhs.Item2);
                    if (UseConstantFolding)
                        rvalue = CFT.Traverse(rvalue);
                }
                else if (lhsrhs.Item1 is MapAssignLhs)
                {
                    // We need to use "AsSimleAssignCmd" so that we have a single Variable as lhs and MapStore expressions
                    // on the right hand side
                    var ac = c.AsSimpleAssignCmd;
                    Debug.Assert(ac.Lhss[index].DeepAssignedVariable == lvalue, "lvalue mismatch");
                    rvalue = ac.Rhss[index];
                    // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                    rvalue = (Expr) r.Visit(rvalue);

                    if (UseConstantFolding)
                        rvalue = CFT.Traverse(rvalue);
                }
                else
                {
                    throw new NotSupportedException("Unknown type of assignment");
                }

                currentState.assignToVariableInScope(lvalue, rvalue);

                Debug.WriteLine("Assignment : " + lvalue + " := " + rvalue);
                ++index;
            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssertCmd c, Executor executor)
        {
            handleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(currentState);
            var dupAndrw = (Expr) r.Visit(c.Expr);

            if (UseConstantFolding)
                dupAndrw = CFT.Traverse(dupAndrw);

            Debug.WriteLine("Assert : " + dupAndrw);

            // TODO: fork with true and negated assertions and solve
            // TODO: Notify termination handlers if necessary

            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssumeCmd c, Executor executor)
        {
            handleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(currentState);
            var dupAndrw = (Expr) r.Visit(c.Expr);

            if (UseConstantFolding)
                dupAndrw = CFT.Traverse(dupAndrw);

            Debug.WriteLine("Assume : " + dupAndrw);

            // TODO: Check assumption
            // TODO: Notify termination handlers if necessary

            currentState.cm.addConstraint(dupAndrw);
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(GotoCmd c, Executor executor)
        {
            Debug.Assert(c.labelTargets.Count() > 0);

            if (c.labelTargets.Count() > 1)
            {
                ExecutionState newState = null;
                for (int targetId = 1, tEnd = c.labelTargets.Count; targetId < tEnd; ++targetId)
                {
                    // FIXME: We should look ahead for assumes and check that they are satisfiable so we don't create states and then immediatly destroy them!
                    newState = currentState.DeepClone(); // FIXME: This is not memory efficient
                    newState.getCurrentStackFrame().transferToBlock(c.labelTargets[targetId]);
                    stateScheduler.addState(newState);
                }
            }

            // The current execution state will always take the first target
            currentState.getCurrentStackFrame().transferToBlock(c.labelTargets[0]);

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

