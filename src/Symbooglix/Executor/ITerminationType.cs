using System;
using System.IO;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Linq;

namespace Symbooglix
{
    public interface ITerminationType
    {
        ExecutionState State
        {
            get;
        }

        ProgramLocation ExitLocation
        {
            get;
        }

        string GetMessage();
    }

    public abstract class TerminationTypeWithSatAndUnsatExpr : ITerminationType
    {
        protected TerminationTypeWithSatAndUnsatExpr()
        {
            this.ConditionForSat = null;
            this.ConditionForUnsat = null;
        }

        // This is the condition that could be added to the ExecutionState's
        // constraints and would be satisfiable. This is intended to be used
        // for getting a model from the solver
        // If the Expr is not available then this will return null.
        public Expr ConditionForSat
        {
            get;
            set;
        }

        // This is the condition that could be added to an ExecutionState's
        // constraints to make them unsatisfiable. This is intended to be used
        // to determine the unsat core.
        // If the Expr is not available then this will return null.
        public Expr ConditionForUnsat
        {
            get;
            set;
        }

        public abstract string GetMessage();

        public ExecutionState State
        {
            get;
            internal set;
        }

        public ProgramLocation ExitLocation
        {
            get;
            internal set;
        }
    }

    public class TerminatedWithoutError : ITerminationType
    {
        public TerminatedWithoutError(ReturnCmd location)
        {
            this.ExitLocation = new ProgramLocation(location);
        }

        public string GetMessage()
        {
            Debug.Assert(ExitLocation.IsTransferCmd && ExitLocation.AsTransferCmd is ReturnCmd);

            var returnCmd = ExitLocation.AsTransferCmd as ReturnCmd;
            return "Terminated without error at " +
            returnCmd.tok.filename + ":" +
            returnCmd.tok.line + " " +
            returnCmd.GetProgramLocation().Line;
        }

        public ExecutionState State
        {
            get;
            internal set;
        }

        public ProgramLocation ExitLocation
        {
            get;
            private set;
        }
    }

    public class TerminatedAtFailingAssert : TerminationTypeWithSatAndUnsatExpr
    {
        public TerminatedAtFailingAssert(AssertCmd location)
        {
            this.ExitLocation = new ProgramLocation(location);
        }

        public override string GetMessage()
        {
            Debug.Assert(ExitLocation.IsCmd && ExitLocation.AsCmd is AssertCmd);
            var assertCmd = ExitLocation.AsCmd as AssertCmd;
            return "Terminated with assertion failure " +
                assertCmd.tok.filename + ":" +
                assertCmd.tok.line + ": " +
                assertCmd.ToString().TrimEnd('\n');
        }
    }

    public class TerminatedAtUnsatisfiableAssume : TerminationTypeWithSatAndUnsatExpr
    {
        public TerminatedAtUnsatisfiableAssume(AssumeCmd location)
        {
            this.ExitLocation = new ProgramLocation(location);
        }

        public override string GetMessage()
        {
            Debug.Assert(ExitLocation.IsCmd && ExitLocation.AsCmd is AssumeCmd);
            var assumeCmd = ExitLocation.AsCmd as AssumeCmd;
            return "Terminated with unsatisiable assumption " +
                assumeCmd.tok.filename + ":" +
                assumeCmd.tok.line + ": " +
                assumeCmd.ToString().TrimEnd('\n');
        }
    }

    // This is only for requires on program entry points
    public class TerminatedAtUnsatisfiableEntryRequires : TerminationTypeWithSatAndUnsatExpr
    {
        public TerminatedAtUnsatisfiableEntryRequires(Requires requires)
        {
            this.ExitLocation = new ProgramLocation(requires);
        }
            
        public override string GetMessage()
        {
            Debug.Assert(ExitLocation.IsRequires);
            var requires = ExitLocation.AsRequires;
            return "Terminated at program entry point at an unsatisfiable requires " +
                requires.tok.filename + ":" +
                requires.tok.line + ": " +
                requires.Condition.ToString().TrimEnd('\n');
        }
    }

    public class TerminatedAtFailingRequires : TerminationTypeWithSatAndUnsatExpr
    {
        public TerminatedAtFailingRequires(Requires requires)
        {
            this.ExitLocation = new ProgramLocation(requires);
        }

        public override string GetMessage()
        {
            Debug.Assert(ExitLocation.IsRequires);
            var requires = ExitLocation.AsRequires;
            return "Terminated with failing requires " +
                requires.tok.filename + ":" +
                requires.tok.line + ": " +
                requires.Condition.ToString().TrimEnd('\n');
        }
    }

    public class TerminatedAtFailingEnsures : TerminationTypeWithSatAndUnsatExpr
    {
        public TerminatedAtFailingEnsures(Ensures ensures)
        {
            this.ExitLocation = new ProgramLocation(ensures);
        }

        public override string GetMessage()
        {
            Debug.Assert(ExitLocation.IsEnsures);
            var ensures = ExitLocation.AsEnsures;
            return "Terminated with failing ensures " +
                ensures.tok.filename + ":" +
                ensures.tok.line + ": " +
                ensures.Condition.ToString().TrimEnd('\n');
        }
    }

    // This is for Ensures that we try assume when calling into
    // a procedure
    public class TerminatedAtUnsatisfiableEnsures : TerminationTypeWithSatAndUnsatExpr
    {
        public TerminatedAtUnsatisfiableEnsures(Ensures ensures)
        {
            this.ExitLocation = new ProgramLocation(ensures);
        }

        public override string GetMessage()
        {
            Debug.Assert(ExitLocation.IsEnsures);
            var ensures = ExitLocation.AsEnsures;
            return "Terminated with unsatisfiable ensures " +
                ensures.tok.filename + ":" +
                ensures.tok.line + ": " +
                ensures.Condition.ToString().TrimEnd('\n');
        }
    }

    public class TerminatedAtUnsatisfiableAxiom : TerminationTypeWithSatAndUnsatExpr
    {
        public TerminatedAtUnsatisfiableAxiom(Axiom axiom)
        {
            this.ExitLocation = new ProgramLocation(axiom);
        }

        public override string GetMessage ()
        {
            Debug.Assert(ExitLocation.IsAxiom);
            var axiom = ExitLocation.AsAxiom;
            return "Terminated with unsatisfiable axiom " +
                axiom.tok.filename + ":" +
                axiom.tok.line + ": " +
                axiom.Expr.ToString();
        }
    }

    public class TerminatedWithDisallowedSpeculativePath : ITerminationType
    {
        public string GetMessage()
        {
            return "Disallowed speculative path. Starting at " + ExitLocation.ToString();
        }

        public ExecutionState State
        {
            get;
            internal set;
        }

        public ProgramLocation ExitLocation
        {
            get
            {
                // FIXME: This might not be reliable. We should perhaps move this into
                // "Find nearest instruction" helper class.

                // Go through the stack frame backwards without modifying it
                // We need to walk the stack frame back because we might be in the middle
                // of setting up a call and so the Current instruction might not be
                // available in the newest stackframe.
                foreach (var stackFrame in Enumerable.Reverse(State.Mem.Stack))
                {
                    var currentInstruction = stackFrame.CurrentInstruction.Current;

                    if (currentInstruction != null)
                        return currentInstruction.GetProgramLocation();
                }

                // If we've exhausted the stack we don't really know where the error
                // is. Not sure what to do next so lets not implement it for now
                throw new NotImplementedException();
            }
        }
    }

    public class TerminatedAtGotoWithUnsatisfiableTargets : ITerminationType
    {
        public TerminatedAtGotoWithUnsatisfiableTargets(GotoCmd gotoCmd)
        {
            this.ExitLocation = gotoCmd.GetProgramLocation();
        }

        public string GetMessage()
        {
            Debug.Assert(ExitLocation.IsTransferCmd && ExitLocation.AsTransferCmd is GotoCmd);

            var gotoCmd = ExitLocation.AsTransferCmd as GotoCmd;
            string line = "";
            using (var SW = new StringWriter())
            {
                gotoCmd.Emit(new TokenTextWriter("", SW, /*setTokens=*/false, /*pretty=*/false), 0);
                line = SW.ToString().TrimEnd('\n');
            }

            return "Terminated with no satisfiable path available from goto " +
                gotoCmd.tok.filename + ":" +
                gotoCmd.tok.line + " " +
                line;
        }

        public ExecutionState State
        {
            get;
            internal set;
        }

        public ProgramLocation ExitLocation
        {
            get;
            internal set;
        }
    }

    public class TerminatedWithDisallowedExplicitBranchDepth : ITerminationType
    {
        public TerminatedWithDisallowedExplicitBranchDepth(ProgramLocation location)
        {
            Debug.Assert(location != null, "location cannot be null");
            this.ExitLocation = location;
            State = null;
        }

        public string GetMessage()
        {
            var depth = State != null ? ( State.ExplicitBranchDepth ) : -1;
            var s = "Terminated with Explicit branch depth exceeded (";

            if (depth == -1)
                s += "unknown";
            else
                s += depth.ToString();

            s += ") at " + ExitLocation.ToString();
            return s;
        }

        public ExecutionState State
        {
            get;
            internal set;
        }

        public ProgramLocation ExitLocation
        {
            get;
            internal set;
        }
    }
}

