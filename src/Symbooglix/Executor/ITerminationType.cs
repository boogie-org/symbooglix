using System;
using System.IO;
using Microsoft.Boogie;
using System.Diagnostics;

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
            string line = "";
            using (var SW = new StringWriter())
            {
                returnCmd.Emit(new TokenTextWriter("", SW, /*setTokens=*/false, /*pretty=*/false), 0);
                line = SW.ToString();
            }

            return "Terminated without error at " +
                returnCmd.tok.filename + ":" +
                returnCmd.tok.line + " " +
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
                assertCmd.ToString();
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
                assumeCmd.ToString();
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
                requires.Condition.ToString();
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
                requires.Condition.ToString();
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
                ensures.Condition.ToString();
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
                ensures.Condition.ToString();
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
                return State.GetCurrentStackFrame().CurrentInstruction.Current.GetProgramLocation();
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
                line = SW.ToString();
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
}

