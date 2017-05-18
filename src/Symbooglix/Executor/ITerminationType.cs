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
using System.IO;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;

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
            return "Terminated with unsatisfiable assumption " +
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

        public TerminatedWithDisallowedSpeculativePath(ProgramLocation loc)
        {
            this.ExitLocation = loc;
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

    public class TerminatedWithDisallowedLoopBound : ITerminationType
    {
        public TerminatedWithDisallowedLoopBound(ProgramLocation location, BigInteger loopBound)
        {
            Debug.Assert(location != null, "location cannot be null");
            this.LoopBound = loopBound;
            this.ExitLocation = location;
            State = null;
        }

        public string GetMessage()
        {
            String msg = String.Format("Terminated with loop bound {0} exceeded at {1}:{2}",
                                       LoopBound,
                                       ExitLocation.FileName,
                                       ExitLocation.LineNumber);
            return msg;
        }

        public ExecutionState State {
            get;
            internal set;
        }

        public ProgramLocation ExitLocation {
            get;
            internal set;
        }

        public BigInteger LoopBound {
            get;
            internal set;
        }
    }

    public class TerminatedWithUnsatisfiableUniqueAttribute : TerminationTypeWithSatAndUnsatExpr
    {
        IList<Constant> UniqueVariables;
        public TerminatedWithUnsatisfiableUniqueAttribute(IList<Constant> variables)
        {
            Debug.Assert(variables.Count > 1);
            // Just make the exit location the first variable
            this.ExitLocation = variables[0].GetProgramLocation();
            this.UniqueVariables = variables;
        }

        public override string GetMessage()
        {
            var SB = new StringBuilder();

            var theType = UniqueVariables[0].TypedIdent.Type;
            SB.Append("Terminated with unsatisfiable unique attribute for variables of type ");
            SB.Append(theType.ToString());
            return SB.ToString();
        }


    }
}

