using System;
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
                returnCmd.ToString();
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

    public class TerminatedAtFailingAssert : ITerminationType
    {
        public TerminatedAtFailingAssert(AssertCmd location)
        {
            this.ExitLocation = new ProgramLocation(location);
        }

        public string GetMessage()
        {
            Debug.Assert(ExitLocation.IsCmd && ExitLocation.AsCmd is AssertCmd);
            var assertCmd = ExitLocation.AsCmd as AssertCmd;
            return "Terminated with assertion failure " +
                assertCmd.tok.filename + ":" +
                assertCmd.tok.line + ": " +
                assertCmd.ToString();
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

    public class TerminatedAtUnsatisfiableAssume : ITerminationType
    {
        public TerminatedAtUnsatisfiableAssume(AssumeCmd location)
        {
            this.ExitLocation = new ProgramLocation(location);
        }

        public string GetMessage()
        {
            Debug.Assert(ExitLocation.IsCmd && ExitLocation.AsCmd is AssumeCmd);
            var assumeCmd = ExitLocation.AsCmd as AssumeCmd;
            return "Terminated with unsatisiable assumption " +
                assumeCmd.tok.filename + ":" +
                assumeCmd.tok.line + ": " +
                assumeCmd.ToString();
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

    // This is only for requires on program entry points
    public class TerminatedAtUnsatisfiableEntryRequires : ITerminationType
    {
        public TerminatedAtUnsatisfiableEntryRequires(Requires requires)
        {
            this.ExitLocation = new ProgramLocation(requires);
        }
            
        public string GetMessage()
        {
            Debug.Assert(ExitLocation.IsRequires);
            var requires = ExitLocation.AsRequires;
            return "Terminated at program entry point at an unsatisfiable requires " +
                requires.tok.filename + ":" +
                requires.tok.line + ": " +
                requires.ToString();
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

    public class TerminatedAtFailingRequires : ITerminationType
    {
        public TerminatedAtFailingRequires(Requires requires)
        {
            this.ExitLocation = new ProgramLocation(requires);
        }

        public string GetMessage()
        {
            Debug.Assert(ExitLocation.IsRequires);
            var requires = ExitLocation.AsRequires;
            return "Terminated with failing requires " +
                requires.tok.filename + ":" +
                requires.tok.line + ": " +
                requires.Condition.ToString();
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

    public class TerminatedAtFailingEnsures : ITerminationType
    {
        public TerminatedAtFailingEnsures(Ensures ensures)
        {
            this.ExitLocation = new ProgramLocation(ensures);
        }
        public string GetMessage()
        {
            Debug.Assert(ExitLocation.IsEnsures);
            var requires = ExitLocation.AsEnsures;
            return "Terminated with failing ensures " +
                requires.tok.filename + ":" +
                requires.tok.line + ": " +
                requires.Condition.ToString();
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

    // This is for Ensures that we try assume when calling into
    // a procedure
    public class TerminatedAtUnsatisfiableEnsures : ITerminationType
    {
        public TerminatedAtUnsatisfiableEnsures(Ensures ensures)
        {
            this.ExitLocation = new ProgramLocation(ensures);
        }

        public string GetMessage()
        {
            Debug.Assert(ExitLocation.IsEnsures);
            var requires = ExitLocation.AsEnsures;
            return "Terminated with unsatisfiable ensures " +
                requires.tok.filename + ":" +
                requires.tok.line + ": " +
                requires.Condition.ToString();
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
}

