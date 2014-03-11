using System;

namespace symbooglix
{
    public class SymbooglixCommandLineOptions : Microsoft.Boogie.CommandLineOptions
    {
        public SymbooglixCommandLineOptions() : base("Symbooglix","Symbolic execution engine for Boogie")
        {

        }

        public bool useInstructionPrinter = false;
        public bool useEnterLeaveStackPrinter = false;
        public bool useCallSequencePrinter = false;
        public bool useVerifyUnmodifiedProcedureHandler = true;

        protected override bool ParseOption(string name, CommandLineParseState ps)
        {
            if (name == "useInstructionPrinter")
            {
                useInstructionPrinter = true;
                return true;
            }

            if (name == "useEnterLeaveStackPrinter")
            {
                useEnterLeaveStackPrinter = true;
                return true;
            }

            if (name == "useCallSequencePrinter")
            {
                useCallSequencePrinter = true;
                return true;
            }

            if (name == "noVerifyUMP")
            {
                useVerifyUnmodifiedProcedureHandler = false;
                return true;
            }

            return base.ParseOption(name, ps);
        }
    }
}

