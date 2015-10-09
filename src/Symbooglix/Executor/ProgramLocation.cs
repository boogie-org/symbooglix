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

namespace Symbooglix
{
    // Should we split this into an abstract ProgramLocation and then have subclasses
    // for the different locations?
    public class ProgramLocation
    {
        private Object Location;

        public string FileName
        {
            get
            {
                if (Location is Absy)
                    return ( Location as Absy ).tok.filename;
                else
                    return "unknown"; // FIXME
            }
        }

        public int LineNumber
        {
            get
            {
                if (Location is Absy)
                    return ( Location as Absy ).tok.line;
                else
                    return -1; // FIXME
            }
        }

        public string Line
        {
            get
            {
                if (Location is Absy)
                    return ( Location as Absy ).ToString().TrimEnd('\n');
                else
                    return "";
            }
        }

        public InstructionStatistics InstrStatistics
        {
            get
            {
                if (IsCmd)
                    return AsCmd.GetInstructionStatistics();
                else if (IsTransferCmd)
                    return AsTransferCmd.GetInstructionStatistics();
                else if (IsRequires)
                    return AsRequires.GetInstructionStatistics();
                else if (IsEnsures)
                    return AsEnsures.GetInstructionStatistics();
                else if (IsAxiom)
                {
                    return AsAxiom.GetInstructionStatistics();
                }

                return null;
            }
        }

        // The location is where this variable is declared
        public ProgramLocation(Variable V)
        {
            Location = (Object) V;
        }

        // The location is where this cmd is executed
        public ProgramLocation(Cmd cmd)
        {
            Location = (Object) cmd;
        }

        // The location is where this cmd is executed
        public ProgramLocation(TransferCmd cmd)
        {
            Location = (Object) cmd;
        }

        public ProgramLocation(Requires requires)
        { 
            Location = (Object) requires;
        }

        public ProgramLocation(Ensures ensures)
        { 
            Location = (Object) ensures;
        }

        public ProgramLocation(ModifiesSet modset)
        {
            Location = (Object) modset;
        }

        public ProgramLocation(Axiom axiom)
        {
            Location = (Object) axiom;
        }

        public bool IsVariable
        {
            get { return Location is Variable; }
        }

        public Variable AsVariable
        {
            get
            {
                if (IsVariable)
                    return Location as Variable;
                else
                    return null;
            }
        }

        public bool IsCmd
        {
            get { return Location is Cmd; }
        }

        public Cmd AsCmd
        {
            get
            {
                if (IsCmd)
                    return Location as Cmd;
                else
                    return null;
            }
        }

        public bool IsTransferCmd
        {
            get { return Location is TransferCmd; }
        }

        public TransferCmd AsTransferCmd
        {
            get
            {
                if (IsTransferCmd)
                    return Location as TransferCmd;
                else
                    return null;
            }
        }

        public bool IsRequires
        {
            get { return Location is Requires; }
        }

        public Requires AsRequires
        {
            get
            {
                if (IsRequires)
                    return Location as Requires;
                else
                    return null;
            }
        }

        public bool IsEnsures
        {
            get { return Location is Ensures; }
        }

        public Ensures AsEnsures
        {
            get
            {
                if (IsEnsures)
                    return Location as Ensures;
                else
                    return null;
            }
        }

        public bool IsModifiesSet
        {
            get { return Location is ModifiesSet; }
        }

        public ModifiesSet AsModifiesSet
        {
            get
            {
                if (IsModifiesSet)
                    return Location as ModifiesSet;
                else
                    return null;
            }
        }

        public bool IsAxiom
        {
            get { return Location is Axiom; }
        }

        public Axiom AsAxiom
        {
            get
            {
                if (IsAxiom)
                    return Location as Axiom;
                else
                    return null;
            }
        }

        public override string ToString()
        {
            char[] toTrim = { '\r', '\n' };

            if (IsVariable)
                return "[Variable] " + AsVariable.ToString();
            else if (IsCmd)
                return "[Cmd] " + AsCmd.ToString().TrimEnd(toTrim);
            else if (IsTransferCmd)
                return "[TransferCmd] " + AsTransferCmd.ToString().TrimEnd(toTrim);
            else if (IsRequires)
                return "[Requires] " + AsRequires.Condition.ToString();
            else if (IsEnsures)
                return "[Ensures] " + AsEnsures.Condition.ToString();
            else if (IsModifiesSet)
                return "[Modifies set] " + AsModifiesSet.ToString();
            else if (IsAxiom)
                return "[Axiom] " + AsAxiom.Expr.ToString();
            else
                return "unknown";
        }
    }
}
