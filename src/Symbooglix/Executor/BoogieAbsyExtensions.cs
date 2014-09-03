using System;
using Symbooglix;
using Microsoft.Boogie;

namespace Symbooglix
{
    public static class BoogieAbsyExtensions
    {
        // Handy extension to get ProgramLocation instaces from where we expect them to be
        // This implicitly depends on the AnnotationIndicies pass being run on the program
        // FIXME: This method should only be on instances (e.g. Cmds) that support having a 
        // ProgramLocation, applying to Absy is too broad!
        public static ProgramLocation GetProgramLocation(this Absy node)
        {
            return node.GetMetatdata<ProgramLocation>( (int) Annotation.AnnotationIndex.PROGRAM_LOCATION);
        }
    }
}

