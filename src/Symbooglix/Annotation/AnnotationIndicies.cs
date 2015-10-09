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

namespace Symbooglix
{
    namespace Annotation
    {
        public enum AnnotationIndex
        {
            PROGRAM_LOCATION = 0,
            PROFILE_DATA,
            GLOBALS_USED_IN_OLD_EXPR,
            PROGRAM_LOCATION_PROCEDURE_MODSET // Urgh... This is necessary due to how Modsets are represented in Boogie
        }
    }
}

