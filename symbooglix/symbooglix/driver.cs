using System;
using Microsoft;

namespace symbooglix
{
    public class driver
    {
        public static int Main(String[] args)
        {
            Console.WriteLine ("Hello World!");
            if (args.Length == 0) {
                Console.WriteLine ("Pass boogie file as first arg!");
                return 1;
            }

            Microsoft.Boogie.Program x = null;
            System.Collections.Generic.List<string> defines = null;
            int success = Parser.Parse (args[0], defines, out x);
            return success;
        }
    }
}

