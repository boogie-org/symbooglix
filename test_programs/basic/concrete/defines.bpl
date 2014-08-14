// RUN: %symbooglix %s 2>&1 | %OutputCheck --check-prefix=CHECK1 %s
// RUN: %symbooglix --defines FOO %s 2>&1 | %OutputCheck --check-prefix=CHECK2 %s
procedure main()
{
    // CHECK2-L: Adding define "FOO" to Boogie parser
    #if FOO
    // CHECK2-L: State 0: Terminated without error
    assert true;
    #else
    // CHECK1-L: State 0: Terminated with assertion failure
    assert false;
    #endif
}
