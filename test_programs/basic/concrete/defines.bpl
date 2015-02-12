// RUN: %rmdir %t.symbooglix-out1
// RUN: %rmdir %t.symbooglix-out2
// RUN: %eec 2 %symbooglix --output-dir %t.symbooglix-out1 %s 2>&1 | %OutputCheck --check-prefix=CHECK1 %s
// RUN: %symbooglix --output-dir %t.symbooglix-out2 --defines FOO %s 2>&1 | %OutputCheck --check-prefix=CHECK2 %s
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
