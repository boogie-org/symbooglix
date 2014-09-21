// RUN: %rmdir %t.symbooglix-out1
// RUN: %rmdir %t.symbooglix-out2
// RUN: %symbooglix --output-dir %t.symbooglix-out1 %s --fold-constants=0 2>&1 | %OutputCheck %s
// RUN: %symbooglix --output-dir %t.symbooglix-out2 %s --fold-constants=1 2>&1 | %OutputCheck %s
procedure main()
{
    var x:real;
    x := -1.5;
    // CHECK: State 0: Terminated without error
    assert (x + x) == -3.0;
}
