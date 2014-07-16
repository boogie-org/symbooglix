// RUN: %symbooglix %s --fold-constants=0 2>&1 | %OutputCheck %s
// RUN: %symbooglix %s --fold-constants=1 2>&1 | %OutputCheck %s
procedure main()
{
    var x:real;
    x := -1.5;
    // CHECK: State 0 terminated without error
    assert (x + x) == -3.0;
}
