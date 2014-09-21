// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out --use-modset-transform=1 %s | %OutputCheck %s
var x:int;

procedure main()
{
    x := 5;
    // CHECK-L: State 0: Terminated without error
    assert x == 5;
}
