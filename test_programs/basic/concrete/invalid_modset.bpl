// RUN: %symbooglix --use-modset-transform=1 %s | %OutputCheck %s
var x:int;

procedure main()
{
    x := 5;
    // CHECK-L: State 0 terminated without error
    assert x == 5;
}