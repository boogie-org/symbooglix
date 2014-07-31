// RUN: %symbooglix --entry-points entry1,entry2 %s | %OutputCheck %s
var g:int;

// CHECK-L: Entering Implementation entry1 as entry point
// CHECK-L: State 0 terminated without error
procedure entry1(x:int)
modifies g;
{
    g := 15;
    assert g == 15;
}

// CHECK-L: Entering Implementation entry2 as entry point
// CHECK-L: State 1 terminated without error
// CHECK-L: State 2 terminated without error
procedure entry2(x:int)
{
    if (g == 15)
    {
        assert {:symbooglix_bp "true_branch"} true;
    }
    else
    {
        assert {:symbooglix_bp "false_branch"} true;
    }
}
