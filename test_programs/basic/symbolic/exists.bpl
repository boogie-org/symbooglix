// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck -d %s
procedure main()
{
    // CHECK-L: Creating Symbolic symbolic_0:int
    // CHECK-L: Creating Symbolic symbolic_1:int
    var a:int;
    var b:int;
    // CHECK-L: Assert : (exists c: int :: symbolic_0 + c == symbolic_1)
    assert (exists c:int :: a + c == b);
}
