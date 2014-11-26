// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck -d %s
procedure main()
{
    // CHECK-L: Creating Symbolic ~sb_a_0:int
    // CHECK-L: Creating Symbolic ~sb_b_0:int
    var a:int;
    var b:int;
    // CHECK-L: Assert : (exists c: int :: ~sb_a_0 + c == ~sb_b_0)
    assert (exists c:int :: a + c == b);
}
