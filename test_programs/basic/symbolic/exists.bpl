// RUN: %symbooglix %s 2>&1 | %OutputCheck -d %s
procedure main()
{
    // CHECK: Created new symbolic \[SymbolicVariable: symbolic_0:int\]
    // CHECK: Created new symbolic \[SymbolicVariable: symbolic_1:int\]
    var a:int;
    var b:int;
    // CHECK: Assert : \(exists c: int :: symbolic_0 \+ c == symbolic_1\)
    assert (exists c:int :: a + c == b);
}
