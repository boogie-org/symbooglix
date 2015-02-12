// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableAssume 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedSpeculativePath 0
procedure main()
{
    var m:[bv8][bv16]bv32;
    // Assume it's initialised
    assume (forall x:bv8, y:bv16 :: m[x][y] == 0bv32);
    assert (forall a:bv8, b:bv16 :: m[a][b] == 0bv32);
}
