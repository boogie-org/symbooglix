// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 2 %symbooglix --output-dir %t.symbooglix-out --fold-constants=1 %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 1
function {:bvbuiltin "bvudiv"} BVDIV8(bv8,bv8) returns(bv8);
procedure main()
{
    assert BVDIV8(2bv8, 0bv8) == 0bv8;
}
