// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
function {:bvbuiltin "zero_extend 4"} BV4_ZEXT8(bv4) : bv8;
function {:bvbuiltin "bvugt"} BVUGT8(bv8, bv8) : bool;
procedure main(a:bv4) returns (r:bv8)
requires a == 15bv4;
{
    r := BV4_ZEXT8(a);
    assert r == 15bv8;
}
