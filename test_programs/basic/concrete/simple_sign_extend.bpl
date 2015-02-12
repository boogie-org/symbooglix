// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
function {:bvbuiltin "sign_extend 4"} BV4_SEXT8(bv4) : bv8;
function {:bvbuiltin "bvugt"} BV8_UGT(bv8, bv8) : bool;
procedure main(a:bv4) returns (r:bv8)
requires a == 15bv4;
{
    r := BV4_SEXT8(a);
    assert r == 255bv8;
}
