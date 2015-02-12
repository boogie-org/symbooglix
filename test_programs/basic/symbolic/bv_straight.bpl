// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 2 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 1
procedure main(p1:int, p2:bv8) returns (r:bv8);

// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);


implementation main(p1:int, p2:bv8) returns (r:bv8)
{
    var a:bv8;
    var b:bv8;
    r := bv8add(a,b);
    assert bv8ugt(r, 0bv8);
}
