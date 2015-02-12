// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 2
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
procedure main(p1:int, p2:bv8) returns (r:bv8);

// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);
function {:bvbuiltin "bvsub"} bv8sub(bv8,bv8) returns(bv8);

var g:bv8;

implementation main(p1:int, p2:bv8) returns (r:bv8)
{
    var a:bv8;
    var b:bv8;
    a := 1bv8;
    b := 2bv8;
    goto BB1, BB2;

    BB1:
    r := bv8add(a,b);
    assert bv8ugt(r, 0bv8);
    return;

    BB2:
    r := bv8sub(b,a);
    assert r == 1bv8;
    return;
}
