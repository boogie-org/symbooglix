// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck %s
procedure main(p1:int, p2:bv8) returns (r:bv8);

// Bitvector functions
function {:bvbuiltin "bvadd"} BVADD8(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvugt"} BVUGT8(bv8,bv8) returns(bool);

var g:bv8;

implementation main(p1:int, p2:bv8) returns (r:bv8)
{
    var a:bv8;
    var b:bv8;
    // CHECK: Assignment : r := BVADD8\(~sb_a_0, ~sb_b_0\)
    r := BVADD8(a,b);
    // CHECK: Assume : BVADD8\(~sb_a_0, ~sb_b_0\) == 1bv8
    assume  r == 1bv8;
    // CHECK: Assert : BVUGT8\(BVADD8\(~sb_a_0, ~sb_b_0\), 0bv8\)
    assert BVUGT8(r, 0bv8); // This is feasible so we should carry on executing
    // CHECK: Assert : true
    assert true;
}
