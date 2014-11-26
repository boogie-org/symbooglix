// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck %s
procedure main(p1:int, p2:bv8) returns (r:bv8);

// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);

var g:bv8;

implementation main(p1:int, p2:bv8) returns (r:bv8)
{
    var a:bv8;
    var b:bv8;
    // CHECK: Assignment : r := bv8add\(~sb_a_0, ~sb_b_0\)
    r := bv8add(a,b);
    // CHECK: Assume : bv8add\(~sb_a_0, ~sb_b_0\) == 1bv8
    assume  r == 1bv8;
    // CHECK: Assert : bv8ugt\(bv8add\(~sb_a_0, ~sb_b_0\), 0bv8\)
    assert bv8ugt(r, 0bv8); // This is feasible so we should carry on executing
    // CHECK: Assert : true
    assert true;
}
