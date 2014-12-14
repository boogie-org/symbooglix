// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 1 %symbooglix --output-dir %t.symbooglix-out %s 2>&1 | %OutputCheck %s
procedure main(p1:int, p2:bv8) returns (r:bv8);
requires g == 0bv8; // Required to prevent GlobalDDE from removing "g"

// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);

// CHECK-L: Creating Symbolic ~sb_g_0:bv8
var g:bv8;

implementation main(p1:int, p2:bv8) returns (r:bv8)
{
    var a:bv8;
    var b:bv8;
    // CHECK-L: Creating Symbolic ~sb_b_0:bv8
    // CHECK-L: Assignment : r := bv8add(~sb_a_0, ~sb_b_0)
    r := bv8add(a,b);
    // CHECK-L: Assert : bv8ugt(bv8add(~sb_a_0, ~sb_b_0), 0bv8)
    assert bv8ugt(r, 0bv8);
}
