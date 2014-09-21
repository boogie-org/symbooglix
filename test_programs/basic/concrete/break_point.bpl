// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s --print-instr 2>&1 | %OutputCheck %s
procedure main(p1:int, p2:bv8) returns (r:bv8);

// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);

var g:bv8;

implementation main(p1:int, p2:bv8) returns (r:bv8)
{
    var a:bv8;
    // CHECK: Hit break point first
    assert {:symbooglix_bp "first"} true;
    a := 1bv8;
    // CHECK: Hit break point second
    assert {:symbooglix_bp "second"} true;
}
