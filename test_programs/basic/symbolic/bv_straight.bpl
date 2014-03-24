// RUN: %symbooglix %s 2>&1 | %OutputCheck %s
procedure main(p1:int, p2:bv8) returns (r:bv8);

// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);

var g:bv8;

implementation main(p1:int, p2:bv8) returns (r:bv8)
{
    var a:bv8;
    var b:bv8;
    // CHECK: SymbolicVariable: symbolic_5:bv8
    // CHECK: Assignment : r := bv8add\(symbolic_4, symbolic_5\)
    r := bv8add(a,b);
    // CHECK: Assert : bv8ugt\(bv8add\(symbolic_4, symbolic_5\), 0bv8\)
    assert bv8ugt(r, 0bv8);
}
