// RUN: %symbooglix %s --fold-constants=0 --print-instr 2>&1 | %OutputCheck %s
procedure main(p1:int, p2:bv8) returns (r:bv8);

// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);

var g:bv8;

implementation main(p1:int, p2:bv8) returns (r:bv8)
{
    var a:bv8;
    var b:bv8;
    // CHECK: InstructionPrinter: a := 1bv8;
    a := 1bv8;
    // CHECK: InstructionPrinter: b := 2bv8;
    b := 2bv8;
    // CHECK-L: InstructionPrinter: r := bv8add(a, b);
    // CHECK-L: Assignment : r := bv8add(1bv8, 2bv8)
    r := bv8add(a,b);
    assert bv8ugt(r, 0bv8);
}
