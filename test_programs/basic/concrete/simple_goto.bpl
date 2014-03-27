// RUN: %symbooglix %s /useInstructionPrinter 2>&1 | %OutputCheck %s
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
    // CHECK: InstructionPrinter: a := 1bv8;
    a := 1bv8;
    // CHECK: InstructionPrinter: b := 2bv8;
    b := 2bv8;
    goto BB1, BB2; // This test is fragile, it depends on what state scheduler we use

    BB1:
    // CHECK: InstructionPrinter: r := bv8add\(a, b\);
    // CHECK: Assignment : r := bv8add\(1bv8, 2bv8\)
    r := bv8add(a,b);
    assert bv8ugt(r, 0bv8);
    return;

    BB2:
    // CHECK: InstructionPrinter: r := bv8sub\(b, a\);
    // CHECK: Assignment : r := bv8sub\(2bv8, 1bv8\)
    r := bv8sub(b,a);
    assert r == 1bv8;
    return;
}
