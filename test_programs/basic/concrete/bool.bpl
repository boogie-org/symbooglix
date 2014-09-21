// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s --print-instr 2>&1 | %OutputCheck %s
procedure main(p1:bool, p2:bool) returns (r:bool)
// CHECK-L: Concretising  p1 := true
// CHECK-L: Concretising  p2 := false
requires (p1 == true);
requires (p2 == false);
{
    // Basically just xor
    // CHECK-L: InstructionPrinter: r := (p1 || p2) && !(p1 && p2)
    // CHECK-L: Assignment : r := true
    r := (p1 || p2) && !(p1 && p2);
    assert r == true;
}
