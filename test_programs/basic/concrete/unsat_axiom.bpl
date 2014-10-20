// RUN: %rmdir %t.symbooglix-out
// RUN: %not %symbooglix --output-dir %t.symbooglix-out %s | %OutputCheck %s
axiom true;
// CHECK-L: Terminated with unsatisfiable axiom ${CHECKFILE_ABS_PATH}:${LINE:+1}: false
axiom false;

procedure main()
{
    assert true;
}
