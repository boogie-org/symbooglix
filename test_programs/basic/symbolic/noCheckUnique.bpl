// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out --check-entry-axioms=0 --check-unique-vars=0 %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableAxiom 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0

// These contradict
// but they won't be caught
// due to flags being passed to symbooglix
axiom a == b;
const unique a:int;
const unique b:int;


procedure main()
{
    var x:int;
    x := a;

    // If we got this far the constraint set is now inconsitent
    // Symbooglix will behave very strangely now (both these asserts
    // will pass)
    //
    // This is why it is important that the axioms, entry requires and
    // unique constraint be satisfiable before execution begins.
    // using flags like --check-unique-vars=0 and --check-entry-axioms=0
    // should be used with care.
    assert a == b;
    assert a != b;
}
