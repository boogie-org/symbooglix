// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 8 %symbooglix --output-dir %t.symbooglix-out --globaldde=0 %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithUnsatisfiableUniqueAttribute 1
const unique a:int;
const unique b:int;
axiom a == b;

procedure main()
{
    return;
}
