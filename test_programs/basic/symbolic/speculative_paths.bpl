// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 9 %symbooglix --output-dir %t.symbooglix-out --solver=DUMMY %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedSpeculativePath 2
procedure main()
{
    var c:bool;
    // Using the dummy solver should generate two speculative paths
    assert c;
}
