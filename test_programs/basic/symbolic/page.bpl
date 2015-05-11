// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0


/* Memory is an 8 bit address space of bytes.
Providing 2^4 = 16 'pages' of 16 bytes each.
*/

type Byte = bv8;
type Addr = bv8;
type Ram = [Addr] Byte;
type Page = bv4;

var mem : Ram;

/* Zero a page, leave others unchanged. */
procedure zeroPage(page : Page);
modifies mem;
// Zero bytes of page
ensures (forall a : Addr :: a[8:4] == page ==> mem[a] == 0bv8);
// Other pages unchanged.
ensures (forall a : Addr :: a[8:4] != page ==> mem[a] == old(mem)[a]);

procedure main()
modifies mem;
{
    call zeroPage(2bv4);

    // test page is zeroed
    assert (forall a: Addr :: a[8:4] == 2bv4 ==> mem[a] == 0bv8);
}
