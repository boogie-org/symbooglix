procedure main()
{
        var a:bv8;
   entry_block:
        assert {:symbooglix_bp "entry"} true;
        goto P0, P1, P2;

   P0:
        a := 7bv8;
        assert {:symbooglix_bp "path0"} true;
        return;
   P1:
        a := 8bv8;
        assert {:symbooglix_bp "path1"} true;
        return;

   P2:
        a := 9bv8;
        assert {:symbooglix_bp "path2"} true;
        return;
}
