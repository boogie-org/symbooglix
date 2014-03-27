procedure main()
{
    // FIXME: Why can't I name the entry block!
        var a:bv8;
        assert {:symbooglix_bp "entry"} true;
        goto P0, P1;

   P0:
        a := 7bv8; 
        assert {:symbooglix_bp "path0"} true;
        return;
   P1:
        a := 7bv8; 
        assert {:symbooglix_bp "path1"} true;
        return;
}
