procedure main()
{
    // FIXME: Why can't I name the entry block!
        var a:bv8;
        assert {:symbooglix_bp "entry"} true;
        goto NEXT;

   NEXT:
        a := 7bv8; 
        assert {:symbooglix_bp "reached"} true;
}
