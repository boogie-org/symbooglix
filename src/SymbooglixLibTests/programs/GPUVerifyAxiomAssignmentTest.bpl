const {:group_id_x} group_id_x$1: bv32;

const {:group_id_x} group_id_x$2: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

// GPUVerify style of setting NDRange constants via axioms
axiom (if group_size_x == 512bv32 then 1bv1 else 0bv1) != 0bv1;
axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;
axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 256bv32 then 1bv1 else 0bv1) != 0bv1;
axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;
axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

procedure main()
{
    assert {:symbooglix_bp "check"} true;
    assert group_size_x == 512bv32;
    assert group_size_y == 1bv32;
    assert group_size_z == 1bv32;

    assert num_groups_x == 256bv32;
    assert num_groups_y == 1bv32;
    assert num_groups_z == 1bv32;
}
