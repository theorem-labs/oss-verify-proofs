(* check_read_kit_seg_pa: the assumptions of the two allocator-level lemmas of the image-A walk of check_read
   (lib/A/Prog/check_read_kit_seg.v). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import check_read_kit_segs check_read_kit_seg.

Check (crd_stack_malloc_at_ok : crd_stack_malloc_at_stmt).
Check (crd_flag_free_ok : crd_flag_free_stmt).
Print Assumptions crd_stack_malloc_at_ok.
Print Assumptions crd_flag_free_ok.
