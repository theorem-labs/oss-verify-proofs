(** The builder segment of LLVMFuzzerTestOneInput (plain image, [0x12f14, 0x13f48)): role_build_contract from the
    three leaf contracts it calls. The walk is in RoleBuild/: the first piece (Pre.v: memset of the block, the
    header, the property loop's preheader), the property loop and the composition (Loop.v), one property
    (Prop*.v), one pod of a params Struct (Ent*.v for ent_build, Write.v for the inlined pod_write_ent and the
    record copy) and the end (Post.v: the top size word, the corruption, the request of the second malloc). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import memset_c memcpy_c strlen_c
  LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import Pre Loop.

Theorem role_build_holds : memset_c.memset_contract -> memcpy_c.memcpy_contract -> strlen_c.strlen_contract ->
  role_build_contract.
Proof.
  intros MSET MCPY STRL. exact (build_of_pre (pre_holds MSET) MSET MCPY STRL).
Qed.
