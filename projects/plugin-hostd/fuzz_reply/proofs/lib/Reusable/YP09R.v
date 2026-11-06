(* CARRIED from commit d692856bfecbb98b2d89a0bba73b457c2098f96d,
   proofs/cgif/cgif_file_fuzzer/lib/YP09R.v, sha256 8687eef1896c3106d9e94709264453570e9f3081f8403bf51ba322ea71c57951 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK14 YK1b YP0m YP0e YP09.
Import ListNotations.
Open Scope Z_scope.

Definition in_rrange (E : env) (rs : smem) (a : Z) : Prop :=
  exists r, In r rs /\ base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r.

Definition accs_in_rrange (E : env) (rs : smem) (accs : list (word * nat)) : Prop :=
  forall a n k, In (a, n) accs -> (k < n)%nat -> in_rrange E rs (bv_unsigned a + Z.of_nat k).
