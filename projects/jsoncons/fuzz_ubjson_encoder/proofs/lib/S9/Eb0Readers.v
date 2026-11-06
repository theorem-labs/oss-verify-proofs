(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r65f44_65f5c Eb0_code_r67bcc_67d3c Eb0_code_r6bbd4_6bc28 Eb0_code_r60dd4_61420.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX. Context {fx : PropExec.FPState}.

Definition only_a0 (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> getr regs' r = getr regs r.

#[local] Ltac post_only_a0 :=
  intros r Hr; gres; try reflexivity;
  repeat (rewrite getr_other by (exact Hr || (symmetry; exact Hr) || reg_neq_tac)); reflexivity.

Lemma asan_inited_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x146dd8 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x81380 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_81330 D_81330.
    mlb F_81334 D_81334 (0x146dd8 : word) HM.
    stepfence F_81338 D_81338.
    stepn F_8133c D_8133c.
    stepn F_81340 D_81340.
    stepret F_81344 D_81344 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

Lemma get_malloc_context_size_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x146dfc : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 30)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x83018 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 30 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_82fc8 D_82fc8.
    mlw F_82fcc D_82fcc (0x146dfc : word) HM.
    stepfence F_82fd0 D_82fd0.
    stepret F_82fd4 D_82fd4 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

Lemma rss_limit_exceeded_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1c8362 : word) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps ASEGS (mkst regs (0x87048 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_86ff8 D_86ff8.
    mlb F_86ffc D_86ffc (0x1c8362 : word) HM.
    stepn F_87000 D_87000.
    stepret F_87004 D_87004 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

Lemma allocator_may_return_null_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1c8361 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x87020 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_86fd0 D_86fd0.
    mlb F_86fd4 D_86fd4 (0x1c8361 : word) HM.
    stepn F_86fd8 D_86fd8.
    stepret F_86fdc D_86fdc ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

Lemma can_poison_memory_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x14595c : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x7bcd0 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_7bc80 D_7bc80.
    mlb F_7bc84 D_7bc84 (0x14595c : word) HM.
    stepfence F_7bc88 D_7bc88.
    stepn F_7bc8c D_7bc8c.
    stepret F_7bc90 D_7bc90 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

End FPX.
