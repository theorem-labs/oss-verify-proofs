(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r65f44_65f5c Ea0_code_r67bcc_67d3c Ea0_code_r6bbd4_6bc28 Ea0_code_r60dd4_61420.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX. Context {fx : PropExec.FPState}.

Definition only_a0 (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> getr regs' r = getr regs r.

#[local] Ltac post_only_a0 :=
  intros r Hr; gres; try reflexivity;
  repeat (rewrite getr_other by (exact Hr || (symmetry; exact Hr) || reg_neq_tac)); reflexivity.

Lemma asan_inited_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1426d8 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x80b58 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_80b08 D_80b08.
    mlb F_80b0c D_80b0c (0x1426d8 : word) HM.
    stepfence F_80b10 D_80b10.
    stepn F_80b14 D_80b14.
    stepn F_80b18 D_80b18.
    stepret F_80b1c D_80b1c ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

Lemma get_malloc_context_size_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1426fc : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 30)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x827f0 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 30 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_827a0 D_827a0.
    mlw F_827a4 D_827a4 (0x1426fc : word) HM.
    stepfence F_827a8 D_827a8.
    stepret F_827ac D_827ac ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

Lemma rss_limit_exceeded_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1c3c62 : word) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps ASEGS (mkst regs (0x86820 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_867d0 D_867d0.
    mlb F_867d4 D_867d4 (0x1c3c62 : word) HM.
    stepn F_867d8 D_867d8.
    stepret F_867dc D_867dc ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

Lemma allocator_may_return_null_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1c3c61 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x867f8 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_867a8 D_867a8.
    mlb F_867ac D_867ac (0x1c3c61 : word) HM.
    stepn F_867b0 D_867b0.
    stepret F_867b4 D_867b4 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

Lemma can_poison_memory_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x14125c : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x7b4a8 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_7b458 D_7b458.
    mlb F_7b45c D_7b45c (0x14125c : word) HM.
    stepfence F_7b460 D_7b460.
    stepn F_7b464 D_7b464.
    stepret F_7b468 D_7b468 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

End FPX.
