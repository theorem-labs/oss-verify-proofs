(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  As0_code_660d4_660ec As0_code_67d5c_67ecc As0_code_6bd64_6bdb8 As0_code_60f64_615b0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition only_a0 (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> getr regs' r = getr regs r.

#[local] Ltac post_only_a0 :=
  intros r Hr; gres; try reflexivity;
  repeat (rewrite getr_other by (exact Hr || (symmetry; exact Hr) || reg_neq_tac)); reflexivity.

(* [comment removed for export] *)
Lemma asan_inited_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0xde818 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x660d4 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_660d4 D_660d4.                                  (* [comment removed for export] *)
    mlb F_660d8 D_660d8 (0xde818 : word) HM.                (* [comment removed for export] *)
    stepfence F_660dc D_660dc.                              (* [comment removed for export] *)
    stepn F_660e0 D_660e0.                                  (* [comment removed for export] *)
    stepn F_660e4 D_660e4.                                  (* [comment removed for export] *)
    stepret F_660e8 D_660e8 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.


(* [comment removed for export] *)
Lemma get_malloc_context_size_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0xde83c : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 30)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x67d6c : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 30 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_67d6c D_67d6c.                                  (* [comment removed for export] *)
    mlw F_67d70 D_67d70 (0xde83c : word) HM.                (* [comment removed for export] *)
    stepfence F_67d74 D_67d74.                              (* [comment removed for export] *)
    stepret F_67d78 D_67d78 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma rss_limit_exceeded_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x15fda2 : word) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps ASEGS (mkst regs (0x6bd9c : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_6bd9c D_6bd9c.
    mlb F_6bda0 D_6bda0 (0x15fda2 : word) HM.
    stepn F_6bda4 D_6bda4.
    stepret F_6bda8 D_6bda8 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma allocator_may_return_null_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x15fda1 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x6bd74 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_6bd74 D_6bd74.
    mlb F_6bd78 D_6bd78 (0x15fda1 : word) HM.
    stepn F_6bd7c D_6bd7c.
    stepret F_6bd80 D_6bd80 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma can_poison_memory_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0xdd39c : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x60f64 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_60f64 D_60f64.
    mlb F_60f68 D_60f68 (0xdd39c : word) HM.
    stepfence F_60f6c D_60f6c.
    stepn F_60f70 D_60f70.
    stepret F_60f74 D_60f74 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

End FPX.
