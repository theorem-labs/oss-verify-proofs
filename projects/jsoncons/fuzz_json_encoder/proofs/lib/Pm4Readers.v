(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  Pm4_code_83000_84000 Pm4_code_88000_89000 Pm4_code_8a000_8b000 Pm4_code_8e000_8f000      .
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
  rdn ASEGS M (0x16abd8 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x88780 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_88730 D_88730.                                  (* [comment removed for export] *)
    mlb F_88734 D_88734 (0x16abd8 : word) HM.                (* [comment removed for export] *)
    stepfence F_88738 D_88738.                              (* [comment removed for export] *)
    stepn F_8873c D_8873c.                                  (* [comment removed for export] *)
    stepn F_88740 D_88740.                                  (* [comment removed for export] *)
    stepret F_88744 D_88744 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.


(* [comment removed for export] *)
Lemma get_malloc_context_size_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x16abfc : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 30)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x8a418 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 30 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_8a3c8 D_8a3c8.                                  (* [comment removed for export] *)
    mlw F_8a3cc D_8a3cc (0x16abfc : word) HM.                (* [comment removed for export] *)
    stepfence F_8a3d0 D_8a3d0.                              (* [comment removed for export] *)
    stepret F_8a3d4 D_8a3d4 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma rss_limit_exceeded_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1ec162 : word) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps ASEGS (mkst regs (0x8e448 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_8e3f8 D_8e3f8.
    mlb F_8e3fc D_8e3fc (0x1ec162 : word) HM.
    stepn F_8e400 D_8e400.
    stepret F_8e404 D_8e404 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma allocator_may_return_null_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1ec161 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x8e420 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_8e3d0 D_8e3d0.
    mlb F_8e3d4 D_8e3d4 (0x1ec161 : word) HM.
    stepn F_8e3d8 D_8e3d8.
    stepret F_8e3dc D_8e3dc ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma can_poison_memory_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x16975c : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x830d0 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_83080 D_83080.
    mlb F_83084 D_83084 (0x16975c : word) HM.
    stepfence F_83088 D_83088.
    stepn F_8308c D_8308c.
    stepret F_83090 D_83090 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

End FPX.
