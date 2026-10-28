(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r65f44_65f5c_b Ba0_code_r67bcc_67d3c_b Ba0_code_r6bbd4_6bc28_b Ba0_code_r60dd4_61420_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition only_a0 (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> getr regs' r = getr regs r.

#[local] Ltac post_only_a0 :=
  intros r Hr; gres; try reflexivity;
  repeat (rewrite getr_other by (exact Hr || (symmetry; exact Hr) || reg_neq_tac)); reflexivity.

(* [comment removed for export] *)
Lemma asan_inited_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x140918 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x801d4 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_7fdbc D_7fdbc.                                  (* [comment removed for export] *)
    mlb F_7fdc0 D_7fdc0 (0x140918 : word) HM.                (* [comment removed for export] *)
    stepfence F_7fdc4 D_7fdc4.                              (* [comment removed for export] *)
    stepn F_7fdc8 D_7fdc8.                                  (* [comment removed for export] *)
    stepn F_7fdcc D_7fdcc.                                  (* [comment removed for export] *)
    stepret F_7fdd0 D_7fdd0 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.


(* [comment removed for export] *)
Lemma get_malloc_context_size_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x14093c : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 30)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x81e6c : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 30 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_81a54 D_81a54.                                  (* [comment removed for export] *)
    mlw F_81a58 D_81a58 (0x14093c : word) HM.                (* [comment removed for export] *)
    stepfence F_81a5c D_81a5c.                              (* [comment removed for export] *)
    stepret F_81a60 D_81a60 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma rss_limit_exceeded_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1c1ea2 : word) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps ASEGS (mkst regs (0x85e9c : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_85a84 D_85a84.
    mlb F_85a88 D_85a88 (0x1c1ea2 : word) HM.
    stepn F_85a8c D_85a8c.
    stepret F_85a90 D_85a90 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma allocator_may_return_null_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x1c1ea1 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x85e74 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_85a5c D_85a5c.
    mlb F_85a60 D_85a60 (0x1c1ea1 : word) HM.
    stepn F_85a64 D_85a64.
    stepret F_85a68 D_85a68 ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

(* [comment removed for export] *)
Lemma can_poison_memory_run : forall regs (M rom : word -> option byte) ret,
  getr regs 1 = ret -> ret_ok ret ->
  rdn ASEGS M (0x13f49c : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x7ab24 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ only_a0 regs regs'.
Proof.
  intros regs M rom ret H1 Hret HM.
  eexists. split.
  - stepn F_7a70c D_7a70c.
    mlb F_7a710 D_7a710 (0x13f49c : word) HM.
    stepfence F_7a714 D_7a714.
    stepn F_7a718 D_7a718.
    stepret F_7a71c D_7a71c ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.

End FPX.
