(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_list_access.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWUb HttpRepA AWKit.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.

#[using="Type"] Lemma ListHead_spec_A : ListHead_stmt_A.
Proof.
  intros until m. intros LC NZ SZ FRG AE0 SH LLO LHI AM AL ST CLO QHI LO MI ->. unfold ListHead_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  unfold app_mem in AM. shadow_cells_lit SH.
  pose proof (rw_cells_bound asegs _ _ _ LC) as BL. cbn [cells_size csize Nat.add llist_cells] in BL.
  unfold llist_cells in LC.
  carve_frame 16%nat ST.
  step. fix_lit_store. step. fix_lit_store.
  step. if_cases K; zify_cond K; condn K. { exfalso. lia. }
  ub_align.
  step. step. step.
  step. step. step.
  achk SH 6%nat (L + 48)%Z.
  step.
  step. if_cases K2; zify_cond K2; condn K2.
  -   step. step. step. step.
    env_now AE0 MU WM.
    match goal with P : stk asegs _ lo _ |- _ => release_frame FR P q end.
    subst size. unfold ListHead_post_A. cbn [Z.eqb]. finish.
  - step. step. step.
    achk SH 1%nat (L + 8)%Z.
    step.
    step. step. step.
    env_now AE0 MU WM.
    match goal with P : stk asegs _ lo _ |- _ => release_frame FR P q end.
    unfold ListHead_post_A. destruct (Z.eqb_spec size 0); [lia|]. finish.
Qed.

#[using="Type"] Lemma ListNext_spec_A : ListNext_stmt_A.
Proof.
  intros until m. intros NC LNZ NNZ NX LR AE0 SH NLO NHI AM AL ALL ST CLO QHI LO MI -> ->. unfold ListNext_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  unfold app_mem in AM. shadow_cells_lit SH.
  pose proof (rw_cells_bound asegs _ _ _ NC) as BN. cbn [cells_size csize Nat.add node_cells] in BN.
  unfold node_cells in NC.
  carve_frame 16%nat ST.
  step. fix_lit_store. step. fix_lit_store.
  zstep.
  zstep. if_cases K; zify_cond K; condn K. { exfalso; lia. }
  zstep. if_cases K2; zify_cond K2; condn K2. { exfalso; lia. }
  zstep. ub_align.
  step. step. step.
  step. step. step.
  achk SH 1%nat (N + 8)%Z.
  zstep.
  zstep. zstep. zstep. zstep. zstep.
  change (Z.land _ nx) with (P0.H_list_access.listnext_expr nx (L + 24)). rewrite P0.H_list_access.listnext_eval by lia.
  zstep. step. step. step.
  env_now AE0 MU WM.
  match goal with P : stk asegs _ lo _ |- _ => release_frame FR P q end.
  finish.
Qed.

#[using="Type"] Lemma FreeListInit_spec_A : FreeListInit_stmt_A.
Proof.
  intros until m. intros FC NZ E1 E2 AE0 SH FLO FHI AM AL ST CLO QHI LO MI -> -> ->. unfold FreeListInit_entryA.
  a0_prologue AE0 [(FL, FL + 24); (lo, q)]%Z m.
  unfold app_mem in AM. shadow_cells_lit SH.
  pose proof (rw_cells_bound asegs _ _ _ FC) as BN. cbn [cells_size csize Nat.add] in BN.
  carve_frame 16%nat ST.
  step. fix_lit_store. step. fix_lit_store.
  step. if_cases K; zify_cond K; condn K. { exfalso; lia. }
  ub_align.
  step. step. step.
  step. step. step.
  achk SH 1%nat (FL + 8)%Z.
  sstep.
  step. step. step.
  achk SH 2%nat (FL + 16)%Z.
  sstep.
  step. step.
  achk SH 0%nat FL.
  sstep.
  step. step. step.
  achk SH 2%nat (FL + 20)%Z.
  sstep.
  zstep. step. step. step.
  env_now AE0 MU WM.
  match goal with P : stk asegs _ lo _ |- _ => release_frame FR P q end.
  finish.
Qed.

#[using="Type"] Lemma ListInit_spec_A : FreeListInit_stmt_A -> ListInit_stmt_A.
Proof.
  intros FLI. intros until m. intros LC NZ R1 R2 AE0 SH LLO LHI AM AL ST CLO QHI LO MI -> -> ->. unfold ListInit_entryA.
  a0_prologue AE0 [(L, L + 96); (lo, q)]%Z m.
  unfold app_mem in AM. shadow_cells_lit SH.
  pose proof (rw_cells_bound asegs _ _ _ LC) as BN. cbn [cells_size csize Nat.add] in BN.
  carve_frame 32%nat ST.
  step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
  step. if_cases K; zify_cond K; condn K. { exfalso; lia. }
  zstep.
  ub_align.
  step. step. step.
  step. step. step. achk SH 6%nat (L + 48)%Z. sstep.
  step. step. step. achk SH 11%nat (L + 88)%Z. sstep.
  step. step. step. achk SH 10%nat (L + 80)%Z. sstep.
  zstep. zstep. zstep.
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_take3 asegs mm L [CB 48 (firstn 48 junk); C8 (Z_to_bv 64 0)] [CB 24 (firstn 24 (firstn 32 (skipn 56 junk)))]
                [C8 (Z_to_bv 64 ffree); C8 (Z_to_bv 64 fcmp)] LC) as (LC1 & LC2 & LC3); clear LC;
    cbn [cells_size csize Nat.add] in LC2, LC3;
    replace (L + Z.of_nat 56)%Z with (L + 56)%Z in LC2 by lia;
    replace (L + Z.of_nat 56 + Z.of_nat 24)%Z with (L + 80)%Z in LC3 by lia;
    assert (SHF : rw_cells asegs mm (sh (L + 56)) (shadow_zero_cells 3))
      by (apply (shadow_zero_sub mm L 12 56 3); [exact SH| exact AL| reflexivity| lia| cbn; lia])
  end.
  env_now AE0 MU WM.
  call (FLI (L + 56)%Z 24%Z 100%Z lo).
  all: side (try (first [ eassumption | reflexivity | (unfold app_mem, A0_RT_STACK in *; lia) ])).

  step. step. step. achk SH 2%nat (L + 16)%Z. sstep.
  step. step. step. achk SH 1%nat (L + 8)%Z.
  step. step. sstep. step.
  achk SH 0%nat L. sstep.
  step. step. step. achk SH 5%nat (L + 40)%Z. sstep.
  step. step. achk SH 3%nat (L + 24)%Z. sstep.
  step. step. step. achk SH 4%nat (L + 32)%Z. sstep.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with P1 : rw_cells asegs mm L _, P2 : rw_cells asegs mm (L + 56)%Z _, P3 : rw_cells asegs mm (L + 80)%Z _ |- _ =>
      pose proof (rw_cells_put3 asegs _ L _ _ _ P1 ltac:(cbn [cells_size csize Nat.add]; replace (L + Z.of_nat 56)%Z with (L + 56)%Z by lia; exact P2)
                ltac:(cbn [cells_size csize Nat.add]; replace (L + Z.of_nat 56 + Z.of_nat 24)%Z with (L + 80)%Z by lia; exact P3)) as LCF;
      cbn [app] in LCF; clear P1 P2 P3 end end.
  step. step. step. step. step.
  env_now AE0 MU WM.
  match goal with P : stk asegs _ lo _ |- _ => release_frame FR P q end.
  unfold ListInit_post_A, llist_cells, LISTNODE_SIZEOF, FREELISTSIZE. finish.
Qed.
End W.
