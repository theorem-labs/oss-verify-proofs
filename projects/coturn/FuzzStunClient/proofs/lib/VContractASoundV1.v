(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VStepMem VStepMemSound VCert VContract VDriver VSound VContractSound VContractSound2 VState2 VStepMem2 VCert2 VContract2 VGamma2 VStepMem2SoundA VContract2Iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Section V1Lift.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO2 : params_ok2 SEGS P.
  Let P1 := p1 P.
  Let E1 := ev1 E.

  (* [comment removed for export] *)
  Definition globs_kept (c : contract) : Prop :=
    forall A spoff A1 v x, contract_apply P1 CI c A spoff = CROk A1 v -> In x (vs_globs A1) -> In x (vs_globs A).

  Theorem contract_post2_of_v1 (c : contract) (tgt : Z) :
    (forall m0, VContractSound2.contract_post SEGS P1 E1 m0 rom CI c tgt) ->
    globs_kept c ->
    contract_post2 SEGS P E mem0 rom CI (CV1 c) tgt.
  Proof.
    intros POST GK A spoff l nu regs mem ra Happ HG2 MEMO Hsp HK Hret Hra.
    cbn [contract_apply2] in Happ. unfold lift_cres in Happ. fold P1 in Happ, HK.
    destruct (contract_apply P1 CI c (v1 A) spoff) as [A1 v| |m] eqn:E1c; try discriminate.
    unfold CR2Ok in Happ. injection Happ as <-.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    destruct (POST (zpatch P E mem0 mem) (v1 A) spoff A1 v nu regs mem ra E1c HG1 Hsp HK Hret Hra)
      as (regs' & mem' & nu' & RUN & GB & RA' & EXT & LE & FM).
    set (B := contract_frame c A1 spoff v) in *.
    assert (GLB : globs_ok2 P (with_v1 A B)).
    { unfold globs_ok2. cbn [v1 with_v1]. intros AM a w v' Hin.
      destruct (contract_frame_shape c A1 spoff v) as (_ & FG & _).
      unfold B in Hin. rewrite FG in Hin.
      exact (GL2 AM a w v' (GK _ _ _ _ _ E1c Hin)). }
    destruct (gamma2_lift SEGS P E mem0 PO2 A B nu nu' regs regs' mem mem' HG2 GB EXT LE FM GLB (or_intror MEMO))
      as (G2 & FM2 & FS).
    exists (with_v1 A A1), v, regs', mem', nu'.
    split; [left; reflexivity|].
    split; [exact RUN|].
    change (contract_frame2 (CV1 c) (with_v1 A A1) spoff v) with (with_v1 A B).
    split; [exact G2|]. split; [exact RA'|]. split; [exact EXT|]. split; [exact LE|]. split; [exact FM2|exact FS].
  Qed.

  Theorem contract_dead2_of_v1 (c : contract) :
    (forall m0, VContractSound2.contract_dead SEGS P1 E1 m0 CI c) ->
    contract_dead2 SEGS P E mem0 CI (CV1 c).
  Proof.
    intros DEAD A spoff nu regs mem Happ HG2.
    cbn [contract_apply2] in Happ. unfold lift_cres in Happ. fold P1 in Happ.
    destruct (contract_apply P1 CI c (v1 A) spoff) as [A1 v| |m] eqn:E1c; try discriminate.
    exact (DEAD (zpatch P E mem0 mem) (v1 A) spoff nu regs mem E1c (proj1 HG2)).
  Qed.

  Lemma fresh_lin_globs A b : vs_globs (snd (fresh_lin A b)) = vs_globs A.
  Proof. unfold fresh_lin. destruct b as [[lo|] [hi|]]; try destruct (lo =? hi); reflexivity. Qed.

  Lemma afresh_globs A b x : In x (vs_globs (snd (afresh A b))) -> In x (vs_globs A).
  Proof. unfold afresh. pose proof (fresh_lin_globs A b) as H. destruct (fresh_lin A b) as [e A']. cbn [snd] in *. rewrite H. exact (fun h => h). Qed.

  (* [comment removed for export] *)
  Lemma globs_kept_tolower : globs_kept C_tolower.
  Proof.
    intros A spoff A1 v x Happ Hin. cbn [contract_apply] in Happ. unfold c_tolower, getA in Happ.
    destruct (get_reg A A0r) as [e|]; [|discriminate].
    destruct (dead_lin A e); [discriminate|].
    destruct (bnd A e) as [[lo|] [hi|]]; try discriminate.
    destruct (Z.ltb lo 0 || Z.ltb 255 hi); [discriminate|].
    destruct (lin_is_const e).
    - injection Happ as <- <-. exact Hin.
    - pose proof (afresh_globs A (Some (if 65 <=? lo then Z.min lo 97 else lo), Some (if 65 <=? hi then Z.max hi (Z.min (hi + 32) 122) else hi)) x) as AG.
      destruct (afresh A _) as [v0 A0]. injection Happ as <- <-. exact (AG Hin).
  Qed.

  Lemma globs_kept_strtoul : globs_kept C_strtoul.
  Proof.
    intros A spoff A1 v x Happ Hin. cbn [contract_apply] in Happ. unfold c_strtoul, getA in Happ.
    destruct (get_reg A A1r) as [ee|]; [|discriminate].
    destruct (get_reg A A2r) as [be|]; [|discriminate].
    destruct (negb (lin_is_const ee && (lc ee =? 0))); [discriminate|].
    destruct (negb (lin_is_const be && (lc be =? 10))); [discriminate|].
    destruct (get_reg A A0r) as [pe|]; [|discriminate].
    destruct (negb (is_sp_rel pe)); [discriminate|].
    destruct (dead_lin A (lsub pe (lsym SP0))); [discriminate|].
    destruct (bnd A (lsub pe (lsym SP0))) as [[plo|] [phi|]]; try discriminate.
    destruct (min_opt _) as [stop|]; [|discriminate].
    destruct (0 <? stop + 1); [discriminate|].
    destruct (plo <? spoff); [discriminate|].
    destruct (spoff - STRTOUL_FRAME <? - vp_frame P1); [discriminate|].
    destruct (negb (in_cells (vp_wcells P1) (ci_errno CI) 4)); [discriminate|].
    destruct (negb _); [discriminate|].
    match type of Happ with context [afresh ?A2 ?b] => pose proof (afresh_globs A2 b x) as AG; destruct (afresh A2 b) as [v0 A0] end.
    injection Happ as <- <-. specialize (AG Hin). unfold set_globs in AG. cbn [vs_globs] in AG. exact (cm_kill_sub _ _ _ _ AG).
  Qed.
End V1Lift.
