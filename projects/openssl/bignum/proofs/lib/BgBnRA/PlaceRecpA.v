(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS Tac. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout RT_iface RT_client_kit D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA AsStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pl_place_recp (PL : placement) (an : Z) : placement :=
  pl_set_recp (pl_set (pl_set PL RRecpN (Some (PFrame an))) RRecpNr (Some (PFrame (an + 24)))) (Some (an + 48)).

Definition st_recp_init (st : ST) : ST := setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) (set_recp 0 0 st)).

Lemma pl_bn_place_recp_N : forall PL an, pl_bn (pl_place_recp PL an) RRecpN = Some (PFrame an).
Proof. reflexivity. Qed.
Lemma pl_bn_place_recp_Nr : forall PL an, pl_bn (pl_place_recp PL an) RRecpNr = Some (PFrame (an + 24)).
Proof. reflexivity. Qed.
Lemma pl_bn_place_recp_other : forall PL an r, r <> RRecpN -> r <> RRecpNr -> pl_bn (pl_place_recp PL an) r = pl_bn PL r.
Proof.
  intros PL an r N1 N2. unfold pl_place_recp. cbn [pl_bn pl_set_recp pl_set].
  replace (r =? RRecpNr)%nat with false by (symmetry; apply Nat.eqb_neq; exact N2).
  replace (r =? RRecpN)%nat with false by (symmetry; apply Nat.eqb_neq; exact N1). reflexivity.
Qed.
Lemma pl_of_place_recp_other : forall PL an r, r <> RRecpN -> r <> RRecpNr -> pl_of (pl_place_recp PL an) r = pl_of PL r.
Proof. intros PL an r N1 N2. unfold pl_place_recp. rewrite pl_of_set_recp, !pl_of_set_other by assumption. reflexivity. Qed.
Lemma pl_of_place_recp_N : forall PL an, pl_of (pl_place_recp PL an) RRecpN = Some (PFrame an).
Proof. reflexivity. Qed.
Lemma pl_of_place_recp_Nr : forall PL an, pl_of (pl_place_recp PL an) RRecpNr = Some (PFrame (an + 24)).
Proof. reflexivity. Qed.

Lemma ref_at_place_recp : forall st OW PL an r a, r <> RRecpN -> r <> RRecpNr ->
  (ref_at st OW (pl_place_recp PL an) r a <-> ref_at st OW PL r a).
Proof.
  intros st OW PL an r a N1 N2. unfold ref_at. destruct (r <? NFIX)%nat; [|reflexivity].
  rewrite pl_of_place_recp_other by assumption. reflexivity.
Qed.

Lemma ref_at_not_recp : forall st OW PL r a, pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> ref_at st OW PL r a -> r <> RRecpN /\ r <> RRecpNr.
Proof.
  intros st OW PL r a E1 E2 H. split; intros ->; unfold ref_at in H; cbn in H; destruct H as (p & Ep & _); unfold pl_of in Ep; cbn in Ep;
    [rewrite E1 in Ep| rewrite E2 in Ep]; discriminate Ep.
Qed.

Lemma recp_at_place : forall PL an, recp_at (pl_place_recp PL an) an.
Proof. intros PL an. split; [reflexivity|]. split; reflexivity. Qed.

Lemma pl_frames_place_recp_In : forall PL an iv, In iv (pl_frames (pl_place_recp PL an)) ->
  iv = (an, an + 24) \/ iv = (an + 24, an + 48) \/ iv = (an + 48, an + 60) \/ In iv (pl_frames PL).
Proof.
  intros PL an iv H. unfold pl_place_recp in H. apply pl_frames_set_recp_In in H. destruct H as [[<-|[]]|H].
  - right; right; left. unfold RECP_SC_SZ. f_equal. lia.
  - apply pl_frames_set_In in H. destruct H as [[<-|[]]|H].
    + right; left. unfold BN_STRUCT_SZ. f_equal. lia.
    + apply pl_frames_set_In in H. destruct H as [[<-|[]]|H]; [left; unfold BN_STRUCT_SZ; reflexivity| right; right; right; exact H].
Qed.

Lemma xw_place_recp : forall PL an x, rin_ivs (XW (pl_place_recp PL an)) x -> rin_ivs (XW PL) x \/ an <= x < an + 60.
Proof.
  intros PL an x H. unfold XW in *. apply rin_ivs_app in H. destruct H as [H|H]; [left; apply rin_ivs_app; left; exact H|].
  apply rin_ivs_In in H. destruct H as (iv & Hin & Hx). apply pl_frames_place_recp_In in Hin.
  destruct Hin as [->|[->|[->|Hin]]]; cbn [fst snd] in Hx; try (right; lia).
  left. apply rin_ivs_app. right. apply rin_ivs_In. exists iv. split; assumption.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma frames_ok_place_recp : forall LB PL an SPX BX b,
  frames_ok LB PL SPX BX -> blk_addr b <= an -> an + 60 <= blk_addr b + blk_size b -> frames_ok (b :: LB) (pl_place_recp PL an) SPX BX.
Proof.
  intros LB PL an SPX BX b (PF & H2) B1 B2. split; [| exact H2].
  intros iv Hiv. apply pl_frames_place_recp_In in Hiv. destruct Hiv as [->|[->|[->|Hin]]]; cbn [fst snd];
    try (exists b; split; [left; reflexivity | lia]).
  destruct (PF iv Hin) as (b' & Hb' & R). exists b'. split; [right; exact Hb' | exact R].
Qed.

Lemma frames_al_place_recp : forall PL an, frames_al PL -> an mod 8 = 0 -> frames_al (pl_place_recp PL an).
Proof.
  intros PL an FAL A8 iv Hiv. apply pl_frames_place_recp_In in Hiv. destruct Hiv as [->|[->|[->|Hin]]]; cbn [fst];
    [exact A8 | clear - A8; Z.div_mod_to_equations; lia | clear - A8; Z.div_mod_to_equations; lia | exact (FAL iv Hin)].
Qed.

Lemma frames_lb_place_recp : forall LB PL an b,
  frames_lb PL LB -> an mod 8 = 0 -> blk_addr b <= an -> an + 60 <= blk_addr b + blk_size b -> frames_lb (pl_place_recp PL an) (b :: LB).
Proof.
  intros LB PL an b NOFR A8 B1 B2. split; [| exact (frames_al_place_recp PL an (proj2 NOFR) A8)].
  assert (FROK : frames_ok LB PL ACEIL 0) by (apply frames_lb_ok; [exact NOFR | lia | lia]).
  exact (proj1 (frames_ok_place_recp LB PL an ACEIL 0 b FROK B1 B2)).
Qed.

Lemma pl_ids_place_recp : forall PL an, pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> pl_ids (pl_place_recp PL an) = pl_ids PL.
Proof.
  intros PL an E1 E2. unfold pl_ids. cbn [pl_ctx pl_mont pl_place_recp pl_set_recp pl_set]. f_equal.
  assert (G : forall n, pl_bn_ids (pl_place_recp PL an) n = pl_bn_ids PL n).
  { induction n as [|n IH]; cbn [pl_bn_ids]; [reflexivity|]. rewrite IH. f_equal.
    destruct (Nat.eq_dec n RRecpN) as [->|N1]; [rewrite pl_bn_place_recp_N, E1; reflexivity|].
    destruct (Nat.eq_dec n RRecpNr) as [->|N2]; [rewrite pl_bn_place_recp_Nr, E2; reflexivity|].
    rewrite pl_bn_place_recp_other by assumption. reflexivity. }
  apply G.
Qed.

Theorem lib_state_place_recp : forall cxo hs st m OW PL EA an,
  lib_state_hc cxo hs st m OW PL EA -> pl_wf (pl_place_recp PL an) ->
  pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> pl_recp PL = None ->
  rw_cells bgasegs m an (bn_cells 0 (bn_nil 0)) -> rw_cells bgasegs m (an + 24) (bn_cells 0 (bn_nil 0)) ->
  rw_cells bgasegs m (an + 48) [C4 (wz 0); C4 (wz 0); C4 (wz 0)] ->
  lib_state_hc cxo hs (st_recp_init st) m OW (pl_place_recp PL an) EA.
Proof.
  intros cxo hs st m OW PL EA an (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) PWF1 E1 E2 E3 C1 C2 C3.
  assert (G8 : getbn RRecpN st = bn_nil 0) by (apply M2; [unfold RRecpN, NFIX; lia| exact E1]).
  assert (G9 : getbn RRecpNr st = bn_nil 0) by (apply M2; [unfold RRecpNr, NFIX; lia| exact E2]).
  assert (EST : st_recp_init st = set_recp 0 0 st).
  { unfold st_recp_init.
    replace (setbn RRecpN (bn_nil 0) (set_recp 0 0 st)) with (set_recp 0 0 st).
    - rewrite <- G9 at 1. change (getbn RRecpNr st) with (getbn RRecpNr (set_recp 0 0 st)). apply setbn_getbn_id.
    - rewrite <- G8 at 1. change (getbn RRecpN st) with (getbn RRecpN (set_recp 0 0 st)). symmetry. apply setbn_getbn_id. }
  rewrite EST.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [exact WF|]. split; [exact PWF1|].
  split. { unfold ids_ok, all_ids in *. rewrite pl_ids_place_recp by assumption. exact IDS. }
  split; [|split; [|split; [|split]]].
  - intros r p Hr Ep.
    destruct (Nat.eq_dec r RRecpN) as [->|N1].
    { rewrite pl_of_place_recp_N in Ep. injection Ep as <-. split; [exact I|]. right. cbn [place_addr].
      change (getbn RRecpN (set_recp 0 0 st)) with (getbn RRecpN st). rewrite G8. exists 0. split; [exact C1|]. cbn. split; reflexivity. }
    destruct (Nat.eq_dec r RRecpNr) as [->|N2].
    { rewrite pl_of_place_recp_Nr in Ep. injection Ep as <-. split; [exact I|]. right. cbn [place_addr].
      change (getbn RRecpNr (set_recp 0 0 st)) with (getbn RRecpNr st). rewrite G9. exists 0. split; [exact C2|]. cbn. split; reflexivity. }
    rewrite pl_of_place_recp_other in Ep by assumption. destruct (M1 r p Hr Ep) as [PO HR]. split; [exact PO|].
    change (getbn r (set_recp 0 0 st)) with (getbn r st). unfold holeR in *. rewrite pl_of_place_recp_other by assumption. exact HR.
  - intros r Hr Ep.
    destruct (Nat.eq_dec r RRecpN) as [->|N1]; [rewrite pl_of_place_recp_N in Ep; discriminate Ep|].
    destruct (Nat.eq_dec r RRecpNr) as [->|N2]; [rewrite pl_of_place_recp_Nr in Ep; discriminate Ep|].
    rewrite pl_of_place_recp_other in Ep by assumption. exact (M2 r Hr Ep).
  - change (pl_ctx (pl_place_recp PL an)) with (pl_ctx PL). destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hin (Hs & Ia & HL & HCX & HIT)]. split; [exact Hin|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a b i [Hh|HR]; [left; exact Hh| right; exact HR].
  - change (pl_mont (pl_place_recp PL an)) with (pl_mont PL). destruct (pl_mont PL) as [[am qm]|]; [|exact I]. exact M4.
  - cbn [pl_recp pl_place_recp pl_set_recp]. exact C3.
Qed.

Theorem lib_state_unplace_recp : forall cxo hs hs' st m OW PL EA an x y,
  lib_state_hc cxo hs st m OW (pl_place_recp PL an) EA -> pl_wf PL ->
  pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> pl_recp PL = None ->
  getbn RRecpN st = bn_nil 0 -> getbn RRecpNr st = bn_nil 0 ->
  (forall r, In r hs -> r = RRecpN \/ r = RRecpNr \/ In r hs') ->
  lib_state_hc cxo hs' (set_recp x y st) m OW PL EA.
Proof.
  intros cxo hs hs' st m OW PL EA an x y (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) PWF0 E1 E2 E3 G8 G9 HH.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [exact WF|]. split; [exact PWF0|].
  split. { unfold ids_ok, all_ids in *. rewrite pl_ids_place_recp in IDS by assumption. exact IDS. }
  split; [|split; [|split; [|split]]].
  - intros r p Hr Ep. change (getbn r (set_recp x y st)) with (getbn r st).
    assert (N1 : r <> RRecpN).
    { intros ->. unfold pl_of in Ep. cbn in Ep. rewrite E1 in Ep. discriminate Ep. }
    assert (N2 : r <> RRecpNr).
    { intros ->. unfold pl_of in Ep. cbn in Ep. rewrite E2 in Ep. discriminate Ep. }
    rewrite <- (pl_of_place_recp_other PL an r N1 N2) in Ep. destruct (M1 r p Hr Ep) as [PO HR]. split; [exact PO|].
    unfold holeR in *. rewrite pl_of_place_recp_other in HR by assumption.
    destruct HR as [Hh|HR]; [|right; exact HR]. destruct (HH r Hh) as [E|[E|Hh']]; [contradiction| contradiction| left; exact Hh'].
  - intros r Hr Ep. change (getbn r (set_recp x y st)) with (getbn r st).
    destruct (Nat.eq_dec r RRecpN) as [->|N1]; [exact G8|].
    destruct (Nat.eq_dec r RRecpNr) as [->|N2]; [exact G9|].
    apply M2; [exact Hr|]. rewrite pl_of_place_recp_other by assumption. exact Ep.
  - change (pl_ctx (pl_place_recp PL an)) with (pl_ctx PL) in M3. destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hin (Hs & Ia & HL & HCX & HIT)]. split; [exact Hin|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a b i [Hh|HR]; [|right; exact HR].
    destruct (HH _ Hh) as [E|[E|Hh']]; [exfalso; unfold RPool, NFIX, RRecpN in E; lia| exfalso; unfold RPool, NFIX, RRecpNr in E; lia| left; exact Hh'].
  - change (pl_mont (pl_place_recp PL an)) with (pl_mont PL) in M4. destruct (pl_mont PL) as [[am qm]|]; [|exact I]. exact M4.
  - rewrite E3. exact I.
Qed.

End WithRT.
