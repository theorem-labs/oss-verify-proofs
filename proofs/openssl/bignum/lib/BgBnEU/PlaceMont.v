(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnDivWords BnModel BnTree BnInv BnBridge BgState BgWords BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition st_mont_init (st : ST) : ST := setbn RMontNi (bn_nil 0) (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) (set_mont 0 0 st))).

Lemma mont_cells_init : forall st : ST, mont_cells (set_mont 0 0 st) = [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz BN_FLG_MALLOCED)].
Proof. reflexivity. Qed.

Lemma pl_set_mont_fresh : forall PL x, pl_mont PL = None -> pl_set_mont (pl_set_mont PL x) None = PL.
Proof. intros [b c mo r] x E. cbn in *. subst mo. reflexivity. Qed.

Lemma mont_ref_cases : forall r, mont_ref r = true -> r = RMontRR \/ r = RMontN \/ r = RMontNi.
Proof.
  intros r H. unfold mont_ref in H. rewrite !orb_true_iff, !Nat.eqb_eq in H. tauto.
Qed.

Lemma pl_of_set_mont_other : forall PL x r, mont_ref r = false -> pl_of (pl_set_mont PL x) r = pl_of PL r.
Proof.
  intros PL x r H. unfold mont_ref in H. rewrite !orb_false_iff in H. destruct H as [[H1 H2] H3].
  unfold pl_of. rewrite H1, H2, H3. reflexivity.
Qed.

Lemma pl_of_mont_RR : forall PL am qm, pl_of (pl_set_mont PL (Some (am, qm))) RMontRR = Some (PHeap am qm 0).
Proof. reflexivity. Qed.
Lemma pl_of_mont_N : forall PL am qm, pl_of (pl_set_mont PL (Some (am, qm))) RMontN = Some (PHeap (am + 24) qm 24).
Proof. reflexivity. Qed.
Lemma pl_of_mont_Ni : forall PL am qm, pl_of (pl_set_mont PL (Some (am, qm))) RMontNi = Some (PHeap (am + 48) qm 48).
Proof. reflexivity. Qed.

Lemma pl_of_mont_none : forall PL r, pl_mont PL = None -> mont_ref r = true -> pl_of PL r = None.
Proof.
  intros PL r E H. destruct (mont_ref_cases r H) as [-> | [-> | -> ]]; unfold pl_of; cbn; rewrite E; reflexivity.
Qed.

Lemma pl_ids_set_mont : forall PL am qm, pl_mont PL = None -> Permutation (pl_ids (pl_set_mont PL (Some (am, qm)))) (qm :: pl_ids PL).
Proof.
  intros PL am qm E. unfold pl_ids. cbn [pl_ctx pl_mont pl_set_mont opt_ids]. rewrite E. cbn [opt_ids].
  change (pl_bn_ids (pl_set_mont PL (Some (am, qm))) NFIX) with (pl_bn_ids PL NFIX).
  rewrite !app_nil_r. rewrite app_assoc. apply Permutation_sym. apply Permutation_cons_append.
Qed.

Lemma pl_ids_unset_mont : forall PL am qm, pl_mont PL = Some (am, qm) -> Permutation (pl_ids PL) (qm :: pl_ids (pl_set_mont PL None)).
Proof.
  intros PL am qm E. unfold pl_ids. cbn [pl_ctx pl_mont pl_set_mont opt_ids]. rewrite E. cbn [opt_ids].
  change (pl_bn_ids (pl_set_mont PL None) NFIX) with (pl_bn_ids PL NFIX).
  rewrite !app_nil_r. rewrite app_assoc. apply Permutation_sym. apply Permutation_cons_append.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem lib_state_place_mont : forall cxo hs st m OW PL EA am qm,
  lib_state_hc cxo hs st m OW PL EA -> pl_mont PL = None ->
  In (qm, am, MONT_CTX_SZ) OW -> ~ In qm (all_ids st PL EA) ->
  rw_cells bgusegs m am (bn_cells 0 (bn_nil 0)) -> rw_cells bgusegs m (am + 24) (bn_cells 0 (bn_nil 0)) ->
  rw_cells bgusegs m (am + 48) (bn_cells 0 (bn_nil 0)) ->
  rw_cells bgusegs m (am + 72) [C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz BN_FLG_MALLOCED)] ->
  lib_state_hc cxo hs (st_mont_init st) m OW (pl_set_mont PL (Some (am, qm))) EA.
Proof.
  intros cxo hs st m OW PL EA am qm (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) E Hin FRESH C1 C2 C3 C4.
  assert (GRR : getbn RMontRR st = bn_nil 0) by (apply M2; [unfold RMontRR, NFIX; lia| apply pl_of_mont_none; [exact E| reflexivity]]).
  assert (GN : getbn RMontN st = bn_nil 0) by (apply M2; [unfold RMontN, NFIX; lia| apply pl_of_mont_none; [exact E| reflexivity]]).
  assert (GNi : getbn RMontNi st = bn_nil 0) by (apply M2; [unfold RMontNi, NFIX; lia| apply pl_of_mont_none; [exact E| reflexivity]]).
  assert (EST : st_mont_init st = set_mont 0 0 st).
  { unfold st_mont_init.
    assert (X1 : setbn RMontRR (bn_nil 0) (set_mont 0 0 st) = set_mont 0 0 st)
      by (rewrite <- GRR at 1; change (getbn RMontRR st) with (getbn RMontRR (set_mont 0 0 st)); apply setbn_getbn_id).
    rewrite X1.
    assert (X2 : setbn RMontN (bn_nil 0) (set_mont 0 0 st) = set_mont 0 0 st)
      by (rewrite <- GN at 1; change (getbn RMontN st) with (getbn RMontN (set_mont 0 0 st)); apply setbn_getbn_id).
    rewrite X2.
    rewrite <- GNi at 1. change (getbn RMontNi st) with (getbn RMontNi (set_mont 0 0 st)). apply setbn_getbn_id. }
  rewrite EST.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [exact WF|]. split; [exact PWF|].
  split.
  { unfold ids_ok, all_ids in *. change (blocks_of (set_mont 0 0 st)) with (blocks_of st).
    eapply Permutation_NoDup with (l := qm :: (pl_ids PL ++ BnRep.ea_ids EA ++ map fst (blocks_of st))); [|constructor; [exact FRESH| exact IDS]].
    apply Permutation_sym. exact (Permutation_app_tail _ (pl_ids_set_mont PL am qm E)). }
  split; [|split; [|split; [|split]]].
  - intros r p Hr Ep. change (getbn r (set_mont 0 0 st)) with (getbn r st).
    destruct (mont_ref r) eqn:MR.
    + destruct (mont_ref_cases r MR) as [-> | [-> | -> ]].
      * rewrite pl_of_mont_RR in Ep. injection Ep as <-. split.
        { cbn [place_ok]. exists MONT_CTX_SZ. replace (am - 0) with am by lia. split; [exact Hin|]. unfold MONT_CTX_SZ, BN_STRUCT_SZ. lia. }
        right. cbn [place_addr]. rewrite GRR. exists 0. split; [exact C1|]. cbn. split; reflexivity.
      * rewrite pl_of_mont_N in Ep. injection Ep as <-. split.
        { cbn [place_ok]. exists MONT_CTX_SZ. replace (am + 24 - 24) with am by lia. split; [exact Hin|]. unfold MONT_CTX_SZ, BN_STRUCT_SZ. lia. }
        right. cbn [place_addr]. rewrite GN. exists 0. split; [exact C2|]. cbn. split; reflexivity.
      * rewrite pl_of_mont_Ni in Ep. injection Ep as <-. split.
        { cbn [place_ok]. exists MONT_CTX_SZ. replace (am + 48 - 48) with am by lia. split; [exact Hin|]. unfold MONT_CTX_SZ, BN_STRUCT_SZ. lia. }
        right. cbn [place_addr]. rewrite GNi. exists 0. split; [exact C3|]. cbn. split; reflexivity.
    + rewrite pl_of_set_mont_other in Ep by exact MR. destruct (M1 r p Hr Ep) as [PO HR]. split; [exact PO|].
      unfold holeR in *. rewrite pl_of_set_mont_other by exact MR. exact HR.
  - intros r Hr Ep. change (getbn r (set_mont 0 0 st)) with (getbn r st).
    destruct (mont_ref r) eqn:MR.
    + destruct (mont_ref_cases r MR) as [-> | [-> | -> ]]; assumption.
    + rewrite pl_of_set_mont_other in Ep by exact MR. exact (M2 r Hr Ep).
  - change (pl_ctx (pl_set_mont PL (Some (am, qm)))) with (pl_ctx PL). change (st_ctx (set_mont 0 0 st)) with (st_ctx st).
    change (st_bns (set_mont 0 0 st)) with (st_bns st).
    destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hinc (Hs & Ia & HL & HCX & HIT)]. split; [exact Hinc|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a b i [Hh|HR]; [left; exact Hh| right]. rewrite pl_of_pool in *. exact HR.
  - cbn [pl_mont pl_set_mont]. split; [exact Hin|]. rewrite mont_cells_init. exact C4.
  - change (pl_recp (pl_set_mont PL (Some (am, qm)))) with (pl_recp PL). destruct (pl_recp PL) as [c|]; [|exact I].
    change (recp_cells (set_mont 0 0 st)) with (recp_cells st). exact M5.
Qed.

Theorem lib_state_unplace_mont : forall cxo hs hs' st m OW PL EA am qm x y,
  lib_state_hc cxo hs st m OW PL EA -> pl_mont PL = Some (am, qm) ->
  getbn RMontRR st = bn_nil 0 -> getbn RMontN st = bn_nil 0 -> getbn RMontNi st = bn_nil 0 ->
  (forall r, In r hs -> mont_ref r = true \/ In r hs') ->
  lib_state_hc cxo hs' (set_mont x y st) m OW (pl_set_mont PL None) EA
  /\ ~ In qm (all_ids (set_mont x y st) (pl_set_mont PL None) EA).
Proof.
  intros cxo hs hs' st m OW PL EA am qm x y (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) E GRR GN GNi HH.
  assert (ND : List.NoDup (qm :: all_ids (set_mont x y st) (pl_set_mont PL None) EA)).
  { unfold ids_ok, all_ids in *. change (blocks_of (set_mont x y st)) with (blocks_of st).
    eapply Permutation_NoDup; [|exact IDS]. exact (Permutation_app_tail _ (pl_ids_unset_mont PL am qm E)). }
  apply NoDup_cons_iff in ND. destruct ND as [NQ ND].
  split; [|exact NQ].
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [exact WF|]. split; [exact PWF|]. split; [exact ND|].
  split; [|split; [|split; [|split]]].
  - intros r p Hr Ep. change (getbn r (set_mont x y st)) with (getbn r st).
    destruct (mont_ref r) eqn:MR.
    + rewrite (pl_of_mont_none (pl_set_mont PL None) r eq_refl MR) in Ep. discriminate Ep.
    + rewrite pl_of_set_mont_other in Ep by exact MR. destruct (M1 r p Hr Ep) as [PO HR]. split; [exact PO|].
      unfold holeR in *. rewrite pl_of_set_mont_other by exact MR.
      destruct HR as [Hh|HR]; [|right; exact HR]. destruct (HH r Hh) as [X|X]; [rewrite MR in X; discriminate X| left; exact X].
  - intros r Hr Ep. change (getbn r (set_mont x y st)) with (getbn r st).
    destruct (mont_ref r) eqn:MR.
    + destruct (mont_ref_cases r MR) as [-> | [-> | -> ]]; assumption.
    + rewrite pl_of_set_mont_other in Ep by exact MR. exact (M2 r Hr Ep).
  - change (pl_ctx (pl_set_mont PL None)) with (pl_ctx PL). change (st_ctx (set_mont x y st)) with (st_ctx st).
    change (st_bns (set_mont x y st)) with (st_bns st).
    destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hinc (Hs & Ia & HL & HCX & HIT)]. split; [exact Hinc|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a b i [Hh|HR]; [|right; rewrite pl_of_pool in *; exact HR].
    destruct (HH _ Hh) as [X|X]; [exfalso; unfold mont_ref, RPool, NFIX, RMontRR, RMontN, RMontNi in X; rewrite !orb_true_iff, !Nat.eqb_eq in X; lia| left; exact X].
  - cbn [pl_mont pl_set_mont]. exact I.
  - change (pl_recp (pl_set_mont PL None)) with (pl_recp PL). destruct (pl_recp PL) as [c|]; [|exact I].
    change (recp_cells (set_mont x y st)) with (recp_cells st). exact M5.
Qed.

End WithCeiling0.
