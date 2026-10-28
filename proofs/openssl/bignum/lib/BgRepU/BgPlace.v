(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require BgSpecs.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit Driver_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require BnKit2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pl_bn_ids_set_below : forall PL r p n, (n <= r)%nat -> pl_bn_ids (pl_set PL r p) n = pl_bn_ids PL n.
Proof.
  intros PL r p n. induction n as [|n IH]; intros H; cbn [pl_bn_ids]; [reflexivity|].
  rewrite IH by lia. rewrite pl_set_other by lia. reflexivity.
Qed.

Lemma pl_bn_ids_set_heap : forall PL r a q off n, (r < n)%nat -> pl_bn PL r = None ->
  Permutation (pl_bn_ids (pl_set PL r (Some (PHeap a q off))) n) (q :: pl_bn_ids PL n).
Proof.
  intros PL r a q off n. induction n as [|n IH]; intros Hr E; [lia|]. cbn [pl_bn_ids].
  destruct (Nat.eq_dec n r) as [->|NE].
  - rewrite pl_set_same, E. rewrite pl_bn_ids_set_below by lia. apply Permutation_refl.
  - rewrite pl_set_other by exact NE. eapply Permutation_trans; [apply Permutation_app_head; apply IH; [lia| exact E]|].
    apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma pl_bn_ids_set_none_heap : forall PL r a q off n, (r < n)%nat -> pl_bn PL r = Some (PHeap a q off) ->
  Permutation (pl_bn_ids PL n) (q :: pl_bn_ids (pl_set PL r None) n).
Proof.
  intros PL r a q off n. induction n as [|n IH]; intros Hr E; [lia|]. cbn [pl_bn_ids].
  destruct (Nat.eq_dec n r) as [->|NE].
  - rewrite pl_set_same, E. rewrite pl_bn_ids_set_below by lia. apply Permutation_refl.
  - rewrite pl_set_other by exact NE. eapply Permutation_trans; [apply Permutation_app_head; apply IH; [lia| exact E]|].
    apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma pl_ids_set_heap : forall PL r a q off, (r < NFIX)%nat -> pl_bn PL r = None ->
  Permutation (pl_ids (pl_set PL r (Some (PHeap a q off)))) (q :: pl_ids PL).
Proof.
  intros PL r a q off Hr E. unfold pl_ids. change (pl_ctx (pl_set PL r (Some (PHeap a q off)))) with (pl_ctx PL).
  change (pl_mont (pl_set PL r (Some (PHeap a q off)))) with (pl_mont PL).
  exact (Permutation_app_tail _ (pl_bn_ids_set_heap PL r a q off NFIX Hr E)).
Qed.

Lemma pl_ids_set_none_heap : forall PL r a q off, (r < NFIX)%nat -> pl_bn PL r = Some (PHeap a q off) ->
  Permutation (pl_ids PL) (q :: pl_ids (pl_set PL r None)).
Proof.
  intros PL r a q off Hr E. unfold pl_ids. change (pl_ctx (pl_set PL r None)) with (pl_ctx PL).
  change (pl_mont (pl_set PL r None)) with (pl_mont PL).
  exact (Permutation_app_tail _ (pl_bn_ids_set_none_heap PL r a q off NFIX Hr E)).
Qed.

Lemma skipn_list_set_below : forall {A} (l : list A) n r x, (r < n)%nat -> skipn n (list_set l r x) = skipn n l.
Proof.
  intros A l. induction l as [|y l IH]; intros n r x H; destruct n as [|n]; try lia; destruct r as [|r]; cbn [list_set skipn]; try reflexivity.
  apply IH. lia.
Qed.

Lemma skipn_setbn_fixed : forall r b (s : ST), (r < NFIX)%nat -> skipn NFIX (st_bns (setbn r b s)) = skipn NFIX (st_bns s).
Proof. intros r b s H. rewrite st_bns_setbn. apply skipn_list_set_below. exact H. Qed.

Lemma pl_bn_ids_set_ctx : forall PL c n, pl_bn_ids (pl_set_ctx PL c) n = pl_bn_ids PL n.
Proof. intros PL c n. induction n as [|n IH]; cbn [pl_bn_ids]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma set_ctx_id : forall (s : ST), set_ctx (st_ctx s) s = s.
Proof. intros [l c x1 x2 x3 x4]. reflexivity. Qed.

Lemma ctx_wf_nil : ctx_wf (gx_nil : bg_ctx bptr).
Proof. unfold ctx_wf. cbn. repeat split; try reflexivity; try lia. left. auto. Qed.

Definition st_ctx_freed (st : ST) : ST := set_ctx gx_nil (set_bns (firstn NFIX (st_bns st)) st).

Lemma getbn_ctx_freed : forall r (st : ST), (r < NFIX)%nat -> getbn r (st_ctx_freed st) = getbn r st.
Proof.
  intros r st H. unfold getbn, st_ctx_freed, set_ctx, set_bns. cbn [st_bns].
  rewrite <- (firstn_skipn NFIX (st_bns st)) at 2.
  destruct (Nat.lt_ge_cases r (length (firstn NFIX (st_bns st)))) as [L|G].
  - rewrite app_nth1 by exact L. reflexivity.
  - rewrite (nth_overflow (firstn NFIX (st_bns st))) by exact G. rewrite length_firstn in G.
    rewrite nth_overflow; [reflexivity|]. rewrite length_app, length_firstn, length_skipn. lia.
Qed.

Lemma st_wf_ctx_freed : forall (st : ST), st_wf st -> st_wf (st_ctx_freed st).
Proof.
  intros st (EL & OK & ONE & CW). unfold st_wf. unfold st_ctx_freed at 1 2. cbn [st_bns st_ctx set_ctx set_bns gx_items gx_nil length].
  assert (LF : length (firstn NFIX (st_bns st)) = NFIX) by (rewrite length_firstn, EL; lia).
  split; [rewrite LF; lia|]. split; [|split; [|exact ctx_wf_nil]].
  - intros r Hr Hn. unfold st_ctx_freed in Hr. cbn [st_bns set_ctx set_bns] in Hr. rewrite LF in Hr.
    rewrite getbn_ctx_freed by exact Hr. apply OK; [rewrite EL; lia| exact Hn].
  - rewrite getbn_ctx_freed by (unfold ROne, NFIX; lia). exact ONE.
Qed.

Definition ctx_part_ids (st : ST) (qc : bptr) : list bptr :=
  [qc] ++ map fst (concat (map bn_blocks (skipn NFIX (st_bns st)))) ++ gx_items (st_ctx st)
       ++ map fst (opt_block (gx_indexes (st_ctx st)) (4 * Z.of_nat BN_CTX_START_FRAMES)).

Lemma concat_blocks_split : forall (l : list BN) n,
  concat (map bn_blocks l) = concat (map bn_blocks (firstn n l)) ++ concat (map bn_blocks (skipn n l)).
Proof. intros l n. rewrite <- (firstn_skipn n l) at 1. rewrite map_app, concat_app. reflexivity. Qed.

Lemma all_ids_ctx_split : forall (st : ST) PL EA ac qc, pl_ctx PL = Some (ac, qc) ->
  Permutation (all_ids st PL EA) (ctx_part_ids st qc ++ all_ids (st_ctx_freed st) (pl_set_ctx PL None) EA).
Proof.
  intros st PL EA ac qc E. unfold all_ids, ctx_part_ids, pl_ids, blocks_of, st_ctx_freed.
  cbn [st_bns st_ctx set_ctx set_bns gx_items gx_indexes gx_nil pl_ctx pl_mont pl_set_ctx opt_ids opt_block map app].
  rewrite pl_bn_ids_set_ctx, E. cbn [opt_ids]. rewrite app_nil_r.
  rewrite (concat_blocks_split (st_bns st) NFIX), !map_app, map_map. cbn [fst]. rewrite map_id.
  set (a := pl_bn_ids PL NFIX). set (b := opt_ids (pl_mont PL)). set (c := BnRep.ea_ids EA).
  set (d := map fst (concat (map bn_blocks (firstn NFIX (st_bns st))))). set (e := map fst (concat (map bn_blocks (skipn NFIX (st_bns st))))).
  set (f := gx_items (st_ctx st)). set (g := map fst (opt_block (gx_indexes (st_ctx st)) (4 * Z.of_nat BN_CTX_START_FRAMES))).
  clearbody a b c d e f g. rewrite <- !app_assoc. cbn [app].

  eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. constructor.
  replace (a ++ b ++ c ++ d ++ e ++ f ++ g) with ((a ++ b ++ c ++ d) ++ (e ++ f ++ g)) by (rewrite <- !app_assoc; reflexivity).
  replace (e ++ f ++ g ++ a ++ b ++ c ++ d) with ((e ++ f ++ g) ++ (a ++ b ++ c ++ d)) by (rewrite <- !app_assoc; reflexivity).
  apply Permutation_app_comm.
Qed.

Section WithCeiling2. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem lib_state_place_bn : forall cxo hs st m OW PL EA r a q n,
  lib_state_hc cxo hs st m OW PL EA ->
  stored_ref r -> pl_bn PL r = None ->
  In (q, a, n) OW -> BN_STRUCT_SZ <= n -> ~ In q (all_ids st PL EA) ->
  rw_cells bgusegs m a (bn_cells 0 (bn_nil BN_FLG_MALLOCED)) ->
  lib_state_hc cxo hs (setbn r (bn_nil BN_FLG_MALLOCED) st) m OW (pl_set PL r (Some (PHeap a q 0))) EA.
Proof.
  intros cxo hs st m OW PL EA r a q n (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) SR E Hin Hn FRESH CELLS.
  pose proof SR as (RN & RO & RM).
  assert (EO : pl_of PL r = None) by (rewrite pl_of_stored by exact SR; exact E).
  assert (G : getbn r st = bn_nil 0) by (apply M2; [exact RN| exact EO]).
  assert (HV : vref r st) by (unfold vref; destruct WF as (EL & _); rewrite EL; lia).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split. { apply st_wf_setbn; [exact WF| exact RO| apply bg_ok_nil; right; reflexivity]. }
  split.
  {
    destruct PWF as (W1 & W2 & W3). split; [|split].
    - intros r' p Ep. destruct (Nat.eq_dec r' r) as [->|NE].
      + rewrite pl_set_same in Ep. injection Ep as <-. split; [exact RN|]. split; [exact RO|]. split; [exact RM| reflexivity].
      + rewrite pl_set_other in Ep by exact NE. exact (W1 r' p Ep).
    - intros r1 r2 p1 p2 iv1 iv2 NE E1 E2 I1 I2.
      destruct (Nat.eq_dec r1 r) as [->|N1]; [rewrite pl_set_same in E1; injection E1 as <-; destruct I1|].
      destruct (Nat.eq_dec r2 r) as [->|N2]; [rewrite pl_set_same in E2; injection E2 as <-; destruct I2|].
      rewrite pl_set_other in E1 by exact N1. rewrite pl_set_other in E2 by exact N2. exact (W2 r1 r2 p1 p2 iv1 iv2 NE E1 E2 I1 I2).
    - change (pl_recp (pl_set PL r (Some (PHeap a q 0)))) with (pl_recp PL). destruct (pl_recp PL) as [c|]; [|exact I].
      destruct W3 as [C0 W3]. split; [exact C0|]. intros r' p iv Ep Iv.
      destruct (Nat.eq_dec r' r) as [->|NE]; [rewrite pl_set_same in Ep; injection Ep as <-; destruct Iv|].
      rewrite pl_set_other in Ep by exact NE. exact (W3 r' p iv Ep Iv). }
  split.
  {
    unfold ids_ok, all_ids in *. rewrite (blocks_of_setbn_same r _ st HV) by (rewrite G; reflexivity).
    eapply Permutation_NoDup with (l := q :: (pl_ids PL ++ BnRep.ea_ids EA ++ map fst (blocks_of st))); [|constructor; [exact FRESH| exact IDS]].
    apply Permutation_sym. exact (Permutation_app_tail _ (pl_ids_set_heap PL r a q 0 RN E)). }
  split; [|split; [|split; [|split]]].
  - intros r' p Hr' Ep. destruct (Nat.eq_dec r' r) as [->|NE].
    + rewrite pl_of_set_same in Ep by exact SR. injection Ep as <-. split.
      * cbn [place_ok]. exists n. replace (a - 0) with a by lia. split; [exact Hin|]. unfold BN_STRUCT_SZ in *. lia.
      * right. cbn [place_addr]. rewrite getbn_setbn_same by exact HV. rewrite pl_of_set_same by exact SR.
        exists 0. split; [exact CELLS|]. cbn. split; reflexivity.
    + rewrite pl_of_set_other in Ep by exact NE. destruct (M1 r' p Hr' Ep) as [PO HR]. split; [exact PO|].
      rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). unfold holeR in *. rewrite pl_of_set_other by exact NE. exact HR.
  - intros r' Hr' Ep. destruct (Nat.eq_dec r' r) as [->|NE]; [rewrite pl_of_set_same in Ep by exact SR; discriminate Ep|].
    rewrite pl_of_set_other in Ep by exact NE. rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). exact (M2 r' Hr' Ep).
  - change (pl_ctx (pl_set PL r (Some (PHeap a q 0)))) with (pl_ctx PL). rewrite st_ctx_setbn, skipn_setbn_fixed by exact RN.
    destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hinc (Hs & Ia & HL & HCX & HIT)]. split; [exact Hinc|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a0 b0 i [Hh|HR]; [left; exact Hh| right]. rewrite pl_of_pool in *. exact HR.
  - change (pl_mont (pl_set PL r (Some (PHeap a q 0)))) with (pl_mont PL). destruct (pl_mont PL) as [[am qm]|]; [|exact I]. exact M4.
  - change (pl_recp (pl_set PL r (Some (PHeap a q 0)))) with (pl_recp PL). destruct (pl_recp PL) as [c|]; [|exact I]. exact M5.
Qed.

Theorem lib_state_unplace_bn : forall cxo hs st m OW PL EA r a q,
  lib_state_hc cxo (r :: hs) st m OW PL EA -> ~ In r hs ->
  pl_bn PL r = Some (PHeap a q 0) ->
  lib_state_hc cxo hs (setbn r (bn_nil 0) st) m OW (pl_set PL r None) EA
  /\ ~ In q (all_ids (setbn r (bn_nil 0) st) (pl_set PL r None) EA)
  /\ (forall p, bn_d (getbn r st) = Some p -> ~ In p (all_ids (setbn r (bn_nil 0) st) (pl_set PL r None) EA)).
Proof.
  intros cxo hs st m OW PL EA r a q (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) NH E.
  pose proof (pl_wf_stored PL r _ PWF E) as SR. pose proof SR as (RN & RO & RM).
  assert (HV : vref r st) by (unfold vref; destruct WF as (EL & _); rewrite EL; lia).

  assert (IDS1 : ids_ok (setbn r (bn_nil 0) st) PL EA) by (apply ids_ok_setbn_none; [exact IDS| exact HV| reflexivity]).
  assert (IDQ : List.NoDup (q :: (pl_ids (pl_set PL r None) ++ BnRep.ea_ids EA ++ map fst (blocks_of (setbn r (bn_nil 0) st))))).
  { unfold ids_ok, all_ids in IDS1. eapply Permutation_NoDup; [|exact IDS1].
    exact (Permutation_app_tail _ (pl_ids_set_none_heap PL r a q 0 RN E)). }
  apply NoDup_cons_iff in IDQ. destruct IDQ as [NQ IDS2].
  split; [|split; [exact NQ|]].
  2:{ intros p Ed Hp. unfold all_ids in Hp.
      destruct (blocks_setbn r st HV) as (R & P1 & P2). specialize (P2 (bn_nil 0)). cbn [bn_blocks bn_nil bn_d app] in P2.
      unfold bn_blocks in P1. rewrite Ed in P1. cbn [app] in P1.
      unfold ids_ok, all_ids in IDS.
      assert (ND : List.NoDup (p :: (pl_ids PL ++ BnRep.ea_ids EA ++ map fst R))).
      { eapply Permutation_NoDup; [|exact IDS]. apply (Permutation_map fst) in P1. cbn [map fst] in P1.
        eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_head; exact P1|].
        rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle. }
      apply NoDup_cons_iff in ND. destruct ND as [NP _]. apply NP.
      rewrite !in_app_iff in Hp |- *. destruct Hp as [Hp|[Hp|Hp]].
      - left. unfold pl_ids in *. rewrite !in_app_iff in Hp |- *. destruct Hp as [Hp|Hp]; [left; eapply pl_bn_ids_set_none; exact Hp| right; exact Hp].
      - right; left. exact Hp.
      - right; right. eapply Permutation_in; [apply (Permutation_map fst); exact P2| exact Hp]. }
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split. { apply st_wf_setbn; [exact WF| exact RO| apply bg_ok_nil; left; reflexivity]. }
  split.
  {
    destruct PWF as (W1 & W2 & W3). split; [|split].
    - intros r' p Ep. destruct (Nat.eq_dec r' r) as [->|NE]; [rewrite pl_set_same in Ep; discriminate Ep|].
      rewrite pl_set_other in Ep by exact NE. exact (W1 r' p Ep).
    - intros r1 r2 p1 p2 iv1 iv2 NE E1 E2 I1 I2.
      destruct (Nat.eq_dec r1 r) as [->|N1]; [rewrite pl_set_same in E1; discriminate E1|].
      destruct (Nat.eq_dec r2 r) as [->|N2]; [rewrite pl_set_same in E2; discriminate E2|].
      rewrite pl_set_other in E1 by exact N1. rewrite pl_set_other in E2 by exact N2. exact (W2 r1 r2 p1 p2 iv1 iv2 NE E1 E2 I1 I2).
    - change (pl_recp (pl_set PL r None)) with (pl_recp PL). destruct (pl_recp PL) as [c|]; [|exact I].
      destruct W3 as [C0 W3]. split; [exact C0|]. intros r' p iv Ep Iv.
      destruct (Nat.eq_dec r' r) as [->|NE]; [rewrite pl_set_same in Ep; discriminate Ep|].
      rewrite pl_set_other in Ep by exact NE. exact (W3 r' p iv Ep Iv). }
  split; [exact IDS2|].
  split; [|split; [|split; [|split]]].
  - intros r' p Hr' Ep. destruct (Nat.eq_dec r' r) as [->|NE]; [rewrite pl_of_set_same in Ep by exact SR; discriminate Ep|].
    rewrite pl_of_set_other in Ep by exact NE. destruct (M1 r' p Hr' Ep) as [PO HR]. split; [exact PO|].
    rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). unfold holeR in *. rewrite pl_of_set_other by exact NE.
    destruct HR as [[Hh|Hh]|HR]; [exfalso; apply NE; symmetry; exact Hh| left; exact Hh| right; exact HR].
  - intros r' Hr' Ep. destruct (Nat.eq_dec r' r) as [->|NE]; [apply getbn_setbn_same; exact HV|].
    rewrite pl_of_set_other in Ep by exact NE. rewrite getbn_setbn_other by (intros E'; apply NE; symmetry; exact E'). exact (M2 r' Hr' Ep).
  - change (pl_ctx (pl_set PL r None)) with (pl_ctx PL). rewrite st_ctx_setbn, skipn_setbn_fixed by exact RN.
    destruct (pl_ctx PL) as [[ac qc]|]; [|exact M3].
    destruct M3 as [Hinc (Hs & Ia & HL & HCX & HIT)]. split; [exact Hinc|]. exists Hs, Ia. split; [exact HL|]. split; [exact HCX|].
    eapply items_gen_impl; [|exact HIT]. intros a0 b0 i [[Hh|Hh]|HR]; [exfalso; unfold RPool in Hh; lia| left; exact Hh| right]. rewrite pl_of_pool in *. exact HR.
  - change (pl_mont (pl_set PL r None)) with (pl_mont PL). destruct (pl_mont PL) as [[am qm]|]; [|exact I]. exact M4.
  - change (pl_recp (pl_set PL r None)) with (pl_recp PL). destruct (pl_recp PL) as [c|]; [|exact I]. exact M5.
Qed.

Theorem lib_state_place_ctx : forall hs st m OW PL EA ac qc,
  lib_state_hc false hs st m OW PL EA -> pl_ctx PL = None ->
  In (qc, ac, BN_CTX_SZ) OW -> ~ In qc (all_ids st PL EA) ->
  rw_cells bgusegs m ac (ctx_cells 0 0 0 0 gx_nil) ->
  lib_state_hc false hs (set_ctx gx_nil st) m OW (pl_set_ctx PL (Some (ac, qc))) EA.
Proof.
  intros hs st m OW PL EA ac qc (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) E Hin FRESH CELLS.
  rewrite E in M3. destruct M3 as [EC ES].
  assert (EST : set_ctx gx_nil st = st) by (rewrite <- EC at 1; apply set_ctx_id). rewrite EST.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [exact WF|]. split; [exact PWF|].
  split.
  { unfold ids_ok, all_ids in *.
    eapply Permutation_NoDup with (l := qc :: (pl_ids PL ++ BnRep.ea_ids EA ++ map fst (blocks_of st))); [|constructor; [exact FRESH| exact IDS]].
    apply Permutation_sym. apply (Permutation_app_tail (BnRep.ea_ids EA ++ map fst (blocks_of st)) (l := pl_ids (pl_set_ctx PL (Some (ac, qc)))) (l' := qc :: pl_ids PL)).
    unfold pl_ids. cbn [pl_ctx pl_mont pl_set_ctx opt_ids]. rewrite pl_bn_ids_set_ctx, E. cbn [opt_ids app].
    apply Permutation_sym. apply Permutation_middle. }
  split; [exact M1|]. split; [exact M2|]. split; [|split; [exact M4| exact M5]].
  cbn [pl_ctx pl_set_ctx]. split; [exact Hin|]. rewrite EC, ES.
  exists [], 0. split; [reflexivity|]. split; [intros _; split; [exact CELLS| cbn; auto]|]. reflexivity.
Qed.

Theorem lib_state_unplace_ctx : forall hs st m OW PL EA ac qc,
  lib_state_hc false hs st m OW PL EA -> (forall i, ~ In (RPool i) hs) ->
  pl_ctx PL = Some (ac, qc) ->
  lib_state_hc false hs (st_ctx_freed st) m OW (pl_set_ctx PL None) EA
  /\ (forall q, In q (ctx_part_ids st qc) -> ~ In q (all_ids (st_ctx_freed st) (pl_set_ctx PL None) EA)).
Proof.
  intros hs st m OW PL EA ac qc (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) NP E.
  assert (ND : List.NoDup (ctx_part_ids st qc ++ all_ids (st_ctx_freed st) (pl_set_ctx PL None) EA)).
  { eapply Permutation_NoDup; [apply (all_ids_ctx_split st PL EA ac qc E)| exact IDS]. }
  split.
  2:{ intros q H1 H2. revert ND H1 H2. generalize (ctx_part_ids st qc) (all_ids (st_ctx_freed st) (pl_set_ctx PL None) EA). clear.
      intros l1 l2 ND H1 H2. induction l1 as [|x l1 IH]; [destruct H1|]. cbn [app] in ND. apply NoDup_cons_iff in ND. destruct ND as [NX ND].
      destruct H1 as [->|H1]; [apply NX; apply in_or_app; right; exact H2| exact (IH ND H1)]. }
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [exact (st_wf_ctx_freed st WF)|]. split; [exact PWF|].
  split. { unfold ids_ok. revert ND. generalize (ctx_part_ids st qc). intros l ND. induction l as [|x l IH]; [exact ND|]. cbn [app] in ND. apply NoDup_cons_iff in ND. exact (IH (proj2 ND)). }
  split; [|split; [|split; [|split]]].
  - intros r p Hr Ep. rewrite getbn_ctx_freed by exact Hr. exact (M1 r p Hr Ep).
  - intros r Hr Ep. rewrite getbn_ctx_freed by exact Hr. exact (M2 r Hr Ep).
  - cbn [pl_ctx pl_set_ctx]. split; [reflexivity|]. unfold st_ctx_freed. cbn [st_bns set_ctx set_bns].
    destruct WF as (EL & _). apply skipn_all2. rewrite length_firstn. lia.
  - exact M4.
  - exact M5.
Qed.

Theorem lib_state_fini_any : forall st m OW PL EA, lib_state st m OW PL EA -> List.NoDup (BnRep.ea_ids EA) -> lib_inv_bgr m OW.
Proof.
  intros st m OW PL EA (HC & HE & (HO & HGOT) & ((_ & _ & ONE & _) & _ & _ & (HF & _))) ND. split; [exists EA; auto|]. split; [|exact HGOT].
  destruct (HF ROne (PStatic CONST_ONE) ltac:(unfold ROne, NFIX; lia) (pl_of_one PL)) as [_ [[]|(D & HS & HD)]].
  rewrite ONE in HS, HD. rewrite pl_of_one in HS, HD. unfold bn_arr in HD. cbn [bn_d bn_const_one] in HD. destruct HD as [-> _].
  exact HS.
Qed.

End WithCeiling2.
