(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim PEnv APrimSpec2 APrimLem APrimPop APrimRefill APrimQ APrimDealloc APrimCover ASec ASecD AQuar AQuarM
                        AHeap F_quar_E AQuarR AQuarS AQuarP F_quar_As F_quar_R F_quar_DR F_quar_D F_quar_P ALedger AHeap2 AHeapB.
Import ListNotations.
Open Scope Z_scope.

Lemma class_of_a0 : forall x, class_of x = a0_class_of x. Proof. reflexivity. Qed.

Lemma cache_alloc_mu : forall P c, 1 <= c <= 31 -> length (pr_cls P) = 32%nat ->
  let P' := fst (cache_alloc P c) in let k := get_cls P c in
  (forall c', 1 <= c' <= 31 -> c' <> c -> get_cls P' c' = get_cls P c')
  /\ p_mu (get_cls P' c) = (if p_cnt k =? 0 then p_mu (refill k c) else p_mu k)
  /\ pr_cmapped P' = pr_cmapped P + (p_mu (get_cls P' c) - p_mu k).
Proof.
  intros P c Hc LEN. cbv zeta. unfold cache_alloc. destruct (cache_alloc_cls (get_cls P c) c) as [kp v] eqn:EC. cbn [fst].
  assert (EM : p_mu kp = (if p_cnt (get_cls P c) =? 0 then p_mu (refill (get_cls P c) c) else p_mu (get_cls P c))).
  { unfold cache_alloc_cls in EC. destruct (p_cnt (get_cls P c) =? 0); inversion EC; reflexivity. }
  destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
  split; [intros c' Hc' NE; apply get_cls_set_off; assumption|].
  rewrite get_cls_set_same by (first [exact LEN | lia]). split; [exact EM| reflexivity].
Qed.

Section MP.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).

Definition lbcZ (LB : list (block Z)) (c : Z) : Z := Z.of_nat (length (List.filter (fun b => a0_cls (blk_size b) =? c) LB)).
#[using="Type"] Lemma lbcZ_perm : forall LB LB' c, Permutation LB LB' -> lbcZ LB c = lbcZ LB' c.
Proof.
  intros LB LB' c PM. unfold lbcZ. f_equal. apply Permutation_length.
  induction PM as [|x l l' PM IH|x y l|l l' l'' P1 I1 P2 I2]; cbn [List.filter].
  - constructor.
  - destruct (a0_cls (blk_size x) =? c); [apply perm_skip|]; exact IH.
  - destruct (a0_cls (blk_size x) =? c), (a0_cls (blk_size y) =? c); try apply Permutation_refl. apply perm_swap.
  - exact (Permutation_trans I1 I2).
Qed.
#[using="Type"] Lemma lbc_cls_cnt : forall (live : list (qchunk * Z)) c, 1 <= c <= 31 ->
  Forall lr_ok live -> Forall ch_cls_ok (map fst live) -> Forall qchunk_wf (map fst live) ->
  lbcZ (map (blk_ofB AL) live) c = cls_cnt c (map fst live).
Proof.
  intros live c Hc. induction live as [|[ch cn] l IH]; intros LO CO WF; [reflexivity|].
  apply Forall_cons_iff in LO as [L1 LO]. cbn [map fst] in CO, WF. apply Forall_cons_iff in CO as [C1 CO]. apply Forall_cons_iff in WF as [W1 WF].
  specialize (IH LO CO WF). cbn [map fst]. change (ch :: map fst l) with ([ch] ++ map fst l). rewrite cls_cnt_app, <- IH.
  unfold lbcZ. cbn [List.filter]. unfold blk_ofB at 1, blk_size at 1. cbn [fst snd]. unfold cls_cnt. cbn [List.filter].
  assert (EN : a0_cls cn = a0_cls (qc_n ch)) by (destruct L1 as [L1|[L1 L2]]; cbn [fst snd] in *; [rewrite L1; reflexivity| rewrite L1, L2; reflexivity]).
  rewrite EN. unfold ch_cls_ok in C1. destruct (qc_kind ch) as [c' v'|sc].
  - destruct C1 as [EC NZ]. rewrite <- EC. destruct (c' =? c); cbn [length]; lia.
  - destruct C1 as [C1 _]. rewrite C1. replace (0 =? c) with false by (symmetry; apply Z.eqb_neq; lia). cbn [length]. lia.
Qed.

#[using="Type"] Lemma malloc_prim_budget : forall s LB (m : mem) c (ch : qchunk) (cn : Z) H' hs' total',
  RHEAP_B AL E s LB m -> 1 <= c <= 31 ->
  qc_kind ch = QPrim c (snd (cache_alloc (bs_prim s) c)) ->
  (lbcZ LB c + 1) * a0_csz c <= A0_CAP c ->
  let P' := fst (cache_alloc (bs_prim s) c) in
  let s' := mkASB H' (bs_pages s) P' (bs_sec s) (bs_quar s) hs' total' (bs_nsec s) ((ch, cn) :: bs_live s) (bs_depot0 s) in
  pinv AL (P', bs_sec s) (allheld s') (flat_map sec_of (flat_map qb_chunks (bs_gl s')) ++ flat_map sec_of (live_chunks s')) /\ budget_ok s'.
Proof.
  intros s LB m c ch cn H' hs' total' HR Hc EK CAP. cbv zeta.
  pose proof (rheap_pinv AL E s LB m HR) as (LEN & HO & CV & CA & SEP & COK & PSE). cbn [fst snd bs_X] in *.
  pose proof (rheap_wf AL E s LB m HR) as WF0. pose proof (rheap_refill_budget AL E s LB m HR c Hc) as RB.
  destruct (cover_cache_alloc (bs_prim s) c _ Hc LEN (WF0 c Hc) (fun _ => RB) CV) as (CV' & CA' & LEN').
  pose proof (held_cache_alloc (bs_prim s) c _ Hc LEN (WF0 c Hc) (fun _ => RB) HO) as HO'.
  destruct (cache_alloc_mu (bs_prim s) c Hc LEN) as (EO & EMU & ECM). cbv zeta in EO, EMU, ECM.
  set (P' := fst (cache_alloc (bs_prim s) c)) in *. set (v := snd (cache_alloc (bs_prim s) c)) in *.
  assert (PMH : Permutation ((c, v) :: allheld s) (tc_of (bs_gl s) ++ prim_of ch ++ heldB s)).
  { unfold allheld, prim_of. rewrite EK. cbn [app]. apply Permutation_middle. }
  pose proof HR as (PLB & LOK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WFL & _ & _ & _ & _ & _ & _ & _ & _ & _ & CCL & _ & _ & (BMU & BLV & _ & CMP & SC0 & SB0 & NS0) & _).
  set (s' := mkASB H' (bs_pages s) P' (bs_sec s) (bs_quar s) hs' total' (bs_nsec s) ((ch, cn) :: bs_live s) (bs_depot0 s)).
  assert (EA : allheld s' = tc_of (bs_gl s) ++ prim_of ch ++ heldB s) by reflexivity.
  assert (ES : flat_map sec_of (flat_map qb_chunks (bs_gl s')) ++ flat_map sec_of (live_chunks s')
               = flat_map sec_of (flat_map qb_chunks (bs_gl s)) ++ flat_map sec_of (live_chunks s)).
  { unfold live_chunks, s'. cbn [bs_live map flat_map fst]. unfold sec_of at 2. rewrite EK. reflexivity. }
  assert (ECS : sum_cs (allheld s') = sum_cs (allheld s) + class_size c) by (rewrite EA, <- (sum_cs_perm _ _ PMH), sum_cs_cons; cbn [fst]; lia).
  split.
  - unfold pinv. cbn [fst snd]. rewrite EA, ES.
    split; [exact LEN'|]. split; [eapply held_ok_perm'; [exact PMH| exact HO']|].
    split; [apply (cover_incl _ _ _ CV'); intros x Hx; eapply Permutation_in; [exact PMH| exact Hx]|].
    split; [rewrite <- EA, ECS, CA', CA; lia|]. split; [exact SEP|]. split; [exact COK| exact PSE].
  - unfold budget_ok. change (bs_prim s') with P'. split; [| split; [| split; [| split; [| split; [| split]]]]].
    + intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [| rewrite (EO c' Hc' NE); exact (BMU c' Hc')].
      rewrite EMU. destruct (Z.eqb_spec (p_cnt (get_cls (bs_prim s) c)) 0) as [C0|CN]; [exact (rheap_refill_mu AL E s LB m HR c Hc C0)| exact (BMU c Hc)].
    + intros c' Hc'. unfold live_chunks, s'. cbn [bs_live map fst]. change (ch :: map fst (bs_live s)) with ([ch] ++ map fst (bs_live s)). rewrite cls_cnt_app.
      unfold cls_cnt at 1. cbn [List.filter]. rewrite EK. specialize (BLV c' Hc'). unfold live_chunks in BLV.
      destruct (Z.eqb_spec c c') as [<-|NE]; cbn [length Z.of_nat]; [| lia].
      rewrite (lbcZ_perm _ _ c PLB), (lbc_cls_cnt (bs_live s) c Hc LOK CCL WFL) in CAP. unfold live_chunks in *. lia.
    + rewrite ECS, CA', CA. reflexivity.
    + rewrite ECM, CMP. symmetry. apply (sum_mu_upd (bs_prim s) P' c _ Hc); [intros c' Hc' NE; rewrite (EO c' Hc' NE); reflexivity| lia].
    + unfold sec_live_cnt, live_chunks, s'. cbn [bs_live map flat_map fst]. unfold sec_of at 1. rewrite EK. exact SC0.
    + unfold sec_live_bytes, s'. cbn [bs_live fold_right]. unfold sec_rec_bytes at 1. cbn [fst]. rewrite EK. exact SB0.
    + exact NS0.
Qed.

#[using="Type"] Lemma malloc_sec_budget : forall s LB (m : mem) a size (ch : qchunk) (cn : Z) H' hs' total',
  RHEAP_B AL E s LB m -> sec_wf AL (sec_alloc (bs_sec s) a size) ->
  qc_kind ch = QSec (mkSC a (sec_msize size) size) ->
  sec_live_cnt s + 1 <= A0_SEC_CNT -> sec_live_bytes s + cn <= A0_SEC_BYTES -> bs_nsec s + 1 <= A0_NSEC_MAX ->
  let S' := sec_alloc (bs_sec s) a size in
  let s' := mkASB H' (bs_pages s) (bs_prim s) S' (bs_quar s) hs' total' (bs_nsec s + 1) ((ch, cn) :: bs_live s) (bs_depot0 s) in
  pinv AL (bs_prim s, S') (allheld s') (flat_map sec_of (flat_map qb_chunks (bs_gl s')) ++ flat_map sec_of (live_chunks s')) /\ budget_ok s'.
Proof.
  intros s LB m a size ch cn H' hs' total' HR SWF EK BC BB BN. cbv zeta.
  pose proof (rheap_pinv AL E s LB m HR) as (LEN & HO & CV & CA & _ & _ & PSE). cbn [fst snd bs_X] in *.
  destruct SWF as (_ & _ & _ & _ & _ & COK' & SEP').
  set (s' := mkASB H' (bs_pages s) (bs_prim s) (sec_alloc (bs_sec s) a size) (bs_quar s) hs' total' (bs_nsec s + 1) ((ch, cn) :: bs_live s) (bs_depot0 s)).
  assert (EA : allheld s' = allheld s).
  { unfold allheld, heldB, live_chunks, s'. cbn [bs_quar bs_live map flat_map fst]. unfold prim_of at 1. rewrite EK. reflexivity. }
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (BMU & BLV & _ & CMP & SC0 & SB0 & NS0) & _).
  split.
  - unfold pinv. cbn [fst snd]. rewrite EA. split; [exact LEN|]. split; [exact HO|]. split; [exact CV|]. split; [exact CA|].
    split; [exact SEP'|]. split; [exact COK'|].
    unfold live_chunks, s'. cbn [bs_live bs_quar map flat_map fst]. unfold sec_of at 2. rewrite EK. cbn [app]. unfold sec_alloc. cbn [se_chunks].
    eapply Permutation_trans; [apply Permutation_app_tail; exact PSE|]. rewrite <- app_assoc. apply Permutation_app_head.
    apply Permutation_sym. apply Permutation_cons_append.
  - unfold budget_ok. change (bs_prim s') with (bs_prim s). rewrite EA. split; [exact BMU|]. split; [| split; [exact CA| split; [exact CMP|]]].
    2: { split; [unfold sec_live_cnt, live_chunks, s'; cbn [bs_live map flat_map fst]; unfold sec_of at 1; rewrite EK; cbn [app length]; unfold sec_live_cnt, live_chunks in BC; lia|].
         split; [unfold sec_live_bytes, s'; cbn [bs_live fold_right]; unfold sec_rec_bytes at 1; cbn [fst snd]; rewrite EK; unfold sec_live_bytes in BB; lia|].
         unfold s'. cbn [bs_nsec]. lia. }
    intros c' Hc'. unfold live_chunks, s'. cbn [bs_live map fst]. change (ch :: map fst (bs_live s)) with ([ch] ++ map fst (bs_live s)). rewrite cls_cnt_app.
    unfold cls_cnt at 1. cbn [List.filter]. rewrite EK. cbn [length Z.of_nat]. exact (BLV c' Hc').
Qed.

#[using="Type"] Lemma a0_cls0_min : forall n, 1 <= n -> a0_cls n = 0 -> 64513 <= n.
Proof.
  intros n Hn E0. destruct (Z_le_gt_dec n 64512) as [LE|GT]; [| lia]. exfalso.
  pose proof (a0_chk_ok (fun n => negb (a0_cls n =? 0)) (Z.to_nat 64512) 1 ltac:(vm_compute; reflexivity) n ltac:(lia)) as X0.
  cbv beta in X0. rewrite E0 in X0. discriminate.
Qed.
#[using="Type"] Lemma sec_cnt_live : forall (live : list (qchunk * Z)), Forall lr_ok live -> Forall ch_cls_ok (map fst live) ->
  Z.of_nat (length (flat_map sec_of (map fst live))) = lbcZ (map (blk_ofB AL) live) 0.
Proof.
  induction live as [|[ch cn] l IH]; intros LO CO; [reflexivity|].
  apply Forall_cons_iff in LO as [L1 LO]. cbn [map fst] in CO. apply Forall_cons_iff in CO as [C1 CO]. specialize (IH LO CO).
  cbn [map fst flat_map]. rewrite length_app, Nat2Z.inj_add, IH. unfold lbcZ. cbn [List.filter]. unfold blk_ofB at 2, blk_size at 2. cbn [fst snd].
  assert (EN : a0_cls cn = a0_cls (qc_n ch)) by (destruct L1 as [L1|[L1 L2]]; cbn [fst snd] in *; [rewrite L1; reflexivity| rewrite L1, L2; reflexivity]).
  rewrite EN. unfold ch_cls_ok in C1. unfold sec_of. destruct (qc_kind ch) as [c' v'|sc].
  - destruct C1 as [EC NZ]. rewrite <- EC. replace (c' =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). cbn [length]. lia.
  - destruct C1 as [C1 _]. rewrite C1. cbn [Z.eqb length]. lia.
Qed.
#[using="Type"] Lemma sec_cnt_quar : forall chs, Forall qchunk_wf chs -> Forall ch_cls_ok chs -> Z.of_nat (length (flat_map sec_of chs)) * 64521 <= wsum chs.
Proof.
  induction chs as [|ch chs IH]; intros FW FC; [cbn; lia|].
  apply Forall_cons_iff in FW as [(_ & _ & N1 & _) FW]. apply Forall_cons_iff in FC as [CK FC]. specialize (IH FW FC).
  cbn [flat_map wsum fold_right]. fold (wsum chs). rewrite length_app, Nat2Z.inj_add. unfold ch_cls_ok in CK. unfold sec_of at 1.
  destruct (qc_kind ch) as [c' v'|sc]; cbn [length Z.of_nat]; [lia|]. pose proof (a0_cls0_min (qc_n ch) ltac:(lia) (proj1 CK)). lia.
Qed.
#[using="Type"] Lemma wsum_list : forall gl, Forall qbatch_wf gl -> wsum (flat_map qb_chunks gl) <= qbytes gl.
Proof.
  induction gl as [|b gl IH]; intros FW; [cbn; lia|]. apply Forall_cons_iff in FW as [WB FW]. specialize (IH FW).
  cbn [flat_map qbytes fold_right]. fold (qbytes gl). pose proof (wsum_batch b WB) as W2.
  assert (G : forall l1 l2 : list qchunk, wsum (l1 ++ l2) = wsum l1 + wsum l2).
  { induction l1 as [|x l1 IHl]; intros l2; [reflexivity|]. cbn [wsum fold_right app]. fold (wsum (l1 ++ l2)). fold (wsum l1). rewrite IHl. lia. }
  rewrite G. lia.
Qed.
#[using="Type"] Lemma rheap_sec_n : forall s LB (m : mem), RHEAP_B AL E s LB m -> se_n (bs_sec s) <= lbcZ LB 0 + A0_QB / 64521.
Proof.
  intros s LB m HR. destruct (rheap_qbytes AL E s LB m HR) as [FWG QB].
  destruct HR as (PLB & LOK & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PSEC & _ & _ & _ & _ & _ & _ & CCL & CCQ & _).
  destruct INVB as (_ & _ & _ & _ & _ & _ & WFQ & _).
  unfold se_n. rewrite (Permutation_length PSEC), length_app, Nat2Z.inj_add. unfold live_chunks in *.
  rewrite (sec_cnt_live (bs_live s) LOK CCL), <- (lbcZ_perm _ _ 0 PLB).
  pose proof (sec_cnt_quar _ WFQ CCQ) as SQ. pose proof (wsum_list _ FWG) as WL.
  assert (Q : Z.of_nat (length (flat_map sec_of (flat_map qb_chunks (bs_gl s)))) <= A0_QB / 64521) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

End MP.
