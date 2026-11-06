(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v, with its module paths and module names changed; 141 of its 268 lines of code are new or changed and 467 lines of the source are left out. *)
(* proves no function (kind: model and invariant lemmas): fr_LS3c := fr_LS3 /\ fr_CNT at image B, fr_CNT's keep rules
   and the rules that keep the model's blocks or add the opened source's partial buffer *)
(* Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3c.v (sha256
   041bc3ac99b3; internal record) at 1b1e21bdbd40: A's definitions, names and proofs over lib/B's
   records, with the swaps of lib/B/ReplyB3LS3.v's header:
   - the Require header is ReplyB3LS3.v's plus ReplyB3LSCntL (lib/A ReplyLS3 ReplyLSCntL -> lib/B ReplyB3LS3
     ReplyB3LSCntL; lib/A ReplyLS -> lib/B ReplyLSB ReplyB3Base);
   - fr_LS3 B -> fr_LS3 B CALL_ROOM_B: the Section takes the Variable CALL_ROOM_B after B, so fr_LS3c is
     `fr_LS3c B CALL_ROOM_B` (fr_CNT reads no room and stays `fr_CNT B`), and each fr_LS3 rule is called at it;
   - fr_LS3c_pro: as ReplyB3LS3.fr_LS3_pro (ReplyLSB.fr_LS_pro_b's B form of A's lf_base premise): the meter MT is
     quantified and fr_live_pre is `fun S0 => blocks_bytes S0 + CALL_ROOM_B <= LIVE_MAX`;
   - the Section takes {SK : YI16.sink_head} in its Context (lf_base's sink argument, as ReplyLSB.v :144).
   No lemma here reads CALL_ROOM_B's value. *)
(* The count half of LS v3, part 3: the count conjuncts LS carries, fr_LS3c := fr_LS3 /\ fr_CNT (design:
   B1c's count design note, COUNTS-DESIGN in a Theorem Labs lane's B1c claim; a Theorem Labs lane's check 00:23Z).
   fr_CNT says, for the blocks of S other than the input and the model's (that is, fr_LS3's `rest`, the entry's other
   blocks, which every rule keeps): at most SEC0 secondary requests and at most CLS0 requests of each class; and at
   most t pending records (one per write operation).  Stated by differences of counts, so it needs no access to
   fr_LS3's existential rest.  The model's own counts come from its structure (a separate lemma over amodel_at's
   clauses) and from the potentials of part 4.
   This file: fr_CNT, its keep rules, and the rules that keep the model's blocks or add the opened source's partial
   buffer.  fr_LS3c's rule for each is fr_LS3's rule paired with fr_CNT's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyB3Base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3 ReplyB3LSCntL.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Definition SEC0 : Z := 64.
Definition CLS0 : Z := 64.

Section c3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the call room of fr_LS3 (ReplyB3LS3.v, as ReplyLSB.fr_LS takes it) *)
Variable CALL_ROOM_B : Z.
Local Notation zsum l := (fold_right Z.add 0 l).

Definition fr_CNT (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  cnt_sec (ablocks B ly S) - cnt_sec (model_blks m) - cnt_sec (input_blks cx) <= SEC0 /\
  (forall c, cnt_cls c (ablocks B ly S) - cnt_cls c (model_blks m) - cnt_cls c (input_blks cx) <= CLS0) /\
  npend m <= t.
Definition fr_LS3c (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  fr_LS3 B CALL_ROOM_B cx t m ly S /\ fr_CNT cx t m ly S.

(* ------------------------------------------------------------------ fr_CNT's keep rules *)
Lemma fr_CNT_keep : forall cx t t' m m' ly S,
  model_blks m' = model_blks m -> npend m' = npend m -> t <= t' -> fr_CNT cx t m ly S -> fr_CNT cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S Hb Hn Ht (C1 & C2 & C3). unfold fr_CNT. rewrite Hb, Hn.
  split; [exact C1 | split; [exact C2 | lia]].
Qed.
Lemma fr_CNT_k_only : forall cx t t' m m' ly S,
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  t <= t' -> fr_CNT cx t m ly S -> fr_CNT cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S E1 E2 E3 E4 E5 Ht H.
  apply (fr_CNT_keep cx t t' m m' ly S); [| unfold npend; rewrite E1; reflexivity | exact Ht | exact H].
  unfold model_blks; rewrite E1, E2, E3, E4, E5; reflexivity.
Qed.
Lemma fr_CNT_upd : forall cx t t' m m' ly S i f,
  lm_hs m' = upd_hs i f (lm_hs m) -> (forall h, asrc_blks (f h) = asrc_blks h) ->
  (forall h, hs_pending (f h) = hs_pending h) ->
  lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  t <= t' -> fr_CNT cx t m ly S -> fr_CNT cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S i f E1 Hfb Hf E2 E3 E4 E5 Ht H.
  apply (fr_CNT_keep cx t t' m m' ly S); [| | exact Ht | exact H].
  - unfold model_blks. rewrite E2, E3, E4, E5, E1, (upd_hs_blks i f (lm_hs m) Hfb). reflexivity.
  - unfold npend. rewrite E1, (upd_hs_map slot_npend i f (lm_hs m)); [reflexivity|].
    intros h. cbn [slot_npend]. rewrite Hf. reflexivity.
Qed.

(* ------------------------------------------------------------------ the rules *)
Lemma fr_LS3c_head_nout : forall cx t m ly S, fr_LS3c cx t m ly S -> fr_LS3c cx t (lm_clear_O m) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3_head_nout B CALL_ROOM_B cx t m ly S H1)|].
  apply (fr_CNT_k_only cx t t m _ ly S); try reflexivity; try lia; exact H2.
Qed.
Lemma fr_LS3c_head_skip : forall cx t m ly S,
  0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> fr_LS3c cx t m ly S -> fr_LS3c cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof.
  intros cx t m ly S A1 A2 A3 A4 A5 A6 (H1 & H2). split; [exact (fr_LS3_head_skip B CALL_ROOM_B cx t m ly S A1 A2 A3 A4 A5 A6 H1)|].
  apply (fr_CNT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H2.
Qed.
Lemma fr_LS3c_close : forall cx t m i ly S, fr_LS3c cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_LS3c cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S (H1 & H2) Hp. split; [exact (fr_LS3_close B CALL_ROOM_B cx t m i ly S H1 Hp)|].
  apply (fr_CNT_upd cx t (t + 1) m _ ly S i upd_closed);
    [reflexivity | intros h; reflexivity | intros h; reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | exact H2].
Qed.
Lemma fr_LS3c_eintr : forall cx t m i ly S, fr_LS3c cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_LS3c cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S (H1 & H2) Hp. split; [exact (fr_LS3_eintr B CALL_ROOM_B cx t m i ly S H1 Hp)|].
  apply (fr_CNT_upd cx t (t + 1) m _ ly S i upd_eintr);
    [reflexivity | intros h; reflexivity | intros h; reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia | exact H2].
Qed.
Lemma fr_LS3c_sendmax : forall cx t m ly S, fr_LS3c cx t m ly S ->
  fr_LS3c cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3_sendmax B CALL_ROOM_B cx t m ly S H1)|].
  apply (fr_CNT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H2.
Qed.
Lemma fr_LS3c_default : forall cx t m ly S, fr_LS3c cx t m ly S -> fr_LS3c cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3_default B CALL_ROOM_B cx t m ly S H1)|].
  apply (fr_CNT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H2.
Qed.
Lemma fr_LS3c_write_skip : forall cx t m ly S, fr_LS3c cx t m ly S -> fr_LS3c cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3_write_skip B CALL_ROOM_B cx t m ly S H1)|].
  apply (fr_CNT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H2.
Qed.
Lemma fr_LS3c_add_none : forall cx t m ly S, fr_LS3c cx t m ly S -> fr_LS3c cx (t + 1) (ad_none m) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3_add_none B CALL_ROOM_B cx t m ly S H1)|].
  apply (fr_CNT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H2.
Qed.
Lemma fr_LS3c_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3c cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_LS3c cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' (H1 & H2) Hf HP'.
  split; [exact (fr_LS3_add_open B CALL_ROOM_B cx t m i q pj ev ly S ly' S' H1 Hf HP')|].
  destruct H1 as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  destruct (oa_first_free (lm_hs m) i Hl Hf) as (Hi4 & Hi).
  pose proof (model_perm_add m i q pj ev Hi) as Hm.
  destruct H2 as (C1 & C2 & C3). unfold fr_CNT.
  rewrite (cnt_sec_perm _ _ HP'), (cnt_sec_perm _ _ Hm), !cnt_sec_cons.
  split; [lia | split].
  - intros c. rewrite (cnt_cls_perm _ _ _ HP'), (cnt_cls_perm _ _ _ Hm), !cnt_cls_cons. specialize (C2 c). lia.
  - assert (Zs : zsum (map slot_npend (lm_hs (ad_open m i q pj ev))) + slot_npend None =
                 zsum (map slot_npend (lm_hs m)) + slot_npend (Some (oa_new_src (100 + lm_nfd m) q pj)))
      by (rewrite ad_open_hs; exact (set_nth_zsum slot_npend i _ None (lm_hs m) Hi)).
    assert (P4 : slot_npend (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (N4 : slot_npend None = 0) by reflexivity.
    unfold npend in *. lia.
Qed.
(* ------------------------------------------------------------------ the same rest: the counts carry over *)
Lemma fr_CNT_same_rest : forall cx t t' m m' ly S ly' S' r,
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ r) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ r) ->
  npend m' <= npend m + (t' - t) -> fr_CNT cx t m ly S -> fr_CNT cx t' m' ly' S'.
Proof.
  intros cx t t' m m' ly S ly' S' r HP HP' Hn (C1 & C2 & C3). unfold fr_CNT.
  rewrite (cnt_sec_perm _ _ HP'), !cnt_sec_app. rewrite (cnt_sec_perm _ _ HP), !cnt_sec_app in C1.
  split; [lia | split; [| lia]].
  intros c. specialize (C2 c). rewrite (cnt_cls_perm _ _ _ HP'), !cnt_cls_app.
  rewrite (cnt_cls_perm _ _ _ HP), !cnt_cls_app in C2. lia.
Qed.

Ltac perm_lia3 :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

(* write_push at the proposed text: the pushed text and the vector are model blocks; the frame keeps the rest *)
Lemma fr_LS3c_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS3c cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  fr_LS3c cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ly S ly' S' ev (H1 & H2) Hpk Hn Hrecs Hcap Hv Hlp.
  split; [exact (fr_LS3_write_push B CALL_ROOM_B cx t m si h l' d ly S ly' S' ev H1 Hpk Hn Hrecs Hcap Hv Hlp)|].
  destruct Hpk as (_ & _ & Hh).
  destruct H1 as (rest & e0 & HP & _).
  pose proof (nth_some_error _ _ _ Hh) as Hi.
  set (l := hs_pending h) in *. set (x := wr_x cx m) in *. set (h' := set_pending h l').
  set (m' := wr_push m (wr_k2 cx m) si h' ev).
  set (dd := (d, Z.of_nat (length x) + 1)).
  set (OV := if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []).
  set (NV := if lp_grow l then [(hl_v l', AREC * hl_cap l')] else []).
  set (VL := if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]).
  set (VL' := if hl_cap l' =? 0 then [] else [(hl_v l', AREC * hl_cap l')]).
  set (CL := map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)).
  assert (Hn1 : hl_n l' = hl_n l + 1) by (unfold hl_n; rewrite Hrecs, length_app; cbn; lia).
  assert (HVp : Permutation (VL' ++ OV) (VL ++ NV)).
  { unfold VL', OV, VL, NV. unfold lp_grow in *. unfold grow_cap in Hcap.
    destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [G|G].
    - try rewrite (proj2 (Z.eqb_eq _ _) G) in Hcap. cbv beta iota in Hcap.
      destruct (Z.eqb_spec (hl_cap l) 0) as [C0|C0].
      + rewrite Hcap. rewrite C0 in *. cbn. apply Permutation_refl.
      + assert (E2 : (2 * hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
        rewrite Hcap, E2. cbn [andb negb app]. first [apply perm_swap | apply Permutation_app_comm].
    - assert (Hv' : hl_v l' = hl_v l) by (apply Hv; first [exact (proj2 (Z.eqb_neq _ _) G) | reflexivity]).
      try rewrite (proj2 (Z.eqb_neq _ _) G) in Hcap. cbv beta iota in Hcap.
      rewrite Hcap, Hv'. cbn [andb negb app]. apply Permutation_refl. }
  assert (Ha : asrc_blks h = (hs_partial h, APARTIAL) :: (VL ++ CL) ++ alist_blks (hs_expected h) ++ alist_blks (hs_held h))
    by reflexivity.
  assert (Ha' : asrc_blks h' = (hs_partial h, APARTIAL) :: (VL' ++ CL ++ [dd]) ++ alist_blks (hs_expected h) ++
                  alist_blks (hs_held h))
    by (unfold h', asrc_blks, alist_blks; cbn [set_pending hs_partial hs_pending hs_expected hs_held];
        fold VL'; rewrite Hrecs, map_app; reflexivity).
  pose proof (set_nth_perm slot_blks si (Some h') (Some h) (lm_hs m) Hi) as Hsw. cbn [slot_blks] in Hsw.
  rewrite Ha, Ha' in Hsw.
  assert (HM2 : Permutation (model_blks m' ++ OV) (model_blks m ++ NV ++ [dd])).
  { unfold model_blks, m'. cbn [wr_push lm_G lm_es lm_hs lm_cap lm_out]. perm_lia3. }
  assert (Hsplit : exists mm, Permutation (model_blks m) (OV ++ mm)).
  { destruct (lp_grow l && negb (hl_cap l =? 0)) eqn:Eg; unfold OV; try rewrite Eg; cbv beta iota.
    - assert (Hin : In (hl_v l, AREC * hl_cap l) (model_blks m)).
      { apply andb_true_iff in Eg as (_ & E). apply negb_true_iff in E. unfold model_blks.
        right. apply in_app_iff. right. apply in_app_iff. left. apply in_concat.
        exists (slot_blks (Some h)). split; [apply in_map; exact (nth_error_In _ _ Hi)|].
        cbn [slot_blks]. rewrite Ha. right. apply in_app_iff. left. apply in_app_iff. left.
        unfold VL. rewrite E. left. reflexivity. }
      destruct (in_split _ _ Hin) as (l1 & l2 & E). exists (l1 ++ l2). rewrite E. perm_lia3.
    - exists (model_blks m). apply Permutation_refl. }
  destruct Hsplit as (mm & Hmm).
  assert (HP1 : Permutation (ablocks B ly S) (OV ++ (input_blks cx ++ mm ++ rest))) by perm_lia3.
  pose proof (Hlp _ HP1) as HP2. fold x dd NV in HP2.
  assert (HP' : Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest)) by (clear - HP2 Hmm HM2; perm_lia3).
  apply (fr_CNT_same_rest cx t (t + 1) m m' ly S ly' S' rest HP HP'); [| exact H2].
  assert (Zs : zsum (map slot_npend (lm_hs m')) + slot_npend (Some h) = zsum (map slot_npend (lm_hs m)) + slot_npend (Some h'))
    by exact (set_nth_zsum slot_npend si (Some h') (Some h) (lm_hs m) Hi).
  cbn [slot_npend h' set_pending hs_pending] in Zs. fold l in Zs.
  unfold npend in *. lia.
Qed.

(* the prologue: the entry contract's count bound (the entry's blocks other than the input, the kept table and g_out)
   is the rest's *)
Definition xcnt_pre (cx : lfcx) (T0 cap out : Z) : Prop :=
  cnt_sec (ablocks B (c_ly cx) (c_S cx)) - cnt_sec (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++
    aout_blks cap out) <= SEC0 /\
  forall c, cnt_cls c (ablocks B (c_ly cx) (c_S cx)) - cnt_cls c (input_blks cx ++
    (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out) <= CLS0.
Lemma fr_LS3c_pro : forall MT XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S,
  lf_base B MT XM_LIB RLO RHI (fun S0 => blocks_bytes S0 + CALL_ROOM_B <= LIVE_MAX) G_fr cx ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     xcnt_pre cx T0 cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_LS3c cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros MT XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S Hb (T0 & rest0 & HE0 & (X1 & X2) & Hcase).
  split; [exact (fr_LS3_pro B CALL_ROOM_B MT XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S Hb
                   (ex_intro _ T0 (ex_intro _ rest0 (conj HE0 Hcase))))|].
  assert (Hmb : model_blks (ls_pro_m q T' pj c O cap out) = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out)
    by reflexivity.
  assert (En : npend (ls_pro_m q T' pj c O cap out) = 0) by reflexivity.
  assert (HP : Permutation (ablocks B ly S) (input_blks cx ++ model_blks (ls_pro_m q T' pj c O cap out) ++ rest0)).
  { rewrite Hmb. destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
    - subst T0. rewrite Z.eqb_refl in HE0. cbv beta iota in HE0. perm_lia3.
    - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0. perm_lia3. }
  unfold fr_CNT. rewrite (cnt_sec_perm _ _ HP), !cnt_sec_app.
  rewrite (cnt_sec_perm _ _ HE0), !cnt_sec_app in X1.
  split; [lia | split; [| rewrite En; lia]].
  intros c0. specialize (X2 c0). rewrite (cnt_cls_perm _ _ _ HP), !cnt_cls_app.
  rewrite (cnt_cls_perm _ _ _ HE0), !cnt_cls_app in X2. lia.
Qed.

End c3.

