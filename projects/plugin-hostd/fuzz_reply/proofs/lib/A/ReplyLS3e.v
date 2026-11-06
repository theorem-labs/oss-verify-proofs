(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v; 306 of its 411 lines of code are new or changed and 489 lines of the source are left out. *)
(* The entry half of LS v3: fr_ENT, the conjunct that keeps the call's REST the entry's rest, its twin of every
   rule, and the exit's LS_exit_end CONCLUDING fr_surv.  proves no function (kind: invariant lemma).

   WHY.  a8's fr_surv (lib/A/ACfn_cf.v:105) relates the entry's live blocks to the return's.  Row B1c's
   LS_exit_end could not conclude it, because fr_LS3's block relation is `exists rest` and every cut forgets which
   rest it was (the finding of 2026-10-30 03:0xZ).  fr_ENT carries it:

     fr_ENT cx m ly S := forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
                         Permutation (ablocks B (c_ly cx) (c_S cx)) (input_blks cx ++ fr_hblks (c_W cx) (c_mem cx) ++ rest)

   THE CONDITIONAL FORM IS THE "SAME REST" FORM.  Under fr_LS3's own clause (some rest exists) the two are
   equivalent, and ent_rest_eq / fr_ENT_iff below prove it: a state's rest is unique up to Permutation
   (Permutation_app_inv_l twice), so quantifying over every rest that fits says exactly what one witness says.  The
   conditional form is the one kept here because its KEEP rules (the eight that move neither the state nor the
   model's blocks) need no rest at all, and because its twin composes as a one-line application at each arm, with
   no existential to open.  Its hypothesis is also what the exit text already hands over: the exit's own
   `Permutation (ablocks B ly3 S3) (input ++ model_blks m ++ rest)` premise.

   fr_hblks is W_LLVMFuzzerTestOneInput_cut.v:166's, the definition the exit text (lib/A/W_LLVMFuzzerTestOneInput_exit_x.v fr_surv / fr_hblks_kept /
   HHB3) and ACfn_cf.v's fr_surv use.  Note W_LLVMFuzzerTestOneInput_cut.v ablocks_sep: its
   first clause is fr_LS3's existential rest, its second ("a model block is fresh or inside the entry's footprint")
   is fr_surv's third clause in footprint form - over req_size ranges, so it does not give the block equality that
   clause wants, and is not used here.

   This file: fr_ENT, the rest-uniqueness lemmas, the twin of every rule that has an fr_OUT twin in
   lib/A/ReplyLS3o.v (plus the prologue rule and the gone end), and LS_exit_end3e. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c RelayCap SlotReads SlotInv
  relay_remove_b_aux send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3 ReplyLS3Arms ReplyLSCntL ReplyLS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3cTopx ReplyLS3cTopxGone ReplyLS3cTopxGoneF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* block lists are permutations when their count_occ agree: ReplyLS3c.v's perm_lia3, which its Section keeps *)
Ltac ent_perm :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

Section oent.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LSH : lib_shape}.
Variable B : asyms.
(* the meter (KF-COUNT): a Variable, implicit (read off the rules' mo_le arguments); no rule here reads it.  The
   exit's meter conclusion is ReplyLSI.v's (lsi_LS_exit_end, from its fr_SEC), not LS_exit_end3e's. *)
Context {MT : ameter_ops}.

(* the call's rest is the entry's rest: every block that is neither the input block nor one of the model's is a
   block the entry already had outside its harness blocks *)
Definition fr_ENT (cx : lfcx) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
    Permutation (ablocks B (c_ly cx) (c_S cx)) (input_blks cx ++ fr_hblks (c_W cx) (c_mem cx) ++ rest).

(* ================================================================== the rest is unique up to Permutation *)
Lemma ent_rest_eq : forall (A I M r1 r2 : list (Z * Z)),
  Permutation A (I ++ M ++ r1) -> Permutation A (I ++ M ++ r2) -> Permutation r1 r2.
Proof.
  intros A I M r1 r2 H1 H2.
  apply (Permutation_app_inv_l M), (Permutation_app_inv_l I).
  exact (Permutation_trans (Permutation_sym H1) H2).
Qed.
(* the conditional form and the "one witness" form say the same thing under fr_LS3's clause *)
Lemma fr_ENT_iff : forall cx m ly S,
  (exists rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest)) ->
  (fr_ENT cx m ly S <->
   exists rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) /\
     Permutation (ablocks B (c_ly cx) (c_S cx)) (input_blks cx ++ fr_hblks (c_W cx) (c_mem cx) ++ rest)).
Proof.
  intros cx m ly S (r0 & H0). split.
  - intros HE. exists r0. split; [exact H0 | exact (HE r0 H0)].
  - intros (r1 & H1 & HE) r Hr.
    pose proof (ent_rest_eq _ _ _ _ _ H1 Hr) as Hrr.
    exact (Permutation_trans HE (Permutation_app_head _ (Permutation_app_head _ Hrr))).
Qed.
(* the step every twin uses: a rule that keeps ONE rest keeps fr_ENT *)
Lemma fr_ENT_step : forall cx m ly S m' ly' S' rest,
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest) ->
  fr_ENT cx m ly S -> fr_ENT cx m' ly' S'.
Proof.
  intros cx m ly S m' ly' S' rest HP HP' HE r Hr.
  pose proof (ent_rest_eq _ _ _ _ _ HP' Hr) as Hrr.
  exact (Permutation_trans (HE rest HP) (Permutation_app_head _ (Permutation_app_head _ Hrr))).
Qed.

(* ================================================================== the rules that move neither state nor blocks *)
Lemma fr_ENT_keep : forall cx m m' ly S, model_blks m' = model_blks m -> fr_ENT cx m ly S -> fr_ENT cx m' ly S.
Proof. intros cx m m' ly S E H rest Hr. rewrite E in Hr. exact (H rest Hr). Qed.

Lemma fr_ENT_head_nout : forall cx m ly S, fr_ENT cx m ly S -> fr_ENT cx (lm_clear_O m) ly S.
Proof. intros cx m ly S H. exact (fr_ENT_keep cx m _ ly S eq_refl H). Qed.
Lemma fr_ENT_head_skip : forall cx m ly S, fr_ENT cx m ly S -> fr_ENT cx (lm_set_k m (hd_k' cx m)) ly S.
Proof. intros cx m ly S H. exact (fr_ENT_keep cx m _ ly S eq_refl H). Qed.
Lemma fr_ENT_sendmax : forall cx m u ly S, fr_ENT cx m ly S -> fr_ENT cx (sm_sendmax cx m u) ly S.
Proof. intros cx m u ly S H. exact (fr_ENT_keep cx m _ ly S eq_refl H). Qed.
Lemma fr_ENT_default : forall cx m g ly S, fr_ENT cx m ly S -> fr_ENT cx (sm_default cx m g) ly S.
Proof. intros cx m g ly S H. exact (fr_ENT_keep cx m _ ly S eq_refl H). Qed.
Lemma fr_ENT_write_skip : forall cx m ly S, fr_ENT cx m ly S -> fr_ENT cx (wr_skip m (wr_k2 cx m)) ly S.
Proof. intros cx m ly S H. exact (fr_ENT_keep cx m _ ly S eq_refl H). Qed.
Lemma fr_ENT_add_none : forall cx m ly S, fr_ENT cx m ly S -> fr_ENT cx (ad_none m) ly S.
Proof. intros cx m ly S H. exact (fr_ENT_keep cx m _ ly S eq_refl H). Qed.
Lemma fr_ENT_close : forall cx m i ly S, fr_ENT cx m ly S -> fr_ENT cx (sm_close cx m i) ly S.
Proof.
  intros cx m i ly S H. apply (fr_ENT_keep cx m _ ly S); [|exact H].
  unfold model_blks. cbn [sm_close lm_G lm_es lm_hs lm_cap lm_out].
  rewrite (upd_hs_blks i upd_closed (lm_hs m) (fun h => eq_refl)). reflexivity.
Qed.
Lemma fr_ENT_eintr : forall cx m i ly S, fr_ENT cx m ly S -> fr_ENT cx (sm_eintr cx m i) ly S.
Proof.
  intros cx m i ly S H. apply (fr_ENT_keep cx m _ ly S); [|exact H].
  unfold model_blks. cbn [sm_eintr lm_G lm_es lm_hs lm_cap lm_out].
  rewrite (upd_hs_blks i upd_eintr (lm_hs m) (fun h => eq_refl)). reflexivity.
Qed.

(* ================================================================== op_add's open *)
Lemma fr_ENT_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3 B cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_ENT cx m ly S -> fr_ENT cx (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' H1 Hf HP' HE.
  destruct H1 as (rest & e0 & HP & _ & _ & _ & Hl & _).
  destruct (oa_first_free (lm_hs m) i Hl Hf) as (_ & Hi).
  pose proof (model_perm_add m i q pj ev Hi) as Hm.
  apply (fr_ENT_step cx m ly S _ ly' S' rest HP); [|exact HE].
  ent_perm.
Qed.

(* ================================================================== the write arm's push *)
Lemma fr_ENT_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS3 B cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  fr_ENT cx m ly S -> fr_ENT cx (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ly S ly' S' ev H1 Hpk Hn Hrecs Hcap Hv Hlp HE.
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
  { unfold model_blks, m'. cbn [wr_push lm_G lm_es lm_hs lm_cap lm_out]. ent_perm. }
  assert (Hsplit : exists mm, Permutation (model_blks m) (OV ++ mm)).
  { destruct (lp_grow l && negb (hl_cap l =? 0)) eqn:Eg; unfold OV; try rewrite Eg; cbv beta iota.
    - assert (Hin : In (hl_v l, AREC * hl_cap l) (model_blks m)).
      { apply andb_true_iff in Eg as (_ & E). apply negb_true_iff in E. unfold model_blks.
        right. apply in_app_iff. right. apply in_app_iff. left. apply in_concat.
        exists (slot_blks (Some h)). split; [apply in_map; exact (nth_error_In _ _ Hi)|].
        cbn [slot_blks]. rewrite Ha. right. apply in_app_iff. left. apply in_app_iff. left.
        unfold VL. rewrite E. left. reflexivity. }
      destruct (in_split _ _ Hin) as (l1 & l2 & E). exists (l1 ++ l2). rewrite E. ent_perm.
    - exists (model_blks m). apply Permutation_refl. }
  destruct Hsplit as (mm & Hmm).
  assert (HP1 : Permutation (ablocks B ly S) (OV ++ (input_blks cx ++ mm ++ rest))) by ent_perm.
  pose proof (Hlp _ HP1) as HP2. fold x dd NV in HP2.
  apply (fr_ENT_step cx m ly S m' ly' S' rest HP); [|exact HE].
  clear - HP2 HM2 Hmm. ent_perm.
Qed.

(* ================================================================== the drain arm's step *)
Lemma fr_ENT_drain_step_p : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  fr_ENT cx m ly S -> fr_ENT cx (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HLS Hpick Hj
    (rest_d & HPd1 & HPd2) HEq HHq Hcnl Hh'' HE.
  subst E H h''.
  pose proof Hpick as (_ & _ & Hh).
  destruct HLS as (rest & e0 & HP & _).
  set (e := nth j (lm_es m) dr_e0) in *.
  set (h'' := set_exp_held h1 E' H') in *.
  set (m' := dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') in *.
  assert (Hej : nth_error (lm_es m) j = Some e) by (unfold e; apply nth_error_nth'; exact Hj).
  pose proof (nth_some_error _ _ _ Hh) as Hhi.
  assert (LB : forall l, list_blks l = alist_blks l) by reflexivity.
  assert (Ha1 : asrc_blks h1 = (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++
                               alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) by reflexivity.
  assert (Ha'' : asrc_blks h'' = (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++
                                 list_blks E' ++ list_blks H') by reflexivity.
  pose proof (Hcnl ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ aentry_blks e' ++
                    aout_blks cap' out' ++ rest_d)) as HP3.
  rewrite !LB in HP3.
  assert (HP2' : Permutation (ablocks B ly1 S1) (alist_blks (hs_expected h1) ++ alist_blks (hs_held h1) ++
                   (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ aentry_blks e' ++ aout_blks cap' out' ++
                   rest_d)).
  { rewrite Ha1 in HPd2. clear - HPd2. ent_perm. }
  specialize (HP3 HP2'). clear HP2'.
  pose proof (dr3_dset_perm aentry_blks j e' e (lm_es m) Hej) as PA.
  pose proof (dr3_dset_perm slot_blks si (Some h'') (Some h) (lm_hs m) Hhi) as PS.
  change (slot_blks (Some h'')) with (asrc_blks h'') in PS. change (slot_blks (Some h)) with (asrc_blks h) in PS.
  rewrite Ha'' in PS.
  apply (fr_ENT_step cx m ly S m' ly' S' rest HP); [|exact HE].
  unfold model_blks in HP. unfold model_blks, m'. cbn [dr_step lm_G lm_es lm_hs lm_cap lm_out].
  clear - HP HPd1 HP3 PA PS. ent_perm.
Qed.

(* ================================================================== the remove arm's step *)
Lemma fr_ENT_rm_step_p : forall cx t m ly0 S0 (ly : alayout) (S : astate) si j0 c2 O2 cap2 out2 ev5,
  fr_LS3 B cx t m ly0 S0 ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  fr_ENT cx m ly0 S0 -> fr_ENT cx (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si j0 c2 O2 cap2 out2 ev5 HLS Hfr HE.
  destruct HLS as (rest & e0 & HP & _).
  exact (fr_ENT_step cx m ly0 S0 _ ly S rest HP (Hfr rest HP) HE).
Qed.

(* ================================================================== the event arm's step *)
Lemma fr_ENT_event_step_p : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS3 B cx t m ly S ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_ENT cx m ly S -> fr_ENT cx (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HLS Hm HRR Hf HE.
  destruct HRR as (restR & HR1 & HR2). destruct Hf as (l1 & l2 & Hf2 & Hf3).
  destruct HLS as (rest & e0 & HP & _).
  assert (HmP : Permutation (ablocks B ly1 S1) (ablocks B ly S ++ [(q, re_len e)]))
    by (rewrite Hm; apply Permutation_refl).
  assert (Hf2P : Permutation (ablocks B ly2 S2) (l1 ++ (q, re_len e) :: l2))
    by (rewrite Hf2; apply Permutation_refl).
  assert (Hf3P : Permutation (ablocks B ly3 S3) (l1 ++ l2)) by (rewrite Hf3; apply Permutation_refl).
  apply (fr_ENT_step cx m ly S _ ly3 S3 rest HP); [|exact HE].
  rewrite (ev3_model_blks (ev_step cx m e v out')).
  rewrite (ev3_model_blks m) in HP.
  assert (Ep : ev3_pfx (ev_step cx m e v out') = ev3_pfx m) by reflexivity.
  assert (Ec : lm_cap (ev_step cx m e v out') =
               sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) by reflexivity.
  assert (Eo : lm_out (ev_step cx m e v out') = out') by reflexivity.
  rewrite Ep, Ec, Eo.
  clear - HP HmP HR1 HR2 Hf2P Hf3P. ent_perm.
Qed.

(* ================================================================== the first head (the prologue) *)
(* NAMED HYPOTHESIS HFH0: the entry's harness blocks are the table g_src names and g_out's buffer, the same three
   reads fr_hblks makes (_cut.v:163-167 at bb9dae5d905).  SEG_PRO holds it where it reads T0, cap and out out of
   the entry's memory to build this premise; fr_LS3c_pro (ReplyLS3c.v:260-267) keeps only the blocks. *)
Lemma fr_ENT_pro : forall cx q T' pj c O cap out ly S T0 rest0,
  Permutation (ablocks B (c_ly cx) (c_S cx))
    (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) ->
  ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
   (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx)))) ->
  fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ->
  fr_ENT cx (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros cx q T' pj c O cap out ly S T0 rest0 HE0 Hcase HFH0.
  assert (Hmb : model_blks (ls_pro_m q T' pj c O cap out) = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out)
    by reflexivity.
  assert (HP : Permutation (ablocks B ly S)
                 (input_blks cx ++ model_blks (ls_pro_m q T' pj c O cap out) ++ rest0)).
  { rewrite Hmb. destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
    - subst T0. rewrite Z.eqb_refl in HE0. cbv beta iota in HE0. ent_perm.
    - subst T'. rewrite (proj2 (Z.eqb_neq _ _) HT0) in HE0. cbv beta iota in HE0. ent_perm. }
  intros r Hr.
  pose proof (ent_rest_eq _ _ _ _ _ HP Hr) as Hrr.
  rewrite HFH0. clear - HE0 Hrr. ent_perm.
Qed.

(* ================================================================== the gone arm's end *)
(* 6a2e02357a4 GN_RI_end's premises, in gx6_end_LS3c's order (lib/A/ReplyLS3cTopxGoneF.v:140-163); fr_ENT needs only
   the block relation and fr_LS3's rest, so RINV, gn_op, the per-entry premise, REQ1-REQ3, gn_pairs, gn_after_rig,
   gn_rig_ok, gn_run, mo_le and REQ5 are taken and not read. *)
Lemma fr_ENT_gone_end : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_LS3 B cx t m ly S -> fr_ENT cx m ly S ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (forall j hj hj', nth j (lm_hs m) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
     hl_cap (hs_held hj) <= hl_cap (hs_held hj')) ->
  fr_ENT cx mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst _ _ _ _ _ _ HLS HE _ _ _ _ _ Hfr _.
  destruct HLS as (rest & e0 & HP & _).
  exact (fr_ENT_step cx m ly S mc lyx Sx rest HP (Hfr rest HP) HE).
Qed.

(* ================================================================== the exit, now concluding fr_surv *)
Section oentx.
Context {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
(* LS_exit_end at LS := fr_LS3c /\ fr_OUT /\ fr_ENT: the ARx text of exit_x.v:158-167 (integ bb9dae5d905) with row
   B1c's ONE added premise `cap = gse_cap (lx_rf_run ..)`, NP dropped (ROOM-TEXTS.md:218-219 sha256 767baa12f13c; internal record), and fr_surv now a
   CONCLUSION.  Its two added premises are the walk's own facts, each at the site that holds it in
   lx_end_of_ffexit_x (integ lib/A/W_LLVMFuzzerTestOneInput_exit_x.v):
     HFH - fr_hblks W' mem' = the kept table and g_out.  The walk gets it in two steps: fr_hblks W3 mem3 =
       fr_hblks W2 mem2 at :4827 (fr_hblks_kept, from KEEP at :4809 and lx_glob_lits at :4824), and
       fr_hblks W2 mem2 = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m) from HM2's g_src / relay / g_out
       clauses HSL, HRL, HOUT at :4820-4821 - the same three reads fr_hblks makes (_cut.v:163-167) - with EM
       at :4811-4812.
     HND - the return's blocks without duplicates.  The walk has ARx there (HAR2 at :4803, from
       ajournal_gx_AR_x on the journal premise), and NoDup (ablocks B ly S) is AR's standard law
       (W_LLVMFuzzerTestOneInput_add.v:277 ad_nodup); HHB2 at :4802-4805 is proved from exactly that and BLKN,
       and EB at :4810 carries it across stack_free_state.
   ROUTE R (a Theorem Labs lane, 2026-10-31): the rule is stated at any world relation R, its journal premise at
   ajournal_gx_xR .. R (W_journal_x.v): LS_exit_end3e_xR, for lib/A/W_LLVMFuzzerTestOneInput_exit_x.v's LS_exit_end_R (Section exitR).  The proof reads
   only the journal's `0 <= k'`, the same conjunct of ajournal_xR at every R.  The strict LS_exit_end3e is its instance
   at R := wle (ajournal_gx_x_wle: the two journals are equal by conversion). *)
Lemma LS_exit_end3e_xR : forall (R : world segs -> world segs -> Prop),
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  fr_LS3c B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 -> fr_ENT cx m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  (* HFH *) fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  (* HND *) List.NoDup (ablocks B ly' S') ->
  fr_live_post3 OM (c_S cx) (stack_free_state 1 fpos S') k' /\
  ACfn_cf.fr_surv B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem'.
Proof.
  intros R cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out HLS HOU HENT HP HP' Hfr Hmo HC Hcap Ht HJ HFH HND.
  assert (Hk : 0 <= k').
  { destruct HJ as (_ & _ & (memS & HAJ & _) & _).
    destruct HAJ as (_ & _ & _ & _ & _ & _ & _ & Hk0 & _). exact Hk0. }
  assert (EA : ablocks B ly' (stack_free_state 1 fpos S') = ablocks B ly' S') by reflexivity.
  assert (EB : blocks_bytes (stack_free_state 1 fpos S') = blocks_bytes S').
  { rewrite (blocks_bytes_bsum B ly' (stack_free_state 1 fpos S')), (blocks_bytes_bsum B ly' S'), EA. reflexivity. }
  (* the entry's blocks, split by fr_ENT at the exit's own rest *)
  pose proof (HENT rest HP) as HEnt.
  set (FHe := fr_hblks (c_W cx) (c_mem cx)) in *.
  set (NEW := (lm_G m, ATABLE) :: aout_blks cap out) in *.
  split.
  - unfold fr_live_post3. rewrite EB. split; [| exact Hk].
    exact (ou_exit_bytes B OM HOM cx t m ly3 S3 rest ly' S' cap out HLS HOU HP HP' Hcap Ht).
  - unfold ACfn_cf.fr_surv. rewrite EA, HFH. split; [| split].
    + intros b Hb Hnot.
      pose proof (Permutation_in b HEnt Hb) as Hin.
      apply in_app_iff in Hin as [Hin | Hin]; [| apply in_app_iff in Hin as [Hin | Hin]].
      * apply (Permutation_in b (Permutation_sym HP')). apply in_app_iff. left. exact Hin.
      * contradiction.
      * apply (Permutation_in b (Permutation_sym HP')). apply in_app_iff. right.
        apply in_cons, in_app_iff. right. exact Hin.
    + intros b Hb.
      pose proof (Permutation_in b HP' Hb) as Hin.
      apply in_app_iff in Hin as [Hin | Hin].
      * right. apply (Permutation_in b (Permutation_sym HEnt)). apply in_app_iff. left. exact Hin.
      * destruct Hin as [Hin | Hin]; [left; left; exact Hin|].
        apply in_app_iff in Hin as [Hin | Hin].
        -- left. right. exact Hin.
        -- right. apply (Permutation_in b (Permutation_sym HEnt)). apply in_app_iff. right.
           apply in_app_iff. right. exact Hin.
    + intros b Hb.
      destruct (in_dec zzdec b FHe) as [Hfe | Hfe]; [right; exact Hfe|]. left. intros Hin.
      (* b is one of the return's harness blocks and one of the entry's other blocks: it would be live twice *)
      pose proof (Permutation_in b HEnt Hin) as Hin2.
      assert (Hio : In b (input_blks cx) \/ In b rest).
      { apply in_app_iff in Hin2 as [X | X]; [left; exact X|].
        apply in_app_iff in X as [X | X]; [contradiction | right; exact X]. }
      assert (HP'N : Permutation (ablocks B ly' S') (input_blks cx ++ NEW ++ rest))
        by (unfold NEW; exact HP').
      assert (Hcnt : (count_occ zzdec (input_blks cx ++ NEW ++ rest) b <= 1)%nat).
      { pose proof (proj1 (Permutation_count_occ zzdec _ _) HP'N b) as Hq.
        pose proof (proj1 (NoDup_count_occ zzdec _) HND b) as Hc1. lia. }
      rewrite !count_occ_app in Hcnt.
      pose proof (proj1 (count_occ_In zzdec NEW b) Hb) as HbN.
      destruct Hio as [Hio | Hio];
        [pose proof (proj1 (count_occ_In zzdec (input_blks cx) b) Hio) as Hz
        | pose proof (proj1 (count_occ_In zzdec rest b) Hio) as Hz]; lia.
Qed.

(* the strict rule (lib/A/W_LLVMFuzzerTestOneInput_exit_x.v:183's LS_exit_end, through ReplyLSI.v lsi_LS_exit_end): LS_exit_end3e_xR at R := wle *)
Lemma LS_exit_end3e : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  fr_LS3c B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 -> fr_ENT cx m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  (* HFH *) fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  (* HND *) List.NoDup (ablocks B ly' S') ->
  fr_live_post3 OM (c_S cx) (stack_free_state 1 fpos S') k' /\
  ACfn_cf.fr_surv B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem'.
Proof. exact (LS_exit_end3e_xR (@wle segs)). Qed.
End oentx.
End oent.
