(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v, with its module paths and module names changed; 340 of its 445 lines of code are new or changed and 489 lines of the source are left out. *)
(* proves no function (kind: model and invariant lemmas): fr_ENT, the entry half of LS v3 at image B, its twin of
   every rule, and the exit's LS_exit_end CONCLUDING fr_surv *)
(* Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3e.v (sha256
   e92ab3744c8b; internal record) at d9e8f914caa (row G-BLS3-port).  Every definition
   is A's text and every lemma keeps A's name and statement but for the swaps below; each piece cites its A line
   (A = lib/A/ReplyLS3e.v).
   A -> B SWAPS (as lib/B/ReplyB3LS3.v and ReplyB3LS3Arms.v make them):
   - the Require header is lib/B/ReplyB3LS3Arms.v's (lib/B YB1v, YE01, YE2k, `Require YCfn`, lib/B W_*, ReplyGuardB,
     _cut, _cut_x, the drain arm's model lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v, YCfn_cf) plus the B arm files
     _head / _small / _write / _add (the sm_, upd_, wr_ and ad_ names), W_journal_x (ajournal_gx_x), and, Required only,
     lib/B/W_bx_defs.v (A's W_LLVMFuzzerTestOneInput_exit.lx_rf_run / lx_exit_cost: B's exit model) and
     lib/B/W_LLVMFuzzerTestOneInput_gone_base.v (A's ReplyLS3cTopxDefs / ReplyLS3cTopxGoneF copies gn_op, gn_pairs,
     gn_after_rig, gn_rig_ok, gn_run, gn_pre: B's gone arm's own texts, the ones its GN_RI_end names);
   - lib/A ReplyLS / ReplyLSArms / ReplyRINV / ReplyLS3 / ReplyLSCntL / ReplyLS3c / ReplyLS3Arms (with A's ReplyLSDrain3,
     ReplyLSRemove3, ReplyLSEvent3 facts) -> lib/B ReplyLSB, ReplyB3Base, ReplyLSBArms, ReplyRINVB, ReplyB3LS3,
     ReplyB3LSCntL, ReplyB3LS3c, ReplyB3LS3Arms (dr3_dset_perm, rm_mk, rm_cev); A's ReplyLSEvent3 ev3_pfx /
     ev3_model_blks / ev3_bsum_aout_eq -> lib/B/ReplyLSBArms.v bt_pfx / bt_model_blks / bt_bsum_aout_eq;
   - lib/A ReplyLS3o (fr_OUT, OUT_MAX4) -> lib/B/ReplyLSBo.v (xb_perm is its bo_xb_perm) and lib/B/ReplyLSBoRf.v (kw5s,
     rf_sum, rf_sum_mass, ou_gse_cap).  The ReplyLS3o names this file reads and lib/B lacks are proved here under A's
     name with an `_e` suffix: ou_rf_cap_e (A ReplyLS3o.v :961-975), fr_live_post3_e (:985-986), ou_exit_bytes_e
     (:990-1012);
   - lib/A ReplyLS3cTopx's fr_hblks -> lib/B/W_LLVMFuzzerTestOneInput_cut.v :254 fr_hblks, B's one definition;
   - fr_LS3 B -> fr_LS3 B CALL_ROOM_B and fr_LS3c B -> fr_LS3c B CALL_ROOM_B: the Section takes the Variable
     CALL_ROOM_B after B (lib/B/ReplyB3LS3.v's ruling).  fr_ENT restates no clause of fr_LS3 and reads no room, so it
     stays `fr_ENT B`; no lemma here reads CALL_ROOM_B's value;
   - the Section's Context is {fx} {rc} {SK : YI16.sink_head} (A: {LSH : lib_shape}, then {SK} in Section oentx):
     lib/B/ReplyGuardB.v removes the sink classes' hints, as lib/B/ReplyLSB.v :144;
   - LS_exit_end3e: A's LLVMF_STK (lib/A ACfn) -> YCfn.LLVMF_STK, as lib/B/W_LLVMFuzzerTestOneInput_exit_x.v :80;
   - KF-COUNT (the meter pattern of a Theorem Labs lane, A #6, as A's ReplyLS3e.v): A's MT := ameter_triv -> Section oent's
     Context {MT : ameter_ops}, implicit (read off the rules' mo_le arguments; no rule here reads it).  LS_exit_end3e
     no longer concludes the exit's meter conjunct `mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx))`
     (proved by `exact I` at ameter_triv; the B instance's, from its count clause), so Section oentx's variable XN_LIB
     is gone.
   A's header follows. *)
(* The entry half of LS v3: fr_ENT, the conjunct that keeps the call's REST the entry's rest, its twin of every
   rule, and the exit's LS_exit_end CONCLUDING fr_surv.  proves no function (kind: invariant lemma).

   WHY.  a8's fr_surv (ACfn_cf.v at a389032ec36 :94-98) relates the entry's live blocks to the return's.  Row B1c's
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT drain_b_c send_line_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c
  RelayCap SlotReads SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBArms ReplyLSBTrPeak ReplyRINVB.
(* the arm files after ReplyLSBArms: the wr_* names are B's _write.v's (lib/B/ReplyB3Base.v's ruling) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBo ReplyLSBoRf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3Base ReplyB3LS3 ReplyB3LSCntL ReplyB3LS3c ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_bx_defs W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* B's gone arm's model (lib/B/W_LLVMFuzzerTestOneInput_gone_base.v :380, :420, :439, :444, :458, :491) *)
Local Notation gn_op := W_LLVMFuzzerTestOneInput_gone_base.gn_op.
Local Notation gn_pre := W_LLVMFuzzerTestOneInput_gone_base.gn_pre.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
Local Notation gn_after_rig := W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig.
Local Notation gn_rig_ok := W_LLVMFuzzerTestOneInput_gone_base.gn_rig_ok.
Local Notation gn_run := W_LLVMFuzzerTestOneInput_gone_base.gn_run.

(* block lists are permutations when their count_occ agree: ReplyLS3c.v's perm_lia3, which its Section keeps
   (A :85-90) *)
Ltac ent_perm :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

Section oent.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the call room of fr_LS3 (lib/B/ReplyB3LS3.v, as ReplyLSB.fr_LS takes it) *)
Variable CALL_ROOM_B : Z.
(* the meter (KF-COUNT): a Variable, implicit, read off the rules' mo_le arguments; no rule here reads it *)
Context {MT : ameter_ops}.

(* the call's rest is the entry's rest: every block that is neither the input block nor one of the model's is a
   block the entry already had outside its harness blocks (A :96-100) *)
Definition fr_ENT (cx : lfcx) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
    Permutation (ablocks B (c_ly cx) (c_S cx)) (input_blks cx ++ fr_hblks (c_W cx) (c_mem cx) ++ rest).

(* ================================================================== the rest is unique up to Permutation (A :102-132) *)
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

(* ================================================================== the rules that move neither state nor blocks
   (A :134-161) *)
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

(* ================================================================== op_add's open (A :163-175) *)
Lemma fr_ENT_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3 B CALL_ROOM_B cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
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

(* ================================================================== the write arm's push (A :177-240) *)
Lemma fr_ENT_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
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

(* ================================================================== the drain arm's step (A :242-286) *)
Lemma fr_ENT_drain_step_p : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B CALL_ROOM_B cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
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

(* ================================================================== the remove arm's step (A :288-299) *)
Lemma fr_ENT_rm_step_p : forall cx t m ly0 S0 (ly : alayout) (S : astate) si j0 c2 O2 cap2 out2 ev5,
  fr_LS3 B CALL_ROOM_B cx t m ly0 S0 ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  fr_ENT cx m ly0 S0 -> fr_ENT cx (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si j0 c2 O2 cap2 out2 ev5 HLS Hfr HE.
  destruct HLS as (rest & e0 & HP & _).
  exact (fr_ENT_step cx m ly0 S0 _ ly S rest HP (Hfr rest HP) HE).
Qed.

(* ================================================================== the event arm's step (A :301-328) *)
Lemma fr_ENT_event_step_p : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS3 B CALL_ROOM_B cx t m ly S ->
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
  rewrite (bt_model_blks (ev_step cx m e v out')).
  rewrite (bt_model_blks m) in HP.
  assert (Ep : bt_pfx (ev_step cx m e v out') = bt_pfx m) by reflexivity.
  assert (Ec : lm_cap (ev_step cx m e v out') =
               sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) by reflexivity.
  assert (Eo : lm_out (ev_step cx m e v out') = out') by reflexivity.
  rewrite Ep, Ec, Eo.
  clear - HP HmP HR1 HR2 Hf2P Hf3P. ent_perm.
Qed.

(* ================================================================== the first head (the prologue) (A :330-353) *)
(* NAMED HYPOTHESIS HFH0: the entry's harness blocks are the table g_src names and g_out's buffer, the same three
   reads fr_hblks makes (lib/B/W_LLVMFuzzerTestOneInput_cut.v :254-258).  SEG_PRO holds it where it reads T0, cap and
   out out of the entry's memory to build this premise; fr_LS3c_pro (ReplyB3LS3c.v) keeps only the blocks. *)
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

(* ================================================================== the gone arm's end (A :355-385) *)
(* 6a2e02357a4 GN_RI_end's premises, in gx6_end_LS3c's order (lib/A/ReplyLS3cTopxGoneF.v:140-163), over B's gone
   arm's model (lib/B/W_LLVMFuzzerTestOneInput_gone_base.v); fr_ENT needs only the block relation and fr_LS3's rest, so
   RINV, gn_op, the per-entry premise, REQ1-REQ3, gn_pairs, gn_after_rig, gn_rig_ok, gn_run, mo_le and REQ5 are taken
   and not read. *)
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
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_ENT cx m ly S ->
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

(* ================================================================== relay_finish over the table (A ReplyLS3o.v
   :960-975 ou_rf_cap, which lib/B/ReplyLSBoRf.v lacks; its gestures_end lemma ou_gse_cap is ReplyLSBoRf's) *)
Lemma ou_rf_cap_e : forall es c O mx no cap, 0 <= cap ->
  cap <= gse_cap (W_bx_defs.lx_rf_run c O mx no cap es) /\
  gse_cap (W_bx_defs.lx_rf_run c O mx no cap es) <= Z.max cap (2 * (no + rf_sum es)) /\
  no <= gse_no (W_bx_defs.lx_rf_run c O mx no cap es) <= no + rf_sum es.
Proof.
  induction es as [|e es IH]; intros c O mx no cap Hc.
  - cbn [W_bx_defs.lx_rf_run gse_cap gse_no snd fst]. rewrite rf_sum_nil.
    repeat split; lia.
  - cbn [W_bx_defs.lx_rf_run]. rewrite rf_sum_cons.
    destruct (ou_gse_cap (gse_keys e) c O mx no cap Hc) as (G1 & G2 & G3).
    destruct (IH (gse_c (gse_run c O mx no cap (gse_keys e))) (gse_O (gse_run c O mx no cap (gse_keys e))) mx
                 (gse_no (gse_run c O mx no cap (gse_keys e))) (gse_cap (gse_run c O mx no cap (gse_keys e)))
                 ltac:(lia)) as (I1 & I2 & I3).
    pose proof (rf_sum_nonneg es). pose proof (kw5s_nonneg (gse_keys e)). repeat split; lia.
Qed.

(* ================================================================== the exit, now concluding fr_surv (A :387-485) *)
Section oentx.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).

(* copied from a8's working branch a389032ec36 lib/A/ACfn_cf.v:94-98 (its fr_hblks is the cut's, the
   one read above) (A :399-405) *)
Definition fr_surv_e (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) : Prop :=
  (forall b, In b (ablocks B ly S) -> ~ In b (fr_hblks W mem) -> In b (ablocks B ly' S')) /\
  (forall b, In b (ablocks B ly' S') -> In b (fr_hblks W' mem') \/ In b (ablocks B ly S)) /\
  (forall b, In b (fr_hblks W' mem') -> ~ In b (ablocks B ly S) \/ In b (fr_hblks W mem)).

(* A ReplyLS3o.v :985-986 fr_live_post3 (lib/B/ReplyLSBo.v lacks it): ACfn_cf.fr_live_post with a8's OUT_MAX read as
   the parameter OM *)
Definition fr_live_post3_e (S S' : astate) (k : Z) : Prop :=
  blocks_bytes S' <= blocks_bytes S + ATABLE + OM /\ 0 <= k.

(* A ReplyLS3o.v :988-1012 ou_exit_bytes (lib/B/ReplyLSBo.v lacks it).  THE BYTES AT THE RETURN: the exit keeps the
   relay's table and g_out and frees everything else of the model, and g_out's final capacity is relay_finish's, which
   is at most twice the model's mass. *)
Lemma ou_exit_bytes_e : forall cx t m ly3 S3 rest ly' S' cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  blocks_bytes S' <= blocks_bytes (c_S cx) + ATABLE + OM.
Proof.
  intros cx t m ly3 S3 rest ly' S' cap out (HLS & _) (U1 & U2 & U3 & U4) HP HP' Hcap Ht.
  destruct (ou_rf_cap_e (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) U1) as (R1 & R2 & _).
  rewrite <- Hcap in R1, R2.
  assert (Hc0 : 0 <= cap) by lia.
  assert (EX : XB cx m S3 = blocks_bytes (c_S cx) - bsum (input_blks cx) - bsum rest)
    by exact (bo_xb_perm B cx m ly3 S3 rest HP).
  assert (EB' : blocks_bytes S' = bsum (input_blks cx) + ATABLE + cap + bsum rest).
  { rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP').
    repeat progress (rewrite ?bsum_app, ?bsum_cons). cbn [snd].
    rewrite (bt_bsum_aout_eq cap out Hc0). lia. }
  pose proof (rf_sum_mass (lm_es m)) as Hrf.
  assert (Hmass : MASSe (lm_es m) <= MASS m).
  { unfold MASS. assert (0 <= pend_bytes m) by (apply zsum_map_nonneg; exact slot_pend_nonneg). lia. }
  unfold WMAX, OUT_MAX4, OPS_MAX in *. lia.
Qed.

(* LS_exit_end at LS := fr_LS3c /\ fr_OUT /\ fr_ENT: the ARx text of lib/B/W_LLVMFuzzerTestOneInput_exit_x.v
   :150-159 (A's exit_x.v:158-167 with B's names) with row B1c's ONE added premise `cap = gse_cap (lx_rf_run ..)`, NP
   dropped (ROOM-TEXTS.md:218-219 sha256 767baa12f13c; internal record), and fr_surv now a CONCLUSION.  Its two added premises are the walk's own facts, each
   at the site that holds it in lx_end_of_ffexit_x (A's walk, integ exit_x.v):
     HFH - fr_hblks W' mem' = the kept table and g_out.  The walk gets it in two steps: fr_hblks W3 mem3 =
       fr_hblks W2 mem2 at :4827 (fr_hblks_kept, from KEEP at :4809 and lx_glob_lits at :4824), and
       fr_hblks W2 mem2 = (lm_G m0, ATABLE) :: aout_blks (lm_cap m) (lm_out m) from HM2's g_src / relay / g_out
       clauses HSL, HRL, HOUT at :4820-4821 - the same three reads fr_hblks makes (B _cut.v:251-255) - with EM
       at :4811-4812.
     HND - the return's blocks without duplicates.  The walk has ARx there (HAR2 at :4803, from
       ajournal_gx_AR_x on the journal premise), and NoDup (ablocks B ly S) is AR's standard law
       (W_LLVMFuzzerTestOneInput_add.v:276 ad_nodup); HHB2 at :4802-4805 is proved from exactly that and BLKN,
       and EB at :4810 carries it across stack_free_state. *)
Lemma LS_exit_end3e : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 -> fr_ENT cx m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  (* HFH *) fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  (* HND *) List.NoDup (ablocks B ly' S') ->
  fr_live_post3_e (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv_e (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem'.
Proof.
  intros cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out HLS HOU HENT HP HP' Hfr Hmo HC Hcap Ht HJ HFH HND.
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
  - unfold fr_live_post3_e. rewrite EB. split; [| exact Hk].
    exact (ou_exit_bytes_e cx t m ly3 S3 rest ly' S' cap out HLS HOU HP HP' Hcap Ht).
  - unfold fr_surv_e. rewrite EA, HFH. split; [| split].
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
End oentx.
End oent.
