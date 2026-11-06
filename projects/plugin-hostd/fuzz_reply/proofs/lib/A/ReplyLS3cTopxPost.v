(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 171 of its 248 lines of code are new or changed and 1150 lines of the source are left out. *)
(* top_x's free-post-state LS rules in the restated texts top_x adopts (a Theorem Labs lane's ruling after a Theorem Labs lane's
   vacuity finding, a working branch 2a368424fed lib/A/TopxVacuity.v topx_two_events_false).
   proves no function (kind: invariant lemma).
   - LS_event_step, LS_cnl_pre and LS_rm_cnl_pre: top_x (the TOP head 3d17f490d56) states them at this file's former
     TX_ texts, so the TX_ definitions are gone; ReplyLSI.v's lsi_* plugs state top_x's text at its instance.
   - TX_LS_drain_step / TX_LS_exit_end / TX_LS_exit_end_d stay: top_x takes the drain row with `0 <= t < OPS_MAX`
     and the exit row with ReplyLS3e.v's premises (ReplyLSI.v states those texts).  Argument order after the Section:
       TX_LS_drain_step TfibB MT LSx RINV;
       TX_LS_exit_end TfibB MT XN_LIB fr_live_post fr_surv NP fr_FP LSx ARX G (and {SK : sink_head});
       TX_LS_exit_end_d the same without NP.
     The drain rows name B1c's predicates dr3_epre / dr3_hpre / dr3_epost / dr3_hpost (ReplyLSDrain3.v:78-98) and
     ls3_kh / ls3_hn / ls3_dpost / ls3_cpost (ReplyLS3Arms.v:305-326): W8 copies their texts with the rows.
   - Plugs: tx_<row>_plug at MT := ameter_triv, LSx := fr_LS3c B, RINV := fr_RINV, TfibB := B.  LS_exit_end needs
     LS := fr_LS3c /\ fr_OUT (ReplyLS3o.v) and fr_live_post := fr_live_post3 OM, and concludes neither NP nor fr_surv
     (see TX_LS_exit_end_d).
   - tx_two_events_escapes: a8's two-events shape over top_x's LS_event_step text does not prove False (a model of
     all its hypotheses at LSx := fr_LS3c B). *)
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
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv SlotDrain3Aux SlotPass2Aux
  relay_remove_b_aux send_line_b_c RelayRunT RelayRunF ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak ReplyTrPeakC.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the five texts *)
Section tx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable TfibB : asyms.
Variable MT : ameter_ops.
Variable XN_LIB : Z -> Z.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable NP : astate -> Prop.
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable G : list (Z * Z).

(* top_x :422 (riplug :433) LS_drain_step; added (ReplyLS3cArms.v:119 fr_LS3c_drain_step_p): binders ly1 h1 E' H'
   and the twenty premises after top_x's five *)
Definition TX_LS_drain_step : Prop :=
  forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) -> dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 -> ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.

(* top_x :452 (riplug :465) LS_exit_end; added (ReplyLS3o.v:1062 LS_exit_end3_x): the three premises after top_x's
   seven (relay_finish's final capacity, the loop's t bound, and fr_surv itself); its LS is fr_LS3c /\ fr_OUT *)
Definition TX_LS_exit_end : Prop :=
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\ NP (stack_free_state 1 fpos S') /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* the same without top_x's NP conclusion (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d): the exit walk takes NP from the threaded room
   invariant), which is what LS_exit_end3_x concludes *)
Definition TX_LS_exit_end_d : Prop :=
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
End tx.

(* ================================================================== the plugs *)
Section plug.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.

Lemma tx_LS_drain_step_plug : TX_LS_drain_step B ameter_triv (fr_LS3c B) fr_RINV.
Proof. unfold TX_LS_drain_step. exact (fr_LS3c_drain_step_p B). Qed.

(* LS := fr_LS3c /\ fr_OUT (the exit's LS; ReplyLS3o.v) *)
Definition tx_LSo (OM : Z) : lfcx -> Z -> lmod -> alayout -> astate -> Prop :=
  fun cx t m ly S => fr_LS3c B cx t m ly S /\ fr_OUT OM cx t m ly S.

Lemma tx_LS_exit_end_d_plug : forall OM, OUT_MAX4 <= OM ->
  forall XN_LIB fr_surv fr_FP ARX G,
  TX_LS_exit_end_d B ameter_triv XN_LIB (fr_live_post3 OM) fr_surv fr_FP (tx_LSo OM) ARX G.
Proof.
  intros OM HOM XN_LIB fr_surv fr_FP ARX G. unfold TX_LS_exit_end_d.
  intros cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out (HLS & HOU) HP HP' Hfr Hmo HC HJ Hcap Ht HSURV.
  eapply LS_exit_end3_x; eassumption.
Qed.

End plug.

(* ================================================================== a8's argument no longer goes through *)
Section vac.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Notation MT := ameter_triv.

(* (a) a8's proof instantiates S1 := S (2a368424fed TopxVacuity.v:146); TX's malloc premise rules that out *)
Lemma tx_a8_instance_blocked : forall ly ly1 (S : astate) q n, ablocks B ly1 S <> ablocks B ly S ++ [(q, n)].
Proof.
  intros ly ly1 S q n H. apply (f_equal (@length _)) in H. unfold ablocks in H.
  rewrite length_app, !length_map in H. cbn [length] in H. lia.
Qed.

(* (b) for ANY LSx, TX's premises fix S3's live bytes: the start's, plus g_out's change (the event buffer is malloc'd
   and freed), so S3 is not arbitrary *)
Lemma tx_event_S3_bytes : forall ly S (S1 S2 S3 : astate) (ly1 ly2 ly3 : alayout) q n cap out cap' out',
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, n)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks cap out ++ rest) /\
     Permutation (ablocks B ly2 S2) (aout_blks cap' out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, n) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  blocks_bytes S3 = blocks_bytes S + bsum (aout_blks cap' out') - bsum (aout_blks cap out).
Proof.
  intros ly S S1 S2 S3 ly1 ly2 ly3 q n cap out cap' out' Hm (rest & HR1 & HR2) (l1 & l2 & Hf2 & Hf3).
  rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly S), Hf3.
  assert (E1 : bsum (ablocks B ly1 S1) = bsum (ablocks B ly S) + n) by (rewrite Hm, bsum_app, bsum_cons, bsum_nil; cbn [snd]; lia).
  rewrite (bsum_perm _ _ HR1), bsum_app in E1.
  assert (E2 : bsum (ablocks B ly2 S2) = bsum l1 + n + bsum l2) by (rewrite Hf2, bsum_app, bsum_cons; cbn [snd]; lia).
  rewrite (bsum_perm _ _ HR2), bsum_app in E2.
  rewrite bsum_app. lia.
Qed.

(* (c) a8's two-events shape (2a368424fed TopxVacuity.v:122-141), byte for byte, with its LS_event_step replaced by
   top_x's (3d17f490d56) LS_event_step text at TfibB := B *)
Definition tx_two_events_shape : Prop :=
  forall (LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop) (RINV : lfcx -> Z -> lmod -> Prop),
  (forall cx t m e v out',
     RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
     ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
     RINV cx (t + 1) (ev_step cx m e v out')) ->
  (forall cx t m ly S e,
     LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
     re_len e < CfParamsReply.fr_MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e))) ->
  (forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
     LSx cx t m ly S -> ev_evt cx m e ->
     mo_le MT S S1 (mo_malloc MT (re_len e)) ->
     mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
     mo_le MT S2 S3 (mo_free MT) ->
     0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
     ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
     (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
        Permutation (ablocks B ly2 S2)
          (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
     (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
     LSx cx (t + 1) (ev_step cx m e v out') ly3 S3) ->
  forall cx t m ly S e v out' e',
  LSx cx t m ly S -> RINV cx t m ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  ev_evt cx (ev_step cx m e v out') e' ->
  False.

(* the witness: fr_LS3_sat's first-head state (ReplyLS3.v sat3) with the input byte 7 (an event op) *)
Definition tx_cx7 : lfcx :=
  LFCX (c_ly (ls3_cx B)) (c_S (ls3_cx B)) (c_W (ls3_cx B)) (c_regs (ls3_cx B)) (c_mem (ls3_cx B)) (c_md (ls3_cx B))
    (c_p (ls3_cx B)) (c_n (ls3_cx B)) [Z_to_bv 8 7] (c_M (ls3_cx B)).
Lemma tx_sat7 : fr_LS3c B tx_cx7 0 (ls3_m B) ls3_ly ls3_S.
Proof.
  assert (EA : ablocks B ls3_ly ls3_S = input_blks tx_cx7 ++ model_blks (ls3_m B) ++ []) by reflexivity.
  split.
  - exists [], 0.
    assert (Hbb : blocks_bytes ls3_S = 1 + ATABLE + APARTIAL) by (vm_compute; reflexivity).
    assert (Hin : bsum (input_blks tx_cx7) = 1) by reflexivity.
    assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
    assert (HS : c_S tx_cx7 = ls3_S) by reflexivity.
    assert (Hn : c_n tx_cx7 = 1) by reflexivity.
    assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
    assert (HL : LIVE_MAX = 17179869184) by reflexivity.
    assert (En : npend (ls3_m B) = 0) by reflexivity.
    assert (Ek : kk tx_cx7 (ls3_m B) = 0) by reflexivity.
    assert (Eo : nopen (lm_hs (ls3_m B)) = 1) by reflexivity.
    assert (Ep : PHI3 (ls3_m B) = ATABLE + APARTIAL + E_ENT + K0) by reflexivity.
    rewrite EA, HS, Hbb, Hn, Hin, Hrest, HC, HL, En, Ek, Eo, Ep.
    split; [apply Permutation_refl|].
    unfold W_OPEN, MB_K, MB_C, ATABLE, APARTIAL, E_ENT, K0.
    refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
  - unfold fr_CNT. rewrite EA, !cnt_sec_app, cnt_sec_nil.
    assert (En : npend (ls3_m B) = 0) by reflexivity.
    split; [unfold SEC0; lia | split; [| rewrite En; lia]].
    intros c. rewrite !cnt_cls_app, cnt_cls_nil. unfold CLS0. lia.
Qed.
Lemma tx_evt_nil7 : forall m, ev_len tx_cx7 m = 0 -> ev_evt tx_cx7 m [].
Proof.
  intros m H. unfold ev_evt. rewrite H. cbn [length Z.of_nat].
  refine (conj _ (conj _ (conj _ _))); [lia | intros i Hi; lia | intros Hin; destruct Hin | intros Hl; lia].
Qed.

(* the escape: at LSx := fr_LS3c B (the event row by ReplyLS3cArms.v fr_LS3c_event_step_p), RINV := True, the
   hypotheses of a8's theorem all hold at the witness, so the shape does not prove False *)
Theorem tx_two_events_escapes : ~ tx_two_events_shape.
Proof.
  intros H.
  refine (H (fr_LS3c B) (fun _ _ _ => True) _ _ (fr_LS3c_event_step_p B)
    tx_cx7 0 (ls3_m B) ls3_ly ls3_S [] 0 0 [] tx_sat7 I _ _ _ _ _ _).
  - intros. exact I.
  - intros cx t m ly S e HL _ (He & _).
    pose proof (fr_LS3_room B cx t m ly S (proj1 HL)) as Hroom. pose proof (fr_LS3_k B cx t m ly S (proj1 HL)) as Hk.
    destruct HL as ((rest & e0 & _ & _ & _ & Hc & _) & _).
    assert (Hk0 : 0 <= lm_k m) by (unfold kk in Hk; lia).
    pose proof (ev_len_le cx m Hk0 ltac:(lia)) as Hl.
    assert (HW : CfParamsReply.fr_MMAX = 1072693248) by reflexivity.
    unfold re_len, ROOM_SPARE in *. refine (conj _ (conj _ (mo_ok_triv _ _))); lia.
  - change (0 <= 0 < 1). lia.
  - reflexivity.
  - reflexivity.
  - apply tx_evt_nil7. reflexivity.
  - lia.
  - apply tx_evt_nil7.
    assert (Ek : lm_k (ev_step tx_cx7 (ls3_m B) [] 0 0) = 1) by reflexivity.
    unfold ev_len. rewrite Ek. reflexivity.
Qed.
End vac.
