(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: group RI-gone of the image-A top (W_LLVMFuzzerTestOneInput_top_x.v, the rows
   RI_gone_pairs / RI_gone_read / RI_gone_step / RI_gone_end) at RINV := fr_RINV (ReplyRINV.v).  Proves no function
   walk (model-rule obligations only).
   Part 1 (over ReplyRINV.v's copies of the gone model, verbatim the same text as gone_base.v's):
   - RI_gone_pairs_holds: fr_RINV's pairing hj of the table with the open sources is a gn_pairs witness.  The size
     bounds gn_pair_ok asks come from fr_RINV's cost bound (fr_cost <= c_n < 2 ^ 26: a pending stream and a key count
     are parts of one entry's cost) and from fr_pair_ok's ecap_ok.
   - RI_gone_read_holds: a slot k that reads (gn_reads m k = 1) holds the source of an open entry j; that entry's
     gn_pair_ok source is at slot k (fr_RINV's distinct fds, RI_fds_holds), so after relay_instance_gone slot k holds
     rig_post's source for entry j, which rig_rel's dr_rel leaves drained (pending list empty, offset 0).
   - RI_gone_read_sat: one state meets all of RI_gone_read's premises (and RI_gone_pairs's).
   - Section collapse / collapse2: the records of rounds 1 and 2 of the gone rules' texts (bb9dae5d905, a1a3591c77c),
     which were false at the instance; machine-checked counter-instances, not proofs of the rows.
   Part 2 (over W_LLVMFuzzerTestOneInput_gone_base.v's own model): RI_gone_pairs_plug / RI_gone_read_plug restate
   part 1 at gone_base's GN_RI_pairs / GN_RI_read; then the step and end rows.
   - The table-order loop (gn_run) as an invariant (rg_inv): every entry's slot, once processed, holds what
     check_no_loss and check_shape_ends left of what relay_instance_gone left there; when gone = 0, `at` is the
     entry's position in the stream relay_instance_gone sent (rg_acc_pos), which is the entries' drained lines and
     then their ended keys' end lines (rg_rel_dec, rg_strm).
   - RI_gone_step_holds(_c): GN_RI_step of a working branch a39b599f92e (copied verbatim as
     GN_RI_step_d) at MT := ameter_triv, RINV := fr_RINV, MMAX := WR_MMAX, LS := fr_LS3 B / fr_LS3c B.  The LS-side
     conjunct cnl_room is a Theorem Labs lane's gx6_step_room(_c) (ReplyLS3cTopxGoneF.v at b25d82fcf04); mo_ok is True at
     ameter_triv; the rest is RINV-side (rg_step_rinv_side).
   - RI_gone_end_holds_q5(_c): GN_RI_end of a39b599f92e (copied as GN_RI_end_q5) with REQ5 (no held list's capacity
     shrinks from m to mc) as one more, last, premise: s5-r1d's gx6_end_LS3(_c) needs it, and a39b599f92e's gn_cnl_ok
     does not carry `hl_cap (hs_held h) <= hl_cap H'` from which ReplyLS3cTopxGoneH.v's gxh_req5 derives it.
   - GN_RI_step_r3 (Section rg3): the record of round 3 (aa34c06e82c): without re_U NUL-free the step row is false.
   Local helpers rg_lines_nz / rg_upds_in / rg_W_read_lines_nz state what a Theorem Labs lane's ReplyRINV_a12.v
   (lines_nul_free / upds_nul_free) states; they stay local. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v; 105 of its 196 lines of code are new or changed and 2832 lines of the source are left out. *)
(* The gone arm's LS conjuncts against the gone rules' premise lists (lib/A/W_LLVMFuzzerTestOneInput_gone_base.v
   GN_RI_step / GN_RI_end; W8's walk commit 6a2e02357a4 first stated these premises), at LS := fr_LS3 B / fr_LS3c B,
   RINV := fr_RINV, MT := ameter_triv, MMAX := WR_MMAX (= CfParamsReply.fr_MMAX), over gone_base's model.
   proves no function (kind: invariant lemma).
   The rules have, after RINV, `gn_op cx t m` and the per-entry premise (re_U NUL-free; each key NUL-free with
   14 <= |key| <= APARTIAL).  Of ReplyLS3cTopxGone.v's named hypotheses gx_xpre / gx_xstep / gx_xend these discharge
   lm_O m = [] (gn_op) and, of dr3_epre, re_U NUL-free and 14 <= |key|.  The rest is REQ1-REQ3 (after the per-entry
   premise, at the operation's start), REQ4 (last in GN_RI_step, at the loop's state), both in the rules, and REQ5
   (held vectors not shrinking), which the gx6_end rows take last and ReplyLS3cTopxGoneH.v derives (gxh_req5). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrain3 ReplyLS3Arms ReplyLSCntL ReplyLS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3cTopxGone.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.

Section fin.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma gx_nth_some_in : forall (l : list (option hsrc)) j h, nth j l None = Some h -> In (Some h) l.
Proof.
  induction l as [|o l IH]; intros [|j] h H; cbn in H; try discriminate.
  - left. exact H.
  - right. exact (IH j h H).
Qed.

(* gx_xpre from 6a2e02357a4's two new premises (gn_op, the per-entry premise), gn_pairs, and REQ1-REQ3 *)
Lemma gx_xpre_of6 : forall cx t m hs,
  gn_op cx t m ->
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
  gn_pairs m hs -> gx_xpre m hs.
Proof.
  intros cx t m hs (_ & HO & _) HE Hcap HE6 HS6 (_ & HP & _).
  split; [exact HO|]. split; [exact Hcap|].
  apply Forall_forall. intros [e [h j]] Hin Heof. cbn [fst snd] in *.
  pose proof (in_combine_l _ _ _ _ Hin) as He.
  rewrite Forall_forall in HE, HE6, HS6, HP.
  destruct (HE e He) as (HU & HK).
  destruct (HE6 e He) as (HUl & Hcp & Hkh).
  destruct (HP (e, (h, j)) Hin Heof) as (_ & Hnth & _). cbn [fst snd] in Hnth.
  pose proof (HS6 (Some h) (gx_nth_some_in _ _ _ Hnth)) as Hh. cbn beta iota in Hh.
  split; [|split].
  - unfold dr3_epre. split; [exact Hcp|]. split; [exact HUl|]. split; [exact HU|]. split.
    + intros Hhp. destruct Hkh as [(Hhp0 & _) | (_ & _ & H8)]; [contradiction | exact H8].
    + rewrite Forall_forall in HK |- *. intros k Hk. destruct (HK k Hk) as (_ & H14 & _). exact H14.
  - unfold ls3_kh. destruct Hkh as [H0 | (Hhp & Hn & _)]; [left; exact H0 | right; split; assumption].
  - exact Hh.
Qed.

(* ================================================================== E1: GN_RI_end's `LS cx (t + 1) mc lyx Sx` *)
(* the GN_RI_end premises, with REQ1-REQ3 after the per-entry premise and REQ5 last *)
Lemma gx6_end_LS3 : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (* REQ1 *) 0 <= lm_cap m ->
  (* REQ2 *)
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  (* REQ3 *)
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_LS3 B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (* REQ5 *)
  (forall j hj hj', nth j (lm_hs m) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
     hl_cap (hs_held hj) <= hl_cap (hs_held hj')) ->
  fr_LS3 B cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs Hafter Hrok Hrun
    Hmle Hfr Hns.
  exact (gx_end_LS3 B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI HLS Hpairs Hafter Hrok Hrun Hmle Hfr
    (conj (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hpairs) Hns)).
Qed.
Lemma gx6_end_LS3c : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (* REQ1 *) 0 <= lm_cap m ->
  (* REQ2 *)
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  (* REQ3 *)
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_LS3c B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (* REQ5 *)
  (forall j hj hj', nth j (lm_hs m) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
     hl_cap (hs_held hj) <= hl_cap (hs_held hj')) ->
  fr_LS3c B cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs Hafter Hrok Hrun
    Hmle Hfr Hns.
  exact (gx_end_LS3c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI HLS Hpairs Hafter Hrok Hrun Hmle Hfr
    (conj (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hpairs) Hns)).
Qed.

(* ================================================================== S1: GN_RI_step's cnl_room on blocks_bytes Sx *)
(* the GN_RI_step premises, with REQ1-REQ3 after the per-entry premise and REQ4 last *)
Lemma gx6_step_room : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (* REQ1 *) 0 <= lm_cap m ->
  (* REQ2 *)
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  (* REQ3 *)
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_LS3 B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (* REQ4 *)
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)).
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs Hafter Hrok
    Hrun Hmle Hfr Hi Hk Hh Hfd Hcnt.
  exact (gx_step_room B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI HLS Hpairs Hafter Hrok Hrun
    Hmle Hfr Hi Hk Hh Hfd (conj (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hpairs) Hcnt)).
Qed.
Lemma gx6_step_room_c : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (* REQ1 *) 0 <= lm_cap m ->
  (* REQ2 *)
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  (* REQ3 *)
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_LS3c B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (* REQ4 *)
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)).
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6 (HLS & _).
  exact (gx6_step_room cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS).
Qed.
End fin.
