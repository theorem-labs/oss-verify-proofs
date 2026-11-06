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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v; 138 of its 234 lines of code are new or changed and 2827 lines of the source are left out. *)
(* REQ5 ("no held capacity shrinks from m to mc", the gone-rule request (sha256 b345d98e85b2; internal record)) derived from GN_RI_end's own
   premises, over lib/A/W_LLVMFuzzerTestOneInput_gone_base.v's model, whose gn_cnl_ok carries the bound the program
   keeps, `hl_cap (hs_held h) <= hl_cap H'` (W8's 2b1ed64e05b).  proves no function (kind: invariant lemma).
   - gxh_rig_held: relay_instance_gone keeps every held list from m to m1 (gn_after_rig's kept-slot clause for a
     slot it does not drain; for a drained slot, gn_pair_ok's slot and dr_rel's `hs_held h1 = hs_held h`,
     W_contract.v:1267, through gn_rig_ok's rig_rel).  No fact beyond the rule's premises is needed.
   - gxh_run_held: gn_run never lowers a held capacity (gn_cnl_ok's eighth conjunct, and check_shape_ends'
     hl_cap H'' = hl_cap held).
   - gxh_req5: REQ5 at any loop point; gx7_*: the gone rows with no REQ5 premise. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3cTopxGone ReplyLS3cTopxGoneF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.

Section gh.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================== the slot lists *)
Lemma gxh_setn_same : forall k x (l : list (option hsrc)) y, nth k l None = Some y -> nth k (gn_setn k x l) None = x.
Proof.
  induction k as [|k IH]; intros x [|z l] y H; cbn in *; try discriminate; [reflexivity | exact (IH x l y H)].
Qed.
Lemma gxh_setn_other : forall k j x (l : list (option hsrc)), j <> k -> nth j (gn_setn k x l) None = nth j l None.
Proof.
  induction k as [|k IH]; intros j x [|z l] Hne; cbn; try reflexivity.
  - destruct j as [|j]; [congruence | reflexivity].
  - destruct j as [|j]; [reflexivity | apply IH; lia].
Qed.

(* ================================================================== m -> m1: relay_instance_gone keeps held lists *)
(* a slot that holds a source in m holds one in m1 with the same held list: kept slots by gn_after_rig's clause
   (6a2e02357a4 gone_base.v:434-435), drained slots by gn_pair_ok's slot (:418) and dr_rel's hs_held clause
   (W_contract.v:1267) through gn_rig_ok's rig_rel (:450-451) *)
Lemma gxh_rig_held : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  forall j hj, nth j (lm_hs m) None = Some hj ->
  exists hj1, nth j (lm_hs m1) None = Some hj1 /\ hs_held hj1 = hs_held hj.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok j hj Hj.
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hpairs as (Hlh & _ & _).
  pose proof Hrok as (Hrr & Hlq & _ & _).
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof (gx_rig_pairs _ _ _ _ _ _ _ _ _ _ Hrr) as HRP.
  rewrite Forall_forall in HPQ, HRP.
  assert (Hj4 : (j < 4)%nat).
  { pose proof HRI as (_ & (Hl4 & _) & _).
    destruct (Nat.lt_ge_cases j (length (lm_hs m))) as [L|L]; [lia|].
    rewrite nth_overflow in Hj by exact L. discriminate Hj. }
  set (ps := combine (lm_es m) hs) in *.
  destruct (in_dec Nat.eq_dec j (rig_slots ps)) as [Hin|Hnin].
  2: { exists hj. split; [rewrite (A12 j Hj4 Hnin); exact Hj | reflexivity]. }
  destruct (gx_rs_in j ps Hin) as (p & Hp & Heof & Hpk).
  destruct (In_nth ps p (gn_e0, gn_hj0) Hp) as (i & Hi & Hpi).
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  set (q := nth i qs gn_q0).
  assert (Hpq : In (p, q) (combine ps qs)).
  { rewrite <- Hpi. unfold q. rewrite <- combine_nth by exact Hlps. apply nth_In. rewrite length_combine. lia. }
  destruct (HRP _ Hpq) as (_ & Hdr). cbn [fst snd] in Hdr.
  destruct (Hdr Heof) as (c & mx & no & cap & e1 & LB & Hd).
  destruct (HPQ _ Hpq Heof) as (_ & Hm & Hm1). cbn [fst snd] in Hm, Hm1.
  destruct p as [e [h0 j']]. cbn [fst snd] in *. subst j'.
  rewrite Hj in Hm. injection Hm as Eh0. subst h0.
  destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dheld & _).
  exists (snd q). split; [exact Hm1 | exact Dheld].
Qed.

(* ================================================================== m1 -> mc: the loop never lowers a held capacity *)
Lemma gxh_run_held : forall P m1 mc A i k, gn_run P m1 mc A i k ->
  forall j hj hj', nth j (lm_hs m1) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
  hl_cap (hs_held hj) <= hl_cap (hs_held hj').
Proof.
  intros P m1 mc A i k HR.
  induction HR as [|mc A i k HR IH Hk Hs|mc A i k h h' h'' E' H' ds c HR IH Hk Hi Hh Hfd Hc Hcs|mc A i HR IH];
    intros j hj hj' H1 H2.
  - rewrite H1 in H2. injection H2 as E2. subst hj'. lia.
  - exact (IH j hj hj' H1 H2).
  - cbn [gn_set lm_hs] in H2.
    destruct (Nat.eq_dec j k) as [->|Hne].
    + rewrite (gxh_setn_same k (Some h'') (lm_hs mc) h Hh) in H2. injection H2 as E2. subst hj'.
      pose proof (IH k hj h H1 Hh) as Hle.
      destruct Hc as (Eh' & _ & _ & _ & _ & _ & _ & Hb & _).
      destruct Hcs as (H2' & Eh'' & _ & Hc2 & _).
      subst h'' h'. cbn [set_held set_exp_held hs_held] in Hc2, Hb |- *. lia.
    + rewrite (gxh_setn_other k j (Some h'') (lm_hs mc) Hne) in H2. exact (IH j hj hj' H1 H2).
  - exact (IH j hj hj' H1 H2).
Qed.

(* ================================================================== REQ5 from the rule's own premises *)
Lemma gxh_req5 : forall cx t m hs qs c2 O2 cap2 out2 m1 mc A i k,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gn_run (gn_pre cx m) m1 mc A i k ->
  forall j hj hj', nth j (lm_hs m) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
  hl_cap (hs_held hj) <= hl_cap (hs_held hj').
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A i k HRI Hpairs Hafter Hrok Hrun j hj hj' Hj Hj'.
  destruct (gxh_rig_held cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok j hj Hj) as (hj1 & Hj1 & Eh).
  pose proof (gxh_run_held _ m1 mc A i k Hrun j hj1 hj' Hj1 Hj') as Hle.
  rewrite Eh in Hle. exact Hle.
Qed.

Variable B : asyms.

(* ================================================================== E1, no REQ5 *)
(* the GN_RI_end premises, and REQ1-REQ3 after the per-entry premise; no REQ5 *)
Lemma gx7_end_LS3 : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
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
  fr_LS3 B cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs Hafter Hrok Hrun
    Hmle Hfr.
  exact (gx6_end_LS3 B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs Hafter
    Hrok Hrun Hmle Hfr
    (gxh_req5 cx t m hs qs c2 O2 cap2 out2 m1 mc A _ _ HRI Hpairs Hafter Hrok Hrun)).
Qed.
Lemma gx7_end_LS3c : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
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
  fr_LS3c B cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs Hafter Hrok Hrun
    Hmle Hfr.
  exact (gx6_end_LS3c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs Hafter
    Hrok Hrun Hmle Hfr
    (gxh_req5 cx t m hs qs c2 O2 cap2 out2 m1 mc A _ _ HRI Hpairs Hafter Hrok Hrun)).
Qed.

(* ================================================================== S1 *)
(* the same rows as ReplyLS3cTopxGoneF.v's *)
Lemma gx7_step_room : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
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
    Hrun.
  exact (gx6_step_room B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs
    Hafter Hrok Hrun).
Qed.
Lemma gx7_step_room_c : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
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
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS Hpairs Hafter Hrok
    Hrun.
  exact (gx6_step_room_c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS
    Hpairs Hafter Hrok Hrun).
Qed.
End gh.
