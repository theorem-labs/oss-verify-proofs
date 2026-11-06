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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v; 198 of its 316 lines of code are new or changed and 2805 lines of the source are left out. *)
(* The gone rules lib/A/W_LLVMFuzzerTestOneInput_gone_base.v GN_RI_step / GN_RI_end (W8's text with REQ1-REQ5,
   a working branch 1fcc03569d3, at a Theorem Labs lane's KF-COUNT text 6151e809fb3: the meter cost
   cst bounded by gn_runc / gn_cst, check_no_loss's post at its own cost), and B1c's LS / meter halves of them proved
   at their exact premise lists.  proves no function (kind: invariant lemma).
   - G8.GN_RI_*_ri / _ls / _room / _meter: B1c's split of each rule into its RINV part and its LS / meter part, each
     with the rule's premise list verbatim over gone_base's model, and G8.GN_RI_*_split, which gives gone_base's rule
     from its parts.  Module G8 holds only these (a Theorem Labs lane's ReplyRINV_gone.v names G8.GN_RI_step_ri /
     G8.GN_RI_end_ri).
   - gx8_*: the LS parts at LS := fr_LS3 B, fr_LS3c B and tx8_LSx OM := fr_LS3c B /\ fr_OUT OM /\ fr_ENT B,
     RINV := fr_RINV, MT a Variable (KF-COUNT; implicit, read off the rules' mo_le premise, which no proof reads),
     MMAX := CfParamsReply.fr_MMAX; REQ5 is derived inside (gxh_req5).  GN_RI_step's two meter conjuncts are
     ReplyLSI.v's (from its fr_SEC), not this file's.
   - gx8_GN_RI_end_*: the whole end rule from its RINV part. *)
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
  ReplyLS3cTopxGone ReplyLS3cTopxGoneF ReplyLS3cTopxGoneH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o ReplyLS3oGn ReplyLS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module G8.
Section g8.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* lib/A/W_LLVMFuzzerTestOneInput_gone_base.v's Section g Variables, in its order (B :170, MT :171, LS :179, RINV :180; MMAX :499 below) *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* gone_base.v:499 *)
Variable MMAX : Z.
(* ---- B1c's split of the two rules into their RINV part and their LS / meter part (NOT W8's texts): each has the
   premise list of gone_base's rule, verbatim (at a Theorem Labs lane's KF-COUNT text 6151e809fb3: the binder q, gn_runc and
   gn_cst; check_no_loss's post at its own cost); the split lemmas below give the rule from its parts ---- *)
Definition GN_RI_step_ri : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst q,
  RINV cx t m -> gn_op cx t m ->
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
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> gn_runc MT (gn_pre cx m) m1 mc A i k q ->
  mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  (forall h' E' H' (Sy : astate), gn_cnl_ok h h' E' H' ->
     mo_le MT Sx Sy (cnl_cost MT (hs_expected h) (hs_held h)) ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None)).
Definition GN_RI_step_room : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst q,
  RINV cx t m -> gn_op cx t m ->
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
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> gn_runc MT (gn_pre cx m) m1 mc A i k q ->
  mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)).
Definition GN_RI_step_cnl_meter : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst q,
  RINV cx t m -> gn_op cx t m ->
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
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> gn_runc MT (gn_pre cx m) m1 mc A i k q ->
  mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)).
Definition GN_RI_step_cshe_meter : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst q,
  RINV cx t m -> gn_op cx t m ->
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
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> gn_runc MT (gn_pre cx m) m1 mc A i k q ->
  mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  forall h' E' H' (Sy : astate), gn_cnl_ok h h' E' H' ->
     mo_le MT Sx Sy (cnl_cost MT (hs_expected h) (hs_held h)) ->
  mo_ok MT Sy (hl_n (hs_held h') * mo_free MT).
Definition GN_RI_end_ri : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst q,
  RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (lm_gn m = 0 \/ lm_gn m = 1) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  gn_runc MT (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat q ->
  mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  A = Z.of_nat (length (lm_O mc)) /\ RINV cx (t + 1) mc.
Definition GN_RI_end_ls : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst q,
  RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (lm_gn m = 0 \/ lm_gn m = 1) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  gn_runc MT (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat q ->
  mo_le MT S Sx cst -> gn_cst MT cx m m1 q cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  LS cx (t + 1) mc lyx Sx.

Lemma GN_RI_step_split : GN_RI_step_ri -> GN_RI_step_room -> GN_RI_step_cnl_meter -> GN_RI_step_cshe_meter ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step B MT LS RINV MMAX.
Proof.
  unfold GN_RI_step_ri, GN_RI_step_room, GN_RI_step_cnl_meter, GN_RI_step_cshe_meter,
    W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step.
  intros HR HRm HCm HSm cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20.
  specialize (HR cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20).
  specialize (HRm cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20).
  specialize (HCm cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20).
  specialize (HSm cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20).
  destruct HR as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C10).
  refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj HRm (conj HCm _))))))))).
  intros h' E' H' Sy Hc Hm. destruct (C10 h' E' H' Sy Hc Hm) as (D1 & D2 & D3).
  exact (conj D1 (conj D2 (conj D3 (HSm h' E' H' Sy Hc Hm)))).
Qed.
Lemma GN_RI_end_split : GN_RI_end_ri -> GN_RI_end_ls -> W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B MT LS RINV.
Proof.
  unfold GN_RI_end_ri, GN_RI_end_ls, W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end.
  intros HR HL cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16.
  destruct (HR cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16) as (R1 & R2).
  exact (conj R1 (conj R2 (HL cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16))).
Qed.
End g8.
End G8.

Section l8.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Context {MT : ameter_ops}.
(* ================================================================== GN_RI_end's LS conjunct *)
Lemma gx8_end_LS3 : G8.GN_RI_end_ls B MT (fr_LS3 B) fr_RINV.
Proof.
  unfold G8.GN_RI_end_ls.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16.
  exact (gx7_end_LS3 B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst P1 P2 P3 P5 P6 P7 P8 P9 P10 P11 P12 I
    P16).
Qed.
Lemma gx8_end_LS3c : G8.GN_RI_end_ls B MT (fr_LS3c B) fr_RINV.
Proof.
  unfold G8.GN_RI_end_ls.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16.
  exact (gx7_end_LS3c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst P1 P2 P3 P5 P6 P7 P8 P9 P10 P11 P12 I
    P16).
Qed.

(* LS := fr_LS3c /\ fr_OUT (ReplyLS3o.v) /\ fr_ENT (ReplyLS3e.v) *)
Definition tx8_LSx (OM : Z) : lfcx -> Z -> lmod -> alayout -> astate -> Prop :=
  fun cx t m ly S => fr_LS3c B cx t m ly S /\ fr_OUT OM cx t m ly S /\ fr_ENT B cx m ly S.
(* the composite: gx8_end_LS3c, ReplyLS3oGn.fr_OUT_gone_end and ReplyLS3e.fr_ENT_gone_end (its REQ5 from gxh_req5) *)
Lemma gx8_end_LSx : forall OM, OUT_MAX4 <= OM -> G8.GN_RI_end_ls B MT (tx8_LSx OM) fr_RINV.
Proof.
  intros OM HOM. unfold G8.GN_RI_end_ls, tx8_LSx.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q P1 P2 P3 P4 P5 P6 P7 (HLS & HOU & HEN)
    P9 P10 P11 P12 P13 P14 P15 P16.
  pose proof (proj1 HLS) as HLS3.
  pose proof (gxh_req5 cx t m hs qs c2 O2 cap2 out2 m1 mc A _ _ P1 P9 P10 P11 P12) as HR5.
  split; [exact (gx8_end_LS3c cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q P1 P2 P3 P4 P5 P6 P7 HLS
                   P9 P10 P11 P12 P13 P14 P15 P16)|].
  split.
  - eapply fr_OUT_gone_end; eassumption.
  - eapply fr_ENT_gone_end; eassumption.
Qed.

(* ================================================================== GN_RI_step's cnl_room *)
Lemma gx8_step_room : G8.GN_RI_step_room B MT (fr_LS3 B) fr_RINV CfParamsReply.fr_MMAX.
Proof.
  unfold G8.GN_RI_step_room.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20.
  exact (gx7_step_room B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst P1 P2 P3 P4 P5 P6 P7 P8 P9 P10
    P11 I P15 P16 P17 P18 P19 P20).
Qed.
Lemma gx8_step_room_c : G8.GN_RI_step_room B MT (fr_LS3c B) fr_RINV CfParamsReply.fr_MMAX.
Proof.
  unfold G8.GN_RI_step_room.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20.
  exact (gx7_step_room_c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst P1 P2 P3 P4 P5 P6 P7 P8 P9 P10
    P11 I P15 P16 P17 P18 P19 P20).
Qed.
Lemma gx8_step_room_x : forall OM, G8.GN_RI_step_room B MT (tx8_LSx OM) fr_RINV CfParamsReply.fr_MMAX.
Proof.
  intros OM. unfold G8.GN_RI_step_room, tx8_LSx.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 (HLS & _ & _) P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20.
  exact (gx8_step_room cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q P1 P2 P3 P4 P5 P6 (proj1 HLS)
    P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20).
Qed.
(* ================================================================== the whole rules from their RINV part *)
Lemma gx8_GN_RI_end_LS3 : G8.GN_RI_end_ri B MT (fr_LS3 B) fr_RINV ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B MT (fr_LS3 B) fr_RINV.
Proof. intros HR. apply G8.GN_RI_end_split; [exact HR | exact gx8_end_LS3]. Qed.
Lemma gx8_GN_RI_end_LS3c : G8.GN_RI_end_ri B MT (fr_LS3c B) fr_RINV ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B MT (fr_LS3c B) fr_RINV.
Proof. intros HR. apply G8.GN_RI_end_split; [exact HR | exact gx8_end_LS3c]. Qed.
Lemma gx8_GN_RI_end_LSx : forall OM, OUT_MAX4 <= OM ->
  G8.GN_RI_end_ri B MT (tx8_LSx OM) fr_RINV -> W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B MT (tx8_LSx OM) fr_RINV.
Proof. intros OM HOM HR. apply G8.GN_RI_end_split; [exact HR | exact (gx8_end_LSx OM HOM)]. Qed.
End l8.
