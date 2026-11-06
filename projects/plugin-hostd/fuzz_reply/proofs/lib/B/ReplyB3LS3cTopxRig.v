(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyLSBDrainPre.v, with its module names changed; 896 of its 1045 lines of code are new or changed and 537 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyB3LS3Peak.v, with its module names changed; 80 of its 164 lines of code are new or changed and 961 lines of the source are left out. *)
(* The image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3cTopxRig.v at
   1318828167d3 (sha256 c5c6daea7c2b; internal record), row G-BLS-drain:
   the v3 rig, top_x's LS_gone_rig at LS := lib/B/ReplyB3LS3.v
   fr_LS3 B CALL_ROOM_B and lib/B/ReplyB3LS3c.v fr_LS3c B CALL_ROOM_B, RINV := lib/B/ReplyRINVB.v fr_RINV,
   MMAX := fr_MMAX.  proves no function (kind: invariant lemma).
   PORTED, A's names and statements: fr_LS3_gone_rig_c1, fr_LS3_gone_rig_c4, fr_LS3_gone_rig_134, their fr_LS3c forms
   fr_LS3c_gone_rig_c1 / _c4 / _134 (A :399-473), and fr_LS3_gone_rig_c2p / fr_LS3c_gone_rig_c2p (A :606-660).
   KF-COUNT B step 3 (a Theorem Labs lane 09:35Z / 10:31Z; s5-r1d's KF-METER-PATTERN): no lemma here is at a meter any more.
   A's (R3) fr_LS3_gone_rig_c3 / fr_LS3c_gone_rig_c3, which were only `mo_ok ameter_triv ..` and had no user, are
   deleted (the pattern's step 3); the _134 lemmas keep their names without R3's mo_ok conjunct.
   REUSED, not copied: every helper A's file has (A :105-397, :475-605) is lib/B/ReplyLSBRig.v's under the name
   grg_ -> brig_, with A's statement word for word: brig_cost, brig_ok, brig_cost_nonneg, brig_geia_loop_perm,
   brig_combine_kw, brig_xks_le, brig_fold_fst, brig_fold_nonneg, brig_run_cons, brig_entry_no, brig_entry_tr,
   brig_run_rq, brig_zsum_le, brig_pair_pt, brig_pairs, brig_okp, brig_pc, brig_pc_nonneg, brig_pc_le, brig_zsum_pc,
   brig_entry_pos, brig_run_pos, brig_pos_entry.
   NOT PORTED: grg_probe_300 (A :662-673), a vm-checked probe over A's ReplyTrPeak.v pr_c / pr_e / pr_h, which lib/B
   does not have (lib/B/ReplyLSBTrPeak.v leaves A's probe out); no lemma reads it.
   A -> B SWAPS (as lib/B/ReplyLSBRig.v and ReplyB3LS3Arms.v made them): lib/A AB1v -> lib/B YB1v; Reusable YE01 +
   lib/A AE2k -> lib/B YE01 YE2k; lib/A ACfn -> lib/B YCfn (Required only); lib/A W_* -> lib/B W_*, then ReplyGuardB;
   lib/A ReplyLS / ReplyLSArms / ReplyRINV / ReplyTrPeak / ReplyLSDrainPre / ReplyLSRrPre / ReplyLSRemove3 ->
   lib/B/ReplyLSB.v, ReplyLSBArms.v (gn_pairs, gn_pair_ok, gn_id: the same texts as A's ReplyLS3cTopxDefs.v),
   ReplyRINVB.v, ReplyLSBTrPeak.v, ReplyLSBDrainPre.v; ReplyLS3 / ReplyLS3c -> lib/B/ReplyB3LS3.v / ReplyB3LS3c.v;
   ACfn_cf.CALL_ROOM -> the Section variable CALL_ROOM_B (lib/B/ReplyLSB.v's ruling): the c2p lemmas read the room
   through ReplyB3LS3.v fr_LS3_room_x and take its premise `YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B` first; MMAX: A's
   WR_MMAX -> fr_MMAX (lib/A/CfParamsReply.v, as lib/B/ReplyLSBRig.v and ReplyB3LS3Arms.v; the same value
   1,072,693,248).
   A's header follows: for what each conjunct is and why R2 / R5 in sum form are false, read it there (A :3-58);
   its arithmetic is unchanged on B. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBArms ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBTrPeak ReplyLSBDrainPre ReplyLSBRig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3Base ReplyB3LS3 ReplyB3LSCntL ReplyB3LS3c.
Import ListNotations.
(* the gone arm notions lib/B/ReplyLSBArms.v copied are _gone_base.v's (s5-r1d's cutover, lib/B/ReplyLSBI.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_gone_base.
Local Notation gn_id := W_LLVMFuzzerTestOneInput_gone_base.gn_id.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the instance's request bound (MMAX := fr_MMAX, A's WR_MMAX's value) *)
Local Notation MMAX := fr_MMAX.
Local Notation zsum l := (fold_right Z.add 0 l).

Section grig.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.

(* ================================================================== the rules *)
(* (R1) GN_LS_rig's first conjunct, at the PROPOSED text: the published premises and the three gn_op / aentry_ok
   facts the gone arm holds at gone_p3.v:995 (HOP from GRG :659, HREL from GRG's amodel_at) *)
Lemma fr_LS3_gone_rig_c1 : forall cx t m ly S hs,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  tr_max (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) < MMAX.
Proof.
  intros cx t m ly S hs _ HRI HP HO Ht HUs.
  destruct (brig_pairs cx t m hs HRI HP Ht HUs) as (HF & HC & Hn & _).
  rewrite HO. cbn [length Z.of_nat].
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr. cbv zeta.
  assert (EM : fr_MMAX = 1072693248) by reflexivity.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  pose proof (zsum_map_nonneg brig_cost (combine (lm_es m) hs) brig_cost_nonneg) as H0.
  apply (Z.le_lt_trans _ (fr_MMAX - 1)); [|lia].
  apply dpre_tr_max; [lia|].
  apply (brig_run_rq _ _ _ _ _ 0 _ _ _ (fr_MMAX - 1) (c_n cx) HF HC); lia.
Qed.

(* (R4) GN_LS_rig's fourth conjunct, with the named extra fact Hcap (neither fr_LS3 nor fr_RINV bounds lm_cap) *)
Lemma fr_LS3_gone_rig_c4 : forall cx t m ly S hs,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  lm_cap m < MMAX.
Proof. intros cx t m ly S hs _ _ _ Hcap. assert (EM : fr_MMAX = 1072693248) by reflexivity. lia. Qed.

(* R1 and R4 together, at R1's PROPOSED text and with Hcap (KF-COUNT B step 3: R3's mo_ok conjunct dropped) *)
Lemma fr_LS3_gone_rig_134 : forall cx t m ly S hs,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs in
  tr_max tr < MMAX /\ lm_cap m < MMAX.
Proof.
  intros cx t m ly S hs HLS HRI HP HO Ht HUs Hcap tr.
  split; [exact (fr_LS3_gone_rig_c1 cx t m ly S hs HLS HRI HP HO Ht HUs)|].
  exact (fr_LS3_gone_rig_c4 cx t m ly S hs HLS HRI HP Hcap).
Qed.

(* the same at fr_LS3c (its first projection is fr_LS3) *)
Lemma fr_LS3c_gone_rig_c1 : forall cx t m ly S hs,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  tr_max (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) < MMAX.
Proof. intros cx t m ly S hs H. exact (fr_LS3_gone_rig_c1 cx t m ly S hs (proj1 H)). Qed.
Lemma fr_LS3c_gone_rig_c4 : forall cx t m ly S hs,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  lm_cap m < MMAX.
Proof. intros cx t m ly S hs H. exact (fr_LS3_gone_rig_c4 cx t m ly S hs (proj1 H)). Qed.
Lemma fr_LS3c_gone_rig_134 : forall cx t m ly S hs,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs in
  tr_max tr < MMAX /\ lm_cap m < MMAX.
Proof. intros cx t m ly S hs H. exact (fr_LS3_gone_rig_134 cx t m ly S hs (proj1 H)). Qed.
End grig.

(* ================================================================== the peak form of R2 (cause C3) *)
Section gpeak.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.

(* (R2), peak form: rig_spec's room at cause C3's measure (lib/B/ReplyLSBArms.v tr_peak), at R1's PROPOSED premises and
   the model blocks' sizes not negative (fr_LS_rm_rr_pre_c3p's premise; amodel_at at GRG gives it as the remove arm's
   rr_blks_pos does), with 636848 bytes to spare; the room read through lib/B/ReplyB3LS3.v fr_LS3_room_x, so the
   premise `YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B` comes first *)
Lemma fr_LS3_gone_rig_c2p : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S hs,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S +
    tr_peak (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) + 636848
    <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S hs HLS HRI HP HO Ht HUs Hpos.
  pose proof (fr_LS3_gone_rig_c1 B CALL_ROOM_B cx t m ly S hs HLS HRI HP HO Ht HUs) as HM.
  pose proof (fr_LS3_room_x B CALL_ROOM_B HCR cx t m ly S HLS) as Hroom.
  destruct (brig_pairs cx t m hs HRI HP Ht HUs) as (HF & HC & Hn & H4).
  pose proof HP as (HLhs & _ & _).
  assert (HFp : Forall brig_okp (combine (lm_es m) hs)).
  { apply Forall_forall. intros p Hp. split; [exact (proj1 (Forall_forall _ _) HF p Hp)|].
    apply (brig_pos_entry m (fst p)); [|exact Hpos].
    destruct p as [e q]. cbn [fst]. exact (in_combine_l _ _ _ _ Hp). }
  assert (Hcap : 0 <= lm_cap m).
  { destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
    apply (Hpos (lm_out m, lm_cap m)). unfold model_blks. right. apply in_or_app. right. apply in_or_app. right.
    unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity. }
  pose proof (brig_zsum_pc (combine (lm_es m) hs)) as HPC.
  rewrite length_combine, HLhs, Nat.min_id in HPC.
  pose proof (zsum_map_nonneg brig_cost (combine (lm_es m) hs) brig_cost_nonneg) as H0.
  revert HM. rewrite HO. cbn [length Z.of_nat]. intros HM.
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr in *. cbv zeta in *.
  match goal with |- context [tr_peak (fst (fst (fst (relay_instance_gone_b_c.gone_run
                                ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9))))] =>
    pose proof (brig_run_pos a6 a1 a2 a5 a7 a3 a4 a8 a9 HFp Hcap) as POS;
    pose proof (tr_peak_le_pos (fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))))
      as PK;
    set (T := fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))) in *
  end.
  assert (HL : Z.of_nat (length (lm_es m)) <= 4) by lia.
  set (Zc := zsum (map brig_cost (combine (lm_es m) hs))) in *.
  set (Zp := zsum (map brig_pc (combine (lm_es m) hs))) in *.
  clearbody T Zc Zp.
  clear - Hroom HM POS PK HPC HL HC Hn H0 Hcap.
  assert (EM : fr_MMAX = 1072693248) by reflexivity.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  lia.
Qed.
Lemma fr_LS3c_gone_rig_c2p : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S hs,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S +
    tr_peak (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) + 636848
    <= LIVE_MAX.
Proof. intros HCR cx t m ly S hs H. exact (fr_LS3_gone_rig_c2p HCR cx t m ly S hs (proj1 H)). Qed.
End gpeak.
