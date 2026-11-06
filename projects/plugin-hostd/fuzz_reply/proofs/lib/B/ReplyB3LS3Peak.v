(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyLSBDrainPre.v, with its module names changed; 896 of its 1045 lines of code are new or changed and 537 lines of the source are left out. *)
(* The image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3Peak.v at
   1318828167d3 (sha256 1962b69c8fbd; internal record), row G-BLS-drain:
   the same lemmas under the same names over lib/B's records, at
   LS := lib/B/ReplyB3LS3.v fr_LS3 B CALL_ROOM_B, RINV := lib/B/ReplyRINVB.v fr_RINV; no lemma reads a meter except
   the top_x-text corollaries at MT := ameter_triv (KF-COUNT B step 3, below).
   PORTED, in A's order: the texts TX_LS_drain_pre, TX_LS_rm_rr_pre and TX_GN_LS_rig (A :128-184, Variable MMAX as on
   A); pk_fr_MMAX / pk_WR_MMAX (A :188-191); pk_TXM and pk_pw8 .. pk_dr_tr_max8 (A :192-340); Section req (A :341-614:
   pk_rr_tr_max, pk_ok8 .. pk_gp_le_pend); pk_room_pend (A :619-637); the drain half pk_drain_c5_slack / pk_drain_c5 /
   pk_drain_pre (A :639-725); the relay_remove half pk_rr_c3_slack, pk_rr_c3, pk_rr_c6, pk_rm_rr_pre (A :727-851); the
   gone half pk_rig_r5, pk_gone_rig (A :852-951).  THE PLUGS (A :953-992 states them at txp_LSx B OM / tx8_LSx B OM,
   which lib/B does not have), each stated at B top_x's own text (LS_drain_pre :461, LS_rm_rr_pre :678,
   GN_LS_rig_x :873; the B cutover's re-point, a Theorem Labs lane 10:58Z): at any LS that gives what A's plug destructures,
   pk_tx_drain_pre_of (fr_LS3),
   pk_tx_rm_rr_pre_of and pk_tx_gone_rig_of (fr_LS3c /\ fr_OUT OUT_MAX4 /\ fr_ENT), and at B's instance
   lib/B/ReplyLS3B_inst.v LSI B OUT_MAX4 fr_CAP (through lsi_parts, at CALL_ROOM_B := YCfn_cf.CALL_ROOM_B):
   pk_lsi_rm_rr_pre, pk_lsi_gone_rig (LS_drain_pre's LSI plug is lib/B/ReplyB3LSIDrain.v lsi_LS_drain_pre).
   A's ReplyLS3eCap.v (ent_capout_ok0, ls3e_cap_lt_MMAX) is lib/B/ReplyB3LS3eCap.v and A's v3 rig
   (fr_LS3c_gone_rig_c1 / _c2p) is lib/B/ReplyB3LS3cTopxRig.v; their MMAX is fr_MMAX, the same constant as the texts'
   CfParamsReply.fr_MMAX, so A's `rewrite pk_fr_MMAX` steps (to A's WR_MMAX) are not needed here.
   KF-COUNT B step 3 (a Theorem Labs lane 09:35Z / 10:31Z; s5-r1d's KF-METER-PATTERN): the meter conjunct is dropped from
   pk_drain_pre (its mo_ok of dr_cost), pk_rm_rr_pre (its mo_ok of rm_rr_cost) and pk_gone_rig (its mo_ok of tr_cost),
   names kept.  Each plug at top_x's text has a version without the text's meter conjunct (meter-free, so generic in
   any MT) and keeps its name at ameter_triv as a corollary that supplies the conjunct by I: pk_tx_drain_pre_of_m ->
   pk_tx_drain_pre_of, pk_tx_rm_rr_pre_of_m -> pk_tx_rm_rr_pre_of, pk_tx_gone_rig_of_m -> pk_tx_gone_rig_of,
   pk_lsi_rm_rr_pre_m -> pk_lsi_rm_rr_pre, pk_lsi_gone_rig_m -> pk_lsi_gone_rig.
   A -> B SWAPS (as lib/B/ReplyB3LS3Arms.v made them): the imports of lib/B/ReplyB3LS3Arms.v; A's ReplyTrPeak.v is
   lib/B/ReplyLSBTrPeak.v (tp_dr, tp_pos_entry, tp_pos_out, tr_peak_le_pos, tr_max_nonneg', same names); A's
   ReplyLS3 / ReplyLS3Arms / ReplyLSDrain3 are lib/B/ReplyB3LS3.v / ReplyB3LS3Arms.v (fr_LS3_room_x,
   fr_LS3_drain_pre_c1236, fr_LS3_drain_pre_c4, dpre_pair); room lemmas take `YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B`
   first, as lib/B/ReplyB3LS3.v fr_LS3_room_x does (Z.le_refl at the instance).  fr_MMAX stays A's
   CfParamsReply.fr_MMAX, which lib/B/ReplyB3LS3Arms.v and ReplyBTop.v Import (the same value, 2 ^ 30 - 2 ^ 20).
   A's ReplyLS3cTopxRig.v helpers grg_* are lib/B/ReplyLSBRig.v's brig_* (each statement A's with grg_ -> brig_:
   brig_ok, brig_cost, brig_cost_nonneg, brig_entry_no, brig_run_cons, brig_xks_le, brig_fold_fst, brig_pairs,
   brig_pc); A's ReplyLSRrPre.v rrp_tr_max_app is lib/B/ReplyLSBTrPeak.v tr_max_app'; A's ReplyLS3cTopxDefs.v
   gn_pairs / gn_pair_ok are lib/B/ReplyLSBArms.v's copies and its gn_e0 / gn_hj0 are
   lib/B/W_LLVMFuzzerTestOneInput_gone_base.v's (the same texts); A's ReplyLS.v / ReplyLS3.v / ReplyLS3Arms.v facts
   (zsum_map_nonneg, nopen_le4, npend_nonneg, slot_*_nonneg, ECRED_nonneg, ls3_ps_sp) are lib/B/ReplyB3Base.v's,
   ReplyB3LS3.v's and ReplyB3LS3Arms.v's; A's ReplyLS3cTopxGoneF.v gn_op is lib/B/W_LLVMFuzzerTestOneInput_gone_base.v's
   (cited qualified, the same text); A's ReplyLS3cTopxPost.v tx_rm_rr_cost is lib/B/ReplyB3LS3cTopxPost.v's; A's
   ReplyLS3o.v fr_OUT / OUT_MAX4 are lib/B/ReplyLSBo.v's and its pend_bytes_in lib/B/ReplyB3LS3o.v's; A's ReplyLS3e.v
   fr_ENT is lib/B/ReplyB3LS3e.v's (cited qualified). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c
  RelayCap SlotReads SlotInv SlotDrain3Aux SlotPass2Aux relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBRig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBo.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3Base ReplyB3LS3 ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LSCntL ReplyB3LS3c ReplyB3LS3cTopxRig ReplyB3LS3eCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LS3e ReplyB3LS3o ReplyB3LS3cTopxPost ReplyLS3B_inst.
Import ListNotations.
(* the remove and gone arm notions lib/B/ReplyLSBArms.v copied are lib/B's arm files' (s5-r1d's cutover,
   lib/B/ReplyLSBI.v), pinned here *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
Local Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Notation rm_rr_tr := W_LLVMFuzzerTestOneInput_remove.rm_rr_tr.
Local Notation gn_id := W_LLVMFuzzerTestOneInput_gone_base.gn_id.
Local Notation gn_pair_ok := W_LLVMFuzzerTestOneInput_gone_base.gn_pair_ok.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== the texts, in top_x's family form *)
Section tx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable MT : ameter_ops.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* top_x :401 LS_drain_pre; conjunct 5 in peak form; added: t, |re_U| and the blocks' sizes (A :128-147) *)
Definition TX_LS_drain_pre : Prop :=
  forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).

(* top_x :491 LS_rm_rr_pre (its W_LLVMFuzzerTestOneInput_remove.rm_* are lib/B/ReplyLSBArms.v's copies and
   `(rm_rr_cost MT)` is lib/B/ReplyB3LS3cTopxPost.v tx_rm_rr_cost MT); conjuncts 3 and 6 in peak form; added: t,
   |re_U|, the model blocks' sizes, HSRC, HCAP0 (A :149-166) *)
Definition TX_LS_rm_rr_pre : Prop :=
  forall cx t m ly S si h j0,
  LSx cx t m ly S -> RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  ent_capout_ok0 (c_W cx) (c_mem cx) ->
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (rm_rr_tr m h) <= LIVE_MAX /\
  mo_ok MT S ((ReplyB3LS3cTopxPost.tx_rm_rr_cost MT) m h) /\ lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (rm_rr_tr m h)) <= LIVE_MAX.

(* GN_LS_rig (A's ReplyLS3cTopxDefs.v:177, W8's G8 text 1fcc03569d3); R2 and R5 in peak form; added: gn_op, |re_U|
   of every entry, the model blocks' sizes, every slot's HSRC, HCAP0 (A :168-184) *)
Variable MMAX : Z.
Definition TX_GN_LS_rig : Prop := forall cx t m ly S hs,
  LSx cx t m ly S -> RINV cx t m -> gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  ent_capout_ok0 (c_W cx) (c_mem cx) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (gn_id cx m) (lm_es m) hs in
  tr_max tr < MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\ mo_ok MT S (tr_cost MT tr) /\
  lm_cap m < MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
End tx.

(* ================================================================== the instance's MMAX (A :188-191) *)
Lemma pk_fr_MMAX : CfParamsReply.fr_MMAX = W_LLVMFuzzerTestOneInput_write.WR_MMAX.
Proof. reflexivity. Qed.
Lemma pk_WR_MMAX : W_LLVMFuzzerTestOneInput_write.WR_MMAX = 1072693248.
Proof. reflexivity. Qed.
(* every request bound below: 8 (2^26 + 6000) *)
Definition pk_TXM : Z := 536918912.

(* ================================================================== the expected array's capacity *)
(* 0 or 8 * 2^k: SlotInv.ecap_ok without its upper end, kept by push_cap *)
Definition pk_pw8 (c : Z) : Prop := c = 0 \/ exists k, 0 <= k /\ c = 8 * 2 ^ k.
Lemma pk_pw8_ecap : forall c, SlotInv.ecap_ok c -> pk_pw8 c.
Proof. intros c [H|(k & Hk & H)]; [left; exact H | right; exists k; split; [lia | exact H]]. Qed.
Lemma pk_pw8_push : forall n c, pk_pw8 c -> pk_pw8 (drain_b_c.push_cap n c).
Proof.
  intros n c Hc. unfold drain_b_c.push_cap.
  destruct (Z.eqb_spec n c); [|exact Hc].
  destruct (Z.eqb_spec c 0) as [E|E].
  - right. exists 0. split; [lia | reflexivity].
  - destruct Hc as [Hc|(k & Hk & Hc)]; [contradiction|].
    right. exists (k + 1). split; [lia|]. rewrite Hc, Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.
(* below 2^25 such a capacity is at most 2^24 *)
Lemma pk_pw8_le : forall c E, pk_pw8 c -> c < E -> E <= 2 ^ 25 -> c <= 2 ^ 24.
Proof.
  intros c E [->|(k & Hk & ->)] H1 H2; [lia|].
  assert (E21 : 2 ^ 21 = 2097152) by reflexivity. assert (E22 : 2 ^ 22 = 4194304) by reflexivity.
  assert (E24 : 2 ^ 24 = 16777216) by reflexivity. assert (E25 : 2 ^ 25 = 33554432) by reflexivity.
  destruct (Z_le_gt_dec k 21) as [Hle|Hgt].
  - pose proof (Z.pow_le_mono_r 2 k 21 ltac:(lia) Hle). lia.
  - pose proof (Z.pow_le_mono_r 2 22 k ltac:(lia) ltac:(lia)). lia.
Qed.

(* reference_feed's pushes (A's ReplyLSDrainPre.v dpre_pushes_run, lib/B/ReplyLSBDrainPre.v's; the array's growth at
   most 2^29) *)
Lemma pk_pushes_run8 : forall ls n cap j v rs M En,
  Forall (fun l => Z.of_nat (length l) <= 6000) ls -> n + Z.of_nat (length ls) <= En -> En <= 2 ^ 25 ->
  pk_pw8 cap -> 2 ^ 29 <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) /\
  pk_pw8 (snd (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  assert (E24 : 2 ^ 24 = 16777216) by reflexivity. assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  induction ls as [|l r IH]; intros n cap j v rs M En HF Hn HE Hc H29 H6; cbn [drain_b_c.pushes_run].
  - cbn [fst snd]. split; [constructor | exact Hc].
  - apply Forall_cons_iff in HF as [Hl HF]. cbn [length] in Hn.
    match goal with |- context [drain_b_c.pushes_run (n + 1) ?c2 r ?j2 ?v2 ?rs2] =>
      destruct (IH (n + 1) c2 j2 v2 rs2 M En HF ltac:(lia) HE (pk_pw8_push n cap Hc) H29 H6) as [I1 I2] end.
    cbn [fst snd]. split; [|exact I2].
    apply Forall_app. split; [|exact I1].
    unfold ListTr.list_push_tra. apply Forall_app. split.
    + destruct (Z.eqb_spec n cap) as [E|E]; [|constructor].
      pose proof (pk_pw8_le cap En Hc ltac:(lia) HE) as Hle.
      destruct (cap =? 0); (apply Forall_cons; [cbn [dpre_rq]; lia | constructor]).
    + apply Forall_cons; [cbn [dpre_rq]; lia | constructor].
Qed.

(* drain's rounds (lib/B/ReplyLSBDrainPre.v dpre_drain_run with the capacity's form kept) *)
Definition pk_inv8 (Hk A En : Z) (s : drain_b_c.dstate) : Prop :=
  dpre_inv Hk A En s /\ pk_pw8 (drain_b_c.ds_ecap s).
Lemma pk_drain_run8 : forall f live mx s j a M Hk A En, pk_inv8 Hk A En s ->
  20192 <= M -> 2 * A <= M -> 8 * (Hk + A) <= M -> En <= 2 ^ 25 -> 2 ^ 29 <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (drain_b_c.drain_run f live mx s j a)).
Proof.
  induction f as [|f IH]; intros live mx s j a M Hk A En (HI & Hpw) Hg H2 H8 HE H29 H6; [constructor|].
  pose proof HI as (Iu & Io & Ir & Ia & Ih & Ie).
  cbn [drain_b_c.drain_run].
  pose proof (dpre_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) M
                ltac:(lia) Hg) as G1.
  destruct (drain_b_c.ds_eintr s).
  - (* EINTR: the growth only, then the same state *)
    cbn [fst]. apply Forall_app. split; [exact G1|].
    apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
    unfold pk_inv8. split; [|cbn [drain_b_c.ds_ecap]; exact Hpw].
    unfold dpre_inv, dpre_rem in HI |- *.
    cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
         drain_b_c.ds_pend].
    exact HI.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP; [exact G1|].
    assert (Hrem : dpre_rem s = Z.of_nat (length r0) + Z.of_nat (length (concat rs)) - drain_b_c.ds_off s).
    { unfold dpre_rem. rewrite EP. cbn [concat]. rewrite length_app. lia. }
    match goal with |- context [Z.leb ?x 0] => destruct (Z.leb_spec x 0) as [Hn0|Hn0] end; [exact G1|].
    match type of Hn0 with 0 < ?x =>
      assert (Hn1 : x <= Z.of_nat (length r0) - drain_b_c.ds_off s) by lia;
      set (n := x) in * end.
    assert (Hd : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0))) = n)
      by (rewrite length_firstn, length_skipn; lia).
    set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
    destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
    destruct (dpre_chunk _ _ _ _ _ _ EC) as (C1 & C2 & C3).
    cbv beta iota.
    destruct (dpre_ref_lines d (drain_b_c.ds_ref s) Ir) as (R1 & R2 & R3).
    match goal with |- context [drain_b_c.pushes_run ?n0 ?c ?ls ?jj ?v ?rs0] =>
      destruct (pk_pushes_run8 ls n0 c jj v rs0 M En R1 ltac:(lia) HE Hpw H29 H6) as [P1 P2] end.
    match goal with |- context [drain_b_c.lines_run ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?l8 ?l9 ?l10 ?l11] =>
      pose proof (dpre_lines_run l7 l1 l2 l3 l4 l5 l6 l8 l9 l10 l11 M Hk A C1 ltac:(lia) ltac:(lia) H2 H8 H6)
        as [L1 L2];
      revert L1 L2;
      destruct (drain_b_c.lines_run l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11) as [[tl [[oc' H'] ka']] [[o' ha'] ks']];
      intros L1 L2 end.
    cbn [fst snd] in L1, L2 |- *.
    apply Forall_app. split; [exact G1|].
    apply Forall_app. split; [exact P1|].
    destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [Ew|Ew].
    + (* the head text is read to its end: list_drop frees it *)
      apply Forall_app. split; [unfold ListTr.list_drop_tra; apply Forall_cons; [exact I | constructor]|].
      apply Forall_app. split; [exact L1|].
      apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
      unfold pk_inv8. split; [|cbn [drain_b_c.ds_ecap]; exact P2].
      unfold dpre_inv, dpre_rem.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
           drain_b_c.ds_pend].
      split; [exact C3|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; lia.
    + apply Forall_app. split; [constructor|].
      apply Forall_app. split; [exact L1|].
      apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
      unfold pk_inv8. split; [|cbn [drain_b_c.ds_ecap]; exact P2].
      unfold dpre_inv, dpre_rem.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
           drain_b_c.ds_pend concat].
      rewrite length_app.
      split; [exact C3|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; lia.
Qed.

(* one drain from g_nout = 0 (lib/B/ReplyLSBDrainPre.v dpre_dr_tr_max at any M of the four sizes) *)
Lemma pk_dr_tr_max8 : forall c mx cap e h M,
  Z.of_nat (length (re_U e)) <= APARTIAL ->
  hs_overlong h = 1 \/ bzs (re_U e) = bzs (hs_W h) ->
  0 <= hs_off h -> hl_recs (hs_expected h) = [] -> SlotInv.ecap_ok (hl_cap (hs_expected h)) ->
  Z.of_nat (length (pending_stream h)) <= 65535 * 511 ->
  20192 <= M -> 2 * (6000 + Z.of_nat (length (pending_stream h))) <= M ->
  8 * (Z.of_nat (length (re_keys e)) + (6000 + Z.of_nat (length (pending_stream h)))) <= M -> 2 ^ 29 <= M ->
  tr_max (dr_tr c mx 0 cap e h) <= M.
Proof.
  intros c mx cap e h M HU HJ Ho He Hec Hp Hg H2 H8 H29.
  assert (E25 : 2 ^ 25 = 33554432) by reflexivity. assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  unfold APARTIAL in HU.
  unfold dr_tr, drain_b_c.drain_tr, drain_b_c.drain_go.
  apply dpre_tr_max; [lia|].
  apply (pk_drain_run8 _ _ _ _ _ _ M (Z.of_nat (length (re_keys e)))
           (6000 + Z.of_nat (length (pending_stream h))) (Z.of_nat (length (pending_stream h))));
    [|lia ..].
  unfold pk_inv8. split; [|cbn [drain_b_c.drain_init drain_b_c.ds_ecap]; exact (pk_pw8_ecap _ Hec)].
  pose proof (dpre_rem_init 0 cap e h Ho) as Hr.
  unfold dpre_inv.
  cbn [drain_b_c.drain_init drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H
       drain_b_c.ds_en] in Hr |- *.
  assert (Hu : length (bzs (re_U e)) = length (re_U e)) by (unfold bzs; apply length_map).
  split; [lia|]. split; [exact Ho|]. split.
  { unfold dpre_jref, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
    destruct HJ as [E|E]; [left; rewrite E; reflexivity | right; rewrite <- E; lia]. }
  split; [lia|]. split.
  { unfold drain_b_c.keys_texts. rewrite length_map. lia. }
  unfold hl_n. rewrite He. cbn [length]. lia.
Qed.

Section req.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* relay_remove's requests (A's ReplyLSRrPre.v fr_LS_rm_rr_pre_c2's proof, lib/B/ReplyLSBRrPre.v brr_rm_rr_pre_c2, at
   pk_TXM; it reads RINV only) *)
Lemma pk_rr_tr_max : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  tr_max (rm_rr_tr m h) <= pk_TXM.
Proof.
  intros cx t m si h j0 HRI Hat Ht HU.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & Hc & Hn).
  pose proof Hat as (_ & HO & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff).
  cbn [fst snd] in Hre, Hexp, Hec, Hpe, Hoff.
  destruct HE as (_ & _ & _ & _ & Hsk).
  unfold fr_pair_cost in Hc. cbn [fst] in Hc.
  pose proof (fr_keys_total_nonneg (re_keys (rm_ent m j0))) as HKT0.
  pose proof (dpre_keys_le (re_keys (rm_ent m j0))) as Hkl.
  assert (HX0 : 0 <= (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0))
    by (destruct (re_skip (rm_ent m j0) =? 0); lia).
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  unfold rm_rr_tr, rr_tr. cbv beta zeta.
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  destruct (hs_fd h <? 0); cbv iota; [unfold tr_max, pk_TXM; cbn [fold_right]; lia|].
  rewrite Hfind. cbv beta iota zeta.
  destruct (re_eof (rm_ent m j0) =? 0) eqn:Eo; cbv iota.
  - (* open: drain's own trace, then the gesture ends of the keys it leaves, then two frees *)
    apply Z.eqb_eq in Eo.
    assert (HA : tr_max (dr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) (rm_ent m j0) h) <= pk_TXM).
    { destruct (Hre Eo) as (S1 & W1). unfold pk_TXM. apply pk_dr_tr_max8.
      - exact HU.
      - destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia.
      - exact Hoff.
      - exact Hexp.
      - exact Hec.
      - unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia.
      - lia.
      - lia.
      - lia.
      - lia. }
    rewrite tr_max_app'.
    match goal with |- Z.max _ (tr_max ?KF) <= _ => assert (HB : tr_max KF <= pk_TXM) end.
    { unfold pk_TXM. apply dpre_tr_max; [lia|]. apply Forall_app. split.
      - apply rrp_ker_lens. unfold dr_fin.
        pose proof (rm3_no_fin (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) (rm_ent m j0) h Hoff) as NF.
        pose proof (rrp_fin_kw (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) (rm_ent m j0) h) as KW.
        rewrite (rm3_skip_if (re_skip (rm_ent m j0)) (Z.of_nat (length (re_U (rm_ent m j0)))) Hsk) in NF.
        lia.
      - apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil. }
    lia.
  - (* at eof: no drain; the gesture ends of the entry's own keys from g_nout = 0, then two frees *)
    rewrite app_nil_l. unfold pk_TXM.
    apply dpre_tr_max; [lia|]. apply Forall_app. split.
    + apply rrp_ker_lens. cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_H].
      rewrite <- rm3_kt_kw. lia.
    + apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
Qed.

(* ================================================================== relay_instance_gone's requests *)
(* lib/B/ReplyLSBRig.v brig_ok (A's ReplyLS3cTopxRig.v grg_ok) with the expected array's capacity of an open pair *)
Definition pk_ok8 (p : rentry * (hsrc * nat)) : Prop :=
  brig_ok p /\ (re_eof (fst p) = 0 -> SlotInv.ecap_ok (hl_cap (hs_expected (fst (snd p))))).

(* brig_entry_tr (A's grg_entry_tr) at pk_inv8 *)
Lemma pk_entry_tr8 : forall lv mx no cap (e : rentry) (hj : hsrc * nat) j (a0 : drain_b_c.dadr) M K,
  pk_ok8 (e, hj) -> brig_cost (e, hj) <= K ->
  2 * (no + 2 * brig_cost (e, hj) + 6000) <= M -> 8 * (K + 6000) <= M -> 2 ^ 29 <= M -> 20192 <= M ->
  Forall (dpre_rq M) (if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e (fst hj) j a0 else []).
Proof.
  intros lv mx no cap e hj j a0 M K ((Hsk & Hop) & Hec8) HK HM H8 H29 Hg.
  unfold brig_cost in HK, HM. cbn [fst snd] in Hsk, Hop, Hec8, HK, HM.
  assert (E25 : 2 ^ 25 = 33554432) by reflexivity. assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  pose proof (fr_keys_total_nonneg (re_keys e)) as HKT.
  pose proof (dpre_keys_le (re_keys e)) as Hkl.
  revert HK HM. destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; intros HK HM; cbv iota in HK, HM |- *;
    [|constructor].
  destruct (Hop Eo) as (HU & HJ & Ho & He & Hp & _).
  pose proof (Hec8 Eo) as Hec.
  assert (Hu : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
    by (destruct (re_skip e =? 0); lia).
  unfold drain_b_c.drain_tr, drain_b_c.drain_go.
  apply (pk_drain_run8 _ _ _ _ _ _ M (Z.of_nat (length (re_keys e)) - no)
           (no + 6000 + Z.of_nat (length (pending_stream (fst hj)))) (Z.of_nat (length (pending_stream (fst hj)))));
    [| lia ..].
  unfold pk_inv8. split; [|cbn [drain_b_c.drain_init drain_b_c.ds_ecap]; exact (pk_pw8_ecap _ Hec)].
  pose proof (dpre_rem_init no cap e (fst hj) Ho) as Hr.
  unfold dpre_inv.
  cbn [drain_b_c.drain_init drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H
       drain_b_c.ds_en] in Hr |- *.
  assert (Hu' : length (bzs (re_U e)) = length (re_U e)) by (unfold bzs; apply length_map).
  unfold APARTIAL in HU.
  split; [lia|]. split; [exact Ho|]. split.
  { unfold dpre_jref, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
    destruct HJ as [E|E]; [left; rewrite E; reflexivity | right; rewrite <- E; lia]. }
  split; [lia|]. split.
  { unfold drain_b_c.keys_texts. rewrite length_map. lia. }
  unfold hl_n. rewrite He. cbn [length]. lia.
Qed.

(* brig_run_rq (A's grg_run_rq) at pk_ok8 *)
Lemma pk_run_rq8 : forall ps lv mx pre nm no cap j o M K,
  Forall pk_ok8 ps -> zsum (map brig_cost ps) <= K ->
  2 * (no + 2 * zsum (map brig_cost ps) + 6000) <= M -> 8 * (K + 6000) <= M -> 2 ^ 29 <= M -> 20192 <= M ->
  Forall (dpre_rq M) (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))).
Proof.
  induction ps as [|[e hj] r IH]; intros lv mx pre nm no cap j o M K HF HK HM H8 H29 Hg.
  { cbn [relay_instance_gone_b_c.gone_run fst]. constructor. }
  apply Forall_cons_iff in HF as [Hok HF].
  cbn [map fold_right] in HK, HM.
  pose proof (brig_cost_nonneg (e, hj)) as Hc0.
  pose proof (zsum_map_nonneg brig_cost r brig_cost_nonneg) as Hr0.
  pose proof (brig_entry_no lv mx no cap e hj (proj1 Hok)) as HN.
  pose proof (brig_run_cons lv mx no cap pre e hj r nm j o) as EC. cbv zeta in EC. rewrite EC. clear EC.
  apply Forall_app. split.
  { apply (pk_entry_tr8 _ _ _ _ _ _ _ _ M K Hok); lia. }
  match goal with |- Forall _ (fst (gestures_end_b_c.keys_end_run ?lv' ?mx' (drain_b_c.ds_no ?S0) ?c1 ?X ?j1 ?o1)
                               ++ _) =>
    assert (HXF : Forall (fun x => 0 <= fst x) X)
      by (apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (x & <- & _); cbn [fst]; lia);
    assert (HX : fold_right (fun x acc => fst x + 5 + acc) 0 X <= rm3_kw (drain_b_c.ds_H S0))
      by apply brig_xks_le;
    pose proof (brig_fold_fst _ X) as EF
  end.
  apply Forall_app. split.
  { apply rrp_ker; [exact HXF | lia]. }
  apply (IH lv mx pre nm _ _ _ _ M K HF); lia.
Qed.

(* the open pairs' expected arrays are fr_relay's rows' (brig_pair_pt's argument, A's grg_pair_pt) *)
Lemma pk_pair_ecap : forall cx t m e p q,
  fr_RINV cx t m -> fr_pair_ok m t e q -> gn_pair_ok m e p -> SlotInv.ecap_ok (hl_cap (hs_expected (fst p))).
Proof.
  intros cx t m e p q HRI Hq Hp.
  destruct Hq as (Hq4 & Hqn & Hqf & _ & _ & _ & _ & Hec & _).
  destruct Hp as (Hp4 & Hpn & Hpf & _).
  assert (Es : fst p = fst q).
  { destruct (Nat.eq_dec (snd p) (snd q)) as [E|E].
    - rewrite E, Hqn in Hpn. injection Hpn as Hpq. exact (eq_sym Hpq).
    - exfalso. apply (RI_fds_holds cx t m (snd p) (snd q) (fst p) (fst q) HRI Hp4 Hq4 E Hpn Hqn).
      rewrite Hpf, Hqf. reflexivity. }
  rewrite Es. exact Hec.
Qed.
Lemma pk_pairs8 : forall cx t m hs,
  fr_RINV cx t m -> gn_pairs m hs -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  Forall pk_ok8 (combine (lm_es m) hs).
Proof.
  intros cx t m hs HRI HP Ht HUs.
  destruct (brig_pairs cx t m hs HRI HP Ht HUs) as (HF & _).
  pose proof HRI as (_ & HR & _).
  destruct HR as (_ & _ & _ & _ & hj & HF2 & _).
  pose proof HP as (HLhs & HFa & _).
  pose proof (Forall2_length HF2) as Lhj.
  apply Forall_forall. intros x Hx.
  split; [exact (proj1 (Forall_forall _ _) HF x Hx)|].
  intros Eo.
  pose proof (proj1 (Forall_forall _ _) HFa x Hx Eo) as Hp.
  apply (In_nth _ _ (W_LLVMFuzzerTestOneInput_gone_base.gn_e0, W_LLVMFuzzerTestOneInput_gone_base.gn_hj0)) in Hx as (i & Hi & Ex).
  rewrite length_combine in Hi.
  rewrite combine_nth in Ex by lia.
  subst x. cbn [fst snd] in Hp |- *.
  exact (pk_pair_ecap cx t m _ _ _ HRI (fr_F2_nth _ _ _ _ _ HF2 i W_LLVMFuzzerTestOneInput_gone_base.gn_e0 W_LLVMFuzzerTestOneInput_gone_base.gn_hj0 ltac:(lia)) Hp).
Qed.

(* ================================================================== the run's input, summed *)
Definition pk_gk (p : rentry * (hsrc * nat)) : Z := gestures_end_b_c.keys_total (re_keys (fst p)).
Definition pk_gp (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then Z.of_nat (length (pending_stream (fst (snd p)))) else 0.
Lemma pk_gk_nonneg : forall p, 0 <= pk_gk p.
Proof. intros p. unfold pk_gk. apply fr_keys_total_nonneg. Qed.
Lemma pk_gp_nonneg : forall p, 0 <= pk_gp p.
Proof. intros p. unfold pk_gp. destruct (re_eof (fst p) =? 0); lia. Qed.
Lemma pk_sum_cost : forall ps, Forall brig_ok ps ->
  zsum (map brig_cost ps) <= zsum (map pk_gk ps) + zsum (map pk_gp ps) + 6000 * Z.of_nat (length ps).
Proof.
  induction ps as [|p ps IH]; intros HF; cbn [map fold_right length]; [lia|].
  apply Forall_cons_iff in HF as [(Hsk & Hop) HF]. specialize (IH HF).
  assert (Hp : brig_cost p <= pk_gk p + pk_gp p + 6000).
  { unfold brig_cost, pk_gk, pk_gp.
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Eo|Eo]; cbv iota.
    - destruct (Hop Eo) as (HU & _). unfold APARTIAL in HU. destruct (re_skip (fst p) =? 0); lia.
    - lia. }
  lia.
Qed.
Lemma pk_sum_pc : forall ps,
  zsum (map brig_pc ps) <= 42 * zsum (map pk_gp ps) + 8 * zsum (map pk_gk ps) + 80320 * Z.of_nat (length ps).
Proof.
  induction ps as [|p ps IH]; cbn [map fold_right length]; [lia|].
  assert (Hp : brig_pc p <= 42 * pk_gp p + 8 * pk_gk p + 80320).
  { unfold brig_pc, pk_gk, pk_gp.
    pose proof (dpre_keys_le (re_keys (fst p))). pose proof (fr_keys_total_nonneg (re_keys (fst p))).
    destruct (re_eof (fst p) =? 0); lia. }
  lia.
Qed.
Lemma pk_sum_k : forall ps, zsum (map pk_gk ps) <= zsum (map brig_cost ps).
Proof.
  induction ps as [|p ps IH]; cbn [map fold_right]; [lia|].
  assert (Hp : pk_gk p <= brig_cost p).
  { unfold brig_cost, pk_gk. destruct (re_eof (fst p) =? 0); [destruct (re_skip (fst p) =? 0)|]; lia. }
  lia.
Qed.

(* ---------------------------------------------------------------- the open pairs' pending bytes *)
Lemma pk_zsum_perm : forall (g : nat -> Z) l l', Permutation l l' -> zsum (map g l) = zsum (map g l').
Proof. intros g l l' HP. induction HP; cbn [map fold_right]; lia. Qed.
(* distinct indices sum to at most all of them (lib/B/ReplyB3LS3Arms.v ls3_sum_incl, any nonnegative weight) *)
Lemma pk_zsum_nodup_le : forall (g : nat -> Z) A Bl, (forall i, 0 <= g i) -> List.NoDup A -> incl A Bl ->
  zsum (map g A) <= zsum (map g Bl).
Proof.
  intros g. induction A as [|a A IH]; intros Bl Hg Hnd Hinc.
  - cbn [map fold_right]. apply zsum_map_nonneg. exact Hg.
  - apply NoDup_cons_iff in Hnd as [Ha Hnd].
    assert (Hin : In a Bl) by (apply Hinc; left; reflexivity).
    destruct (in_split _ _ Hin) as (l1 & l2 & ->).
    assert (Hi : incl A (l1 ++ l2)).
    { intros x Hx. assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hinc; right; exact Hx).
      apply in_app_iff in Hx' as [H1 | [H2 | H3]]; apply in_app_iff;
        [left; exact H1 | subst x; contradiction | right; exact H3]. }
    specialize (IH (l1 ++ l2) Hg Hnd Hi).
    rewrite (pk_zsum_perm g (l1 ++ a :: l2) (a :: l1 ++ l2) (Permutation_sym (Permutation_middle l1 l2 a))).
    cbn [map fold_right]. lia.
Qed.
Lemma pk_zsum_seq : forall (f : option hsrc -> Z) l,
  zsum (map (fun i => f (nth i l None)) (seq 0 (length l))) = zsum (map f l).
Proof.
  intros f l. induction l as [|x l IH]; [reflexivity|].
  cbn [length seq map fold_right nth]. rewrite <- seq_shift, map_map. cbn [nth]. rewrite IH. reflexivity.
Qed.
Lemma pk_slots_cons : forall e (hj : hsrc * nat) ps,
  rig_slots ((e, hj) :: ps) = (if re_eof e =? 0 then [snd hj] else []) ++ rig_slots ps.
Proof. intros e hj ps. unfold rig_slots. cbn [map concat]. reflexivity. Qed.
Lemma pk_gp_slots : forall m ps,
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  zsum (map pk_gp ps) = zsum (map (fun i => slot_pend (nth i (lm_hs m) None)) (rig_slots ps)).
Proof.
  intros m. induction ps as [|[e hj] ps IH]; intros HF HS; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF].
  rewrite pk_slots_cons, map_app, zsum_app. cbn [map fold_right]. cbn [fst snd] in H1.
  change (pk_gp (e, hj)) with (if re_eof e =? 0 then Z.of_nat (length (pending_stream (fst hj))) else 0).
  rewrite <- (IH HF HS).
  destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; cbn [map fold_right].
  - destruct (H1 Eo) as (_ & Hn & _).
    rewrite Hn, (ls3_ps_sp (fst hj) (HS _ _ Hn)). lia.
  - lia.
Qed.
Lemma pk_gp_le_pend : forall m ps,
  length (lm_hs m) = 4%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps ->
  List.NoDup (rig_slots ps) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  zsum (map pk_gp ps) <= pend_bytes m.
Proof.
  intros m ps Hl HF HND HS.
  rewrite (pk_gp_slots m ps HF HS).
  unfold pend_bytes. rewrite <- (pk_zsum_seq slot_pend (lm_hs m)).
  apply pk_zsum_nodup_le; [intros i; apply slot_pend_nonneg | exact HND |].
  intros i Hi. unfold rig_slots in Hi. apply in_concat in Hi as (l & Hl' & Hil).
  apply in_map_iff in Hl' as (p & <- & Hp).
  destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Eo|Eo]; [|destruct Hil].
  destruct Hil as [<- | []].
  destruct (proj1 (Forall_forall _ _) HF p Hp Eo) as (H4 & _).
  apply in_seq. rewrite Hl. lia.
Qed.

End req.

(* ================================================================== the instance *)
Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.

(* what LS v3 gives at any cut point with the pending credit kept: fr_LS3_room_x's proof without dropping
   W_P * pend_bytes from PHI3 (A :619-637) *)
Lemma pk_room_pend : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S, fr_LS3 B CALL_ROOM_B cx t m ly S ->
  blocks_bytes S + 4160659073 + W_P * pend_bytes m <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app.
  unfold PHI3, PHI, held_bytes, vslack in HM.
  pose proof (ECRED_nonneg m).
  pose proof (zsum_map_nonneg slot_held (lm_hs m) slot_held_nonneg).
  pose proof (zsum_map_nonneg entry_held (lm_es m) entry_held_nonneg).
  pose proof (zsum_map_nonneg slot_vsl (lm_hs m) slot_vsl_nonneg).
  pose proof (nopen_le4 _ Hl). pose proof (npend_nonneg m).
  assert (Hk : kk cx m <= c_n cx) by (unfold kk; lia).
  assert (HC : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
  unfold MB_K, MB_C, W_OPEN, E_ENT, K0, APARTIAL, W_H, W_P in *. lia.
Qed.

(* ---------------------------------------------------------------- (1) LS_drain_pre *)
(* conjunct 5 in its slack form: A's ReplyTrPeak.v fr_LS_drain_pre_c5p_slack at fr_LS3 (fr_LS3_drain_pre_c4,
   fr_LS3_room_x) (A :640-681) *)
Lemma pk_drain_c5_slack : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S si h j,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) +
    tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP.
  pose proof (fr_LS3_drain_pre_c4 B CALL_ROOM_B cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU) as HM.
  pose proof (fr_LS3_room_x B CALL_ROOM_B HCR cx t m ly S HLS) as Hroom.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & Hent & Hcost).
  destruct Hp as (_ & _ & _ & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct Hent as (_ & _ & _ & _ & Hsk).
  destruct (Hre Heof) as (S1 & W1).
  destruct Hat as (_ & HO & _).
  set (e := nth j (lm_es m) dr_e0) in *.
  destruct (tp_pos_entry e (fun b Hb => Z.lt_le_incl _ _ (HXP b (in_or_app _ _ _ (or_introl Hb))))) as [Hrc Hka].
  assert (Hcap : 0 <= lm_cap m).
  { apply (tp_pos_out (lm_cap m) (lm_out m)). intros b Hb. apply Z.lt_le_incl, HXP, in_or_app. right.
    apply in_or_app. right. exact Hb. }
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec'.
  assert (HJ : hs_overlong h = 1 \/ bzs (re_U e) = bzs (hs_W h)).
  { destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia. }
  replace (Z.of_nat (length (lm_O m))) with 0 in HM by (rewrite HO; reflexivity).
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  destruct (tp_dr (lm_c m) (lm_mx m) (lm_cap m) e h Hcap Hrc Hka (proj1 Hec') Hoff Hexp HU HJ) as (D1 & _).
  pose proof (tr_peak_le_pos (dr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) e h)) as PK.
  unfold fr_pair_cost in Hcost. cbn [fst] in Hcost.
  pose proof (dpre_keys_le (re_keys e)) as Hkl.
  assert (HX : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0)) by (destruct (re_skip e =? 0); lia).
  assert (EM : CfParamsReply.fr_MMAX = 1072693248) by reflexivity.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia.
Qed.
Lemma pk_drain_c5 : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S si h j,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP.
  pose proof (pk_drain_c5_slack HCR cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP) as H.
  pose proof (tr_max_nonneg'
    (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)). lia.
Qed.
(* the six conjuncts at LS := fr_LS3 (A :699-725) *)
Lemma pk_drain_pre : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S si h j,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP.
  destruct (fr_LS3_drain_pre_c1236 B CALL_ROOM_B cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof)
    as (C1 & C2 & C3).
  pose proof (fr_LS3_drain_pre_c4 B CALL_ROOM_B cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU) as C4.
  pose proof (pk_drain_c5 HCR cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP) as C5.
  exact (conj C1 (conj C2 (conj C3 (conj C4 C5)))).
Qed.

(* ---------------------------------------------------------------- (2) LS_rm_rr_pre *)
(* conjunct 3 in its slack form: A's ReplyTrPeak.v fr_LS_rm_rr_pre_c3p_slack at fr_LS3 (pk_rr_tr_max in place of
   fr_LS_rm_rr_pre_c2, fr_LS3_room_x in place of dr3_room_S) (A :729-768) *)
Lemma pk_rr_c3_slack : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S si h j0,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S + tr_peak (rm_rr_tr m h) + tr_max (rm_rr_tr m h) <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S si h j0 HLS HRI Hat Ht HU Hpos.
  pose proof (pk_rr_tr_max cx t m si h j0 HRI Hat Ht HU) as HM.
  pose proof (fr_LS3_room_x B CALL_ROOM_B HCR cx t m ly S HLS) as Hroom.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & Hc & Hn).
  pose proof Hat as (_ & HO & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct HE as (_ & _ & _ & _ & Hsk).
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  destruct (tp_pos_entry (rm_ent m j0) (fun b Hb => Hpos b (rm3_in_model_entry m j0 b Hj0 Hb))) as [Hrc Hka].
  assert (Hcap : 0 <= lm_cap m).
  { apply (tp_pos_out (lm_cap m) (lm_out m)). intros b Hb. exact (Hpos b (rm3_in_model_out m b Hb)). }
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec'.
  assert (HJ : re_eof (rm_ent m j0) = 0 -> hs_overlong h = 1 \/ bzs (re_U (rm_ent m j0)) = bzs (hs_W h)).
  { intros Eo. destruct (Hre Eo) as (S1 & W1).
    destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia. }
  unfold rm_rr_tr in *.
  replace (Z.of_nat (length (lm_O m))) with 0 in HM by (rewrite HO; reflexivity).
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  pose proof (tp_rr (lm_c m) (lm_mx m) (lm_cap m) (hs_fd h) (lm_es m) h (rm_ent m j0) Hfind Hcap Hrc Hka
                (proj1 Hec') Hoff Hexp HU HJ) as TR.
  pose proof (tr_peak_le_pos (rr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) (hs_fd h) (lm_es m) h)) as PK.
  unfold fr_pair_cost in Hc. cbn [fst] in Hc.
  pose proof (dpre_keys_le (re_keys (rm_ent m j0))) as Hkl.
  pose proof (RelayCap.keys_total_nonneg (re_keys (rm_ent m j0))) as HKT.
  assert (HX : 0 <= (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0))
    by (destruct (re_skip (rm_ent m j0) =? 0); lia).
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold SlotInv.WRITE_MAX, OPS_MAX, pk_TXM in *. lia.
Qed.
Lemma pk_rr_c3 : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S si h j0,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S + tr_peak (rm_rr_tr m h) <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S si h j0 HLS HRI Hat Ht HU Hpos.
  pose proof (pk_rr_c3_slack HCR cx t m ly S si h j0 HLS HRI Hat Ht HU Hpos) as H.
  pose proof (tr_max_nonneg' (rm_rr_tr m h)). lia.
Qed.

(* conjunct 6: the pending credit (pk_room_pend, P <= pend_bytes by HSRC), pk_rr_tr_max, and lm_cap <= 2^29 from
   HCAP0 (lib/B/ReplyB3LS3eCap.v ls3e_cap_lt_MMAX) (A :778-813) *)
Lemma pk_rr_c6 : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S si h j0,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_OUT OUT_MAX4 cx t m ly S -> ReplyB3LS3e.fr_ENT B cx m ly S ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  ent_capout_ok0 (c_W cx) (c_mem cx) ->
  blocks_bytes S + tr_peak (rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S si h j0 HLS HOU HE HRI Hat Ht HU Hpos Hsrc HCAP0.
  pose proof (pk_rr_tr_max cx t m si h j0 HRI Hat Ht HU) as HM.
  pose proof (pk_room_pend HCR cx t m ly S (proj1 HLS)) as Hroom.
  destruct (ls3e_cap_lt_MMAX B CALL_ROOM_B cx t m ly S HLS HOU HE HCAP0) as (_ & Hcap29 & _).
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE' & Hc & Hn).
  pose proof Hat as (_ & HO & _ & _ & Hsi & Hh & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff). cbn [fst snd] in Hre, Hexp, Hec, Hpe, Hoff.
  destruct HE' as (_ & _ & _ & _ & Hsk).
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  destruct (tp_pos_entry (rm_ent m j0) (fun b Hb => Hpos b (rm3_in_model_entry m j0 b Hj0 Hb))) as [Hrc Hka].
  assert (Hcap : 0 <= lm_cap m).
  { apply (tp_pos_out (lm_cap m) (lm_out m)). intros b Hb. exact (Hpos b (rm3_in_model_out m b Hb)). }
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec'.
  assert (HJ : re_eof (rm_ent m j0) = 0 -> hs_overlong h = 1 \/ bzs (re_U (rm_ent m j0)) = bzs (hs_W h)).
  { intros Eo. destruct (Hre Eo) as (S1 & W1).
    destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia. }
  assert (HPS : Z.of_nat (length (pending_stream h)) <= pend_bytes m).
  { rewrite (ls3_ps_sp h Hsrc). apply ReplyB3LS3o.pend_bytes_in. rewrite <- Hh. apply nth_In.
    pose proof HRI as (_ & (Hl4 & _) & _). lia. }
  unfold rm_rr_tr in *.
  replace (Z.of_nat (length (lm_O m))) with 0 in HM by (rewrite HO; reflexivity).
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  pose proof (tp_rr (lm_c m) (lm_mx m) (lm_cap m) (hs_fd h) (lm_es m) h (rm_ent m j0) Hfind Hcap Hrc Hka
                (proj1 Hec') Hoff Hexp HU HJ) as TR.
  pose proof (tr_peak_le_pos (rr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) (hs_fd h) (lm_es m) h)) as PK.
  unfold fr_pair_cost in Hc. cbn [fst] in Hc.
  pose proof (dpre_keys_le (re_keys (rm_ent m j0))) as Hkl.
  pose proof (RelayCap.keys_total_nonneg (re_keys (rm_ent m j0))) as HKT.
  assert (HX : 0 <= (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0))
    by (destruct (re_skip (rm_ent m j0) =? 0); lia).
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  unfold pk_TXM, W_P in *. lia.
Qed.
(* the six conjuncts at LS := fr_LS3c /\ fr_OUT OUT_MAX4 /\ fr_ENT (A :814-851) *)
Lemma pk_rm_rr_pre : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S si h j0,
  (fr_LS3c B CALL_ROOM_B cx t m ly S /\ fr_OUT OUT_MAX4 cx t m ly S /\ ReplyB3LS3e.fr_ENT B cx m ly S) ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  ent_capout_ok0 (c_W cx) (c_mem cx) ->
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (rm_rr_tr m h) <= LIVE_MAX /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S si h j0 (HLS & HOU & HE) HRI Hat Ht HU Hpos Hsrc HCAP0.
  pose proof (fr_LS3_rm_rr_pre_sizes B CALL_ROOM_B cx t m ly S si h j0 (proj1 HLS) HRI Hat) as C1.
  pose proof (pk_rr_tr_max cx t m si h j0 HRI Hat Ht HU) as C2.
  pose proof (pk_rr_c3 HCR cx t m ly S si h j0 (proj1 HLS) HRI Hat Ht HU Hpos) as C3.
  destruct (ls3e_cap_lt_MMAX B CALL_ROOM_B cx t m ly S HLS HOU HE HCAP0) as (_ & _ & C5).
  pose proof (pk_rr_c6 HCR cx t m ly S si h j0 HLS HOU HE HRI Hat Ht HU Hpos Hsrc HCAP0) as C6.
  refine (conj C1 (conj _ (conj C3 (conj C5 C6)))).
  assert (EM : CfParamsReply.fr_MMAX = 1072693248) by reflexivity. unfold pk_TXM in C2. lia.
Qed.

(* ---------------------------------------------------------------- (3) GN_LS_rig *)
(* R5: the pending credit over the open pairs (every slot's HSRC; the pairs' slots are distinct), pk_rig's request
   bound, and lm_cap <= 2^29 from HCAP0 *)
Lemma pk_rig_r5 : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S hs,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_OUT OUT_MAX4 cx t m ly S -> ReplyB3LS3e.fr_ENT B cx m ly S ->
  fr_RINV cx t m -> gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  ent_capout_ok0 (c_W cx) (c_mem cx) ->
  blocks_bytes S +
    tr_peak (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) +
    4 * Z.max (lm_cap m)
          (tr_max (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs))
    <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S hs HLS HOU HE HRI HP Hop HUs Hpos Hsrc HCAP0.
  destruct Hop as (_ & HO & Ht & _).
  pose proof (pk_room_pend HCR cx t m ly S (proj1 HLS)) as Hroom.
  destruct (ls3e_cap_lt_MMAX B CALL_ROOM_B cx t m ly S HLS HOU HE HCAP0) as (_ & Hcap29 & _).
  destruct (brig_pairs cx t m hs HRI HP Ht HUs) as (HF & HC & Hn & H4).
  pose proof (pk_pairs8 cx t m hs HRI HP Ht HUs) as HF8.
  pose proof HP as (HLhs & HFa & HND).
  pose proof HRI as (_ & (Hl4 & _) & _).
  assert (HFp : Forall brig_okp (combine (lm_es m) hs)).
  { apply Forall_forall. intros p Hp. split; [exact (proj1 (Forall_forall _ _) HF p Hp)|].
    apply (brig_pos_entry m (fst p)); [|exact Hpos].
    destruct p as [e q]. cbn [fst]. exact (in_combine_l _ _ _ _ Hp). }
  assert (Hcap : 0 <= lm_cap m).
  { destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
    apply (Hpos (lm_out m, lm_cap m)). unfold model_blks. right. apply in_or_app. right. apply in_or_app. right.
    unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity. }
  assert (HND' : List.NoDup (rig_slots (combine (lm_es m) hs))).
  { first [exact (proj1 (NoDup_ListNoDup _) HND) | exact HND]. }
  pose proof (pk_gp_le_pend m (combine (lm_es m) hs) Hl4 HFa HND' Hsrc) as HZp.
  pose proof (pk_sum_cost (combine (lm_es m) hs) HF) as HZc.
  pose proof (pk_sum_pc (combine (lm_es m) hs)) as HZpc.
  pose proof (pk_sum_k (combine (lm_es m) hs)) as HZk.
  pose proof (zsum_map_nonneg pk_gp (combine (lm_es m) hs) pk_gp_nonneg) as HZp0.
  pose proof (zsum_map_nonneg pk_gk (combine (lm_es m) hs) pk_gk_nonneg) as HZk0.
  rewrite length_combine, HLhs, Nat.min_id in HZc, HZpc.
  assert (HL : Z.of_nat (length (lm_es m)) <= 4) by lia.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  rewrite HO. cbn [length Z.of_nat].
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr. cbv zeta.
  match goal with |- context [tr_peak (fst (fst (fst (relay_instance_gone_b_c.gone_run
                                ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9))))] =>
    pose proof (brig_run_pos a6 a1 a2 a5 a7 a3 a4 a8 a9 HFp Hcap) as POS;
    pose proof (tr_peak_le_pos (fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))))
      as PK;
    pose proof (dpre_tr_max (fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))) pk_TXM
                  ltac:(unfold pk_TXM; lia)
                  (pk_run_rq8 a6 a1 a2 a5 a7 a3 a4 a8 a9 pk_TXM (c_n cx) HF8 HC
                     ltac:(unfold pk_TXM; lia) ltac:(unfold pk_TXM; lia)
                     ltac:(unfold pk_TXM; lia) ltac:(unfold pk_TXM; lia))) as TM;
    set (T := fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))) in *
  end.
  set (Zc := zsum (map brig_cost (combine (lm_es m) hs))) in *.
  set (Zpc := zsum (map brig_pc (combine (lm_es m) hs))) in *.
  set (Zp := zsum (map pk_gp (combine (lm_es m) hs))) in *.
  set (Zk := zsum (map pk_gk (combine (lm_es m) hs))) in *.
  clearbody T Zc Zpc Zp Zk.
  clear - Hroom Hcap29 HC Hn Hcap HZp HZc HZpc HZk HZp0 HZk0 HL POS PK TM.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  unfold pk_TXM, W_P in *. lia.
Qed.
(* the five conjuncts at LS := fr_LS3c /\ fr_OUT OUT_MAX4 /\ fr_ENT, MMAX := fr_MMAX (A :922-951) *)
Lemma pk_gone_rig : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B -> forall cx t m ly S hs,
  (fr_LS3c B CALL_ROOM_B cx t m ly S /\ fr_OUT OUT_MAX4 cx t m ly S /\ ReplyB3LS3e.fr_ENT B cx m ly S) ->
  fr_RINV cx t m -> gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  ent_capout_ok0 (c_W cx) (c_mem cx) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
Proof.
  intros HCR cx t m ly S hs (HLS & HOU & HE) HRI HP Hop HUs Hpos Hsrc HCAP0 tr.
  pose proof Hop as (_ & HO & Ht & _).
  pose proof (fr_LS3c_gone_rig_c1 B CALL_ROOM_B cx t m ly S hs HLS HRI HP HO Ht HUs) as R1.
  pose proof (fr_LS3c_gone_rig_c2p B CALL_ROOM_B HCR cx t m ly S hs HLS HRI HP HO Ht HUs Hpos) as R2.
  destruct (ls3e_cap_lt_MMAX B CALL_ROOM_B cx t m ly S HLS HOU HE HCAP0) as (_ & _ & R4).
  pose proof (pk_rig_r5 HCR cx t m ly S hs HLS HOU HE HRI HP Hop HUs Hpos Hsrc HCAP0) as R5.
  unfold tr.
  refine (conj R1 (conj _ (conj R4 R5))). lia.
Qed.

(* ================================================================== the plugs *)
(* each plug is stated at B top_x's own text (lib/B/W_LLVMFuzzerTestOneInput_top_x.v; the B cutover's re-point,
   a Theorem Labs lane 10:58Z) at RINV := fr_RINV (MT := ameter_triv; the `_m` forms drop the meter conjunct); top_x's
   CAPOUT_MAX is lib/B's cut's (W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX, the body of lib/B/ReplyB3LS3eCap.v's), and
   its inline g_capout clause is ReplyB3LS3eCap.v's ent_capout_ok0 unfolded; the TX_* texts these plugs used to have
   are equal to them up to unfolding *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* (1) top_x :461 LS_drain_pre without its meter conjunct (pk_tx_drain_pre_of_m) and at ameter_triv
   (pk_tx_drain_pre_of), at any LS that gives fr_LS3 (A :955-966 at txp_LSx / tx8_LSx: the row reads fr_LS3 only) *)
Lemma pk_tx_drain_pre_of_m : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop,
  (forall cx t m ly S, LSx cx t m ly S -> fr_LS3 B CALL_ROOM_B cx t m ly S) ->
  forall cx t m ly S si h j,
  LSx cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX.
Proof.
  intros HCR LSx HL.
  intros cx t m ly S si h j H HRI Hat Hpick Hj Hfdj Heof Ht HU HXP.
  exact (pk_drain_pre HCR cx t m ly S si h j (HL cx t m ly S H) HRI Hat Hpick Hj Hfdj Heof Ht HU HXP).
Qed.
Lemma pk_tx_drain_pre_of : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop,
  (forall cx t m ly S, LSx cx t m ly S -> fr_LS3 B CALL_ROOM_B cx t m ly S) ->
  forall cx t m ly S si h j,
  LSx cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok ameter_triv S (dr_cost ameter_triv (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros HCR LSx HL cx t m ly S si h j H HRI Hat Hpick Hj Hfdj Heof Ht HU HXP.
  destruct (pk_tx_drain_pre_of_m HCR LSx HL cx t m ly S si h j H HRI Hat Hpick Hj Hfdj Heof Ht HU HXP) as (C1 & C2 & C3 & C4 & C5).
  exact (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 I))))).
Qed.
(* (2) top_x :678 LS_rm_rr_pre without its meter conjunct (pk_tx_rm_rr_pre_of_m) and at ameter_triv
   (pk_tx_rm_rr_pre_of), at any LS that gives fr_LS3c /\ fr_OUT OUT_MAX4 /\ fr_ENT (A :967-978 at txp_LSx B OUT_MAX4
   / tx8_LSx B OUT_MAX4) *)
Lemma pk_tx_rm_rr_pre_of_m : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop,
  (forall cx t m ly S, LSx cx t m ly S ->
     fr_LS3c B CALL_ROOM_B cx t m ly S /\ fr_OUT OUT_MAX4 cx t m ly S /\ ReplyB3LS3e.fr_ENT B cx m ly S) ->
  forall cx t m ly S si h j0,
  LSx cx t m ly S -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX) ->
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros HCR LSx HL.
  intros cx t m ly S si h j0 H. exact (pk_rm_rr_pre HCR cx t m ly S si h j0 (HL cx t m ly S H)).
Qed.
Lemma pk_tx_rm_rr_pre_of : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop,
  (forall cx t m ly S, LSx cx t m ly S ->
     fr_LS3c B CALL_ROOM_B cx t m ly S /\ fr_OUT OUT_MAX4 cx t m ly S /\ ReplyB3LS3e.fr_ENT B cx m ly S) ->
  forall cx t m ly S si h j0,
  LSx cx t m ly S -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX) ->
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  mo_ok ameter_triv S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost ameter_triv) m h) /\ lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros HCR LSx HL cx t m ly S si h j0 H HRI Hat Ht HU Hpos Hsrc HCAP0.
  destruct (pk_tx_rm_rr_pre_of_m HCR LSx HL cx t m ly S si h j0 H HRI Hat Ht HU Hpos Hsrc HCAP0) as (C1 & C2 & C3 & C5 & C6).
  exact (conj C1 (conj C2 (conj C3 (conj I (conj C5 C6))))).
Qed.
(* (3) top_x :873 GN_LS_rig_x without its meter conjunct (pk_tx_gone_rig_of_m) and at ameter_triv
   (pk_tx_gone_rig_of) (B gone_base's GN_LS_rig at MMAX := fr_MMAX), the same LS (A :979-992 at txp_LSx B OUT_MAX4 /
   tx8_LSx B OUT_MAX4) *)
Lemma pk_tx_gone_rig_of_m : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop,
  (forall cx t m ly S, LSx cx t m ly S ->
     fr_LS3c B CALL_ROOM_B cx t m ly S /\ fr_OUT OUT_MAX4 cx t m ly S /\ ReplyB3LS3e.fr_ENT B cx m ly S) ->
  forall cx t m ly S hs,
  LSx cx t m ly S -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_gone_base.gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
Proof.
  intros HCR LSx HL.
  intros cx t m ly S hs H. exact (pk_gone_rig HCR cx t m ly S hs (HL cx t m ly S H)).
Qed.
Lemma pk_tx_gone_rig_of : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop,
  (forall cx t m ly S, LSx cx t m ly S ->
     fr_LS3c B CALL_ROOM_B cx t m ly S /\ fr_OUT OUT_MAX4 cx t m ly S /\ ReplyB3LS3e.fr_ENT B cx m ly S) ->
  forall cx t m ly S hs,
  LSx cx t m ly S -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_gone_base.gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\ mo_ok ameter_triv S (tr_cost ameter_triv tr) /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
Proof.
  intros HCR LSx HL cx t m ly S hs H HRI HP Hop HUs Hpos Hsrc HCAP0.
  pose proof (pk_tx_gone_rig_of_m HCR LSx HL cx t m ly S hs H HRI HP Hop HUs Hpos Hsrc HCAP0) as X. cbv zeta in X |- *.
  destruct X as (R1 & R2 & R4 & R5). exact (conj R1 (conj R2 (conj I (conj R4 R5)))).
Qed.
End inst.

(* ================================================================== the plugs at B's instance *)
(* LSI B OUT_MAX4 fr_CAP (lib/B/ReplyLS3B_inst.v, its fr_LS3cp at YCfn_cf.CALL_ROOM_B), through lsi_parts; A's
   ReplyLSI.v :665-676 lsi_LS_rm_rr_pre / lsi_GN_LS_rig; top_x's texts at that LSx *)
Section lsi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable fr_CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop.

Lemma pk_lsi_rm_rr_pre_m : forall cx t m ly S si h j0,
  (ReplyLS3B_inst.LSI B OUT_MAX4 fr_CAP) cx t m ly S -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX) ->
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  apply (pk_tx_rm_rr_pre_of_m B YCfn_cf.CALL_ROOM_B (Z.le_refl _) (ReplyLS3B_inst.LSI B OUT_MAX4 fr_CAP)).
  intros cx t m ly S H.
  destruct (ReplyLS3B_inst.lsi_parts B OUT_MAX4 fr_CAP cx t m ly S H) as (_ & H3c & _ & HO & HE & _).
  exact (conj H3c (conj HO HE)).
Qed.
Lemma pk_lsi_rm_rr_pre : forall cx t m ly S si h j0,
  (ReplyLS3B_inst.LSI B OUT_MAX4 fr_CAP) cx t m ly S -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX) ->
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  mo_ok ameter_triv S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost ameter_triv) m h) /\ lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j0 H HRI Hat Ht HU Hpos Hsrc HCAP0.
  destruct (pk_lsi_rm_rr_pre_m cx t m ly S si h j0 H HRI Hat Ht HU Hpos Hsrc HCAP0) as (C1 & C2 & C3 & C5 & C6).
  exact (conj C1 (conj C2 (conj C3 (conj I (conj C5 C6))))).
Qed.
Lemma pk_lsi_gone_rig_m : forall cx t m ly S hs,
  (ReplyLS3B_inst.LSI B OUT_MAX4 fr_CAP) cx t m ly S -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_gone_base.gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
Proof.
  apply (pk_tx_gone_rig_of_m B YCfn_cf.CALL_ROOM_B (Z.le_refl _) (ReplyLS3B_inst.LSI B OUT_MAX4 fr_CAP)).
  intros cx t m ly S H.
  destruct (ReplyLS3B_inst.lsi_parts B OUT_MAX4 fr_CAP cx t m ly S H) as (_ & H3c & _ & HO & HE & _).
  exact (conj H3c (conj HO HE)).
Qed.
Lemma pk_lsi_gone_rig : forall cx t m ly S hs,
  (ReplyLS3B_inst.LSI B OUT_MAX4 fr_CAP) cx t m ly S -> fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_gone_base.gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\ mo_ok ameter_triv S (tr_cost ameter_triv tr) /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
Proof.
  intros cx t m ly S hs H HRI HP Hop HUs Hpos Hsrc HCAP0.
  pose proof (pk_lsi_gone_rig_m cx t m ly S hs H HRI HP Hop HUs Hpos Hsrc HCAP0) as X. cbv zeta in X |- *.
  destruct X as (R1 & R2 & R4 & R5). exact (conj R1 (conj R2 (conj I (conj R4 R5)))).
Qed.
End lsi.
