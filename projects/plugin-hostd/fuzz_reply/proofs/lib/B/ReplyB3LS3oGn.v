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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v, with its module paths and module names changed; 271 of its 342 lines of code are new or changed and 2852 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3oGn.v (sha256
   5c71d2347914; internal record) at d9e8f914caaf (the same blob as at 1b1e21bdbd40),
   row G-BLS3-port: A's lemmas under A's names and statements over lib/B's records and lib/B/ReplyLSBo.v's fr_OUT
   (`fr_OUT OM cx t m ly S`), with these swaps:
   - the Require header is lib/B/ReplyB3LS3cTopxGoneF.v's plus lib/B ReplyLSBTrPeak (A's ReplyTrPeak: tp_inv, tp_R,
     tp_projg, tp_drain_run), ReplyLSBo / ReplyLSBoRf (fr_OUT, MASS, ou_sl_cap_ge, ou_keys_total_nonneg), ReplyB3LS3o
     (A's ReplyLS3o: kw7s_app, kw7s_perm, kw7s_incl, kw7s_upds) and ReplyB3LS3cTopxGoneF (A's ReplyLS3cTopxGoneF:
     gx_xpre_of6, gx6_end_LS3c); A's ReplyLS3cTopxDefs / ReplyLS3cTopxGone -> lib/B ReplyB3LS3cTopxDefs /
     ReplyB3LS3cTopxGone (the gx_* facts, A's names; the gn_* notions are lib/B/W_LLVMFuzzerTestOneInput_gone_base.v's);
   - A's ou_keys_total_nonneg (A :90) is lib/B/ReplyLSBoRf.v's, the same statement, and is not restated;
   - fr_LS3 B -> fr_LS3 B CALL_ROOM_B, fr_LS3c B -> fr_LS3c B CALL_ROOM_B (the Section takes CALL_ROOM_B after B);
     fr_OUT cx -> fr_OUT OM cx; A's xb_same_rest -> ReplyLSBo.v bo_xb_same_rest;
   - KF-COUNT (the meter pattern of a Theorem Labs lane, A #6): A's MT := ameter_triv -> Section ogn's Context
     {MT : ameter_ops}, implicit (read off LS_gone_end_o's mo_le premise, which it passes on to
     ReplyB3LS3cTopxGoneF.v gx6_end_LS3c, generic in the meter too).
   THE TEXT.  A's fr_OUT_gone_end / LS_gone_end_o state 6a2e02357a4's GN_RI_end premises with REQ1-REQ3 (and REQ5 in
   LS_gone_end_o) as A does; lib/B/W_LLVMFuzzerTestOneInput_gone_base.v's GN_RI_end (:581-593) has the same premises
   without REQ and with `(lm_gn m = 0 \/ lm_gn m = 1)`, which neither lemma reads.
   A's header follows. *)
(* fr_OUT (lib/A/ReplyLS3o.v) kept by the gone arm: relay_instance_gone and the table-order check loop.
   proves no function (kind: invariant lemma).

   THE TEXT.  W8's final gone text GN_RI_end: from the model m at the arm's dispatch, relay_instance_gone's model m1
   (gn_after_rig / gn_rig_ok, its rig_rel run over the table) and the loop's model mc (gn_run to its end), it
   concludes LS cx (t + 1) mc lyx Sx.  fr_OUT_gone_end below is fr_OUT's half of that conclusion, at GN_RI_end's
   premises with RINV := fr_RINV and LS := fr_LS3 B /\ fr_OUT OM; LS_gone_end_o is the whole LS conjunct at
   LS := fr_LS3c B /\ fr_OUT OM, with ReplyLS3cTopxGoneF.v gx6_end_LS3c for the first half.

   WHY IT HOLDS.  One gone operation sends, for each entry of the table in order, the entry's drained lines (when
   it is open) and the END lines of its keys with the instance prefix (rig_rel).  As for remove
   (ReplyLS3o.ou_rm_cap2), an open entry sends at most 2 * (its mass + its source's pending bytes), because the
   END lines of the keys this drain made are paid by the begin lines' own key weight (kw7).  Summed over the table
   that is at most 2 * MASS m (the open entries' slots are distinct, gn_pairs), and send_line leaves g_capout at
   most twice what it has sent (ReplyLS3cTopxGone.v gx_rig), so cap2 <= max (lm_cap m) (4 * MASS m), which
   OUT_MAX4 covers at t < OPS_MAX (gn_op).  MASS does not grow: a drained entry's new unfinished line and keys are
   within its old ones and the pending bytes it read (ReplyLS3cTopxGone.v gx_drain_fin), the ended keys leave, and
   the drained slots' pending lists are empty; the check loop (gn_run) keeps the table and every pending list
   (check_no_loss and check_shape_ends change only the expected and held lists).  XB is unchanged by GN_RI_end's
   own block-relation premise.

   NAMED HYPOTHESES.  Only ReplyLS3cTopxGoneF.v's REQ1-REQ3 (0 <= lm_cap m; the relay entries' representation;
   the sources' pending clauses); through gx_xpre_of6 they give every open pair's gx_pf.  0 <= cap2 is PROVED (a
   drain never lowers g_capout below 0, ReplyTrPeak.v tp_drain_run; send_line never lowers it).  fr_OUT_gone_end
   does not use GN_RI_end's mo_le premise nor REQ5. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c RelayCap
  SlotReads SlotInv SlotDrain3Aux SlotPass2Aux relay_remove_b_aux send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
ReplyB3Base ReplyB3LS3 ReplyB3LS3Arms ReplyB3LSCntL ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cTopxDefs ReplyB3LS3cTopxGone.
(* gn_pairs is gone_base's (ReplyLSBArms's copy goes, s5-r1d's cutover) *)
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBo ReplyLSBoRf ReplyB3LS3o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cTopxGoneF.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== one entry of relay_instance_gone (A :83-186) *)
(* what an open entry's source may still send: its pending bytes *)
Definition ou_ps (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then Z.of_nat (length (pending_stream (fst (snd p)))) else 0.
(* an entry of the table with its source: its mass and, when it is open, its source's pending bytes *)
Definition ou_pm (p : rentry * (hsrc * nat)) : Z := ent_mass (fst p) + ou_ps p.

Lemma ou_zsum_opp : forall {X : Type} (g : X -> Z) l, zsum (map (fun x => - g x) l) = - zsum (map g l).
Proof. intros X g l. induction l as [|x l IH]; cbn [map fold_right]; lia. Qed.
(* g_capout does not fall over a send *)
Lemma ou_sends_ge : forall mx Bs c O cap, 0 <= cap -> cap <= snd (sl_sends mx c O cap Bs).
Proof.
  intros mx Bs. induction Bs as [|Bl r IH]; intros c O cap Hc; cbn [sl_sends]; [cbn [snd]; lia|].
  pose proof (ou_sl_cap_ge c mx (Z.of_nat (length O)) cap (Z.of_nat (length Bl)) Hc) as H1.
  pose proof (IH (sl_ctl c (Z.of_nat (length Bl))) (sl_O c O Bl)
                (sl_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length Bl))) ltac:(lia)) as H2. lia.
Qed.
(* nor over a drain: ReplyLSBTrPeak.v tp_drain_run's round invariant, at any g_nout *)
Lemma ou_dr_ocap : forall lv mx no cap (e : rentry) h,
  0 <= cap -> 0 <= re_cap e -> 0 <= drain_b_c.ent_ka e -> Z.of_nat (length (re_U e)) <= APARTIAL ->
  0 <= hs_off h -> hl_recs (hs_expected h) = [] -> 0 <= hl_cap (hs_expected h) ->
  0 <= drain_b_c.ds_ocap (drain_b_c.drain_fin lv mx no cap e h).
Proof.
  intros lv mx no cap e h Hcap Hrc Hka HU Hoff Hexp Hec.
  unfold APARTIAL in HU.
  assert (HI : tp_inv (Z.max (re_cap e) 20192)
                 (Z.max (hl_cap (hs_expected h)) (Z.max 8 (2 * Z.of_nat (length (pending_stream h)))))
                 (Z.of_nat (length (pending_stream h))) (drain_b_c.drain_init no cap e h)).
  { unfold tp_inv, tp_R. rewrite rm3_dstr_init, RelayCap.rc_length_bzs.
    unfold drain_b_c.drain_init. tp_projg. unfold hl_n. rewrite Hexp, RelayCap.rc_length_bzs. cbn [length]. lia. }
  destruct (tp_drain_run (S (S (length (pending_stream h)))) lv mx (drain_b_c.drain_init no cap e h)
              0%nat drain_b_c.dadr0 (Z.max (re_cap e) 20192)
              (Z.max (hl_cap (hs_expected h)) (Z.max 8 (2 * Z.of_nat (length (pending_stream h)))))
              (Z.of_nat (length (pending_stream h))) ltac:(lia) ltac:(lia) HI) as [_ T2].
  unfold drain_b_c.drain_fin, drain_b_c.drain_go.
  destruct T2 as (_ & _ & F3 & _). exact F3.
Qed.

(* gestures_end_instance: the ended keys send at most what they weigh, and the kept keys weigh at most the rest *)
Lemma ou_geik_mass : forall pre ks,
  gestures_end_b_c.keys_total (fst (geik pre ks)) + kw7s (drain_b_c.keys_texts (snd (geik pre ks))) <=
  kw7s (drain_b_c.keys_texts ks).
Proof.
  intros pre ks. unfold geik.
  destruct (gx_geik_loop (length ks) pre 0 ks) as (HP & _).
  pose proof (ou_keys_total_kw7 (fst (geik_loop (length ks) pre 0 ks))) as H1.
  assert (E : kw7s (drain_b_c.keys_texts ks) =
              kw7s (drain_b_c.keys_texts (fst (geik_loop (length ks) pre 0 ks))) +
              kw7s (drain_b_c.keys_texts (snd (geik_loop (length ks) pre 0 ks)))).
  { rewrite <- kw7s_app. apply kw7s_perm. unfold drain_b_c.keys_texts. rewrite <- map_app.
    apply Permutation_map. exact HP. }
  lia.
Qed.

(* an open entry: what it sends (its drained lines and the END lines of its prefixed keys), and its mass after *)
Lemma ou_open_entry : forall pre c mx (O : list byte) cap e h j e1 h1 LB,
  gx_pf (e, (h, j)) -> dr_rel c mx (Z.of_nat (length O)) cap e h e1 h1 LB ->
  Z.of_nat (length LB) + gestures_end_b_c.keys_total (fst (geik pre (re_keys e1))) <=
    2 * (ent_mass e + Z.of_nat (length (pending_stream h))) /\
  ent_mass (entry_keys e1 (snd (geik pre (re_keys e1)))) <= ent_mass e + Z.of_nat (length (pending_stream h)).
Proof.
  intros pre c mx O cap e h j e1 h1 LB Hpf Hdr.
  destruct Hpf as (Hexp & Hec0 & Hoff & Hsk & HskU & Hsk01 & Hepre & Hkh & Hhpre & Hps).
  cbn [fst snd] in *.
  pose proof Hepre as (Hce & HU & HUz & _).
  destruct (gx_dr_rel c mx (Z.of_nat (length O)) cap e h e1 h1 LB Hdr)
    as (_ & _ & HU' & _ & Hnd & Hss & _ & _ & _ & _ & _ & _ & _ & _ & HLB).
  set (NO := Z.of_nat (length O)) in *.
  set (Ls := dr_lines h) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))).
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  assert (Hkh168 : 168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e).
  { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & E2) | (E1 & E2)].
    - rewrite E1, E2. cbn [length Z.of_nat Z.eqb]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live c h) mx NO cap e h HJ (dr3_pok NO cap e h Hoff Hhpre) Hce0)
    as Hno.
  change (lines (hs_state h) (bzs (pending_stream h))) with Ls in Hno. fold TOT in Hno.
  assert (HU6 : Z.of_nat (length (re_U e)) <= 6000) by (unfold APARTIAL in HU; lia).
  destruct (gx_drain_fin (dr_live c h) mx NO cap e h (proj1 Hhpre) Hkh168 Hce HU6 Hec0) as (RM & _).
  unfold dr_fin in HU'. rewrite <- HU' in RM. rewrite SlotReads.bzs_length in RM.
  assert (HMASS : TOT + Z.of_nat (length (re_U e1)) <=
                  Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h))) by lia.
  assert (HLBl : Z.of_nat (length LB) = TOT)
    by (unfold TOT; rewrite <- HLB, SlotReads.bzs_length; reflexivity).
  assert (HK1 : kw7s (drain_b_c.keys_texts (re_keys e1)) <= kw7s (drain_b_c.keys_texts (re_keys e)) + TOT).
  { pose proof (kw7s_incl _ _ (proj1 (NoDup_ListNoDup _) Hnd) (fun y Hy => proj1 (Hss y) Hy)) as K1.
    pose proof (kw7s_upds Ls (drain_b_c.keys_texts (re_keys e))) as K2. fold TOT in K2. lia. }
  pose proof (ou_geik_mass pre (re_keys e1)) as HG.
  pose proof (kw7s_nonneg (drain_b_c.keys_texts (snd (geik pre (re_keys e1))))) as HK0.
  pose proof (ou_keys_total_nonneg (fst (geik pre (re_keys e1)))) as HT0.
  pose proof (kw7s_nonneg (drain_b_c.keys_texts (re_keys e))) as HKe.
  assert (EM' : ent_mass (entry_keys e1 (snd (geik pre (re_keys e1)))) =
                Z.of_nat (length (re_U e1)) + kw7s (drain_b_c.keys_texts (snd (geik pre (re_keys e1)))))
    by reflexivity.
  rewrite EM'. unfold ent_mass. lia.
Qed.

(* ================================================================== relay_instance_gone's table run (A :188-254) *)
(* what the run sends and the mass it leaves, pair by pair; ReplyB3LS3cTopxGone.v gx_rig's induction with the mass
   in place of the potential *)
Lemma ou_rig : forall pre mx ps qs c O cap c2 O2 cap2,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 ->
  Forall (fun p => re_eof (fst p) = 0 -> gx_pf p) ps -> 0 <= cap ->
  Z.of_nat (length O2) - Z.of_nat (length O) <= 2 * zsum (map ou_pm ps) /\
  zsum (map (fun q => ent_mass (fst q)) qs) <= zsum (map ou_pm ps) /\
  0 <= cap2.
Proof.
  intros pre mx ps. induction ps as [|[e [h j]] r IH]; intros qs c O cap c2 O2 cap2 HR HF Hc.
  - destruct qs as [|q qs]; cbn [rig_rel] in HR; [|contradiction].
    destruct HR as (-> & -> & ->). cbn [map fold_right]. lia.
  - destruct qs as [|[e' h1] q]; cbn [rig_rel] in HR; [contradiction|].
    destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & He' & Hrest).
    apply Forall_cons_iff in HF as [Hp HF]. cbn [fst snd] in Hp.
    match type of Hrest with context [sl_sends ?a ?b ?d ?f ?g] =>
      destruct (sl_sends a b d f g) as [[c3 O3] cap3] eqn:ES end.
    cbn [map fold_right fst snd].
    subst e'.
    assert (EP : ou_pm (e, (h, j)) = ent_mass e + (if re_eof e =? 0 then Z.of_nat (length (pending_stream h)) else 0))
      by reflexivity.
    rewrite EP.
    revert Hd ES. destruct (re_eof e =? 0) eqn:Eo; cbn [andb]; intros Hd ES.
    + apply Z.eqb_eq in Eo. specialize (Hp Eo).
      destruct (ou_open_entry pre c mx O cap e h j e1 h1 LB Hp Hd) as (Q1 & Q2).
      pose proof Hp as (_ & Hec & Hoff & _ & _ & _ & Hepre & Hkh & _ & _). cbn [fst snd] in Hec, Hoff, Hepre, Hkh.
      pose proof Hp as (Hexp & _). cbn [fst snd] in Hexp.
      destruct Hepre as (Hce & HU & _ & _ & _).
      assert (Hka : 0 <= drain_b_c.ent_ka e).
      { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & _) | (E1 & E2)].
        - rewrite E1. cbn [Z.eqb]. lia.
        - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
      assert (Hoc0 : 0 <= drain_b_c.ds_ocap (dr_fin c mx (Z.of_nat (length O)) cap e h))
        by (unfold dr_fin; apply ou_dr_ocap; try assumption; lia).
      pose proof (ou_keys_total_nonneg (fst (geik pre (re_keys e1)))) as HT0.
      destruct (dr_live c h) eqn:Lv.
      * destruct (gx_sends mx _ _ _ _ _ _ _ (drain_b_c.ds_ocap (dr_fin c mx (Z.of_nat (length O)) cap e h)) ES
                  ltac:(lia)) as (S1 & S2 & S3).
        rewrite gx_ge_bytes_len, length_app in S1.
        pose proof (ou_sends_ge mx (ge_bytes (fst (geik pre (re_keys e1)))) (dr_ctl c h ev) (O ++ LB)
                      (drain_b_c.ds_ocap (dr_fin c mx (Z.of_nat (length O)) cap e h)) Hoc0) as G.
        rewrite ES in G. cbn [snd] in G.
        destruct (IH q c3 O3 cap3 c2 O2 cap2 Hrest HF ltac:(lia)) as (I1 & I2 & I3).
        refine (conj _ (conj _ I3)); lia.
      * destruct (gx_sends mx _ _ _ _ _ _ _ cap ES ltac:(lia)) as (S1 & S2 & S3).
        rewrite gx_ge_bytes_len in S1.
        pose proof (ou_sends_ge mx (ge_bytes (fst (geik pre (re_keys e1)))) (dr_ctl c h ev) O cap Hc) as G.
        rewrite ES in G. cbn [snd] in G.
        destruct (IH q c3 O3 cap3 c2 O2 cap2 Hrest HF ltac:(lia)) as (I1 & I2 & I3).
        refine (conj _ (conj _ I3)); lia.
    + destruct Hd as [-> ->].
      pose proof (ou_geik_mass pre (re_keys e)) as HG.
      pose proof (kw7s_nonneg (drain_b_c.keys_texts (snd (geik pre (re_keys e))))) as HK0.
      pose proof (ou_keys_total_nonneg (fst (geik pre (re_keys e)))) as HT0.
      assert (EM' : ent_mass (entry_keys e (snd (geik pre (re_keys e)))) =
                    Z.of_nat (length (re_U e)) + kw7s (drain_b_c.keys_texts (snd (geik pre (re_keys e)))))
        by reflexivity.
      assert (EM : ent_mass e = Z.of_nat (length (re_U e)) + kw7s (drain_b_c.keys_texts (re_keys e)))
        by reflexivity.
      destruct (gx_sends mx _ _ _ _ _ _ _ cap ES ltac:(lia)) as (S1 & S2 & S3).
      rewrite gx_ge_bytes_len in S1.
      pose proof (ou_sends_ge mx (ge_bytes (fst (geik pre (re_keys e)))) c O cap Hc) as G.
      rewrite ES in G. cbn [snd] in G.
      destruct (IH q c3 O3 cap3 c2 O2 cap2 Hrest HF ltac:(lia)) as (I1 & I2 & I3).
      refine (conj _ (conj _ I3)); lia.
Qed.

(* ================================================================== GN_RI_end's fr_OUT (A :256-409) *)
Section ogn.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the call room of fr_LS3 (ReplyB3LS3.v, as ReplyLSB.fr_LS takes it) *)
Variable CALL_ROOM_B : Z.
(* the meter (KF-COUNT): a Variable, implicit, read off LS_gone_end_o's mo_le premise *)
Context {MT : ameter_ops}.
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.

(* fr_OUT kept over the gone operation: 6a2e02357a4's GN_RI_end premises with RINV := fr_RINV and
   LS := fr_LS3 B CALL_ROOM_B /\ fr_OUT OM, plus ReplyB3LS3cTopxGoneF.v's REQ1-REQ3 after the per-entry premise (the
   same named hypotheses gx6_end_LS3 takes).  mo_le and REQ5 are not used. *)
Lemma fr_OUT_gone_end : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate),
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
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_OUT OM cx t m ly S ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  fr_OUT OM cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx HRI Hop HE Hcap HE6 HS6 HLS (U1 & U2 & U3 & U4)
    Hpairs Hafter Hrok Hrun Hfr.
  pose proof (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hpairs) as HX.
  pose proof (gx_pf_all cx t m hs HRI Hpairs HX) as HPF.
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof HX as (HO & _ & _).
  pose proof Hpairs as (Hlh & HPok & HRS).
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (Hrr & Hlq & _ & Hfds).
  pose proof HRI as (_ & (Hl4 & _) & _).
  pose proof Hop as (_ & _ & Ht & _).
  pose proof (gx_rig_pairs _ _ _ _ _ _ _ _ _ _ Hrr) as HRP.
  set (ps := combine (lm_es m) hs) in *.
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  (* the run: what it sends, the mass it leaves, and g_capout *)
  destruct (ou_rig _ (lm_mx m) ps qs (lm_c m) (lm_O m) (lm_cap m) c2 O2 cap2 Hrr HPF U1) as (R1 & R2 & R3).
  destruct (gx_rig _ (lm_mx m) ps qs (lm_c m) (lm_O m) (lm_cap m) c2 O2 cap2 (lm_cap m) Hrr (gx_pre_len _) HPF
              ltac:(lia)) as (_ & R4).
  rewrite HO in R1. cbn [length Z.of_nat] in R1.
  (* the loop keeps the table, g_capout and every slot's pending bytes *)
  assert (Hnd : List.NoDup (map re_fd (lm_es m1))) by (rewrite A3; apply NoDup_ListNoDup; exact Hfds).
  destruct (gx_run _ m1 mc A _ _ Hrun Hnd) as (R5 & R6 & _ & _ & _ & R7 & Hhist & _).
  assert (Hpm1 : pend_bytes mc = pend_bytes m1).
  { unfold pend_bytes. rewrite (gx_sum4 slot_pend (lm_hs mc) ltac:(lia)), (gx_sum4 slot_pend (lm_hs m1) A11).
    assert (Hk : forall k', slot_pend (nth k' (lm_hs mc) None) = slot_pend (nth k' (lm_hs m1) None)).
    { intros k'. destruct (Hhist k') as [L | (h0 & h2 & i0 & X1 & X2 & X3 & _)]; [rewrite L; reflexivity|].
      rewrite X1, X2.
      destruct X3 as (h' & E' & H' & P & g & A0 & ob & ds & c & (E1 & _) & (H'' & E2 & _)).
      subst. reflexivity. }
    rewrite !Hk. reflexivity. }
  (* relay_instance_gone empties the pending lists of the slots it drains and keeps the others *)
  assert (HALL : Forall (fun pq => re_eof (fst (fst pq)) = 0 ->
            nth (snd (snd (fst pq))) (lm_hs m) None = Some (fst (snd (fst pq))) /\
            nth (snd (snd (fst pq))) (lm_hs m1) None = Some (snd (snd pq)) /\
            slot_pend (Some (fst (snd (fst pq)))) = Z.of_nat (length (pending_stream (fst (snd (fst pq))))) /\
            slot_pend (Some (snd (snd pq))) = 0) (combine ps qs)).
  { rewrite Forall_forall in HPQ, HRP, HPF |- *. intros [p q] Hin Heof. cbn [fst snd] in Heof |- *.
    destruct (HPQ (p, q) Hin Heof) as (_ & Q2 & Q3). cbn [fst snd] in Q2, Q3.
    destruct (HRP (p, q) Hin) as (_ & Hdr). cbn [fst snd] in Hdr.
    destruct (Hdr Heof) as (c' & mx' & no & cap' & e1 & LB & D).
    destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ D) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Dp & Do & _).
    pose proof (HPF p (in_combine_l _ _ _ _ Hin) Heof) as Hpf.
    destruct Hpf as (_ & _ & _ & _ & _ & _ & _ & _ & Hhpre & _).
    split; [exact Q2|]. split; [exact Q3|]. split.
    - symmetry. exact (ls3_ps_sp _ (proj1 Hhpre)).
    - cbn [slot_pend]. unfold hl_bytes. rewrite Dp, Do. reflexivity. }
  set (F := fun j => slot_pend (nth j (lm_hs m1) None) - slot_pend (nth j (lm_hs m) None)).
  assert (S1 : pend_bytes m1 - pend_bytes m = F 0%nat + F 1%nat + F 2%nat + F 3%nat).
  { unfold pend_bytes, F. rewrite (gx_sum4 slot_pend (lm_hs m1) A11), (gx_sum4 slot_pend (lm_hs m) Hl4). lia. }
  assert (S2 : F 0%nat + F 1%nat + F 2%nat + F 3%nat = zsum (map F (rig_slots ps))).
  { apply gx_sum_RS.
    - apply NoDup_ListNoDup. exact HRS.
    - intros j Hj. destruct (gx_rs_in j ps Hj) as (p & Hp & Heof & <-).
      rewrite Forall_forall in HPok. destruct (HPok p Hp Heof) as (Hj4 & _). exact Hj4.
    - intros j Hj Hn. unfold F. rewrite (A12 j Hj Hn). lia. }
  rewrite gx_rs_sum in S2.
  rewrite (gx_sum_cfst (fun p => if re_eof (fst p) =? 0 then F (snd (snd p)) else 0) ps qs Hlps) in S2.
  cbv beta in S2.
  assert (S3 : zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then F (snd (snd (fst pq))) else 0)
                     (combine ps qs)) =
               zsum (map (fun pq => - ou_ps (fst pq)) (combine ps qs))).
  { apply (gx_sum_ext _ _ _ _ HALL). intros [p q] Hpq. cbn [fst snd] in Hpq |- *. unfold ou_ps.
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|lia].
    apply Z.eqb_eq in Eo. destruct (Hpq Eo) as (Hm & Hm1 & P1 & P2).
    unfold F. rewrite Hm, Hm1, P1, P2. lia. }
  rewrite ou_zsum_opp, <- (gx_sum_cfst ou_ps ps qs Hlps) in S3.
  (* the mass: the old entries' and the drained sources', against the new entries' *)
  assert (EPM : zsum (map ou_pm ps) = MASSe (lm_es m) + zsum (map ou_ps ps)).
  { unfold ou_pm, MASSe. rewrite (gx_zsum_add (fun p => ent_mass (fst p)) ou_ps ps).
    rewrite (gx_sum_cfst ent_mass (lm_es m) hs ltac:(lia)). reflexivity. }
  assert (EMq : MASSe (lm_es mc) = zsum (map (fun q => ent_mass (fst q)) qs))
    by (unfold MASSe; rewrite R5, A3, map_map; reflexivity).
  assert (Hp1 : 0 <= pend_bytes m1) by (apply zsum_map_nonneg; exact slot_pend_nonneg).
  assert (HMm : MASS m = MASSe (lm_es m) + pend_bytes m) by reflexivity.
  assert (HMc : MASS mc = MASSe (lm_es mc) + pend_bytes mc) by reflexivity.
  assert (HMASS : MASS mc <= MASS m) by lia.
  assert (HOUT : Z.of_nat (length O2) <= 2 * MASS m) by lia.
  (* g_capout and XB *)
  assert (ECap : lm_cap mc = cap2) by (rewrite R6; exact A7).
  destruct HLS as (rest & e0 & HPm & _).
  assert (EX : XB cx mc Sx = XB cx m S) by exact (bo_xb_same_rest B cx m ly S mc lyx Sx rest HPm (Hfr rest HPm)).
  unfold fr_OUT. rewrite EX, ECap. unfold WMAX, OUT_MAX4, OPS_MAX in *. repeat split; try lia.
Qed.

(* GN_RI_end's LS conjunct at LS := fr_LS3c B CALL_ROOM_B /\ fr_OUT OM: ReplyB3LS3cTopxGoneF.v gx6_end_LS3c and the
   above, at 6a2e02357a4's premises (with REQ1-REQ3 after the per-entry premise and REQ5 last, as gx6_end_LS3c takes
   them) *)
Lemma LS_gone_end_o : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
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
  fr_LS3c B CALL_ROOM_B cx t m ly S /\ fr_OUT OM cx t m ly S ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (* REQ5 *)
  (forall j hj hj', nth j (lm_hs m) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
     hl_cap (hs_held hj) <= hl_cap (hs_held hj')) ->
  fr_LS3c B CALL_ROOM_B cx (t + 1) mc lyx Sx /\ fr_OUT OM cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6 HS6 (HLS & HOU) Hpairs Hafter
    Hrok Hrun Hmle Hfr Hns.
  split.
  - exact (gx6_end_LS3c B CALL_ROOM_B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6 HS6
             HLS Hpairs Hafter Hrok Hrun Hmle Hfr Hns).
  - exact (fr_OUT_gone_end cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx HRI Hop HE Hcap HE6 HS6 (proj1 HLS) HOU
             Hpairs Hafter Hrok Hrun Hfr).
Qed.
End ogn.
