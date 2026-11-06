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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v, with its module paths changed; 263 of its 327 lines of code are new or changed and 2859 lines of the source are left out. *)
(* fr_POT (lib/A/ReplyLS3p.v) kept by the gone arm: relay_instance_gone and the table-order check loop.
   proves no function (kind: invariant lemma).

   THE TEXT.  The fr_POT twin of ReplyLS3oGn.v fr_OUT_gone_end: a Theorem Labs lane's final gone text GN_RI_end (
   a working branch 6a2e02357a4, lib/A/W_LLVMFuzzerTestOneInput_gone_base.v) concludes LS cx (t + 1) mc
   lyx Sx from the model m at the arm's dispatch, relay_instance_gone's model m1 (gn_after_rig / gn_rig_ok, its
   rig_rel run over the table) and the loop's model mc (gn_run to its end).  fr_POT_gone_end below is fr_POT's half
   of that conclusion, at fr_OUT_gone_end's premises with fr_OUT OM cx t m ly S replaced by fr_POT cx t m.

   WHY IT HOLDS.  For every class c the potential pt_s c * pt_kc c m + pt_v c * pt_mass m does not grow from m to mc
   (pg_core), so fr_POT_step closes with the one write op's budget unused.  The potential splits by component
   (pg_split): each entry pg_EP c e (its keys of class c, its unfinished line re_U) and each slot pg_SP c o (its
   expected and held texts of class c, its pending bytes past the read offset).  Over relay_instance_gone the slots
   carry pg_SQ c, the held texts and the begin keys of the expected texts (what check_no_loss will turn them into),
   equal to pg_SP c on a slot with no expected record (pg_SQ_SP; every open slot of m by fr_RINV, gx_rinv_slot).
   - An open entry (pg_open): fr_LS3cp_drain_step_p's arithmetic.  Its drained lines (TOT bytes with their NULs) and
     its new re_U are within its old re_U and the pending bytes it read (TOT + U' <= U + P, ReplyLS3cTopxGone.v
     gx_drain_fin), and the slot's pending bytes go to 0 (dr_rel); a begin line with a key of class c adds at most
     one relay key and one future held text, both that key, and pt_s c <= |line| + 1 (pt_nk), so
     pt_s c * (2 nk) <= 2 TOT <= pt_v c * TOT (pt_arith).  gestures_end_instance then removes keys (pg_geik).
   - An eof entry keeps its re_U and loses keys (pg_closed); a slot no open entry drains stays (gn_after_rig).
   - The loop (pg_touch): check_no_loss empties the expected list and leaves the held texts within the old held texts
     and the begin keys of the expected ones (texts H' = upds held expected, NoDup H'); check_shape_ends keeps a sub-
     list of the held records; neither touches the pending list, the read offset or the table.  At the end of the
     loop every slot has an empty expected list: a touched one by check_no_loss, an untouched drained one because
     the loop passed its entry (ReplyLS3cTopxGone.v gx_cov at (|es|, 0)), any other untouched one by fr_RINV.

   PREMISES.  fr_OUT_gone_end's, in its order, with fr_OUT OM cx t m ly S -> fr_POT cx t m.  Dropped because the proof
   does not use them: fr_LS3 B cx t m ly S and the block-permutation premise (so ly, S, lyx, Sx carry type
   annotations and stay unused binders, and B is not a parameter).  Used: fr_RINV (the open slots' empty expected
   lists, the slot count 4, gx_pf), gn_op with the per-entry premise and ReplyLS3cTopxGoneF.v's REQ1-REQ3 (through
   gx_xpre_of6: every open pair's gx_pf), gn_pairs, gn_after_rig, gn_rig_ok, gn_run.  No extra hypothesis and no REQ5:
   the bound does not need the held capacities. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c RelayCap SlotReads SlotInv
  SlotDrain3Aux SlotPass2Aux relay_remove_b_aux send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3 ReplyLS3Arms ReplyLSCntL ReplyLS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3cTopxGone ReplyLS3cTopxGoneF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== the potential by component *)
(* an entry: its keys of class c and its unfinished line *)
Definition pg_EP (c : Z) (e : rentry) : Z := pt_s c * pt_ekc c e + pt_v c * pt_eu e.
(* a slot as fr_POT counts it: its expected and held texts of class c, its pending bytes past the read offset *)
Definition pg_SP (c : Z) (o : option hsrc) : Z := pt_s c * pt_skc c o + pt_v c * slot_pend o.
(* a slot between relay_instance_gone and check_no_loss: its held texts and the begin keys of its expected texts *)
Definition pg_SQ (c : Z) (o : option hsrc) : Z :=
  match o with
  | Some h => pt_s c * (pt_tc c (texts (hs_held h)) + pt_tc c (dr3_nk (texts (hs_expected h)))) +
              pt_v c * slot_pend (Some h)
  | None => 0
  end.

Lemma pg_zsum_lin : forall {X : Type} (a b : Z) (f g : X -> Z) l,
  zsum (map (fun x => a * f x + b * g x) l) = a * zsum (map f l) + b * zsum (map g l).
Proof. intros X a b f g l. induction l as [|x l IH]; cbn [map fold_right]; [ring|]. rewrite IH. ring. Qed.
Lemma pg_split : forall c m, pt_s c * pt_kc c m + pt_v c * pt_mass m =
  zsum (map (pg_EP c) (lm_es m)) + zsum (map (pg_SP c) (lm_hs m)).
Proof.
  intros c m. unfold pt_kc, pt_mass, pend_bytes, pg_EP, pg_SP.
  rewrite (pg_zsum_lin (pt_s c) (pt_v c) (pt_ekc c) pt_eu (lm_es m)).
  rewrite (pg_zsum_lin (pt_s c) (pt_v c) (pt_skc c) slot_pend (lm_hs m)).
  generalize (zsum (map (pt_ekc c) (lm_es m))) (zsum (map (pt_skc c) (lm_hs m))) (zsum (map slot_pend (lm_hs m)))
    (zsum (map pt_eu (lm_es m))) (pt_s c) (pt_v c).
  intros a b d f s v. ring.
Qed.
Lemma pg_SQ_SP : forall c h, hl_recs (hs_expected h) = [] -> pg_SQ c (Some h) = pg_SP c (Some h).
Proof.
  intros c h H. unfold pg_SP. cbn [pg_SQ pt_skc].
  assert (E : texts (hs_expected h) = []) by (unfold texts; rewrite H; reflexivity).
  rewrite E. assert (Z1 : dr3_nk [] = []) by reflexivity. assert (Z0 : pt_tc c [] = 0) by reflexivity.
  rewrite Z1, Z0, Z.add_0_r, Z.add_0_l. reflexivity.
Qed.
Lemma pg_SQ_SP_none : forall c, pg_SQ c None = pg_SP c None.
Proof. intros c. unfold pg_SP. cbn [pg_SQ pt_skc slot_pend]. rewrite !Z.mul_0_r. reflexivity. Qed.

(* ================================================================== relay_instance_gone, entry by entry *)
(* gestures_end_instance keeps a sub-permutation of the keys *)
Lemma pg_geik : forall c pre ks,
  pt_tc c (drain_b_c.keys_texts (snd (geik pre ks))) <= pt_tc c (drain_b_c.keys_texts ks).
Proof.
  intros c pre ks. unfold geik.
  destruct (gx_geik_loop (length ks) pre 0 ks) as (HP & _).
  set (E := fst (geik_loop (length ks) pre 0 ks)) in *.
  set (K := snd (geik_loop (length ks) pre 0 ks)) in *.
  assert (EQ : pt_tc c (drain_b_c.keys_texts ks) =
               pt_tc c (drain_b_c.keys_texts E) + pt_tc c (drain_b_c.keys_texts K)).
  { unfold pt_tc, drain_b_c.keys_texts. rewrite <- zsum_app, <- !map_app.
    apply fr_sum_perm. apply Permutation_map. exact HP. }
  pose proof (pt_tc_nonneg c (drain_b_c.keys_texts E)). lia.
Qed.
(* an eof entry: its keys with the prefix ended, its re_U kept *)
Lemma pg_closed : forall c pre e, pg_EP c (entry_keys e (snd (geik pre (re_keys e)))) <= pg_EP c e.
Proof.
  intros c pre e. unfold pg_EP.
  assert (E1 : pt_ekc c (entry_keys e (snd (geik pre (re_keys e)))) =
               pt_tc c (drain_b_c.keys_texts (snd (geik pre (re_keys e))))) by reflexivity.
  assert (E2 : pt_eu (entry_keys e (snd (geik pre (re_keys e)))) = pt_eu e) by reflexivity.
  rewrite E1, E2. pose proof (pg_geik c pre (re_keys e)) as G. pose proof (pt_s_ge c).
  assert (M : pt_s c * pt_tc c (drain_b_c.keys_texts (snd (geik pre (re_keys e)))) <= pt_s c * pt_ekc c e)
    by (apply Z.mul_le_mono_nonneg_l; [lia | exact G]).
  lia.
Qed.
(* an open entry and its slot: the drain (fr_LS3cp_drain_step_p's arithmetic, check_no_loss's keys in pg_SQ), then
   gestures_end_instance *)
Lemma pg_open : forall c pre cc mx no cap e h j e1 h1 LB,
  gx_pf (e, (h, j)) -> dr_rel cc mx no cap e h e1 h1 LB ->
  pg_EP c (entry_keys e1 (snd (geik pre (re_keys e1)))) + pg_SQ c (Some h1) <= pg_EP c e + pg_SQ c (Some h).
Proof.
  intros c pre cc mx no cap e h j e1 h1 LB Hpf Hdr.
  destruct Hpf as (Hexp & Hec0 & Hoff & Hsk & HskU & Hsk01 & Hepre & Hkh & Hhpre & _).
  cbn [fst snd] in *.
  pose proof Hepre as (Hce & HU & HUz & _).
  destruct (gx_exp_lines cc mx no cap e h e1 h1 LB Hdr Hexp) as (HT & _ & _ & _).
  destruct (gx_dr_rel cc mx no cap e h e1 h1 LB Hdr)
    as (_ & _ & HU' & _ & Hnd & Hss & _ & _ & _ & Dpend & Doff & _ & _ & Dheld & _).
  set (Ls := dr_lines h) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))).
  (* ---- the relay's mass: TOT + U' <= U + P ---- *)
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  assert (Hkh168 : 168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e).
  { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & E2) | (E1 & E2)].
    - rewrite E1, E2. cbn [length Z.of_nat Z.eqb]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live cc h) mx no cap e h HJ (dr3_pok no cap e h Hoff Hhpre) Hce0)
    as Hno.
  change (lines (hs_state h) (bzs (pending_stream h))) with Ls in Hno. fold TOT in Hno.
  assert (HU6 : Z.of_nat (length (re_U e)) <= 6000) by (unfold APARTIAL in HU; lia).
  destruct (gx_drain_fin (dr_live cc h) mx no cap e h (proj1 Hhpre) Hkh168 Hce HU6 Hec0) as (RM & _).
  unfold dr_fin in HU'. rewrite <- HU' in RM. rewrite SlotReads.bzs_length in RM.
  assert (HMASS : TOT + Z.of_nat (length (re_U e1)) <=
                  Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h))) by lia.
  clear RM Hno.
  (* ---- the keys: the drain's are within the old ones and the lines' begin keys; gestures_end_instance removes ---- *)
  assert (KI : pt_ekc c e1 <= pt_ekc c e + pt_tc c (dr3_nk Ls)).
  { unfold pt_ekc, pt_tc. pose proof Hnd as Hnd2. apply NoDup_ListNoDup in Hnd2.
    pose proof (pt_sum_incl (pt_w c) (drain_b_c.keys_texts (re_keys e1))
                  (drain_b_c.keys_texts (re_keys e) ++ dr3_nk Ls) (fun x => proj1 (pt_w_range c x)) Hnd2) as X.
    rewrite map_app, zsum_app in X. apply X. intros y Hy. apply in_or_app.
    destruct (dr3_upds_in Ls _ y (proj1 (Hss y) Hy)) as [Hy'|Hy']; [left | right]; exact Hy'. }
  pose proof (pg_geik c pre (re_keys e1)) as HG.
  change (pt_tc c (drain_b_c.keys_texts (re_keys e1))) with (pt_ekc c e1) in HG.
  pose proof (pt_nk c Ls) as NK. fold TOT in NK.
  pose proof (pt_s_ge c) as Hs. pose proof (pt_v_range c) as Hv.
  assert (HTOT0 : 0 <= TOT) by (unfold TOT; lia).
  (* ---- the slot: pending bytes released, the lines expected, the held texts kept ---- *)
  assert (ES1 : slot_pend (Some h1) = 0) by (cbn [slot_pend]; unfold hl_bytes; rewrite Dpend, Doff; reflexivity).
  assert (ES0 : slot_pend (Some h) = Z.of_nat (length (pending_stream h)))
    by (symmetry; exact (ls3_ps_sp h (proj1 Hhpre))).
  assert (EX0 : texts (hs_expected h) = []) by (unfold texts; rewrite Hexp; reflexivity).
  unfold pg_EP. cbn [pg_SQ]. rewrite ES1, ES0, HT, EX0, Dheld.
  assert (Z0 : pt_tc c (dr3_nk []) = 0) by reflexivity. rewrite Z0.
  assert (Ek : pt_ekc c (entry_keys e1 (snd (geik pre (re_keys e1)))) =
               pt_tc c (drain_b_c.keys_texts (snd (geik pre (re_keys e1))))) by reflexivity.
  assert (Eu : pt_eu (entry_keys e1 (snd (geik pre (re_keys e1)))) = Z.of_nat (length (re_U e1))) by reflexivity.
  assert (Eu0 : pt_eu e = Z.of_nat (length (re_U e))) by reflexivity.
  rewrite Ek, Eu, Eu0.
  pose proof (pt_arith (pt_s c) (pt_v c) (pt_ekc c e + pt_tc c (texts (hs_held h)))
                (pt_tc c (drain_b_c.keys_texts (snd (geik pre (re_keys e1)))) + pt_tc c (texts (hs_held h)) +
                 pt_tc c (dr3_nk Ls))
                (Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h))) (Z.of_nat (length (re_U e1)))
                (pt_tc c (dr3_nk Ls)) TOT ltac:(lia) ltac:(lia) HTOT0 ltac:(lia) NK ltac:(lia)) as AR.
  rewrite !Z.mul_add_distr_l in AR |- *. lia.
Qed.

(* the table run: entries and drained slots after it, against before it (pg_SQ = pg_SP on m's open slots) *)
Lemma pg_rig : forall c pre mx ps qs cc O cap c2 O2 cap2,
  rig_rel pre mx cc O cap ps qs c2 O2 cap2 ->
  Forall (fun p => re_eof (fst p) = 0 -> gx_pf p) ps ->
  zsum (map (fun pq => pg_EP c (fst (snd pq))) (combine ps qs)) +
  zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then pg_SQ c (Some (snd (snd pq))) else 0) (combine ps qs)) <=
  zsum (map (fun pq => pg_EP c (fst (fst pq))) (combine ps qs)) +
  zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then pg_SQ c (Some (fst (snd (fst pq)))) else 0)
          (combine ps qs)).
Proof.
  intros c pre mx ps. induction ps as [|[e [h j]] r IH]; intros qs cc O cap c2 O2 cap2 HR HF.
  - destruct qs as [|q qs]; cbn [rig_rel] in HR; [|contradiction].
    cbn [combine map fold_right]. lia.
  - destruct qs as [|[e' h1] q]; cbn [rig_rel] in HR; [contradiction|].
    destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & He' & Hrest).
    apply Forall_cons_iff in HF as [Hp HF]. cbn [fst snd] in Hp.
    match type of Hrest with context [sl_sends ?a ?b ?d ?f ?g] =>
      destruct (sl_sends a b d f g) as [[c3 O3] cap3] eqn:ES end.
    pose proof (IH q c3 O3 cap3 c2 O2 cap2 Hrest HF) as I.
    clear ES Hrest IH.
    cbn [combine map fold_right fst snd].
    subst e'.
    revert Hd. destruct (re_eof e =? 0) eqn:Eo; cbn [andb]; intros Hd.
    + apply Z.eqb_eq in Eo. specialize (Hp Eo).
      pose proof (pg_open c pre cc mx _ cap e h j e1 h1 LB Hp Hd) as P1. lia.
    + destruct Hd as [-> ->]. pose proof (pg_closed c pre e) as P1. lia.
Qed.

(* ================================================================== the loop: one check_no_loss + check_shape_ends *)
Lemma pg_touch : forall c h h'', gx_touch h h'' ->
  pg_SQ c (Some h'') <= pg_SQ c (Some h) /\ hl_recs (hs_expected h'') = [].
Proof.
  intros c h h'' Ht.
  destruct (gx_touch_cost h h'' Ht) as (T1 & T0 & T3 & _).
  destruct Ht as (h' & E' & H' & P & g & A0 & ob & ds & cc & Hcnl & Hcshe).
  destruct (gx_cshe_perm P g A0 ob h' h'' ds cc Hcshe) as (H'' & E2 & _ & Hperm).
  destruct Hcnl as (E1 & _ & _ & _ & HndH' & HtH' & _).
  split; [|exact T3].
  cbn [pg_SQ].
  assert (Q3 : hs_held h'' = H'') by (rewrite E2; reflexivity).
  assert (Q5 : hs_held h' = H') by (rewrite E1; reflexivity).
  rewrite Q5 in Hperm.
  assert (Qs : slot_pend (Some h'') = slot_pend (Some h)) by (cbn [slot_pend]; rewrite T1, T0; reflexivity).
  assert (QE : texts (hs_expected h'') = []) by (unfold texts; rewrite T3; reflexivity).
  set (Ls := texts (hs_expected h)) in *.
  assert (W1 : pt_tc c (texts H'') <= pt_tc c (texts H')).
  { assert (P1 : Permutation (texts H') (texts H'' ++ map (fun r => bzs (snd r)) ds))
      by (unfold texts; rewrite <- map_app; apply Permutation_map; exact Hperm).
    unfold pt_tc. rewrite (fr_sum_perm _ (pt_w c) _ _ P1), map_app, zsum_app.
    pose proof (pt_tc_nonneg c (map (fun r => bzs (snd r)) ds)) as N. unfold pt_tc in N. lia. }
  assert (W2 : pt_tc c (texts H') <= pt_tc c (texts (hs_held h)) + pt_tc c (dr3_nk Ls)).
  { unfold pt_tc. pose proof HndH' as Hnd2. apply NoDup_ListNoDup in Hnd2.
    pose proof (pt_sum_incl (pt_w c) (texts H') (texts (hs_held h) ++ dr3_nk Ls)
                  (fun x => proj1 (pt_w_range c x)) Hnd2) as X.
    rewrite map_app, zsum_app in X. apply X. intros y Hy. apply in_or_app. rewrite HtH' in Hy.
    destruct (dr3_upds_in Ls _ y Hy) as [Hy'|Hy']; [left | right]; exact Hy'. }
  rewrite Qs, QE, Q3.
  assert (Z0 : pt_tc c (dr3_nk []) = 0) by reflexivity. rewrite Z0.
  pose proof (pt_s_ge c) as Hs.
  assert (M : pt_s c * (pt_tc c (texts H'') + 0) <=
              pt_s c * (pt_tc c (texts (hs_held h)) + pt_tc c (dr3_nk Ls)))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

Section pgn.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================== the potential, m against mc *)
Lemma pg_core : forall c cx t m hs qs c2 O2 cap2 out2 m1 mc A,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  gx_xpre m hs ->
  pt_s c * pt_kc c mc + pt_v c * pt_mass mc <= pt_s c * pt_kc c m + pt_v c * pt_mass m.
Proof.
  intros c cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hpairs Hafter Hrok Hrun HX.
  pose proof (gx_pf_all cx t m hs HRI Hpairs HX) as HPF.
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof Hpairs as (Hlh & HPok & HRS).
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (Hrr & Hlq & _ & Hfds).
  pose proof HRI as (_ & (Hl4 & _) & _).
  set (ps := combine (lm_es m) hs) in *.
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  (* ---- relay_instance_gone: the entries and the drained slots ---- *)
  pose proof (pg_rig c _ (lm_mx m) ps qs (lm_c m) (lm_O m) (lm_cap m) c2 O2 cap2 Hrr HPF) as R.
  assert (EA : zsum (map (pg_EP c) (lm_es m1)) = zsum (map (fun pq => pg_EP c (fst (snd pq))) (combine ps qs))).
  { rewrite A3, map_map, (gx_sum_csnd (fun q => pg_EP c (fst q)) ps qs Hlps). reflexivity. }
  assert (EB : zsum (map (pg_EP c) (lm_es m)) = zsum (map (fun pq => pg_EP c (fst (fst pq))) (combine ps qs))).
  { rewrite (gx_sum_cfst (pg_EP c) (lm_es m) hs ltac:(lia)). fold ps.
    rewrite (gx_sum_cfst (fun p => pg_EP c (fst p)) ps qs Hlps). reflexivity. }
  (* ---- the slots: only the drained ones change ---- *)
  set (F := fun j => pg_SQ c (nth j (lm_hs m1) None) - pg_SQ c (nth j (lm_hs m) None)).
  assert (S1 : zsum (map (pg_SQ c) (lm_hs m1)) - zsum (map (pg_SP c) (lm_hs m)) =
               F 0%nat + F 1%nat + F 2%nat + F 3%nat).
  { rewrite (gx_sum4 (pg_SQ c) (lm_hs m1) A11), (gx_sum4 (pg_SP c) (lm_hs m) Hl4).
    assert (R0 : forall j, (j < 4)%nat -> pg_SQ c (nth j (lm_hs m) None) = pg_SP c (nth j (lm_hs m) None)).
    { intros j Hj. destruct (nth j (lm_hs m) None) as [h|] eqn:Eh; [|exact (pg_SQ_SP_none c)].
      destruct (gx_rinv_slot cx t m j h HRI Hj Eh) as (Hexp & _). exact (pg_SQ_SP c h Hexp). }
    unfold F. rewrite (R0 0%nat), (R0 1%nat), (R0 2%nat), (R0 3%nat) by lia. lia. }
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
     zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then pg_SQ c (Some (snd (snd pq))) else 0) (combine ps qs)) -
     zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then pg_SQ c (Some (fst (snd (fst pq)))) else 0)
             (combine ps qs))).
  { rewrite <- gx_zsum_sub. apply (gx_sum_ext _ _ _ _ HPQ). intros [p q] Hpq. cbn [fst snd] in Hpq |- *.
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|lia].
    apply Z.eqb_eq in Eo. destruct (Hpq Eo) as (_ & Hm & Hm1).
    unfold F. rewrite Hm, Hm1. lia. }
  assert (HRIG : zsum (map (pg_EP c) (lm_es m1)) + zsum (map (pg_SQ c) (lm_hs m1)) <=
                 zsum (map (pg_EP c) (lm_es m)) + zsum (map (pg_SP c) (lm_hs m))).
  { clearbody F. lia. }
  (* ---- the loop: each slot of mc against m1's ---- *)
  assert (Hnd : List.NoDup (map re_fd (lm_es m1))) by (rewrite A3; apply NoDup_ListNoDup; exact Hfds).
  destruct (gx_run _ m1 mc A _ _ Hrun Hnd) as (R1 & _ & _ & _ & _ & R6 & Hhist & Hcov).
  assert (Hlc : length (lm_hs mc) = 4%nat) by lia.
  assert (Hslot : forall k', (k' < 4)%nat ->
            pg_SP c (nth k' (lm_hs mc) None) <= pg_SQ c (nth k' (lm_hs m1) None)).
  { intros k' Hk'.
    destruct (Hhist k') as [L | (h & h'' & i0 & X1 & X2 & X3 & _)].
    - rewrite L.
      destruct (gx_rig_slot cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX k' Hk')
        as [L2 | (e & h0 & h1 & cc & mx & no & cap & e1 & LB & i1 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
      + rewrite L2. destruct (nth k' (lm_hs m) None) as [h0|] eqn:Eh.
        * destruct (gx_rinv_slot cx t m k' h0 HRI Hk' Eh) as (Hexp & _). rewrite (pg_SQ_SP c h0 Hexp). lia.
        * rewrite pg_SQ_SP_none. lia.
      + rewrite Y2.
        assert (Hexp1 : hl_recs (hs_expected h1) = []).
        { apply (Hcov i1 k' h1); [lia | exact Y5 | exact Hk' | rewrite L; exact Y2 | symmetry; exact Y6]. }
        rewrite (pg_SQ_SP c h1 Hexp1). lia.
    - rewrite X2, X1. destruct (pg_touch c h h'' X3) as (T1 & T2). rewrite <- (pg_SQ_SP c h'' T2). exact T1. }
  assert (HLOOP : zsum (map (pg_SP c) (lm_hs mc)) <= zsum (map (pg_SQ c) (lm_hs m1))).
  { rewrite (gx_sum4 (pg_SP c) (lm_hs mc) Hlc), (gx_sum4 (pg_SQ c) (lm_hs m1) A11).
    pose proof (Hslot 0%nat ltac:(lia)). pose proof (Hslot 1%nat ltac:(lia)).
    pose proof (Hslot 2%nat ltac:(lia)). pose proof (Hslot 3%nat ltac:(lia)). lia. }
  rewrite (pg_split c mc), (pg_split c m), R1. lia.
Qed.

(* ================================================================== GN_RI_end's fr_POT *)
(* fr_POT kept over the gone operation: ReplyLS3oGn.v fr_OUT_gone_end's premises in its order, with
   fr_OUT OM cx t m ly S replaced by fr_POT cx t m; fr_LS3 B cx t m ly S and the block-permutation premise dropped
   (not used).  No extra hypothesis, no REQ5. *)
Lemma fr_POT_gone_end : forall cx t m (ly : alayout) (S : astate) hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout)
    (Sx : astate),
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
  fr_POT cx t m ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  fr_POT cx (t + 1) mc.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx HRI Hop HE Hcap HE6 HS6 HPOT Hpairs Hafter Hrok Hrun.
  pose proof (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hpairs) as HX.
  apply (fr_POT_step cx t (t + 1) m mc); [intros c | exact HPOT].
  pose proof (pg_core c cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hpairs Hafter Hrok Hrun HX) as H.
  pose proof (pt_wm_nonneg c (t + 1 - t) ltac:(lia)) as W.
  lia.
Qed.
End pgn.
