(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v, with its module paths and module names changed; 559 of its 679 lines of code are new or changed and 474 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) port of the rules of lib/A/ReplyLS3o.v (sha256
   385bcddd64a1; internal record) at d9e8f914caaf (the same blob as at 1b1e21bdbd40),
   row G-BLS3-port, over lib/B/ReplyLSBo.v's fr_OUT (B has ONE fr_OUT: `fr_OUT OM cx t m ly S`, ReplyLSBo.v :138).
   proves no function (kind: invariant lemma).
   WHAT IS ALREADY AT B (not restated here), A name -> lib/B name:
     ReplyLSBo.v: OUT_MAX3, OUT_MAX4, WMAX, OUT_MAX3_src, OUT_MAX4_src, kw7, kw7s, kw7_nonneg, kw7s_nonneg,
       ou_gesture_begin_key, ou_keys_total_kw7, ent_mass, ent_mass_nonneg, ou_keys_total_mass, MASSe, MASS,
       MASSe_nonneg, MASS_nonneg, XB, fr_OUT, fr_OUT_keep, fr_OUT_k_only (same names); xb_perm -> bo_xb_perm,
       xb_same_rest -> bo_xb_same_rest, fr_OUT_head_nout -> fr_OUT_head_nout_b, fr_OUT_head_skip -> fr_OUT_head_skip_b,
       fr_OUT_pro -> fr_OUT_pro_b (premise `0 <= OM` for A's HOM), ou_ev_len -> bo_ev_len, fr_OUT_event_step_p ->
       fr_OUT_event_step_b (without A's unused fr_LS3 premise; `131072 <= OM` for A's HOM);
     ReplyLSBoRf.v: kw5s, kw5s_nil, kw5s_cons, kw5s_nonneg, kw5s_keys, rf_sum, rf_sum_nil, rf_sum_cons, rf_sum_nonneg,
       rf_sum_mass, ou_sl_cap_ge, ou_ge_cap_ge, ou_ge_cap_le, ou_ge_no, ou_gse_cap (same names);
     A's Ltac ou_perm: lib/B/ReplyB3LS3Arms.v ls3_perm (the same text).
   PORTED HERE, A's names and statements: WMAX_src, kw7s_app, kw7s_perm, kw7s_filter, kw7s_incl, kw7s_upd, kw7s_upds,
     kw7s_nk, MASSe_in, pend_bytes_in, ou_wit_gest511, ou_mass_bound, ou_mass_bound2, fr_OUT_upd, fr_OUT_close,
     fr_OUT_eintr, fr_OUT_sendmax, fr_OUT_default, fr_OUT_write_skip, fr_OUT_add_none, fr_OUT_add_open, ou_wr_n_le,
     fr_OUT_write_push, ou_rm_keys, fr_OUT_drain_step_p, ou_rm_cap2, fr_OUT_rm_step_p, fr_OUT_pro_c, fr_OUT_sat_state,
     fr_LS3c_OUT_sat, ou_rf_cap, fr_live_post3, ou_exit_bytes, LS_exit_end3, LS_exit_end3_x.
   A -> B SWAPS (as lib/B/ReplyB3LS3.v / ReplyB3LS3c.v / ReplyB3LS3Arms.v make them):
   - the Require header is ReplyB3LS3cArms.v's plus lib/B ReplyLSBo / ReplyLSBoRf (fr_OUT and its helpers), lib/B
     W_bx_defs (the exit's lx_rf_run / lx_exit_cost, which lib/B/W_LLVMFuzzerTestOneInput_exit.v reads from there;
     Required, not Imported) and lib/B W_journal_x (ajournal_gx_x, Required); lib/B ReplyLSBArms is Imported before
     the B arm files so that wr_pick / wr_n / wr_k2 / wr_x are lib/B/W_LLVMFuzzerTestOneInput_write.v's, the ones
     ReplyB3LS3.v's write rules read (ReplyLSBArms.v keeps copies of them);
   - fr_LS3 B -> fr_LS3 B CALL_ROOM_B, fr_LS3c B -> fr_LS3c B CALL_ROOM_B: the Sections take CALL_ROOM_B after B;
     fr_OUT cx -> fr_OUT OM cx (ReplyLSBo's fr_OUT takes OM first); A's Section hypothesis HOM : OUT_MAX4 <= OM kept;
   - A's dr3_* / rm3_* / ls3_* / fr_remove_perm facts are lib/B/ReplyB3LS3Arms.v's (A names), rm3_pair / rm3_no_fin /
     rm3_nth_lt / fr_sum_perm lib/B/ReplyLSBDrainPre.v's; A's ev3_bsum_aout_eq is ReplyLSBArms.v bt_bsum_aout_eq;
   - fr_OUT_pro_c: its lf_base premise in lib/B/ReplyB3LS3c.v fr_LS3c_pro's form (the meter quantified, fr_live_pre
     `fun S0 => blocks_bytes S0 + CALL_ROOM_B <= LIVE_MAX`); fr_LS3c_OUT_sat: at CALL_ROOM_B := YCfn_cf.CALL_ROOM_B;
   - the exit: W_LLVMFuzzerTestOneInput_exit.lx_rf_run / lx_exit_cost -> W_bx_defs.lx_rf_run / lx_exit_cost
     (lib/B/W_bx_defs.v :154, :273; lx_exit_cost takes the meter first, as lib/B/W_LLVMFuzzerTestOneInput_exit.v
     :172 reads it); LLVMF_STK := YCfn.LLVMF_STK (as lib/B/W_LLVMFuzzerTestOneInput_exit_x.v
     :78).  fr_live_post3 at OM := YCfn_cf.OUT_MAX (= OUT_MAX4, lib/B/YCfn_cf.v :49) is YCfn_cf.fr_live_post_b's text;
   - KF-COUNT (the meter pattern of a Theorem Labs lane, A #6; A's ReplyLS3e.v LS_exit_end3e the same): A's
     MT := ameter_triv -> Section oexit's Context {MT : ameter_ops}, implicit (read off the exit rules' mo_le
     argument, which no proof reads).  LS_exit_end3 / LS_exit_end3_x no longer conclude the exit's meter conjunct
     `mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx))` (proved by `exact I` at ameter_triv; the B
     instance's, from its count clause), so the Section variable XN_LIB is gone.
   A's header follows. *)
(* The out-buffer half of LS v3 (row B1c, a Theorem Labs lane): fr_OUT, the conjunct that bounds g_capout, its twin of
   every rule that ends in fr_LS3c (lib/A/ReplyLS3c.v, lib/A/ReplyLS3cArms.v), and the exit obligations
   LS_exit_end restated over it (LS_rf_room's peak form is lib/A/ReplyLS3oRf.v).  proves no function (kind:
   invariant lemma).

   OUT_MAX4 = 133,953,540 = 4 * (OPS_MAX - 1) * 65,535 is a Theorem Labs lane's ruling of 2026-10-30 01:47Z, after this row
   found that a8's 66,976,770 is still too small.  WHY: relay_remove drains the source FIRST and then ends the
   gestures of the entry the drain left (rm_rr_ok: `dr_rel ... e1 h1 LB` then
   `sl_sends mx c1 O1 cap1 (ge_bytes (re_keys e1))`; relay.c:463-465), so the begin lines AND the end lines of the
   keys those same begin lines made go out in ONE operation.

   fr_OUT (the e0-free form a Theorem Labs lane accepted at 00:59Z / 01:02Z):
     0 <= lm_cap m /\ 0 <= XB /\ lm_cap m <= XB + OM /\ MASS m <= 65535 * t,
   XB cx m S := blocks_bytes (c_S cx) - blocks_bytes S + bsum (model_blks m), and
     MASS m := sum over the relay's entries of (|re_U e| + sum over its keys of (|key| + 7)) + pend_bytes m,
   the bytes one operation may still send.  MASS counts a held key at |key| + 7 = the cost of the BEGIN line that
   made it (ou_gesture_begin_key).  Every rule keeps MASS except the write, which adds at most one fuzz_take of
   65,535 bytes; so one operation sends at most 2 * MASS <= 2 * 65,535 * t bytes and a send grows g_capout to at
   most 2 * (g_nout + len), whence 4 * 65,535 * 511 = OUT_MAX4 at t < OPS_MAX. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF drain_b_c send_line_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads
  SlotInv SlotDrain3Aux SlotPass2Aux relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
(* ReplyLSBArms before the arm files: the write arm's names below are W_LLVMFuzzerTestOneInput_write.v's *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3Base ReplyB3LS3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3Arms ReplyB3LSCntL ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBo ReplyLSBoRf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_bx_defs W_journal_x.
Import ListNotations.
(* the remove arm notions lib/B/ReplyLSBArms.v copied are lib/B's arm files' (s5-r1d's cutover; ev_* stay
   ReplyLSBArms's until an internal work row, a Theorem Labs lane 08:09Z), pinned here *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
Local Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== the constants (A :98-111) *)
Lemma WMAX_src : WMAX = SlotInv.WRITE_MAX.
Proof. reflexivity. Qed.

(* ================================================================== the key model (A :139-194) *)
Lemma kw7s_app : forall A C, kw7s (A ++ C) = kw7s A + kw7s C.
Proof. intros A C. unfold kw7s. rewrite map_app. apply zsum_app. Qed.
Lemma kw7s_perm : forall A C, Permutation A C -> kw7s A = kw7s C.
Proof. intros A C H. unfold kw7s. induction H; cbn [map fold_right]; lia. Qed.
Lemma kw7s_filter : forall (p : list Z -> bool) T, kw7s (List.filter p T) <= kw7s T.
Proof.
  intros p T. unfold kw7s. induction T as [|x T IH]; [cbn; lia|]. cbn [List.filter].
  pose proof (kw7_nonneg x). destruct (p x); cbn [map fold_right]; lia.
Qed.
Lemma kw7s_incl : forall A C, List.NoDup A -> incl A C -> kw7s A <= kw7s C.
Proof.
  induction A as [|a A IH]; intros C Hnd Hinc; [cbn [kw7s map fold_right]; apply kw7s_nonneg|].
  apply NoDup_cons_iff in Hnd as [Ha Hnd].
  assert (Hin : In a C) by (apply Hinc; left; reflexivity).
  destruct (in_split _ _ Hin) as (l1 & l2 & ->).
  assert (Hi : incl A (l1 ++ l2)).
  { intros x Hx. assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hinc; right; exact Hx).
    apply in_app_iff in Hx' as [H1 | [H2 | H3]]; apply in_app_iff;
      [left; exact H1 | subst x; contradiction | right; exact H3]. }
  specialize (IH (l1 ++ l2) Hnd Hi).
  rewrite (kw7s_perm (l1 ++ a :: l2) (a :: l1 ++ l2) (Permutation_sym (Permutation_middle l1 l2 a))).
  unfold kw7s in *. cbn [map fold_right]. lia.
Qed.
(* one relayed line adds at most its own cost (its bytes and its NUL) to the key weights *)
Lemma kw7s_upd : forall T l, kw7s (upd T l) <= kw7s T + (Z.of_nat (length l) + 1).
Proof.
  intros T l. unfold upd. destruct (gesture l) as [[[|] x]|] eqn:G.
  - destruct (existsb (list_eqb x) T); [pose proof (kw7_nonneg x); unfold kw7 in *; lia|].
    rewrite kw7s_app. pose proof (ou_gesture_begin_key l x G).
    unfold kw7s, kw7. cbn [map fold_right]. lia.
  - pose proof (kw7s_filter (fun y => negb (list_eqb x y)) T). lia.
  - lia.
Qed.
Lemma kw7s_upds : forall ls T, kw7s (upds T ls) <= kw7s T + Z.of_nat (length (with_nul ls)).
Proof.
  induction ls as [|l ls IH]; intros T.
  - unfold upds. cbn [fold_left]. rewrite RelayCap.with_nul_nil_len. lia.
  - unfold upds in *. cbn [fold_left]. rewrite RelayCap.with_nul_cons_len.
    pose proof (IH (upd T l)). pose proof (kw7s_upd T l). lia.
Qed.
(* the keys a drain's lines can add (ReplyB3LS3Arms.v dr3_nk), by weight *)
Lemma kw7s_nk : forall Ls, kw7s (dr3_nk Ls) <= Z.of_nat (length (with_nul Ls)).
Proof.
  induction Ls as [|l Ls IH]; [unfold dr3_nk; cbn; lia|].
  unfold dr3_nk in *. cbn [map concat]. rewrite kw7s_app, RelayCap.with_nul_cons_len.
  assert (Hb : kw7s (dr3_bk l) <= Z.of_nat (length l) + 1).
  { unfold dr3_bk. destruct (gesture l) as [[[|] x]|] eqn:G.
    - pose proof (ou_gesture_begin_key l x G). unfold kw7s, kw7. cbn [map fold_right]. lia.
    - unfold kw7s. cbn [map fold_right]. lia.
    - unfold kw7s. cbn [map fold_right]. lia. }
  lia.
Qed.

(* ================================================================== MASS (A :218-221) *)
Lemma MASSe_in : forall es e, In e es -> ent_mass e <= MASSe es.
Proof. intros es e H. apply (dr3_sum_in ent_mass es e ent_mass_nonneg H). Qed.
Lemma pend_bytes_in : forall m o, In o (lm_hs m) -> slot_pend o <= pend_bytes m.
Proof. intros m o H. apply (dr3_sum_in slot_pend (lm_hs m) o slot_pend_nonneg H). Qed.

(* ================================================================== the growth law, and b1's measured witness *)
(* the MEASURED witnesses (b1-RECHECK.md (sha256 2d07c55f9e3f; internal record) Part 2): gest511_rm.bin leaves
   g_nout = 66,962,805 and g_capout = 98,303,538; the model's law makes the last growth (g_nout + len) * 2 from b1's
   capacity 49,148,190, at the split 49,151,764 + 5 of the measured sum (A :229-244) *)
Lemma ou_wit_gest511 :
  send_line_b_c.send_line_cap true 0 49151764 49148190 5 = 98303538 /\
  66962805 <= 98303538 /\ OUT_MAX3 < 98303538 <= OUT_MAX4.
Proof.
  assert (E : send_line_b_c.send_line_cap true 0 49151764 49148190 5 = 98303538) by (vm_compute; reflexivity).
  unfold OUT_MAX3, OUT_MAX4. repeat split; lia.
Qed.
(* one operation's output is at most 2 * MASS, and a send leaves at most twice it *)
Lemma ou_mass_bound : forall t, 0 <= t < OPS_MAX -> 4 * (WMAX * t) <= OUT_MAX4.
Proof. intros t Ht. unfold OUT_MAX4, WMAX, OPS_MAX in *. lia. Qed.
Lemma ou_mass_bound2 : forall t, 0 <= t <= OPS_MAX -> 2 * (WMAX * t) <= OUT_MAX4.
Proof. intros t Ht. unfold OUT_MAX4, WMAX, OPS_MAX in *. lia. Qed.

(* ================================================================== fr_OUT's rules (A :259-838) *)
Section ou.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the call room of fr_LS3 (ReplyB3LS3.v, as ReplyLSB.fr_LS takes it) *)
Variable CALL_ROOM_B : Z.
(* the out-buffer bound the contract carries; every lemma below is at any OM at least a Theorem Labs lane's ruled value *)
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.

(* ---------------------------------------------------------------- the keep rules (A :313-323) *)
Lemma fr_OUT_upd : forall cx t t' m m' ly S i f,
  lm_hs m' = upd_hs i f (lm_hs m) -> (forall h, asrc_blks (f h) = asrc_blks h) ->
  (forall h, slot_pend (Some (f h)) = slot_pend (Some h)) ->
  lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  t <= t' -> fr_OUT OM cx t m ly S -> fr_OUT OM cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S i f E1 Hfb Hfp E2 E3 E4 E5 Ht H.
  apply (fr_OUT_keep OM cx t t' m m' ly S); [| exact E4 | | exact Ht | exact H].
  - unfold model_blks. rewrite E1, E2, E3, E4, E5, (upd_hs_blks i f (lm_hs m) Hfb). reflexivity.
  - unfold MASS, MASSe, pend_bytes. rewrite E1, E2, (upd_hs_map slot_pend i f (lm_hs m) Hfp). lia.
Qed.

(* ---------------------------------------------------------------- the rules of ReplyLS3c.v (A :331-348) *)
Lemma fr_OUT_close : forall cx t m i ly S, fr_OUT OM cx t m ly S -> fr_OUT OM cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S H. apply (fr_OUT_upd cx t (t + 1) m _ ly S i upd_closed);
    try reflexivity; try (intros h; reflexivity); try lia; exact H.
Qed.
Lemma fr_OUT_eintr : forall cx t m i ly S, fr_OUT OM cx t m ly S -> fr_OUT OM cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S H. apply (fr_OUT_upd cx t (t + 1) m _ ly S i upd_eintr);
    try reflexivity; try (intros h; reflexivity); try lia; exact H.
Qed.
Lemma fr_OUT_sendmax : forall cx t m u ly S,
  fr_OUT OM cx t m ly S -> fr_OUT OM cx (t + 1) (sm_sendmax cx m u) ly S.
Proof. intros cx t m u ly S H. apply (fr_OUT_k_only OM cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_default : forall cx t m g ly S,
  fr_OUT OM cx t m ly S -> fr_OUT OM cx (t + 1) (sm_default cx m g) ly S.
Proof. intros cx t m g ly S H. apply (fr_OUT_k_only OM cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_write_skip : forall cx t m ly S,
  fr_OUT OM cx t m ly S -> fr_OUT OM cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof. intros cx t m ly S H. apply (fr_OUT_k_only OM cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_add_none : forall cx t m ly S, fr_OUT OM cx t m ly S -> fr_OUT OM cx (t + 1) (ad_none m) ly S.
Proof. intros cx t m ly S H. apply (fr_OUT_k_only OM cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.

(* op_add's open: the new partial buffer is a model block, so XB is unchanged; the new entry and the new source
   carry no mass (A :350-376) *)
Lemma fr_OUT_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3 B CALL_ROOM_B cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_OUT OM cx t m ly S -> fr_OUT OM cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' H1 Hf HP' (O1 & O2 & O3 & O4).
  destruct H1 as (rest & e0 & HP & _ & _ & _ & Hl & _).
  destruct (oa_first_free (lm_hs m) i Hl Hf) as (Hi4 & Hi).
  pose proof (model_perm_add m i q pj ev Hi) as Hm.
  set (m' := ad_open m i q pj ev) in *.
  assert (EB : blocks_bytes S' = blocks_bytes S + APARTIAL).
  { rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP'), bsum_cons, <- (blocks_bytes_bsum B ly S).
    cbn [snd]. lia. }
  assert (EM : bsum (model_blks m') = bsum (model_blks m) + APARTIAL)
    by (rewrite (bsum_perm _ _ Hm), bsum_cons; cbn [snd]; lia).
  assert (EC : lm_cap m' = lm_cap m) by reflexivity.
  assert (EX : XB cx m' S' = XB cx m S) by (unfold XB; rewrite EB, EM; lia).
  assert (EMass : MASS m' <= MASS m).
  { unfold MASS, MASSe, pend_bytes, m'. rewrite ad_open_hs, ad_open_es, map_app, zsum_app.
    assert (Z0 : zsum (map ent_mass [ra_new (100 + lm_nfd m)]) = 0) by reflexivity.
    pose proof (set_nth_zsum slot_pend i (Some (oa_new_src (100 + lm_nfd m) q pj)) None (lm_hs m) Hi) as Zs.
    assert (P4 : slot_pend (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (N4 : slot_pend None = 0) by reflexivity. rewrite Z0. lia. }
  unfold fr_OUT in *. rewrite EC, EX. unfold WMAX in *. repeat split; try lia.
Qed.

(* ---------------------------------------------------------------- the write arm's push (A :378-466) *)
(* wr_n is one fuzz_take of fuzz_u16 bytes: at most 65,535 *)
Lemma ou_wr_n_le : forall cx m, wr_n cx m <= WMAX.
Proof.
  intros cx m. unfold wr_n, wr_u, WMAX.
  pose proof (in_byte_range cx (wr_k1 cx m)). pose proof (in_byte_range cx (wr_k1 cx m + 1)).
  destruct (2 <=? wr_rem cx m), (wr_rem cx m =? 1); lia.
Qed.
Lemma fr_OUT_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
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
  fr_OUT OM cx t m ly S -> fr_OUT OM cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ly S ly' S' ev H1 Hpk Hn Hrecs Hcap Hv Hlp (O1 & O2 & O3 & O4).
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
  { unfold model_blks, m'. cbn [wr_push lm_G lm_es lm_hs lm_cap lm_out]. ls3_perm. }
  assert (Hsplit : exists mm, Permutation (model_blks m) (OV ++ mm)).
  { destruct (lp_grow l && negb (hl_cap l =? 0)) eqn:Eg; unfold OV; try rewrite Eg; cbv beta iota.
    - assert (Hin : In (hl_v l, AREC * hl_cap l) (model_blks m)).
      { apply andb_true_iff in Eg as (_ & E). apply negb_true_iff in E. unfold model_blks.
        right. apply in_app_iff. right. apply in_app_iff. left. apply in_concat.
        exists (slot_blks (Some h)). split; [apply in_map; exact (nth_error_In _ _ Hi)|].
        cbn [slot_blks]. rewrite Ha. right. apply in_app_iff. left. apply in_app_iff. left.
        unfold VL. rewrite E. left. reflexivity. }
      destruct (in_split _ _ Hin) as (l1 & l2 & E). exists (l1 ++ l2). rewrite E. ls3_perm.
    - exists (model_blks m). apply Permutation_refl. }
  destruct Hsplit as (mm & Hmm).
  assert (HP1 : Permutation (ablocks B ly S) (OV ++ (input_blks cx ++ mm ++ rest))) by ls3_perm.
  pose proof (Hlp _ HP1) as HP2. fold x dd NV in HP2.
  (* the live bytes and the model's bytes move by the same amount *)
  assert (EB : blocks_bytes S' + bsum OV = blocks_bytes S + bsum NV + bsum [dd]).
  { rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP2), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP1),
      !bsum_cons, !bsum_app. cbn [snd]. unfold dd, bsum. cbn [fold_right map snd]. lia. }
  assert (EM : bsum (model_blks m') + bsum OV = bsum (model_blks m) + bsum NV + bsum [dd])
    by (pose proof (bsum_perm _ _ HM2) as PM; rewrite !bsum_app in PM; lia).
  assert (EX : XB cx m' S' = XB cx m S) by (unfold XB; lia).
  assert (EC : lm_cap m' = lm_cap m) by reflexivity.
  assert (EMass : MASS m' <= MASS m + WMAX).
  { unfold MASS, MASSe, pend_bytes, m'. cbn [wr_push lm_es lm_hs].
    pose proof (set_nth_zsum slot_pend si (Some h') (Some h) (lm_hs m) Hi) as Zs.
    assert (Hb : hl_bytes l' = hl_bytes l + Z.of_nat (length x)).
    { unfold hl_bytes. rewrite Hrecs, map_app, zsum_app. cbn [map fold_right snd]. lia. }
    assert (Hp' : slot_pend (Some h') <= slot_pend (Some h) + Z.of_nat (length x)).
    { cbn [slot_pend h' set_pending hs_pending hs_off]. fold l. rewrite Hb. lia. }
    assert (Hx : Z.of_nat (length x) <= WMAX).
    { unfold x, wr_x. rewrite length_firstn.
      pose proof (ou_wr_n_le cx m). pose proof (Z2Nat.id (wr_n cx m)). unfold WMAX in *. lia. }
    lia. }
  unfold fr_OUT in *. rewrite EC, EX. unfold WMAX in *. repeat split; try lia.
Qed.

(* ---------------------------------------------------------------- the remove arm's step (A :499-515) *)
(* the END lines of the entry's keys after the drain: at most the entry's key weight and the lines it relayed; a
   relayed begin line is counted ONCE (the key weight kw7 is the begin line's own cost) *)
Lemma ou_rm_keys : forall e e1 Ls,
  List.NoDup (drain_b_c.keys_texts (re_keys e1)) ->
  (forall y, In y (drain_b_c.keys_texts (re_keys e1)) -> In y (upds (drain_b_c.keys_texts (re_keys e)) Ls)) ->
  gestures_end_b_c.keys_total (re_keys e1) <=
    kw7s (drain_b_c.keys_texts (re_keys e)) + Z.of_nat (length (with_nul Ls)).
Proof.
  intros e e1 Ls Hnd Hin.
  pose proof (ou_keys_total_kw7 (re_keys e1)) as H1.
  assert (H2 : kw7s (drain_b_c.keys_texts (re_keys e1)) <=
               kw7s (upds (drain_b_c.keys_texts (re_keys e)) Ls))
    by (apply kw7s_incl; [exact Hnd | exact Hin]).
  pose proof (kw7s_upds Ls (drain_b_c.keys_texts (re_keys e))) as H3.
  lia.
Qed.

(* ---------------------------------------------------------------- the drain arm's step (A :517-644) *)
(* Hcap0' (0 <= cap') is dr_post's aout_at; Ht is the arm's cut (lregs_D, `0 <= t < OPS_MAX`) *)
Lemma fr_OUT_drain_step_p : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B CALL_ROOM_B cx t m ly S -> fr_OUT OM cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> fr_RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) -> dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 -> ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  0 <= cap' -> 0 <= t < OPS_MAX ->
  fr_OUT OM cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HLS (U1 & U2 & U3 & U4) Hpick Hj
    (rest_d & HPd1 & HPd2) Hpend HEq HHq Hcnl Hh'' Hat HRI Hfd Heof Hepre Hkh Hhpre Hhn Hcap0 Hcap'
    Hepost Hhpost Hdpost Hcpost Hcapn Ht.
  subst E H h''.
  pose proof Hpick as (_ & Hsi & Hh).
  destruct Hat as (Hk & HO & _).
  set (e := nth j (lm_es m) dr_e0) in *.
  set (h'' := set_exp_held h1 E' H') in *.
  set (m' := dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') in *.
  assert (Hej : nth_error (lm_es m) j = Some e) by (unfold e; apply nth_error_nth'; exact Hj).
  pose proof (nth_some_error _ _ _ Hh) as Hhi.
  destruct Hdpost as (HU' & Hka' & Hoff1 & Hmap & Hheld & HnE1).
  replace (Z.of_nat (length (lm_O m))) with 0 in Hcap', HU', Hka' by (rewrite HO; reflexivity).
  unfold dr_fin in HU', Hka'. fold e in HU', Hka'.
  (* ---- XB is unchanged: the live bytes and the model's bytes move by the same amount ---- *)
  assert (LB : forall l, list_blks l = alist_blks l) by reflexivity.
  assert (Ha1 : asrc_blks h1 = (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++
                               alist_blks (hs_expected h1) ++ alist_blks (hs_held h1)) by reflexivity.
  assert (Ha'' : asrc_blks h'' = (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++
                                 alist_blks E' ++ alist_blks H') by reflexivity.
  pose proof (Hcnl ((hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ aentry_blks e' ++
                    aout_blks cap' out' ++ rest_d)) as HP3.
  rewrite !LB in HP3.
  assert (HP2' : Permutation (ablocks B ly1 S1) (alist_blks (hs_expected h1) ++ alist_blks (hs_held h1) ++
                   (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1) ++ aentry_blks e' ++ aout_blks cap' out' ++
                   rest_d)).
  { rewrite Ha1 in HPd2. clear - HPd2. ls3_perm. }
  specialize (HP3 HP2'). clear HP2'.
  pose proof (dr3_dset_perm aentry_blks j e' e (lm_es m) Hej) as PA.
  pose proof (dr3_dset_perm slot_blks si (Some h'') (Some h) (lm_hs m) Hhi) as PS.
  change (slot_blks (Some h'')) with (asrc_blks h'') in PS. change (slot_blks (Some h)) with (asrc_blks h) in PS.
  assert (Bm : bsum (model_blks m') + bsum (aentry_blks e) + bsum (asrc_blks h) +
                 bsum (aout_blks (lm_cap m) (lm_out m)) =
               bsum (model_blks m) + bsum (aentry_blks e') + bsum (asrc_blks h'') + bsum (aout_blks cap' out')).
  { pose proof (bsum_perm _ _ PA) as BA. pose proof (bsum_perm _ _ PS) as BS. rewrite ?bsum_app in BA, BS.
    unfold model_blks, m'. cbn [dr_step lm_G lm_es lm_hs lm_cap lm_out]. rewrite ?bsum_cons, ?bsum_app.
    cbn [snd]. lia. }
  assert (EBS : blocks_bytes S = bsum (aentry_blks e) + bsum (asrc_blks h) +
                                 bsum (aout_blks (lm_cap m) (lm_out m)) + bsum rest_d)
    by (rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPd1), ?bsum_app; lia).
  assert (EA'' : bsum (asrc_blks h'') = APARTIAL + bsum (alist_blks (hs_pending h1)) +
                                        bsum (list_blks E') + bsum (list_blks H'))
    by (unfold h''; rewrite (dr3_bsum_asrc (set_exp_held h1 E' H')); reflexivity).
  assert (EBS' : blocks_bytes S' = bsum (asrc_blks h'') + bsum (aentry_blks e') +
                                   bsum (aout_blks cap' out') + bsum rest_d).
  { rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP3), EA''.
    repeat progress (rewrite ?bsum_app, ?bsum_cons). cbn [snd]. lia. }
  assert (EX : XB cx m' S' = XB cx m S) by (unfold XB; lia).
  (* ---- the relay's run: what the drain sends is within the pair's mass ---- *)
  destruct (dr3_rinv cx t m si h j HRI Hpick Hj Hfd Heof)
    as ((Hsk & HskU) & Hsk01 & _ & _ & Hexp & _ & _ & _ & Hoff & _).
  destruct Hepre as (Hce & HU & HUz & Hkh8 & H14).
  destruct Hepost as (Hce' & Hkh' & Hnd' & Hss').
  set (Ls := dr_lines h) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))) in *.
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  assert (Hkh168 : 168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e).
  { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & E2) | (E1 & E2)].
    - rewrite E1, E2. cbn [length Z.of_nat Z.eqb]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live (lm_c m) h) (lm_mx m) 0 (lm_cap m) e h HJ
                (dr3_pok 0 (lm_cap m) e h Hoff Hhpre) Hce0) as Hno.
  change (lines (hs_state h) (bzs (pending_stream h))) with Ls in Hno. fold TOT in Hno.
  destruct (ls3_drain_fin (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) e h (proj1 Hhpre) Hkh168) as (RM & RK).
  rewrite <- HU' in RM. rewrite SlotReads.bzs_length in RM.
  assert (HMASS : TOT + Z.of_nat (length (re_U e')) <=
                  Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h))) by lia.
  (* the pair's mass is within the model's *)
  assert (He_in : In e (lm_es m)) by (unfold e; apply nth_In; exact Hj).
  assert (Hh_in : In (Some h) (lm_hs m)) by (rewrite <- Hh; apply nth_In; exact (rm3_nth_lt _ _ _ Hh)).
  pose proof (MASSe_in (lm_es m) e He_in) as Hem.
  pose proof (pend_bytes_in m (Some h) Hh_in) as Hpm.
  assert (HPS : Z.of_nat (length (pending_stream h)) = slot_pend (Some h)) by exact (ls3_ps_sp h (proj1 Hhpre)).
  pose proof (kw7s_nonneg (drain_b_c.keys_texts (re_keys e))) as Hkw0.
  assert (HUm : Z.of_nat (length (re_U e)) <= ent_mass e) by (unfold ent_mass; lia).
  (* ---- the capacity ---- *)
  assert (HTOTm : 2 * TOT <= 2 * MASS m).
  { unfold MASS. pose proof (MASSe_nonneg (lm_es m)). lia. }
  assert (Hcapb : cap' <= Z.max (lm_cap m) (2 * MASS m)).
  { pose proof (dr3_ocap (lm_c m) (lm_mx m) (lm_cap m) e h HJ (dr3_pok 0 (lm_cap m) e h Hoff Hhpre) Hce0) as Ho.
    fold Ls in Ho. fold TOT in Ho.
    rewrite Hcap'. destruct (dr_live (lm_c m) h); lia. }
  (* ---- the mass ---- *)
  assert (EMass : MASS m' <= MASS m).
  { unfold MASS, MASSe, pend_bytes, m'. cbn [dr_step lm_es lm_hs].
    pose proof (dr3_dset_zsum ent_mass j e' e (lm_es m) Hej) as Ze.
    pose proof (dr3_dset_zsum slot_pend si (Some h'') (Some h) (lm_hs m) Hhi) as Zp.
    assert (Ep'' : slot_pend (Some h'') = 0).
    { cbn [slot_pend]. unfold h''. cbn [set_exp_held hs_pending hs_off]. unfold hl_bytes.
      rewrite Hpend, Hoff1. cbn [map fold_right]. lia. }
    assert (Eme' : ent_mass e' <= ent_mass e + Z.of_nat (length (pending_stream h))).
    { unfold ent_mass.
      pose proof (kw7s_incl (drain_b_c.keys_texts (re_keys e'))
                    (upds (drain_b_c.keys_texts (re_keys e)) Ls)
                    (proj1 (NoDup_ListNoDup _) Hnd') (fun y Hy => proj1 (Hss' y) Hy)) as K1.
      pose proof (kw7s_upds Ls (drain_b_c.keys_texts (re_keys e))) as K2. fold TOT in K2. lia. }
    rewrite HPS in Eme'. lia. }
  assert (ECap : lm_cap m' = cap') by reflexivity.
  unfold fr_OUT in *. rewrite EX, ECap. unfold WMAX, OUT_MAX4, OPS_MAX in *. repeat split; try lia.
Qed.

(* ---------------------------------------------------------------- the remove arm's step (A :646-771) *)
(* g_capout after relay_remove, SHARPLY: ReplyB3LS3Arms.v ls3_rm_cap2's proof with the key weight kw7 in place of
   its "2 per relayed byte", so a begin line relayed in this operation pays for its own END line ONCE *)
Lemma ou_rm_cap2 : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  cap2 <= Z.max (lm_cap m) (2 * (2 * ent_mass (rm_ent m j0) + 2 * Z.of_nat (length (pending_stream h)))).
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr.
  pose proof Hat as (_ & HO & _ & _ & Hsi & Hh & Hj0 & _).
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & HC & Hcn).
  destruct HP as (_ & _ & _ & HP4 & HP5 & HP6 & HP7 & HP8 & HP9 & _ & HP11).
  cbn [fst snd] in HP4, HP5, HP6, HP7, HP8, HP9, HP11.
  destruct HE as (_ & _ & _ & HEnd & HEsk).
  unfold rm_rr_ok in Hrr. cbv zeta in Hrr. rewrite HO in Hrr. change (Z.of_nat (length (@nil byte))) with 0 in Hrr.
  set (e := rm_ent m j0) in *.
  set (U := Z.of_nat (length (re_U e))) in *.
  set (PS := Z.of_nat (length (pending_stream h))) in *.
  set (KW := kw7s (drain_b_c.keys_texts (re_keys e))) in *.
  assert (HU0 : 0 <= U) by (unfold U; lia).
  assert (HPS0 : 0 <= PS) by (unfold PS; lia).
  assert (HKW0 : 0 <= KW) by (unfold KW; apply kw7s_nonneg).
  assert (HM : ent_mass e = U + KW) by reflexivity.
  set (X := if re_skip e =? 0 then U else 0) in *.
  assert (EX : X = if re_skip e =? 0 then U else 0) by reflexivity.
  clearbody X.
  assert (HX0 : 0 <= X) by (rewrite EX; destruct (re_skip e =? 0); cbv iota; lia).
  assert (HXu : X <= U) by (rewrite EX; destruct (re_skip e =? 0); cbv iota; lia).
  assert (HXs : re_skip e = 0 -> X = U) by (intros E; rewrite EX, E; reflexivity).
  assert (HXs1 : re_skip e = 1 -> X = 0) by (intros E; rewrite EX, E; reflexivity).
  clear EX.
  remember (X + PS) as P eqn:EP.
  assert (HNF : forall live mx CAP, drain_b_c.ds_no (drain_b_c.drain_fin live mx 0 CAP e h) <= P).
  { intros live mx CAP. pose proof (rm3_no_fin live mx CAP e h HP11) as NF. rewrite EP.
    destruct HEsk as [E|E]; rewrite E in NF.
    - change (0 =? 1) with false in NF. cbv iota in NF. fold U PS in NF. rewrite (HXs E). lia.
    - change (1 =? 1) with true in NF. cbv iota in NF. fold PS in NF. rewrite (HXs1 E). lia. }
  revert Hrr. destruct (re_eof e =? 0) eqn:Eo; intros Hrr; cbn [andb] in Hrr.
  - apply Z.eqb_eq in Eo.
    destruct Hrr as [HD HS].
    destruct HD as (_ & _ & _ & _ & _ & _ & _ & _ & D9 & D10 & _ & D12 & _ & _ & _ & D16 & _ & _ & D19 & _ & _ &
                    D22 & _ & D24 & _ & _ & D27).
    set (DT := Z.of_nat (length (with_nul (dr_lines h)))) in *.
    assert (HDT0 : 0 <= DT) by (unfold DT; lia).
    assert (Hdt : DT <= P).
    { destruct (HP4 Eo) as (Hov & HU).
      pose proof (SlotReads.lines_bytes (bzs (pending_stream h)) (hs_state h)) as LB0.
      assert (W0 : 0 <= SlotReads.wcost (feed (hs_state h) (bzs (pending_stream h))))
        by (unfold SlotReads.wcost; destruct (ls_k (feed (hs_state h) (bzs (pending_stream h)))); cbv iota; lia).
      change (SlotReads.wcost (hs_state h)) with
        (if hs_overlong h =? 1 then 0 else Z.of_nat (length (bzs (hs_W h)))) in LB0.
      change (lines (hs_state h) (bzs (pending_stream h))) with (dr_lines h) in LB0. fold DT in LB0.
      rewrite !RelayCap.rc_length_bzs in LB0. fold PS in LB0.
      rewrite EP. destruct HEsk as [E|E].
      - assert (LU : length (hs_W h) = length (re_U e)).
        { specialize (HU E). rewrite <- (RelayCap.rc_length_bzs (hs_W h)), <- HU, RelayCap.rc_length_bzs.
          reflexivity. }
        rewrite E in Hov. rewrite <- Hov in LB0. rewrite LU in LB0. fold U in LB0.
        change (0 =? 1) with false in LB0. cbv iota in LB0. rewrite (HXs E). lia.
      - rewrite E in Hov. rewrite <- Hov in LB0.
        change (1 =? 1) with true in LB0. cbv iota in LB0. rewrite (HXs1 E). lia. }
    assert (Hkt1 : gestures_end_b_c.keys_total (re_keys e1) <= KW + DT).
    { unfold KW, DT.
      apply (ou_rm_keys e e1 (dr_lines h));
        [first [exact (proj1 (NoDup_ListNoDup _) D9) | exact D9] | intros y Hy; exact (proj1 (D10 y) Hy)]. }
    set (cap1 := if dr_live (lm_c m) h then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) 0 (lm_cap m) e h)
                 else lm_cap m) in HS.
    set (O1 := if dr_live (lm_c m) h then [] ++ LB else []) in HS.
    assert (Hc1 : cap1 <= Z.max (lm_cap m) (2 * P)).
    { unfold cap1. destruct (dr_live (lm_c m) h); cbv iota; [|lia].
      unfold dr_fin. pose proof (RelayCap.drain_ocap_le (dr_live (lm_c m) h) (lm_mx m) 0 (lm_cap m) e h) as [_ OC].
      pose proof (HNF (dr_live (lm_c m) h) (lm_mx m) (lm_cap m)) as NF. lia. }
    assert (HO1 : Z.of_nat (length O1) <= DT).
    { unfold O1. destruct (dr_live (lm_c m) h); cbv iota; cbn [app length]; [|lia].
      rewrite <- RelayCap.rc_length_bzs, D27. unfold DT. lia. }
    clearbody cap1 O1.
    pose proof (f_equal snd HS) as HS2. cbn [snd] in HS2. rewrite <- HS2.
    eapply Z.le_trans; [apply rm3_sends_cap|]. rewrite rm3_tot_ge. lia.
  - destruct Hrr as [[He1 Hh1] HS]. subst e1 h1.
    pose proof (f_equal snd HS) as HS2. cbn [snd] in HS2. rewrite <- HS2.
    eapply Z.le_trans; [apply rm3_sends_cap|]. rewrite rm3_tot_ge. cbn [length].
    pose proof (ou_keys_total_kw7 (re_keys e)) as HK. fold KW in HK. lia.
Qed.

Lemma fr_OUT_rm_step_p : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  fr_LS3 B CALL_ROOM_B cx t m ly0 S0 -> fr_OUT OM cx t m ly0 S0 ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= cap2 -> 0 <= t < OPS_MAX ->
  fr_OUT OM cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 H1 (U1 & U2 & U3 & U4)
    HRI Hat Hrr Hcn Hcs Hfr Hpos H14 Hoffc Hcapn Ht.
  pose proof Hat as (_ & _ & _ & _ & Hsi & Hh & Hj0 & _).
  set (m' := rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) in *.
  destruct H1 as (rest & e0 & HPm & _).
  assert (EX : XB cx m' S = XB cx m S0) by exact (bo_xb_same_rest B cx m ly0 S0 m' ly S rest HPm (Hfr rest HPm)).
  (* the capacity: the drained lines and the END lines of the keys they made, within twice the pair's mass *)
  pose proof (ou_rm_cap2 cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr) as Hc2.
  assert (He_in : In (rm_ent m j0) (lm_es m)) by (unfold rm_ent; apply nth_In; exact Hj0).
  assert (Hh_in : In (Some h) (lm_hs m)) by (rewrite <- Hh; apply nth_In; exact (rm3_nth_lt _ _ _ Hh)).
  pose proof (MASSe_in (lm_es m) _ He_in) as Hem.
  pose proof (pend_bytes_in m (Some h) Hh_in) as Hpm.
  assert (HPS : Z.of_nat (length (pending_stream h)) = slot_pend (Some h)) by exact (ls3_ps_sp h Hoffc).
  assert (Hmass_nn : 0 <= MASS m) by (apply MASS_nonneg).
  assert (Hc2' : cap2 <= Z.max (lm_cap m) (4 * MASS m)) by (unfold MASS in *; lia).
  (* the mass falls: the entry leaves the table and the slot is closed *)
  assert (EMass : MASS m' <= MASS m).
  { unfold MASS, MASSe, pend_bytes, m'. cbn [rm_mk lm_es lm_hs].
    pose proof (fr_sum_perm _ ent_mass _ _ (fr_remove_perm _ (lm_es m) j0 relay_remove_b_c.no_entry Hj0)) as Pe.
    cbn [map fold_right] in Pe. fold (rm_ent m j0) in Pe.
    pose proof (ent_mass_nonneg (rm_ent m j0)) as Hen.
    pose proof (rm3_set_zsum _ slot_pend si None (Some h) (lm_hs m) (nth_some_error _ _ _ Hh)) as Zp.
    assert (N4 : slot_pend None = 0) by reflexivity.
    pose proof (slot_pend_nonneg (Some h)). lia. }
  assert (ECap : lm_cap m' = cap2) by reflexivity.
  unfold fr_OUT in *. rewrite EX, ECap. unfold WMAX, OUT_MAX4, OPS_MAX in *. repeat split; try lia.
Qed.

(* ---------------------------------------------------------------- the first head, at fr_LS3c_pro's premises (A :826-837) *)
Lemma fr_OUT_pro_c : forall MT0 XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S,
  lf_base B MT0 XM_LIB RLO RHI (fun S0 => blocks_bytes S0 + CALL_ROOM_B <= LIVE_MAX) G_fr cx -> 0 <= cap ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_OUT OM cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros MT0 XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S _ Hc HE.
  assert (H0 : 0 <= OM) by (unfold OUT_MAX4 in HOM; lia).
  exact (fr_OUT_pro_b B OM cx q T' pj c O cap out ly S Hc H0 HE).
Qed.
End ou.

(* ================================================================== fr_OUT is satisfiable (A :840-885) *)
(* at fr_LS3c_sat's state (ReplyB3LS3.v Section sat3: a 1-byte input block, the relay's table, one open source's
   partial buffer, no out buffer) *)
Section osat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma fr_OUT_sat_state : forall OM, 0 <= OM -> fr_OUT OM (ls3_cx B) 0 (ls3_m B) ls3_ly ls3_S.
Proof.
  intros OM HOM.
  assert (ES : c_S (ls3_cx B) = ls3_S) by reflexivity.
  assert (EM : bsum (model_blks (ls3_m B)) = ATABLE + APARTIAL) by (vm_compute; reflexivity).
  assert (EC : lm_cap (ls3_m B) = 0) by reflexivity.
  assert (EMass : MASS (ls3_m B) = 0) by reflexivity.
  unfold fr_OUT, XB. rewrite ES, EM, EC, EMass. unfold ATABLE, APARTIAL. repeat split; lia.
Qed.
(* the same state is ReplyB3LS3cArms.v fr_LS3c_sat's witness, so LS v3's count half and its out half hold together
   there; that proof's body is replayed here because fr_LS3c_sat states only the existential.  B: at the B instance
   CALL_ROOM_B := YCfn_cf.CALL_ROOM_B *)
Lemma fr_LS3c_OUT_sat : forall OM, 0 <= OM ->
  exists (cx : lfcx (rc := rc)) t m ly S, fr_LS3c B YCfn_cf.CALL_ROOM_B cx t m ly S /\ fr_OUT OM cx t m ly S.
Proof.
  intros OM HOM. exists (ls3_cx B), 0, (ls3_m B), ls3_ly, ls3_S.
  split; [|exact (fr_OUT_sat_state OM HOM)].
  assert (EA : ablocks B ls3_ly ls3_S = input_blks (ls3_cx B) ++ model_blks (ls3_m B) ++ []) by reflexivity.
  split.
  - exists [], 0.
    assert (Hbb : blocks_bytes ls3_S = 1 + ATABLE + APARTIAL) by (vm_compute; reflexivity).
    assert (Hin : bsum (input_blks (ls3_cx B)) = 1) by reflexivity.
    assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
    assert (HS : c_S (ls3_cx B) = ls3_S) by reflexivity.
    assert (Hn : c_n (ls3_cx B) = 1) by reflexivity.
    assert (HC : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
    assert (HL : LIVE_MAX = 17179869184) by reflexivity.
    assert (En : npend (ls3_m B) = 0) by reflexivity.
    assert (Ek : kk (ls3_cx B) (ls3_m B) = 0) by reflexivity.
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
End osat.

(* ================================================================== the exit (SEG_EXIT) (A :887-1089) *)
(* relay_finish over the table: the capacity never falls and grows to at most twice what is sent (A :960-975) *)
Lemma ou_rf_cap : forall es c O mx no cap, 0 <= cap ->
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

Section oexit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable CALL_ROOM_B : Z.
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.
(* the meter (KF-COUNT): a Variable, implicit, read off the exit rules' mo_le arguments *)
Context {MT : ameter_ops}.
(* the contract's fr_live_post with OUT_MAX read as the parameter OM (at OM := YCfn_cf.OUT_MAX it is
   YCfn_cf.fr_live_post_b's text, lib/B/YCfn_cf.v :63-64) *)
Definition fr_live_post3 (S S' : astate) (k : Z) : Prop :=
  blocks_bytes S' <= blocks_bytes S + ATABLE + OM /\ 0 <= k.

(* THE BYTES AT THE RETURN: the exit keeps the relay's table and g_out and frees everything else of the model, and
   g_out's final capacity is relay_finish's, which is at most twice the model's mass. *)
Lemma ou_exit_bytes : forall cx t m ly3 S3 rest ly' S' cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  blocks_bytes S' <= blocks_bytes (c_S cx) + ATABLE + OM.
Proof.
  intros cx t m ly3 S3 rest ly' S' cap out (HLS & _) (U1 & U2 & U3 & U4) HP HP' Hcap Ht.
  destruct (ou_rf_cap (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) U1) as (R1 & R2 & _).
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

(* ---- the AR text, lib/B/W_LLVMFuzzerTestOneInput_exit.v :173-180, with A's ONE added premise,
   `cap = gse_cap (lx_rf_run ..)` (the arm passes relay_finish's FINAL capacity), and A's `0 <= t <= OPS_MAX`.
   `out` stays free.  HSURV: this fr_surv takes only the entry's and the return's layouts and states; LS cannot
   conclude it (A :1014-1019). ---- *)
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Lemma LS_exit_end3 : forall cx t m ly3 S3 rest ly' S' fpos k' C cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX -> 0 <= k' ->
  fr_surv (c_ly cx) (c_S cx) ly' (stack_free_state 1 fpos S') ->
  fr_live_post3 (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) ly' (stack_free_state 1 fpos S').
Proof.
  intros cx t m ly3 S3 rest ly' S' fpos k' C cap out HLS HOU HP HP' Hfr Hmo HC Hcap Ht Hk HSURV.
  assert (EB : blocks_bytes (stack_free_state 1 fpos S') = blocks_bytes S').
  { rewrite (blocks_bytes_bsum B ly' (stack_free_state 1 fpos S')), (blocks_bytes_bsum B ly' S').
    assert (EA : ablocks B ly' (stack_free_state 1 fpos S') = ablocks B ly' S') by reflexivity.
    rewrite EA. reflexivity. }
  split; [| exact HSURV].
  unfold fr_live_post3. rewrite EB. split; [| exact Hk].
  exact (ou_exit_bytes cx t m ly3 S3 rest ly' S' cap out HLS HOU HP HP' Hcap Ht).
Qed.

(* ---- the ARx text, lib/B/W_LLVMFuzzerTestOneInput_exit_x.v :172-186, with the same ONE added premise and its NP
   conclusion DROPPED (the exit walk takes NP from the threaded room invariant; this proof never read NP).  0 <= k'
   is NOT a hypothesis: the journal premise gives it (Reusable/YCbqG.v ajournal_x's 8th conjunct).  fr_surv stays a
   named hypothesis because LS cannot conclude it (A :1044-1056). ---- *)
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable fr_surv_x : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate ->
  world segs -> (word -> option byte) -> Prop.
Lemma LS_exit_end3_x : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  W_journal_x.ajournal_gx_x segs B PST ARx G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  fr_surv_x (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' ->
  fr_live_post3 (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv_x (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem'.
Proof.
  intros cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out HLS HOU HP HP' Hfr Hmo HC Hcap Ht HJ HSURV.
  assert (Hk : 0 <= k').
  { destruct HJ as (_ & _ & (memS & HAJ & _) & _).
    destruct HAJ as (_ & _ & _ & _ & _ & _ & _ & Hk0 & _). exact Hk0. }
  assert (EB : blocks_bytes (stack_free_state 1 fpos S') = blocks_bytes S').
  { rewrite (blocks_bytes_bsum B ly' (stack_free_state 1 fpos S')), (blocks_bytes_bsum B ly' S').
    assert (EA : ablocks B ly' (stack_free_state 1 fpos S') = ablocks B ly' S') by reflexivity.
    rewrite EA. reflexivity. }
  split; [| exact HSURV].
  unfold fr_live_post3. rewrite EB. split; [| exact Hk].
  exact (ou_exit_bytes cx t m ly3 S3 rest ly' S' cap out HLS HOU HP HP' Hcap Ht).
Qed.
End oexit.
