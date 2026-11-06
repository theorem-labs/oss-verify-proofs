(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v; 782 of its 917 lines of code are new or changed and 459 lines of the source are left out. *)
(* The out-buffer half of LS v3 (row B1c, a Theorem Labs lane): fr_OUT, the conjunct that bounds g_capout, its twin of
   every rule that ends in fr_LS3c (lib/A/ReplyLS3c.v, lib/A/ReplyLS3cArms.v), and the exit obligations
   LS_exit_end restated over it (LS_rf_room's peak form is lib/A/ReplyLS3oRf.v).  proves no function (kind:
   invariant lemma).

   OUT_MAX.  a8 raised the contract's g_out bound: a working branch a389032ec36 lib/A/ACfn_cf.v:57
   `Definition OUT_MAX : Z := 66976770`, :59 `OUT_MAX_src : OUT_MAX = 2 * (OPS_MAX - 1) * 65535`, :67
   `fr_live_post S S' k := blocks_bytes S' <= blocks_bytes S + ATABLE + OUT_MAX /\ 0 <= k`.  THIS WORKTREE still has
   the old 33,554,430 (ACfn_cf.v:44), so OUT_MAX3 below repeats a8's value and OUT_MAX4 a Theorem Labs lane's later ruling;
   the switch to ACfn_cf.OUT_MAX is a rename when the trees merge.

   OUT_MAX4 = 133,953,540 = 4 * (OPS_MAX - 1) * 65,535 is a Theorem Labs lane's ruling of 2026-10-30 01:47Z, after this row
   found that a8's 66,976,770 is still too small.  WHY: relay_remove drains the source FIRST and then ends the
   gestures of the entry the drain left (ReplyRINV.v:380-391 rm_rr_ok: `dr_rel ... e1 h1 LB` then
   `sl_sends mx c1 O1 cap1 (ge_bytes (re_keys e1))`; relay.c:463-465), so the begin lines AND the end lines of the
   keys those same begin lines made go out in ONE operation.  a8's reviewer counted each begin line once.  A Theorem Labs lane
   MEASURED it on the pinned fuzz_reply.asan (b1-RECHECK.md (sha256 2d07c55f9e3f; internal record) Part 2,
   2026-10-30 01:50Z): gest511_rm.bin (511 writes holding 5,580 distinct 6,000-byte `param_gesture <key> begin`
   lines, then one remove) leaves g_nout = 66,962,805 and g_capout = 98,303,538 = 2.93 x the old OUT_MAX;
   gest188_rm.bin leaves 49,141,066; the smallest witness is K = 129 writes (g_capout 33,777,208).  b1 also REFUTED
   the 511-NUL-writes shape as a witness: there g_capout = 2 ^ ceil(log2(65,535 K + 2)) - 2 = 33,554,430 exactly.
   The model's growth law is the measured one: Prog/send_line_b_c.v:33-37 sl_run grows to `(no + n) * 2` only when
   `cap < no + n`, so from cap = 0 and one-byte sends the capacities run 2, 6, 14, ... = 2 ^ m - 2, which is b1's
   law; ou_growth below is that step, Qed-checked at b1's measured numbers (ou_wit_gest511).

   fr_OUT (the e0-free form a Theorem Labs lane accepted at 00:59Z / 01:02Z):
     0 <= lm_cap m /\ 0 <= XB /\ lm_cap m <= XB + OM /\ MASS m <= 65535 * t,
   XB cx m S := blocks_bytes (c_S cx) - blocks_bytes S + bsum (model_blks m)  (= blocks_bytes (c_S cx) - bsum input
   - bsum rest under fr_LS3's permutation, so `lm_cap m <= e0 + OUT_MAX` is this with e0's definition unfolded), and
     MASS m := sum over the relay's entries of (|re_U e| + sum over its keys of (|key| + 7)) + pend_bytes m,
   the bytes one operation may still send.  MASS counts a held key at |key| + 7 = the cost of the BEGIN line that
   made it (ou_gesture_begin_key: `gesture l = Some (GBegin, x)` forces |x| + 6 = |l|), which is the key-model form
   of "an END line (|key| + 5) is shorter than its BEGIN line (|key| + 7)" that a Theorem Labs lane asked for (00:59Z),
   stated once here and NOT through keys_total.  Every rule keeps MASS except the write, which adds at most one
   fuzz_take of 65,535 bytes; so one operation sends at most 2 * MASS <= 2 * 65,535 * t bytes and a send grows
   g_capout to at most 2 * (g_nout + len), whence 4 * 65,535 * 511 = OUT_MAX4 at t < OPS_MAX.

   This file: fr_OUT, its keep rules, its twin of the fourteen fr_LS3c rules, satisfiability, and the exit's
   LS_exit_end at LS := fr_LS3c /\ fr_OUT (LS_rf_room in peak form: lib/A/ReplyLS3oRf.v LS_rf_room_p). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak ReplyTrPeakC.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== the constants *)
(* a8's value, a working branch a389032ec36 lib/A/ACfn_cf.v:57 (copied: this worktree's ACfn_cf.v:44
   still has the old 2 ^ 25 - 2) *)
Definition OUT_MAX3 : Z := 66976770.
(* a Theorem Labs lane's ruling 2026-10-30 01:47Z, from this row's finding and a Theorem Labs lane's measurement *)
Definition OUT_MAX4 : Z := 133953540.
(* the bytes one write operation adds: fuzz_take (fuzz_u16 (&in), ...) (fuzz_reply.c:705), = SlotInv.WRITE_MAX *)
Definition WMAX : Z := 65535.
Lemma OUT_MAX3_src : OUT_MAX3 = 2 * (OPS_MAX - 1) * WMAX.
Proof. reflexivity. Qed.
Lemma OUT_MAX4_src : OUT_MAX4 = 4 * (OPS_MAX - 1) * WMAX.
Proof. reflexivity. Qed.
Lemma WMAX_src : WMAX = SlotInv.WRITE_MAX.
Proof. reflexivity. Qed.

(* ================================================================== the key model *)
(* The weight of a held key: its END line is |key| + 5 bytes (gestures_end_b_c.keys_total), and the BEGIN line that
   made it is |key| + 6 bytes, |key| + 7 with its NUL.  THE KEY-MODEL FACT (a Theorem Labs lane 00:59Z: state it once over
   the key model, not through keys_total): RelayModel.gesture reads a begin line as `<key> begin`, so its key is the
   line less " begin". *)
Definition kw7 (x : list Z) : Z := Z.of_nat (length x) + 7.
Definition kw7s (T : list (list Z)) : Z := zsum (map kw7 T).

Lemma ou_gesture_begin_key : forall l x, gesture l = Some (GBegin, x) ->
  Z.of_nat (length x) + 6 = Z.of_nat (length l).
Proof.
  intros l x H. unfold gesture in H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|]; [|discriminate].
  destruct (Nat.ltb 13 j); [|discriminate].
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:Eb.
  - assert (Ex : firstn j l = x) by (injection H as E; exact E).
    rewrite <- Ex.
    unfold list_eqb in Eb. destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [E|_]; [|discriminate].
    assert (L5 : length (skipn (S j) l) = 5%nat) by (rewrite E; reflexivity).
    rewrite length_skipn in L5.
    assert (Hj : (S j + 5 <= length l)%nat) by lia.
    rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); discriminate.
Qed.

Lemma kw7_nonneg : forall x, 0 <= kw7 x.
Proof. intros x. unfold kw7. lia. Qed.
Lemma kw7s_nonneg : forall T, 0 <= kw7s T.
Proof. intros T. apply zsum_map_nonneg. exact kw7_nonneg. Qed.
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
(* the keys a drain's lines can add (ReplyLSDrain3.v dr3_nk), by weight *)
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

(* ================================================================== MASS: what one operation may still send *)
Definition ent_mass (e : rentry) : Z :=
  Z.of_nat (length (re_U e)) + kw7s (drain_b_c.keys_texts (re_keys e)).
Lemma ent_mass_nonneg : forall e, 0 <= ent_mass e.
Proof. intros e. unfold ent_mass. pose proof (kw7s_nonneg (drain_b_c.keys_texts (re_keys e))). lia. Qed.
(* an END line (|key| + 5) is within its key's weight (|key| + 7 = the BEGIN line's own cost) *)
Lemma ou_keys_total_kw7 : forall ks, gestures_end_b_c.keys_total ks <= kw7s (drain_b_c.keys_texts ks).
Proof.
  induction ks as [|k ks IH]; [cbn [kw7s map fold_right]; reflexivity|].
  change (gestures_end_b_c.keys_total (k :: ks)) with
    (Z.of_nat (length (gestures_end_b_c.key_text k)) + 5 + gestures_end_b_c.keys_total ks).
  change (drain_b_c.keys_texts (k :: ks)) with
    (bzs (gestures_end_b_c.key_text k) :: drain_b_c.keys_texts ks).
  unfold kw7s, kw7 in *. cbn [map fold_right]. rewrite RelayCap.rc_length_bzs. lia.
Qed.
(* the END lines of an entry's keys are within its mass *)
Lemma ou_keys_total_mass : forall e, gestures_end_b_c.keys_total (re_keys e) <= ent_mass e.
Proof. intros e. unfold ent_mass. pose proof (ou_keys_total_kw7 (re_keys e)). lia. Qed.
Definition MASSe (es : list rentry) : Z := zsum (map ent_mass es).
Definition MASS (m : lmod) : Z := MASSe (lm_es m) + pend_bytes m.
Lemma MASSe_nonneg : forall es, 0 <= MASSe es.
Proof. intros es. apply zsum_map_nonneg. exact ent_mass_nonneg. Qed.
Lemma MASSe_in : forall es e, In e es -> ent_mass e <= MASSe es.
Proof. intros es e H. apply (dr3_sum_in ent_mass es e ent_mass_nonneg H). Qed.
Lemma pend_bytes_in : forall m o, In o (lm_hs m) -> slot_pend o <= pend_bytes m.
Proof. intros m o H. apply (dr3_sum_in slot_pend (lm_hs m) o slot_pend_nonneg H). Qed.
Lemma MASS_nonneg : forall m, 0 <= MASS m.
Proof.
  intros m. unfold MASS. pose proof (MASSe_nonneg (lm_es m)).
  assert (0 <= pend_bytes m) by (apply zsum_map_nonneg; exact slot_pend_nonneg). lia.
Qed.

(* ================================================================== the growth law, and b1's measured witness *)
(* the MEASURED witnesses (b1-RECHECK.md (sha256 2d07c55f9e3f; internal record) Part 2):
   gest511_rm.bin (511 writes holding 5,580 distinct 6,000-byte `param_gesture <key> begin` lines, then one
   remove) leaves g_nout = 66,962,805 and g_capout = 98,303,538, on the counting build AND as an mmap of
   sec_map_size(98,303,538) on the pinned fuzz_reply.asan; gest188_rm.bin leaves 49,141,066; the smallest witness
   is K = 129 writes (33,777,208).  b1 also REFUTED the 511-NUL-writes shape (g_capout = 33,554,430 exactly, the
   OLD OUT_MAX): there every send is one byte, so the capacities run 2 ^ m - 2.
   THE MODEL'S LAW IS THE MEASURED ONE.  send_line grows g_capout to (g_nout + n) * 2 and only when
   g_capout < g_nout + n (Prog/send_line_b_c.v:33-37 sl_run), which is b1's
   g_capout = 2 ^ ceil(log2(65,535 K + 2)) - 2 for one-byte sends and 2 * (g_nout + len) for a line.
   gest511_rm's LAST growth is b1's raw counting-build line
   `old=49148190 new=98303538 g_nout_now=49151774`: the capacity before it was 49,148,190 and after it
   98,303,538.  The model's law makes that growth (g_nout + len) * 2, so g_nout + len = 49,151,769 at the growing
   send (the shim reads g_nout at the next allocator call, after more bytes went out).  The measurement fixes ONLY
   that sum, not how it splits into g_nout and len; the split 49,151,764 + 5 below is one choice of it.  At that
   point the model's own send_line_cap, from b1's capacity 49,148,190, gives b1's measured final g_capout, which
   is above a8's OUT_MAX3 and inside a Theorem Labs lane's OUT_MAX4. *)
Lemma ou_wit_gest511 :
  send_line_b_c.send_line_cap true 0 49151764 49148190 5 = 98303538 /\
  66962805 <= 98303538 /\ OUT_MAX3 < 98303538 <= OUT_MAX4.
Proof.
  assert (E : send_line_b_c.send_line_cap true 0 49151764 49148190 5 = 98303538) by (vm_compute; reflexivity).
  unfold OUT_MAX3, OUT_MAX4. repeat split; lia.
Qed.
(* one operation's output is at most 2 * MASS, and a send leaves at most twice it: this is why OUT_MAX4 and not
   OUT_MAX3 is the contract's bound (the remove sends the drained lines AND the ends of the keys they made) *)
Lemma ou_mass_bound : forall t, 0 <= t < OPS_MAX -> 4 * (WMAX * t) <= OUT_MAX4.
Proof. intros t Ht. unfold OUT_MAX4, WMAX, OPS_MAX in *. lia. Qed.
Lemma ou_mass_bound2 : forall t, 0 <= t <= OPS_MAX -> 2 * (WMAX * t) <= OUT_MAX4.
Proof. intros t Ht. unfold OUT_MAX4, WMAX, OPS_MAX in *. lia. Qed.

(* ================================================================== fr_OUT *)
Section ou.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the out-buffer bound the contract carries (ACfn_cf.fr_live_post's OUT_MAX); every lemma below is at any OM at
   least a Theorem Labs lane's ruled value *)
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.

Definition XB (cx : lfcx) (m : lmod) (S : astate) : Z :=
  blocks_bytes (c_S cx) - blocks_bytes S + bsum (model_blks m).
Definition fr_OUT (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  0 <= lm_cap m /\ 0 <= XB cx m S /\ lm_cap m <= XB cx m S + OM /\ MASS m <= WMAX * t.

Ltac ou_perm :=
  repeat match goal with H : Permutation _ _ |- _ =>
    let H' := fresh "Hc" in pose proof (proj1 (Permutation_count_occ zzdec _ _) H) as H'; clear H end;
  apply (proj2 (Permutation_count_occ zzdec _ _)); let x := fresh "x" in intros x;
  repeat match goal with H : forall _ : Z * Z, count_occ _ _ _ = count_occ _ _ _ |- _ => specialize (H x) end;
  repeat progress (rewrite ?count_occ_app, ?cnt_cons, ?cnt_nil in *); lia.

(* ---------------------------------------------------------------- XB moves with the rest only *)
Lemma xb_perm : forall cx m ly S rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  XB cx m S = blocks_bytes (c_S cx) - bsum (input_blks cx) - bsum rest.
Proof.
  intros cx m ly S rest HP. unfold XB.
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app. lia.
Qed.
Lemma xb_same_rest : forall cx m ly S m' ly' S' rest,
  Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ model_blks m' ++ rest) ->
  XB cx m' S' = XB cx m S.
Proof.
  intros cx m ly S m' ly' S' rest HP HP'.
  rewrite (xb_perm cx m ly S rest HP), (xb_perm cx m' ly' S' rest HP'). reflexivity.
Qed.

(* ---------------------------------------------------------------- the keep rules *)
Lemma fr_OUT_keep : forall cx t t' m m' ly S,
  model_blks m' = model_blks m -> lm_cap m' = lm_cap m -> MASS m' <= MASS m -> t <= t' ->
  fr_OUT cx t m ly S -> fr_OUT cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S Hb Hc Hm Ht (O1 & O2 & O3 & O4).
  unfold fr_OUT, XB in *. rewrite Hb, Hc. unfold WMAX in *. repeat split; try lia.
Qed.
Lemma fr_OUT_k_only : forall cx t t' m m' ly S,
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  t <= t' -> fr_OUT cx t m ly S -> fr_OUT cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S E1 E2 E3 E4 E5 Ht H.
  apply (fr_OUT_keep cx t t' m m' ly S); [| exact E4 | | exact Ht | exact H].
  - unfold model_blks. rewrite E1, E2, E3, E4, E5. reflexivity.
  - unfold MASS, MASSe, pend_bytes. rewrite E1, E2. lia.
Qed.
Lemma fr_OUT_upd : forall cx t t' m m' ly S i f,
  lm_hs m' = upd_hs i f (lm_hs m) -> (forall h, asrc_blks (f h) = asrc_blks h) ->
  (forall h, slot_pend (Some (f h)) = slot_pend (Some h)) ->
  lm_es m' = lm_es m -> lm_G m' = lm_G m -> lm_cap m' = lm_cap m -> lm_out m' = lm_out m ->
  t <= t' -> fr_OUT cx t m ly S -> fr_OUT cx t' m' ly S.
Proof.
  intros cx t t' m m' ly S i f E1 Hfb Hfp E2 E3 E4 E5 Ht H.
  apply (fr_OUT_keep cx t t' m m' ly S); [| exact E4 | | exact Ht | exact H].
  - unfold model_blks. rewrite E1, E2, E3, E4, E5, (upd_hs_blks i f (lm_hs m) Hfb). reflexivity.
  - unfold MASS, MASSe, pend_bytes. rewrite E1, E2, (upd_hs_map slot_pend i f (lm_hs m) Hfp). lia.
Qed.

(* ---------------------------------------------------------------- the rules of ReplyLS3c.v *)
Lemma fr_OUT_head_nout : forall cx t m ly S, fr_OUT cx t m ly S -> fr_OUT cx t (lm_clear_O m) ly S.
Proof. intros cx t m ly S H. apply (fr_OUT_k_only cx t t m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_head_skip : forall cx t m ly S, fr_OUT cx t m ly S ->
  fr_OUT cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof. intros cx t m ly S H. apply (fr_OUT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_close : forall cx t m i ly S, fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S H. apply (fr_OUT_upd cx t (t + 1) m _ ly S i upd_closed);
    try reflexivity; try (intros h; reflexivity); try lia; exact H.
Qed.
Lemma fr_OUT_eintr : forall cx t m i ly S, fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S H. apply (fr_OUT_upd cx t (t + 1) m _ ly S i upd_eintr);
    try reflexivity; try (intros h; reflexivity); try lia; exact H.
Qed.
Lemma fr_OUT_sendmax : forall cx t m u ly S, fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (sm_sendmax cx m u) ly S.
Proof. intros cx t m u ly S H. apply (fr_OUT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_default : forall cx t m g ly S, fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (sm_default cx m g) ly S.
Proof. intros cx t m g ly S H. apply (fr_OUT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_write_skip : forall cx t m ly S, fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof. intros cx t m ly S H. apply (fr_OUT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.
Lemma fr_OUT_add_none : forall cx t m ly S, fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (ad_none m) ly S.
Proof. intros cx t m ly S H. apply (fr_OUT_k_only cx t (t + 1) m _ ly S); try reflexivity; try lia; exact H. Qed.

(* op_add's open: the new partial buffer is a model block, so XB is unchanged; the new entry and the new source
   carry no mass *)
Lemma fr_OUT_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3 B cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (ad_open m i q pj ev) ly' S'.
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

(* ---------------------------------------------------------------- the write arm's push *)
(* wr_n is one fuzz_take of fuzz_u16 bytes (W_LLVMFuzzerTestOneInput_write.v:181-190): at most 65,535 *)
Lemma ou_wr_n_le : forall cx m, wr_n cx m <= WMAX.
Proof.
  intros cx m. unfold wr_n, wr_u, WMAX.
  pose proof (in_byte_range cx (wr_k1 cx m)). pose proof (in_byte_range cx (wr_k1 cx m + 1)).
  destruct (2 <=? wr_rem cx m), (wr_rem cx m =? 1); lia.
Qed.
Lemma fr_OUT_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS3 B cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  fr_OUT cx t m ly S -> fr_OUT cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
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
  { unfold model_blks, m'. cbn [wr_push lm_G lm_es lm_hs lm_cap lm_out]. ou_perm. }
  assert (Hsplit : exists mm, Permutation (model_blks m) (OV ++ mm)).
  { destruct (lp_grow l && negb (hl_cap l =? 0)) eqn:Eg; unfold OV; try rewrite Eg; cbv beta iota.
    - assert (Hin : In (hl_v l, AREC * hl_cap l) (model_blks m)).
      { apply andb_true_iff in Eg as (_ & E). apply negb_true_iff in E. unfold model_blks.
        right. apply in_app_iff. right. apply in_app_iff. left. apply in_concat.
        exists (slot_blks (Some h)). split; [apply in_map; exact (nth_error_In _ _ Hi)|].
        cbn [slot_blks]. rewrite Ha. right. apply in_app_iff. left. apply in_app_iff. left.
        unfold VL. rewrite E. left. reflexivity. }
      destruct (in_split _ _ Hin) as (l1 & l2 & E). exists (l1 ++ l2). rewrite E. ou_perm.
    - exists (model_blks m). apply Permutation_refl. }
  destruct Hsplit as (mm & Hmm).
  assert (HP1 : Permutation (ablocks B ly S) (OV ++ (input_blks cx ++ mm ++ rest))) by ou_perm.
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

(* ---------------------------------------------------------------- the first head (the prologue) *)
Lemma fr_OUT_pro : forall cx q T' pj c O cap out ly S,
  0 <= cap ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_OUT cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros cx q T' pj c O cap out ly S Hc (T0 & rest0 & HE0 & Hcase).
  set (m := ls_pro_m q T' pj c O cap out).
  assert (EC : lm_cap m = cap) by reflexivity.
  assert (EM : bsum (model_blks m) = ATABLE + APARTIAL + cap).
  { assert (Hmb : model_blks m = (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
    rewrite Hmb, !bsum_cons, (ev3_bsum_aout_eq cap out Hc). cbn [snd]. lia. }
  assert (EB : blocks_bytes S = blocks_bytes (c_S cx) + (if T0 =? 0 then ATABLE else 0) + APARTIAL).
  { destruct Hcase as [(HT0 & HP) | (HT0 & HT' & HP)].
    - subst T0. rewrite Z.eqb_refl.
      rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_cons,
        <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). cbn [snd]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) HT0).
      rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_cons,
        <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). cbn [snd]. lia. }
  assert (EX : XB cx m S = (if T0 =? 0 then 0 else ATABLE) + cap)
    by (unfold XB; rewrite EM, EB; destruct (T0 =? 0); lia).
  assert (EMass : MASS m = 0) by reflexivity.
  unfold fr_OUT. rewrite EC, EX, EMass. unfold OUT_MAX4, ATABLE in *.
  destruct (T0 =? 0); repeat split; lia.
Qed.

(* ---------------------------------------------------------------- the remove arm's step *)
(* the END lines of the entry's keys after the drain: at most the entry's mass and the lines it relayed.  This is
   the sharp form of ReplyLS3Arms.v ls3_rm_cap2 (which charges 2 per relayed byte); the key weight kw7 is the
   begin line's own cost, so a relayed begin line is counted ONCE here. *)
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

(* ---------------------------------------------------------------- the drain arm's step *)
(* Hcap0' (0 <= cap') is dr_post's aout_at (W_rep.v:187-189, the disjunction's two cases both give it); Ht is the
   arm's cut (lregs_D, W_LLVMFuzzerTestOneInput_cut.v:754 `0 <= t < OPS_MAX`), as LS_cnl_pre already takes it. *)
Lemma fr_OUT_drain_step_p : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B cx t m ly S -> fr_OUT cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
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
  fr_OUT cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
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
  { rewrite Ha1 in HPd2. clear - HPd2. ou_perm. }
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
  (* HU' / RM / Hno are all over drain_b_c.drain_fin; Hcap' and dr3_ocap stay in dr_fin's form *)
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

(* ---------------------------------------------------------------- the remove arm's step *)
(* g_capout after relay_remove, SHARPLY: ReplyLS3Arms.v ls3_rm_cap2's proof with the key weight kw7 in place of
   its "2 per relayed byte", so a begin line relayed in this operation pays for its own END line ONCE. *)
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
  fr_LS3 B cx t m ly0 S0 -> fr_OUT cx t m ly0 S0 ->
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
  fr_OUT cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 H1 (U1 & U2 & U3 & U4)
    HRI Hat Hrr Hcn Hcs Hfr Hpos H14 Hoffc Hcapn Ht.
  pose proof Hat as (_ & _ & _ & _ & Hsi & Hh & Hj0 & _).
  set (m' := rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) in *.
  destruct H1 as (rest & e0 & HPm & _).
  assert (EX : XB cx m' S = XB cx m S0) by exact (xb_same_rest cx m ly0 S0 m' ly S rest HPm (Hfr rest HPm)).
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

(* ---------------------------------------------------------------- the event arm's step *)
(* one event sends one line of at most 65,536 bytes (fuzz_u16, fuzz_reply.c:725-726), so the buffer grows to at
   most 131,072 whatever the mass is *)
Lemma ou_ev_len : forall cx m e, ev_evt cx m e -> re_len e <= 65536.
Proof.
  intros cx m e (He & _). unfold re_len, ev_len, ev_u16 in *.
  pose proof (in_byte_range cx (lm_k m + 1)). pose proof (in_byte_range cx (lm_k m + 2)).
  destruct (2 <=? c_n cx - lm_k m - 1), (1 <=? c_n cx - lm_k m - 1); lia.
Qed.
Lemma fr_OUT_event_step_p : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS3 B cx t m ly S -> fr_OUT cx t m ly S -> ev_evt cx m e ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_OUT cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HLS (U1 & U2 & U3 & U4) HE Hk HO Hc0 Hm HRR Hf.
  destruct HRR as (restR & HR1 & HR2). destruct Hf as (l1 & l2 & Hf2 & Hf3).
  set (cap' := sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in *.
  set (m' := ev_step cx m e v out') in *.
  assert (ECap : lm_cap m' = cap') by reflexivity.
  (* the capacity: at most twice one line *)
  assert (Hcge : lm_cap m <= cap').
  { unfold cap', sl_cap.
    exact (proj2 (tp_send_line (sl_live (lm_c m) (re_len e)) (lm_mx m) (Z.of_nat (length (lm_O m)))
                   (lm_cap m) (re_len e) 0 RelayRunF.adr0 Hc0)). }
  assert (HO0 : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  assert (Hcle : cap' <= Z.max (lm_cap m) (2 * 65536)).
  { pose proof (ev3_cap_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hle.
    pose proof (ou_ev_len cx m e HE) as Hlen. unfold cap'. lia. }
  assert (Hc0' : 0 <= cap') by lia.
  (* XB: the event's block is malloc'd and freed, and the out buffer's bytes move with its capacity *)
  assert (EB1 : blocks_bytes S1 = blocks_bytes S + re_len e) by exact (bb_after_malloc B ly S ly1 S1 q (re_len e) Hm).
  assert (EB2 : blocks_bytes S2 = blocks_bytes S1 - bsum (aout_blks (lm_cap m) (lm_out m)) +
                                  bsum (aout_blks cap' out')).
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HR2), (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ HR1),
      !bsum_app. lia. }
  assert (EB3 : blocks_bytes S3 = blocks_bytes S2 - re_len e)
    by exact (bb_after_free B ly2 S2 ly3 S3 q (re_len e) (ex_intro _ l1 (ex_intro _ l2 (conj Hf2 Hf3)))).
  assert (EM : bsum (model_blks m') = bsum (model_blks m) - bsum (aout_blks (lm_cap m) (lm_out m)) +
                                      bsum (aout_blks cap' out')).
  { rewrite (ev3_model_blks m'), (ev3_model_blks m), !bsum_app.
    assert (Ep : ev3_pfx m' = ev3_pfx m) by reflexivity. rewrite Ep.
    assert (Ec : lm_cap m' = cap') by reflexivity. assert (Eo : lm_out m' = out') by reflexivity.
    rewrite Ec, Eo. lia. }
  assert (EX : XB cx m' S3 = XB cx m S) by (unfold XB; lia).
  assert (EMass : MASS m' = MASS m) by reflexivity.
  unfold fr_OUT in *. rewrite EX, ECap. unfold WMAX, OUT_MAX4 in *. repeat split; try lia.
Qed.

(* ---------------------------------------------------------------- the first head, at fr_LS3c_pro's premises *)
Lemma fr_OUT_pro_c : forall XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S,
  lf_base B ameter_triv XM_LIB RLO RHI ACfn_cf.fr_live_pre G_fr cx -> 0 <= cap ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_OUT cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S _ Hc HE.
  exact (fr_OUT_pro cx q T' pj c O cap out ly S Hc HE).
Qed.
End ou.

(* ================================================================== fr_OUT is satisfiable *)
(* at fr_LS3c_sat's state (ReplyLS3.v Section sat3: a 1-byte input block, the relay's table, one open source's
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
(* the same state is ReplyLS3cArms.v fr_LS3c_sat's witness (:204), so LS v3's count half and its out half hold
   together there; that proof's body is replayed here because fr_LS3c_sat states only the existential *)
Lemma fr_LS3c_OUT_sat : forall OM, 0 <= OM ->
  exists (cx : lfcx (rc := rc)) t m ly S, fr_LS3c B cx t m ly S /\ fr_OUT OM cx t m ly S.
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
    assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
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

(* ================================================================== the exit (SEG_EXIT) *)
(* relay_finish's output: it sends the END line of every key of every entry of the table, each |key| + 5 bytes
   (gestures_end_b_c.keys_total), so the whole run sends at most the model's mass. *)
Definition kw5s (xs : list (list byte)) : Z := zsum (map (fun x => Z.of_nat (length x) + 5) xs).
Lemma kw5s_nonneg : forall xs, 0 <= kw5s xs.
Proof. intros xs. apply zsum_map_nonneg. intros x. lia. Qed.
Lemma kw5s_keys : forall e, kw5s (gse_keys e) = gestures_end_b_c.keys_total (re_keys e).
Proof.
  intros e. unfold kw5s, gse_keys. induction (re_keys e) as [|k ks IH]; [reflexivity|].
  cbn [map fold_right]. change (gestures_end_b_c.keys_total (k :: ks)) with
    (Z.of_nat (length (gestures_end_b_c.key_text k)) + 5 + gestures_end_b_c.keys_total ks). lia.
Qed.
Definition rf_sum (es : list rentry) : Z := zsum (map (fun e => kw5s (gse_keys e)) es).
Lemma rf_sum_nonneg : forall es, 0 <= rf_sum es.
Proof. intros es. apply zsum_map_nonneg. intros e. apply kw5s_nonneg. Qed.
Lemma kw5s_nil : kw5s [] = 0.
Proof. reflexivity. Qed.
Lemma kw5s_cons : forall x xs, kw5s (x :: xs) = Z.of_nat (length x) + 5 + kw5s xs.
Proof. reflexivity. Qed.
Lemma rf_sum_nil : rf_sum [] = 0.
Proof. reflexivity. Qed.
Lemma rf_sum_cons : forall e es, rf_sum (e :: es) = kw5s (gse_keys e) + rf_sum es.
Proof. reflexivity. Qed.
Lemma rf_sum_mass : forall es, rf_sum es <= MASSe es.
Proof.
  induction es as [|e es IH]; [cbn [rf_sum MASSe map fold_right]; lia|].
  unfold rf_sum, MASSe in *. cbn [map fold_right].
  pose proof (ou_keys_total_mass e) as H. rewrite (kw5s_keys e). lia.
Qed.

(* one send, one gesture_end and one entry: the capacity never falls and grows to at most twice what is sent *)
Lemma ou_sl_cap_ge : forall c mx no cap len, 0 <= cap -> cap <= sl_cap c mx no cap len.
Proof.
  intros c mx no cap len Hc. unfold sl_cap.
  exact (proj2 (tp_send_line (sl_live c len) mx no cap len 0 RelayRunF.adr0 Hc)).
Qed.
Lemma ou_ge_cap_ge : forall c mx no cap XL, 0 <= cap -> cap <= ge_cap c mx no cap XL.
Proof.
  intros c mx no cap XL Hc. unfold ge_cap.
  pose proof (ou_sl_cap_ge c mx no cap XL Hc) as H1.
  pose proof (ou_sl_cap_ge (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5 ltac:(lia)) as H2. lia.
Qed.
Lemma ou_ge_cap_le : forall c mx no cap XL, 0 <= cap -> 0 <= XL ->
  ge_cap c mx no cap XL <= Z.max cap (2 * (no + (XL + 5))).
Proof.
  intros c mx no cap XL Hc HX. unfold ge_cap.
  pose proof (ev3_cap_le c mx no cap XL) as H1.
  pose proof (ev3_cap_le (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5) as H2.
  assert (Hn : sl_no c no XL <= no + XL) by (unfold sl_no; destruct (sl_live c XL); lia). lia.
Qed.
Lemma ou_ge_no : forall c no XL, 0 <= XL -> no <= ge_no c no XL <= no + (XL + 5).
Proof.
  intros c no XL HX. unfold ge_no, sl_no.
  destruct (sl_live c XL), (sl_live (sl_ctl c XL) 5); cbv beta iota; lia.
Qed.
(* gestures_end over one entry's keys *)
Lemma ou_gse_cap : forall xs c O mx no cap, 0 <= cap ->
  cap <= gse_cap (gse_run c O mx no cap xs) /\
  gse_cap (gse_run c O mx no cap xs) <= Z.max cap (2 * (no + kw5s xs)) /\
  no <= gse_no (gse_run c O mx no cap xs) <= no + kw5s xs.
Proof.
  induction xs as [|x xs IH]; intros c O mx no cap Hc.
  - cbn [gse_run gse_cap gse_no snd fst]. rewrite kw5s_nil. repeat split; lia.
  - cbn [gse_run]. rewrite kw5s_cons.
    set (XL := Z.of_nat (length x)) in *.
    assert (HX : 0 <= XL) by (unfold XL; lia).
    pose proof (ou_ge_cap_ge c mx no cap XL Hc) as G1.
    pose proof (ou_ge_cap_le c mx no cap XL Hc HX) as G2.
    pose proof (ou_ge_no c no XL HX) as G3.
    destruct (IH (ge_ctl c XL) (ge_O c O x) mx (ge_no c no XL) (ge_cap c mx no cap XL) ltac:(lia))
      as (I1 & I2 & I3).
    pose proof (kw5s_nonneg xs). repeat split; lia.
Qed.
(* relay_finish over the table *)
Lemma ou_rf_cap : forall es c O mx no cap, 0 <= cap ->
  cap <= gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run c O mx no cap es) /\
  gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run c O mx no cap es) <= Z.max cap (2 * (no + rf_sum es)) /\
  no <= gse_no (W_LLVMFuzzerTestOneInput_exit.lx_rf_run c O mx no cap es) <= no + rf_sum es.
Proof.
  induction es as [|e es IH]; intros c O mx no cap Hc.
  - cbn [W_LLVMFuzzerTestOneInput_exit.lx_rf_run gse_cap gse_no snd fst]. rewrite rf_sum_nil.
    repeat split; lia.
  - cbn [W_LLVMFuzzerTestOneInput_exit.lx_rf_run]. rewrite rf_sum_cons.
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
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.
(* ACfn_cf.fr_live_post with a8's OUT_MAX read as the parameter OM (this worktree's ACfn_cf.v:76 still carries the
   old constant; at OM := ACfn_cf.OUT_MAX the two texts are the same) *)
Definition fr_live_post3 (S S' : astate) (k : Z) : Prop :=
  blocks_bytes S' <= blocks_bytes S + ATABLE + OM /\ 0 <= k.

(* THE BYTES AT THE RETURN: the exit keeps the relay's table and g_out and frees everything else of the model, and
   g_out's final capacity is relay_finish's, which is at most twice the model's mass. *)
Lemma ou_exit_bytes : forall cx t m ly3 S3 rest ly' S' cap out,
  fr_LS3c B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  blocks_bytes S' <= blocks_bytes (c_S cx) + ATABLE + OM.
Proof.
  intros cx t m ly3 S3 rest ly' S' cap out (HLS & _) (U1 & U2 & U3 & U4) HP HP' Hcap Ht.
  destruct (ou_rf_cap (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) U1) as (R1 & R2 & _).
  rewrite <- Hcap in R1, R2.
  assert (Hc0 : 0 <= cap) by lia.
  assert (EX : XB cx m S3 = blocks_bytes (c_S cx) - bsum (input_blks cx) - bsum rest)
    by exact (xb_perm B cx m ly3 S3 rest HP).
  assert (EB' : blocks_bytes S' = bsum (input_blks cx) + ATABLE + cap + bsum rest).
  { rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP').
    repeat progress (rewrite ?bsum_app, ?bsum_cons). cbn [snd].
    rewrite (ev3_bsum_aout_eq cap out Hc0). lia. }
  pose proof (rf_sum_mass (lm_es m)) as Hrf.
  assert (Hmass : MASSe (lm_es m) <= MASS m).
  { unfold MASS. assert (0 <= pend_bytes m) by (apply zsum_map_nonneg; exact slot_pend_nonneg). lia. }
  unfold WMAX, OUT_MAX4, OPS_MAX in *. lia.
Qed.

(* ---- the AR text, W_LLVMFuzzerTestOneInput_exit.v:775-782 (= integ bb9dae5d905 :7750-7757) with ONE added
   premise, `cap = gse_cap (lx_rf_run ..)`: the arm passes relay_finish's FINAL capacity (a Theorem Labs lane 01:02Z).
   `out` stays free.  Named hypotheses: Ht (the loop's bound on t, from lregs_H / SEG_LATCH), Hk (0 <= k', which the
   AR text cannot give - its own comment flags k' as universal), HSURV (this fr_surv takes only the entry's and
   the return's layouts and states; LS cannot conclude it: it needs the entry's blocks to be the input, the
   entry's harness blocks and THIS rest, which LS forgets - see LS_exit_end3_x's note). ---- *)
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable XN_LIB : Z -> Z.
Lemma LS_exit_end3 : forall cx t m ly3 S3 rest ly' S' fpos k' C cap out,
  fr_LS3c B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX -> 0 <= k' ->
  fr_surv (c_ly cx) (c_S cx) ly' (stack_free_state 1 fpos S') ->
  fr_live_post3 (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) ly' (stack_free_state 1 fpos S') /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Proof.
  intros cx t m ly3 S3 rest ly' S' fpos k' C cap out HLS HOU HP HP' Hfr Hmo HC Hcap Ht Hk HSURV.
  assert (EB : blocks_bytes (stack_free_state 1 fpos S') = blocks_bytes S').
  { rewrite (blocks_bytes_bsum B ly' (stack_free_state 1 fpos S')), (blocks_bytes_bsum B ly' S').
    assert (EA : ablocks B ly' (stack_free_state 1 fpos S') = ablocks B ly' S') by reflexivity.
    rewrite EA. reflexivity. }
  split; [| split; [exact HSURV | exact I]].
  unfold fr_live_post3. rewrite EB. split; [| exact Hk].
  exact (ou_exit_bytes cx t m ly3 S3 rest ly' S' cap out HLS HOU HP HP' Hcap Ht).
Qed.

(* ---- the ARx text, W_LLVMFuzzerTestOneInput_exit_x.v:158-167 at integ bb9dae5d905, with the same ONE added
   premise and its NP conclusion DROPPED (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d), :218-219: the exit walk takes NP from the threaded
   room invariant; this proof never read NP).  0 <= k' is NOT a hypothesis: the journal premise gives it
   (YCbqG.v:249).  fr_surv stays a named hypothesis because LS cannot conclude it.  At a8's instance
   (ACfn_cf.v at a389032ec36 :94-98) its three clauses need, besides this text's premises,
   (i) the entry's blocks as the input, the entry's harness blocks and THIS rest:
       Permutation (ablocks B (c_ly cx) (c_S cx)) (input_blks cx ++ fr_hblks (c_W cx) (c_mem cx) ++ rest) -
       SEG_PRO holds it (LS_pro's premise, ReplyLS3c.v fr_LS3c_pro), every LS rule keeps the rest, but fr_LS3's
       rest is existential, so no cut carries it to X;
   (ii) the return's harness blocks as the kept table and g_out, fr_hblks W' mem' = (lm_G m, ATABLE) ::
       aout_blks cap out, and those blocks without duplicates - the exit walk holds what gives both
       (lx_end_of_ffexit_x, integ exit_x.v:4801-4830: the reset model's g_src / relay / g_out clauses HSL, HRL,
       HOUT of HM2, kept to W3 mem3 by KEEP, and HHB3 = NoDup and incl of fr_hblks W3 mem3). ---- *)
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable fr_surv_x : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate ->
  world segs -> (word -> option byte) -> Prop.
Lemma LS_exit_end3_x : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  fr_LS3c B cx t m ly3 S3 -> fr_OUT OM cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  fr_surv_x (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' ->
  fr_live_post3 (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv_x (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Proof.
  intros cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out HLS HOU HP HP' Hfr Hmo HC Hcap Ht HJ HSURV.
  assert (Hk : 0 <= k').
  { destruct HJ as (_ & _ & (memS & HAJ & _) & _).
    destruct HAJ as (_ & _ & _ & _ & _ & _ & _ & Hk0 & _). exact Hk0. }
  assert (EB : blocks_bytes (stack_free_state 1 fpos S') = blocks_bytes S').
  { rewrite (blocks_bytes_bsum B ly' (stack_free_state 1 fpos S')), (blocks_bytes_bsum B ly' S').
    assert (EA : ablocks B ly' (stack_free_state 1 fpos S') = ablocks B ly' S') by reflexivity.
    rewrite EA. reflexivity. }
  split; [| split; [exact HSURV | exact I]].
  unfold fr_live_post3. rewrite EB. split; [| exact Hk].
  exact (ou_exit_bytes cx t m ly3 S3 rest ly' S' cap out HLS HOU HP HP' Hcap Ht).
Qed.
End oexit.
