(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v; 605 of its 725 lines of code are new or changed and 474 lines of the source are left out. *)
(* The count half of LS v3, part 4: the per-class potential fr_POT, beside fr_LS3c (ReplyLS3c.v / ReplyLS3cArms.v, which
   stay as they are), for a Theorem Labs lane's FREE-PIECES row B1c (a Theorem Labs lane; a Theorem Labs lane 00:19Z, a Theorem Labs lane 00:23Z).
   proves no function (kind: invariant lemma).

   WHY.  fr_CNT bounds the counts of LS's rest only.  The model's own count in a class c (1..30) can grow with the input:
   the relay keys and the held texts (one of each per begin line a drain relays), and the pending texts.  A Theorem Labs lane's
   rl_prim_ok needs, at the PRE of every allocator call, ccnt_c c <= RL_PRIM c = 2^31 / class_size c, and
   ccnt24 <= 2^15 (L24); inside a callee the count also carries the callee's peak (ReplyTrPeakW.tr_peak_w), and a
   drain's peak in a class grows with the bytes it drains (one expected copy per line, one key per begin line).

   WHAT IS COUNTED.  At a cut point the model's blocks are
   - FIXED ones, at most 2 + 2 |es| + 4 |hs|: the table, per entry its line buffer and key array, per source its
     partial buffer and its three list vectors, the out buffer (pt_cls_model);
   - the PENDING texts, one per write op: at most npend m <= t (fr_CNT);
   - the LINE blocks: the relay keys, the held texts and the expected texts (pt_kc c m counts those of class c).
     Expected texts are only ever emptied at a cut point (check_no_loss leaves hl_recs E' = [], cnl_post; nothing else
     adds them), so they are counted only to keep the potential closed.
   The input's not-yet-relayed bytes are the MASS: pend_bytes m (the pending bytes past the read offset) plus the
   relay's unfinished lines |re_U| (pt_mass m).

   THE POTENTIAL.  For every class c:
     fr_POT:   pt_s c * pt_kc c m + pt_v c * pt_mass m <= pt_v c * (WRITE_MAX * t)
   with pt_s c = max 21 (lo c) (lo c the least request of class c, PresetRoom.lo; 21 the least begin line with its
   NUL, SlotReads.gesture_begin_len) and pt_v c = 42 (c = 1), 4 (c = 2), 3 (c >= 3).
   - a write op adds at most WRITE_MAX = 65,535 bytes of mass (wr_n < 65,536) and no line block: + pt_v c * WRITE_MAX;
   - a drain turns mass into lines: the lines with their NULs and the new re_U are at most the old re_U and the
     pending bytes (TOT + U' <= U + P, as fr_LS3_drain_step_p's HMASS), so the mass falls by TOT; a begin line l with
     a key x of class c adds at most one relay key and one held text, both x, and pt_s c <= |l| + 1 (21 <= |l| + 1 and
     lo c <= |x| + 1 <= |l| + 1); so pt_s c * (line blocks added) <= 2 * TOT <= pt_v c * TOT (pt_v c >= 2 suffices);
   - a remove frees a source and an entry: both terms fall; every other rule keeps the sources and the entries.
   pt_v c / pt_s c is the callee room the potential leaves per byte of mass.  It covers both
   - the drain's and the remove's peak as ReplyTrPeakCnt.v bounds it, lo c * peak <= 5 lo c + 2 * pair_bytes
     (2 / lo c per byte: pt_v 1 >= 42, pt_v 2 >= 3, pt_v c >= 2), and
   - check_no_loss after a drain (its lines' expected copies, 1 / lo c per byte, and two keys per begin line,
     2 / max 21 (lo c) per byte: pt_v 1 >= 23, pt_v 2 >= 4, pt_v c >= 3).

   THE CUT POINT (fr_LS3cp_cls_cut, fr_LS3cp_cls_room, fr_LS3cp_c24_room): with fr_CNT's rest bound CLS0 and the input
   block,
     pt_s c * (cnt_cls c (ablocks B ly S) - (CLS0 + 1 + 18 + 2 |es| + t)) + pt_v c * pt_mass m <= pt_v c * WRITE_MAX * t,
   so at t <= 511 and |es| <= 16 a callee whose class-c peak R has pt_s c * R <= pt_v c * pt_mass m leaves
   cnt_cls c (ablocks B ly S) + R + MARGIN c <= RL_PRIM c, MARGIN c >= 30,055 for c in 1..30 (MARGIN_table), and
   cnt24 (ablocks B ly S) + R + 15,083 <= 2^15 (MARGIN24_val).  fr_LS3cp_cls_pair is the form ReplyTrPeakCnt.v's
   Hcls takes (cnt_cls c <= RL_PRIM c - 5 - 2 * X / lo c for any X <= pt_mass m, pt_pair_le_mass: a drained pair's
   pending stream and re_U are at most pt_mass m); fr_LS3cp_cnt24_cut gives cnt24 <= 2^15 - 15,083. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv SlotDrain3Aux SlotPass2Aux
  relay_remove_b_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).
Local Notation WRITE_MAX := SlotInv.WRITE_MAX.

(* ================================================================== the weights *)
(* the least byte cost of a line block of class c: its begin line with the NUL (>= 21) and its own request (>= lo c) *)
Definition pt_s (c : Z) : Z := Z.max 21 (PresetRoom.lo c).
(* the mass weight: at least 2 (a begin line makes two line blocks); above it, the callee room per byte of mass *)
Definition pt_v (c : Z) : Z := if c =? 1 then 42 else if c =? 2 then 4 else 3.
(* a text x as a block (|x| + 1 bytes, its NUL) in class c *)
Definition pt_w (c : Z) (x : list Z) : Z := if PresetRoom.in_cls c (Z.of_nat (length x) + 1) then 1 else 0.
Definition pt_tc (c : Z) (xs : list (list Z)) : Z := zsum (map (pt_w c) xs).
(* the line blocks of class c: an entry's keys, a source's expected and held texts *)
Definition pt_ekc (c : Z) (e : rentry) : Z := pt_tc c (drain_b_c.keys_texts (re_keys e)).
Definition pt_skc (c : Z) (o : option hsrc) : Z :=
  match o with Some h => pt_tc c (texts (hs_expected h)) + pt_tc c (texts (hs_held h)) | None => 0 end.
Definition pt_kc (c : Z) (m : lmod) : Z := zsum (map (pt_ekc c) (lm_es m)) + zsum (map (pt_skc c) (lm_hs m)).
(* the mass: the pending bytes past the read offset, and the relay's unfinished lines *)
Definition pt_eu (e : rentry) : Z := Z.of_nat (length (re_U e)).
Definition pt_mass (m : lmod) : Z := pend_bytes m + zsum (map pt_eu (lm_es m)).

Lemma pt_s_ge : forall c, 21 <= pt_s c.
Proof. intros c. unfold pt_s. lia. Qed.
Lemma pt_v_range : forall c, 2 <= pt_v c <= 42.
Proof. intros c. unfold pt_v. destruct (c =? 1); [lia|]. destruct (c =? 2); lia. Qed.
Lemma pt_w_range : forall c x, 0 <= pt_w c x <= 1.
Proof. intros c x. unfold pt_w. destruct (PresetRoom.in_cls c _); lia. Qed.
Lemma pt_tc_nonneg : forall c xs, 0 <= pt_tc c xs.
Proof. intros c xs. unfold pt_tc. apply zsum_map_nonneg. intros x. apply pt_w_range. Qed.
Lemma pt_ekc_nonneg : forall c e, 0 <= pt_ekc c e.
Proof. intros c e. apply pt_tc_nonneg. Qed.
Lemma pt_skc_nonneg : forall c o, 0 <= pt_skc c o.
Proof.
  intros c [h|]; cbn [pt_skc]; [|lia].
  pose proof (pt_tc_nonneg c (texts (hs_expected h))). pose proof (pt_tc_nonneg c (texts (hs_held h))). lia.
Qed.
Lemma pt_eu_nonneg : forall e, 0 <= pt_eu e.
Proof. intros e. unfold pt_eu. lia. Qed.
Lemma pt_pend_nonneg : forall o, 0 <= slot_pend o.
Proof. intros [h|]; cbn [slot_pend]; lia. Qed.

(* ================================================================== list helpers *)
Lemma pt_sum_incl : forall {X} (f : X -> Z) A Bl, (forall x, 0 <= f x) -> List.NoDup A -> incl A Bl ->
  zsum (map f A) <= zsum (map f Bl).
Proof.
  intros X f A. induction A as [|a A IH]; intros Bl Hf Hnd Hinc.
  - cbn [map fold_right]. apply zsum_map_nonneg. exact Hf.
  - apply NoDup_cons_iff in Hnd as [Ha Hnd].
    assert (Hin : In a Bl) by (apply Hinc; left; reflexivity).
    destruct (in_split _ _ Hin) as (l1 & l2 & ->).
    assert (Hi : incl A (l1 ++ l2)).
    { intros x Hx. assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hinc; right; exact Hx).
      apply in_app_iff in Hx' as [H1 | [H2 | H3]]; apply in_app_iff;
        [left; exact H1 | subst x; contradiction | right; exact H3]. }
    specialize (IH (l1 ++ l2) Hf Hnd Hi).
    rewrite (fr_sum_perm _ f (l1 ++ a :: l2) (a :: l1 ++ l2) (Permutation_sym (Permutation_middle l1 l2 a))).
    cbn [map fold_right]. lia.
Qed.
Lemma pt_cls_le_len : forall c l, cnt_cls c l <= Z.of_nat (length l).
Proof.
  intros c l. rewrite cnt_cls_ccnt. unfold PresetRoom.ccnt.
  pose proof (dr3_filter_len (PresetRoom.in_cls c) (map snd l)) as H. rewrite length_map in H. lia.
Qed.
Lemma pt_cls_opt : forall c (b : bool) (a n : Z), cnt_cls c (if b then [] else [(a, n)]) <= 1.
Proof.
  intros c b a n. destruct b; [rewrite cnt_cls_nil; lia|].
  rewrite cnt_cls_cons, cnt_cls_nil. destruct (PresetRoom.in_cls c n); lia.
Qed.
Lemma pt_cls_concat : forall c {X} (f : X -> list (Z * Z)) (g : X -> Z) l,
  (forall x, cnt_cls c (f x) <= g x) -> cnt_cls c (concat (map f l)) <= zsum (map g l).
Proof.
  intros c X f g l H. induction l as [|x l IH]; [rewrite cnt_cls_nil; cbn; lia|].
  cbn [map concat fold_right]. rewrite cnt_cls_app. specialize (H x). lia.
Qed.
Lemma pt_zsum_plus : forall {X} (f g : X -> Z) l,
  zsum (map (fun x => f x + g x) l) = zsum (map f l) + zsum (map g l).
Proof. intros X f g l. induction l as [|x l IH]; cbn [map fold_right]; [reflexivity|]. rewrite IH. lia. Qed.
Lemma pt_zsum_add : forall {X} (k : Z) (f : X -> Z) l,
  zsum (map (fun x => k + f x) l) = k * Z.of_nat (length l) + zsum (map f l).
Proof. intros X k f l. induction l as [|x l IH]; cbn [map fold_right length]; [lia|]. rewrite IH. lia. Qed.
(* a list's texts and an entry's keys, as blocks: their class count is pt_tc of the texts *)
Lemma pt_cls_recs : forall c (rs : list (Z * list byte)),
  cnt_cls c (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) rs) =
  pt_tc c (map (fun r : Z * list byte => bzs (snd r)) rs).
Proof.
  intros c rs. unfold pt_tc. induction rs as [|r rs IH]; [reflexivity|]. cbn [map fold_right].
  rewrite cnt_cls_cons, IH. unfold pt_w. rewrite SlotReads.bzs_length. reflexivity.
Qed.
Lemma pt_cls_keys : forall c (ks : list (Z * list byte * list byte)),
  cnt_cls c (map (fun k => (gestures_end_b_c.key_addr k, Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) ks) =
  pt_tc c (drain_b_c.keys_texts ks).
Proof.
  intros c ks. unfold pt_tc, drain_b_c.keys_texts. induction ks as [|k ks IH]; [reflexivity|]. cbn [map fold_right].
  rewrite cnt_cls_cons, IH. unfold pt_w. rewrite SlotReads.bzs_length. reflexivity.
Qed.

(* ================================================================== the model's class count *)
Lemma pt_cls_alist : forall c l, cnt_cls c (alist_blks l) <= 1 + pt_tc c (texts l) /\
  cnt_cls c (alist_blks l) <= 1 + hl_n l.
Proof.
  intros c l. unfold alist_blks. rewrite cnt_cls_app.
  pose proof (pt_cls_opt c (hl_cap l =? 0) (hl_v l) (AREC * hl_cap l)) as V.
  pose proof (pt_cls_le_len c (map (fun r : Z * list byte => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l))) as L.
  rewrite length_map in L. rewrite pt_cls_recs in L |- *. unfold texts, hl_n. lia.
Qed.
Lemma pt_cls_entry : forall c e, cnt_cls c (aentry_blks e) <= 2 + pt_ekc c e.
Proof.
  intros c e. unfold aentry_blks, pt_ekc. rewrite !cnt_cls_app, pt_cls_keys.
  pose proof (pt_cls_opt c (re_cap e =? 0) (re_buf e) (re_cap e)).
  pose proof (pt_cls_opt c (re_hp e =? 0) (re_hp e) (re_kh e)). lia.
Qed.
Lemma pt_cls_slot : forall c o, cnt_cls c (slot_blks o) <= 4 + slot_npend o + pt_skc c o.
Proof.
  intros c [h|]; cbn [slot_blks slot_npend pt_skc]; [|rewrite cnt_cls_nil; lia].
  unfold asrc_blks. rewrite cnt_cls_cons, !cnt_cls_app.
  destruct (pt_cls_alist c (hs_pending h)) as (_ & P).
  destruct (pt_cls_alist c (hs_expected h)) as (E & _).
  destruct (pt_cls_alist c (hs_held h)) as (H & _).
  destruct (PresetRoom.in_cls c APARTIAL); lia.
Qed.
(* the model: its fixed blocks (table, per entry 2, per slot 4, out buffer), its pending texts, its line blocks *)
Lemma pt_cls_model : forall c m,
  cnt_cls c (model_blks m) <=
    2 + 2 * Z.of_nat (length (lm_es m)) + 4 * Z.of_nat (length (lm_hs m)) + npend m + pt_kc c m.
Proof.
  intros c m. unfold model_blks, pt_kc, npend. rewrite cnt_cls_cons, !cnt_cls_app.
  pose proof (pt_cls_concat c aentry_blks (fun e => 2 + pt_ekc c e) (lm_es m) (pt_cls_entry c)) as CE.
  assert (HS : forall o, cnt_cls c (slot_blks o) <= 4 + (slot_npend o + pt_skc c o))
    by (intros o; pose proof (pt_cls_slot c o); lia).
  pose proof (pt_cls_concat c slot_blks (fun o => 4 + (slot_npend o + pt_skc c o)) (lm_hs m) HS) as CS.
  rewrite pt_zsum_add in CE. rewrite pt_zsum_add in CS.
  rewrite (pt_zsum_plus slot_npend (pt_skc c)) in CS.
  assert (CO : cnt_cls c (aout_blks (lm_cap m) (lm_out m)) <= 1)
    by (unfold aout_blks; apply pt_cls_opt).
  destruct (PresetRoom.in_cls c ATABLE); lia.
Qed.

(* ================================================================== the drain's new keys *)
(* a begin line l with a key x of class c costs at least pt_s c bytes with its NUL *)
Lemma pt_s_line : forall c l x, gesture l = Some (GBegin, x) ->
  PresetRoom.in_cls c (Z.of_nat (length x) + 1) = true -> pt_s c <= Z.of_nat (length l) + 1.
Proof.
  intros c l x G Hc. pose proof (SlotReads.gesture_begin_len l x G) as L1. pose proof (dr3_gesture_sub l GBegin x G) as L2.
  pose proof (PresetRoom.lo_le c (Z.of_nat (length x) + 1) ltac:(lia) Hc) as L3. unfold pt_s. lia.
Qed.
(* the keys a drain's lines can add, in class c: pt_s c each, within the lines' bytes with their NULs *)
Lemma pt_nk : forall c Ls, pt_s c * pt_tc c (dr3_nk Ls) <= Z.of_nat (length (with_nul Ls)).
Proof.
  intros c Ls. pose proof (pt_s_ge c) as Hs. induction Ls as [|l Ls IH].
  - unfold dr3_nk, pt_tc. cbn [map concat fold_right]. rewrite RelayCap.with_nul_nil_len. lia.
  - unfold dr3_nk, pt_tc in *. cbn [map concat]. rewrite map_app, zsum_app, RelayCap.with_nul_cons_len.
    assert (Hb : dr3_bk l = match gesture l with Some (GBegin, x) => [x] | _ => [] end) by reflexivity.
    rewrite Hb. rewrite Z.mul_add_distr_l.
    destruct (gesture l) as [[[|] x]|] eqn:G; cbv beta iota; cbn [map fold_right].
    + assert (Hw : pt_w c x = 0 \/ (pt_w c x = 1 /\ PresetRoom.in_cls c (Z.of_nat (length x) + 1) = true))
        by (unfold pt_w; destruct (PresetRoom.in_cls c (Z.of_nat (length x) + 1)); [right; split | left]; reflexivity).
      destruct Hw as [Hw | (Hw & Ec)]; rewrite Hw.
      * lia.
      * pose proof (pt_s_line c l x G Ec). lia.
    + lia.
    + lia.
Qed.

(* ================================================================== the arithmetic of a drain's step *)
Lemma pt_arith : forall s v k k' ms ms' nk tot, 0 <= s -> 2 <= v -> 0 <= tot ->
  k' <= k + 2 * nk -> s * nk <= tot -> ms' + tot <= ms -> s * k' + v * ms' <= s * k + v * ms.
Proof.
  intros s v k k' ms ms' nk tot Hs Hv Ht Hk Hn Hm.
  assert (A1 : s * k' <= s * (k + 2 * nk)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (A2 : v * ms' <= v * (ms - tot)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (A3 : 2 * tot <= v * tot) by (apply Z.mul_le_mono_nonneg_r; lia).
  rewrite Z.mul_add_distr_l in A1. rewrite Z.mul_sub_distr_l in A2. lia.
Qed.

(* the budget of d write ops in class c *)
Lemma pt_wm_nonneg : forall c d, 0 <= d -> 0 <= pt_v c * (WRITE_MAX * d).
Proof.
  intros c d Hd. pose proof (pt_v_range c). apply Z.mul_nonneg_nonneg; [lia|].
  apply Z.mul_nonneg_nonneg; [unfold SlotInv.WRITE_MAX; lia | exact Hd].
Qed.

Section pot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the meter (KF-COUNT): a Variable, implicit, so the arm rules' callers keep their argument lists (it is read off
   their mo_le arguments).  The rules below never read it: ReplyLS3cArms.v's twins sit at ameter_triv, where the
   mo_le premise is True, so they get I. *)
Context {MT : ameter_ops}.

(* ================================================================== the potential and LS v3 with it *)
Definition fr_POT (cx : lfcx) (t : Z) (m : lmod) : Prop :=
  forall c, pt_s c * pt_kc c m + pt_v c * pt_mass m <= pt_v c * (WRITE_MAX * t).
Definition fr_LS3cp (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  fr_LS3c B cx t m ly S /\ fr_POT cx t m.

(* ------------------------------------------------------------------ fr_POT's step and keep rules *)
Lemma fr_POT_step : forall cx t t' m m',
  (forall c, pt_s c * pt_kc c m' + pt_v c * pt_mass m' <=
             pt_s c * pt_kc c m + pt_v c * pt_mass m + pt_v c * (WRITE_MAX * (t' - t))) ->
  fr_POT cx t m -> fr_POT cx t' m'.
Proof.
  intros cx t t' m m' H HP c. specialize (H c). specialize (HP c).
  assert (E : pt_v c * (WRITE_MAX * t') = pt_v c * (WRITE_MAX * t) + pt_v c * (WRITE_MAX * (t' - t))) by ring.
  lia.
Qed.
Lemma fr_POT_keep : forall cx t t' m m',
  pt_mass m' <= pt_mass m -> (forall c, pt_kc c m' <= pt_kc c m) -> t <= t' -> fr_POT cx t m -> fr_POT cx t' m'.
Proof.
  intros cx t t' m m' Hm Hk Ht. apply fr_POT_step. intros c.
  pose proof (pt_s_ge c). pose proof (pt_v_range c).
  assert (A1 : pt_s c * pt_kc c m' <= pt_s c * pt_kc c m) by (apply Z.mul_le_mono_nonneg_l; [lia | apply Hk]).
  assert (A2 : pt_v c * pt_mass m' <= pt_v c * pt_mass m) by (apply Z.mul_le_mono_nonneg_l; lia).
  pose proof (pt_wm_nonneg c (t' - t) ltac:(lia)) as A3.
  lia.
Qed.
Lemma fr_POT_same : forall cx t t' m m',
  lm_hs m' = lm_hs m -> lm_es m' = lm_es m -> t <= t' -> fr_POT cx t m -> fr_POT cx t' m'.
Proof.
  intros cx t t' m m' E1 E2 Ht. apply fr_POT_keep; [| intros c | exact Ht].
  - unfold pt_mass, pend_bytes. rewrite E1, E2. lia.
  - unfold pt_kc. rewrite E1, E2. lia.
Qed.
Lemma fr_POT_upd : forall cx t t' m m' i f,
  lm_hs m' = upd_hs i f (lm_hs m) -> lm_es m' = lm_es m ->
  (forall h, hs_pending (f h) = hs_pending h /\ hs_off (f h) = hs_off h /\ hs_held (f h) = hs_held h /\
     hs_expected (f h) = hs_expected h) ->
  t <= t' -> fr_POT cx t m -> fr_POT cx t' m'.
Proof.
  intros cx t t' m m' i f E1 E2 Hf Ht. apply fr_POT_keep; [| intros c | exact Ht].
  - unfold pt_mass, pend_bytes. rewrite E1, E2, (upd_hs_map slot_pend); [lia|].
    intros h. destruct (Hf h) as (P1 & P2 & _). cbn [slot_pend]. rewrite P1, P2. reflexivity.
  - unfold pt_kc. rewrite E1, E2, (upd_hs_map (pt_skc c)); [lia|].
    intros h. destruct (Hf h) as (_ & _ & P3 & P4). cbn [pt_skc]. rewrite P3, P4. reflexivity.
Qed.

(* ================================================================== fr_LS3cp's rules (ReplyLS3c.v) *)
Lemma fr_LS3cp_head_nout : forall cx t m ly S, fr_LS3cp cx t m ly S -> fr_LS3cp cx t (lm_clear_O m) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3c_head_nout B cx t m ly S H1)|].
  apply (fr_POT_same cx t t m); [reflexivity | reflexivity | lia | exact H2].
Qed.
Lemma fr_LS3cp_head_skip : forall cx t m ly S,
  0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> fr_LS3cp cx t m ly S -> fr_LS3cp cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof.
  intros cx t m ly S A1 A2 A3 A4 A5 A6 (H1 & H2).
  split; [exact (fr_LS3c_head_skip B cx t m ly S A1 A2 A3 A4 A5 A6 H1)|].
  apply (fr_POT_same cx t (t + 1) m); [reflexivity | reflexivity | lia | exact H2].
Qed.
Lemma fr_LS3cp_close : forall cx t m i ly S, fr_LS3cp cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_LS3cp cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S (H1 & H2) Hp. split; [exact (fr_LS3c_close B cx t m i ly S H1 Hp)|].
  apply (fr_POT_upd cx t (t + 1) m _ i upd_closed); [reflexivity | reflexivity | intros h; repeat split | lia
    | exact H2].
Qed.
Lemma fr_LS3cp_eintr : forall cx t m i ly S, fr_LS3cp cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  fr_LS3cp cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S (H1 & H2) Hp. split; [exact (fr_LS3c_eintr B cx t m i ly S H1 Hp)|].
  apply (fr_POT_upd cx t (t + 1) m _ i upd_eintr); [reflexivity | reflexivity | intros h; repeat split | lia
    | exact H2].
Qed.
Lemma fr_LS3cp_sendmax : forall cx t m ly S, fr_LS3cp cx t m ly S ->
  fr_LS3cp cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3c_sendmax B cx t m ly S H1)|].
  apply (fr_POT_same cx t (t + 1) m); [reflexivity | reflexivity | lia | exact H2].
Qed.
Lemma fr_LS3cp_default : forall cx t m ly S, fr_LS3cp cx t m ly S ->
  fr_LS3cp cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3c_default B cx t m ly S H1)|].
  apply (fr_POT_same cx t (t + 1) m); [reflexivity | reflexivity | lia | exact H2].
Qed.
Lemma fr_LS3cp_write_skip : forall cx t m ly S, fr_LS3cp cx t m ly S ->
  fr_LS3cp cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3c_write_skip B cx t m ly S H1)|].
  apply (fr_POT_same cx t (t + 1) m); [reflexivity | reflexivity | lia | exact H2].
Qed.
Lemma fr_LS3cp_add_none : forall cx t m ly S, fr_LS3cp cx t m ly S -> fr_LS3cp cx (t + 1) (ad_none m) ly S.
Proof.
  intros cx t m ly S (H1 & H2). split; [exact (fr_LS3c_add_none B cx t m ly S H1)|].
  apply (fr_POT_same cx t (t + 1) m); [reflexivity | reflexivity | lia | exact H2].
Qed.
(* op_add: the new source (three empty lists, nothing pending) and the new entry (no keys, re_U []) add nothing *)
Lemma fr_LS3cp_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3cp cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_LS3cp cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' (H1 & H2) Hf HP'.
  split; [exact (fr_LS3c_add_open B cx t m i q pj ev ly S ly' S' H1 Hf HP')|].
  destruct H1 as ((rest & e0 & _ & _ & _ & _ & Hl & _) & _).
  destruct (oa_first_free (lm_hs m) i Hl Hf) as (_ & Hi).
  assert (Zs : forall (g : option hsrc -> Z), zsum (map g (lm_hs (ad_open m i q pj ev))) + g None =
                 zsum (map g (lm_hs m)) + g (Some (oa_new_src (100 + lm_nfd m) q pj)))
    by (intros g; rewrite ad_open_hs; exact (set_nth_zsum g i _ None (lm_hs m) Hi)).
  apply (fr_POT_keep cx t (t + 1) m); [| intros c | lia | exact H2].
  - unfold pt_mass, pend_bytes. rewrite ad_open_es, map_app, zsum_app. pose proof (Zs slot_pend) as Z1.
    assert (P1 : slot_pend (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (N1 : slot_pend None = 0) by reflexivity.
    assert (U1 : pt_eu (ra_new (100 + lm_nfd m)) = 0) by reflexivity.
    cbn [map fold_right]. lia.
  - unfold pt_kc. rewrite ad_open_es, map_app, zsum_app. pose proof (Zs (pt_skc c)) as Z1.
    assert (P1 : pt_skc c (Some (oa_new_src (100 + lm_nfd m) q pj)) = 0) by reflexivity.
    assert (N1 : pt_skc c None = 0) by reflexivity.
    assert (K1 : pt_ekc c (ra_new (100 + lm_nfd m)) = 0) by reflexivity.
    cbn [map fold_right]. lia.
Qed.
(* the write's push: at most WRITE_MAX new pending bytes (wr_n < 65,536), no line block *)
Lemma fr_LS3cp_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS3cp cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  fr_LS3cp cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ly S ly' S' ev (H1 & H2) Hpk Hn Hrecs Hcap Hv Hlp.
  split; [exact (fr_LS3c_write_push B cx t m si h l' d ly S ly' S' ev H1 Hpk Hn Hrecs Hcap Hv Hlp)|].
  destruct Hpk as (_ & _ & Hh).
  pose proof (nth_some_error _ _ _ Hh) as Hi.
  pose proof (wr_facts cx m Hn) as ((W1 & W2) & Wx).
  assert (Hk1 : wr_k1 cx m <= c_n cx) by (unfold wr_k1; destruct (lm_k m + 1 <? c_n cx); lia).
  destruct (wr_n_range cx m Hk1) as ((Wn0 & Wn1) & _).
  set (h' := set_pending h l').
  assert (Zs : forall (g : option hsrc -> Z), zsum (map g (lm_hs (wr_push m (wr_k2 cx m) si h' ev))) + g (Some h) =
                 zsum (map g (lm_hs m)) + g (Some h'))
    by (intros g; exact (set_nth_zsum g si (Some h') (Some h) (lm_hs m) Hi)).
  assert (Hb1 : hl_bytes l' = hl_bytes (hs_pending h) + Z.of_nat (length (wr_x cx m)))
    by (unfold hl_bytes; rewrite Hrecs, map_app, zsum_app; cbn; lia).
  apply (fr_POT_step cx t (t + 1) m); [intros c | exact H2].
  pose proof (pt_s_ge c) as Hs. pose proof (pt_v_range c) as Hv'.
  assert (EK : pt_kc c (wr_push m (wr_k2 cx m) si h' ev) = pt_kc c m).
  { unfold pt_kc. pose proof (Zs (pt_skc c)) as Z1.
    assert (E1 : pt_skc c (Some h') = pt_skc c (Some h)) by reflexivity.
    assert (E2 : lm_es (wr_push m (wr_k2 cx m) si h' ev) = lm_es m) by reflexivity. rewrite E2. lia. }
  assert (EM : pt_mass (wr_push m (wr_k2 cx m) si h' ev) <= pt_mass m + WRITE_MAX).
  { unfold pt_mass, pend_bytes. pose proof (Zs slot_pend) as Z1.
    assert (E1 : slot_pend (Some h') = Z.max 0 (hl_bytes l' - hs_off h)) by reflexivity.
    assert (E0 : slot_pend (Some h) = Z.max 0 (hl_bytes (hs_pending h) - hs_off h)) by reflexivity.
    assert (E2 : lm_es (wr_push m (wr_k2 cx m) si h' ev) = lm_es m) by reflexivity. rewrite E2.
    unfold SlotInv.WRITE_MAX. lia. }
  rewrite EK. replace (t + 1 - t) with 1 by lia. rewrite Z.mul_1_r.
  assert (A : pt_v c * pt_mass (wr_push m (wr_k2 cx m) si h' ev) <= pt_v c * (pt_mass m + WRITE_MAX))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  rewrite Z.mul_add_distr_l in A. lia.
Qed.
(* the first head: nothing pending, no key, no text, re_U [] *)
Lemma pt_pro_zero : forall q T' pj c0 O cap out c,
  pt_kc c (ls_pro_m q T' pj c0 O cap out) = 0 /\ pt_mass (ls_pro_m q T' pj c0 O cap out) = 0.
Proof. intros. split; reflexivity. Qed.
Lemma fr_LS3cp_pro : forall XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S,
  lf_base B ameter_triv XM_LIB RLO RHI ACfn_cf.fr_live_pre G_fr cx ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     xcnt_pre B cx T0 cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_LS3cp cx 0 (ls_pro_m q T' pj c O cap out) ly S.
Proof.
  intros XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S Hb Hx.
  split; [exact (fr_LS3c_pro B XM_LIB RLO RHI G_fr cx q T' pj c O cap out ly S Hb Hx)|].
  intros k. destruct (pt_pro_zero q T' pj c O cap out k) as (E1 & E2). rewrite E1, E2. lia.
Qed.

(* ================================================================== fr_LS3cp's arm rules (ReplyLS3cArms.v) *)
(* remove: the source's slot and the entry go; every other source and entry stays *)
Lemma fr_LS3cp_rm_step_p : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  fr_LS3cp cx t m ly0 S0 ->
  mo_le MT S0 S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
                 W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1) +
                 W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
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
  fr_LS3cp cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 (H1 & H2) Hmo HRI Hat Hrr Hcn
    Hcs Hfr Hpos H14 Hoffc.
  split; [exact (fr_LS3c_rm_step_p B cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 H1 I
    HRI Hat Hrr Hcn Hcs Hfr Hpos H14 Hoffc)|].
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  pose proof (nth_some_error _ _ _ Hh) as Hi.
  set (m' := rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2).
  assert (Zs : forall g : option hsrc -> Z, zsum (map g (lm_hs m')) + g (Some h) = zsum (map g (lm_hs m)) + g None)
    by (intros g; exact (rm3_set_zsum _ g si None (Some h) (lm_hs m) Hi)).
  assert (Ze : forall g : rentry -> Z, zsum (map g (lm_es m')) + g (rm_ent m j0) = zsum (map g (lm_es m))).
  { intros g. pose proof (fr_sum_perm _ g _ _ (fr_remove_perm _ (lm_es m) j0 relay_remove_b_c.no_entry Hj0)) as Pe.
    cbn [map fold_right] in Pe. change (lm_es m') with (relay_remove_b_c.remove_at j0 (lm_es m)).
    unfold rm_ent. lia. }
  apply (fr_POT_keep cx t (t + 1) m m'); [| intros c | lia | exact H2].
  - unfold pt_mass, pend_bytes. pose proof (Zs slot_pend) as Z1. pose proof (Ze pt_eu) as Z2.
    assert (N1 : slot_pend None = 0) by reflexivity.
    pose proof (pt_pend_nonneg (Some h)). pose proof (pt_eu_nonneg (rm_ent m j0)). lia.
  - unfold pt_kc. pose proof (Zs (pt_skc c)) as Z1. pose proof (Ze (pt_ekc c)) as Z2.
    assert (N1 : pt_skc c None = 0) by reflexivity.
    pose proof (pt_skc_nonneg c (Some h)). pose proof (pt_ekc_nonneg c (rm_ent m j0)). lia.
Qed.
(* the event: the sources and the entries stay *)
Lemma fr_LS3cp_event_step_p : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS3cp cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_LS3cp cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q (H1 & H2) HE M1 M2 M3 Hk HO Hc0 Hm HRR Hf.
  split; [exact (fr_LS3c_event_step_p B cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q H1 HE I I I Hk HO Hc0 Hm HRR Hf)|].
  apply (fr_POT_same cx t (t + 1) m); [reflexivity | reflexivity | lia | exact H2].
Qed.

(* the drain: the drained source's pending bytes and the entry's old re_U become lines (TOT bytes with their NULs) and
   the new re_U; the keys and held texts it adds are within the lines' begin keys (dr_post :958-959, cnl_post) *)
Lemma fr_LS3cp_drain_step_p : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3cp cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
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
  fr_LS3cp cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' (HLS & HPOT) Hpick Hj M1 M2
    HPd Hpend HEq HHq Hcnl Hh'' Hat HRI Hfd Heof Hepre Hkh Hhpre Hhn Hcap0 Hcap' Hepost Hhpost Hdpost Hcpost.
  split; [exact (fr_LS3c_drain_step_p B cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HLS Hpick
    Hj I I HPd Hpend HEq HHq Hcnl Hh'' Hat HRI Hfd Heof Hepre Hkh Hhpre Hhn Hcap0 Hcap' Hepost Hhpost Hdpost Hcpost)|].
  clear HLS M1 M2 HPd Hcnl.
  subst E H h''.
  pose proof Hpick as (_ & Hsi & Hh).
  destruct Hat as (Hk & HO & _).
  destruct (dr3_rinv cx t m si h j HRI Hpick Hj Hfd Heof)
    as ((Hsk & HskU) & Hsk01 & _ & _ & Hexp & _ & _ & _ & Hoff & _).
  destruct Hdpost as (HU' & Hka' & Hoff1 & Hmap & Hheld & HnE1).
  replace (Z.of_nat (length (lm_O m))) with 0 in HU' by (rewrite HO; reflexivity).
  unfold dr_fin in HU'.
  set (e := nth j (lm_es m) dr_e0) in *.
  assert (Hej : nth_error (lm_es m) j = Some e) by (unfold e; apply nth_error_nth'; exact Hj).
  pose proof (nth_some_error _ _ _ Hh) as Hhi.
  destruct Hepre as (Hce & HU & HUz & Hkh8 & H14).
  destruct Hepost as (Hce' & Hkh' & Hnd' & Hss').
  destruct Hcpost as (HrE' & HcE' & HndH' & HtH' & HcH' & HnH').
  set (Ls := dr_lines h) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))).
  set (P := Z.of_nat (length (pending_stream h))).
  set (U := Z.of_nat (length (re_U e))).
  set (U' := Z.of_nat (length (re_U e'))).
  pose proof (dr3_lines h) as (HLn & _ & HZr & HCB). fold Ls in HLn, HZr, HCB.
  assert (HTOT0 : 0 <= TOT) by (unfold TOT; lia).
  (* ---- the relay's mass: TOT + U' <= U + P (fr_LS3_drain_step_p's HMASS) ---- *)
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live (lm_c m) h) (lm_mx m) 0 (lm_cap m) e h HJ
                (dr3_pok 0 (lm_cap m) e h Hoff Hhpre) Hce0) as Hno.
  change (lines (hs_state h) (bzs (pending_stream h))) with Ls in Hno. fold TOT in Hno.
  assert (Hkh168 : 168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e).
  { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & E2) | (E1 & E2)].
    - rewrite E1, E2. cbn [length Z.of_nat Z.eqb]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
  destruct (ls3_drain_fin (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) e h (proj1 Hhpre) Hkh168) as (RM & _).
  rewrite <- HU' in RM. rewrite SlotReads.bzs_length in RM. fold U' in RM.
  assert (HMASS : TOT + U' <= U + P) by (unfold U, P in *; lia).
  clear RM Hno.
  (* ---- the expected texts after the drain are the lines; the held texts after check_no_loss ---- *)
  assert (HT : texts (hs_expected h1) = Ls).
  { unfold texts. rewrite <- (map_map snd bzs). rewrite Hmap, Hexp. cbn [map app]. exact (fr_bzs_lines _ HZr). }
  rewrite HT, Hheld in HtH'.
  (* ---- the mass after the step ---- *)
  set (h'' := set_exp_held h1 E' H').
  set (m' := dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out').
  assert (Zp : zsum (map slot_pend (lm_hs m')) + slot_pend (Some h) = zsum (map slot_pend (lm_hs m)) + slot_pend (Some h''))
    by exact (dr3_dset_zsum slot_pend si (Some h'') (Some h) (lm_hs m) Hhi).
  assert (Zu : zsum (map pt_eu (lm_es m')) + pt_eu e = zsum (map pt_eu (lm_es m)) + pt_eu e')
    by exact (dr3_dset_zsum pt_eu j e' e (lm_es m) Hej).
  assert (P0 : slot_pend (Some h'') = 0).
  { unfold h''. cbn [slot_pend set_exp_held hs_pending hs_off]. unfold hl_bytes. rewrite Hpend, Hoff1.
    cbn [map fold_right]. lia. }
  assert (P1 : slot_pend (Some h) = P) by exact (eq_sym (ls3_ps_sp h (proj1 Hhpre))).
  assert (Eu : pt_eu e = U) by reflexivity. assert (Eu' : pt_eu e' = U') by reflexivity.
  assert (HM' : pt_mass m' + TOT <= pt_mass m) by (unfold pt_mass, pend_bytes; lia).
  (* ---- per class: the line blocks the step adds ---- *)
  apply (fr_POT_step cx t (t + 1) m m'); [intros c | exact HPOT].
  pose proof (pt_s_ge c) as Hs. pose proof (pt_v_range c) as Hv.
  assert (Zke : zsum (map (pt_ekc c) (lm_es m')) + pt_ekc c e = zsum (map (pt_ekc c) (lm_es m)) + pt_ekc c e')
    by exact (dr3_dset_zsum (pt_ekc c) j e' e (lm_es m) Hej).
  assert (Zks : zsum (map (pt_skc c) (lm_hs m')) + pt_skc c (Some h) =
                zsum (map (pt_skc c) (lm_hs m)) + pt_skc c (Some h''))
    by exact (dr3_dset_zsum (pt_skc c) si (Some h'') (Some h) (lm_hs m) Hhi).
  assert (KI : pt_ekc c e' <= pt_ekc c e + pt_tc c (dr3_nk Ls)).
  { unfold pt_ekc, pt_tc. pose proof Hnd' as Hnd2. apply NoDup_ListNoDup in Hnd2.
    pose proof (pt_sum_incl (pt_w c) (drain_b_c.keys_texts (re_keys e'))
                  (drain_b_c.keys_texts (re_keys e) ++ dr3_nk Ls) (fun x => proj1 (pt_w_range c x)) Hnd2) as X.
    rewrite map_app, zsum_app in X. apply X. intros y Hy. apply in_or_app.
    destruct (dr3_upds_in Ls _ y (proj1 (Hss' y) Hy)) as [Hy'|Hy']; [left | right]; exact Hy'. }
  assert (KH : pt_tc c (texts H') <= pt_tc c (texts (hs_held h)) + pt_tc c (dr3_nk Ls)).
  { unfold pt_tc. pose proof HndH' as Hnd2. apply NoDup_ListNoDup in Hnd2.
    pose proof (pt_sum_incl (pt_w c) (texts H') (texts (hs_held h) ++ dr3_nk Ls)
                  (fun x => proj1 (pt_w_range c x)) Hnd2) as X.
    rewrite map_app, zsum_app in X. apply X. intros y Hy. apply in_or_app. rewrite HtH' in Hy.
    destruct (dr3_upds_in Ls _ y Hy) as [Hy'|Hy']; [left | right]; exact Hy'. }
  assert (S1' : pt_skc c (Some h'') = pt_tc c (texts H')).
  { unfold h''. cbn [pt_skc set_exp_held hs_expected hs_held]. unfold texts at 1. rewrite HrE'.
    cbn [map]. unfold pt_tc at 1. cbn [map fold_right]. lia. }
  assert (S0 : pt_skc c (Some h) = pt_tc c (texts (hs_expected h)) + pt_tc c (texts (hs_held h))) by reflexivity.
  pose proof (pt_tc_nonneg c (texts (hs_expected h))) as T0.
  pose proof (pt_nk c Ls) as NK. fold TOT in NK.
  assert (HK' : pt_kc c m' <= pt_kc c m + 2 * pt_tc c (dr3_nk Ls)) by (unfold pt_kc; lia).
  pose proof (pt_arith (pt_s c) (pt_v c) (pt_kc c m) (pt_kc c m') (pt_mass m) (pt_mass m') (pt_tc c (dr3_nk Ls)) TOT
                ltac:(lia) ltac:(lia) HTOT0 HK' NK HM') as A.
  pose proof (pt_wm_nonneg c (t + 1 - t) ltac:(lia)) as A3.
  lia.
Qed.

End pot.

(* ================================================================== fr_LS3cp is satisfiable at a concrete state *)
(* fr_LS3c_sat's state (ReplyLS3.v sat3, ReplyLS3cArms.v sat3c): the first head's model, nothing pending, no key *)
Section sat3p.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma fr_LS3cp_sat : exists (cx : lfcx (rc := rc)) t m ly S, fr_LS3cp B cx t m ly S.
Proof.
  exists (ls3_cx B), 0, (ls3_m B), ls3_ly, ls3_S.
  assert (EA : ablocks B ls3_ly ls3_S = input_blks (ls3_cx B) ++ model_blks (ls3_m B) ++ []) by reflexivity.
  split; [split|].
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
  - intros c. assert (E1 : pt_kc c (ls3_m B) = 0) by reflexivity. assert (E2 : pt_mass (ls3_m B) = 0) by reflexivity.
    rewrite E1, E2. lia.
Qed.
End sat3p.

(* ================================================================== the cut point: the class counts and their room *)
(* a Theorem Labs lane's per-class limit (rl_prim_ok, 00:28Z): 2^31 / class_size c *)
Definition RL_PRIM (c : Z) : Z := 2 ^ 31 / PresetRoom.size_of_class c.
(* the count besides the line blocks at a cut point with t <= 511 and |es| <= 16: CLS0 (rest), 1 (input), 18 (table,
   out buffer, 4 sources' partial buffer and vectors), 2 per entry, t pending texts *)
Definition CUT_X : Z := CLS0 + 1 + 18 + 2 * 16 + 511.
Definition MARGIN (c : Z) : Z := RL_PRIM c - (CUT_X + pt_v c * (WRITE_MAX * 511) / pt_s c).
Definition MARGIN24 : Z := 2 ^ 15 - (CUT_X + pt_v 24 * (WRITE_MAX * 511) / pt_s 24).

Lemma pt_room_gen : forall LIM c cnt X R ms t, 0 <= t <= 511 -> X <= CUT_X ->
  pt_s c * (cnt - X) + pt_v c * ms <= pt_v c * (WRITE_MAX * t) -> pt_s c * R <= pt_v c * ms ->
  cnt + R + (LIM - (CUT_X + pt_v c * (WRITE_MAX * 511) / pt_s c)) <= LIM.
Proof.
  intros LIM c cnt X R ms t Ht HX Hc HR. pose proof (pt_s_ge c) as Hs. pose proof (pt_v_range c) as Hv.
  assert (A : pt_v c * (WRITE_MAX * t) <= pt_v c * (WRITE_MAX * 511))
    by (apply Z.mul_le_mono_nonneg_l; [lia | unfold SlotInv.WRITE_MAX; lia]).
  assert (B0 : pt_s c * (cnt - X + R) <= pt_v c * (WRITE_MAX * 511)) by (rewrite Z.mul_add_distr_l; lia).
  assert (C : cnt - X + R <= pt_v c * (WRITE_MAX * 511) / pt_s c) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Section cut.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma pt_cls_input : forall (cx : lfcx (rc := rc)) c, cnt_cls c (input_blks cx) <= 1.
Proof. intros cx c. unfold input_blks. apply pt_cls_opt. Qed.
(* at any cut point: the class-c count past the fixed blocks, the pending texts, the input and the rest is paid by the
   potential, with the mass still to be relayed on the left *)
Lemma fr_LS3cp_cls_cut : forall cx t m ly S c, fr_LS3cp B cx t m ly S ->
  pt_s c * (cnt_cls c (ablocks B ly S) - (CLS0 + 1 + 18 + 2 * Z.of_nat (length (lm_es m)) + t)) +
    pt_v c * pt_mass m <= pt_v c * (WRITE_MAX * t).
Proof.
  intros cx t m ly S c ((HLS & (_ & C2 & C3)) & HP).
  destruct HLS as (rest & e0 & _ & _ & _ & _ & Hl & _).
  specialize (C2 c). specialize (HP c).
  pose proof (pt_cls_model c m) as CM.
  replace (Z.of_nat (length (lm_hs m))) with 4 in CM by (rewrite Hl; reflexivity).
  pose proof (pt_cls_input cx c) as CI.
  assert (X : cnt_cls c (ablocks B ly S) - (CLS0 + 1 + 18 + 2 * Z.of_nat (length (lm_es m)) + t) <= pt_kc c m)
    by lia.
  pose proof (Z.mul_le_mono_nonneg_l _ _ (pt_s c) ltac:(pose proof (pt_s_ge c); lia) X). lia.
Qed.
(* the room a callee finds: at t <= 511 with at most 16 entries, a callee whose class-c peak R is within the mass's
   share (pt_s c * R <= pt_v c * pt_mass m) keeps the class-c count MARGIN c under RL_PRIM c *)
Lemma fr_LS3cp_cls_room : forall cx t m ly S c R, fr_LS3cp B cx t m ly S -> 0 <= t <= 511 ->
  (length (lm_es m) <= 16)%nat -> pt_s c * R <= pt_v c * pt_mass m ->
  cnt_cls c (ablocks B ly S) + R + MARGIN c <= RL_PRIM c.
Proof.
  intros cx t m ly S c R H Ht Hes HR. pose proof (fr_LS3cp_cls_cut cx t m ly S c H) as Hc. unfold MARGIN.
  apply (pt_room_gen (RL_PRIM c) c _ (CLS0 + 1 + 18 + 2 * Z.of_nat (length (lm_es m)) + t) R (pt_mass m) t Ht);
    [unfold CUT_X; lia | exact Hc | exact HR].
Qed.
(* class 24 under L24 = 2^15 (a Theorem Labs lane's ccnt24 premise) *)
Lemma fr_LS3cp_c24_room : forall cx t m ly S R, fr_LS3cp B cx t m ly S -> 0 <= t <= 511 ->
  (length (lm_es m) <= 16)%nat -> pt_s 24 * R <= pt_v 24 * pt_mass m ->
  cnt24 (ablocks B ly S) + R + MARGIN24 <= 2 ^ 15.
Proof.
  intros cx t m ly S R H Ht Hes HR. pose proof (fr_LS3cp_cls_cut cx t m ly S 24 H) as Hc. unfold MARGIN24, cnt24.
  change PresetRoom.K_BATCH_CLASS with 24.
  apply (pt_room_gen (2 ^ 15) 24 _ (CLS0 + 1 + 18 + 2 * Z.of_nat (length (lm_es m)) + t) R (pt_mass m) t Ht);
    [unfold CUT_X; lia | exact Hc | exact HR].
Qed.
End cut.

(* the weights and the margins, evaluated *)
Lemma pt_s_table : map pt_s (map Z.of_nat (seq 1 30)) =
  [21; 21; 49; 65; 65537; 97; 129; 161; 193; 225; 257; 289; 321; 353; 385; 417; 449; 641; 897; 1409; 1921; 2945;
   3969; 5889; 7937; 12033; 16129; 24065; 32257; 48129].
Proof. vm_compute. reflexivity. Qed.
Lemma MARGIN_table : map MARGIN (map Z.of_nat (seq 1 30)) =
  [131468; 27175066; 20318686; 15230973; 13419614; 10148461; 8807555; 7763975; 6935370; 6263749; 5709264;
   5244149; 4848619; 4508261; 4212350; 3952755; 2571823; 1939795; 1285474; 976648; 646126; 489549; 323587; 244459;
   161479; 122097; 80527; 60736; 39950; 30055].
Proof. vm_compute. reflexivity. Qed.
Lemma MARGIN_min : forall c, 1 <= c <= 30 -> 30055 <= MARGIN c.
Proof.
  intros c Hc.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/
              c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/
              c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct E as [-> | E]; [apply Z.leb_le; vm_compute; reflexivity |]).
  subst c. apply Z.leb_le; vm_compute; reflexivity.
Qed.
Lemma MARGIN24_val : MARGIN24 = 15083.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== the callee form (ReplyTrPeakCnt.v's Hcls) *)
Lemma lo_ge21 : forall c, 3 <= c <= 30 -> 21 <= PresetRoom.lo c.
Proof.
  intros c Hc.
  assert (E : c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/
              c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16 \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/
              c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct E as [-> | E]; [apply Z.leb_le; vm_compute; reflexivity |]).
  subst c. apply Z.leb_le; vm_compute; reflexivity.
Qed.
(* a peak of 2 X / lo c (X stream bytes) is within the mass's share when X <= the mass *)
Lemma pt_room_pair : forall c X M, 1 <= c <= 30 -> 0 <= X <= M -> pt_s c * (2 * X / PresetRoom.lo c) <= pt_v c * M.
Proof.
  intros c X M Hc HX. pose proof (PresetRoom.lo_pos c) as Hlo.
  assert (Hq : PresetRoom.lo c * (2 * X / PresetRoom.lo c) <= 2 * X) by (apply Z.mul_div_le; lia).
  assert (Hq0 : 0 <= 2 * X / PresetRoom.lo c) by (apply Z.div_pos; lia).
  destruct (Z.eq_dec c 1) as [->|H1]; [|destruct (Z.eq_dec c 2) as [->|H2]].
  - assert (E : PresetRoom.lo 1 = 1) by (vm_compute; reflexivity).
    assert (Es : pt_s 1 = 21) by (unfold pt_s; rewrite E; reflexivity). assert (Ev : pt_v 1 = 42) by reflexivity.
    rewrite Es, Ev, E, Z.div_1_r. lia.
  - assert (E : PresetRoom.lo 2 = 17) by (vm_compute; reflexivity).
    assert (Es : pt_s 2 = 21) by (unfold pt_s; rewrite E; reflexivity). assert (Ev : pt_v 2 = 4) by reflexivity.
    rewrite Es, Ev. rewrite E in Hq, Hq0 |- *. lia.
  - pose proof (lo_ge21 c ltac:(lia)) as L.
    assert (Es : pt_s c = PresetRoom.lo c) by (unfold pt_s; lia).
    assert (Ev : pt_v c = 3) by (unfold pt_v; rewrite (proj2 (Z.eqb_neq c 1) H1), (proj2 (Z.eqb_neq c 2) H2); reflexivity).
    rewrite Es, Ev. lia.
Qed.
Lemma pt_mass_nonneg : forall m, 0 <= pt_mass m.
Proof.
  intros m. unfold pt_mass, pend_bytes.
  pose proof (zsum_map_nonneg slot_pend (lm_hs m) pt_pend_nonneg).
  pose proof (zsum_map_nonneg pt_eu (lm_es m) pt_eu_nonneg). lia.
Qed.
(* a drained or removed pair's stream bytes (its pending stream, its entry's re_U) are at most the mass *)
Lemma pt_pair_le_mass : forall m si h j e, nth si (lm_hs m) None = Some h -> nth_error (lm_es m) j = Some e ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  Z.of_nat (length (pending_stream h)) + Z.of_nat (length (re_U e)) <= pt_mass m.
Proof.
  intros m si h j e Hh Hj Hoff. unfold pt_mass, pend_bytes. rewrite (ls3_ps_sp h Hoff).
  pose proof (zsum_map_elem slot_pend (lm_hs m) si (Some h) pt_pend_nonneg (nth_some_error _ _ _ Hh)).
  pose proof (zsum_map_elem pt_eu (lm_es m) j e pt_eu_nonneg Hj).
  assert (Eu : pt_eu e = Z.of_nat (length (re_U e))) by reflexivity. lia.
Qed.

Section cut2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the class count at a cut point, in the form ReplyTrPeakCnt.v's Hcls takes (LIM := RL_PRIM c): any X of stream bytes
   within the mass (a drained pair's pair_bytes, by pt_pair_le_mass) *)
Lemma fr_LS3cp_cls_pair : forall cx t m ly S c X, fr_LS3cp B cx t m ly S -> 0 <= t <= 511 ->
  (length (lm_es m) <= 16)%nat -> 1 <= c <= 30 -> 0 <= X <= pt_mass m ->
  cnt_cls c (ablocks B ly S) <= RL_PRIM c - 5 - 2 * X / PresetRoom.lo c.
Proof.
  intros cx t m ly S c X H Ht Hes Hc HX.
  pose proof (fr_LS3cp_cls_room B cx t m ly S c (2 * X / PresetRoom.lo c) H Ht Hes (pt_room_pair c X (pt_mass m) Hc HX))
    as R.
  pose proof (MARGIN_min c Hc). lia.
Qed.
(* the batch class at a cut point (ReplyTrPeakCnt.v's cnt24 calls need 2^15 - 11,380) *)
Lemma fr_LS3cp_cnt24_cut : forall cx t m ly S, fr_LS3cp B cx t m ly S -> 0 <= t <= 511 ->
  (length (lm_es m) <= 16)%nat -> cnt24 (ablocks B ly S) <= 2 ^ 15 - 15083.
Proof.
  intros cx t m ly S H Ht Hes.
  assert (H0 : pt_s 24 * 0 <= pt_v 24 * pt_mass m).
  { pose proof (pt_mass_nonneg m). pose proof (pt_v_range 24). rewrite Z.mul_0_r. apply Z.mul_nonneg_nonneg; lia. }
  pose proof (fr_LS3cp_c24_room B cx t m ly S 0 H Ht Hes H0) as R. rewrite MARGIN24_val in R. lia.
Qed.
End cut2.
