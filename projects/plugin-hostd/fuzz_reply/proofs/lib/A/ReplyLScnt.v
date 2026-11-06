(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_LLVMFuzzerTestOneInput_gone_base_x.v, with its module paths and module names changed; 432 of its 501 lines of code are new or changed and 589 lines of the source are left out. *)
(* The count rows LS_cnt of LS v3, one per arm (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c), the ROOM round), at the instance
   LSx := fr_LS3cp B (ReplyLS3p.v) and RINV := fr_RINV, for a Theorem Labs lane's FREE-PIECES row B1c.
   proves no function (kind: invariant lemma).  Arm files and line numbers: a working branch at 4e0e1968abd;
   the callees' count premises: the ROOM round audit cb71685bcb2, lib/A/W_contract_x.v and lib/A/W_op_add.v.

   WHAT A ROW SAYS.  At the arm's cut point (ly, S), for the arm's peak PK : (Z -> bool) -> nat,
     acnt Psec (ablocks B ly S) + PK Psec <= Lsec /\ acnt P24 (ablocks B ly S) + PK P24 <= L24 /\
     (forall c, 1 <= c <= 30 -> acnt (Pcls c) (ablocks B ly S) + PK (Pcls c) <= LPRIM c)
   in ReplyCnt.v's names (Lsec = 1,024, L24 = 2^15, LPRIM c = RL_PRIM c = 2^31 / class_size c).  PK P is at least,
   at every allocating callee call of the arm, the net count the earlier callees added plus that callee's OWN premise
   peak (the audit's rule, W_contract_x.v:274-284: a callee's premise is fixed text, so the arm pays the callee's
   stated constant, not its smaller actual peak).  A net growth is at most a peak, so a sum of the earlier callees'
   trace peaks plus the largest premise constant is enough.  The arm's walk gets each inner call's count premise from
   the row and the block relation it threads (ROOM-TEXTS (b), "Inner-call derivation"; cnt_ok_pk_mono, audit
   W_journal_x.v:1402).

   THE PEAKS (the forms W8Entry-2 matches), with the callees' premise peaks at the audit:
   - SEG_PRO, ARM_add: op_add, oa_peak (W_op_add.v:348, :430).  pk_oa P = [P ATABLE] + [P APARTIAL], oa_peak's text.
   - ARM_write: list_push, lp_peak (W_contract_x.v:260, :377).  pk_lp = lp_peak word for word.
   - ARM_drain: drain, dr_pk = own trace peak + 2 (:303-304, :764); check_no_loss_read (no request); check_no_loss,
     cnl_pk E H = tr_peakP (cnl_tr E H) + 2 (:296-302, :1341); check_shape_done (no request).
     pk_drain m h j P = tr_peakP P (dr_tr ..) + (cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P + 2).
     The second summand is the audit's cnl_pk at the call: the drain appended its reference lines to the empty
     expected list and kept the held list (dr_rel W_contract.v:1262, :1264; LS_cnl_pre's premises); lsc_cnl_call
     equates the call's own check_no_loss trace, under any naming (the audit's cnl_tr names every block
     RelayRunF.adr0), with this file's cnl_pk (ReplyTrPeakCnl.v; NOT the audit's W_contract_x.cnl_pk, which takes
     (E H) and adds the 2).
   - ARM_remove: relay_remove, rr_pk = own trace peak + 4 (:305, :923); check_no_loss_read; check_no_loss, cnl_pk + 2
     (an entry at eof leaves h1 = h, nothing expected: tr_peakP 0, premise 2); check_shape_ends cshe_pk 0 (:273,
     :1271); check_shape_done; source_reset sr_pk 0 (:271, :404).
     pk_rm m h j0 P = tr_peakP P (rm_rr_tr m h) + (this file's cnl_pk when the entry is open, else 0) + 4.
   - ARM_gone: relay_instance_gone, rig_pk = own trace peak + 3 (:306, :975); then per table entry check_no_loss_read,
     check_no_loss (cnl_pk + 2), check_shape_ends (0); check_shape_done.
     pk_gone cx m hs P = tr_peakP P (rig_tr ..) + (the sum over the table of gn_cnl P, each open entry's cnl_pk of its
     drained texts) + 3.
   - ARM_event: malloc (cnt_ok, peak 0, audit W_journal_x.v:1504), relay_event at S ++ [(q, re_len e)] with re_pk = 2
     (W_contract_x.v:286, :816), free (cnt_ok; relay_event's own trace peak <= 2, W_tr_cnt.v tc_re :204).
     pk_event e P = [P (re_len e)] + 2.
   - SEG_EXIT: relay_finish rf_pk = 5 (:289, :1165), then check_shape_ends and source_reset (0); check_shape_done.
     pk_exit P = 5 (relay_finish's own trace peak <= 5, W_tr_cnt.v tc_rf :309, covers the later frees' premises).
   ROOM-TEXTS (c)'s table gives ARM_remove "rr's peak" and ARM_gone "rig's peak": both arms also call check_no_loss
   after a drain (_remove_x.v CNL :193; _gone_x.v's cnl_spec_x), whose premise peak depends on the drained lines
   (the audit's cnl_pk, W_contract_x.v:302), so the rows here carry it.

   THE GUARDS.  Each row takes the arm's own premises of its LS rules (ad_at_op; wr_pick and 0 < wr_n; dr_at_op,
   dr_pick, j, the fd and re_eof = 0; rm_at; gn_pairs; ev_evt), then facts the arm has at its cut point and LS / RINV
   do not give: msz_ok (lm_es m) (lm_hs m) (the model's sizes, from amodel_at, ReplyCnt.v), 0 <= t < OPS_MAX (the
   cut's operation
   count), and for drain / remove / gone the drained entries' |re_U| <= APARTIAL (aentry_ok), positive or nonnegative
   block sizes (al_blocks), and the pending lists' read offsets (asrc_at, W_rep.v:104-105).  SEG_PRO takes the entry
   contract's xcnt_ok (ROOM-TEXTS (e); ReplyCnt.v), as its counts come from the entry, not from LS.

   HOW.  lsc_room: at a cut point fr_LS3cp gives cnt_sec <= 593 (ReplyTrPeakCnt.tc_sec_cut) and, for class 24 and
   each primary class c, cnt + R + MARGIN c <= RL_PRIM c (2^15 for class 24) whenever pt_s c * R <= pt_v c * pt_mass m
   (ReplyLS3p.fr_LS3cp_cls_room / fr_LS3cp_c24_room; MARGIN c >= 30,055, MARGIN 24 = 15,083).  A constant peak K
   takes R = PK - K <= 0 (lsc_room_const).  For drain / remove / gone, R is the peak above its constant K: the
   drain's part is paid at 2 / lo c per stream byte (ReplyTrPeakCnt), class 1 at 22 / 21 (ReplyTrPeakCnl.v part B),
   check_no_loss's at 1 / pt_s c (part A), and the stream bytes are at most the mass (pt_pair_le_mass,
   lsc_rig_pb_mass); lsc_pay checks the sum against pt_v c = 42 / 4 / 3 (c = 1 / 2 / >= 3).  The constants K:
   op_add and list_push 2, event 3, exit 5, drain 5 + 2 + 2 = 9, remove 5 + 2 + 4 = 11, gone (4 |es| + 1) + 2 |es| + 3
   <= 28 (|es| <= 4).  The margin a row leaves is MARGIN c - K (secondary: 1,024 - 593 - K; SEG_PRO: from xcnt_ok,
   at most CLS0 + 3 + 2 per class and SEC0 + 3 + 2 secondary).
   CLASS 1, explicitly (a Theorem Labs lane 02:05Z).  At a cut, 21 (cnt_1 - X0) + 42 mass <= 42 * WRITE_MAX * t with
   X0 <= CUT_X = 626 (fr_LS3cp_cls_cut).  The drain arm's peak is dr_1 + cnl_1 + 2 with 21 dr_1 <= 105 + 22 PB
   (fr_LS_drain_c1_peak) and 21 (cnl_1 - 2) <= PB (cnl_pk_cls, cnl_drain_bytes), PB = pair_bytes <= mass, so
   21 (dr_1 + cnl_1 + 2 - 9) <= 23 mass and cnt_1 + dr_1 + cnl_1 + 2 <= 626 + 9 + 2 * 65,535 * 511 - 19 mass / 21
   <= 66,977,405 = RL_PRIM 1 - 131,459: the class-1 margin left is 131,459 counts (MARGIN 1 = 131,468, less the 9),
   at its least when the mass is 0.  Remove: less 11, 131,457.  Gone: less at most 28, >= 131,440. *)
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
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSRemove3 ReplyLSRrPre ReplyLSDrain3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSCntM ReplyLS3p ReplyTrPeakCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the arms' peaks (Z -> bool) -> nat *)
Definition zn (b : bool) : nat := if b then 1%nat else 0%nat.
(* op_add: its premise peak oa_peak, word for word (audit cb71685bcb2 W_op_add.v:190): the partial buffer APARTIAL,
   then relay_add's new table ATABLE *)
Definition pk_oa (P : Z -> bool) : nat := (zn (P ATABLE) + zn (P APARTIAL))%nat.
(* list_push: its premise peak lp_peak, word for word (audit W_contract_x.v:260-261) *)
Definition pk_lp (l : hlist) (n : Z) : (Z -> bool) -> nat :=
  fun P => ((if P (lp_vbytes l) && lp_grow l then 1 else 0) + (if P (n + 1)%Z then 1 else 0))%nat.
(* the event: malloc (re_len e), then relay_event at the state with that block, its premise peak re_pk = 2 (audit
   W_contract_x.v:286), then free *)
Definition pk_event (e : list byte) (P : Z -> bool) : nat := (zn (P (re_len e)) + 2)%nat.
(* the exit: relay_finish, its premise peak rf_pk = 5 (audit W_contract_x.v:289), then check_shape_ends and
   source_reset (premise peak 0, frees) *)
Definition pk_exit (P : Z -> bool) : nat := 5%nat.

(* the per-pair facts of an open entry (rig_ok's body) *)
Definition lsc_pq (p : rentry * (hsrc * nat)) : Prop :=
  re_eof (fst p) = 0 ->
    (re_skip (fst p) = 0 \/ re_skip (fst p) = 1) /\ re_skip (fst p) = hs_overlong (fst (snd p)) /\
    (re_skip (fst p) = 0 -> bzs (re_U (fst p)) = bzs (hs_W (fst (snd p)))) /\
    Z.of_nat (length (re_U (fst p))) <= APARTIAL /\ 0 <= hs_off (fst (snd p)).
(* the drain arm: drain (premise dr_pk = its trace peak + 2, audit W_contract_x.v:303), then check_no_loss (premise
   cnl_pk E H = its trace peak + 2, :302) over the expected texts the drain appended (dr_rel / LS_cnl_pre:
   map snd (hl_recs (hs_expected h'')) = [] ++ map (map (Z_to_bv 8)) (dr_lines h)) and the held list it keeps
   (hs_held h'' = hs_held h) *)
Definition pk_drain (m : lmod) (h : hsrc) (j : nat) (P : Z -> bool) : nat :=
  (Z.to_nat (tr_peakP P (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                         (nth j (lm_es m) dr_e0) h)) +
   (cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P + 2))%nat.
(* the remove arm: relay_remove (premise rr_pk = its trace peak + 4, :305), check_no_loss (cnl_pk + 2) over what the
   drain appended (rm_rr_ok's dr_rel when open; h1 = h, nothing expected, when at eof), check_shape_ends and
   source_reset (premise peak 0) *)
Definition pk_rm (m : lmod) (h : hsrc) (j0 : nat) (P : Z -> bool) : nat :=
  (Z.to_nat (tr_peakP P (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) +
   (if (re_eof (rm_ent m j0) =? 0)%Z then cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P else 0) + 4)%nat.
(* the gone arm: relay_instance_gone (premise rig_pk = its trace peak + 3, :306), then per table entry check_no_loss
   (cnl_pk + 2) over what its drain appended (nothing for an entry at eof) and check_shape_ends (premise peak 0) *)
Definition gn_cnl (P : Z -> bool) (p : rentry * (hsrc * nat)) : nat :=
  if re_eof (fst p) =? 0 then cnl_pk (hs_held (fst (snd p))) (map (map (Z_to_bv 8)) (dr_lines (fst (snd p)))) P
  else 0%nat.

Lemma zn_le1 : forall b, (zn b <= 1)%nat.
Proof. intros [|]; cbn; lia. Qed.

Section lsc.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ================================================================== nat and Z *)
Lemma lsc_RL_pos : forall c, 1 <= c <= 30 -> 30055 <= RL_PRIM c.
Proof.
  intros c Hc. pose proof (MARGIN_min c Hc) as M. unfold MARGIN in M.
  assert (D : 0 <= pt_v c * (SlotInv.WRITE_MAX * 511) / pt_s c).
  { pose proof (pt_s_ge c). pose proof (pt_v_range c). apply Z.div_pos; [|lia].
    apply Z.mul_nonneg_nonneg; [lia | unfold SlotInv.WRITE_MAX; lia]. }
  assert (CX : CUT_X = 626) by reflexivity.
  change (ReplyCnt.RL_PRIM c) with (ReplyLS3p.RL_PRIM c). lia.
Qed.
Lemma lsc_LPRIM : forall c, 1 <= c <= 30 -> Z.of_nat (LPRIM c) = ReplyLS3p.RL_PRIM c.
Proof.
  intros c Hc. pose proof (lsc_RL_pos c Hc). unfold LPRIM. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma lsc_L24 : Z.of_nat L24 = 2 ^ 15.
Proof. unfold L24. rewrite Z2Nat.id by lia. reflexivity. Qed.
Lemma lsc_Lsec : Z.of_nat Lsec = 1024.
Proof. reflexivity. Qed.

(* ================================================================== the room at a cut point *)
(* LS v3 with the potential (fr_LS3cp) at a cut point with t < OPS_MAX: the secondary count is at most 593
   (tc_sec_cut, from msz_ok); class 24 and every primary class keep their MARGIN for a peak whose part above the
   constants K24 / Kc is paid by the mass (pt_s c * R <= pt_v c * pt_mass m) *)
Lemma lsc_room : forall cx t m ly S (PK : (Z -> bool) -> nat) K24 Kc,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (PK Psec) <= 431 ->
  K24 <= 15083 -> pt_s 24 * (Z.of_nat (PK P24) - K24) <= pt_v 24 * pt_mass m ->
  Kc <= 30055 -> (forall c, 1 <= c <= 30 -> pt_s c * (Z.of_nat (PK (Pcls c)) - Kc) <= pt_v c * pt_mass m) ->
  (acnt Psec (ablocks B ly S) + PK Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + PK P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + PK (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S PK K24 Kc HLS HRI Hm Ht Hs H24k H24 Hck Hc.
  pose proof (fr_RINV_es_le cx t m HRI) as E4.
  assert (Ht' : 0 <= t <= 511) by (unfold OPS_MAX in Ht; lia).
  assert (E16 : (length (lm_es m) <= 16)%nat) by lia.
  split; [|split].
  - pose proof (tc_sec_cut B cx t m ly S (proj1 HLS) Hm HRI Ht) as C.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_Lsec.
    change (Z.of_nat (acnt Psec (ablocks B ly S))) with (ReplyCnt.cnt_sec (ablocks B ly S)). lia.
  - pose proof (fr_LS3cp_c24_room B cx t m ly S _ HLS Ht' E16 H24) as C. rewrite MARGIN24_val in C.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_L24.
    change (Z.of_nat (acnt P24 (ablocks B ly S))) with (ReplyCnt.cnt24 (ablocks B ly S)). lia.
  - intros c Hc1. pose proof (fr_LS3cp_cls_room B cx t m ly S c _ HLS Ht' E16 (Hc c Hc1)) as C.
    pose proof (MARGIN_min c Hc1) as M.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, (lsc_LPRIM c Hc1).
    change (Z.of_nat (acnt (Pcls c) (ablocks B ly S))) with (ReplyCnt.cnt_cls c (ablocks B ly S)). lia.
Qed.
(* a constant peak of at most K for every predicate, K <= 431 (the secondary room above 593) *)
Lemma lsc_room_const : forall cx t m ly S (PK : (Z -> bool) -> nat) (K : nat),
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (K <= 431)%nat -> (forall P, (PK P <= K)%nat) ->
  (acnt Psec (ablocks B ly S) + PK Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + PK P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + PK (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S PK K HLS HRI Hm Ht HK HP.
  pose proof (pt_mass_nonneg m) as Hms.
  assert (G : forall c, pt_s c * (Z.of_nat (PK (Pcls c)) - Z.of_nat K) <= pt_v c * pt_mass m).
  { intros c. pose proof (HP (Pcls c)). pose proof (pt_s_ge c). pose proof (pt_v_range c). nia. }
  apply (lsc_room cx t m ly S PK (Z.of_nat K) (Z.of_nat K) HLS HRI Hm Ht).
  - pose proof (HP Psec). lia.
  - lia.
  - pose proof (HP P24). pose proof (pt_s_ge 24). pose proof (pt_v_range 24). nia.
  - lia.
  - intros c _. apply G.
Qed.

(* ================================================================== the constant-peak arms *)
(* ARM_add (cut_x's _add_x.v, LS_cnt after LS_add_none :750): op_add *)
Lemma fr_LS3cp_cnt_add : forall cx t m ly S,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> ad_at_op cx m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_oa Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + pk_oa P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_oa (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S HLS HRI _ Hm Ht. apply (lsc_room_const cx t m ly S pk_oa 2 HLS HRI Hm Ht); [lia|].
  intros P. unfold pk_oa. pose proof (zn_le1 (P ATABLE)). pose proof (zn_le1 (P APARTIAL)). lia.
Qed.
(* ARM_write (_write_x.v, LS_cnt after LS_write_push :142): list_push of the pending list *)
Lemma fr_LS3cp_cnt_write : forall cx t m si h ly S,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> wr_pick cx m si h -> 0 < wr_n cx m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_lp (hs_pending h) (wr_n cx m) Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_lp (hs_pending h) (wr_n cx m) P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 ->
     (acnt (Pcls c) (ablocks B ly S) + pk_lp (hs_pending h) (wr_n cx m) (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m si h ly S HLS HRI _ _ Hm Ht. apply (lsc_room_const cx t m ly S _ 2 HLS HRI Hm Ht); [lia|].
  intros P. unfold pk_lp. destruct (P (lp_vbytes (hs_pending h)) && lp_grow (hs_pending h));
    destruct (P (wr_n cx m + 1)); lia.
Qed.
(* ARM_event (_event_x.v, LS_cnt after LS_event_step :204): malloc (re_len e), relay_event (re_pk 2), free *)
Lemma fr_LS3cp_cnt_event : forall cx t m ly S e,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> ev_evt cx m e ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_event e Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_event e P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_event e (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S e HLS HRI _ Hm Ht. apply (lsc_room_const cx t m ly S _ 3 HLS HRI Hm Ht); [lia|].
  intros P. unfold pk_event. pose proof (zn_le1 (P (re_len e))). lia.
Qed.
(* SEG_EXIT (_exit_x.v, LS_cnt after LS_exit_end :158): relay_finish (rf_pk 5) and the exit's frees *)
Lemma fr_LS3cp_cnt_exit : forall cx t m ly S,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  (acnt Psec (ablocks B ly S) + pk_exit Psec <= Lsec)%nat /\ (acnt P24 (ablocks B ly S) + pk_exit P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_exit (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S HLS HRI Hm Ht. apply (lsc_room_const cx t m ly S _ 5 HLS HRI Hm Ht); [lia|].
  intros P. unfold pk_exit. lia.
Qed.

(* ================================================================== SEG_PRO: from the entry *)
(* the entry's kept blocks (input, table, g_out) are at most one each *)
Lemma lsc_kept_le : forall (P : Z -> bool) (cx : lfcx (rc := rc)) T cap out,
  (acnt P (xcnt_kept (input_blks cx) T cap out) <= 3)%nat.
Proof.
  intros P cx T cap out. unfold xcnt_kept, input_blks, aout_blks. rewrite !acnt_app.
  assert (A1 : forall (b : bool) (x : Z * Z), (acnt P (if b then [] else [x]) <= 1)%nat).
  { intros [|] [a n]; unfold acnt; cbn [map List.filter snd]; [cbn; lia|]. destruct (P n); cbn; lia. }
  pose proof (A1 (c_n cx =? 0) (c_p cx, c_n cx)). pose proof (A1 (T =? 0) (T, ATABLE)).
  pose proof (A1 (cap =? 0) (out, cap)). lia.
Qed.
(* SEG_PRO (_pro_x.v, LS_cnt after LS_pro :213): op_add from the entry, at the state S2 after the fake frame (same blocks
   as the entry, LS_pro_oa's premise).  The counts come from the entry contract's xcnt_ok (ROOM-TEXTS (e), ReplyCnt.v
   xcnt_ok, with inp := input_blks cx and the entry's table T and g_out (cap, out)), not from LS. *)
Lemma fr_cnt_pro : forall (cx : lfcx (rc := rc)) T cap out (S2 : astate),
  xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T cap out ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) ->
  (acnt Psec (ablocks B (c_ly cx) S2) + pk_oa Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B (c_ly cx) S2) + pk_oa P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B (c_ly cx) S2) + pk_oa (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx T cap out S2 (X1 & X2) E. rewrite E.
  assert (PO : forall P, (pk_oa P <= 2)%nat).
  { intros P. unfold pk_oa. pose proof (zn_le1 (P ATABLE)). pose proof (zn_le1 (P APARTIAL)). lia. }
  unfold cnt_sec, cnt_cls, SEC0, CLS0 in *.
  split; [|split].
  - pose proof (lsc_kept_le Psec cx T cap out). pose proof (PO Psec).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_Lsec. lia.
  - pose proof (X2 kBatchClass ltac:(change kBatchClass with 24; lia)) as X.
    pose proof (lsc_kept_le P24 cx T cap out). pose proof (PO P24).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, lsc_L24. unfold P24 in *. lia.
  - intros c Hc. pose proof (X2 c Hc). pose proof (lsc_kept_le (Pcls c) cx T cap out). pose proof (PO (Pcls c)).
    pose proof (lsc_RL_pos c Hc).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, (lsc_LPRIM c Hc).
    change (ReplyLS3p.RL_PRIM c) with (ReplyCnt.RL_PRIM c). lia.
Qed.

(* ################################################################## the data-dependent arms *)
(* ---- check_no_loss after a drain: the call's own trace (any naming nm of its blocks) has the rows' cnl_pk, from
   the expected list the drain appended to (empty at the operation's start, fr_pair_ok ReplyRINV.v:165; dr_rel
   W_contract.v:1262) and the held list it kept (dr_rel :1229) ---- *)
Lemma lsc_cnl_call : forall (j : nat) (nm : Z -> RelayRunT.addr YO0i.sptr) (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  Z.to_nat (tr_peakP P (HarnessTr.check_no_loss_tr j (ListTr.sh_of nm (hs_held h''))
                          (map (ListTr.shr nm) (hl_recs (hs_expected h''))))) =
  cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P.
Proof.
  intros j nm h h'' P E0 Ex Eh. unfold cnl_pk. rewrite cnl_tr_names, Ex, E0, Eh. reflexivity.
Qed.

(* ---- the kit's tr_peakP at the two weights ---- *)
Lemma lsc_w_cls : forall (X : Type) c (tr : list (RelayRunT.rev X)),
  tr_peakP (Pcls c) tr = ReplyTrPeakW.tr_peak_w (w_cls c) tr.
Proof. intros. rewrite tr_peakP_w. reflexivity. Qed.
Lemma lsc_w_sec : forall (X : Type) (tr : list (RelayRunT.rev X)), tr_peakP Psec tr = ReplyTrPeakW.tr_peak_w w_sec tr.
Proof. intros. rewrite tr_peakP_w. reflexivity. Qed.

(* ---- the class arithmetic: a callee whose class-1 part is paid at 22 / 21 per mass byte and whose part in any other
   class at 2 / lo c, then check_no_loss at 1 / pt_s c, fits the potential's pt_v c per mass byte (ReplyLS3p pt_v:
   42, 4, 3) ---- *)
Lemma lsc_pay : forall c X Y K1 K2 D PB M, 1 <= c <= 30 -> 0 <= PB <= M ->
  (c = 1 -> 21 * (X - K1) <= 22 * PB) -> (c <> 1 -> PresetRoom.lo c * (X - K1) <= 2 * PB) ->
  pt_s c * (Y - K2) <= PB ->
  pt_s c * (X + Y + D - (K1 + K2 + D)) <= pt_v c * M.
Proof.
  intros c X Y K1 K2 D PB M Hc HPB H1 Hn HY.
  replace (X + Y + D - (K1 + K2 + D)) with (X + Y - (K1 + K2)) by ring.
  destruct (Z.eq_dec c 1) as [->|N1]; [|destruct (Z.eq_dec c 2) as [->|N2]].
  - specialize (H1 eq_refl). assert (E : PresetRoom.lo 1 = 1) by (vm_compute; reflexivity).
    assert (Es : pt_s 1 = 21) by (unfold pt_s; rewrite E; reflexivity). assert (Ev : pt_v 1 = 42) by reflexivity.
    rewrite Es, Ev in *. lia.
  - specialize (Hn ltac:(lia)). assert (E : PresetRoom.lo 2 = 17) by (vm_compute; reflexivity).
    assert (Es : pt_s 2 = 21) by (unfold pt_s; rewrite E; reflexivity). assert (Ev : pt_v 2 = 4) by reflexivity.
    rewrite E in Hn. rewrite Es, Ev in *. lia.
  - specialize (Hn N1). pose proof (lo_ge21 c ltac:(lia)) as L.
    assert (Es : pt_s c = PresetRoom.lo c) by (unfold pt_s; lia).
    assert (Ev : pt_v c = 3)
      by (unfold pt_v; rewrite (proj2 (Z.eqb_neq c 1) N1), (proj2 (Z.eqb_neq c 2) N2); reflexivity).
    rewrite Es, Ev in *. nia.
Qed.

(* ================================================================== ARM_drain *)
(* ARM_drain (_drain_x.v, LS_cnt after LS_drain_step :468): drain, then check_no_loss *)
Lemma fr_LS3cp_cnt_drain : forall cx t m ly S si h j,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (acnt Psec (ablocks B ly S) + pk_drain m h j Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_drain m h j P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_drain m h j (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S si h j HLS HRI _ Hpick Hj Hfdj Heof Hm Ht HU HXP Hoffs.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & Hent & _).
  destruct Hp as (_ & _ & _ & Hre & _). destruct Hent as (_ & _ & _ & _ & Hsk).
  destruct (Hre Heof) as (Hov & HW).
  destruct (tc_dr_facts cx t m si h j HRI Hpick Hj Hfdj Heof HU) as (_ & Href & _ & _).
  pose proof (pair_bytes_nonneg (nth j (lm_es m) dr_e0) h) as HPB0.
  assert (HPBm : pair_bytes (nth j (lm_es m) dr_e0) h <= pt_mass m).
  { pose proof Hpick as (_ & _ & Hh).
    pose proof (pt_pair_le_mass m si h j (nth j (lm_es m) dr_e0) Hh (nth_error_nth' (lm_es m) dr_e0 Hj) Hoffs) as M.
    unfold pair_bytes. destruct (re_skip (nth j (lm_es m) dr_e0) =? 0); lia. }
  pose proof (cnl_drain_bytes _ h Hsk Hov HW) as CB.
  pose proof (cnl_pk_sec (hs_held h) _ (cnl_drain_short h Href)) as CS.
  assert (EPK : forall P, Z.of_nat (pk_drain m h j P) =
    tr_peakP P (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) +
    tr_peakP P (cnl_tr (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h))) + 2).
  { intros P. unfold pk_drain, cnl_pk. rewrite !Nat2Z.inj_add, !Z2Nat.id by apply tr_peakP_nonneg. lia. }
  apply (lsc_room cx t m ly S (pk_drain m h j) (5 + 2 + 2) (5 + 2 + 2) HLS HRI Hm Ht).
  - rewrite EPK, lsc_w_sec. pose proof (fr_LS_drain_sec_peak cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP). lia.
  - lia.
  - rewrite EPK. unfold P24. change kBatchClass with 24.
    apply (lsc_pay 24 _ _ 5 2 2 _ _ ltac:(lia) (conj HPB0 HPBm)).
    + intros E. lia.
    + intros _. rewrite lsc_w_cls. pose proof (fr_LS_drain_cls_peak 24 cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP).
      nia.
    + pose proof (cnl_pk_cls 24 (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h))). lia.
  - lia.
  - intros c Hc. rewrite EPK. apply (lsc_pay c _ _ 5 2 2 _ _ Hc (conj HPB0 HPBm)).
    + intros ->. rewrite lsc_w_cls. pose proof (fr_LS_drain_c1_peak cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP). lia.
    + intros _. rewrite lsc_w_cls. pose proof (fr_LS_drain_cls_peak c cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP).
      nia.
    + pose proof (cnl_pk_cls c (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h))). lia.
Qed.

(* ================================================================== ARM_remove *)
(* ARM_remove (_remove_x.v, LS_cnt after LS_rm_step :173): relay_remove, check_no_loss, check_shape_ends,
   source_reset *)
Lemma fr_LS3cp_cnt_rm : forall cx t m ly S si h j0,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (acnt Psec (ablocks B ly S) + pk_rm m h j0 Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_rm m h j0 P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_rm m h j0 (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S si h j0 HLS HRI Hat Hm Ht HU Hpos Hoffs.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (Hp & HE & _ & _).
  destruct Hp as (_ & _ & _ & Hre & _). destruct HE as (_ & _ & _ & _ & Hsk).
  destruct (tc_rm_facts cx t m si h j0 HRI Hat HU) as (_ & _ & _ & HJ).
  pose proof (pair_bytes_nonneg (rm_ent m j0) h) as HPB0.
  assert (HPBm : pair_bytes (rm_ent m j0) h <= pt_mass m).
  { pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
    pose proof (pt_pair_le_mass m si h j0 (rm_ent m j0) Hh
                  (nth_error_nth' (lm_es m) relay_remove_b_c.no_entry Hj0) Hoffs) as M.
    unfold pair_bytes. destruct (re_skip (rm_ent m j0) =? 0); lia. }
  assert (CN : Z.of_nat (if re_eof (rm_ent m j0) =? 0
                         then cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) Psec else 0%nat) <= 2 /\
               forall c, pt_s c * (Z.of_nat (if re_eof (rm_ent m j0) =? 0
                         then cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) (Pcls c) else 0%nat) - 2) <=
                         pair_bytes (rm_ent m j0) h).
  { destruct (re_eof (rm_ent m j0) =? 0) eqn:Eo.
    - apply Z.eqb_eq in Eo. destruct (Hre Eo) as (Hov & HW). destruct (HJ Eo) as (Href & _).
      unfold cnl_pk. split.
      + rewrite Z2Nat.id by apply tr_peakP_nonneg. exact (cnl_pk_sec _ _ (cnl_drain_short h Href)).
      + intros c. rewrite Z2Nat.id by apply tr_peakP_nonneg.
        pose proof (cnl_pk_cls c (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h))).
        pose proof (cnl_drain_bytes _ h Hsk Hov HW). lia.
    - split; [cbn; lia|]. intros c. pose proof (pt_s_ge c). cbn. lia. }
  destruct CN as [CNs CNc].
  assert (EPK : forall P, Z.of_nat (pk_rm m h j0 P) = tr_peakP P (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) +
     Z.of_nat (if re_eof (rm_ent m j0) =? 0 then cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P else 0%nat) +
     4).
  { intros P. unfold pk_rm. rewrite !Nat2Z.inj_add. rewrite Z2Nat.id by apply tr_peakP_nonneg. lia. }
  apply (lsc_room cx t m ly S (pk_rm m h j0) (5 + 2 + 4) (5 + 2 + 4) HLS HRI Hm Ht).
  - rewrite EPK, lsc_w_sec. pose proof (fr_LS_rm_sec_peak cx t m si h j0 HRI Hat HU Hpos). lia.
  - lia.
  - rewrite EPK. unfold P24. change kBatchClass with 24.
    apply (lsc_pay 24 _ _ 5 2 4 _ _ ltac:(lia) (conj HPB0 HPBm)).
    + intros E. lia.
    + intros _. rewrite lsc_w_cls. pose proof (fr_LS_rm_cls_peak 24 cx t m si h j0 HRI Hat HU Hpos). nia.
    + exact (CNc 24).
  - lia.
  - intros c Hc. rewrite EPK. apply (lsc_pay c _ _ 5 2 4 _ _ Hc (conj HPB0 HPBm)).
    + intros ->. rewrite lsc_w_cls. pose proof (fr_LS_rm_c1_peak cx t m si h j0 HRI Hat HU Hpos). lia.
    + intros _. rewrite lsc_w_cls. pose proof (fr_LS_rm_cls_peak c cx t m si h j0 HRI Hat HU Hpos). nia.
    + exact (CNc c).
Qed.

(* ================================================================== ARM_gone *)
Definition pk_gone (cx : lfcx) (m : lmod) (hs : list (hsrc * nat)) (P : Z -> bool) : nat :=
  (Z.to_nat (tr_peakP P (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)) +
   fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs)) + 3)%nat.

(* check_no_loss over each open entry's drained lines: 2 + its lines' bytes / pt_s c each *)
Lemma lsc_gn_cnl : forall ps, Forall lsc_pq ps ->
  Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl Psec) ps)) <= 2 * Z.of_nat (length ps) /\
  (forall c, pt_s c * (Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl (Pcls c)) ps)) - 2 * Z.of_nat (length ps)) <=
     fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then pair_bytes (fst p) (fst (snd p)) else 0) ps)).
Proof.
  induction ps as [|p ps IH]; intros HF.
  - cbn. split; [lia|]. intros c. lia.
  - inversion HF as [|? ? Hp HF']; subst. destruct (IH HF') as [I1 I2].
    assert (P1 : Z.of_nat (gn_cnl Psec p) <= 2 /\
                 forall c, pt_s c * (Z.of_nat (gn_cnl (Pcls c) p) - 2) <=
                           (if re_eof (fst p) =? 0 then pair_bytes (fst p) (fst (snd p)) else 0)).
    { unfold gn_cnl. destruct (re_eof (fst p) =? 0) eqn:Eo.
      - apply Z.eqb_eq in Eo. destruct (Hp Eo) as (Hsk & Hov & HW & HU & _).
        pose proof (tc_ref_state (fst p) (fst (snd p)) Hsk Hov HW HU) as Href.
        unfold cnl_pk. split.
        + rewrite Z2Nat.id by apply tr_peakP_nonneg. exact (cnl_pk_sec _ _ (cnl_drain_short _ Href)).
        + intros c. rewrite Z2Nat.id by apply tr_peakP_nonneg.
          pose proof (cnl_pk_cls c (hs_held (fst (snd p))) (map (map (Z_to_bv 8)) (dr_lines (fst (snd p))))).
          pose proof (cnl_drain_bytes (fst p) (fst (snd p)) Hsk Hov HW). lia.
      - split; [cbn; lia|]. intros c. pose proof (pt_s_ge c). cbn. lia. }
    destruct P1 as [P1s P1c]. cbn [map fold_right length]. split.
    + rewrite Nat2Z.inj_add, Nat2Z.inj_succ. lia.
    + intros c. specialize (I2 c). specialize (P1c c). pose proof (pt_s_ge c).
      rewrite Nat2Z.inj_add, Nat2Z.inj_succ. nia.
Qed.

(* an open entry's source is its slot's, the slots are distinct (gn_pairs), so the open pairs' stream bytes are at
   most the mass *)
Lemma lsc_slots_sum : forall (f : nat -> Z) (ps : list (rentry * (hsrc * nat))),
  fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then f (snd (snd p)) else 0) ps) =
  fold_right Z.add 0 (map f (rig_slots ps)).
Proof.
  intros f ps. induction ps as [|p ps IH]; [reflexivity|].
  unfold rig_slots in *. cbn [map concat fold_right]. destruct (re_eof (fst p) =? 0); cbn; rewrite IH; lia.
Qed.
Lemma lsc_seq_sum : forall (g : option hsrc -> Z) (l : list (option hsrc)),
  fold_right Z.add 0 (map (fun k => g (nth k l None)) (seq 0 (length l))) = fold_right Z.add 0 (map g l).
Proof.
  intros g l. induction l as [|a l IH]; [reflexivity|].
  cbn [length seq map fold_right nth]. rewrite <- seq_shift, map_map. cbn [nth]. rewrite IH. reflexivity.
Qed.
Lemma lsc_map_fst_combine : forall (A C : Type) (l : list A) (l' : list C), length l = length l' ->
  map fst (combine l l') = l.
Proof.
  intros A C l. induction l as [|a l IH]; intros [|b l'] E; cbn in *; try reflexivity; try discriminate.
  rewrite IH by lia. reflexivity.
Qed.
Lemma lsc_rig_pb_mass : forall cx t m hs, fr_RINV cx t m -> gn_pairs m hs ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  rig_pb (lm_es m) hs <= pt_mass m.
Proof.
  intros cx t m hs HRI (Hlen & HF & HND) Hoff.
  pose proof HRI as (_ & (Hl4 & _) & _).
  set (f := fun k => slot_pend (nth k (lm_hs m) None)).
  assert (A : forall ps, Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps ->
     fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then pair_bytes (fst p) (fst (snd p)) else 0) ps) <=
     fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then f (snd (snd p)) else 0) ps) +
     fold_right Z.add 0 (map (fun p => pt_eu (fst p)) ps)).
  { induction ps as [|p ps IH]; intros HF'; [cbn; lia|]. inversion HF' as [|? ? Hp HF'']; subst.
    specialize (IH HF''). cbn [map fold_right].
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|pose proof (pt_eu_nonneg (fst p)); lia].
    apply Z.eqb_eq in Eo. destruct (Hp Eo) as (_ & Hn & _).
    assert (E : f (snd (snd p)) = Z.of_nat (length (pending_stream (fst (snd p))))).
    { unfold f. rewrite Hn. symmetry. apply ls3_ps_sp. exact (Hoff _ _ Hn). }
    assert (Ep : pair_bytes (fst p) (fst (snd p)) <= Z.of_nat (length (pending_stream (fst (snd p)))) + pt_eu (fst p))
      by (unfold pair_bytes, pt_eu; destruct (re_skip (fst p) =? 0); lia).
    lia. }
  pose proof (A _ HF) as A1. rewrite lsc_slots_sum in A1.
  assert (A2 : fold_right Z.add 0 (map f (rig_slots (combine (lm_es m) hs))) <=
               fold_right Z.add 0 (map f (seq 0 (length (lm_hs m))))).
  { apply pt_sum_incl.
    - intros k. unfold f. apply pt_pend_nonneg.
    - first [exact HND | apply NoDup_ListNoDup; exact HND].
    - intros k Hk. unfold rig_slots in Hk. apply in_concat in Hk as (l & Hl & Hk).
      apply in_map_iff in Hl as (p & <- & Hp).
      revert Hk. destruct (re_eof (fst p) =? 0) eqn:Eo; intros Hk; [|destruct Hk].
      destruct Hk as [<- | []]. rewrite Forall_forall in HF. apply Z.eqb_eq in Eo.
      destruct (HF p Hp Eo) as (H4 & _). apply in_seq. rewrite Hl4. lia. }
  unfold f in A1, A2. rewrite (lsc_seq_sum slot_pend (lm_hs m)) in A2.
  assert (A3 : fold_right Z.add 0 (map (fun p => pt_eu (fst p)) (combine (lm_es m) hs)) =
               fold_right Z.add 0 (map pt_eu (lm_es m))).
  { rewrite <- (map_map fst pt_eu), lsc_map_fst_combine by lia. reflexivity. }
  unfold rig_pb, pt_mass, pend_bytes. lia.
Qed.
Lemma lsc_rig_ok : forall cx t m hs, fr_RINV cx t m -> gn_pairs m hs ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  rig_ok (lm_es m) hs.
Proof.
  intros cx t m hs HRI (_ & HF & _) HU Hoff. pose proof HRI as (_ & (_ & _ & _ & HE & _) & _).
  unfold rig_ok. rewrite Forall_forall in HF, HU, HE |- *. intros p Hp Eo.
  destruct (HF p Hp Eo) as (_ & Hn & _ & Hov & HW & _).
  destruct p as [e [h k]]. cbn [fst snd] in *.
  pose proof (in_combine_l _ _ _ _ Hp) as He.
  destruct (HE e He) as (_ & _ & _ & _ & Hsk).
  split; [exact Hsk|]. split; [exact Hov|]. split; [exact HW|]. split; [exact (HU e He)|].
  destruct (Hoff k h Hn) as [(_ & ->) | (r & rs & _ & Ho & _)]; lia.
Qed.

(* ARM_gone (top_x's hypothesis, after LS_gone_rig :573): relay_instance_gone, then per entry check_no_loss and
   check_shape_ends *)
Lemma fr_LS3cp_cnt_gone : forall cx t m ly S hs,
  fr_LS3cp B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall k h, nth k (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (acnt Psec (ablocks B ly S) + pk_gone cx m hs Psec <= Lsec)%nat /\
  (acnt P24 (ablocks B ly S) + pk_gone cx m hs P24 <= L24)%nat /\
  (forall c, 1 <= c <= 30 -> (acnt (Pcls c) (ablocks B ly S) + pk_gone cx m hs (Pcls c) <= LPRIM c)%nat).
Proof.
  intros cx t m ly S hs HLS HRI Hgp Hm Ht HU Hpos Hoff.
  pose proof (lsc_rig_ok cx t m hs HRI Hgp HU Hoff) as Hok.
  pose proof (tc_rm_cap m Hpos) as Hcap.
  pose proof (lsc_rig_pb_mass cx t m hs HRI Hgp Hoff) as HPBm.
  assert (HPB0 : 0 <= rig_pb (lm_es m) hs).
  { unfold rig_pb. apply zsum_map_nonneg. intros p. destruct (re_eof (fst p) =? 0); [apply pair_bytes_nonneg | lia]. }
  pose proof (fr_RINV_es_le cx t m HRI) as E4.
  assert (Lc : length (combine (lm_es m) hs) = length (lm_es m)) by (rewrite length_combine; destruct Hgp as (Hl & _); lia).
  destruct (lsc_gn_cnl (combine (lm_es m) hs) Hok) as (G1 & G2). rewrite Lc in G1, G2.
  assert (EPK : forall P, Z.of_nat (pk_gone cx m hs P) =
    tr_peakP P (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) +
    Z.of_nat (fold_right Nat.add 0%nat (map (gn_cnl P) (combine (lm_es m) hs))) + 3).
  { intros P. unfold pk_gone. rewrite !Nat2Z.inj_add. rewrite Z2Nat.id by apply tr_peakP_nonneg. lia. }
  assert (Hn : 0 <= Z.of_nat (length (lm_es m)) <= 4) by lia.
  apply (lsc_room cx t m ly S (pk_gone cx m hs)
           (4 * Z.of_nat (length (lm_es m)) + 1 + 2 * Z.of_nat (length (lm_es m)) + 3)
           (4 * Z.of_nat (length (lm_es m)) + 1 + 2 * Z.of_nat (length (lm_es m)) + 3) HLS HRI Hm Ht).
  - rewrite EPK, lsc_w_sec.
    pose proof (rig_sec_peak (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs
                  Hcap Hok). lia.
  - lia.
  - rewrite EPK. unfold P24. change kBatchClass with 24.
    apply (lsc_pay 24 _ _ (4 * Z.of_nat (length (lm_es m)) + 1) (2 * Z.of_nat (length (lm_es m))) 3 _ _ ltac:(lia)
             (conj HPB0 HPBm)).
    + intros E. lia.
    + intros _. rewrite lsc_w_cls.
      pose proof (rig_cls_peak 24 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs
                    Hcap Hok). nia.
    + exact (G2 24).
  - lia.
  - intros c Hc. rewrite EPK.
    apply (lsc_pay c _ _ (4 * Z.of_nat (length (lm_es m)) + 1) (2 * Z.of_nat (length (lm_es m))) 3 _ _ Hc
             (conj HPB0 HPBm)).
    + intros ->. rewrite lsc_w_cls.
      pose proof (rig_c1_peak (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs
                    Hcap Hok). lia.
    + intros _. rewrite lsc_w_cls.
      pose proof (rig_cls_peak c (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs
                    Hcap Hok). nia.
    + exact (G2 c).
Qed.
End lsc.
