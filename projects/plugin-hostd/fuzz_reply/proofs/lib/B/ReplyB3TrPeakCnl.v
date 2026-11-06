(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyLSBTrPeak.v, with its module paths and module names changed; 892 of its 1054 lines of code are new or changed and 510 lines of the source are left out. *)
(* The image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyTrPeakCnl.v (sha256
   15225bd2ea3e; internal record) at c653c819019, row G-BCNL: A's definitions,
   lemmas, names, statements and proofs over lib/B's records, so that image B's drain arm and top_x can take
   dr_cnl_pk := fun h P => ReplyB3TrPeakCnl.cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P, as A does.
   A's text from its first line after the Requires to its end is kept byte for byte.  The swaps:
   - the Require header: lib/A image files -> lib/B's (YB1v / YE01 YE2k / YCfn / W_* / _drain_defs / _write), as
     lib/B/ReplyB3LS3p.v (A's `Require Import ACfn` -> `Require YCfn`; lib/A/CfParamsReply added, as ReplyB3LS3p);
   - lib/A ReplyLS / ReplyRINV / ReplyLSArms -> lib/B ReplyLSB / ReplyRINVB / ReplyLSBArms;
   - A's ReplyLSDrainPre / ReplyLSRemove3 / ReplyLSRrPre facts -> lib/B/ReplyLSBDrainPre.v, and A's dpre_pair ->
     lib/B/ReplyB3LS3Arms.v (both under A's names);
   - ReplyTrPeak -> lib/B/ReplyLSBTrPeak.v; ReplyTrPeakCnt -> lib/B/ReplyB3TrPeakCnt.v (the helpers this file reads);
     ReplyLS3p -> lib/B/ReplyB3LS3p.v; ReplyLSCntL / ReplyTrPeakW / ReplyCnt -> lib/B's files of those names;
   - A's _event, ReplyLS3, ReplyLS3c, ReplyLSDrain3 and ReplyLSCntM are Required by A's file but none of their names is
     read here, so they are dropped;
   - added after A's header: `Require W_LLVMFuzzerTestOneInput_remove` and Local Notations rm_ent / rm_at / rm_rr_tr
     for _remove.v's names (A read them through ReplyRINV / ReplyLSArms copies, which have no B twin);
   - added at the end: dr_cnl_pk_B, the instance term.
   A's description follows. *)
(* The count half of LS v3, part 7: the count peaks the LS_cnt rows (ReplyLScnt.v) need beyond ReplyTrPeakCnt.v's, for
   a Theorem Labs lane's FREE-PIECES row B1c.  Proves no function (kind: invariant lemma).
   Part A is check_no_loss's count peak (its peak depends on the data: a begin record nets +1 in a class when its key
   is in the class and its line is not).  Part B is a sharper class-1 peak for drain and relay_remove, and the peaks
   of relay_instance_gone, from a walk with two stream budgets.

   PART A.  WHAT IS BOUNDED.  room_live_call_keep (a Theorem Labs lane) needs, at the PRE of every allocator call and for every primary
   class c, ccnt_c c <= RL_PRIM c; inside a callee that is `count at the call + the callee's count peak <= LIM`
   (ReplyTrPeakW.v tr_peak_w_room).  Part A bounds the count peak of check_no_loss's request trace, for the
   class weights and the secondary weight.

   THE TRACE.  For each expected record r (its text ln) check_no_loss_tr runs gesture_model_tr (a begin line whose
   key x is new: list_push_tr = the held vector's growth, malloc 128 when its capacity is 0 and realloc 16 cap ->
   32 cap when it is full, then malloc |x| + 1; an end line whose key is held: list_drop_tr frees that key;
   otherwise nothing), then rec_drop_tr r frees the text (|ln| + 1).  The held vector is ONE live block whose size
   is 16 * sh_cap, so its regrowths telescope: with the potential cnl_phi w s := (0 when sh_cap s = 0, else
   w (16 * sh_cap s)) in [0, 1], one record's piece has peak <= 2 - phi(s) (the regrowth's transient is at most 1,
   its net plus the key at most 1 - phi(s) + 1) and net <= phi(s') - phi(s) + bk2, bk2 := max 0 (w (|x| + 1) -
   w (|ln| + 1)) for a begin line (cnl_bk2: the text's free follows the key's malloc), 0 otherwise (cnl_rec).  The
   pieces compose (cnl_walk), so for any 0/1 weight the peak is at most 2 + the sum of bk2 (cnl_peak_w2: the begin
   records whose key the weight counts and whose text it does not; cnl_pk2 for a predicate), hence at most 2 + the
   sum of bk := w (|x| + 1) over the begin records (cnl_bk, cnl_peak_w).

   THE BOUNDS, at the trace cnl_tr H xs (the held list H, the expected texts xs, every address one constant: the
   peak reads only the request sizes, cnl_tr_names, so any naming of the program's blocks gives the same peak):
   - class c: a begin record whose key is of class c has pt_s c <= |line| + 1 (ReplyLS3p.v pt_s_line), so
     pt_s c * (peak - 2) <= the texts' bytes with their NULs (cnl_pk_cls);
   - secondary: a key is no longer than its line (<= 6,000 bytes), so its request (<= 6,001) is primary and the peak
     is at most 2 (cnl_pk_sec);
   - after a drain the texts are the reference splitter's lines (dr_lines): their bytes are at most pair_bytes
     (SlotReads.lines_bytes, cnl_drain_bytes) and each is at most 6,000 bytes (tc_lines_short, cnl_drain_short).

   PART B.  WHY.  ReplyTrPeakCnt.v's walk pays every kept malloc of a drain from ONE stream budget Bw * tc_bytes, tc_bytes =
   2 * pending + the reference splitter's partial line + the relay's unfinished line (the reference splitter and the
   relay read the same stream).  That gives lo c * peak <= 5 lo c + 2 pair_bytes.  Class 1 (requests of 1..16 bytes)
   is tight: its potential room is 2 counts per mass byte, and 5 + 2 pair_bytes plus check_no_loss's keys overflows
   it.  But the two kinds of kept malloc are paid by DIFFERENT readers:
   - an expected text (list_push_tra's last request, |line| + 1 bytes) by the REFERENCE splitter's bytes
     (SlotReads.lines_bytes: the reference lines with their NULs are at most the fall of tk_refb := pending + the
     splitter's partial line), at Bt per byte;
   - a relay key of a begin line (seen_tr's strndup) by the RELAY's bytes (ReplyLSRemove3.rm3_chunk_mass: the relay
     lines with their NULs are at most the fall of tk_relb := pending + the relay's unfinished line), at Bk per byte
     of its line.
   For class 1 a text of x >= 1 bytes counts at most 1 = 21 x / 21 (Bt = 21 per byte at Lw = 21) and a key at most
   1 <= (|l| + 1) / 21 (Bk = 1 per byte: a begin line has 20 <= |l|, SlotReads.gesture_begin_len).  So
   21 * peak <= 105 + 21 tk_refb + tk_relb = 105 + 22 pair_bytes (tk_init: both budgets are pair_bytes at a drain of
   the model).

   THE WALK.  Section tk is ReplyTrPeakCnt.v's Section piece with the two budgets (its tc_ names renamed tk_): the
   growth of the four one-block chains (s->buf, the expected vector, g_out, s->held) is bounded by the potential
   tk_phi in [0, 4], the kept mallocs by the budgets (hypotheses Hst for the texts, Hsk for the keys), the frees never
   raise a count.  tk_dr / tk_rr: Lw * peak <= 5 Lw + Bt * tk_refb + Bk * tk_relb (at the drain's start).
   tk_rig: relay_instance_gone (Prog/relay_instance_gone_b_c.v gone_run) drains each open table entry in order (from
   the running g_nout / g_capout), then runs gestures_end_instance's key run, and leaves each entry's other blocks
   live.  Each entry's piece starts at a potential >= 0 and ends at one <= 4, so its transient is <= 5 and its net is
   <= 4 (scaled by Lw, plus its budget); composing n entries gives (4 n + 1) Lw plus the summed budgets.

   THE BOUNDS.  Class 1, drain and remove: 21 * peak <= 105 + 22 pair_bytes (fr_LS_drain_c1_peak,
   fr_LS_rm_c1_peak).  relay_instance_gone: secondary peak <= 4 |es| + 1 (rig_sec_peak); class k:
   lo k * peak <= (4 |es| + 1) lo k + 2 rig_pb (rig_cls_peak); class 1: 21 * peak <= 21 (4 |es| + 1) + 22 rig_pb
   (rig_c1_peak); rig_pb sums pair_bytes over the open entries. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSCntL ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3TrPeakCnt ReplyB3LS3p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* B: the remove arm's notions are lib/B/W_LLVMFuzzerTestOneInput_remove.v's, as lib/B/ReplyLSBDrainPre.v reads them
   (A's copies in lib/A/ReplyRINV.v have no image-B twin) *)
Local Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Notation rm_rr_tr := W_LLVMFuzzerTestOneInput_remove.rm_rr_tr.

(* ################################################################## PART A: check_no_loss *)
(* ================================================================== the names *)
(* check_no_loss over the held list H and the expected texts xs, every block named by one constant address *)
Definition cnl_nm (_ : Z) : RelayRunT.addr YO0i.sptr := RelayRunT.Known ListTr.pdefT.
Definition cnl_tr (H : hlist) (xs : list (list byte)) : list (RelayRunT.rev YO0i.sptr) :=
  check_no_loss_tr 0 (ListTr.sh_of cnl_nm H) (map (fun x => (cnl_nm 0, bzs x)) xs).
(* its count peak for the predicate P, as the count premise's nat *)
Definition cnl_pk (H : hlist) (xs : list (list byte)) (P : Z -> bool) : nat :=
  Z.to_nat (ReplyCnt.tr_peakP P (cnl_tr H xs)).
(* what one record may keep: a begin line's key (|x| + 1 bytes) at the weight w *)
Definition cnl_bk (w : Z -> Z) (ln : list Z) : Z :=
  match RelayModel.gesture ln with Some (RelayModel.GBegin, x) => w (Z.of_nat (length x) + 1) | _ => 0 end.
(* the texts' bytes with their NULs *)
Definition cnl_bytes (xs : list (list byte)) : Z := fold_right Z.add 0 (map (fun x => Z.of_nat (length x) + 1) xs).

(* ================================================================== the peak reads only the sizes *)
Definition cnl_ev (ev : RelayRunT.rev YO0i.sptr) : Z * Z * Z :=
  match ev with
  | RelayRunT.RMalloc n => (0, n, 0)
  | RelayRunT.RFree k _ => (1, k, 0)
  | RelayRunT.RRealloc k n _ => (2, k, n)
  end.

Lemma cnl_peakP_ev : forall (P : Z -> bool) (tr1 tr2 : list (RelayRunT.rev YO0i.sptr)),
  map cnl_ev tr1 = map cnl_ev tr2 -> ReplyCnt.tr_peakP P tr1 = ReplyCnt.tr_peakP P tr2.
Proof.
  intros P tr1. induction tr1 as [|e1 t1 IH]; intros [|e2 t2] E; cbn [map] in E; try discriminate; [reflexivity|].
  injection E as E1 Et. specialize (IH t2 Et).
  destruct e1 as [n1|k1 x1|k1 n1 x1], e2 as [n2|k2 x2|k2 n2 x2]; cbn [cnl_ev] in E1; inversion E1; subst;
    cbn [ReplyCnt.tr_peakP]; rewrite IH; reflexivity.
Qed.

Lemma cnl_n : forall s1 s2, ListTr.sh_keys s1 = ListTr.sh_keys s2 -> ListTr.sh_n s1 = ListTr.sh_n s2.
Proof. intros s1 s2 E. unfold ListTr.sh_n. rewrite <- !length_sh_keys, E. reflexivity. Qed.

Lemma cnl_nth_snd : forall s i,
  snd (nth i (ListTr.sh_recs s) (RelayRunT.Known ListTr.pdefT, [])) = nth i (ListTr.sh_keys s) [].
Proof. intros s i. unfold ListTr.sh_keys. exact (eq_sym (map_nth snd (ListTr.sh_recs s) _ i)). Qed.

(* two held lists with the same capacity and keys make the same requests *)
Lemma cnl_gm_ev : forall s1 s2 ln, ListTr.sh_cap s1 = ListTr.sh_cap s2 -> ListTr.sh_keys s1 = ListTr.sh_keys s2 ->
  map cnl_ev (gesture_model_tr s1 ln) = map cnl_ev (gesture_model_tr s2 ln).
Proof.
  intros s1 s2 ln Ec Ek. unfold gesture_model_tr. rewrite Ek.
  destruct (RelayModel.gesture ln) as [[[|] x]|]; [| |reflexivity].
  - destruct (existsb (list_eqb x) (ListTr.sh_keys s2)); [reflexivity|].
    unfold ListTr.list_push_tr, ListTr.list_grow_tr. rewrite (cnl_n s1 s2 Ek), Ec.
    destruct (ListTr.sh_n s2 =? ListTr.sh_cap s2); [destruct (ListTr.sh_cap s2 =? 0)|]; reflexivity.
  - destruct (find_key x (ListTr.sh_keys s2)) as [i|]; [|reflexivity].
    unfold ListTr.list_drop_tr, ListTr.rec_drop_tr, ListTr.rec_len. cbn [map cnl_ev].
    rewrite !cnl_nth_snd, Ek. reflexivity.
Qed.

Lemma cnl_gm_sh : forall j1 j2 s1 s2 ln, ListTr.sh_cap s1 = ListTr.sh_cap s2 -> ListTr.sh_keys s1 = ListTr.sh_keys s2 ->
  ListTr.sh_cap (gesture_model_sh j1 s1 ln) = ListTr.sh_cap (gesture_model_sh j2 s2 ln) /\
  ListTr.sh_keys (gesture_model_sh j1 s1 ln) = ListTr.sh_keys (gesture_model_sh j2 s2 ln).
Proof.
  intros j1 j2 s1 s2 ln Ec Ek. unfold gesture_model_sh. rewrite Ek.
  destruct (RelayModel.gesture ln) as [[[|] x]|]; [| |split; assumption].
  - destruct (existsb (list_eqb x) (ListTr.sh_keys s2)); [split; assumption|].
    unfold ListTr.list_push_sh. rewrite (cnl_n s1 s2 Ek), Ec.
    destruct (ListTr.sh_n s2 =? ListTr.sh_cap s2); cbn [ListTr.sh_cap]; (split; [reflexivity|]);
      unfold ListTr.sh_keys in *; cbn [ListTr.sh_recs]; rewrite !map_app, Ek; reflexivity.
  - destruct (find_key x (ListTr.sh_keys s2)) as [i|]; [|split; assumption].
    unfold ListTr.list_drop_sh. cbn [ListTr.sh_cap]. split; [exact Ec|].
    unfold ListTr.sh_keys in *; cbn [ListTr.sh_recs]. rewrite !map_app, <- !firstn_map, <- !skipn_map, Ek.
    reflexivity.
Qed.

Lemma cnl_names_walk : forall rs1 rs2 j1 j2 s1 s2,
  map snd rs1 = map snd rs2 -> ListTr.sh_cap s1 = ListTr.sh_cap s2 -> ListTr.sh_keys s1 = ListTr.sh_keys s2 ->
  map cnl_ev (check_no_loss_tr j1 s1 rs1) = map cnl_ev (check_no_loss_tr j2 s2 rs2).
Proof.
  induction rs1 as [|r1 t1 IH]; intros [|r2 t2] j1 j2 s1 s2 Er Ec Ek; cbn [map] in Er; try discriminate;
    [reflexivity|].
  injection Er as Er1 Ert. cbn [check_no_loss_tr]. rewrite !map_app.
  destruct (cnl_gm_sh j1 j2 s1 s2 (snd r1) Ec Ek) as [Ec' Ek'].
  rewrite (cnl_gm_ev s1 s2 (snd r1) Ec Ek). rewrite Er1 in Ec', Ek' |- *.
  assert (Ed : map cnl_ev (ListTr.rec_drop_tr r1) = map cnl_ev (ListTr.rec_drop_tr r2))
    by (unfold ListTr.rec_drop_tr, ListTr.rec_len; cbn [map cnl_ev]; rewrite Er1; reflexivity).
  rewrite Ed.
  match goal with |- _ ++ _ ++ map cnl_ev (check_no_loss_tr ?ja ?sa t1) =
                     _ ++ _ ++ map cnl_ev (check_no_loss_tr ?jb ?sb t2) =>
    rewrite (IH t2 ja jb sa sb Ert Ec' Ek') end.
  reflexivity.
Qed.

Lemma cnl_tr_names : forall (j : nat) (nm : Z -> RelayRunT.addr YO0i.sptr) (H E : hlist) (P : Z -> bool),
  ReplyCnt.tr_peakP P (check_no_loss_tr j (ListTr.sh_of nm H) (map (ListTr.shr nm) (hl_recs E))) =
  ReplyCnt.tr_peakP P (cnl_tr H (map snd (hl_recs E))).
Proof.
  intros j nm H E P. unfold cnl_tr. apply cnl_peakP_ev. apply cnl_names_walk.
  - rewrite !map_map. reflexivity.
  - reflexivity.
  - unfold ListTr.sh_keys, ListTr.sh_of. cbn [ListTr.sh_recs]. rewrite !map_map. reflexivity.
Qed.

(* ================================================================== the walk, for any 0/1 weight *)
(* the sharper share of one record: a begin line's key counts only when its weight exceeds its line's (the text
   the record frees right after the key's malloc); at a 0/1 weight, a key that the weight counts in a line it does
   not *)
Definition cnl_bk2 (w : Z -> Z) (ln : list Z) : Z :=
  match RelayModel.gesture ln with
  | Some (RelayModel.GBegin, x) => Z.max 0 (w (Z.of_nat (length x) + 1) - w (Z.of_nat (length ln) + 1))
  | _ => 0
  end.

Section cnl_w.
Variable w : Z -> Z.
Hypothesis Hw : forall x, 0 <= w x <= 1.

(* the held vector's weight: 0 while it is NULL *)
Definition cnl_phi (s : ListTr.shl) : Z := if ListTr.sh_cap s =? 0 then 0 else w (16 * ListTr.sh_cap s).

Lemma cnl_phi_range : forall s, 0 <= cnl_phi s <= 1.
Proof. intros s. unfold cnl_phi. destruct (ListTr.sh_cap s =? 0); [lia | apply Hw]. Qed.
Lemma cnl_bk2_range : forall ln, 0 <= cnl_bk2 w ln <= cnl_bk w ln.
Proof.
  intros ln. unfold cnl_bk2, cnl_bk. destruct (RelayModel.gesture ln) as [[[|] x]|]; [|lia|lia].
  pose proof (Hw (Z.of_nat (length x) + 1)). pose proof (Hw (Z.of_nat (length ln) + 1)). lia.
Qed.
Lemma cnl_sum_le : forall rs : list (RelayRunT.addr YO0i.sptr * list Z),
  0 <= fold_right Z.add 0 (map (fun r => cnl_bk2 w (snd r)) rs) <=
  fold_right Z.add 0 (map (fun r => cnl_bk w (snd r)) rs).
Proof.
  induction rs as [|r rs IH]; cbn [map fold_right]; [lia|]. pose proof (cnl_bk2_range (snd r)). lia.
Qed.

Ltac cnl_fin :=
  unfold tr_peak_w, tr_net_w; cbn [fold_right app ListTr.sh_cap];
  repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end;
  repeat match goal with |- context [w ?a] =>
    lazymatch goal with _ : 0 <= w a <= 1 |- _ => fail | _ => pose proof (Hw a) end end;
  lia.

(* one record: the held vector's regrowth (one live block), the key it keeps, the text it frees *)
Lemma cnl_rec : forall j s r,
  tr_peak_w w (gesture_model_tr s (snd r) ++ ListTr.rec_drop_tr r) <= 2 - cnl_phi s /\
  tr_net_w w (gesture_model_tr s (snd r) ++ ListTr.rec_drop_tr r) <=
    cnl_phi (gesture_model_sh j s (snd r)) - cnl_phi s + cnl_bk2 w (snd r).
Proof.
  intros j s [a ln]. cbn [snd].
  unfold gesture_model_tr, gesture_model_sh, cnl_bk2, ListTr.rec_drop_tr, ListTr.rec_len, cnl_phi. cbn [snd].
  destruct (RelayModel.gesture ln) as [[[|] x]|].
  - destruct (existsb (list_eqb x) (ListTr.sh_keys s)); [cnl_fin|].
    unfold ListTr.list_push_tr, ListTr.list_grow_tr, ListTr.list_push_sh, ListRep.grow_cap. cbv beta.
    destruct (Z.eqb_spec (ListTr.sh_n s) (ListTr.sh_cap s)) as [En|En].
    + destruct (Z.eqb_spec (ListTr.sh_cap s) 0) as [E0|E0].
      * cbn [ListTr.sh_cap]. change (16 * 8) with 128. cnl_fin.
      * cbn [ListTr.sh_cap]. replace (16 * (2 * ListTr.sh_cap s)) with (32 * ListTr.sh_cap s) by lia. cnl_fin.
    + cnl_fin.
  - destruct (find_key x (ListTr.sh_keys s)) as [i|]; [|cnl_fin].
    unfold ListTr.list_drop_tr, ListTr.list_drop_sh, ListTr.rec_drop_tr. cnl_fin.
  - cnl_fin.
Qed.

Lemma cnl_walk : forall rs j s,
  tr_peak_w w (check_no_loss_tr j s rs) <= 2 - cnl_phi s + fold_right Z.add 0 (map (fun r => cnl_bk2 w (snd r)) rs).
Proof.
  induction rs as [|r rs IH]; intros j s.
  - cbn [check_no_loss_tr map fold_right]. change (tr_peak_w w (@nil (RelayRunT.rev YO0i.sptr))) with 0.
    pose proof (cnl_phi_range s). lia.
  - cbn [check_no_loss_tr map fold_right]. rewrite app_assoc, tr_peak_w_app.
    destruct (cnl_rec j s r) as [P N].
    match goal with |- context [check_no_loss_tr ?j' ?s' rs] => pose proof (IH j' s') as I end.
    pose proof (cnl_bk2_range (snd r)). pose proof (cnl_sum_le rs).
    lia.
Qed.
End cnl_w.

(* the sharper bound: 2 + the begin records whose key's weight exceeds their line's *)
Lemma cnl_peak_w2 : forall w : Z -> Z, (forall x, 0 <= w x <= 1) -> forall j s rs,
  ReplyTrPeakW.tr_peak_w w (check_no_loss_tr j s rs) <= 2 + fold_right Z.add 0 (map (fun r => cnl_bk2 w (snd r)) rs).
Proof.
  intros w Hw j s rs. pose proof (cnl_walk w Hw rs j s). pose proof (cnl_phi_range w Hw s). lia.
Qed.

Lemma cnl_peak_w : forall w : Z -> Z, (forall x, 0 <= w x <= 1) -> forall j s rs,
  ReplyTrPeakW.tr_peak_w w (check_no_loss_tr j s rs) <= 2 + fold_right Z.add 0 (map (fun r => cnl_bk w (snd r)) rs).
Proof.
  intros w Hw j s rs. pose proof (cnl_peak_w2 w Hw j s rs). pose proof (cnl_sum_le w Hw rs). lia.
Qed.

(* ================================================================== the class and secondary peaks *)
Lemma cnl_bk_sum_cls : forall c xs,
  pt_s c * fold_right Z.add 0 (map (fun r => cnl_bk (fun n => ReplyCnt.zb (ReplyCnt.Pcls c n)) (snd r))
                                 (map (fun x => (cnl_nm 0, bzs x)) xs)) <= cnl_bytes xs.
Proof.
  intros c xs. pose proof (pt_s_ge c) as Hs. unfold cnl_bytes.
  induction xs as [|x xs IH]; cbn [map fold_right snd]; [lia|].
  rewrite Z.mul_add_distr_l.
  enough (pt_s c * cnl_bk (fun n => ReplyCnt.zb (ReplyCnt.Pcls c n)) (bzs x) <= Z.of_nat (length x) + 1) by lia.
  unfold cnl_bk. destruct (RelayModel.gesture (bzs x)) as [[[|] k]|] eqn:G; [|lia|lia].
  unfold ReplyCnt.zb, ReplyCnt.Pcls. destruct (PresetRoom.in_cls c (Z.of_nat (length k) + 1)) eqn:Ec; [|lia].
  pose proof (pt_s_line c (bzs x) k G Ec) as L. rewrite RelayCap.rc_length_bzs in L. lia.
Qed.

Lemma cnl_pk_cls : forall c H xs,
  pt_s c * (ReplyCnt.tr_peakP (ReplyCnt.Pcls c) (cnl_tr H xs) - 2) <= cnl_bytes xs.
Proof.
  intros c H xs. rewrite ReplyCnt.tr_peakP_w. unfold cnl_tr.
  assert (Hw : forall x, 0 <= (fun n => ReplyCnt.zb (ReplyCnt.Pcls c n)) x <= 1)
    by (intros x; cbv beta; unfold ReplyCnt.zb; destruct (ReplyCnt.Pcls c x); lia).
  pose proof (cnl_peak_w _ Hw 0%nat (ListTr.sh_of cnl_nm H) (map (fun x => (cnl_nm 0, bzs x)) xs)) as P.
  pose proof (cnl_bk_sum_cls c xs) as S. pose proof (pt_s_ge c) as Hs.
  match type of P with ?pk <= 2 + ?sm =>
    assert (M : pt_s c * (pk - 2) <= pt_s c * sm) by (apply Z.mul_le_mono_nonneg_l; lia) end.
  lia.
Qed.

Lemma cnl_bk_sum_sec : forall xs, Forall (fun x => Z.of_nat (length x) <= 6000) xs ->
  fold_right Z.add 0 (map (fun r => cnl_bk (fun n => ReplyCnt.zb (ReplyCnt.Psec n)) (snd r))
                        (map (fun x => (cnl_nm 0, bzs x)) xs)) <= 0.
Proof.
  intros xs Hf. induction Hf as [|x xs Hx _ IH]; cbn [map fold_right snd]; [lia|].
  enough (cnl_bk (fun n => ReplyCnt.zb (ReplyCnt.Psec n)) (bzs x) <= 0) by lia.
  unfold cnl_bk. destruct (RelayModel.gesture (bzs x)) as [[[|] k]|] eqn:G; [|lia|lia].
  pose proof (dpre_gesture_len _ _ _ G) as L. rewrite RelayCap.rc_length_bzs in L.
  rewrite ReplyLSCntL.is_sec_iff by lia.
  assert (E : (64513 <=? Z.of_nat (length k) + 1) = false) by (apply Z.leb_gt; lia).
  rewrite E. unfold ReplyCnt.zb. lia.
Qed.

Lemma cnl_pk_sec : forall H xs, Forall (fun x => Z.of_nat (length x) <= 6000) xs ->
  ReplyCnt.tr_peakP ReplyCnt.Psec (cnl_tr H xs) <= 2.
Proof.
  intros H xs Hf. rewrite ReplyCnt.tr_peakP_w. unfold cnl_tr.
  assert (Hw : forall x, 0 <= (fun n => ReplyCnt.zb (ReplyCnt.Psec n)) x <= 1)
    by (intros x; cbv beta; unfold ReplyCnt.zb; destruct (ReplyCnt.Psec x); lia).
  pose proof (cnl_peak_w _ Hw 0%nat (ListTr.sh_of cnl_nm H) (map (fun x => (cnl_nm 0, bzs x)) xs)) as P.
  pose proof (cnl_bk_sum_sec xs Hf) as S. lia.
Qed.

(* the sharper bound for a predicate P: 2 + the begin texts whose key's request satisfies P and whose own does not *)
Definition cnl_nk2 (P : Z -> bool) (xs : list (list byte)) : nat :=
  length (List.filter (fun x => match RelayModel.gesture (bzs x) with
                           | Some (RelayModel.GBegin, k) =>
                               P (Z.of_nat (length k) + 1) && negb (P (Z.of_nat (length x) + 1))
                           | _ => false
                           end) xs).

Lemma cnl_pk2 : forall P H xs, ReplyCnt.tr_peakP P (cnl_tr H xs) <= 2 + Z.of_nat (cnl_nk2 P xs).
Proof.
  intros P H xs. rewrite ReplyCnt.tr_peakP_w. unfold cnl_tr.
  assert (Hw : forall x, 0 <= (fun n => ReplyCnt.zb (P n)) x <= 1)
    by (intros x; cbv beta; unfold ReplyCnt.zb; destruct (P x); lia).
  pose proof (cnl_peak_w2 _ Hw 0%nat (ListTr.sh_of cnl_nm H) (map (fun x => (cnl_nm 0, bzs x)) xs)) as Pk.
  enough (S : fold_right Z.add 0 (map (fun r => cnl_bk2 (fun n => ReplyCnt.zb (P n)) (snd r))
                                     (map (fun x => (cnl_nm 0, bzs x)) xs)) = Z.of_nat (cnl_nk2 P xs)) by lia.
  unfold cnl_nk2. clear Pk. induction xs as [|x xs IH]; [reflexivity|].
  cbn [map fold_right snd List.filter]. rewrite IH. unfold cnl_bk2. rewrite RelayCap.rc_length_bzs.
  destruct (RelayModel.gesture (bzs x)) as [[[|] k]|]; cbn [andb negb length]; [|lia|lia].
  unfold ReplyCnt.zb. destruct (P (Z.of_nat (length k) + 1)), (P (Z.of_nat (length x) + 1)); cbn [andb negb length];
    lia.
Qed.

(* ================================================================== after a drain: the texts are the lines *)
Lemma cnl_bytes_lines : forall ls : list (list Z),
  cnl_bytes (map (map (Z_to_bv 8)) ls) = Z.of_nat (length (RelayModel.with_nul ls)).
Proof.
  induction ls as [|l ls IH]; [reflexivity|]. unfold cnl_bytes in *. cbn [map fold_right].
  rewrite RelayCap.with_nul_cons_len, length_map, IH. lia.
Qed.

(* the splitter's partial line is the relay's when it keeps it (fr_pair_ok's relay / splitter clause) *)
Lemma cnl_wcost_state : forall e h, (re_skip e = 0 \/ re_skip e = 1) -> re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  SlotReads.wcost (hs_state h) = (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0).
Proof.
  intros e h Hsk Ho Hu. unfold SlotReads.wcost, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
  rewrite <- Ho. destruct Hsk as [E|E].
  - pose proof (Hu E) as Eu. rewrite E. cbn [Z.eqb]. rewrite <- Eu, !RelayCap.rc_length_bzs. reflexivity.
  - rewrite E. reflexivity.
Qed.

Lemma cnl_drain_bytes : forall e h, (re_skip e = 0 \/ re_skip e = 1) -> re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  cnl_bytes (map (map (Z_to_bv 8)) (dr_lines h)) <= pair_bytes e h.
Proof.
  intros e h Hsk Ho Hu. rewrite cnl_bytes_lines. unfold dr_lines, pair_bytes.
  pose proof (SlotReads.lines_bytes (bzs (pending_stream h)) (hs_state h)) as LB.
  pose proof (SlotReads.wcost_nonneg (RelayModel.feed (hs_state h) (bzs (pending_stream h)))) as W0.
  rewrite RelayCap.rc_length_bzs, (cnl_wcost_state e h Hsk Ho Hu) in LB.
  destruct (re_skip e =? 0); lia.
Qed.

Lemma cnl_drain_short : forall h, tc_ref (hs_state h) ->
  Forall (fun x => Z.of_nat (length x) <= 6000) (map (map (Z_to_bv 8)) (dr_lines h)).
Proof.
  intros h Hr. destruct (tc_lines_short (bzs (pending_stream h)) (hs_state h) Hr) as [L _].
  unfold dr_lines. rewrite Forall_map. eapply Forall_impl; [|exact L].
  intros l Hl. rewrite length_map. exact Hl.
Qed.

(* ################################################################## PART B: two budgets *)
(* ================================================================== the two budgets a drain still has *)
(* the reference splitter's: the pending bytes and its partial line *)
Definition tk_refb (s : drain_b_c.dstate) : Z := tp_R s + SlotReads.wcost (drain_b_c.ds_ref s).
(* the relay's: the pending bytes and its unfinished line when it keeps it *)
Definition tk_relb (s : drain_b_c.dstate) : Z := tp_R s + tp_U s.

Lemma tk_refb_nonneg : forall s, 0 <= tk_refb s.
Proof. intros s. unfold tk_refb, tp_R. pose proof (SlotReads.wcost_nonneg (drain_b_c.ds_ref s)). lia. Qed.
Lemma tk_relb_nonneg : forall s, 0 <= tk_relb s.
Proof. intros s. unfold tk_relb, tp_R, tp_U. destruct (drain_b_c.ds_skip s); lia. Qed.

(* ================================================================== the walk, for any 0/1 weight, two budgets *)
Section tk.
Variable w : Z -> Z.
Variables Lw Bt Bk : Z.
Hypothesis Hw : forall x, 0 <= w x <= 1.
Hypothesis HL : 0 <= Lw.
Hypothesis Ht : 0 <= Bt.
Hypothesis Hk : 0 <= Bk.
Hypothesis Hst : forall x, 1 <= x <= 6001 -> Lw * w x <= Bt * x.
Hypothesis Hsk : forall l x, RelayModel.gesture l = Some (RelayModel.GBegin, x) -> Z.of_nat (length l) <= 6000 ->
  Lw * w (Z.of_nat (length x) + 1) <= Bk * (Z.of_nat (length l) + 1).

(* a one-block chain's weight: 0 while NULL *)
Definition tk_wz (n : Z) : Z := if n =? 0 then 0 else w n.
(* a piece of a trace from potential f0 to f1 that spends b: its transient within 5 - f0 above its start, its net
   within f1 - f0 (scaled by Lw, b paid from the two budgets) *)
Definition tk_pc (tr : list (RelayRunT.rev YO0i.sptr)) (f0 f1 b : Z) : Prop :=
  Lw * tr_peak_w w tr <= Lw * (5 - f0) + b /\ Lw * tr_net_w w tr <= Lw * (f1 - f0) + b.

Lemma tk_wz_range : forall n, 0 <= tk_wz n <= 1.
Proof. intros n. unfold tk_wz. destruct (n =? 0); [lia | apply Hw]. Qed.
Lemma tk_wz_nz : forall n, n <> 0 -> tk_wz n = w n.
Proof. intros n H. unfold tk_wz. rewrite (proj2 (Z.eqb_neq n 0) H). reflexivity. Qed.
Lemma tk_wz_0 : tk_wz 0 = 0.
Proof. reflexivity. Qed.

Lemma tk_nil : forall f, f <= 5 -> tk_pc [] f f 0.
Proof.
  intros f Hf. unfold tk_pc. change (tr_peak_w w (@nil (RelayRunT.rev YO0i.sptr))) with 0.
  change (tr_net_w w (@nil (RelayRunT.rev YO0i.sptr))) with 0.
  split; nia.
Qed.
Lemma tk_app : forall t1 t2 f0 f1 f2 b1 b2, tk_pc t1 f0 f1 b1 -> tk_pc t2 f1 f2 b2 -> 0 <= b2 ->
  tk_pc (t1 ++ t2) f0 f2 (b1 + b2).
Proof.
  intros t1 t2 f0 f1 f2 b1 b2 (P1 & N1) (P2 & N2) Hb. unfold tk_pc.
  rewrite tr_peak_w_app, tr_net_w_app. split.
  - destruct (Z.max_spec (tr_peak_w w t1) (tr_net_w w t1 + tr_peak_w w t2)) as [[_ E]|[_ E]]; rewrite E; nia.
  - nia.
Qed.
Lemma tk_le : forall tr f0 f1 b b', tk_pc tr f0 f1 b -> b <= b' -> tk_pc tr f0 f1 b'.
Proof. intros tr f0 f1 b b' (P1 & N1) H. unfold tk_pc. split; lia. Qed.
Lemma tk_eq : forall tr f0 f1 f0' f1' b, tk_pc tr f0 f1 b -> f0 = f0' -> f1 = f1' -> tk_pc tr f0' f1' b.
Proof. intros; subst; assumption. Qed.

(* one regrowth of a chain block, malloc when it is NULL *)
Lemma tk_mc : forall c f, c <> 0 -> f <= 4 -> tk_pc [RelayRunT.RMalloc c] f (f + tk_wz c) 0.
Proof.
  intros c f Hc Hf. rewrite (tk_wz_nz c Hc). pose proof (Hw c) as Wc.
  unfold tk_pc, tr_peak_w, tr_net_w. cbn [fold_right]. rewrite !Z.add_0_r, (Z.max_r 0 (w c)) by lia.
  split; nia.
Qed.
Lemma tk_rc : forall o c (x : RelayRunT.addr YO0i.sptr) f, o <> 0 -> c <> 0 -> f <= 4 ->
  tk_pc [RelayRunT.RRealloc o c x] f (f - tk_wz o + tk_wz c) 0.
Proof.
  intros o c x f Ho Hc Hf. rewrite (tk_wz_nz c Hc), (tk_wz_nz o Ho). pose proof (Hw c) as Wc. pose proof (Hw o) as Wo.
  unfold tk_pc, tr_peak_w, tr_net_w. cbn [fold_right]. rewrite !Z.add_0_r.
  rewrite (Z.max_l (w c) (w c - w o)) by lia. rewrite (Z.max_r 0 (w c)) by lia.
  split; nia.
Qed.
Lemma tk_grow : forall o c (x : RelayRunT.addr YO0i.sptr) f, c <> 0 -> f <= 4 ->
  tk_pc [if o =? 0 then RelayRunT.RMalloc c else RelayRunT.RRealloc o c x] f (f - tk_wz o + tk_wz c) 0.
Proof.
  intros o c x f Hc Hf. destruct (Z.eqb_spec o 0) as [E|E].
  - subst o. rewrite tk_wz_0, Z.sub_0_r. apply tk_mc; assumption.
  - apply tk_rc; assumption.
Qed.
(* a kept malloc paid by b *)
Lemma tk_mal : forall x f b, Lw * w x <= b -> f <= 5 -> tk_pc [RelayRunT.RMalloc x] f f b.
Proof.
  intros x f b Hb Hf. pose proof (Hw x) as Wx.
  unfold tk_pc, tr_peak_w, tr_net_w. cbn [fold_right]. rewrite !Z.add_0_r, (Z.max_r 0 (w x)) by lia.
  split; nia.
Qed.
(* an expected text: a reference line's bytes, at Bt each *)
Lemma tk_text : forall x f, 1 <= x <= 6001 -> f <= 5 -> tk_pc [RelayRunT.RMalloc x] f f (Bt * x).
Proof. intros x f Hx Hf. apply tk_mal; [apply Hst; exact Hx | exact Hf]. Qed.
(* a relay key: its begin line's bytes, at Bk each *)
Lemma tk_key : forall l x f, RelayModel.gesture l = Some (RelayModel.GBegin, x) -> Z.of_nat (length l) <= 6000 ->
  f <= 5 -> tk_pc [RelayRunT.RMalloc (Z.of_nat (length x) + 1)] f f (Bk * (Z.of_nat (length l) + 1)).
Proof. intros l x f G Hl Hf. apply tk_mal; [apply Hsk; assumption | exact Hf]. Qed.
(* a free *)
Lemma tk_free : forall k (x : RelayRunT.addr YO0i.sptr) f, f <= 5 -> tk_pc [RelayRunT.RFree k x] f f 0.
Proof.
  intros k x f Hf. pose proof (Hw k) as Wk.
  unfold tk_pc, tr_peak_w, tr_net_w. cbn [fold_right]. rewrite !Z.add_0_r, (Z.max_l 0 (0 - w k)) by lia.
  split; nia.
Qed.
Lemma tk_cons_free : forall k (x : RelayRunT.addr YO0i.sptr) l f0 f1 b, f0 <= 5 -> tk_pc l f0 f1 b -> 0 <= b ->
  tk_pc (RelayRunT.RFree k x :: l) f0 f1 b.
Proof.
  intros k x l f0 f1 b Hf H Hb. change (RelayRunT.RFree k x :: l) with ([RelayRunT.RFree k x] ++ l).
  replace b with (0 + b) by lia. apply (tk_app _ _ _ f0); [apply tk_free; exact Hf | exact H | exact Hb].
Qed.
Lemma tk_bud_nonneg : forall a b c d, b <= a -> d <= c -> 0 <= Bt * (a - b) + Bk * (c - d).
Proof.
  intros a b c d H1 H2. pose proof (Z.mul_nonneg_nonneg Bt (a - b) Ht ltac:(lia)).
  pose proof (Z.mul_nonneg_nonneg Bk (c - d) Hk ltac:(lia)). lia.
Qed.

(* ---- send_line: g_out's regrowths *)
Lemma tk_sl_run : forall fu mx no cap rem j o A, 0 <= cap -> 0 <= A <= 3 ->
  tk_pc (fst (send_line_b_c.sl_run fu mx no cap rem j o)) (A + tk_wz cap)
     (A + tk_wz (fst (snd (send_line_b_c.sl_run fu mx no cap rem j o)))) 0 /\
  0 <= fst (snd (send_line_b_c.sl_run fu mx no cap rem j o)).
Proof.
  induction fu as [|fu IH]; intros mx no cap rem j o A Hc HA; pose proof (tk_wz_range cap) as Wc;
    cbn [send_line_b_c.sl_run].
  - cbn [fst snd]. split; [apply tk_nil; lia | exact Hc].
  - destruct (rem <=? 0); [cbn [fst snd]; split; [apply tk_nil; lia | exact Hc]|].
    match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
    destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; [|cbv beta iota; apply IH; assumption].
    cbn [fst snd].
    destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) A ltac:(lia) HA) as [I1 I2].
    split; [|exact I2].
    match goal with |- tk_pc (?e :: ?l) _ _ _ => change (e :: l) with ([e] ++ l) end.
    eapply tk_le.
    { eapply (tk_app _ _ _ (A + tk_wz ((no + n) * 2))); [| exact I1 | lia].
      eapply tk_eq; [apply (tk_grow cap ((no + n) * 2) o (A + tk_wz cap)); lia | reflexivity | lia]. }
    lia.
Qed.
Lemma tk_send_line : forall live mx no cap len j o A, 0 <= cap -> 0 <= A <= 3 ->
  tk_pc (send_line_b_c.send_line_tr live mx no cap len j o) (A + tk_wz cap)
     (A + tk_wz (send_line_b_c.send_line_cap live mx no cap len)) 0 /\
  0 <= send_line_b_c.send_line_cap live mx no cap len.
Proof.
  intros live mx no cap len j o A Hc HA. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct live.
  - destruct (tk_sl_run (Z.to_nat len) mx no cap len j o A Hc HA) as [P1 P2].
    rewrite sl_run_fin in P1, P2 |- *. split; assumption.
  - split; [apply tk_nil; pose proof (tk_wz_range cap); lia | exact Hc].
Qed.

(* ---- gesture_seen: the held array's regrowth and the key's strndup (paid by the relay's line), or a key's free *)
Lemma tk_seen : forall H ka l j ha ks A, Z.of_nat (length l) <= 6000 -> 0 <= A <= 3 ->
  tk_pc (fst (fst (drain_b_c.seen_tr H ka l j ha ks))) (A + tk_wz ka)
     (A + tk_wz (snd (fst (drain_b_c.seen_tr H ka l j ha ks)))) (Bk * (Z.of_nat (length l) + 1)).
Proof.
  intros H ka l j ha ks A Hl HA. pose proof (tk_wz_range ka) as Wk. unfold drain_b_c.seen_tr.
  assert (B0 : 0 <= Bk * (Z.of_nat (length l) + 1)) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (RelayModel.gesture l) as [[kd x]|] eqn:G; [|cbn [fst snd]; eapply tk_le; [apply tk_nil; lia | exact B0]].
  destruct kd; destruct (index_of x H) as [nn|] eqn:EI; cbn [fst snd].
  - eapply tk_le; [apply tk_nil; lia | exact B0].
  - set (c := (Z.of_nat (length H) + 1) * 8).
    pose proof (tk_wz_range c) as Wc.
    match goal with |- tk_pc [?e1; ?e2] _ _ _ => change [e1; e2] with ([e1] ++ [e2]) end.
    replace (Bk * (Z.of_nat (length l) + 1)) with (0 + Bk * (Z.of_nat (length l) + 1)) by lia.
    eapply tk_app; [| apply (tk_key l x (A + tk_wz c) G Hl); lia | exact B0].
    eapply tk_eq; [apply (tk_grow ka c ha (A + tk_wz ka)); unfold c; lia | reflexivity | lia].
  - apply tk_cons_free; [lia | eapply tk_le; [apply tk_nil; lia | exact B0] | exact B0].
  - eapply tk_le; [apply tk_nil; lia | exact B0].
Qed.

(* ---- the relayed lines: each send_line, then gesture_seen; the keys at Bk per relay line byte *)
Lemma tk_lines : forall ls live mx no cap H ka j o ha ks tr oc H' ka' ad A, 0 <= cap -> 0 <= A <= 2 ->
  Forall (fun l => Z.of_nat (length l) <= 6000) ls ->
  drain_b_c.lines_run live mx no cap H ka ls j o ha ks = (tr, (oc, H', ka'), ad) ->
  tk_pc tr (A + tk_wz cap + tk_wz ka) (A + tk_wz oc + tk_wz ka')
    (Bk * Z.of_nat (length (RelayModel.with_nul ls))) /\ 0 <= oc.
Proof.
  induction ls as [|l ls IH]; intros live mx no cap H ka j o ha ks tr oc H' ka' ad A Hc HA HF E.
  - cbn [drain_b_c.lines_run] in E. injection E as <- <- <- <- <-.
    rewrite RelayCap.with_nul_nil_len, Z.mul_0_r. pose proof (tk_wz_range cap). pose proof (tk_wz_range ka).
    split; [apply tk_nil; lia | exact Hc].
  - inversion HF as [|? ? Hl HF']; subst.
    cbn [drain_b_c.lines_run] in E. cbv zeta in E.
    match type of E with context [drain_b_c.lines_run live mx ?n2 ?c2 ?H2 ?k2 ls ?j2 ?o2 ?h2 ?s2] =>
      destruct (drain_b_c.lines_run live mx n2 c2 H2 k2 ls j2 o2 h2 s2) as [[tr2 [[oc2 H2'] ka2]] ad2] eqn:E2 end.
    cbn [fst snd] in E. injection E as <- <- <- <- <-.
    rewrite RelayCap.with_nul_cons_len.
    pose proof (tk_wz_range ka) as Wk. pose proof (tk_wz_range cap) as Wc.
    destruct (tk_send_line live mx no cap (Z.of_nat (length l) + 1) j o (A + tk_wz ka) Hc ltac:(lia)) as [S1 S2].
    set (c1 := send_line_b_c.send_line_cap live mx no cap (Z.of_nat (length l) + 1)) in *.
    pose proof (tk_wz_range c1) as Wc1.
    match goal with |- context [drain_b_c.seen_tr H ka l ?jj ha ks] =>
      pose proof (tk_seen H ka l jj ha ks (A + tk_wz c1) Hl ltac:(lia)) as T1 end.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A S2 HA HF' E2) as [I1 I2].
    split; [|exact I2].
    assert (B1 : 0 <= Bk * (Z.of_nat (length l) + 1)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (B2 : 0 <= Bk * Z.of_nat (length (RelayModel.with_nul ls))) by (apply Z.mul_nonneg_nonneg; lia).
    eapply tk_le.
    { eapply tk_app; [eapply tk_eq; [exact S1 | lia | reflexivity] | | ].
      - eapply tk_app; [eapply tk_eq; [exact T1 | lia | reflexivity] | eapply tk_eq; [exact I1 | lia | reflexivity] | ].
        exact B2.
      - lia. }
    lia.
Qed.

(* ---- reference_feed's pushes: the vector's regrowth, then the text at Bt per reference line byte *)
Lemma tk_push : forall v n cap x A, 0 <= x <= 6000 -> 0 <= A <= 3 ->
  tk_pc (ListTr.list_push_tra v n cap x) (A + tk_wz (16 * cap)) (A + tk_wz (16 * drain_b_c.push_cap n cap))
    (Bt * (x + 1)).
Proof.
  intros v n cap x A Hx HA. unfold ListTr.list_push_tra, drain_b_c.push_cap.
  pose proof (tk_wz_range (16 * cap)) as W0.
  assert (B1 : 0 <= Bt * (x + 1)) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (Z.eqb_spec n cap) as [En|En]; [destruct (Z.eqb_spec cap 0) as [E0|E0]|]; cbv beta iota.
  - rewrite E0. change (16 * 0) with 0. change (16 * 8) with 128. rewrite tk_wz_0.
    pose proof (tk_wz_range 128) as W1.
    replace (Bt * (x + 1)) with (0 + Bt * (x + 1)) by lia.
    eapply tk_app; [| apply tk_text; lia | exact B1].
    eapply tk_eq; [apply (tk_mc 128 (A + 0)); lia | reflexivity | lia].
  - replace (16 * (cap * 2)) with (32 * cap) by lia.
    pose proof (tk_wz_range (32 * cap)) as W1.
    replace (Bt * (x + 1)) with (0 + Bt * (x + 1)) by lia.
    eapply tk_app; [| apply tk_text; lia | exact B1].
    eapply tk_eq; [apply (tk_rc (16 * cap) (32 * cap) v (A + tk_wz (16 * cap))); lia | reflexivity | lia].
  - rewrite app_nil_l. apply tk_text; lia.
Qed.
Lemma tk_pushes : forall ls n cap j v rs tr cap' ad A, 0 <= A <= 3 ->
  Forall (fun l => Z.of_nat (length l) <= 6000) ls ->
  drain_b_c.pushes_run n cap ls j v rs = (tr, cap', ad) ->
  tk_pc tr (A + tk_wz (16 * cap)) (A + tk_wz (16 * cap')) (Bt * Z.of_nat (length (RelayModel.with_nul ls))).
Proof.
  induction ls as [|l ls IH]; intros n cap j v rs tr cap' ad A HA HF E.
  - cbn [drain_b_c.pushes_run] in E. injection E as <- <- <-.
    rewrite RelayCap.with_nul_nil_len, Z.mul_0_r. pose proof (tk_wz_range (16 * cap)). apply tk_nil. lia.
  - inversion HF as [|? ? Hl HF']; subst.
    cbn [drain_b_c.pushes_run] in E. cbv zeta in E.
    match type of E with context [drain_b_c.pushes_run (n + 1) ?c2 ls ?j2 ?v2 ?r2] =>
      destruct (drain_b_c.pushes_run (n + 1) c2 ls j2 v2 r2) as [[tr2 cap2] ad2] eqn:E2 end.
    cbn [fst snd] in E. injection E as <- <- <-.
    pose proof (IH _ _ _ _ _ _ _ _ A HA HF' E2) as I.
    rewrite RelayCap.with_nul_cons_len.
    assert (B2 : 0 <= Bt * Z.of_nat (length (RelayModel.with_nul ls))) by (apply Z.mul_nonneg_nonneg; lia).
    eapply tk_le.
    { eapply tk_app; [apply (tk_push v n cap (Z.of_nat (length l)) A); lia | exact I | exact B2]. }
    lia.
Qed.

(* ---- the drain buffer's growth *)
Lemma tk_grow_tr : forall cap used j b A, 0 <= A <= 3 ->
  tk_pc (fst (drain_b_c.grow_tr cap used j b)) (A + tk_wz cap)
    (A + tk_wz (fst (snd (drain_b_c.grow_tr cap used j b)))) 0.
Proof.
  intros cap used j b A HA. pose proof (tk_wz_range cap). unfold drain_b_c.grow_tr.
  destruct (cap - used <? 4096); cbv beta iota zeta; cbn [fst snd].
  - eapply tk_eq; [apply (tk_grow cap _ b (A + tk_wz cap)); [destruct (Z.eqb_spec cap 0); cbv beta iota; lia | lia]
                  | reflexivity | lia].
  - apply tk_nil. lia.
Qed.

(* ---- drain's rounds *)
Definition tk_phi (s : drain_b_c.dstate) : Z :=
  tk_wz (drain_b_c.ds_cap s) + tk_wz (16 * drain_b_c.ds_ecap s) + tk_wz (drain_b_c.ds_ocap s) +
  tk_wz (drain_b_c.ds_ka s).
Lemma tk_phi_range : forall s, 0 <= tk_phi s <= 4.
Proof.
  intros s. unfold tk_phi. pose proof (tk_wz_range (drain_b_c.ds_cap s)).
  pose proof (tk_wz_range (16 * drain_b_c.ds_ecap s)). pose proof (tk_wz_range (drain_b_c.ds_ocap s)).
  pose proof (tk_wz_range (drain_b_c.ds_ka s)). lia.
Qed.

Lemma tk_drain_run : forall f live mx s j ad, tc_inv s ->
  tk_pc (fst (drain_b_c.drain_run f live mx s j ad)) (tk_phi s)
    (tk_phi (fst (snd (drain_b_c.drain_run f live mx s j ad))))
    (Bt * (tk_refb s - tk_refb (fst (snd (drain_b_c.drain_run f live mx s j ad)))) +
     Bk * (tk_relb s - tk_relb (fst (snd (drain_b_c.drain_run f live mx s j ad))))) /\
  tk_refb (fst (snd (drain_b_c.drain_run f live mx s j ad))) <= tk_refb s /\
  tk_relb (fst (snd (drain_b_c.drain_run f live mx s j ad))) <= tk_relb s /\
  tc_inv (fst (snd (drain_b_c.drain_run f live mx s j ad))).
Proof.
  intros f live mx. induction f as [|f IH]; intros s j ad HI.
  { cbn [drain_b_c.drain_run fst snd]. rewrite !Z.sub_diag, !Z.mul_0_r, Z.add_0_r. pose proof (tk_phi_range s).
    split; [apply tk_nil; lia | split; [lia | split; [lia | exact HI]]]. }
  pose proof HI as (Io & Iof & Iref).
  pose proof (tk_wz_range (16 * drain_b_c.ds_ecap s)) as We. pose proof (tk_wz_range (drain_b_c.ds_ocap s)) as Wo.
  pose proof (tk_wz_range (drain_b_c.ds_ka s)) as Wk.
  cbn [drain_b_c.drain_run]. cbv zeta.
  pose proof (tk_grow_tr (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf ad)
    (tk_wz (16 * drain_b_c.ds_ecap s) + tk_wz (drain_b_c.ds_ocap s) + tk_wz (drain_b_c.ds_ka s)) ltac:(lia)) as G.
  revert G.
  generalize (drain_b_c.grow_tr (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf ad)).
  intros [tg [cap1 b1]] G. cbn [fst snd] in G |- *.
  pose proof (tk_wz_range cap1) as W1.
  set (s1 := drain_b_c.DS cap1 (drain_b_c.ds_u s) (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s) false
               (drain_b_c.ds_pend s) (drain_b_c.ds_off s) (drain_b_c.ds_ref s) (drain_b_c.ds_en s)
               (drain_b_c.ds_ecap s) (drain_b_c.ds_no s) (drain_b_c.ds_ocap s)).
  assert (P1 : tk_phi s1 = tk_wz cap1 + tk_wz (16 * drain_b_c.ds_ecap s) + tk_wz (drain_b_c.ds_ocap s) +
                           tk_wz (drain_b_c.ds_ka s)) by (unfold s1, tk_phi; tc_projg; reflexivity).
  assert (R1 : tk_refb s1 = tk_refb s) by (unfold s1, tk_refb, tp_R, rm3_dstr; tc_projg; reflexivity).
  assert (U1 : tk_relb s1 = tk_relb s) by (unfold s1, tk_relb, tp_R, tp_U, rm3_dstr; tc_projg; reflexivity).
  assert (J1 : tc_inv s1) by (unfold s1, tc_inv; tc_projg; tauto).
  assert (G1 : tk_pc tg (tk_phi s) (tk_phi s1) 0) by (eapply tk_eq; [exact G | unfold tk_phi; lia | rewrite P1; lia]).
  clearbody s1.
  destruct (drain_b_c.ds_eintr s).
  - (* an EINTR round: the growth only, then the same state *)
    cbn [fst snd].
    match goal with |- context [drain_b_c.drain_run f live mx s1 ?j1 ?a1] =>
      destruct (IH s1 j1 a1 J1) as (I1 & I2 & I3 & I4) end.
    split; [|split; [lia | split; [lia | exact I4]]].
    eapply tk_le; [eapply tk_app; [exact G1 | exact I1 | apply tk_bud_nonneg; lia] | rewrite R1, U1; lia].
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP.
    + cbn [fst snd]. rewrite R1, U1, !Z.sub_diag, !Z.mul_0_r, Z.add_0_r.
      split; [exact G1 | split; [lia | split; [lia | exact J1]]].
    + match goal with |- context [Z.min ?x ?y <=? 0] => set (n := Z.min x y) in * end.
      assert (Hnr : n <= Z.of_nat (length r0) - drain_b_c.ds_off s) by (unfold n; apply Z.le_min_l).
      destruct (Z.leb_spec n 0) as [Hn|Hn].
      * cbn [fst snd]. rewrite R1, U1, !Z.sub_diag, !Z.mul_0_r, Z.add_0_r.
        split; [exact G1 | split; [lia | split; [lia | exact J1]]].
      * (* a data round *)
        set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
        assert (Ld : Z.of_nat (length d) = n) by (unfold d; rewrite length_firstn, length_skipn; lia).
        destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
        pose proof (rm3_chunk_mass _ _ _ _ _ _ EC) as CM.
        destruct (dpre_chunk _ _ _ _ _ _ EC) as (C1 & _ & _).
        pose proof (SlotReads.lines_bytes d (drain_b_c.ds_ref s)) as LB.
        destruct (tc_lines_short d (drain_b_c.ds_ref s) Iref) as [LS1 LS2].
        cbv beta iota.
        match goal with |- context [drain_b_c.pushes_run ?n0 ?c0 ?ls0 ?jj ?vv ?rr] =>
          destruct (drain_b_c.pushes_run n0 c0 ls0 jj vv rr) as [[tpu ecap'] [v' rs']] eqn:EPU end.
        pose proof (tk_pushes _ _ _ _ _ _ _ _ _
          (tk_wz cap1 + tk_wz (drain_b_c.ds_ocap s) + tk_wz (drain_b_c.ds_ka s)) ltac:(lia) LS1 EPU) as PU.
        pose proof (tk_wz_range (16 * ecap')) as We'.
        match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 ?a3 ?a4 rl ?a5 ?a6 ?a7 ?a8] =>
          destruct (drain_b_c.lines_run live mx a1 a2 a3 a4 rl a5 a6 a7 a8)
            as [[tl [[oc' H'] ka']] [[o' ha'] ks']] eqn:EL end.
        destruct (tk_lines _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tk_wz cap1 + tk_wz (16 * ecap')) Io ltac:(lia) C1 EL)
          as [PL1 PL2].
        pose proof (tk_wz_range oc') as Wo'. pose proof (tk_wz_range ka') as Wk'.
        cbn [fst snd].
        assert (R0 : tp_R s = Z.of_nat (length r0) - drain_b_c.ds_off s + Z.of_nat (length (concat rs))).
        { unfold tp_R, rm3_dstr. rewrite EP, length_app, length_skipn. lia. }
        assert (Hrf : tk_refb s = tp_R s + SlotReads.wcost (drain_b_c.ds_ref s)) by reflexivity.
        assert (Hrl : tk_relb s = tp_R s +
                 (if drain_b_c.ds_skip s then 0 else Z.of_nat (length (drain_b_c.ds_u s)))) by reflexivity.
        assert (BL : 0 <= Bt * Z.of_nat (length (RelayModel.with_nul (RelayModel.lines (drain_b_c.ds_ref s) d))))
          by (apply Z.mul_nonneg_nonneg; lia).
        assert (BR : 0 <= Bk * Z.of_nat (length (RelayModel.with_nul rl))) by (apply Z.mul_nonneg_nonneg; lia).
        destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [W|W].
        -- (* the head text is read to its end: list_drop frees it *)
           match goal with |- context [drain_b_c.drain_run f live mx ?s2 ?j4 ?a2] =>
             set (S2 := s2); set (J4 := j4); set (A2 := a2) end.
           assert (R2 : tp_R S2 = Z.of_nat (length (concat rs))).
           { unfold S2, tp_R, rm3_dstr. tc_projg. rewrite rm3_dstr0. reflexivity. }
           assert (D2 : tk_refb S2 = Z.of_nat (length (concat rs)) +
                          SlotReads.wcost (RelayModel.feed (drain_b_c.ds_ref s) d)).
           { unfold tk_refb. rewrite R2. unfold S2. tc_projg. reflexivity. }
           assert (E2 : tk_relb S2 = Z.of_nat (length (concat rs)) + (if sk' then 0 else Z.of_nat (length u'))).
           { unfold tk_relb. rewrite R2. unfold tp_U, S2. tc_projg. reflexivity. }
           assert (F2 : tk_phi S2 = tk_wz cap1 + tk_wz (16 * ecap') + tk_wz oc' + tk_wz ka')
             by (unfold S2, tk_phi; tc_projg; reflexivity).
           assert (J2 : tc_inv S2) by (unfold S2, tc_inv; tc_projg; split; [exact PL2 | split; [lia | exact LS2]]).
           destruct (IH S2 J4 A2 J2) as (I1 & I2 & I3 & I4).
           assert (BBt : Bt * Z.of_nat (length (RelayModel.with_nul (RelayModel.lines (drain_b_c.ds_ref s) d))) <=
                         Bt * (tk_refb s - tk_refb S2)) by (apply Z.mul_le_mono_nonneg_l; lia).
           assert (BBk : Bk * Z.of_nat (length (RelayModel.with_nul rl)) <= Bk * (tk_relb s - tk_relb S2))
             by (apply Z.mul_le_mono_nonneg_l; lia).
           assert (BP : 0 <= Bt * (tk_refb S2 - tk_refb (fst (snd (drain_b_c.drain_run f live mx S2 J4 A2)))) +
                             Bk * (tk_relb S2 - tk_relb (fst (snd (drain_b_c.drain_run f live mx S2 J4 A2)))))
             by (apply tk_bud_nonneg; lia).
           cbv beta iota. unfold ListTr.list_drop_tra. cbn [app].
           split; [|split; [lia | split; [lia | exact I4]]].
           eapply tk_le.
           { eapply tk_app; [exact G1 | | ].
             - eapply tk_app; [eapply tk_eq; [exact PU | rewrite P1; lia | reflexivity] | | ].
               + apply tk_cons_free; [lia | | ].
                 * eapply (tk_app _ _ _ (tk_phi S2)); [eapply tk_eq; [exact PL1 | lia | rewrite F2; lia] | exact I1 |].
                   exact BP.
                 * lia.
               + lia.
             - lia. }
           lia.
        -- (* part of the head text read *)
           match goal with |- context [drain_b_c.drain_run f live mx ?s2 ?j4 ?a2] =>
             set (S2 := s2); set (J4 := j4); set (A2 := a2) end.
           assert (R2 : tp_R S2 = Z.of_nat (length r0) - (drain_b_c.ds_off s + n) + Z.of_nat (length (concat rs))).
           { unfold S2, tp_R, rm3_dstr. tc_projg. rewrite length_app, length_skipn. lia. }
           assert (D2 : tk_refb S2 = Z.of_nat (length r0) - (drain_b_c.ds_off s + n) +
                                     Z.of_nat (length (concat rs)) +
                          SlotReads.wcost (RelayModel.feed (drain_b_c.ds_ref s) d)).
           { unfold tk_refb. rewrite R2. unfold S2. tc_projg. reflexivity. }
           assert (E2 : tk_relb S2 = Z.of_nat (length r0) - (drain_b_c.ds_off s + n) +
                                     Z.of_nat (length (concat rs)) + (if sk' then 0 else Z.of_nat (length u'))).
           { unfold tk_relb. rewrite R2. unfold tp_U, S2. tc_projg. reflexivity. }
           assert (F2 : tk_phi S2 = tk_wz cap1 + tk_wz (16 * ecap') + tk_wz oc' + tk_wz ka')
             by (unfold S2, tk_phi; tc_projg; reflexivity).
           assert (J2 : tc_inv S2) by (unfold S2, tc_inv; tc_projg; split; [exact PL2 | split; [lia | exact LS2]]).
           destruct (IH S2 J4 A2 J2) as (I1 & I2 & I3 & I4).
           assert (BBt : Bt * Z.of_nat (length (RelayModel.with_nul (RelayModel.lines (drain_b_c.ds_ref s) d))) <=
                         Bt * (tk_refb s - tk_refb S2)) by (apply Z.mul_le_mono_nonneg_l; lia).
           assert (BBk : Bk * Z.of_nat (length (RelayModel.with_nul rl)) <= Bk * (tk_relb s - tk_relb S2))
             by (apply Z.mul_le_mono_nonneg_l; lia).
           assert (BP : 0 <= Bt * (tk_refb S2 - tk_refb (fst (snd (drain_b_c.drain_run f live mx S2 J4 A2)))) +
                             Bk * (tk_relb S2 - tk_relb (fst (snd (drain_b_c.drain_run f live mx S2 J4 A2)))))
             by (apply tk_bud_nonneg; lia).
           cbv beta iota. cbn [app].
           split; [|split; [lia | split; [lia | exact I4]]].
           eapply tk_le.
           { eapply tk_app; [exact G1 | | ].
             - eapply tk_app; [eapply tk_eq; [exact PU | rewrite P1; lia | reflexivity] | | ].
               + eapply (tk_app _ _ _ (tk_phi S2)); [eapply tk_eq; [exact PL1 | lia | rewrite F2; lia] | exact I1 |].
                 exact BP.
               + lia.
             - lia. }
           lia.
Qed.

(* one drain: Lw * peak <= 5 Lw + Bt * (the reference splitter's budget) + Bk * (the relay's budget) *)
Lemma tk_dr : forall c mx no cap e h, 0 <= cap -> 0 <= hs_off h -> tc_ref (hs_state h) ->
  Lw * ReplyTrPeakW.tr_peak_w w (dr_tr c mx no cap e h) <=
    5 * Lw + Bt * tk_refb (drain_b_c.drain_init no cap e h) + Bk * tk_relb (drain_b_c.drain_init no cap e h).
Proof using Hw HL Ht Hk Hst Hsk.
  intros c mx no cap e h Hcap Hoff Href.
  assert (HI : tc_inv (drain_b_c.drain_init no cap e h)) by (unfold tc_inv, drain_b_c.drain_init; tc_projg; tauto).
  destruct (tk_drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx _ 0%nat drain_b_c.dadr0 HI)
    as ((P1 & _) & D2 & D3 & _).
  unfold dr_tr, drain_b_c.drain_tr, drain_b_c.drain_go.
  pose proof (tk_phi_range (drain_b_c.drain_init no cap e h)) as F.
  assert (M1 : 0 <= Lw * tk_phi (drain_b_c.drain_init no cap e h)) by (apply Z.mul_nonneg_nonneg; lia).
  match type of D2 with tk_refb ?sf <= _ =>
    assert (M2 : 0 <= Bt * tk_refb sf) by (apply Z.mul_nonneg_nonneg; [lia | apply tk_refb_nonneg]);
    assert (M3 : 0 <= Bk * tk_relb sf) by (apply Z.mul_nonneg_nonneg; [lia | apply tk_relb_nonneg]) end.
  lia.
Qed.

(* ---- gestures_end's key run: each key's two sends (g_out's regrowths), then the key's free *)
Lemma tk_keys_end_run : forall xks live mx no cap j o A, 0 <= cap -> 0 <= A <= 3 ->
  tk_pc (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o)) (A + tk_wz cap)
     (A + tk_wz (fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o)))) 0 /\
  0 <= fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o)).
Proof.
  induction xks as [|[xl ka] r IH]; intros live mx no cap j o A Hc HA.
  - cbn [gestures_end_b_c.keys_end_run fst snd]. split; [apply tk_nil; pose proof (tk_wz_range cap); lia | exact Hc].
  - cbn [gestures_end_b_c.keys_end_run]. unfold gesture_end_b_c.gesture_end_tr, gesture_end_b_c.gesture_end_cap.
    cbv zeta. cbn [fst snd].
    destruct (tk_send_line live mx no cap xl j o A Hc HA) as [S1 S2].
    match goal with |- context [send_line_b_c.send_line_tr live mx (no + xl) ?c1 5 ?j1 ?o1] =>
      destruct (tk_send_line live mx (no + xl) c1 5 j1 o1 A S2 HA) as [S3 S4] end.
    match goal with |- context [gestures_end_b_c.keys_end_run live mx (no + xl + 5) ?c2 r ?j2 ?o2] =>
      destruct (IH live mx (no + xl + 5) c2 j2 o2 A S4 HA) as [I1 I2];
      pose proof (tk_wz_range c2) as W2 end.
    split; [|exact I2].
    rewrite <- app_assoc.
    eapply tk_le.
    { eapply tk_app; [exact S1 | | ].
      - eapply tk_app; [exact S3 | apply tk_cons_free; [lia | exact I1 | lia] | lia].
      - lia. }
    lia.
Qed.

(* a whole trace's piece gives the callee's peak bound *)
Lemma tk_peak_of : forall tr f0 f1 b B', tk_pc tr f0 f1 b -> 0 <= f0 -> b <= B' -> Lw * tr_peak_w w tr <= 5 * Lw + B'.
Proof. intros tr f0 f1 b B' (P & _) H0 Hb. nia. Qed.

(* relay_remove's requests: drain's when the entry is open, the key run, two frees *)
Lemma tk_rr : forall c mx no cap FD es h e,
  find (fun e => re_fd e =? FD) es = Some e -> 0 <= cap ->
  (re_eof e = 0 -> 0 <= hs_off h /\ tc_ref (hs_state h)) ->
  Lw * ReplyTrPeakW.tr_peak_w w (rr_tr c mx no cap FD es h) <=
    5 * Lw + (if re_eof e =? 0 then Bt * tk_refb (drain_b_c.drain_init no cap e h) +
                                    Bk * tk_relb (drain_b_c.drain_init no cap e h) else 0).
Proof using Hw HL Ht Hk Hst Hsk.
  intros c mx no cap FD es h e Hf Hcap HJ.
  assert (M0 : 0 <= Bt * tk_refb (drain_b_c.drain_init no cap e h) + Bk * tk_relb (drain_b_c.drain_init no cap e h)).
  { pose proof (Z.mul_nonneg_nonneg _ _ Ht (tk_refb_nonneg (drain_b_c.drain_init no cap e h))).
    pose proof (Z.mul_nonneg_nonneg _ _ Hk (tk_relb_nonneg (drain_b_c.drain_init no cap e h))). lia. }
  unfold rr_tr. cbv zeta.
  destruct (FD <? 0).
  { change (tr_peak_w w (@nil (RelayRunT.rev YO0i.sptr))) with 0. destruct (re_eof e =? 0); lia. }
  rewrite Hf. cbv beta iota zeta.
  destruct (re_eof e =? 0) eqn:Eo; cbv beta iota.
  - apply Z.eqb_eq in Eo. destruct (HJ Eo) as [Hoff Href].
    assert (HI : tc_inv (drain_b_c.drain_init no cap e h)) by (unfold tc_inv, drain_b_c.drain_init; tc_projg; tauto).
    pose proof (tk_drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx _ 0%nat drain_b_c.dadr0 HI) as D.
    pose proof (tk_phi_range (drain_b_c.drain_init no cap e h)) as F.
    unfold dr_tr, dr_fin, drain_b_c.drain_tr, drain_b_c.drain_fin, drain_b_c.drain_go.
    revert D.
    generalize (drain_b_c.drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx
                  (drain_b_c.drain_init no cap e h) 0%nat drain_b_c.dadr0).
    intros [tr [fin adf]] (D1 & D2 & D3 & D4). cbn [fst snd] in D1, D2, D3, D4 |- *.
    destruct D4 as (Do & _ & _).
    pose proof (tk_wz_range (drain_b_c.ds_cap fin)). pose proof (tk_wz_range (16 * drain_b_c.ds_ecap fin)).
    pose proof (tk_wz_range (drain_b_c.ds_ka fin)).
    match goal with |- context [gestures_end_b_c.keys_end_run ?lv ?mm ?nn (drain_b_c.ds_ocap fin) ?xks ?jj ?oo] =>
      destruct (tk_keys_end_run xks lv mm nn (drain_b_c.ds_ocap fin) jj oo
        (tk_wz (drain_b_c.ds_cap fin) + tk_wz (16 * drain_b_c.ds_ecap fin) + tk_wz (drain_b_c.ds_ka fin)) Do
        ltac:(lia)) as [K1 _];
      pose proof (tk_wz_range (fst (snd (gestures_end_b_c.keys_end_run lv mm nn (drain_b_c.ds_ocap fin) xks jj oo))))
    end.
    assert (M3 : 0 <= Bt * tk_refb fin) by (apply Z.mul_nonneg_nonneg; [lia | apply tk_refb_nonneg]).
    assert (M4 : 0 <= Bk * tk_relb fin) by (apply Z.mul_nonneg_nonneg; [lia | apply tk_relb_nonneg]).
    eapply tk_peak_of.
    + eapply (tk_app _ _ _ (tk_phi fin)); [exact D1 | | ].
      * eapply tk_app; [eapply tk_eq; [exact K1 | unfold tk_phi; lia | reflexivity] | | ].
        -- apply tk_cons_free; [lia | apply tk_cons_free; [lia | apply tk_nil; lia | lia] | lia].
        -- lia.
      * lia.
    + exact (proj1 F).
    + lia.
  - rewrite app_nil_l.
    match goal with |- context [gestures_end_b_c.keys_end_run ?lv ?mm ?nn ?cc ?xks ?jj ?oo] =>
      assert (Hc0 : 0 <= cc) by (unfold drain_b_c.drain_init; tc_projg; exact Hcap);
      destruct (tk_keys_end_run xks lv mm nn cc jj oo 0 Hc0 ltac:(lia)) as [K1 _];
      pose proof (tk_wz_range cc);
      pose proof (tk_wz_range (fst (snd (gestures_end_b_c.keys_end_run lv mm nn cc xks jj oo))))
    end.
    eapply tk_peak_of.
    + eapply tk_app; [exact K1 | | ].
      * apply tk_cons_free; [lia | apply tk_cons_free; [lia | apply tk_nil; lia | lia] | lia].
      * lia.
    + lia.
    + lia.
Qed.

(* ---- relay_instance_gone: per table entry a piece of transient <= 5 and net <= 4 (plus its budget) *)
(* an entry's budget: its drain's two budgets when it is open (they do not depend on g_nout / g_capout) *)
Definition tk_eb (e : rentry) (h : hsrc) : Z :=
  if re_eof e =? 0 then Bt * tk_refb (drain_b_c.drain_init 0 0 e h) + Bk * tk_relb (drain_b_c.drain_init 0 0 e h)
  else 0.
(* a piece whose transient is within 5 and whose net is within 4 (scaled by Lw, plus b) *)
Definition tk_box (tr : list (RelayRunT.rev YO0i.sptr)) (b : Z) : Prop :=
  Lw * tr_peak_w w tr <= 5 * Lw + b /\ Lw * tr_net_w w tr <= 4 * Lw + b.

Lemma tk_eb_nonneg : forall e h, 0 <= tk_eb e h.
Proof.
  intros e h. unfold tk_eb. destruct (re_eof e =? 0); [|lia].
  pose proof (Z.mul_nonneg_nonneg _ _ Ht (tk_refb_nonneg (drain_b_c.drain_init 0 0 e h))).
  pose proof (Z.mul_nonneg_nonneg _ _ Hk (tk_relb_nonneg (drain_b_c.drain_init 0 0 e h))). lia.
Qed.
Lemma tk_sum_nonneg : forall ps : list (rentry * (hsrc * nat)),
  0 <= fold_right Z.add 0 (map (fun p => tk_eb (fst p) (fst (snd p))) ps).
Proof.
  induction ps as [|p ps IH]; cbn [map fold_right]; [lia|]. pose proof (tk_eb_nonneg (fst p) (fst (snd p))). lia.
Qed.
Lemma tk_pc_box : forall tr f0 f1 b B', tk_pc tr f0 f1 b -> 0 <= f0 -> f1 <= 4 -> b <= B' -> tk_box tr B'.
Proof.
  intros tr f0 f1 b B' (P & N) H0 H1 Hb. unfold tk_box.
  pose proof (Z.mul_nonneg_nonneg Lw f0 HL H0). pose proof (Z.mul_nonneg_nonneg Lw (4 - f1) HL ltac:(lia)).
  split; nia.
Qed.
Lemma tk_box_app : forall t1 t2 (n : nat) b1 B2, tk_box t1 b1 -> 0 <= b1 ->
  Lw * tr_peak_w w t2 <= (4 * Z.of_nat n + 1) * Lw + B2 -> 0 <= B2 ->
  Lw * tr_peak_w w (t1 ++ t2) <= (4 * Z.of_nat (S n) + 1) * Lw + (b1 + B2).
Proof.
  intros t1 t2 n b1 B2 (P1 & N1) Hb1 P2 HB2. rewrite tr_peak_w_app, Nat2Z.inj_succ.
  assert (M : 0 <= Z.of_nat n * Lw) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (Z.max_spec (tr_peak_w w t1) (tr_net_w w t1 + tr_peak_w w t2)) as [[_ E]|[_ E]]; rewrite E; nia.
Qed.

(* one entry: drain when open (its state does not depend on the addresses, RelayCap.rc_drain_state), then the key
   run of gestures_end_instance from the g_capout drain leaves *)
Lemma tk_gone_piece : forall lv mx no cap e h j a0 xks jj oo, 0 <= cap ->
  (re_eof e = 0 -> 0 <= hs_off h /\ tc_ref (hs_state h)) ->
  tk_box ((if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e h j a0 else []) ++
     fst (gestures_end_b_c.keys_end_run lv mx (drain_b_c.ds_no (relay_remove_b_c.after_drain lv mx no cap e h))
            (drain_b_c.ds_ocap (relay_remove_b_c.after_drain lv mx no cap e h)) xks jj oo)) (tk_eb e h) /\
  0 <= fst (snd (gestures_end_b_c.keys_end_run lv mx (drain_b_c.ds_no (relay_remove_b_c.after_drain lv mx no cap e h))
            (drain_b_c.ds_ocap (relay_remove_b_c.after_drain lv mx no cap e h)) xks jj oo)).
Proof.
  intros lv mx no cap e h j a0 xks jj oo Hcap HJ. unfold tk_eb.
  destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo].
  - destruct (HJ Eo) as [Hoff Href].
    rewrite (RelayCap.after_drain_fin lv mx no cap e h Eo).
    unfold drain_b_c.drain_fin, drain_b_c.drain_tr, drain_b_c.drain_go.
    rewrite (RelayCap.rc_drain_state _ _ _ _ 0%nat drain_b_c.dadr0 j a0).
    assert (HI : tc_inv (drain_b_c.drain_init no cap e h)) by (unfold tc_inv, drain_b_c.drain_init; tc_projg; tauto).
    pose proof (tk_drain_run (S (S (length (pending_stream h)))) lv mx _ j a0 HI) as D.
    pose proof (tk_phi_range (drain_b_c.drain_init no cap e h)) as F.
    change (tk_refb (drain_b_c.drain_init 0 0 e h)) with (tk_refb (drain_b_c.drain_init no cap e h)).
    change (tk_relb (drain_b_c.drain_init 0 0 e h)) with (tk_relb (drain_b_c.drain_init no cap e h)).
    revert D.
    generalize (drain_b_c.drain_run (S (S (length (pending_stream h)))) lv mx (drain_b_c.drain_init no cap e h) j a0).
    intros [tr [fin adf]] (D1 & D2 & D3 & D4). cbn [fst snd] in D1, D2, D3, D4 |- *.
    destruct D4 as (Do & _ & _).
    pose proof (tk_wz_range (drain_b_c.ds_cap fin)). pose proof (tk_wz_range (16 * drain_b_c.ds_ecap fin)).
    pose proof (tk_wz_range (drain_b_c.ds_ka fin)).
    destruct (tk_keys_end_run xks lv mx (drain_b_c.ds_no fin) (drain_b_c.ds_ocap fin) jj oo
        (tk_wz (drain_b_c.ds_cap fin) + tk_wz (16 * drain_b_c.ds_ecap fin) + tk_wz (drain_b_c.ds_ka fin)) Do
        ltac:(lia)) as [K1 K2].
    pose proof (tk_wz_range
      (fst (snd (gestures_end_b_c.keys_end_run lv mx (drain_b_c.ds_no fin) (drain_b_c.ds_ocap fin) xks jj oo)))).
    split; [|exact K2].
    assert (M3 : 0 <= Bt * tk_refb fin) by (apply Z.mul_nonneg_nonneg; [lia | apply tk_refb_nonneg]).
    assert (M4 : 0 <= Bk * tk_relb fin) by (apply Z.mul_nonneg_nonneg; [lia | apply tk_relb_nonneg]).
    eapply tk_pc_box.
    + eapply (tk_app _ _ _ (tk_phi fin));
        [exact D1 | eapply tk_eq; [exact K1 | unfold tk_phi; lia | reflexivity] | lia].
    + exact (proj1 F).
    + lia.
    + lia.
  - rewrite (RelayCap.after_drain_init lv mx no cap e h Eo).
    rewrite app_nil_l.
    assert (Hc0 : 0 <= drain_b_c.ds_ocap (drain_b_c.drain_init no cap e h))
      by (unfold drain_b_c.drain_init; tc_projg; exact Hcap).
    destruct (tk_keys_end_run xks lv mx (drain_b_c.ds_no (drain_b_c.drain_init no cap e h))
        (drain_b_c.ds_ocap (drain_b_c.drain_init no cap e h)) jj oo 0 Hc0 ltac:(lia)) as [K1 K2].
    pose proof (tk_wz_range (drain_b_c.ds_ocap (drain_b_c.drain_init no cap e h))).
    pose proof (tk_wz_range (fst (snd (gestures_end_b_c.keys_end_run lv mx
      (drain_b_c.ds_no (drain_b_c.drain_init no cap e h)) (drain_b_c.ds_ocap (drain_b_c.drain_init no cap e h))
      xks jj oo)))).
    split; [|exact K2].
    eapply tk_pc_box; [exact K1 | lia | lia | lia].
Qed.

Lemma tk_gone_run : forall ps lv mx no cap pre nm j o, 0 <= cap ->
  Forall (fun p => re_eof (fst p) = 0 -> 0 <= hs_off (fst (snd p)) /\ tc_ref (hs_state (fst (snd p)))) ps ->
  Lw * tr_peak_w w (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) <=
    (4 * Z.of_nat (length ps) + 1) * Lw + fold_right Z.add 0 (map (fun p => tk_eb (fst p) (fst (snd p))) ps).
Proof.
  induction ps as [|[e hj] r IH]; intros lv mx no cap pre nm j o Hcap HF.
  - cbn [relay_instance_gone_b_c.gone_run fst map fold_right length].
    change (tr_peak_w w (@nil (RelayRunT.rev YO0i.sptr))) with 0. lia.
  - inversion HF as [|? ? He HF']; subst. cbn [fst snd] in He.
    cbn [relay_instance_gone_b_c.gone_run].
    match goal with |- context [gestures_end_b_c.keys_end_run lv mx _ _ ?xks ?jj ?oo] =>
      destruct (tk_gone_piece lv mx no cap e (fst hj) j (drain_b_c.drain_start nm o e (fst hj)) xks jj oo Hcap He)
        as [PK Hc2] end.
    match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?n2 ?c2 pre r nm ?j2 ?o2] =>
      pose proof (IH lv mx n2 c2 pre nm j2 o2 Hc2 HF') as I; revert I;
      destruct (relay_instance_gone_b_c.gone_run lv mx n2 c2 pre r nm j2 o2) as [[[t c0] ss] [o' das]]; intros I
    end.
    cbn [fst snd map fold_right length] in I |- *.
    rewrite app_assoc. apply tk_box_app; [exact PK | apply tk_eb_nonneg | exact I | apply tk_sum_nonneg].
Qed.

(* relay_instance_gone: (4 |es| + 1) Lw plus each open entry's two budgets *)
Lemma tk_rig : forall c mx no cap ID es hs, 0 <= cap ->
  Forall (fun p => re_eof (fst p) = 0 -> 0 <= hs_off (fst (snd p)) /\ tc_ref (hs_state (fst (snd p)))) (combine es hs) ->
  Lw * ReplyTrPeakW.tr_peak_w w (rig_tr c mx no cap ID es hs) <=
    (4 * Z.of_nat (length es) + 1) * Lw +
    fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then
        Bt * tk_refb (drain_b_c.drain_init 0 0 (fst p) (fst (snd p))) +
        Bk * tk_relb (drain_b_c.drain_init 0 0 (fst p) (fst (snd p))) else 0) (combine es hs)).
Proof using Hw HL Ht Hk Hst Hsk.
  intros c mx no cap ID es hs Hcap HF. unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr. cbv zeta.
  pose proof (tk_gone_run (combine es hs) (sl_live c 1) mx no cap (relay_instance_gone_b_c.instance_prefix ID)
    (fun _ => drain_b_c.da_out drain_b_c.dadr0) 0%nat (drain_b_c.da_out drain_b_c.dadr0) Hcap HF) as H.
  assert (L : (length (combine es hs) <= length es)%nat) by (rewrite length_combine; lia).
  assert (M : Lw * Z.of_nat (length (combine es hs)) <= Lw * Z.of_nat (length es))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold tk_eb in H. lia.
Qed.
End tk.

(* ================================================================== at the instance *)
Section tk_inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* fr_pair_ok's relay / splitter clause (re_eof = 0): the splitter's partial line is the relay's, so both budgets
   are pair_bytes *)
Lemma tk_init : forall NO CAP e h, (re_skip e = 0 \/ re_skip e = 1) -> re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  tk_refb (drain_b_c.drain_init NO CAP e h) = pair_bytes e h /\ tk_relb (drain_b_c.drain_init NO CAP e h) = pair_bytes e h.
Proof.
  intros NO CAP e h Hsk Ho Hu. unfold tk_refb, tk_relb, tp_R, tp_U, pair_bytes.
  rewrite rm3_dstr_init, RelayCap.rc_length_bzs.
  unfold drain_b_c.drain_init. tc_projg. unfold SlotReads.wcost, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
  rewrite <- Ho. destruct Hsk as [E|E].
  - pose proof (Hu E) as Eu. rewrite E. cbn [Z.eqb]. rewrite <- Eu, RelayCap.rc_length_bzs. split; lia.
  - rewrite E. cbn [Z.eqb Pos.eqb]. split; lia.
Qed.

(* the three weights' kept-malloc hypotheses *)
Lemma tk_c1_st : forall x, 1 <= x <= 6001 -> 21 * w_cls 1 x <= 21 * x.
Proof. intros x Hx. pose proof (w_cls_range 1 x). lia. Qed.
(* a class-1 key counts at most 1, and its begin line is at least 20 bytes *)
Lemma tk_c1_sk : forall l x, RelayModel.gesture l = Some (RelayModel.GBegin, x) -> Z.of_nat (length l) <= 6000 ->
  21 * w_cls 1 (Z.of_nat (length x) + 1) <= 1 * (Z.of_nat (length l) + 1).
Proof.
  intros l x G Hl. pose proof (SlotReads.gesture_begin_len l x G) as L.
  pose proof (w_cls_range 1 (Z.of_nat (length x) + 1)). lia.
Qed.
(* a key is no longer than its line: primary, and of class k at least lo k bytes *)
Lemma tk_sec_sk : forall l x, RelayModel.gesture l = Some (RelayModel.GBegin, x) -> Z.of_nat (length l) <= 6000 ->
  1 * w_sec (Z.of_nat (length x) + 1) <= 0 * (Z.of_nat (length l) + 1).
Proof.
  intros l x G Hl. pose proof (dpre_gesture_len l RelayModel.GBegin x G) as L.
  pose proof (w_sec_small (Z.of_nat (length x) + 1) ltac:(lia)). lia.
Qed.
Lemma tk_cls_sk : forall k l x, RelayModel.gesture l = Some (RelayModel.GBegin, x) -> Z.of_nat (length l) <= 6000 ->
  PresetRoom.lo k * w_cls k (Z.of_nat (length x) + 1) <= 1 * (Z.of_nat (length l) + 1).
Proof.
  intros k l x G Hl. pose proof (dpre_gesture_len l RelayModel.GBegin x G) as L.
  pose proof (w_cls_small k (Z.of_nat (length x) + 1) ltac:(lia)). lia.
Qed.

(* the facts of the drained pair the walk needs, from fr_RINV and the pick (fr_pair_ok, ReplyRINV.v:106-125) *)
Lemma tk_dr_facts : forall cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  0 <= hs_off h /\ tc_ref (hs_state h) /\
  (forall NO CAP, tk_refb (drain_b_c.drain_init NO CAP (nth j (lm_es m) dr_e0) h) =
                    pair_bytes (nth j (lm_es m) dr_e0) h /\
                  tk_relb (drain_b_c.drain_init NO CAP (nth j (lm_es m) dr_e0) h) =
                    pair_bytes (nth j (lm_es m) dr_e0) h).
Proof.
  intros cx t m si h j HRI Hpick Hj Hfdj Heof HU.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & Hent & _).
  destruct Hp as (_ & _ & _ & Hre & _ & _ & _ & _ & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct Hent as (_ & _ & _ & _ & Hsk).
  destruct (Hre Heof) as (S1 & W1).
  split; [exact Hoff|]. split; [exact (tc_ref_state _ h Hsk S1 W1 HU)|].
  intros NO CAP. exact (tk_init NO CAP _ h Hsk S1 W1).
Qed.

Lemma fr_LS_drain_c1_peak : forall cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  21 * ReplyTrPeakW.tr_peak_w (w_cls 1)
    (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) <=
    105 + 22 * pair_bytes (nth j (lm_es m) dr_e0) h.
Proof.
  intros cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP.
  destruct (tk_dr_facts cx t m si h j HRI Hpick Hj Hfdj Heof HU) as (Hoff & Href & Hdb).
  assert (Hcap : 0 <= lm_cap m).
  { apply tc_out_pos. intros b Hb. apply Z.lt_le_incl, HXP, in_or_app. right. apply in_or_app. right. exact Hb. }
  pose proof (tk_dr (w_cls 1) 21 21 1 (w_cls_range 1) ltac:(lia) ltac:(lia) ltac:(lia) tk_c1_st tk_c1_sk (lm_c m)
                (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h Hcap Hoff Href) as H.
  destruct (Hdb (Z.of_nat (length (lm_O m))) (lm_cap m)) as [E1 E2]. rewrite E1, E2 in H. lia.
Qed.

Lemma tk_rm_facts : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0) /\ 0 <= hs_off h /\
  (re_eof (rm_ent m j0) = 0 -> tc_ref (hs_state h) /\
     forall NO CAP, tk_refb (drain_b_c.drain_init NO CAP (rm_ent m j0) h) = pair_bytes (rm_ent m j0) h /\
                    tk_relb (drain_b_c.drain_init NO CAP (rm_ent m j0) h) = pair_bytes (rm_ent m j0) h).
Proof.
  intros cx t m si h j0 HRI Hat HU.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & _ & _).
  pose proof Hat as (_ & _ & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & _ & _ & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct HE as (_ & _ & _ & _ & Hsk).
  split; [unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]|].
  split; [exact Hoff|].
  intros Eo. destruct (Hre Eo) as (S1 & W1).
  split; [exact (tc_ref_state _ h Hsk S1 W1 HU)|].
  intros NO CAP. exact (tk_init NO CAP _ h Hsk S1 W1).
Qed.

Lemma fr_LS_rm_c1_peak : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  21 * ReplyTrPeakW.tr_peak_w (w_cls 1) (rm_rr_tr m h) <= 105 + 22 * pair_bytes (rm_ent m j0) h.
Proof.
  intros cx t m si h j0 HRI Hat HU Hpos.
  destruct (tk_rm_facts cx t m si h j0 HRI Hat HU) as (Hf & Hoff & HJ).
  pose proof (pair_bytes_nonneg (rm_ent m j0) h) as Hpb0.
  pose proof (tk_rr (w_cls 1) 21 21 1 (w_cls_range 1) ltac:(lia) ltac:(lia) ltac:(lia) tk_c1_st tk_c1_sk (lm_c m)
                (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (hs_fd h) (lm_es m) h (rm_ent m j0) Hf
                (tc_rm_cap m Hpos) (fun Eo => conj Hoff (proj1 (HJ Eo)))) as H.
  unfold rm_rr_tr. revert H. destruct (re_eof (rm_ent m j0) =? 0) eqn:Eo; intros H.
  - apply Z.eqb_eq in Eo. destruct (proj2 (HJ Eo) (Z.of_nat (length (lm_O m))) (lm_cap m)) as [E1 E2].
    rewrite E1, E2 in H. lia.
  - lia.
Qed.

(* ---- relay_instance_gone *)
Definition rig_ok (es : list rentry) (hs : list (hsrc * nat)) : Prop :=
  Forall (fun p => re_eof (fst p) = 0 ->
    (re_skip (fst p) = 0 \/ re_skip (fst p) = 1) /\ re_skip (fst p) = hs_overlong (fst (snd p)) /\
    (re_skip (fst p) = 0 -> bzs (re_U (fst p)) = bzs (hs_W (fst (snd p)))) /\
    Z.of_nat (length (re_U (fst p))) <= APARTIAL /\ 0 <= hs_off (fst (snd p))) (combine es hs).
Definition rig_pb (es : list rentry) (hs : list (hsrc * nat)) : Z :=
  fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then pair_bytes (fst p) (fst (snd p)) else 0) (combine es hs)).

Lemma tk_rig_fact : forall es hs, rig_ok es hs ->
  Forall (fun p => re_eof (fst p) = 0 -> 0 <= hs_off (fst (snd p)) /\ tc_ref (hs_state (fst (snd p)))) (combine es hs).
Proof.
  intros es hs H. unfold rig_ok in H. eapply Forall_impl; [|exact H].
  intros p Hp Eo. destruct (Hp Eo) as (Hsk & Ho & Hu & HU & Hoff).
  split; [exact Hoff | exact (tc_ref_state _ _ Hsk Ho Hu HU)].
Qed.
(* at the model's entries both budgets are pair_bytes *)
Lemma tk_rig_sum : forall Bt Bk es hs, rig_ok es hs ->
  fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then
      Bt * tk_refb (drain_b_c.drain_init 0 0 (fst p) (fst (snd p))) +
      Bk * tk_relb (drain_b_c.drain_init 0 0 (fst p) (fst (snd p))) else 0) (combine es hs)) =
  (Bt + Bk) * rig_pb es hs.
Proof.
  intros Bt Bk es hs H. unfold rig_ok in H. unfold rig_pb. revert H. generalize (combine es hs) as ps.
  intros ps H. induction H as [|p ps Hp HF IH]; cbn [map fold_right]; [ring|].
  rewrite IH. destruct (re_eof (fst p) =? 0) eqn:Eo.
  - apply Z.eqb_eq in Eo. destruct (Hp Eo) as (Hsk & Ho & Hu & _ & _).
    destruct (tk_init 0 0 (fst p) (fst (snd p)) Hsk Ho Hu) as [E1 E2]. rewrite E1, E2. ring.
  - ring.
Qed.

Lemma rig_sec_peak : forall c mx no cap ID es hs, 0 <= cap -> rig_ok es hs ->
  ReplyTrPeakW.tr_peak_w w_sec (rig_tr c mx no cap ID es hs) <= 4 * Z.of_nat (length es) + 1.
Proof.
  intros c mx no cap ID es hs Hcap Hok.
  pose proof (tk_rig w_sec 1 0 0 w_sec_range ltac:(lia) ltac:(lia) ltac:(lia) w_sec_small tk_sec_sk
                c mx no cap ID es hs Hcap (tk_rig_fact es hs Hok)) as H.
  rewrite (tk_rig_sum 0 0 es hs Hok) in H. lia.
Qed.
Lemma rig_cls_peak : forall k c mx no cap ID es hs, 0 <= cap -> rig_ok es hs ->
  PresetRoom.lo k * ReplyTrPeakW.tr_peak_w (w_cls k) (rig_tr c mx no cap ID es hs) <=
    (4 * Z.of_nat (length es) + 1) * PresetRoom.lo k + 2 * rig_pb es hs.
Proof.
  intros k c mx no cap ID es hs Hcap Hok. pose proof (PresetRoom.lo_pos k) as Hlo.
  pose proof (tk_rig (w_cls k) (PresetRoom.lo k) 1 1 (w_cls_range k) ltac:(lia) ltac:(lia) ltac:(lia)
                (w_cls_small k) (tk_cls_sk k) c mx no cap ID es hs Hcap (tk_rig_fact es hs Hok)) as H.
  rewrite (tk_rig_sum 1 1 es hs Hok) in H. lia.
Qed.
Lemma rig_c1_peak : forall c mx no cap ID es hs, 0 <= cap -> rig_ok es hs ->
  21 * ReplyTrPeakW.tr_peak_w (w_cls 1) (rig_tr c mx no cap ID es hs) <=
    21 * (4 * Z.of_nat (length es) + 1) + 22 * rig_pb es hs.
Proof.
  intros c mx no cap ID es hs Hcap Hok.
  pose proof (tk_rig (w_cls 1) 21 21 1 (w_cls_range 1) ltac:(lia) ltac:(lia) ltac:(lia) tk_c1_st tk_c1_sk
                c mx no cap ID es hs Hcap (tk_rig_fact es hs Hok)) as H.
  rewrite (tk_rig_sum 21 1 es hs Hok) in H. lia.
Qed.
End tk_inst.

(* ################################################################## the instance term (a Theorem Labs lane row G-BCNL) *)
(* Image B's drain arm (lib/B/W_LLVMFuzzerTestOneInput_drain_defs_x.v :177, _drain_x.v :329, _drain_calls_x.v :109,
   _drain_entry_x.v :102 at the room 2e33f1270a5) and top_x keep check_no_loss's peak after a drain as the Section
   variable dr_cnl_pk : hsrc -> (Z -> bool) -> nat.  A's instance (a working branch ce7d0d0bf8c:
   lib/A/W_LLVMFuzzerTestOneInput_top_x.v :1321, ReplyLScntRP.v :134) is A's cnl_pk of the held list and the drained
   lines; this is the same term over image B.  A consumer Requires this file without Import (as A does), because its
   cnl_tr / cnl_pk would hide lib/B/W_contract_x.v's. *)
Definition dr_cnl_pk_B (h : hsrc) (P : Z -> bool) : nat := cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P.
