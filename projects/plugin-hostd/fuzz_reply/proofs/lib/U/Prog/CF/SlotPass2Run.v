(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1247 of its 1329 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/drain_b_seg.v, with its module paths and module names changed; 267 of its 305 lines of code are new or changed and 1291 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep SlotHead.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_no_loss_read_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import check_no_loss_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c check_no_loss_read.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op2_seg_drain : forall
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14378) x2 x3 x4 x5 x6 x7 x8 x9 x18 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 DRAIN) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14370) fc None m ro).
Proof.
  intros. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_unlock : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14384) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x19 x11 x12 x13 x14 x15
      x16 x17 x18 (Z_to_bv 64 4) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 PTHREAD_MUTEX_UNLOCK) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14378) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_cnlr : forall
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x1438c) x2 x3 x4 x5 x6 x7 x8 x9 x9 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CHECK_NO_LOSS_READ) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14384) fc None m ro).
Proof.
  intros. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_cnl : forall (SP : Z)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14398) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x9 (Z_to_bv 64 (SP + 40))
      x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 CHECK_NO_LOSS) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1438c) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_done : forall (SP : Z) (v : word)
    (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (SP + 40)) 8 = Some (le8 v) ->
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x145bc) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 v x11
      x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
      (Z_to_bv 64 CHECK_SHAPE_DONE) fc None m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14398) fc None m ro).
Proof.
  intros. step. step. step. apply evt_done. reflexivity.
Qed.

Lemma op2_seg_tail : forall
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x145bc) fc None m ro).
Proof.
  intros. step. apply evt_done. reflexivity.
Qed.

Lemma p2_rd4 : forall m a (v : word), bytes_at rsegs m a (le4 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 v).
Proof.
  intros m a v H. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma p2_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, H1, H2. reflexivity.
Qed.

Lemma p2_head : forall m K e es, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  bytes_at rsegs m K (concat (map entry_bytes (e :: es))) ->
  bytes_at rsegs m K (le4 (Z_to_bv 64 (re_fd e))) /\ bytes_at rsegs m (K + 4) (le4 (Z_to_bv 64 (re_eof e))) /\
  bytes_at rsegs m (K + 56) (concat (map entry_bytes es)).
Proof.
  intros m K e es H1 H2 H. cbn [map concat] in H. apply bytes_at_app in H. destruct H as [HE HR].
  rewrite p2_entry_len in HR by assumption.
  unfold entry_bytes in HE. apply bytes_at_app in HE. destruct HE as [HF HE].
  apply bytes_at_app in HE. destruct HE as [HE _]. rewrite length_le4 in HE.
  split; [exact HF|]. split; [exact HE|exact HR].
Qed.

Lemma p2_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma p2_lts0 : forall N, 0 <= N < 2 ^ 63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 N) = (0 <? N).
Proof.
  intros N HN. rewrite bv_lts_zero_l, unsigned_lit by lia.
  destruct (Z.ltb_spec 0 N), (Z.ltb_spec N (2 ^ 63)); cbn; lia.
Qed.

Lemma p2_nth : forall (T : Type) (l : list T) x l', nth_error (l ++ x :: l') (length l) = Some x.
Proof. intros T l. induction l as [|a l IH]; intros x l'; cbn; [reflexivity|apply IH]. Qed.

Lemma p2_firstn : forall (T : Type) (l l' : list T), firstn (length l) (l ++ l') = l.
Proof. intros T l. induction l as [|a l IH]; intros l'; cbn; [reflexivity|f_equal; apply IH]. Qed.

Lemma p2_entry_scan : forall rc B L A m e, CF.RelayRep.entry_ok (rc := rc) B L A m e ->
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
  (re_eof e = 0 \/ re_eof e = 1).
Proof. intros rc B L A m e (EF & _ & P1 & P2 & FD & _). tauto. Qed.

Lemma p2_mod8 : forall G i, G mod 8 = 0 -> (G + 56 * i) mod 8 = 0.
Proof.
  intros G i H. replace (G + 56 * i) with (G + 7 * i * 8) by ring. rewrite Z_mod_plus_full. exact H.
Qed.

Lemma p2_land7 : forall x, 0 <= x < 2 ^ 64 -> x mod 8 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x Hx H. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H.
Qed.

Ltac p2_cmp :=
  repeat match goal with
  | |- context [v_sltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      first
        [ replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 1)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with (Z_to_bv 64 0)
            by (unfold v_sltu, c_ltu, bv_ltu; rewrite !unsigned_lit by lia;
                replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  | |- context [v_sltiu (Z_to_bv 64 ?x) 1] =>
      first
        [ replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 1)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
        | replace (v_sltiu (Z_to_bv 64 x) 1) with (Z_to_bv 64 0)
            by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
                replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ]
  end.

Ltac p2_land :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] =>
      rewrite (p2_land7 x) by first [lia | assumption]
  end.

Ltac p2_if_f :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
  end.

Definition op2_post (es : list rentry) (G SP S fd : Z)
    (x3 x4 x5 x6 x7 x8 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (ms : machine_state) : Prop :=
  (Forall (fun e => re_fd e <> fd) es /\
   exists a0 a1 a2 a3 a4 a5 a6 a7 s2 : word,
     ms = MS (mkR (Z_to_bv 64 0x14348) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) a0 a1 a2 a3 a4 a5 a6 a7 s2
                  x19 (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc
             None (write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))) ro) \/
  (exists (i : nat) (e : rentry),
     nth_error es i = Some e /\ re_fd e = fd /\ Forall (fun e' => re_fd e' <> fd) (firstn i es) /\
     ((re_eof e = 1 /\
       exists a0 a1 a2 a3 a4 a5 a6 a7 : word,
         ms = MS (mkR (Z_to_bv 64 0x14348) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 (G + 56 * Z.of_nat i)) x19 (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 x28 x29
                      x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None
                 (write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))) ro) \/
      (re_eof e = 0 /\
       exists a1 a2 a3 a4 a5 a6 a7 : word,
         ms = MS (mkR (Z_to_bv 64 0x14370) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 0x318f8)
                      a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (G + 56 * Z.of_nat i)) (Z_to_bv 64 0x318f8)
                      (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F
                 (Z_to_bv 64 PTHREAD_MUTEX_LOCK) fc None
                 (write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))) ro))).

Lemma op2_loop : forall (rest pre es : list rentry) (G K SP S fd n : Z)
    (x3 x4 x5 x6 x7 x8 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  es = pre ++ rest -> rest <> [] -> (length es <= 4)%nat ->
  K = G + 56 * Z.of_nat (length pre) -> n = Z.of_nat (length rest) ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) rest ->
  bytes_at rsegs m K (concat (map entry_bytes rest)) ->
  Forall (fun e => re_fd e <> fd) pre -> 0 <= fd < 2 ^ 31 ->
  store_ok rsegs m (Z_to_bv 64 (SP + 40)) 8 = true ->
  0 < G -> G mod 8 = 0 -> 0 <= SP -> SP + 48 <= 2 ^ 64 -> G + 896 <= SP + 40 \/ SP + 48 <= G ->
  evt rsegs (op2_post es G SP S fd x3 x4 x5 x6 x7 x8 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro)
    (MS (mkR (Z_to_bv 64 0x14348) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 fd) (Z_to_bv 64 K)
      (Z_to_bv 64 n) (Z_to_bv 64 G) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 K) x17 x18 x19 (Z_to_bv 64 0x318a0)
      x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14ea4) fc None m ro).
Proof.
  induction rest as [|e rest IH];
    intros pre es G K SP S fd n x3 x4 x5 x6 x7 x8 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro
      Hes Hne Hlen HK Hn HW HB HP Hfd HS HG0 HG8 HSP0 HSP1 HD; [congruence|].
  apply Forall_cons_iff in HW. destruct HW as [(P1 & P2 & Rfd & Reof) HW].
  destruct (p2_head m K e rest P1 P2 HB) as (BF & BE & BR).
  pose proof (bytes_at_bound _ _ _ _ BR) as BDR.
  assert (HL : (length (pre ++ e :: rest) <= 4)%nat) by (rewrite <- Hes; exact Hlen).
  rewrite length_app in HL. cbn [length] in HL, Hn.
  assert (HK8 : K mod 8 = 0) by (rewrite HK; apply p2_mod8; exact HG8).
  pose proof (p2_rd4 m K _ BF) as RF.
  step. p2_if_f.
  step. p2_cmp.
  step.
  step. p2_if_f.
  step. p2_if_f.
  step. rewrite (sx32_lit (re_fd e)) by lia.
  step.
  destruct (Z.eq_dec (re_fd e) fd) as [Hq|Hq].
  - rewrite Hq. if_true. clear RF.
    step. step.
    step.
    step. p2_if_f.
    step.
    step. p2_land.
    step. p2_if_f.
    assert (BE' : bytes_at rsegs (write_to_mem m (Z_to_bv 64 (SP + 40)) (le8 (Z_to_bv 64 0))) (K + 4)
                   (le4 (Z_to_bv 64 (re_eof e)))).
    { apply (bytes_at_write_other rsegs m (SP + 40) (le8 (Z_to_bv 64 0)) (K + 4) _ BE);
        rewrite ?length_le8, ?length_le4; lia. }
    pose proof (p2_rd4 _ (K + 4) _ BE') as RE.
    step. rewrite (sx32_lit (re_eof e)) by lia.
    step.
    destruct Reof as [E0|E1].
    + rewrite E0. if_false. step. step. step.
      apply evt_done. unfold op2_post. right. exists (length pre), e.
      split; [rewrite Hes; apply p2_nth|]. split; [exact Hq|]. split; [rewrite Hes, p2_firstn; exact HP|].
      right. split; [exact E0|]. do 7 eexists. rewrite <- HK. reflexivity.
    + rewrite E1. if_true.
      apply evt_done. unfold op2_post. right. exists (length pre), e.
      split; [rewrite Hes; apply p2_nth|]. split; [exact Hq|]. split; [rewrite Hes, p2_firstn; exact HP|].
      left. split; [exact E1|]. do 8 eexists. rewrite <- HK. reflexivity.
  - if_false_by (eq_trans (p2_eqb (re_fd e) fd ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_neq _ _) Hq)).
    step. step. step.
    step.
    if_cases HC; rewrite p2_eqb in HC by lia;
      rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff, ?Z.eqb_eq, ?Z.eqb_neq in HC;
      destruct rest as [|e2 rest2]; cbn [length] in Hn; try (exfalso; lia).
    all: first
      [ solve [ step; step; step; step; step; if_true;
                apply evt_done; unfold op2_post; left; split;
                [ rewrite Hes; apply Forall_app; split; [exact HP|constructor; [exact Hq|constructor]]
                | do 9 eexists; reflexivity ] ]
      | solve [ eapply (IH (pre ++ [e]) es G (K + 56) SP S fd (n + -1));
                first [ exact HW | exact BR | exact Hfd | exact HS | exact Hlen | exact HG0 | exact HG8
                      | exact HSP0 | exact HSP1 | exact HD | congruence
                      | (rewrite Hes, <- app_assoc; reflexivity)
                      | (rewrite length_app; cbn [length]; lia)
                      | (cbn [length] in Hn |- *; lia)
                      | (apply Forall_app; split; [exact HP|constructor; [exact Hq|constructor]]) ] ] ].
Qed.

Lemma op2_scan : forall (es : list rentry) (tail : list byte) (G SP S fd : Z)
    (x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  ov_read_bytes rsegs m (Z_to_bv 64 0x318b8) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length es)))) ->
  ov_read_bytes rsegs m (Z_to_bv 64 S) 4 = Some (le4 (Z_to_bv 64 fd)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x318d0) 8 = Some (le8 (Z_to_bv 64 G)) ->
  rw_cells rsegs m G [CB 896 (concat (map entry_bytes es) ++ tail)] ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es ->
  (length es <= 4)%nat -> 0 <= fd < 2 ^ 31 ->
  store_ok rsegs m (Z_to_bv 64 (SP + 40)) 8 = true ->
  0 < S < 2 ^ 64 -> S mod 8 = 0 ->
  (es <> [] -> 0 < G /\ G mod 8 = 0 /\ 0 <= SP /\ SP + 48 <= 2 ^ 64 /\ (G + 896 <= SP + 40 \/ SP + 48 <= G)) ->
  evt rsegs (op2_post es G SP S fd x3 x4 x5 x6 x7 x8 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      (Z_to_bv 64 0x318a0) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14334) fc None m ro).
Proof.
  intros es tail G SP S fd x1 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26
    x27 x28 x29 x30 x31 F fc m ro RN RF RG TB HW Hlen Hfd HS HS0 HS8 HGP.
  destruct TB as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply bytes_at_app in HB. destruct HB as [HB _].
  step. p2_if_f.
  step. p2_land.
  step. p2_if_f.
  step. rewrite (sx32_lit fd) by lia.
  step.
  step. step.
  step. rewrite (sx32_lit (Z.of_nat (length es))) by lia.
  step. rewrite p2_lts0 by lia.
  if_cases HC.
  - apply Bool.negb_true_iff, Z.ltb_ge in HC.
    destruct es as [|e0 es0]; [|cbn [length] in HC; lia].
    step. step. step.
    step. step. if_true.
    apply evt_done. unfold op2_post. left. split; [constructor|]. do 9 eexists. reflexivity.
  - apply Bool.negb_false_iff, Z.ltb_lt in HC.
    destruct es as [|e0 es0]; [cbn [length] in HC; lia|].
    destruct (HGP ltac:(discriminate)) as (HG0 & HG8 & HSP0 & HSP1 & HD).
    pose proof HW as HW0. apply Forall_cons_iff in HW0. destruct HW0 as [(P1 & P2 & _) _].
    destruct (p2_head m G e0 es0 P1 P2 HB) as (_ & _ & BR0).
    pose proof (bytes_at_bound _ _ _ _ BR0) as BDB.
    step.
    step. p2_cmp.
    step. p2_land.
    step. p2_cmp.
    step.
    step. step.
    eapply (op2_loop (e0 :: es0) [] (e0 :: es0) G G SP S fd (Z.of_nat (length (e0 :: es0))));
      first [ exact HW | exact HB | exact Hfd | exact HS | exact Hlen | exact HG0 | exact HG8 | exact HSP0
            | exact HSP1 | exact HD | discriminate | reflexivity | constructor | (cbn [length]; lia) ].
Qed.
