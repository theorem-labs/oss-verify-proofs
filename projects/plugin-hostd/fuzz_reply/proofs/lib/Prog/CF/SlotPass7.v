(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its numbers changed; 1527 of its 1633 lines of code are new or changed and 558 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass1w.v, with its module paths, module names and addresses changed; 97 of its 176 lines of code are new or changed and 1554 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotHead.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import strnlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Ltac op7_go a :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              let b := eval vm_compute in (Z.eqb pc a) in
              lazymatch b with true => fail | false => step end
          end).

Ltac op7_zc C :=
  unfold bv_eqb, bv_ltu in C; rewrite ?unsigned_lit in C by lia;
  repeat match type of C with
  | negb _ = true => apply negb_true_iff in C
  | negb _ = false => apply negb_false_iff in C
  end;
  lazymatch type of C with
  | (_ =? _) = true => apply Z.eqb_eq in C
  | (_ =? _) = false => apply Z.eqb_neq in C
  | (_ <? _) = true => apply Z.ltb_lt in C
  | (_ <? _) = false => apply Z.ltb_ge in C
  end.

Ltac op7_weq := first [ reflexivity | (f_equal; lia)
  | (f_equal; unfold zxb; rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia)
  | (rewrite ?unsigned_lit by lia; f_equal; lia) ].

Lemma op7_len : forall (P N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b0 b1 : byte),
  0 <= K <= N -> N < 2 ^ 26 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b0]) ->
  (K + 1 < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  evt rsegs (fun ms => exists (s0 a0 a1 s7 : word) (D B0 B1 : Z),
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 s0 x9 a0 a1 x12 x13 x14 (Z_to_bv 64 1) x16 x17 x18 x19 x20 x21 x22 s7
        x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14068) fc None m ro /\
      s0 = Z_to_bv 64 (P + K + D) /\ s7 = Z_to_bv 64 (N - K - D) /\
      a0 = Z_to_bv 64 B0 /\ a1 = Z_to_bv 64 (256 * B1) /\
      ((K = N /\ D = 0 /\ B0 = 0 /\ B1 = 0) \/
       (K + 1 = N /\ D = 1 /\ B0 = bv_unsigned b0 /\ B1 = 0) \/
       (K + 2 <= N /\ D = 2 /\ B0 = bv_unsigned b0 /\ B1 = bv_unsigned b1)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17 x18 x19 x20 x21
      x22 (Z_to_bv 64 (N - K)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13dc0) fc None m ro).
Proof.
  intros P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro b0 b1 HK HN RB0 RB1.
  pose proof (bv_unsigned_in_range 8 b0) as BB0. pose proof (bv_unsigned_in_range 8 b1) as BB1.
  unfold bv_modulus in BB0, BB1. change (2 ^ Z.of_N 8) with 256 in BB0, BB1.
  step. if_cases Q1.
  - op7_zc Q1. assert (KN : K = N) by lia.
    step. step. step.
    apply evt_done. do 4 eexists. exists 0, 0, 0. split; [reflexivity|].
    split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. left. lia.
  - op7_zc Q1. specialize (RB0 ltac:(lia)).
    step. step. if_cases Q2.
    + op7_zc Q2. specialize (RB1 ltac:(lia)).
      step. step. step. step.
      apply evt_done. do 4 eexists. exists 2, (bv_unsigned b0), (bv_unsigned b1). split; [reflexivity|].
      split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. right. right. lia.
    + op7_zc Q2.
      step. step. step. step.
      apply evt_done. do 4 eexists. exists 1, (bv_unsigned b0), 0. split; [reflexivity|].
      split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. right. left. lia.
Qed.

Lemma op7_tk : forall (Q R B0 B1 : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 <= B0 < 256 -> 0 <= B1 < 256 -> 0 <= R < 2 ^ 26 ->
  evt rsegs (fun ms => exists s2 : word,
      ms = MS (mkR (Z_to_bv 64 0x14080) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 Q) x9 (Z_to_bv 64 Q) s2 x12 x13 x14 x15 x16 x17
        s2 x19 x20 x21 x22 (Z_to_bv 64 R) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 STRNLEN) fc None m ro /\
      bv_unsigned s2 = Z.min (B0 + 256 * B1) R)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 Q) x9 (Z_to_bv 64 B0) (Z_to_bv 64 (256 * B1)) x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 (Z_to_bv 64 R) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14068) fc None m ro).
Proof.
  intros Q R B0 B1 x1 x2 x3 x4 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro HB0 HB1 HR.
  assert (HU : Z.lor (256 * B1) B0 = B0 + 256 * B1).
  { rewrite Z.lor_comm. rewrite <- lor_shiftl8_add by lia. f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia. }
  step. rewrite (unsigned_lit (256 * B1)), (unsigned_lit B0), HU by lia.
  step. if_cases Q1.
  - op7_zc Q1. op7_go STRNLEN. apply evt_done. eexists. split; [reflexivity|].
    rewrite unsigned_lit by lia. lia.
  - op7_zc Q1. op7_go STRNLEN. apply evt_done. eexists. split; [reflexivity|].
    rewrite unsigned_lit by lia. lia.
Qed.

Lemma op7_head : forall (P N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b0 b1 : byte),
  0 <= K <= N -> N < 2 ^ 26 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b0]) ->
  (K + 1 < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  evt rsegs (fun ms => exists (s0 s2 s7 : word) (K' : Z),
      ms = MS (mkR (Z_to_bv 64 0x14080) x2 x3 x4 x5 x6 x7 s0 x9 s0 s2 x12 x13 x14 (Z_to_bv 64 1) x16 x17 s2 x19
        x20 x21 x22 s7 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 STRNLEN) fc None m ro /\
      s0 = Z_to_bv 64 (P + K') /\ s7 = Z_to_bv 64 (N - K') /\ K <= K' <= N /\ bv_unsigned s2 <= N - K' /\
      K' + bv_unsigned s2 =
        (if K + 2 <=? N then K + 2 + Z.min (bv_unsigned b0 + 256 * bv_unsigned b1) (N - (K + 2)) else N))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 (Z_to_bv 64 1) x16 x17 x18 x19
      x20 x21 x22 (Z_to_bv 64 (N - K)) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13dc0) fc None m ro).
Proof.
  intros P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31
    F fc m ro b0 b1 HK HN RB0 RB1.
  eapply evt_cut; [exact (op7_len P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x24
    x25 x26 x27 x28 x29 x30 x31 F fc m ro b0 b1 HK HN RB0 RB1)|].
  intros ms (s0 & a0 & a1 & s7 & D & B0 & B1 & -> & -> & -> & -> & -> & HC).
  pose proof (bv_unsigned_in_range 8 b0) as BB0. pose proof (bv_unsigned_in_range 8 b1) as BB1.
  unfold bv_modulus in BB0, BB1. change (2 ^ Z.of_N 8) with 256 in BB0, BB1.
  assert (HB : 0 <= B0 < 256 /\ 0 <= B1 < 256 /\ 0 <= D /\ K + D <= N) by lia.
  destruct HB as (HB0 & HB1 & HD0 & HDN).
  eapply evt_cut; [apply (op7_tk (P + K + D) (N - K - D) B0 B1); lia|].
  intros ms (s2 & -> & HS2).
  apply evt_done. exists (Z_to_bv 64 (P + K + D)), s2, (Z_to_bv 64 (N - K - D)), (K + D).
  split; [reflexivity|]. split; [f_equal; lia|]. split; [f_equal; lia|]. split; [lia|]. split; [lia|].
  destruct (Z.leb_spec (K + 2) N); cbv beta iota; lia.
Qed.

Lemma op7_mal : forall (EL : Z) (x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x19 : word),
  evt rsegs (fun ms => exists a0 : word,
      ms = MS (mkR (Z_to_bv 64 0x1408c) x2 x3 x4 x5 x6 x7 x8 x9 a0 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 EL) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x157a4) fc None m ro /\
      a0 = Z_to_bv 64 (EL + 1))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 EL) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14080) fc None m ro).
Proof.
  intros. op7_go 0x157a4. apply evt_done. eexists. split; [reflexivity|]. f_equal; lia.
Qed.

Lemma op7_cpy : forall (Q S0 M R EL : Z) (x2 x3 x4 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x9 x11 x12 : word),
  0 < Q < 2 ^ 64 -> 0 <= M <= R -> R < 2 ^ 64 ->
  evt rsegs (fun ms => exists s2 s7 : word,
      ms = MS (mkR (Z_to_bv 64 0x140a8) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S0) (Z_to_bv 64 Q) (Z_to_bv 64 Q) (Z_to_bv 64 S0) (Z_to_bv 64 EL) x13 x14 x15 x16 x17 s2 (Z_to_bv 64 EL) x20 x21 x22 s7 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1cdfc) fc None m ro /\
      s2 = Z_to_bv 64 (S0 + M) /\ s7 = Z_to_bv 64 (R - M))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S0) x9 (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 M) (Z_to_bv 64 EL) x20 x21 x22 (Z_to_bv 64 R) x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1408c) fc None m ro).
Proof.
  intros. step. if_cases HC.
  - unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_eq in HC. lia.
  - op7_go 0x1cdfc. apply evt_done. do 2 eexists. split; [reflexivity|]. split; [reflexivity|].
    rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma op7_ev : forall (Q EL : Z) (x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x10 : word),
  store_ok rsegs m (Z_to_bv 64 (Q + EL)) 1 = true ->
  evt rsegs (fun ms => exists s3 : word,
      ms = MS (mkR (Z_to_bv 64 0x140b8) x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 Q) (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 x18 s3 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1316c) fc None
        (write_to_mem m (Z_to_bv 64 (Q + EL)) (le1 (Z_to_bv 64 0))) ro /\
      s3 = Z_to_bv 64 (Q + EL))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 Q) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 EL) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x140a8) fc None m ro).
Proof.
  intros. op7_go 0x1316c. apply evt_done. eexists. split; [reflexivity|]. f_equal; lia.
Qed.

Lemma op7_chk : forall (Q : Z) (x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x10 : word),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x140c0) x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 Q) (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14a90) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 Q) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x140b8) fc None m ro).
Proof.
  intros. op7_go 0x14a90. apply evt_done. reflexivity.
Qed.

Lemma op7_fr : forall (Q : Z) (x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x10 : word),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x140c8) x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 Q) (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x15664) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 Q) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x140c0) fc None m ro).
Proof.
  intros. op7_go 0x15664. apply evt_done. reflexivity.
Qed.

Lemma op7_tl : forall (SP : Z) (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x8 x18 x19 : word),
  evt rsegs (fun ms => exists s3 : word,
      ms = MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x18 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m ro /\
      s3 = Z_to_bv 64 (SP + 32))
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x140c8) fc None m ro).
Proof.
  intros. op7_go TAIL_CHECK. apply evt_done. eexists. split; [reflexivity|]. f_equal; lia.
Qed.
