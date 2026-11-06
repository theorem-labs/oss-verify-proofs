(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 625 of its 671 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass9G.v, with its addresses and numbers changed; 1611 of its 1721 lines of code are new or changed and 561 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass1w.v, with its module paths and module names changed; 138 of its 210 lines of code are new or changed and 1649 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotHead.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strnlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
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

Ltac op7_nt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [cbv iota | symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec]
  end.

Lemma op7_hd_tl : forall (P N K' : Z)
    (x1 x2 x3 x4 x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 < P -> P + N < 2 ^ 64 -> 0 <= K' <= N -> bv_unsigned s1 <= N - K' -> s0 = Z_to_bv 64 (P + K') ->
  evt rsegs (fun ms => exists s5 : word,
      ms = MS (mkR (Z_to_bv 64 0x145fc) x2 x3 x4 x5 x6 x7 s0 s1 s0 s1 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 x22 x23
        x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 STRNLEN) fc None m ro /\
      s5 = Z_to_bv 64 (P + K' + bv_unsigned s1))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
      x29 x30 x31) F (Z_to_bv 64 0x145e4) fc None m ro).
Proof.
  intros P N K' x1 x2 x3 x4 x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m ro HP HPN HK HS1 ->.
  pose proof (bv_unsigned_in_range 64 s1) as R1. unfold bv_modulus in R1. cbn in R1.
  step. step. op7_nt. step. op7_nt. op7_go STRNLEN.
  apply evt_done. eexists. split; [reflexivity|]. f_equal; lia.
Qed.

Lemma op7_len : forall (P N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b0 b1 : byte),
  0 <= K <= N -> N < 2 ^ 26 -> 0 < P -> P + N < 2 ^ 64 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b0]) ->
  (K + 1 < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  evt rsegs (fun ms => exists (s0 s1 a0 a1 s10 : word) (D B0 B1 : Z),
      ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 s0 s1 a0 a1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
        (Z_to_bv 64 1) x25 s10 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x145d8) fc None m ro /\
      s0 = Z_to_bv 64 (P + K + D) /\ s10 = Z_to_bv 64 (N - K - D) /\
      a0 = Z_to_bv 64 B0 /\ s1 = Z_to_bv 64 (256 * B1) /\
      ((K = N /\ D = 0 /\ B0 = 0 /\ B1 = 0) \/
       (K + 1 = N /\ D = 1 /\ B0 = bv_unsigned b0 /\ B1 = 0) \/
       (K + 2 <= N /\ D = 2 /\ B0 = bv_unsigned b0 /\ B1 = bv_unsigned b1)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
      (Z_to_bv 64 1) x25 (Z_to_bv 64 (N - K)) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x143b4) fc None m ro).
Proof.
  intros P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31
    F fc m ro b0 b1 HK HN HP HPN RB0 RB1.
  pose proof (bv_unsigned_in_range 8 b0) as BB0. pose proof (bv_unsigned_in_range 8 b1) as BB1.
  unfold bv_modulus in BB0, BB1. change (2 ^ Z.of_N 8) with 256 in BB0, BB1.
  step. if_cases HC.
  - assert (HKN : K = N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_eq in HC. lia. }
    op7_go 0x145d8.
    apply evt_done. do 5 eexists. exists 0, 0, 0. split; [reflexivity|].
    split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. left. lia.
  - assert (HKN : K < N).
    { unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_neq in HC. lia. }
    specialize (RB0 HKN). step. step. op7_nt. step. step. if_cases HE.
    + assert (HK2 : K + 1 < N).
      { unfold bv_eqb in HE. rewrite !unsigned_lit in HE by lia. apply negb_true_iff, Z.eqb_neq in HE. lia. }
      specialize (RB1 HK2). step. step. op7_nt. op7_go 0x145d8.
      apply evt_done. do 5 eexists. exists 2, (bv_unsigned b0), (bv_unsigned b1). split; [reflexivity|].
      split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. right. right. lia.
    + assert (HK1 : K + 1 = N).
      { unfold bv_eqb in HE. rewrite !unsigned_lit in HE by lia. apply negb_false_iff, Z.eqb_eq in HE. lia. }
      op7_go 0x145d8.
      apply evt_done. do 5 eexists. exists 1, (bv_unsigned b0), 0. split; [reflexivity|].
      split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. split; [op7_weq|]. right. left. lia.
Qed.

Lemma op7_tk : forall (Q R B0 B1 : Z)
    (x1 x2 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  0 <= B0 < 256 -> 0 <= B1 < 256 -> 0 <= R < 2 ^ 26 -> 0 < Q -> Q + R < 2 ^ 64 ->
  evt rsegs (fun ms => exists s1 s5 : word,
      ms = MS (mkR (Z_to_bv 64 0x145fc) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 Q) s1 (Z_to_bv 64 Q) s1 x12 x13 x14 x15 x16 x17
        x18 x19 x20 s5 x22 x23 (Z_to_bv 64 1) x25 (Z_to_bv 64 R) x27 x28 x29 x30 x31) F (Z_to_bv 64 STRNLEN) fc None m ro /\
      s5 = Z_to_bv 64 (Q + bv_unsigned s1) /\ bv_unsigned s1 = Z.min (B0 + 256 * B1) R)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 Q) (Z_to_bv 64 (256 * B1)) (Z_to_bv 64 B0) x11 x12 x13 x14 x15 x16 x17
      x18 x19 x20 x21 x22 x23 (Z_to_bv 64 1) x25 (Z_to_bv 64 R) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x145d8) fc None m ro).
Proof.
  intros Q R B0 B1 x1 x2 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31
    F fc m ro HB0 HB1 HR HQ HQR.
  assert (HU : Z.lor (256 * B1) B0 = B0 + 256 * B1).
  { rewrite Z.lor_comm. rewrite <- lor_shiftl8_add by lia. f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia. }
  step. rewrite (unsigned_lit (256 * B1)), (unsigned_lit B0), HU by lia.
  step. if_cases Q1.
  - op7_zc Q1. op7_go 0x145e4.
    eapply evt_cut; [eapply (op7_hd_tl Q R 0); [lia|lia|lia|rewrite unsigned_lit by lia; lia|f_equal; lia]|].
    intros ms (s5 & -> & E5). apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [rewrite E5; f_equal; lia|]. rewrite unsigned_lit by lia. lia.
  - op7_zc Q1. op7_go 0x145e4.
    eapply evt_cut; [eapply (op7_hd_tl Q R 0); [lia|lia|lia|rewrite unsigned_lit by lia; lia|f_equal; lia]|].
    intros ms (s5 & -> & E5). apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [rewrite E5; f_equal; lia|]. rewrite unsigned_lit by lia. lia.
Qed.

Lemma op7_head : forall (P N K : Z)
    (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (b0 b1 : byte),
  0 <= K <= N -> N < 2 ^ 26 -> 0 < P -> P + N < 2 ^ 64 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b0]) ->
  (K + 1 < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K + 1)) 1 = Some [b1]) ->
  evt rsegs (fun ms => exists (s0 s1 s5 s10 : word) (K' : Z),
      ms = MS (mkR (Z_to_bv 64 0x145fc) x2 x3 x4 x5 x6 x7 s0 s1 s0 s1 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 x22 x23
        (Z_to_bv 64 1) x25 s10 x27 x28 x29 x30 x31) F (Z_to_bv 64 STRNLEN) fc None m ro /\
      s0 = Z_to_bv 64 (P + K') /\ s10 = Z_to_bv 64 (N - K') /\ s5 = Z_to_bv 64 (P + K' + bv_unsigned s1) /\
      K <= K' <= N /\ bv_unsigned s1 <= N - K' /\
      K' + bv_unsigned s1 =
        (if K + 2 <=? N then K + 2 + Z.min (bv_unsigned b0 + 256 * bv_unsigned b1) (N - (K + 2)) else N))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
      (Z_to_bv 64 1) x25 (Z_to_bv 64 (N - K)) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x143b4) fc None m ro).
Proof.
  intros P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31
    F fc m ro b0 b1 HK HN HP HPN RB0 RB1.
  eapply evt_cut; [exact (op7_len P N K x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x25 x27 x28 x29 x30 x31 F fc m ro b0 b1 HK HN HP HPN RB0 RB1)|].
  intros ms (s0 & s1 & a0 & a1 & s10 & D & B0 & B1 & -> & -> & -> & -> & -> & HC).
  pose proof (bv_unsigned_in_range 8 b0) as BB0. pose proof (bv_unsigned_in_range 8 b1) as BB1.
  unfold bv_modulus in BB0, BB1. change (2 ^ Z.of_N 8) with 256 in BB0, BB1.
  assert (HB : 0 <= B0 < 256 /\ 0 <= B1 < 256 /\ 0 <= D /\ K + D <= N) by lia.
  destruct HB as (HB0 & HB1 & HD0 & HDN).
  eapply evt_cut; [apply (op7_tk (P + K + D) (N - K - D) B0 B1); lia|].
  intros ms (s1' & s5 & -> & E5 & HS1).
  apply evt_done. exists (Z_to_bv 64 (P + K + D)), s1', s5, (Z_to_bv 64 (N - K - D)), (K + D).
  split; [reflexivity|]. split; [f_equal; lia|]. split; [f_equal; lia|]. split; [rewrite E5; f_equal; lia|].
  split; [lia|]. split; [lia|].
  destruct (Z.leb_spec (K + 2) N); cbv beta iota; lia.
Qed.

Lemma op7_mal : forall (EL : Z) (x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x19 : word),
  evt rsegs (fun ms => exists a0 : word,
      ms = MS (mkR (Z_to_bv 64 0x14608) x2 x3 x4 x5 x6 x7 x8 x9 a0 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 EL) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1608c) fc None m ro /\
      a0 = Z_to_bv 64 (EL + 1))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 EL) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x145fc) fc None m ro).
Proof.
  intros. op7_go 0x1608c. apply evt_done. eexists. split; [reflexivity|]. f_equal; lia.
Qed.

Lemma op7_cpy : forall (Q S0 EL : Z) (x2 x3 x4 x5 x6 x7 x9 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x11 x12 x18 : word),
  0 < Q < 2 ^ 64 ->
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x1461c) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S0) x9 (Z_to_bv 64 Q) (Z_to_bv 64 S0) (Z_to_bv 64 EL) x13 x14 x15 x16 x17 (Z_to_bv 64 Q) (Z_to_bv 64 EL) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1d6e4) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 S0) x9 (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 EL) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14608) fc None m ro).
Proof.
  intros. step. if_cases HC.
  - unfold bv_eqb in HC. rewrite !unsigned_lit in HC by lia. apply Z.eqb_eq in HC. lia.
  - op7_go 0x1d6e4. apply evt_done. reflexivity.
Qed.

Lemma op7_ev : forall (Q M R EL : Z) (x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x10 : word),
  0 <= Q -> 0 <= EL -> Q + EL < 2 ^ 64 -> 0 <= M <= R -> R < 2 ^ 64 ->
  store_ok rsegs m (Z_to_bv 64 (Q + EL)) 1 = true ->
  evt rsegs (fun ms => exists s3 s10 : word,
      ms = MS (mkR (Z_to_bv 64 0x14638) x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 M) (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Q) s3 x20 x21 x22 x23 x24 x25 s10 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x132d8) fc None
        (write_to_mem m (Z_to_bv 64 (Q + EL)) (le1 (Z_to_bv 64 0))) ro /\
      s3 = Z_to_bv 64 (Q + EL) /\ s10 = Z_to_bv 64 (R - M))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 M) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Q) (Z_to_bv 64 EL) x20 x21 x22 x23 x24 x25 (Z_to_bv 64 R) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x1461c) fc None m ro).
Proof.
  intros Q M R EL x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 F fc m
    ro x1 x10 HQ HEL HQE HM HR ST.
  step. step. if_cases HC.
  - exfalso. unfold bv_ltu in HC. rewrite (unsigned_lit Q) in HC by lia.
    rewrite zb_lxor_ones in HC by lia. rewrite !unsigned_lit in HC by lia. apply Z.ltb_lt in HC. lia.
  - op7_go 0x132d8. apply evt_done. do 2 eexists. split; [reflexivity|]. split; [f_equal; lia|].
    rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma op7_chk : forall (Q : Z) (x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x10 : word),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14640) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Q) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x15390) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Q) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14638) fc None m ro).
Proof.
  intros. op7_go 0x15390. apply evt_done. reflexivity.
Qed.

Lemma op7_fr : forall (Q : Z) (x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x1 x10 : word),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x14648) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 Q) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Q) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x15f4c) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Q) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14640) fc None m ro).
Proof.
  intros. op7_go 0x15f4c. apply evt_done. reflexivity.
Qed.

Lemma op7_tl : forall (x1 x2 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (x8 x19 x21 : word),
  evt rsegs (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x21 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 4) x20 (Z_to_bv 64 10) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14648) fc None m ro).
Proof.
  intros. op7_go TAIL_CHECK. apply evt_done. reflexivity.
Qed.
