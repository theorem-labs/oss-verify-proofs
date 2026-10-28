(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 huf41_kit_x41ck huf411_kit_rs huf411_kit_d1t.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section D1D.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis LO : 4096 <= lo /\ lo <= SPV - 912.
  Hypothesis SPB : SPV < 2^47.
  Hypothesis R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ DST + dcap < 2^47.
  Hypothesis OS1 : DST + dcap <= lo \/ SPV <= DST.
  Hypothesis DL : zlen dtb = 16388.
  Hypothesis R3 : 4096 <= DT /\ DT + 16388 < 2^47.
  Hypothesis DJ2 : DST + dcap <= DT \/ DT + 16388 <= DST.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WDK := [(DST, DST + dcap); (SPV - 376, SPV - 336)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -512)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation OEND := (Z_to_bv 64 (DST + dcap)).
  Notation DT4 := (Z_to_bv 64 (DT + 4)).
  Notation Q62 := (Z_to_bv 64 4611686018427387904).

  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -512) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation BD1 mm c b pad p st lm := (rw_cells usegs mm (SPV + -376) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).

  Notation KD1 mb pe x9 x19 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S :=
    (forall mm' (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y26 y28 y29 y30 y31 c' b' p' : word) (pad' : list byte),
        munch WDK mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
        BD1 mm' c' b' pad' p' (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        evt usegs POST (ST 0x2448c mm' y1 y5 y6 y7 y8 x9 y10 y11 y12 y13 y14 y15 y16 y17 y18 x19 Q62 x21 x22 x23 x24
                           DT4 y26 OEND y28 y29 y30 y31)).

  Notation L1K mb j pe S len bs dl tl x1 x9 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 :=
    (j + 4 <= pe -> forall mm' off' bc' t' a0' a1' nd' a3' c2' a5' m1' a7' (c0' : word) pad' (y6 y7 y8 y18 y28 y29 y30 y31 : word),
        munch WDK mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
        BD1 mm' c0' (Z_to_bv 64 bc') pad' (Z_to_bv 64 (S + off')) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) ->
        bytes_at usegs mm' S bs -> (off' = 0 \/ (1 <= off' /\ off' + 8 <= len /\ bc' <= 64)) -> 0 <= bc' <= 64 ->
        t' mod 2^64 = bc' -> a0' mod 2^64 = 64 -> a1' mod 2^64 = (DST + pe - 3) mod 2^64 -> nd' mod 2^64 = (-1 * DT + -5) mod 2^64 ->
        a3' mod 2^64 = (DST + (j + 4) + 3) mod 2^64 -> c2' mod 2^64 = 2 -> a5' mod 2^64 = 64 - tl -> m1' mod 2^64 = 2^64 - 1 ->
        a7' mod 2^64 = (DST + (j + 4)) mod 2^64 ->
        evt usegs POST (ST 0x24080 mm' x1 (Z_to_bv 64 t') y6 y7 y8 x9 (Z_to_bv 64 a0') (Z_to_bv 64 a1') (Z_to_bv 64 nd') (Z_to_bv 64 a3')
                           (Z_to_bv 64 c2') (Z_to_bv 64 a5') (Z_to_bv 64 m1') (Z_to_bv 64 a7') y18 (Z_to_bv 64 dl) Q62
                           x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND y28 y29 y30 y31)).

  Lemma zbv_eqc : forall a c, a mod 2^64 = c -> 0 <= c < 2^64 -> Z_to_bv 64 a = Z_to_bv 64 c.
  Proof. intros a c H Hc. apply zbv_eqm. rewrite H. symmetry. apply Z.mod_small. exact Hc. Qed.

  Ltac d_rw HA0 HA1 HND HA3 HC2 HA5 HM1 HA7 :=
    rewrite (zbv_eqc _ _ HA0 ltac:(lia)), (zbv_eqm _ _ HA1), (zbv_eqm _ _ HND), (zbv_eqm _ _ HA3),
            (zbv_eqc _ _ HC2 ltac:(lia)), (zbv_eqc _ _ HA5 ltac:(lia)), (zbv_eqc _ _ HM1 ltac:(lia)), (zbv_eqm _ _ HA7);
    clear HA0 HA1 HND HA3 HC2 HA5 HM1 HA7.

  Ltac d_walk STOPS j pe b S len tl :=
    kx_autoLx STOPS 40%nat
      [KZRange j 0 (2^32); KZRange pe 4 (2^32); KZRange (dcap - j) 4 (2^32); KZRange dcap 4 (2^32); KZRange DST 4096 (2^47);
       KZRange (DST + j) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange tl 1 12; KZRange DT 4096 (2^47); KZRange b 0 1088;
       KZRange S 4096 (2^47); KZRange len 8 (2^32);
       KZWr DST dcap; KZWr (SPV + -376) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -376) 40; KZDisj (SPV + -376) 40 DT 16388;
       KZDisj DST dcap S len; KZDisj (SPV + -376) 40 S len]
      [(DT, 16388); (SPV + -512, 136); (SPV + -376, 40)].

  Lemma x41_l1_dt : forall mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 (Z_to_bv 64 b) pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j -> j + 4 <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    S <= P -> P + 8 <= S + len -> 0 <= b <= 1088 ->
    a0 mod 2^64 = 64 -> a1 mod 2^64 = (DST + pe - 3) mod 2^64 -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 ->
    a3 mod 2^64 = (DST + j + 3) mod 2^64 -> c2 mod 2^64 = 2 -> a5 mod 2^64 = 64 - tl -> m1 mod 2^64 = 2^64 - 1 ->
    a7 mod 2^64 = (DST + j) mod 2^64 ->
    L1K mb j pe S len bs dl tl x1 x9 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x242d8 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 a0) (Z_to_bv 64 a1) (Z_to_bv 64 nd) (Z_to_bv 64 a3)
                       (Z_to_bv 64 c2) (Z_to_bv 64 a5) (Z_to_bv 64 m1) (Z_to_bv 64 a7) x18 (Z_to_bv 64 dl) Q62
                       x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 c0 pad x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16
      MU WM MI OUT DTB FR BD DJ3 SB SL S0 S1 SL32 DJS DJK HJ HJ4 HPE HDL HTL HRSV HP0 HP1 HB HA0 HA1 HND HA3 HC2 HA5 HM1 HA7 K K2.
    d_rw HA0 HA1 HND HA3 HC2 HA5 HM1 HA7.
    d_walk [0x24080; 0x243fc] j pe b S len tl.
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x243fc) _ _ _ _) =>
             eapply (x41_g1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 DL R3 DJ2
                       mb _ (j + 4) pe dl tl rsv S); try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24080) _ _ _ _) =>
             eapply (K HJ4 _ (P - S) b); try (replace (S + (P - S)) with P by lia); try eassumption; lia
         end.
  Qed.

  Lemma x41_l1_d4 : forall mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 (Z_to_bv 64 b) pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j -> j + 4 <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    S <= P -> P + 8 <= S + len -> 0 <= b <= 832 ->
    a0 mod 2^64 = 64 -> a1 mod 2^64 = (DST + pe - 3) mod 2^64 -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 ->
    a3 mod 2^64 = (DST + j + 3) mod 2^64 -> c2 mod 2^64 = 2 -> a5 mod 2^64 = 64 - tl -> m1 mod 2^64 = 2^64 - 1 ->
    a7 mod 2^64 = (DST + j) mod 2^64 ->
    L1K mb j pe S len bs dl tl x1 x9 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x24290 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 a0) (Z_to_bv 64 a1) (Z_to_bv 64 nd) (Z_to_bv 64 a3)
                       (Z_to_bv 64 c2) (Z_to_bv 64 a5) (Z_to_bv 64 m1) (Z_to_bv 64 a7) x18 (Z_to_bv 64 dl) Q62
                       x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 c0 pad x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16
      MU WM MI OUT DTB FR BD DJ3 SB SL S0 S1 SL32 DJS DJK HJ HJ4 HPE HDL HTL HRSV HP0 HP1 HB HA0 HA1 HND HA3 HC2 HA5 HM1 HA7 K K2.
    d_rw HA0 HA1 HND HA3 HC2 HA5 HM1 HA7.
    d_walk [0x242d8] j pe b S len tl.
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x242d8) _ _ _ _) =>
             eapply (x41_l1_dt mb _ j pe S len bs dl tl rsv P); try eassumption; first [lia | kx_ev_ranges; lia]
         end.
  Qed.

  Lemma x41_l1_d3 : forall mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 (c0 : word) pad
      (x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 (Z_to_bv 64 b) pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j -> j + 4 <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    S <= P -> P + 8 <= S + len -> 0 <= b <= 576 ->
    a0 mod 2^64 = 64 -> a1 mod 2^64 = (DST + pe - 3) mod 2^64 -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 ->
    a3 mod 2^64 = (DST + j + 3) mod 2^64 -> c2 mod 2^64 = 2 -> a5 mod 2^64 = 64 - tl -> m1 mod 2^64 = 2^64 - 1 ->
    a7 mod 2^64 = (DST + j) mod 2^64 ->
    L1K mb j pe S len bs dl tl x1 x9 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x24244 mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 a0) (Z_to_bv 64 a1) (Z_to_bv 64 nd) (Z_to_bv 64 a3)
                       (Z_to_bv 64 c2) (Z_to_bv 64 a5) (Z_to_bv 64 m1) (Z_to_bv 64 a7) x18 (Z_to_bv 64 dl) Q62
                       x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 c0 pad x1 x5 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16
      MU WM MI OUT DTB FR BD DJ3 SB SL S0 S1 SL32 DJS DJK HJ HJ4 HPE HDL HTL HRSV HP0 HP1 HB HA0 HA1 HND HA3 HC2 HA5 HM1 HA7 K K2.
    d_rw HA0 HA1 HND HA3 HC2 HA5 HM1 HA7.
    d_walk [0x24290] j pe b S len tl.
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24290) _ _ _ _) =>
             eapply (x41_l1_d4 mb _ j pe S len bs dl tl rsv P); try eassumption; first [lia | kx_ev_ranges; lia]
         end.
  Qed.

  Lemma x41_l1_d2 : forall mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 (c0 cb : word) pad
      (x1 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 cb pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j -> j + 4 <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    S <= P -> P + 8 <= S + len -> 0 <= b <= 320 ->
    a0 mod 2^64 = 64 -> a1 mod 2^64 = (DST + pe - 3) mod 2^64 -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 ->
    a3 mod 2^64 = (DST + j + 3) mod 2^64 -> c2 mod 2^64 = 2 -> a5 mod 2^64 = 64 - tl -> m1 mod 2^64 = 2^64 - 1 ->
    a7 mod 2^64 = (DST + j) mod 2^64 ->
    L1K mb j pe S len bs dl tl x1 x9 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x241fc mm x1 (Z_to_bv 64 b) x6 x7 x8 x9 (Z_to_bv 64 a0) (Z_to_bv 64 a1) (Z_to_bv 64 nd) (Z_to_bv 64 a3)
                       (Z_to_bv 64 c2) (Z_to_bv 64 a5) (Z_to_bv 64 m1) (Z_to_bv 64 a7) x18 (Z_to_bv 64 dl) Q62
                       x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 c0 cb pad x1 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16
      MU WM MI OUT DTB FR BD DJ3 SB SL S0 S1 SL32 DJS DJK HJ HJ4 HPE HDL HTL HRSV HP0 HP1 HB HA0 HA1 HND HA3 HC2 HA5 HM1 HA7 K K2.
    d_rw HA0 HA1 HND HA3 HC2 HA5 HM1 HA7.
    d_walk [0x24244] j pe b S len tl.
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24244) _ _ _ _) =>
             eapply (x41_l1_d3 mb _ j pe S len bs dl tl rsv P); try eassumption; first [lia | kx_ev_ranges; lia]
         end.
  Qed.

  Lemma x41_l1_d1 : forall mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 p2 (c0 cb : word) pad
      (x1 x6 x7 x8 x9 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 cb pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j -> j + 4 <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    S <= P -> P + 8 <= S + len -> 0 <= b <= 64 ->
    a0 mod 2^64 = 64 -> a1 mod 2^64 = (DST + pe - 3) mod 2^64 -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 ->
    a3 mod 2^64 = (DST + j + 3) mod 2^64 -> c2 mod 2^64 = 2 -> a5 mod 2^64 = 64 - tl -> m1 mod 2^64 = 2^64 - 1 ->
    a7 mod 2^64 = (DST + j) mod 2^64 -> p2 mod 2^64 = (DST + j) mod 2^64 ->
    L1K mb j pe S len bs dl tl x1 x9 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x241b8 mm x1 (Z_to_bv 64 b) x6 x7 x8 x9 (Z_to_bv 64 a0) (Z_to_bv 64 a1) (Z_to_bv 64 nd) (Z_to_bv 64 a3)
                       (Z_to_bv 64 c2) (Z_to_bv 64 a5) (Z_to_bv 64 m1) (Z_to_bv 64 a7) (Z_to_bv 64 p2) (Z_to_bv 64 dl) Q62
                       x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe S len bs dl tl rsv P b a0 a1 nd a3 c2 a5 m1 a7 p2 c0 cb pad x1 x6 x7 x8 x9 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16
      MU WM MI OUT DTB FR BD DJ3 SB SL S0 S1 SL32 DJS DJK HJ HJ4 HPE HDL HTL HRSV HP0 HP1 HB HA0 HA1 HND HA3 HC2 HA5 HM1 HA7 HP2 K K2.
    d_rw HA0 HA1 HND HA3 HC2 HA5 HM1 HA7. rewrite (zbv_eqm p2 _ HP2). clear HP2.
    d_walk [0x241fc] j pe b S len tl.
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x241fc) _ _ _ _) =>
             eapply (x41_l1_d2 mb _ j pe S len bs dl tl rsv P); try eassumption; first [lia | kx_ev_ranges; lia]
         end.
  Qed.


  Lemma x41_l1_d : forall mb mm j pe S len bs dl tl rsv B P vb vf vq a0 a1 nd a3 c2 a5 m1 a7 p2 (c0 : word) pad
      (x1 x8 x9 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 (Z_to_bv 64 B) pad (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    S <= P -> P + 8 <= S + len -> 0 <= B <= 64 -> (vf mod 2^64 = 0 \/ (vf mod 2^64 = 1 /\ B <= 7)) ->
    vb mod 2^64 = B -> vq mod 2^64 = P mod 2^64 ->
    a0 mod 2^64 = 64 -> a1 mod 2^64 = (DST + pe - 3) mod 2^64 -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 ->
    a3 mod 2^64 = (DST + j + 3) mod 2^64 -> c2 mod 2^64 = 2 -> a5 mod 2^64 = 64 - tl -> m1 mod 2^64 = 2^64 - 1 ->
    a7 mod 2^64 = (DST + j) mod 2^64 -> p2 mod 2^64 = (DST + j) mod 2^64 ->
    L1K mb j pe S len bs dl tl x1 x9 x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x24154 mm x1 (Z_to_bv 64 vb) (Z_to_bv 64 vf) (Z_to_bv 64 vq) x8 x9 (Z_to_bv 64 a0) (Z_to_bv 64 a1)
                       (Z_to_bv 64 nd) (Z_to_bv 64 a3) (Z_to_bv 64 c2) (Z_to_bv 64 a5) (Z_to_bv 64 m1) (Z_to_bv 64 a7)
                       (Z_to_bv 64 p2) (Z_to_bv 64 dl) Q62 x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe S len bs dl tl rsv B P vb vf vq a0 a1 nd a3 c2 a5 m1 a7 p2 c0 pad x1 x8 x9 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16
      MU WM MI OUT DTB FR BD DJ3 SB SL S0 S1 SL32 DJS DJK HJ HPE HDL HTL HRSV HP0 HP1 HB HVF HVB HVQ HA0 HA1 HND HA3 HC2 HA5 HM1 HA7 HP2 K K2.
    assert (O : exists o, P = S + o) by (exists (P - S); lia). destruct O as (o & ->).
    d_rw HA0 HA1 HND HA3 HC2 HA5 HM1 HA7. rewrite (zbv_eqm p2 _ HP2), (zbv_eqc _ _ HVB ltac:(lia)), (zbv_eqm vq _ HVQ).
    clear HP2 HVB HVQ.
    destruct HVF as [HVF | [HVF HB7]];
      [rewrite (zbv_eqm vf 0 ltac:(rewrite HVF; reflexivity)) | rewrite (zbv_eqm vf 1 ltac:(rewrite HVF; reflexivity))]; clear HVF.
    all: kx_autoLx [0x241b8; 0x243fc] 40%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
       KZRange SPV 4096 (2^47); KZRange S 4096 (2^47); KZRange len 8 (2^32); KZRange (S + o) 4096 (2^47); KZRange o 0 (2^32);
       KZRange (len - o) 8 (2^32); KZRange B 0 64; KZRange tl 1 12; KZRange DT 4096 (2^47);
       KZWr DST dcap; KZWr (SPV + -376) 40; KZDisj DST dcap S len; KZDisj (SPV + -376) 40 S len;
       KZDisj DST dcap (SPV + -376) 40; KZDisj (SPV + -376) 40 DT 16388]
      [(S, len)].
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x243fc) _ _ _ _) =>
             eapply (x41_g1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 DL R3 DJ2
                       mb _ j pe dl tl rsv S); try eassumption; lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x241b8) _ _ _ _) =>
             eapply (x41_l1_d1 mb _ j pe S len bs dl tl rsv (S + o) B); try eassumption; lia
         end.
  Qed.

End D1D.
