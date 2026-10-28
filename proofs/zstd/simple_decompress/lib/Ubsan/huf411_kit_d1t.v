(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 huf41_kit_x41ck huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section D1T.
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


  Lemma x41_t1 : forall (k : nat) mb mm j pe dl tl rsv S p q cnt sh nd c2 (c0 b p0 : word) pad
      (x1 x5 x6 x7 x8 x9 x15 x16 x17 x21 x22 x23 x24 x26 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 b pad p0 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    pe - j <= Z.of_nat k -> 0 <= j < pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    p mod 2^64 = (DST + j) mod 2^64 -> q mod 2^64 = (DST + j) mod 2^64 -> cnt mod 2^64 = (pe - j) mod 2^64 ->
    sh mod 2^64 = 64 - tl -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 -> c2 mod 2^64 = 2 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x2443c mm x1 x5 x6 x7 x8 x9 (Z_to_bv 64 nd) (Z_to_bv 64 sh) (Z_to_bv 64 cnt) (Z_to_bv 64 c2) (Z_to_bv 64 q)
                       x15 x16 x17 (Z_to_bv 64 p) (Z_to_bv 64 dl) Q62 x21 x22 x23 x24 DT4 x26 OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    induction k as [|k IH]; intros mb mm j pe dl tl rsv S p q cnt sh nd c2 c0 b p0 pad
      x1 x5 x6 x7 x8 x9 x15 x16 x17 x21 x22 x23 x24 x26 x28 x29 x30 x31 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16
      MU WM MI OUT DTB FR BD DJ3 HK HJ HPE HDL HTL HRSV HP HQ HC HSH HND H2 K; [exfalso; lia|].
    rewrite (zbv_eqm p _ HP), (zbv_eqm q _ HQ), (zbv_eqm cnt _ HC),
            (zbv_eqm sh (64 - tl) ltac:(rewrite HSH; symmetry; apply Z.mod_small; lia)),
            (zbv_eqm nd _ HND), (zbv_eqm c2 2 ltac:(rewrite H2; reflexivity)).
    kx_autoLx [0x2443c; 0x2448c] 40%nat
      [KZRange (pe - j) 1 (2^32); KZRange (dcap - j) 1 (2^32); KZRange j 0 (2^32); KZRange pe 1 (2^32); KZRange dcap 1 (2^32);
       KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47); KZRange tl 1 12; KZRange DT 4096 (2^47);
       KZWr DST dcap; KZWr (SPV + -376) 40;
       KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV + -376) 40; KZDisj (SPV + -376) 40 DT 16388]
      [(DT, 16388); (SPV + -376, 40)].
    all: x41_ck.
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2448c) _ _ _ _) => eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2443c) _ _ _ _) =>
             eapply (IH mb _ (j + 1) pe dl tl rsv S); try eassumption; lia
         end.
  Qed.

  Lemma x41_ts1 : forall mb mm j pe dl tl rsv S p (c0 b p0 : word) pad
      (x1 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 b pad p0 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    0 <= j < pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    p mod 2^64 = (DST + j) mod 2^64 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x24420 mm x1 x5 x6 (Z_to_bv 64 DST) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 p) (Z_to_bv 64 dl) Q62
                       x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe dl tl rsv S p c0 b p0 pad x1 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 MU WM MI OUT DTB FR BD DJ3 HJ HPE HDL HTL HRSV HP K.
    rewrite (zbv_eqm p _ HP).
    kx_autoLx [0x2443c] 10%nat
      [KZRange j 0 (2^32); KZRange pe 1 (2^32); KZRange dcap 1 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange dl 0 65536] (@nil (Z * Z)).
    subst dl.
    eapply (x41_t1 (Z.to_nat (pe - j)) mb mm j pe (tl + 256 * rsv) tl rsv S); try eassumption; try lia;
      rewrite ?(neg_dl_sh tl rsv HTL); lia.
  Qed.

  Lemma x41_g1 : forall mb mm j pe dl tl rsv S p (c0 b p0 : word) pad
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 b pad p0 (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    p mod 2^64 = (DST + j) mod 2^64 ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x243fc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 p) (Z_to_bv 64 dl) Q62
                       x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe dl tl rsv S p c0 b p0 pad x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 MU WM MI OUT DTB FR BD DJ3 HJ HPE HDL HTL HRSV HP K.
    rewrite (zbv_eqm p _ HP).
    kx_autoLx [0x24420; 0x2448c] 10%nat
      [KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange (DST + j) 4096 (2^47);
       KZRange SPV 4096 (2^47)]
      [(SPV + -512, 136)].
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x2448c) _ _ _ _) => eapply K; eassumption
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24420) _ _ _ _) =>
             eapply (x41_ts1 mb _ j pe dl tl rsv S); try eassumption; lia
         end.
  Qed.

End D1T.
