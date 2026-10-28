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

Section D1P.
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

  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].

  Notation X41G := (x41_g1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb LO SPB R1 OS1 DL R3 DJ2).

  Ltac p_side := lazymatch goal with |- evt _ _ _ => idtac | |- _ => try solve [lia] end.

  Ltac p_walk S len off bc j pe BLO BHI OLO OHI :=
    kx_autoLx [0x24154; 0x243fc] 120%nat
      [KZRange bc BLO BHI; KZRange off OLO OHI; KZRange (len - off) 8 (2^32); KZRange len 9 (2^32); KZRange S 4096 (2^47);
       KZRange (S + len) 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZRange DT 4096 (2^47);
       KZRange j 0 (2^32); KZRange pe 0 (2^32); KZRange (pe - j) 0 (2^32); KZRange (DST + dcap) 4096 (2^47);
       KZWr (SPV - 376) 40; KZDisj (SPV - 376) 40 S len; KZDisj (SPV - 376) 40 DT 16388; KZDisj DST dcap (SPV - 376) 40]
      [(S, len); (SPV - 512, 136); (SPV - 376, 40)].

  Lemma x41_l1_p : forall mb mm j pe off S len bs dl tl rsv bc (c0 : word) pad
      (x1 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 : word),
    munch WDK mb mm -> wmono usegs mb mm -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
    BD1 mm c0 (Z_to_bv 64 bc) pad (Z_to_bv 64 (S + off)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> (DT + 16388 <= lo \/ SPV <= DT) ->
    bytes_at usegs mm S bs -> zlen bs = len -> 4096 <= S -> S + len < 2^47 -> len < 2^32 ->
    (DST + dcap <= S \/ S + len <= DST) -> (S + len <= lo \/ SPV <= S) ->
    0 <= j <= pe -> pe <= dcap -> dl = tl + 256 * rsv -> 1 <= tl <= 12 -> 0 <= rsv <= 255 ->
    1 <= off <= 7 -> off + 8 <= len -> 0 <= bc <= 64 ->
    (forall mm' B P vb vf vq a0 a1 nd a3 c2 a5 m1 a7 p2 (c0' : word) pad' (y8 y28 y29 y30 y31 : word),
        munch WDK mb mm' -> wmono usegs mb mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 OEND (Z_to_bv 64 (DST + pe)) w10 w11 w12 w13 (Z_to_bv 64 DST) w15 w16 ->
        BD1 mm' c0' (Z_to_bv 64 B) pad' (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 (S + 8)) -> bytes_at usegs mm' S bs ->
        S <= P -> P + 8 <= S + len -> 0 <= B <= 64 -> (vf mod 2^64 = 0 \/ (vf mod 2^64 = 1 /\ B <= 7)) ->
        vb mod 2^64 = B -> vq mod 2^64 = P mod 2^64 ->
        a0 mod 2^64 = 64 -> a1 mod 2^64 = (DST + pe - 3) mod 2^64 -> nd mod 2^64 = (-1 * DT + -5) mod 2^64 ->
        a3 mod 2^64 = (DST + j + 3) mod 2^64 -> c2 mod 2^64 = 2 -> a5 mod 2^64 = 64 - tl -> m1 mod 2^64 = 2^64 - 1 ->
        a7 mod 2^64 = (DST + j) mod 2^64 -> p2 mod 2^64 = (DST + j) mod 2^64 ->
        evt usegs POST (ST 0x24154 mm' x1 (Z_to_bv 64 vb) (Z_to_bv 64 vf) (Z_to_bv 64 vq) y8 x9 (Z_to_bv 64 a0) (Z_to_bv 64 a1)
                           (Z_to_bv 64 nd) (Z_to_bv 64 a3) (Z_to_bv 64 c2) (Z_to_bv 64 a5) (Z_to_bv 64 m1) (Z_to_bv 64 a7)
                           (Z_to_bv 64 p2) (Z_to_bv 64 dl) Q62 x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND y28 y29 y30 y31)) ->
    KD1 mb pe x9 (Z_to_bv 64 dl) x21 x22 x23 x24 w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 S ->
    evt usegs POST (ST 0x24080 mm x1 (Z_to_bv 64 bc) x6 x7 x8 x9 (Z_to_bv 64 64) (Z_to_bv 64 (DST + pe - 3)) (Z_to_bv 64 (-1 * DT + -5))
                       (Z_to_bv 64 (DST + j + 3)) (Z_to_bv 64 2) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 (DST + j))
                       x18 (Z_to_bv 64 dl) Q62 x21 x22 x23 x24 DT4 (Z_to_bv 64 pe) OEND x28 x29 x30 x31).
  Proof using LO SPB R1 OS1 DL R3 DJ2.
    intros mb mm j pe off S len bs dl tl rsv bc c0 pad x1 x6 x7 x8 x9 x18 x21 x22 x23 x24 x28 x29 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w11 w12 w13 w15 w16 MU WM MI OUT DTB FA BD DJT SB SL S0 S1 SL32 DJS DJK HJ HPE HDL TL RSV HO HOL HB K KD.
    assert (QC : 0 <= bc <= 7 \/ 8 <= bc <= 15 \/ 16 <= bc <= 23 \/ 24 <= bc <= 31 \/ 32 <= bc <= 39 \/ 40 <= bc <= 47 \/ 48 <= bc <= 55 \/ 56 <= bc <= 63 \/ 64 <= bc <= 64) by lia.
    destruct QC as [QC|[QC|[QC|[QC|[QC|[QC|[QC|[QC|QC]]]]]]]];
      [ p_walk S len off bc j pe 0 7 1 7
      | p_walk S len off bc j pe 8 15 1 7
      | destruct (Z_lt_le_dec off 2) as [OQ|OQ]; [p_walk S len off bc j pe 16 23 1 1 | p_walk S len off bc j pe 16 23 2 7]
      | destruct (Z_lt_le_dec off 3) as [OQ|OQ]; [p_walk S len off bc j pe 24 31 1 2 | p_walk S len off bc j pe 24 31 3 7]
      | destruct (Z_lt_le_dec off 4) as [OQ|OQ]; [p_walk S len off bc j pe 32 39 1 3 | p_walk S len off bc j pe 32 39 4 7]
      | destruct (Z_lt_le_dec off 5) as [OQ|OQ]; [p_walk S len off bc j pe 40 47 1 4 | p_walk S len off bc j pe 40 47 5 7]
      | destruct (Z_lt_le_dec off 6) as [OQ|OQ]; [p_walk S len off bc j pe 48 55 1 5 | p_walk S len off bc j pe 48 55 6 7]
      | destruct (Z_lt_le_dec off 7) as [OQ|OQ]; [p_walk S len off bc j pe 56 63 1 6 | p_walk S len off bc j pe 56 63 7 7]
      | p_walk S len off bc j pe 64 64 1 7
      ].
    all: p_side.
    all: x41_ck.
    all: kx_ev_ranges; try kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x243fc) _ _ _ _) =>
             eapply (X41G mb _ j pe dl tl rsv S); first [eassumption | reflexivity | lia]
         | H : rw_cells usegs ?m2 (SPV + -376) [C8 ?c; C4 (Z_to_bv 64 ?B); CB 4 _; C8 (Z_to_bv 64 ?P); _; _]
           |- evt _ _ (MS _ _ (Z_to_bv 64 0x24154) _ _ ?m2 _) =>
             eapply (K m2 B P); first [eassumption | lia]
         end.
  Qed.

End D1P.
