(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx41g.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX41H.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).


  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SINV := RZ_huf_dx41.SINV.

  Notation WFR := [(SPV - 416, SPV - 216)].
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation x41_hide := RZ_huf_dx41g.x41_hide.
  #[local] Ltac kx_lia ::= kx_bv_ranges; first [ solve [lia] | solve [kx_lia_pruned] ].   (* [comment removed for export] *)

  Lemma x41_r_hi : forall mm j j4 e1 g2 g3 S1 n1 b1 o1 p1 S2 n2 b2 o2 p2 q2 S3 n3 b3 o3 p3 q3 S4 n4 b4 o4 p4 q4 (k3 k4 b4w p4w : word) pad
      (x1 x13 x14 x17 x18 x19 x26 x27 x28 x29 x31 : word)
      (w0 w3 w5 w6 w7 w8 w9 w10 w12 w19 : word),
    8 <= o1 ->
    mem_inv psegs mm ->
    FRA mm w0 (Z_to_bv 64 S1) (Z_to_bv 64 S2) w3 (Z_to_bv 64 (DST + e1)) w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (S4 + 8)) w12 (Z_to_bv 64 g3) (Z_to_bv 64 g2) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) w19 ->
    BD4 mm k4 b4w pad p4w (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    DINV1 o1 n1 p1 -> DINV2 o2 n2 p2 q2 -> DINV2 o3 n3 p3 q3 -> DINV2 o4 n4 p4 q4 ->
    0 <= j <= dcap -> 0 <= j4 <= dcap -> 0 <= e1 <= dcap -> 0 <= g2 <= dcap -> 0 <= g3 <= dcap ->
    (forall mm' T2 P1 P2 P3 P4 c1' c2' c3' c4' (k3' k4' b4w' p4w' y1 y8 y9 y11 y12 y14 y19 y26 y27 y28 y29 y31 : word),
        munch WFR mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' ->
        FRA mm' w0 (Z_to_bv 64 S1) (Z_to_bv 64 S2) w3 (Z_to_bv 64 (DST + e1)) w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (S4 + 8)) w12 (Z_to_bv 64 g3) (Z_to_bv 64 g2) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c2') ->
        BD4 mm' k4' b4w' pad p4w' (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        HINV (P1 - S1) n1 c1' -> HINV (P2 - S2) n2 c2' -> HINV (P3 - S3) n3 c3' -> HINV (P4 - S4) n4 c4' ->
        T2 = DST + (j + 4) -> j4 + 4 < dcap - 3 ->
        evt psegs POST (ST 0x22e10 mm' y1 (Z_to_bv 64 (DST + j)) k4' (Z_to_bv 64 T2) y8 y9 (Z_to_bv 64 P4) y11 y12 (Z_to_bv 64 c1') y14 k3' (Z_to_bv 64 DST) x17 x18 y19 (Z_to_bv 64 DST) (Z_to_bv 64 P2) (Z_to_bv 64 c3') (Z_to_bv 64 P3) (Z_to_bv 64 P1) (Z_to_bv 64 e1) y26 y27 y28 y29 (Z_to_bv 64 c4') y31)) ->
    (forall mm' T0 A2 A5 A7 P1 P2 P3 P4 c1' c2' c3' c4' (k3' k4' y1 y6 y7 y11 y14 y16 y19 y26 y27 y28 y29 y30 y31 : word),
        munch WFR mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' ->
        FRA mm' w0 (Z_to_bv 64 S1) (Z_to_bv 64 S2) w3 (Z_to_bv 64 (DST + e1)) w5 k3' w7 w8 w9 w10 (Z_to_bv 64 (S4 + 8)) w12 (Z_to_bv 64 g3) (Z_to_bv 64 g2) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c2') ->
        BD4 mm' k4' (Z_to_bv 64 c4') pad (Z_to_bv 64 P4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        SINV (P1 - S1) n1 c1' -> SINV (P2 - S2) n2 c2' -> SINV (P3 - S3) n3 c3' -> SINV (P4 - S4) n4 c4' ->
        0 <= c1' < 2^64 -> 0 <= c2' < 2^64 -> 0 <= c3' < 2^64 -> 0 <= c4' < 2^32 ->
        T0 = DST + (j + 4) -> A7 = DST + (j + 4 + e1) -> A5 = DST + (j + 4 + g2) -> A2 = DST + (j + 4 + g3) ->
        evt psegs POST (ST 0x232bc mm' y1 (Z_to_bv 64 T0) y6 y7 (Z_to_bv 64 S1) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + e1)) y11 (Z_to_bv 64 A2) (Z_to_bv 64 c1') y14 (Z_to_bv 64 A5) y16 (Z_to_bv 64 A7) x18 y19 (Z_to_bv 64 DST) (Z_to_bv 64 P2) (Z_to_bv 64 c3') (Z_to_bv 64 P3) (Z_to_bv 64 P1) (Z_to_bv 64 e1) y26 y27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x23024 mm x1 (Z_to_bv 64 (DST + j)) k4 (Z_to_bv 64 (DST + j4)) (Z_to_bv 64 p3) (Z_to_bv 64 q3) (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 q4) (Z_to_bv 64 p1) x13 x14 k3 (Z_to_bv 64 DST) x17 x18 x19 (Z_to_bv 64 p2) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 q2) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 e1) x26 x27 x28 x29 (Z_to_bv 64 p4) x31).
  Proof.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm j j4 e1 g2 g3 S1 n1 b1 o1 p1 S2 n2 b2 o2 p2 q2 S3 n3 b3 o3 p3 q3 S4 n4 b4 o4 p4 q4 k3 k4 b4w p4w pad
      x1 x13 x14 x17 x18 x19 x26 x27 x28 x29 x31
      w0 w3 w5 w6 w7 w8 w9 w10 w12 w19 O1 MI FA BD SB1 SB2 SB3 SB4 HD1 HD2 HD3 HD4 HJ HJ4 HE1 HG2 HG3 KH KE.
    assert (MU : munch WFR mm mm) by apply munch_refl.
    assert (WM : wmono psegs mm mm) by apply wmono_refl.
    destruct SB1 as (B1 & L1 & R10 & R11 & R12 & D11 & D12). destruct SB2 as (B2 & L2 & R20 & R21 & R22 & D21 & D22).
    destruct SB3 as (B3 & L3 & R30 & R31 & R32 & D31 & D32). destruct SB4 as (B4 & L4 & R40 & R41 & R42 & D41 & D42).
    destruct HD1 as (HP1 & HO1 & HX1). destruct HD2 as (HP2 & HQ2 & HO2 & HX2).
    destruct HD3 as (HP3 & HQ3 & HO3 & HX3). destruct HD4 as (HP4 & HQ4 & HO4 & HX4).
    (* [comment removed for export] *)
    assert (K1 : S1 + n1 <= SPV - 416 \/ SPV <= S1) by (clear - D12 LO; lia).
    assert (K2 : S2 + n2 <= SPV - 416 \/ SPV <= S2) by (clear - D22 LO; lia).
    assert (K3 : S3 + n3 <= SPV - 416 \/ SPV <= S3) by (clear - D32 LO; lia).
    assert (K4 : S4 + n4 <= SPV - 416 \/ SPV <= S4) by (clear - D42 LO; lia).
    clear D11 D21 D31 D41 D12 D22 D32 D42 OS1 DJ2 R3 DL.
    destruct (Z_lt_le_dec o2 8) as [O2|O2]; destruct (Z_lt_le_dec o3 8) as [O3|O3]; destruct (Z_lt_le_dec o4 8) as [O4|O4].
    all: try (assert (N1 : o1 + 8 <= n1 /\ p1 <= 56) by (clear - HX1 O1; lia));
         try (assert (N2 : o2 + 8 <= n2 /\ p2 <= 44) by (clear - HX2 O2; lia));
         try (assert (N3 : o3 + 8 <= n3 /\ p3 <= 44) by (clear - HX3 O3; lia));
         try (assert (N4 : o4 + 8 <= n4 /\ p4 <= 44) by (clear - HX4 O4; lia)).
    all: change (x41_hide (o1 = 0 \/ o1 + 8 <= n1 /\ p1 <= 56)) in HX1; change (x41_hide (o2 = 0 \/ o2 + 8 <= n2 /\ p2 <= 44)) in HX2;
         change (x41_hide (o3 = 0 \/ o3 + 8 <= n3 /\ p3 <= 44)) in HX3; change (x41_hide (o4 = 0 \/ o4 + 8 <= n4 /\ p4 <= 44)) in HX4.
    (* [comment removed for export] *)
    all: [>
         (* [comment removed for export] *)
           kx_autoLx [0x22e10; 0x232bc] 200%nat
               [(KZRange o1 8 (2^32)); (KZRange (n1 - o1) 8 (2^32)); (KZRange p1 0 56); (KZRange o2 0 7); (KZRange o2 0 7); (KZRange p2 0 100); (KZRange o3 0 7); (KZRange o3 0 7); (KZRange p3 0 100); (KZRange o4 0 7); (KZRange o4 0 7); (KZRange p4 0 100);
                KZRange q2 0 12; KZRange q3 0 12; KZRange q4 0 12;
                KZRange n1 0 (2^32); KZRange n2 0 (2^32); KZRange n3 0 (2^32); KZRange n4 0 (2^32);
                KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47);
                KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange (S4 + n4) 4096 (2^47);
                KZRange j 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 256) 40;
                KZDisj (SPV - 416) 160 S1 n1; KZDisj (SPV - 416) 160 S2 n2; KZDisj (SPV - 416) 160 S3 n3; KZDisj (SPV - 416) 160 S4 n4;
                KZDisj (SPV - 256) 40 S1 n1; KZDisj (SPV - 256) 40 S2 n2; KZDisj (SPV - 256) 40 S3 n3; KZDisj (SPV - 256) 40 S4 n4;
                KZDisj (SPV - 416) 160 (SPV - 256) 40]
               [(S1, n1); (S2, n2); (S3, n3); (S4, n4); (SPV - 416, 160); (SPV - 256, 40)]
         |
         (* [comment removed for export] *)
           kx_autoLx [0x22e10; 0x232bc] 200%nat
               [(KZRange o1 8 (2^32)); (KZRange (n1 - o1) 8 (2^32)); (KZRange p1 0 56); (KZRange o2 0 7); (KZRange o2 0 7); (KZRange p2 0 100); (KZRange o3 0 7); (KZRange o3 0 7); (KZRange p3 0 100); (KZRange o4 8 (2^32)); (KZRange (n4 - o4) 8 (2^32)); (KZRange p4 0 44);
                KZRange q2 0 12; KZRange q3 0 12; KZRange q4 0 12;
                KZRange n1 0 (2^32); KZRange n2 0 (2^32); KZRange n3 0 (2^32); KZRange n4 0 (2^32);
                KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47);
                KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange (S4 + n4) 4096 (2^47);
                KZRange j 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 256) 40;
                KZDisj (SPV - 416) 160 S1 n1; KZDisj (SPV - 416) 160 S2 n2; KZDisj (SPV - 416) 160 S3 n3; KZDisj (SPV - 416) 160 S4 n4;
                KZDisj (SPV - 256) 40 S1 n1; KZDisj (SPV - 256) 40 S2 n2; KZDisj (SPV - 256) 40 S3 n3; KZDisj (SPV - 256) 40 S4 n4;
                KZDisj (SPV - 416) 160 (SPV - 256) 40]
               [(S1, n1); (S2, n2); (S3, n3); (S4, n4); (SPV - 416, 160); (SPV - 256, 40)]
         |
         (* [comment removed for export] *)
           kx_autoLx [0x22e10; 0x232bc] 200%nat
               [(KZRange o1 8 (2^32)); (KZRange (n1 - o1) 8 (2^32)); (KZRange p1 0 56); (KZRange o2 0 7); (KZRange o2 0 7); (KZRange p2 0 100); (KZRange o3 8 (2^32)); (KZRange (n3 - o3) 8 (2^32)); (KZRange p3 0 44); (KZRange o4 0 7); (KZRange o4 0 7); (KZRange p4 0 100);
                KZRange q2 0 12; KZRange q3 0 12; KZRange q4 0 12;
                KZRange n1 0 (2^32); KZRange n2 0 (2^32); KZRange n3 0 (2^32); KZRange n4 0 (2^32);
                KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47);
                KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange (S4 + n4) 4096 (2^47);
                KZRange j 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 256) 40;
                KZDisj (SPV - 416) 160 S1 n1; KZDisj (SPV - 416) 160 S2 n2; KZDisj (SPV - 416) 160 S3 n3; KZDisj (SPV - 416) 160 S4 n4;
                KZDisj (SPV - 256) 40 S1 n1; KZDisj (SPV - 256) 40 S2 n2; KZDisj (SPV - 256) 40 S3 n3; KZDisj (SPV - 256) 40 S4 n4;
                KZDisj (SPV - 416) 160 (SPV - 256) 40]
               [(S1, n1); (S2, n2); (S3, n3); (S4, n4); (SPV - 416, 160); (SPV - 256, 40)]
         |
         (* [comment removed for export] *)
           kx_autoLx [0x22e10; 0x232bc] 200%nat
               [(KZRange o1 8 (2^32)); (KZRange (n1 - o1) 8 (2^32)); (KZRange p1 0 56); (KZRange o2 0 7); (KZRange o2 0 7); (KZRange p2 0 100); (KZRange o3 8 (2^32)); (KZRange (n3 - o3) 8 (2^32)); (KZRange p3 0 44); (KZRange o4 8 (2^32)); (KZRange (n4 - o4) 8 (2^32)); (KZRange p4 0 44);
                KZRange q2 0 12; KZRange q3 0 12; KZRange q4 0 12;
                KZRange n1 0 (2^32); KZRange n2 0 (2^32); KZRange n3 0 (2^32); KZRange n4 0 (2^32);
                KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47);
                KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange (S4 + n4) 4096 (2^47);
                KZRange j 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 256) 40;
                KZDisj (SPV - 416) 160 S1 n1; KZDisj (SPV - 416) 160 S2 n2; KZDisj (SPV - 416) 160 S3 n3; KZDisj (SPV - 416) 160 S4 n4;
                KZDisj (SPV - 256) 40 S1 n1; KZDisj (SPV - 256) 40 S2 n2; KZDisj (SPV - 256) 40 S3 n3; KZDisj (SPV - 256) 40 S4 n4;
                KZDisj (SPV - 416) 160 (SPV - 256) 40]
               [(S1, n1); (S2, n2); (S3, n3); (S4, n4); (SPV - 416, 160); (SPV - 256, 40)]
         |
         (* [comment removed for export] *)
           kx_autoLx [0x22e10; 0x232bc] 200%nat
               [(KZRange o1 8 (2^32)); (KZRange (n1 - o1) 8 (2^32)); (KZRange p1 0 56); (KZRange o2 8 (2^32)); (KZRange (n2 - o2) 8 (2^32)); (KZRange p2 0 44); (KZRange o3 0 7); (KZRange o3 0 7); (KZRange p3 0 100); (KZRange o4 0 7); (KZRange o4 0 7); (KZRange p4 0 100);
                KZRange q2 0 12; KZRange q3 0 12; KZRange q4 0 12;
                KZRange n1 0 (2^32); KZRange n2 0 (2^32); KZRange n3 0 (2^32); KZRange n4 0 (2^32);
                KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47);
                KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange (S4 + n4) 4096 (2^47);
                KZRange j 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 256) 40;
                KZDisj (SPV - 416) 160 S1 n1; KZDisj (SPV - 416) 160 S2 n2; KZDisj (SPV - 416) 160 S3 n3; KZDisj (SPV - 416) 160 S4 n4;
                KZDisj (SPV - 256) 40 S1 n1; KZDisj (SPV - 256) 40 S2 n2; KZDisj (SPV - 256) 40 S3 n3; KZDisj (SPV - 256) 40 S4 n4;
                KZDisj (SPV - 416) 160 (SPV - 256) 40]
               [(S1, n1); (S2, n2); (S3, n3); (S4, n4); (SPV - 416, 160); (SPV - 256, 40)]
         |
         (* [comment removed for export] *)
           kx_autoLx [0x22e10; 0x232bc] 200%nat
               [(KZRange o1 8 (2^32)); (KZRange (n1 - o1) 8 (2^32)); (KZRange p1 0 56); (KZRange o2 8 (2^32)); (KZRange (n2 - o2) 8 (2^32)); (KZRange p2 0 44); (KZRange o3 0 7); (KZRange o3 0 7); (KZRange p3 0 100); (KZRange o4 8 (2^32)); (KZRange (n4 - o4) 8 (2^32)); (KZRange p4 0 44);
                KZRange q2 0 12; KZRange q3 0 12; KZRange q4 0 12;
                KZRange n1 0 (2^32); KZRange n2 0 (2^32); KZRange n3 0 (2^32); KZRange n4 0 (2^32);
                KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47);
                KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange (S4 + n4) 4096 (2^47);
                KZRange j 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 256) 40;
                KZDisj (SPV - 416) 160 S1 n1; KZDisj (SPV - 416) 160 S2 n2; KZDisj (SPV - 416) 160 S3 n3; KZDisj (SPV - 416) 160 S4 n4;
                KZDisj (SPV - 256) 40 S1 n1; KZDisj (SPV - 256) 40 S2 n2; KZDisj (SPV - 256) 40 S3 n3; KZDisj (SPV - 256) 40 S4 n4;
                KZDisj (SPV - 416) 160 (SPV - 256) 40]
               [(S1, n1); (S2, n2); (S3, n3); (S4, n4); (SPV - 416, 160); (SPV - 256, 40)]
         |
         (* [comment removed for export] *)
           kx_autoLx [0x22e10; 0x232bc] 200%nat
               [(KZRange o1 8 (2^32)); (KZRange (n1 - o1) 8 (2^32)); (KZRange p1 0 56); (KZRange o2 8 (2^32)); (KZRange (n2 - o2) 8 (2^32)); (KZRange p2 0 44); (KZRange o3 8 (2^32)); (KZRange (n3 - o3) 8 (2^32)); (KZRange p3 0 44); (KZRange o4 0 7); (KZRange o4 0 7); (KZRange p4 0 100);
                KZRange q2 0 12; KZRange q3 0 12; KZRange q4 0 12;
                KZRange n1 0 (2^32); KZRange n2 0 (2^32); KZRange n3 0 (2^32); KZRange n4 0 (2^32);
                KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47);
                KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange (S4 + n4) 4096 (2^47);
                KZRange j 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 256) 40;
                KZDisj (SPV - 416) 160 S1 n1; KZDisj (SPV - 416) 160 S2 n2; KZDisj (SPV - 416) 160 S3 n3; KZDisj (SPV - 416) 160 S4 n4;
                KZDisj (SPV - 256) 40 S1 n1; KZDisj (SPV - 256) 40 S2 n2; KZDisj (SPV - 256) 40 S3 n3; KZDisj (SPV - 256) 40 S4 n4;
                KZDisj (SPV - 416) 160 (SPV - 256) 40]
               [(S1, n1); (S2, n2); (S3, n3); (S4, n4); (SPV - 416, 160); (SPV - 256, 40)]
         |
         (* [comment removed for export] *)
           kx_autoLx [0x22e10; 0x232bc] 200%nat
               [(KZRange o1 8 (2^32)); (KZRange (n1 - o1) 8 (2^32)); (KZRange p1 0 56); (KZRange o2 8 (2^32)); (KZRange (n2 - o2) 8 (2^32)); (KZRange p2 0 44); (KZRange o3 8 (2^32)); (KZRange (n3 - o3) 8 (2^32)); (KZRange p3 0 44); (KZRange o4 8 (2^32)); (KZRange (n4 - o4) 8 (2^32)); (KZRange p4 0 44);
                KZRange q2 0 12; KZRange q3 0 12; KZRange q4 0 12;
                KZRange n1 0 (2^32); KZRange n2 0 (2^32); KZRange n3 0 (2^32); KZRange n4 0 (2^32);
                KZRange S1 4096 (2^47); KZRange (S1 + n1) 4096 (2^47); KZRange S2 4096 (2^47); KZRange (S2 + n2) 4096 (2^47);
                KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange S4 4096 (2^47); KZRange (S4 + n4) 4096 (2^47);
                KZRange j 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange g2 0 (2^32); KZRange g3 0 (2^32);
                KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZWr (SPV - 416) 160; KZWr (SPV - 256) 40;
                KZDisj (SPV - 416) 160 S1 n1; KZDisj (SPV - 416) 160 S2 n2; KZDisj (SPV - 416) 160 S3 n3; KZDisj (SPV - 416) 160 S4 n4;
                KZDisj (SPV - 256) 40 S1 n1; KZDisj (SPV - 256) 40 S2 n2; KZDisj (SPV - 256) 40 S3 n3; KZDisj (SPV - 256) 40 S4 n4;
                KZDisj (SPV - 416) 160 (SPV - 256) 40]
               [(S1, n1); (S2, n2); (S3, n3); (S4, n4); (SPV - 416, 160); (SPV - 256, 40)]
         ].
    all: kx_mem; kx_land_ranges; kx_strip_mod; unfold x41_hide in *.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 142864) _ _ _ _) => eapply KH; try eassumption; try (unfold HINV; lia); try lia
         | |- evt _ _ (MS _ _ (Z_to_bv 64 144060) _ _ _ _) =>
             eapply KE; try eassumption; try (unfold RZ_huf_dx41.SINV; lia); try lia
         end.
  Qed.

  Lemma x41_r : forall mm j j4 e1 g2 g3 S1 n1 b1 o1 p1 S2 n2 b2 o2 p2 q2 S3 n3 b3 o3 p3 q3 S4 n4 b4 o4 p4 q4 (k3 k4 b4w p4w : word) pad
      (x1 x13 x14 x17 x18 x19 x26 x27 x28 x29 x31 : word)
      (w0 w3 w5 w6 w7 w8 w9 w10 w12 w19 : word),
    mem_inv psegs mm ->
    FRA mm w0 (Z_to_bv 64 S1) (Z_to_bv 64 S2) w3 (Z_to_bv 64 (DST + e1)) w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (S4 + 8)) w12 (Z_to_bv 64 g3) (Z_to_bv 64 g2) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) w19 ->
    BD4 mm k4 b4w pad p4w (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    DINV1 o1 n1 p1 -> DINV2 o2 n2 p2 q2 -> DINV2 o3 n3 p3 q3 -> DINV2 o4 n4 p4 q4 ->
    0 <= j <= dcap -> 0 <= j4 <= dcap -> 0 <= e1 <= dcap -> 0 <= g2 <= dcap -> 0 <= g3 <= dcap ->
    (forall mm' T2 P1 P2 P3 P4 c1' c2' c3' c4' (k3' k4' b4w' p4w' y1 y8 y9 y11 y12 y14 y19 y26 y27 y28 y29 y31 : word),
        munch WFR mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' ->
        FRA mm' w0 (Z_to_bv 64 S1) (Z_to_bv 64 S2) w3 (Z_to_bv 64 (DST + e1)) w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (S4 + 8)) w12 (Z_to_bv 64 g3) (Z_to_bv 64 g2) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c2') ->
        BD4 mm' k4' b4w' pad p4w' (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        HINV (P1 - S1) n1 c1' -> HINV (P2 - S2) n2 c2' -> HINV (P3 - S3) n3 c3' -> HINV (P4 - S4) n4 c4' ->
        T2 = DST + (j + 4) -> j4 + 4 < dcap - 3 ->
        evt psegs POST (ST 0x22e10 mm' y1 (Z_to_bv 64 (DST + j)) k4' (Z_to_bv 64 T2) y8 y9 (Z_to_bv 64 P4) y11 y12 (Z_to_bv 64 c1') y14 k3' (Z_to_bv 64 DST) x17 x18 y19 (Z_to_bv 64 DST) (Z_to_bv 64 P2) (Z_to_bv 64 c3') (Z_to_bv 64 P3) (Z_to_bv 64 P1) (Z_to_bv 64 e1) y26 y27 y28 y29 (Z_to_bv 64 c4') y31)) ->
    (forall mm' T0 A2 A5 A7 P1 P2 P3 P4 c1' c2' c3' c4' (k3' k4' y1 y6 y7 y11 y14 y16 y19 y26 y27 y28 y29 y30 y31 : word),
        munch WFR mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' ->
        FRA mm' w0 (Z_to_bv 64 S1) (Z_to_bv 64 S2) w3 (Z_to_bv 64 (DST + e1)) w5 k3' w7 w8 w9 w10 (Z_to_bv 64 (S4 + 8)) w12 (Z_to_bv 64 g3) (Z_to_bv 64 g2) (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c2') ->
        BD4 mm' k4' (Z_to_bv 64 c4') pad (Z_to_bv 64 P4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        SINV (P1 - S1) n1 c1' -> SINV (P2 - S2) n2 c2' -> SINV (P3 - S3) n3 c3' -> SINV (P4 - S4) n4 c4' ->
        0 <= c1' < 2^64 -> 0 <= c2' < 2^64 -> 0 <= c3' < 2^64 -> 0 <= c4' < 2^32 ->
        T0 = DST + (j + 4) -> A7 = DST + (j + 4 + e1) -> A5 = DST + (j + 4 + g2) -> A2 = DST + (j + 4 + g3) ->
        evt psegs POST (ST 0x232bc mm' y1 (Z_to_bv 64 T0) y6 y7 (Z_to_bv 64 S1) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + e1)) y11 (Z_to_bv 64 A2) (Z_to_bv 64 c1') y14 (Z_to_bv 64 A5) y16 (Z_to_bv 64 A7) x18 y19 (Z_to_bv 64 DST) (Z_to_bv 64 P2) (Z_to_bv 64 c3') (Z_to_bv 64 P3) (Z_to_bv 64 P1) (Z_to_bv 64 e1) y26 y27 y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x23024 mm x1 (Z_to_bv 64 (DST + j)) k4 (Z_to_bv 64 (DST + j4)) (Z_to_bv 64 p3) (Z_to_bv 64 q3) (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 q4) (Z_to_bv 64 p1) x13 x14 k3 (Z_to_bv 64 DST) x17 x18 x19 (Z_to_bv 64 p2) (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 q2) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 e1) x26 x27 x28 x29 (Z_to_bv 64 p4) x31).
  Proof.
    intros mm j j4 e1 g2 g3 S1 n1 b1 o1 p1 S2 n2 b2 o2 p2 q2 S3 n3 b3 o3 p3 q3 S4 n4 b4 o4 p4 q4 k3 k4 b4w p4w pad
      x1 x13 x14 x17 x18 x19 x26 x27 x28 x29 x31
      w0 w3 w5 w6 w7 w8 w9 w10 w12 w19 MI FA BD SB1 SB2 SB3 SB4 HD1 HD2 HD3 HD4 HJ HJ4 HE1 HG2 HG3 KH KE.
    destruct (Z_lt_le_dec o1 8) as [O1|O1].
    - eapply (x41_r_lo ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX mm j j4 e1 g2 g3 S1 n1 b1 o1 p1 S2 n2 b2 o2 p2 q2 S3 n3 b3 o3 p3 q3 S4 n4 b4 o4 p4 q4); eassumption.
    - eapply (x41_r_hi mm j j4 e1 g2 g3 S1 n1 b1 o1 p1 S2 n2 b2 o2 p2 q2 S3 n3 b3 o3 p3 q3 S4 n4 b4 o4 p4 q4); eassumption.
  Qed.

End DX41H.
