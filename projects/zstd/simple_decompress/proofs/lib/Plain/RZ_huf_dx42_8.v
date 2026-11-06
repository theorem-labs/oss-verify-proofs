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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_0b RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx42_7_0000 RZ_huf_dx42_7_0001 RZ_huf_dx42_7_0010 RZ_huf_dx42_7_0011 RZ_huf_dx42_7_0100 RZ_huf_dx42_7_0101 RZ_huf_dx42_7_0110 RZ_huf_dx42_7_0111 RZ_huf_dx42_7_1000 RZ_huf_dx42_7_1001 RZ_huf_dx42_7_1010 RZ_huf_dx42_7_1011 RZ_huf_dx42_7_1100 RZ_huf_dx42_7_1101 RZ_huf_dx42_7_1110 RZ_huf_dx42_7_1111.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_8.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (SPV DST dcap DT lo : Z) (dtb : list byte).
  Hypothesis CTX : x41_ctx SPV DST dcap DT lo dtb.
  Variables (tl rsv : Z).
  Hypothesis TL : 1 <= tl <= 12.
  Hypothesis RSV : 0 <= rsv <= 255.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis DJ3 : DT + 16388 <= lo \/ SPV <= DT.
  Hypothesis NBOK : huf_nb_ok true dtb tl.

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 432 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 416, SPV - 216)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -416)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 :=
    (rw_cells psegs mm (SPV + -416) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD4 := [(DST, DST + dcap); (SPV - 256, SPV - 216)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells psegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation EINV := (RZ_huf_dx41.EINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation HINV := RZ_huf_dx41g.HINV.
  Notation x41_hide := RZ_huf_dx41g.x41_hide.
  Notation x42_tbl := (RZ_huf_dx42_0.x42_tbl SPV DST dcap DT lo dtb CTX tl X2OK).
  Notation x42_tbl_nb := (RZ_huf_dx42_0b.x42_tbl_nb SPV DST dcap DT lo dtb CTX tl TL NBOK).
  (* [comment removed for export] *)
  Ltac x42_hide_or := repeat match goal with H : ?A \/ ?B |- _ => change (RZ_huf_dx41g.x41_hide (A \/ B)) in H end.
  Ltac x42_or_goal :=
    match goal with
    | H : _ \/ _ |- _ \/ _ =>
        solve [ let H' := fresh "HD" in pose proof H as H'; destruct H' as [H'|H']; x42_hide_or; first [left; lia | right; lia] ]
    end.
  #[local] Ltac kx_lia ::= kx_bv_ranges; repeat split; (lazymatch goal with |- _ \/ _ => x42_or_goal | |- _ => x42_hide_or; lia end).

  Lemma x42_it : forall mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 (k1 k2 k3 k4 b4w : word) pad
      (x1 x7 x11 x13 x15 x17 x19 x20 x21 x22 x25 x28 x30 x31 : word)
      (w0 w1 w2 w3 w4 w5 w6 w7 w10 w12 w13 : word),
    mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap - 7)) w10 (Z_to_bv 64 (DT + 4)) w12 w13 (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c1) (Z_to_bv 64 (S3 + o3)) k2 ->
    BD4 mm k4 b4w pad (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 -> HINV o4 n4 c4 ->
    0 <= j1 -> j1 + 8 <= dcap -> 0 <= j2 -> j2 + 8 <= dcap -> 0 <= j3 -> j3 + 8 <= dcap -> 0 <= j4 -> j4 + 8 <= dcap -> sh = 64 - tl ->
    (forall mm' T1 T2 T3 T4 P1 P2 P3 P4 c1' c2' c3' c4' (k1' k2' k3' k4' b4w' w12' y1 y7 y11 y13 y15 y17 y19 y20 y21 y22 y25 y28 y30 y31 : word),
        munch WDF mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap - 7)) w10 (Z_to_bv 64 (DT + 4)) w12' w13 (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c1') (Z_to_bv 64 P3) k2' ->
        BD4 mm' k4' b4w' pad (Z_to_bv 64 P4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        HINV (P1 - S1) n1 c1' -> HINV (P2 - S2) n2 c2' -> HINV (P3 - S3) n3 c3' -> HINV (P4 - S4) n4 c4' ->
        j1 + 4 <= T1 - DST <= j1 + 8 -> j2 + 4 <= T2 - DST <= j2 + 8 -> j3 + 4 <= T3 - DST <= j3 + 8 -> j4 + 4 <= T4 - DST <= j4 + 8 ->
        T4 - DST + 8 <= dcap ->
        evt psegs POST (ST 0x1fc8c mm' y1 (Z_to_bv 64 T2) k4' y7 k3' (Z_to_bv 64 T1) (Z_to_bv 64 P4) y11 (Z_to_bv 64 T4) y13 (Z_to_bv 64 T3) y15 (Z_to_bv 64 sh) y17 (Z_to_bv 64 c2') y19 y20 y21 y22 k1' (Z_to_bv 64 P2) y25 (Z_to_bv 64 P1) (Z_to_bv 64 c3') y28 (Z_to_bv 64 c4') y30 y31)) ->
    (forall mm' T1 T2 T3 T4 P1 P2 P3 P4 c1' c2' c3' c4' (k1' k2' k3' k4' w12' y1 y6 y7 y10 y11 y13 y19 y21 y22 y28 y29 y30 y31 : word),
        munch WDF mm mm' -> wmono psegs mm mm' -> mem_inv psegs mm' -> stk psegs mm' DST (DST + dcap) -> bytes_at psegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (DST + dcap - 7)) w10 (Z_to_bv 64 (DT + 4)) w12' w13 (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c1') (Z_to_bv 64 P3) k2' ->
        BD4 mm' k4' (Z_to_bv 64 c4') pad (Z_to_bv 64 P4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        (c1' <= 64 -> SINV (P1 - S1) n1 c1') -> (c2' <= 64 -> SINV (P2 - S2) n2 c2') -> (c3' <= 64 -> SINV (P3 - S3) n3 c3') ->
        (c4' <= 64 -> SINV (P4 - S4) n4 c4') ->
        0 <= c1' < 2^31 -> 0 <= c2' < 2^31 -> 0 <= c3' < 2^31 -> 0 <= c4' < 2^31 ->
        j1 + 4 <= T1 - DST <= j1 + 8 -> j2 + 4 <= T2 - DST <= j2 + 8 -> j3 + 4 <= T3 - DST <= j3 + 8 -> j4 + 4 <= T4 - DST <= j4 + 8 ->
        evt psegs POST (ST 0x2021c mm' y1 (Z_to_bv 64 T2) y6 y7 k3' (Z_to_bv 64 T1) y10 y11 (Z_to_bv 64 T4) y13 (Z_to_bv 64 T3) w5 (Z_to_bv 64 sh) w4 (Z_to_bv 64 c2') y19 w2 y21 y22 k1' (Z_to_bv 64 P2) w1 (Z_to_bv 64 P1) (Z_to_bv 64 c3') y28 y29 y30 y31)) ->
    evt psegs POST (ST 0x1fc8c mm x1 (Z_to_bv 64 (DST + j2)) k4 x7 k3 (Z_to_bv 64 (DST + j1)) (Z_to_bv 64 (S4 + o4)) x11 (Z_to_bv 64 (DST + j4)) x13 (Z_to_bv 64 (DST + j3)) x15 (Z_to_bv 64 sh) x17 (Z_to_bv 64 c2) x19 x20 x21 x22 k1 (Z_to_bv 64 (S2 + o2)) x25 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 c3) x28 (Z_to_bv 64 c4) x30 x31).
  Proof using All.
    intros mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 k1 k2 k3 k4 b4w pad
      x1 x7 x11 x13 x15 x17 x19 x20 x21 x22 x25 x28 x30 x31
      w0 w1 w2 w3 w4 w5 w6 w7 w10 w12 w13 MI OUT DTB FA BD SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 HJ1 HR1 HJ2 HR2 HJ3 HR3 HJ4 HR4 HSH KH KE.
    destruct (Z_lt_le_dec o1 8) as [O1|O1]; destruct (Z_lt_le_dec o2 8) as [O2|O2]; destruct (Z_lt_le_dec o3 8) as [O3|O3];
      destruct (Z_lt_le_dec o4 8) as [O4|O4].
    - eapply (RZ_huf_dx42_7_0000.x42_it_0000 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_0001.x42_it_0001 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_0010.x42_it_0010 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_0011.x42_it_0011 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_0100.x42_it_0100 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_0101.x42_it_0101 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_0110.x42_it_0110 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_0111.x42_it_0111 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_1000.x42_it_1000 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_1001.x42_it_1001 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_1010.x42_it_1010 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_1011.x42_it_1011 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_1100.x42_it_1100 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_1101.x42_it_1101 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_1110.x42_it_1110 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
    - eapply (RZ_huf_dx42_7_1111.x42_it_1111 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4); eassumption.
  Qed.

End DX42_8.
