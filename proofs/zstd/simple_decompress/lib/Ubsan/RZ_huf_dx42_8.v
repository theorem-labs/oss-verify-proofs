(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx42_0 RZ_huf_dx42_0b RZ_huf_dx41f RZ_huf_dx41g RZ_huf_dx42_7_0000 RZ_huf_dx42_7_0001 RZ_huf_dx42_7_0010 RZ_huf_dx42_7_0011 RZ_huf_dx42_7_0100 RZ_huf_dx42_7_0101 RZ_huf_dx42_7_0110 RZ_huf_dx42_7_0111 RZ_huf_dx42_7_1000 RZ_huf_dx42_7_1001 RZ_huf_dx42_7_1010 RZ_huf_dx42_7_1011 RZ_huf_dx42_7_1100 RZ_huf_dx42_7_1101 RZ_huf_dx42_7_1110 RZ_huf_dx42_7_1111.
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

  Notation POST := (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 912 [] m0 huf_noQ).
  Notation WD := [(DST, DST + dcap)].
  Notation WDF := [(DST, DST + dcap); (SPV - 912, SPV - 616)].
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -912)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FRA mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 :=
    (rw_cells usegs mm (SPV + -912) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                                     C8 w14; C8 w15; C8 w16]).
  Notation SINV := RZ_huf_dx41.SINV.
  Notation WD4 := [(DST, DST + dcap); (SPV - 776, SPV - 736)].
  Notation BD4 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -776) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD3 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -736) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD2 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -696) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation BD1 mm c b pad p st lm :=
    (rw_cells usegs mm (SPV + -656) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
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

  Lemma x42_it : forall mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x7 x8 x10 x12 x13 x14 x21 x22 x24 x26 x30 : word)
      (w0 w1 w2 w3 w8 w12 w13 : word),
    mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 w2 w3 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (DST + dcap - 7)) w8 k4 k2 (Z_to_bv 64 (S2 + o2)) w12 w13 k1 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    HINV o1 n1 c1 -> HINV o2 n2 c2 -> HINV o3 n3 c3 -> HINV o4 n4 c4 ->
    0 <= j1 -> j1 + 8 <= dcap -> 0 <= j2 -> j2 + 8 <= dcap -> 0 <= j3 -> j3 + 8 <= dcap -> 0 <= j4 -> j4 + 8 <= dcap -> sh = 64 - tl ->
    (forall mm' T1 T2 T3 T4 P1 P2 P3 P4 c1' c2' c3' c4' (k1' k2' k3' k4' w8' y7 y8 y10 y12 y13 y14 y21 y22 y24 y26 y30 : word),
        munch WDF mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (DST + dcap - 7)) w8' k4' k2' (Z_to_bv 64 P2) w12 w13 k1' (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) ->
        BD1 mm' k1' (Z_to_bv 64 c1') pad1 (Z_to_bv 64 P1) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
        BD2 mm' k2' (Z_to_bv 64 c2') pad2 (Z_to_bv 64 P2) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
        BD3 mm' k3' (Z_to_bv 64 c3') pad3 (Z_to_bv 64 P3) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
        BD4 mm' k4' (Z_to_bv 64 c4') pad4 (Z_to_bv 64 P4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        HINV (P1 - S1) n1 c1' -> HINV (P2 - S2) n2 c2' -> HINV (P3 - S3) n3 c3' -> HINV (P4 - S4) n4 c4' ->
        j1 + 4 <= T1 - DST <= j1 + 8 -> j2 + 4 <= T2 - DST <= j2 + 8 -> j3 + 4 <= T3 - DST <= j3 + 8 -> j4 + 4 <= T4 - DST <= j4 + 8 ->
        T4 - DST + 8 <= dcap ->
        evt usegs POST (ST 0x26000 mm' (Z_to_bv 64 c2') (Z_to_bv 64 P3) (Z_to_bv 64 (DT + 4)) y7 y8 (Z_to_bv 64 c1') y10 (Z_to_bv 64 T1) y12 y13 y14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 T4) k3' (Z_to_bv 64 T3) y21 y22 (Z_to_bv 64 c3') y24 (Z_to_bv 64 c4') y26 (Z_to_bv 64 T2) (Z_to_bv 64 P4) (Z_to_bv 64 P1) y30 (Z_to_bv 64 (DST + dcap)))) ->
    (forall mm' T1 T2 T3 T4 P1 P2 P3 P4 c1' c2' c3' c4' (k1' k2' k3' k4' w8' y1 y5 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y28 y29 y30 : word),
        munch WDF mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' -> stk usegs mm' DST (DST + dcap) -> bytes_at usegs mm' DT dtb ->
        FRA mm' w0 w1 w2 w3 (Z_to_bv 64 (S4 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (DST + dcap - 7)) w8' k4' k2' (Z_to_bv 64 P2) w12 w13 k1' (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DT + 4)) ->
        BD1 mm' k1' (Z_to_bv 64 c1') pad1 (Z_to_bv 64 P1) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
        BD2 mm' k2' (Z_to_bv 64 c2') pad2 (Z_to_bv 64 P2) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
        BD3 mm' k3' (Z_to_bv 64 c3') pad3 (Z_to_bv 64 P3) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
        BD4 mm' k4' (Z_to_bv 64 c4') pad4 (Z_to_bv 64 P4) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
        (c1' <= 64 -> SINV (P1 - S1) n1 c1') -> (c2' <= 64 -> SINV (P2 - S2) n2 c2') -> (c3' <= 64 -> SINV (P3 - S3) n3 c3') ->
        (c4' <= 64 -> SINV (P4 - S4) n4 c4') ->
        0 <= c1' < 2^31 -> 0 <= c2' < 2^31 -> 0 <= c3' < 2^31 -> 0 <= c4' < 2^31 ->
        j1 + 4 <= T1 - DST <= j1 + 8 -> j2 + 4 <= T2 - DST <= j2 + 8 -> j3 + 4 <= T3 - DST <= j3 + 8 -> j4 + 4 <= T4 - DST <= j4 + 8 ->
        evt usegs POST (ST 0x26928 mm' y1 y5 (Z_to_bv 64 (DT + 4)) y7 y8 y9 y10 (Z_to_bv 64 T1) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 T4) y19 (Z_to_bv 64 T3) y21 y22 y23 y24 y25 w3 (Z_to_bv 64 T2) y28 y29 y30 (Z_to_bv 64 (DST + dcap)))) ->
    evt usegs POST (ST 0x26000 mm (Z_to_bv 64 c2) (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 (DT + 4)) x7 x8 (Z_to_bv 64 c1) x10 (Z_to_bv 64 (DST + j1)) x12 x13 x14 (Z_to_bv 64 (2^61)) (Z_to_bv 64 sh) (Z_to_bv 64 (-1 * DT + -5)) (Z_to_bv 64 (DST + j4)) k3 (Z_to_bv 64 (DST + j3)) x21 x22 (Z_to_bv 64 c3) x24 (Z_to_bv 64 c4) x26 (Z_to_bv 64 (DST + j2)) (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 (S1 + o1)) x30 (Z_to_bv 64 (DST + dcap))).
  Proof using All.
    intros mm j1 j2 j3 j4 sh S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 k1 k2 k3 k4 pad1 pad2 pad3 pad4
      x7 x8 x10 x12 x13 x14 x21 x22 x24 x26 x30
      w0 w1 w2 w3 w8 w12 w13 MI OUT DTB FA BS1 BS2 BS3 BS4 SB1 SB2 SB3 SB4 HI1 HI2 HI3 HI4 HJ1 HR1 HJ2 HR2 HJ3 HR3 HJ4 HR4 HSH KH KE.
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
