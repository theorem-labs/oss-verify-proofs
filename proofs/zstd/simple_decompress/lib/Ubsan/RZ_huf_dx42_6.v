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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx42_1f RZ_huf_dx42_2f RZ_huf_dx42_3f RZ_huf_dx42_4f RZ_huf_dx42_5.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DX42_6.
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

  Notation WDG := [(DST, DST + dcap); (SPV - 416, SPV - 256)].
  Notation X42P := (RZ_huf_dx42_5.X42P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation x42p_transport := (RZ_huf_dx42_5.x42p_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation sbuf_transport := (RZ_huf_dx42_5.x42_sbuf_transport SPV DST dcap DT lo dtb CTX).
  Notation x41_einv := (RZ_huf_dx41f.x41_einv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x42_end := (RZ_huf_dx42_5.x42_end ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_ret := (RZ_huf_dx42_5.x42_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_d1 := (RZ_huf_dx42_1f.x42_d1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_d2 := (RZ_huf_dx42_2f.x42_d2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_d3 := (RZ_huf_dx42_3f.x42_d3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).
  Notation x42_d4 := (RZ_huf_dx42_4f.x42_d4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK DJ3 NBOK).

  Ltac wdf_of MU := eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia.
  Notation x42_einv := (RZ_huf_dx42_5.x42_einv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Ltac c34_tr H MU WM :=
    let T := fresh "T" in
    pose proof (rw_cells_transport usegs _ _ _ _ _ H MU WM) as T; clear H; rename T into H;
    lazymatch type of H with
    | ?P -> _ =>
        let D := fresh "D" in
        assert (D : P) by (cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
        specialize (H D); clear D
    end.
  Ltac c34_side := first [apply munch_refl | apply wmono_refl | eassumption | lia].

  Lemma x42_c34 : forall mm rest j3 e3 j4 pe4 dl S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 (k3 k4 : word) pad3 pad4
      (q1 r1 p1 u1 v1 q2 r2 p2 u2 v2 : word) pd1 pd2
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x27 x28 x29 x30 : word)
      (w0 w1 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 (Z_to_bv 64 (DST + e3)) w3 w4 w5 w6 (Z_to_bv 64 (DST + pe4 - 7)) w8 w9 w10 w11 w12 w13 (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe4)) (Z_to_bv 64 (DT + 4)) ->
    BD1 mm q1 r1 pd1 p1 u1 v1 -> BD2 mm q2 r2 pd2 p2 u2 v2 ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 -> (c3 <= 64 -> SINV o3 n3 c3) -> (c4 <= 64 -> SINV o4 n4 c4) ->
    0 <= c3 < 2^31 -> 0 <= c4 < 2^31 -> 0 <= j3 <= e3 -> e3 <= dcap -> 0 <= j4 <= pe4 -> pe4 <= dcap -> dl = tl + 256 * rsv ->
    evt usegs POST (ST 0x27de4 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j4)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j3)) x21 x22 x23 x24 (Z_to_bv 64 dl) (Z_to_bv 64 dcap) x27 x28 x29 x30 (Z_to_bv 64 (DST + pe4))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest j3 e3 j4 pe4 dl S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 k3 k4 pad3 pad4 q1 r1 p1 u1 v1 q2 r2 p2 u2 v2 pd1 pd2
      x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x27 x28 x29 x30 w0 w1 w3 w4 w5 w6 w8 w9 w10 w11 w12 w13
      PV MI OUT DTB FA B1 B2 B3 B4 SB3 SB4 HS3 HS4 HC3 HC4 HJ3 HE3 HJ4 HPE4 HDL.
    pose proof PV as (_ & _ & _ & _ & _ & _ & AL).
    pose proof SB3 as (SB3b & SL3 & R30 & R31 & R32 & D31 & D32).
    eapply (x42_d3 mm mm j3 e3 pe4 o3 S3 n3 b3 dl c3 k3 pad3); try c34_side.
    intros mm' y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y28 y29 y30 c' b' p' MU' WM' MI' OUT' DTB' FA' B3'.
    assert (MUF : munch WDF mm mm') by wdf_of MU'.
    pose proof (x42p_transport mm mm' rest PV MUF WM') as PV'.
    pose proof (sbuf_transport mm mm' S4 n4 b4 SB4 MUF) as (SB4b & SL4 & R40 & R41 & R42 & D41 & D42).
    c34_tr B1 MU' WM'. c34_tr B2 MU' WM'. c34_tr B4 MU' WM'.
    eapply (x42_d4 mm' mm' j4 pe4 o4 S4 n4 b4 dl c4 k4 pad4); try c34_side.
    intros mm'' z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z27 z28 z29 z30 z31 c'' b'' p''
      MU'' WM'' MI'' OUT'' DTB'' FA'' B4''.
    assert (MUF' : munch WDF mm' mm'') by wdf_of MU''.
    pose proof (x42p_transport mm' mm'' rest PV' MUF' WM'') as PV''.
    c34_tr B1 MU'' WM''. c34_tr B2 MU'' WM''. c34_tr B3' MU'' WM''.
    eapply (x42_end mm''); [eapply (x42_einv mm'' rest); eassumption | eassumption ..].
  Qed.

  Lemma x42_c234 : forall mm rest j2 e2 j3 e3 j4 pe4 dl S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 (k2 k3 k4 : word) pad2 pad3 pad4
      (q1 r1 p1 u1 v1 : word) pd1
      (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 : word)
      (w0 w1 w3 w4 w5 w6 w8 w9 w10 w11 w12 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 w1 (Z_to_bv 64 (DST + e3)) w3 w4 w5 w6 (Z_to_bv 64 (DST + pe4 - 7)) w8 w9 w10 w11 w12 (Z_to_bv 64 (DST + e2)) (Z_to_bv 64 tl) (Z_to_bv 64 (DST + pe4)) (Z_to_bv 64 (DT + 4)) ->
    BD1 mm q1 r1 pd1 p1 u1 v1 ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    (c2 <= 64 -> SINV o2 n2 c2) -> (c3 <= 64 -> SINV o3 n3 c3) -> (c4 <= 64 -> SINV o4 n4 c4) ->
    0 <= c2 < 2^31 -> 0 <= c3 < 2^31 -> 0 <= c4 < 2^31 ->
    0 <= j2 <= e2 -> e2 <= dcap -> 0 <= j3 <= e3 -> e3 <= dcap -> 0 <= j4 <= pe4 -> pe4 <= dcap -> dl = tl + 256 * rsv ->
    evt usegs POST (ST 0x273a4 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j4)) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (DST + j3)) x21 x22 x23 x24 (Z_to_bv 64 dl) (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + j2)) x28 x29 x30 (Z_to_bv 64 (DST + pe4))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest j2 e2 j3 e3 j4 pe4 dl S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 k2 k3 k4 pad2 pad3 pad4 q1 r1 p1 u1 v1 pd1
      x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 w0 w1 w3 w4 w5 w6 w8 w9 w10 w11 w12
      PV MI OUT DTB FA B1 B2 B3 B4 SB2 SB3 SB4 HS2 HS3 HS4 HC2 HC3 HC4 HJ2 HE2 HJ3 HE3 HJ4 HPE4 HDL.
    pose proof PV as (_ & _ & _ & _ & _ & _ & AL).
    pose proof SB2 as (SB2b & SL2 & R20 & R21 & R22 & D21 & D22).
    eapply (x42_d2 mm mm j2 e2 pe4 o2 S2 n2 b2 dl c2 k2 pad2); try c34_side.
    intros mm' y1 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y24 y27 c' b' p' MU' WM' MI' OUT' DTB' FA' B2'.
    assert (MUF : munch WDF mm mm') by wdf_of MU'.
    pose proof (x42p_transport mm mm' rest PV MUF WM') as PV'.
    pose proof (sbuf_transport mm mm' S3 n3 b3 SB3 MUF) as SB3'.
    pose proof (sbuf_transport mm mm' S4 n4 b4 SB4 MUF) as SB4'.
    c34_tr B1 MU' WM'. c34_tr B3 MU' WM'. c34_tr B4 MU' WM'.
    eapply (x42_c34 mm' rest j3 e3 j4 pe4 dl S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 k3 k4 pad3 pad4); try c34_side.
  Qed.

  Lemma x42_c1234 : forall mm rest j1 e1 j2 e2 j3 e3 j4 pe4 dl S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4
      (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x1 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x28 x29 x30 : word)
      (w0 w3 w4 w5 w6 w8 w9 w10 w11 w14 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + e3)) w3 w4 w5 w6 (Z_to_bv 64 (DST + pe4 - 7)) w8 w9 w10 w11 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + e2)) w14 (Z_to_bv 64 (DST + pe4)) (Z_to_bv 64 (DT + 4)) ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    (c1 <= 64 -> SINV o1 n1 c1) -> (c2 <= 64 -> SINV o2 n2 c2) -> (c3 <= 64 -> SINV o3 n3 c3) -> (c4 <= 64 -> SINV o4 n4 c4) ->
    0 <= c1 < 2^31 -> 0 <= c2 < 2^31 -> 0 <= c3 < 2^31 -> 0 <= c4 < 2^31 ->
    0 <= j1 <= e1 -> e1 <= dcap -> 0 <= j2 <= e2 -> e2 <= dcap -> 0 <= j3 <= e3 -> e3 <= dcap -> 0 <= j4 <= pe4 -> pe4 <= dcap ->
    dl = tl + 256 * rsv ->
    evt usegs POST (ST 0x26948 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 (Z_to_bv 64 (DST + j1)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j4)) x19 (Z_to_bv 64 (DST + j3)) x21 (Z_to_bv 64 (DST + e1)) x23 x24 x25 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + j2)) x28 x29 x30 (Z_to_bv 64 (DST + pe4))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest j1 e1 j2 e2 j3 e3 j4 pe4 dl S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 k1 k2 k3 k4 pad1 pad2 pad3 pad4
      x1 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x28 x29 x30 w0 w3 w4 w5 w6 w8 w9 w10 w11 w14
      PV MI OUT DTB FA B1 B2 B3 B4 SB1 SB2 SB3 SB4 HS1 HS2 HS3 HS4 HC1 HC2 HC3 HC4 HJ1 HE1 HJ2 HE2 HJ3 HE3 HJ4 HPE4 HDL.
    pose proof PV as (_ & _ & _ & _ & _ & _ & AL).
    pose proof SB1 as (SB1b & SL1 & R10 & R11 & R12 & D11 & D12).
    eapply (x42_d1 mm mm j1 e1 pe4 o1 S1 n1 b1 dl c1 k1 pad1); try c34_side.
    intros mm' y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y23 y24 y28 y29 y30 c' b' p' MU' WM' MI' OUT' DTB' FA' B1'.
    assert (MUF : munch WDF mm mm') by wdf_of MU'.
    pose proof (x42p_transport mm mm' rest PV MUF WM') as PV'.
    pose proof (sbuf_transport mm mm' S2 n2 b2 SB2 MUF) as SB2'.
    pose proof (sbuf_transport mm mm' S3 n3 b3 SB3 MUF) as SB3'.
    pose proof (sbuf_transport mm mm' S4 n4 b4 SB4 MUF) as SB4'.
    c34_tr B2 MU' WM'. c34_tr B3 MU' WM'. c34_tr B4 MU' WM'.
    eapply (x42_c234 mm' rest j2 e2 j3 e3 j4 pe4 dl S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 k2 k3 k4 pad2 pad3 pad4); try c34_side.
  Qed.

  (* [comment removed for export] *)
  Lemma x42_c0 : forall mm rest j1 j2 j3 j4 e1 e2 e3 pe4 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl (k1 k2 k3 k4 : word) pad1 pad2 pad3 pad4
      (x1 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x28 x29 x30 : word)
      (w0 w3 w4 w5 w6 w8 w9 w10 w11 w14 : word),
    X42P mm rest -> mem_inv usegs mm -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm DT dtb ->
    FRA mm w0 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + e3)) w3 w4 w5 w6 (Z_to_bv 64 (DST + pe4 - 7)) w8 w9 w10 w11 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 (DST + e2)) w14 (Z_to_bv 64 (DST + pe4)) (Z_to_bv 64 (DT + 4)) ->
    BD1 mm k1 (Z_to_bv 64 c1) pad1 (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 S1) (Z_to_bv 64 (S1 + 8)) ->
    BD2 mm k2 (Z_to_bv 64 c2) pad2 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 S2) (Z_to_bv 64 (S2 + 8)) ->
    BD3 mm k3 (Z_to_bv 64 c3) pad3 (Z_to_bv 64 (S3 + o3)) (Z_to_bv 64 S3) (Z_to_bv 64 (S3 + 8)) ->
    BD4 mm k4 (Z_to_bv 64 c4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    (c1 <= 64 -> SINV o1 n1 c1) -> (c2 <= 64 -> SINV o2 n2 c2) -> (c3 <= 64 -> SINV o3 n3 c3) -> (c4 <= 64 -> SINV o4 n4 c4) ->
    0 <= c1 < 2^31 -> 0 <= c2 < 2^31 -> 0 <= c3 < 2^31 -> 0 <= c4 < 2^31 ->
    0 <= j1 <= dcap -> 0 <= j2 <= dcap -> 0 <= j3 <= dcap -> 0 <= j4 <= pe4 ->
    0 <= e1 <= dcap -> 0 <= e2 <= dcap -> 0 <= e3 <= dcap -> pe4 <= dcap ->
    dl = tl + 256 * rsv ->
    evt usegs POST (ST 0x26928 mm x1 x5 (Z_to_bv 64 (DT + 4)) x7 x8 x9 x10 (Z_to_bv 64 (DST + j1)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j4)) x19 (Z_to_bv 64 (DST + j3)) x21 x22 x23 x24 x25 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + j2)) x28 x29 x30 (Z_to_bv 64 (DST + pe4))).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest j1 j2 j3 j4 e1 e2 e3 pe4 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl k1 k2 k3 k4 pad1 pad2 pad3 pad4
      x1 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x28 x29 x30
      w0 w3 w4 w5 w6 w8 w9 w10 w11 w14 PV MI OUT DTB FA BS1 BS2 BS3 BS4 SB1 SB2 SB3 SB4 HS1 HS2 HS3 HS4 HC1 HC2 HC3 HC4 HJ1 HJ2 HJ3 HJ4 HE1 HE2 HE3 HPE4 HDL.
    kx_autoLx [0x26948; 0x29160] 20%nat
      [KZRange j1 0 (2^32); KZRange j2 0 (2^32); KZRange j3 0 (2^32); KZRange j4 0 (2^32); KZRange e1 0 (2^32); KZRange e2 0 (2^32);
       KZRange e3 0 (2^32); KZRange dcap 0 (2^32); KZRange pe4 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47)]
      [(SPV - 912, 136)].
    all: kx_mem.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 168288) _ _ ?m2 _) =>
             eapply (x42_ret m2); [eapply (x42_einv m2 rest); eassumption | right; split; reflexivity]
         | _ => idtac
         end.
    all: eapply x42_c1234; try c34_side.
  Qed.

End DX42_6.
