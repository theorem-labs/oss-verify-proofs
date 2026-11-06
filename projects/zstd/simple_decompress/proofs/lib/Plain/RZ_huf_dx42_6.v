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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_huf_dx1 RZ_huf_dx41 RZ_huf_dx41f RZ_huf_dx42_1f RZ_huf_dx42_2f RZ_huf_dx42_3f RZ_huf_dx42_4f RZ_huf_dx42_5.
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

  Notation WDG := [(DST, DST + dcap); (SPV - 416, SPV - 256)].
  Notation X41P := (RZ_huf_dx41f.X41P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation SBUF := (RZ_huf_dx41f.SBUF SPV DST dcap lo).
  Notation x41p_transport := (RZ_huf_dx41f.x41p_transport ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX DJ3).
  Notation sbuf_transport := (RZ_huf_dx41f.sbuf_transport SPV DST dcap DT lo dtb CTX DJ3).
  Notation x41_einv := (RZ_huf_dx41f.x41_einv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap DT lo dtb CTX).
  Notation x42_end := (RZ_huf_dx42_5.x42_end ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_ret := (RZ_huf_dx42_5.x42_ret ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_d1 := (RZ_huf_dx42_1f.x42_d1 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_d2 := (RZ_huf_dx42_2f.x42_d2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_d3 := (RZ_huf_dx42_3f.x42_d3 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).
  Notation x42_d4 := (RZ_huf_dx42_4f.x42_d4 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap DT lo dtb CTX tl rsv TL RSV X2OK).

  Ltac wdf_of MU := eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia.

  (* [comment removed for export] *)
  Lemma x42_c0 : forall mm rest j1 j2 j3 j4 e1 e2 e3 pe4 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl (k4 : word) pad
      (x1 x6 x7 x8 x10 x11 x13 x16 x19 x21 x22 x23 x28 x29 x30 x31 : word)
      (w0 w1 w2 w4 w5 w8 w12 w19 : word),
    X41P mm rest -> mem_inv psegs mm -> stk psegs mm DST (DST + dcap) -> bytes_at psegs mm DT dtb ->
    FRA mm w0 w1 w2 (Z_to_bv 64 (DST + e3)) w4 w5 (Z_to_bv 64 dl) (Z_to_bv 64 S1) w8 (Z_to_bv 64 (DST + pe4 - 7)) (Z_to_bv 64 S3) (Z_to_bv 64 (DT + 4)) w12 (Z_to_bv 64 dcap) (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (S2 + 8)) (Z_to_bv 64 (S3 + 8)) (Z_to_bv 64 c1) (Z_to_bv 64 (S3 + o3)) w19 ->
    BD4 mm k4 (Z_to_bv 64 c4) pad (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) ->
    SBUF mm S1 n1 b1 -> SBUF mm S2 n2 b2 -> SBUF mm S3 n3 b3 -> SBUF mm S4 n4 b4 ->
    (c1 <= 64 -> SINV o1 n1 c1) -> (c2 <= 64 -> SINV o2 n2 c2) -> (c3 <= 64 -> SINV o3 n3 c3) -> (c4 <= 64 -> SINV o4 n4 c4) ->
    0 <= c1 < 2^31 -> 0 <= c2 < 2^31 -> 0 <= c3 < 2^31 -> 0 <= c4 < 2^31 ->
    0 <= j1 <= dcap -> 0 <= j2 <= dcap -> 0 <= j3 <= dcap -> 0 <= j4 <= pe4 ->
    0 <= e1 <= dcap -> 0 <= e2 <= dcap -> 0 <= e3 <= dcap -> pe4 <= dcap ->
    dl = tl + 256 * rsv ->
    evt psegs POST (ST 0x2021c mm x1 (Z_to_bv 64 (DST + j2)) x6 x7 x8 (Z_to_bv 64 (DST + j1)) x10 x11 (Z_to_bv 64 (DST + j4)) x13 (Z_to_bv 64 (DST + j3)) (Z_to_bv 64 (DST + e2)) x16 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 c2) x19 (Z_to_bv 64 S2) x21 x22 x23 (Z_to_bv 64 (S2 + o2)) (Z_to_bv 64 (DST + pe4)) (Z_to_bv 64 (S1 + o1)) (Z_to_bv 64 c3) x28 x29 x30 x31).
  Proof using All.
    pose proof CTX as CTX'. x41_ctx_open CTX'.
    intros mm rest j1 j2 j3 j4 e1 e2 e3 pe4 S1 n1 b1 o1 c1 S2 n2 b2 o2 c2 S3 n3 b3 o3 c3 S4 n4 b4 o4 c4 dl k4 pad
      x1 x6 x7 x8 x10 x11 x13 x16 x19 x21 x22 x23 x28 x29 x30 x31
      w0 w1 w2 w4 w5 w8 w12 w19 PV MI OUT DTB FA BD SB1 SB2 SB3 SB4 HS1 HS2 HS3 HS4 HC1 HC2 HC3 HC4 HJ1 HJ2 HJ3 HJ4 HE1 HE2 HE3 HPE4 HDL.
    assert (MUr : munch WDG mm mm) by apply munch_refl.
    assert (WMr : wmono psegs mm mm) by apply wmono_refl.
    kx_autoLx [0x2042c; 0x20238] 20%nat
      [KZRange j1 0 (2^32); KZRange j2 0 (2^32); KZRange j3 0 (2^32); KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32);
       KZRange dcap 0 (2^32); KZRange DST 4096 (2^47); KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47);
       KZWr (SPV - 416) 160; KZDisj (SPV - 416) 160 DST dcap; KZDisj (SPV - 416) 160 DT 16388; KZDisj (SPV - 416) 160 (SPV - 256) 40]
      [(SPV - 416, 160)].
    all: kx_mem.
    all: lazymatch goal with
         | MU2 : munch _ ?M ?m2, WM2 : wmono _ ?M ?m2 |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
             assert (PV2 : X41P m2 rest) by (eapply (x41p_transport mm m2 rest PV); [wdf_of MU2 | exact WM2]);
             assert (SB1' : SBUF m2 S1 n1 b1) by (eapply (sbuf_transport mm m2 _ _ _ SB1); wdf_of MU2);
             assert (SB2' : SBUF m2 S2 n2 b2) by (eapply (sbuf_transport mm m2 _ _ _ SB2); wdf_of MU2);
             assert (SB3' : SBUF m2 S3 n3 b3) by (eapply (sbuf_transport mm m2 _ _ _ SB3); wdf_of MU2);
             assert (SB4' : SBUF m2 S4 n4 b4) by (eapply (sbuf_transport mm m2 _ _ _ SB4); wdf_of MU2);
             clear PV SB1 SB2 SB3 SB4
         end.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 132140) _ _ ?m2 _) =>
             eapply (x42_ret m2); [eapply (x41_einv m2 rest); eassumption | right; split; reflexivity]
         | _ => idtac
         end.
    clear KXK KXA KXRD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2' _) => set (m2 := m2') in * end.
    pose proof SB1' as (B1 & L1 & R10 & R11 & R12 & D11 & D12).
    eapply (x42_d1 m2 m2 j1 e1 o1 S1 n1 b1 dl c1); try eassumption; try lia; try apply munch_refl; try apply wmono_refl.
    intros mm1 D1 ? ? ? ? ? ? ? ? ? ? ? ? ? MU1 WM1 MI1 OUT1 DTB1 FA1 HD1. subst D1.
    assert (SB2'' : SBUF mm1 S2 n2 b2) by (eapply (sbuf_transport m2 mm1 _ _ _ SB2'); wdf_of MU1).
    destruct SB2'' as (B2 & L2 & R20 & R21 & R22 & D21 & D22).
    eapply (x42_d2 m2 mm1 j2 e2 o2 S2 n2 b2 dl c2); try eassumption; try lia.
    intros mm2 D2 ? ? ? ? ? ? ? ? ? ? ? ? ? MU2 WM2 MI2 OUT2 DTB2 FA2 HD2. subst D2.
    assert (SB3'' : SBUF mm2 S3 n3 b3) by (eapply (sbuf_transport m2 mm2 _ _ _ SB3'); wdf_of MU2).
    destruct SB3'' as (B3 & L3 & R30 & R31 & R32 & D31 & D32).
    eapply (x42_d3 m2 mm2 j3 e3 o3 S3 n3 b3 dl c3); try eassumption; try lia.
    intros mm3 D3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU3 WM3 MI3 OUT3 DTB3 FA3 HD3. subst D3.
    assert (SB4'' : SBUF mm3 S4 n4 b4) by (eapply (sbuf_transport m2 mm3 _ _ _ SB4'); wdf_of MU3).
    destruct SB4'' as (B4 & L4 & R40 & R41 & R42 & D41 & D42).
    assert (BD3 : BD4 mm3 k4 (Z_to_bv 64 c4) pad (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8))).
    { lazymatch goal with BD2 : rw_cells psegs m2 (SPV + -256) _ |- _ =>
        eapply (rw_cells_transport psegs _ m2 mm3 _ _ BD2 MU3 WM3);
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia end. }
    eapply (x42_d4 mm3 mm3 j4 pe4 o4 S4 n4 b4 dl c4 k4 pad); try eassumption; try lia; try apply munch_refl; try apply wmono_refl.
    intros mm4 D4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU4 WM4 MI4 OUT4 DTB4 FA4 BD4' HD4.
    eapply (x42_end mm4); [|exact FA4 | exact BD4'].
    eapply (x41_einv mm4 rest); [ | exact MI4 | exact OUT4 | exact FA4 | exact BD4'].
    eapply (x41p_transport m2 mm4 rest PV2); [|exact (wmono_trans psegs m2 mm3 mm4 WM3 WM4)].
    eapply munch_trans; [wdf_of MU3 | wdf_of MU4].
  Qed.

End DX42_6.
