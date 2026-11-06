(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface RT_fk D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Po_rows Po_iface Po_ropl_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition X_ropl_disp : Z := e_rasteropLow_po + 0x318.    (* [comment removed for export] *)
Definition X_ropl_exit : Z := e_rasteropLow_po + 0xa11c.   (* [comment removed for export] *)
Definition X_ropl_wa   : Z := e_rasteropLow_po + 0x4cc.    (* [comment removed for export] *)
Definition X_ropl_gen  : Z := e_rasteropLow_po + 0x510.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition clip_eqs (dx dy dw dh sx sy dpixw dpixh spixw spixh DX DY DW DH SX SY hangw hangh : Z) : Prop :=
  DX = Z.max dx 0 - Z.min (sx - Z.min dx 0) 0 /\
  SX = Z.max (sx - Z.min dx 0) 0 /\
  hangw = DX + (dw + Z.min dx 0 + Z.min (sx - Z.min dx 0) 0) - dpixw /\
  DW = Z.min (Z.min (dw + Z.min dx 0 + Z.min (sx - Z.min dx 0) 0) (dpixw - DX)) (spixw - SX) /\
  DY = Z.max dy 0 - Z.min (sy - Z.min dy 0) 0 /\
  SY = Z.max (sy - Z.min dy 0) 0 /\
  hangh = DY + (dh + Z.min dy 0 + Z.min (sy - Z.min dy 0) 0) - dpixh /\
  DH = Z.min (Z.min (dh + Z.min dy 0 + Z.min (sy - Z.min dy 0) 0) (dpixh - DY)) (spixh - SY) /\
  SX - DX = sx - dx /\ SY - DY = sy - dy.

(* [comment removed for export] *)
Definition ropl1_exit_cont (m0 : mem) (F : bvmap 5 word) (fc : bv 32) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo datad dn : Z) : Prop :=
  forall (mf : mem) (jk : list byte)
      (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    rw_cells asegs mf (usp + -256) [CB 152 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    munch [(usp + -256, usp); (datad, datad + dn)] m0 mf -> wmono asegs m0 mf -> mem_inv asegs mf -> stk asegs mf lo (usp + -256) ->
    evt asegs (ropl_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo datad dn)
      (MS (mkR xra (Z_to_bv 64 (usp + -256)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 X_ropl_exit) fc None mf (seg_rom asegs)).

(* [comment removed for export] *)
Definition ropl1_arms (op : Z) : Prop :=
  forall (m0 mc : mem) (F : bvmap 5 word) (fc : bv 32) (jk jk2 : list byte)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xa0 xa2 xa3 : word)
         (usp lo datad dpixw dpixh dwpl datas spixw spixh swpl dn sn dx dy dw dh sx sy DX DY DW DH SX SY hangw hangh : Z),
  ropl1_exit_cont m0 F fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo datad dn ->
  (* [comment removed for export] *)
  0 <= DX -> 0 <= DY -> 0 <= SX -> 0 <= SY -> 0 < DW -> 0 < DH -> DX + DW <= dpixw -> DY + DH <= dpixh -> SX + DW <= spixw -> SY + DH <= spixh ->
  ((DX mod 32 = 0 /\ SX mod 32 = 0) \/ DX mod 32 <> SX mod 32) ->
  clip_eqs dx dy dw dh sx sy dpixw dpixh spixw spixh DX DY DW DH SX SY hangw hangh ->
  - 2^16 <= dx <= 2^16 -> - 2^16 <= dy <= 2^16 -> 1 <= dw <= 20064 -> 1 <= dh <= 20064 -> - 2^16 <= sx <= 2^16 -> - 2^16 <= sy <= 2^16 ->
  0 < dpixw <= 20000 -> 0 < dpixh <= 20000 -> 0 < spixw <= 20000 -> 0 < spixh <= 20000 ->
  0 < dwpl <= 2^20 -> 0 < swpl <= 2^20 -> 0 < datad -> datad mod 4 = 0 -> 0 < datas -> datas mod 4 = 0 ->
  dn = 4 * (dwpl * dpixh) -> sn = 4 * (swpl * spixh) -> dpixw <= 32 * dwpl -> spixw <= 32 * swpl ->
  dn <= 2^26 -> sn <= 2^26 -> datad + dn <= 2^47 -> datas + sn <= 2^47 -> (datad + dn <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + dn <= lo \/ usp + 64 <= datad) -> (datas + sn <= lo \/ usp + 64 <= datas) ->
  lo + 1024 <= usp -> usp + 64 <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo ->
  wr_at asegs mc datas sn -> acc asegs mc datas sn -> wr_at asegs mc datad dn -> acc asegs mc datad dn -> acc asegs mc A_LMASK 132 -> acc asegs mc A_RMASK 132 ->
  stk asegs mc lo (usp + -256) -> mem_inv asegs mc -> client_consts mc ->
  rw_cells asegs mc usp [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 op); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 spixw); C8 (Z_to_bv 64 spixh); C8 (Z_to_bv 64 swpl);
                          C8 (Z_to_bv 64 sx); C8 (Z_to_bv 64 sy)] ->
  rw_cells asegs mc (usp + -256) [CB 48 jk; C8 (Z_to_bv 64 SY); C8 (Z_to_bv 64 sy); C8 (Z_to_bv 64 dpixh); C8 (Z_to_bv 64 dy); C8 (Z_to_bv 64 spixh); CB 32 jk2;
                                   C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 swpl); C8 (Z_to_bv 64 dwpl);
                                   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(usp + -256, usp); (datad, datad + dn)] m0 mc -> wmono asegs m0 mc ->
  evt asegs (ropl_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo datad dn)
    (MS (mkR (Z_to_bv 64 hangw) (Z_to_bv 64 (usp + -256)) gp tp (Z_to_bv 64 SY) (Z_to_bv 64 SHB) (Z_to_bv 64 spixh) (Z_to_bv 64 SY) (Z_to_bv 64 DW)
             xa0 (Z_to_bv 64 op) xa2 xa3 (Z_to_bv 64 swpl) (Z_to_bv 64 hangh) (Z_to_bv 64 dy) (Z_to_bv 64 DY)
             s2 (Z_to_bv 64 DH) (Z_to_bv 64 DW) (Z_to_bv 64 SX) (Z_to_bv 64 spixw) (Z_to_bv 64 dx) (Z_to_bv 64 sx) (Z_to_bv 64 dpixw) (Z_to_bv 64 SX) (Z_to_bv 64 DX)
             (Z_to_bv 64 DX) (Z_to_bv 64 DH) (Z_to_bv 64 dpixh) (Z_to_bv 64 sy))
        F (Z_to_bv 64 X_ropl_disp) fc None mc (seg_rom asegs)).

(* [comment removed for export] *)
Definition ropl1_wa (op : Z) : Prop :=
  forall (m0 mc : mem) (F : bvmap 5 word) (fc : bv 32) (jk jk2 : list byte)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xa2 xa3 : word)
         (usp lo datad dpixw dpixh dwpl datas spixw spixh swpl dn sn dx dy dw dh sx sy DX DY DW DH SX SY hangw hangh : Z),
  ropl1_exit_cont m0 F fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo datad dn ->
  0 <= DX -> 0 <= DY -> 0 <= SX -> 0 <= SY -> 0 < DW -> 0 < DH -> DX + DW <= dpixw -> DY + DH <= dpixh -> SX + DW <= spixw -> SY + DH <= spixh ->
  DX mod 32 = 0 -> SX mod 32 = 0 ->
  clip_eqs dx dy dw dh sx sy dpixw dpixh spixw spixh DX DY DW DH SX SY hangw hangh ->
  - 2^16 <= dx <= 2^16 -> - 2^16 <= dy <= 2^16 -> 1 <= dw <= 20064 -> 1 <= dh <= 20064 -> - 2^16 <= sx <= 2^16 -> - 2^16 <= sy <= 2^16 ->
  0 < dpixw <= 20000 -> 0 < dpixh <= 20000 -> 0 < spixw <= 20000 -> 0 < spixh <= 20000 ->
  0 < dwpl <= 2^20 -> 0 < swpl <= 2^20 -> 0 < datad -> datad mod 4 = 0 -> 0 < datas -> datas mod 4 = 0 ->
  dn = 4 * (dwpl * dpixh) -> sn = 4 * (swpl * spixh) -> dpixw <= 32 * dwpl -> spixw <= 32 * swpl ->
  dn <= 2^26 -> sn <= 2^26 -> datad + dn <= 2^47 -> datas + sn <= 2^47 -> (datad + dn <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + dn <= lo \/ usp + 64 <= datad) -> (datas + sn <= lo \/ usp + 64 <= datas) ->
  lo + 1024 <= usp -> usp + 64 <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo ->
  wr_at asegs mc datas sn -> acc asegs mc datas sn -> wr_at asegs mc datad dn -> acc asegs mc datad dn -> acc asegs mc A_LMASK 132 -> acc asegs mc A_RMASK 132 ->
  stk asegs mc lo (usp + -256) -> mem_inv asegs mc -> client_consts mc ->
  rw_cells asegs mc usp [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 op); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 spixw); C8 (Z_to_bv 64 spixh); C8 (Z_to_bv 64 swpl);
                          C8 (Z_to_bv 64 sx); C8 (Z_to_bv 64 sy)] ->
  rw_cells asegs mc (usp + -256) [CB 48 jk; C8 (Z_to_bv 64 SY); C8 (Z_to_bv 64 sy); C8 (Z_to_bv 64 dpixh); C8 (Z_to_bv 64 dy); C8 (Z_to_bv 64 spixh); CB 32 jk2;
                                   C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 swpl); C8 (Z_to_bv 64 dwpl);
                                   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(usp + -256, usp); (datad, datad + dn)] m0 mc -> wmono asegs m0 mc ->
  evt asegs (ropl_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo datad dn)
    (MS (mkR (Z_to_bv 64 hangw) (Z_to_bv 64 (usp + -256)) gp tp (Z_to_bv 64 SY) (Z_to_bv 64 SHB) (Z_to_bv 64 spixh) (Z_to_bv 64 SY) (Z_to_bv 64 DW)
             (Z_to_bv 64 0) (Z_to_bv 64 op) xa2 xa3 (Z_to_bv 64 swpl) (Z_to_bv 64 hangh) (Z_to_bv 64 dy) (Z_to_bv 64 DY)
             s2 (Z_to_bv 64 DH) (Z_to_bv 64 DW) (Z_to_bv 64 SX) (Z_to_bv 64 spixw) (Z_to_bv 64 dx) (Z_to_bv 64 sx) (Z_to_bv 64 dpixw) (Z_to_bv 64 SX) (Z_to_bv 64 DX)
             (Z_to_bv 64 DX) (Z_to_bv 64 DH) (Z_to_bv 64 dpixh) (Z_to_bv 64 sy))
        F (Z_to_bv 64 X_ropl_wa) fc None mc (seg_rom asegs)).

Definition ropl1_gen (op : Z) : Prop :=
  forall (m0 mc : mem) (F : bvmap 5 word) (fc : bv 32) (jk jk2 : list byte)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xa3 : word)
         (usp lo datad dpixw dpixh dwpl datas spixw spixh swpl dn sn dx dy dw dh sx sy DX DY DW DH SX SY hangw hangh dr sr : Z),
  ropl1_exit_cont m0 F fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo datad dn ->
  0 <= DX -> 0 <= DY -> 0 <= SX -> 0 <= SY -> 0 < DW -> 0 < DH -> DX + DW <= dpixw -> DY + DH <= dpixh -> SX + DW <= spixw -> SY + DH <= spixh ->
  dr = DX mod 32 -> sr = SX mod 32 -> dr <> sr ->
  clip_eqs dx dy dw dh sx sy dpixw dpixh spixw spixh DX DY DW DH SX SY hangw hangh ->
  - 2^16 <= dx <= 2^16 -> - 2^16 <= dy <= 2^16 -> 1 <= dw <= 20064 -> 1 <= dh <= 20064 -> - 2^16 <= sx <= 2^16 -> - 2^16 <= sy <= 2^16 ->
  0 < dpixw <= 20000 -> 0 < dpixh <= 20000 -> 0 < spixw <= 20000 -> 0 < spixh <= 20000 ->
  0 < dwpl <= 2^20 -> 0 < swpl <= 2^20 -> 0 < datad -> datad mod 4 = 0 -> 0 < datas -> datas mod 4 = 0 ->
  dn = 4 * (dwpl * dpixh) -> sn = 4 * (swpl * spixh) -> dpixw <= 32 * dwpl -> spixw <= 32 * swpl ->
  dn <= 2^26 -> sn <= 2^26 -> datad + dn <= 2^47 -> datas + sn <= 2^47 -> (datad + dn <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + dn <= lo \/ usp + 64 <= datad) -> (datas + sn <= lo \/ usp + 64 <= datas) ->
  lo + 1024 <= usp -> usp + 64 <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo ->
  wr_at asegs mc datas sn -> acc asegs mc datas sn -> wr_at asegs mc datad dn -> acc asegs mc datad dn -> acc asegs mc A_LMASK 132 -> acc asegs mc A_RMASK 132 ->
  stk asegs mc lo (usp + -256) -> mem_inv asegs mc -> client_consts mc ->
  rw_cells asegs mc usp [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 op); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 spixw); C8 (Z_to_bv 64 spixh); C8 (Z_to_bv 64 swpl);
                          C8 (Z_to_bv 64 sx); C8 (Z_to_bv 64 sy)] ->
  rw_cells asegs mc (usp + -256) [CB 40 jk; C8 (Z_to_bv 64 hangh); C8 (Z_to_bv 64 SY); C8 (Z_to_bv 64 sy); C8 (Z_to_bv 64 dpixh); C8 (Z_to_bv 64 dy); C8 (Z_to_bv 64 spixh);
                                   CB 32 jk2; C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 swpl); C8 (Z_to_bv 64 dwpl);
                                   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(usp + -256, usp); (datad, datad + dn)] m0 mc -> wmono asegs m0 mc ->
  evt asegs (ropl_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo datad dn)
    (MS (mkR (Z_to_bv 64 hangw) (Z_to_bv 64 (usp + -256)) gp tp (Z_to_bv 64 SY) (Z_to_bv 64 SHB) (Z_to_bv 64 spixh) (Z_to_bv 64 SY) (Z_to_bv 64 DW)
             (Z_to_bv 64 (Z.lor dr sr)) (Z_to_bv 64 op) (Z_to_bv 64 sr) xa3 (Z_to_bv 64 swpl) (Z_to_bv 64 hangh) (Z_to_bv 64 dy) (Z_to_bv 64 DY)
             s2 (Z_to_bv 64 DH) (Z_to_bv 64 DW) (Z_to_bv 64 SX) (Z_to_bv 64 spixw) (Z_to_bv 64 dx) (Z_to_bv 64 sx) (Z_to_bv 64 dpixw) (Z_to_bv 64 SX) (Z_to_bv 64 DX)
             (Z_to_bv 64 DX) (Z_to_bv 64 dr) (Z_to_bv 64 dpixh) (Z_to_bv 64 sy))
        F (Z_to_bv 64 X_ropl_gen) fc None mc (seg_rom asegs)).
