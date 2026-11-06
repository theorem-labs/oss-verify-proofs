(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface RT_fk D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_rows Po_iface Po_ropl_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition X_ropl_disp : Z := e_rasteropLow_po + 0x160.    (* [comment removed for export] *)
Definition X_ropl_exit : Z := e_rasteropLow_po + 0x3b44.   (* [comment removed for export] *)
Definition X_ropl_wa   : Z := e_rasteropLow_po + 0x22c.    (* [comment removed for export] *)
Definition X_ropl_gen  : Z := e_rasteropLow_po + 0x260.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ropl1_exit_cont (m0 : mem) (F : bvmap 5 word) (fc : bv 32) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo datad dn : Z) : Prop :=
  forall (mf : mem) (jk : list byte)
      (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    rw_cells asegs mf (usp + -144) [CB 40 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    munch [(usp + -144, usp); (datad, datad + dn)] m0 mf -> wmono asegs m0 mf -> mem_inv asegs mf -> stk asegs mf lo (usp + -144) ->
    evt asegs (ropl_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo datad dn)
      (MS (mkR xra (Z_to_bv 64 (usp + -144)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 X_ropl_exit) fc None mf (seg_rom asegs)).

(* [comment removed for export] *)
Definition ropl1_arms (op : Z) : Prop :=
  forall (m0 mc : mem) (F : bvmap 5 word) (fc : bv 32) (jk : list byte)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa6 xs2 xs3 xs4 xs5 xs6 xt4 xt5 xt6 : word)
         (usp lo datad dpixw dpixh dwpl datas spixw spixh swpl dn sn dx dy dw dh sx sy DX DY DW DH SX SY : Z),
  ropl1_exit_cont m0 F fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo datad dn ->
  (* [comment removed for export] *)
  0 <= DX -> 0 <= DY -> 0 <= SX -> 0 <= SY -> 0 < DW -> 0 < DH -> DX + DW <= dpixw -> DY + DH <= dpixh -> SX + DW <= spixw -> SY + DH <= spixh ->
  ((DX mod 32 = 0 /\ SX mod 32 = 0) \/ DX mod 32 <> SX mod 32) ->
  0 < dpixw <= 20000 -> 0 < dpixh <= 20000 -> 0 < spixw <= 20000 -> 0 < spixh <= 20000 ->
  0 < dwpl <= 2^20 -> 0 < swpl <= 2^20 -> 0 < datad -> datad mod 4 = 0 -> 0 < datas -> datas mod 4 = 0 ->
  dn = 4 * (dwpl * dpixh) -> sn = 4 * (swpl * spixh) -> dpixw <= 32 * dwpl -> spixw <= 32 * swpl ->
  dn <= 2^26 -> sn <= 2^26 -> datad + dn <= 2^47 -> datas + sn <= 2^47 -> (datad + dn <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + dn <= lo \/ usp + 64 <= datad) -> (datas + sn <= lo \/ usp + 64 <= datas) ->
  lo + 1024 <= usp -> usp + 64 <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo ->
  wr_at asegs mc datas sn -> acc asegs mc datas sn -> wr_at asegs mc datad dn -> acc asegs mc datad dn -> acc asegs mc A_LMASK 132 -> acc asegs mc A_RMASK 132 ->
  stk asegs mc lo (usp + -144) -> mem_inv asegs mc -> client_consts mc ->
  rw_cells asegs mc usp [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 op); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 spixw); C8 (Z_to_bv 64 spixh); C8 (Z_to_bv 64 swpl);
                          C8 (Z_to_bv 64 sx); C8 (Z_to_bv 64 sy)] ->
  rw_cells asegs mc (usp + -144) [CB 40 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(usp + -144, usp); (datad, datad + dn)] m0 mc -> wmono asegs m0 mc ->
  evt asegs (ropl_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo datad dn)
    (MS (mkR (Z_to_bv 64 DH) (Z_to_bv 64 (usp + -144)) gp tp xt0 xt1 xt2 xs0 xs1
             (Z_to_bv 64 datad) (Z_to_bv 64 op) xa2 xa3 (Z_to_bv 64 dwpl) (Z_to_bv 64 SHB) xa6 (Z_to_bv 64 swpl)
             xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 datas) (Z_to_bv 64 DX) (Z_to_bv 64 SY) (Z_to_bv 64 DY) (Z_to_bv 64 SX) (Z_to_bv 64 DW) xt4 xt5 xt6)
        F (Z_to_bv 64 X_ropl_disp) fc None mc (seg_rom asegs)).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ropl1_wa (op : Z) : Prop :=
  forall (m0 mc : mem) (F : bvmap 5 word) (fc : bv 32) (jk : list byte)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xt0 xt1 xt2 xs0 xs1 xa3 xa6 xs2 xs3 xs4 xs5 xs6 xt4 xt5 xt6 : word)
         (usp lo datad dpixw dpixh dwpl datas spixw spixh swpl dn sn dx dy dw dh sx sy DX DY DW DH SX SY : Z),
  ropl1_exit_cont m0 F fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo datad dn ->
  0 <= DX -> 0 <= DY -> 0 <= SX -> 0 <= SY -> 0 < DW -> 0 < DH -> DX + DW <= dpixw -> DY + DH <= dpixh -> SX + DW <= spixw -> SY + DH <= spixh ->
  DX mod 32 = 0 -> SX mod 32 = 0 ->
  0 < dpixw <= 20000 -> 0 < dpixh <= 20000 -> 0 < spixw <= 20000 -> 0 < spixh <= 20000 ->
  0 < dwpl <= 2^20 -> 0 < swpl <= 2^20 -> 0 < datad -> datad mod 4 = 0 -> 0 < datas -> datas mod 4 = 0 ->
  dn = 4 * (dwpl * dpixh) -> sn = 4 * (swpl * spixh) -> dpixw <= 32 * dwpl -> spixw <= 32 * swpl ->
  dn <= 2^26 -> sn <= 2^26 -> datad + dn <= 2^47 -> datas + sn <= 2^47 -> (datad + dn <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + dn <= lo \/ usp + 64 <= datad) -> (datas + sn <= lo \/ usp + 64 <= datas) ->
  lo + 1024 <= usp -> usp + 64 <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo ->
  wr_at asegs mc datas sn -> acc asegs mc datas sn -> wr_at asegs mc datad dn -> acc asegs mc datad dn -> acc asegs mc A_LMASK 132 -> acc asegs mc A_RMASK 132 ->
  stk asegs mc lo (usp + -144) -> mem_inv asegs mc -> client_consts mc ->
  rw_cells asegs mc usp [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 op); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 spixw); C8 (Z_to_bv 64 spixh); C8 (Z_to_bv 64 swpl);
                          C8 (Z_to_bv 64 sx); C8 (Z_to_bv 64 sy)] ->
  rw_cells asegs mc (usp + -144) [CB 40 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(usp + -144, usp); (datad, datad + dn)] m0 mc -> wmono asegs m0 mc ->
  evt asegs (ropl_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo datad dn)
    (MS (mkR (Z_to_bv 64 DH) (Z_to_bv 64 (usp + -144)) gp tp xt0 xt1 xt2 xs0 xs1
             (Z_to_bv 64 datad) (Z_to_bv 64 op) (Z_to_bv 64 0) xa3 (Z_to_bv 64 dwpl) (Z_to_bv 64 SHB) xa6 (Z_to_bv 64 swpl)
             xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 datas) (Z_to_bv 64 DX) (Z_to_bv 64 SY) (Z_to_bv 64 DY) (Z_to_bv 64 SX) (Z_to_bv 64 DW) xt4 xt5 xt6)
        F (Z_to_bv 64 X_ropl_wa) fc None mc (seg_rom asegs)).

Definition ropl1_gen (op : Z) : Prop :=
  forall (m0 mc : mem) (F : bvmap 5 word) (fc : bv 32) (jk : list byte)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xt0 xt1 xt2 xs0 xs1 xa3 xs2 xs3 xs4 xs5 xt4 xt5 xt6 : word)
         (usp lo datad dpixw dpixh dwpl datas spixw spixh swpl dn sn dx dy dw dh sx sy DX DY DW DH SX SY dr sr : Z),
  ropl1_exit_cont m0 F fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo datad dn ->
  0 <= DX -> 0 <= DY -> 0 <= SX -> 0 <= SY -> 0 < DW -> 0 < DH -> DX + DW <= dpixw -> DY + DH <= dpixh -> SX + DW <= spixw -> SY + DH <= spixh ->
  dr = DX mod 32 -> sr = SX mod 32 -> dr <> sr ->
  0 < dpixw <= 20000 -> 0 < dpixh <= 20000 -> 0 < spixw <= 20000 -> 0 < spixh <= 20000 ->
  0 < dwpl <= 2^20 -> 0 < swpl <= 2^20 -> 0 < datad -> datad mod 4 = 0 -> 0 < datas -> datas mod 4 = 0 ->
  dn = 4 * (dwpl * dpixh) -> sn = 4 * (swpl * spixh) -> dpixw <= 32 * dwpl -> spixw <= 32 * swpl ->
  dn <= 2^26 -> sn <= 2^26 -> datad + dn <= 2^47 -> datas + sn <= 2^47 -> (datad + dn <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
  (datad + dn <= lo \/ usp + 64 <= datad) -> (datas + sn <= lo \/ usp + 64 <= datas) ->
  lo + 1024 <= usp -> usp + 64 <= 2^47 -> usp mod 16 = 0 -> 0x10007fff8000 <= lo ->
  wr_at asegs mc datas sn -> acc asegs mc datas sn -> wr_at asegs mc datad dn -> acc asegs mc datad dn -> acc asegs mc A_LMASK 132 -> acc asegs mc A_RMASK 132 ->
  stk asegs mc lo (usp + -144) -> mem_inv asegs mc -> client_consts mc ->
  rw_cells asegs mc usp [C8 (Z_to_bv 64 dh); C8 (Z_to_bv 64 op); C8 (Z_to_bv 64 datas); C8 (Z_to_bv 64 spixw); C8 (Z_to_bv 64 spixh); C8 (Z_to_bv 64 swpl);
                          C8 (Z_to_bv 64 sx); C8 (Z_to_bv 64 sy)] ->
  rw_cells asegs mc (usp + -144) [CB 40 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(usp + -144, usp); (datad, datad + dn)] m0 mc -> wmono asegs m0 mc ->
  evt asegs (ropl_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 usp lo datad dn)
    (MS (mkR (Z_to_bv 64 DH) (Z_to_bv 64 (usp + -144)) gp tp xt0 xt1 xt2 xs0 xs1
             (Z_to_bv 64 datad) (Z_to_bv 64 op) (Z_to_bv 64 (Z.lor dr sr)) xa3 (Z_to_bv 64 dwpl) (Z_to_bv 64 SHB) (Z_to_bv 64 sr) (Z_to_bv 64 swpl)
             xs2 xs3 xs4 xs5 (Z_to_bv 64 dr) (Z_to_bv 64 datas) (Z_to_bv 64 DX) (Z_to_bv 64 SY) (Z_to_bv 64 DY) (Z_to_bv 64 SX) (Z_to_bv 64 DW) xt4 xt5 xt6)
        F (Z_to_bv 64 X_ropl_gen) fc None mc (seg_rom asegs)).
