(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF F_ctypeA H_parse_uric H2Kit AWRng AWUb.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_memptr_cmp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import H_puri_seg1 H_puri_seg2 H_puri_seg3.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Variables (U O ulen lo q kq kO : Z) (ustr slack : list byte) (st : fsstate FI).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
Variable canary : word.

Local Notation F := (puriF FI st).  Local Notation FL := (puriFL FI st).  Local Notation SF := (puriSF FI st).  Let st1 := fs_next FI st 3.

Notation WP := [(O, O + 216); (ERRNO_A, ERRNO_A + 4)]%Z.
Notation W0 := ((lo, q) :: FSIV WP)%Z.

Notation ushadow w :=
  ([C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).

Notation USTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 SF) (Z_to_bv 64 U) x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Notation zbU := (Z_to_bv 8 0).

Local Notation minvU := (H_puri_seg1.minvU FI O lo q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
Local Notation UBANDd := (H_puri_seg1.UBANDd U ulen slack).
Local Notation pinvR := (H_puri_seg1.pinvR U ustr slack canary).
Local Notation pinvU := (H_puri_seg1.pinvU U O ustr slack canary).
Local Notation WEU := (H_puri_seg1.WEU FI lo q st).
Local Notation rframeU := (H_puri_seg1.rframeU FI lo q st).
Local Notation postU := (H_puri_seg1.postU FI O lo q st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0).
Local Notation XU := (H_puri_seg1.XU U O ustr slack canary).

Local Notation postU_mono := (H_puri_seg2.postU_mono FI O lo q st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0).
Local Notation XOK_ALL := (H_puri_seg2.XOK_ALL U O ustr slack canary).
Local Notation wb_strU := (H_puri_seg2.wb_strU FI st).

Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= q - PURI_DEPTH_A.
Hypothesis AL16 : q = 16 * kq.
Hypothesis QHI : q < 2^63.
Hypothesis RF0 : RFAKE FI st m0.
Hypothesis FCO : fs_call_ok FI st tp 1.
Hypothesis FE0 : FSENV FI m0.
Hypothesis Q47 : q <= 2^47 - 64.
Hypothesis SHZ : shz m0 (sh lo) (sh q).
Hypothesis SHR : shr m0 (sh lo - sh lo mod 8) (sh q + 8).

Hypothesis OAL : O = 8 * kO.
Hypothesis OLO : 0x609000 <= O.
Hypothesis OHI : O + 216 <= alloc_ceiling.
Hypothesis OLB : lb (fs_live FI st) O 216.
Hypothesis SHWO : shw m0 O 216.
Hypothesis ULEN : Z.of_nat (length ustr) = ulen.
Hypothesis ULR : 0 <= ulen < 2^31.
Hypothesis PAD : (- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis UIMG : 0x609000 <= U.
Hypothesis UHI : U + ulen + 1 + Z.of_nat (length slack) <= alloc_ceiling.
Hypothesis UFS : U + ulen + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U.
Hypothesis UBAND : UBANDd.
Hypothesis SHWU : shw m0 U (ulen + 1).
Hypothesis SHWHTTPS : shw m0 HTTPS_A 6.
Hypothesis SHWGIF : shw m0 GIF_A 4.
Hypothesis SHWMARK : shw m0 MARKTAB_A 10.
Hypothesis SHWRESV : shw m0 RESVTAB_A 13.
Hypothesis TPV : tp = Z_to_bv 64 6190512.

Local Notation geomU := (H_puri_seg1.geomU FI U O ulen lo ustr slack st m0 RF0 OLB ULR).
Local Notation prologueU := (H_puri_seg1.prologueU FI STACK_MALLOC_3 U O ulen lo q kq ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 CLO LO AL16 QHI RF0 FCO FE0 Q47 OHI OLB ULR).
Local Notation WP_app := (H_puri_seg1.WP_app U O ulen lo ustr slack m0 SHWO ULR).
Local Notation W0_fsw := (H_puri_seg1.W0_fsw FI U O ulen lo q ustr slack m0 CLO SHWO ULR).
Local Notation shwStk_now := (H_puri_seg1.shwStk_now FI U O ulen lo q kq ustr slack m0 CLO LO AL16 Q47 SHZ SHR SHWO ULR).
Local Notation WP_out := (H_puri_seg1.WP_out FI U O ulen lo ustr slack m0 SHWO ULEN ULR PAD UHI).
Local Notation shwO_now := (H_puri_seg1.shwO_now FI U O ulen lo q ustr slack st m0 RF0 OLB SHWO ULEN ULR PAD UHI).
Local Notation shwU_now := (H_puri_seg1.shwU_now FI U O ulen lo q ustr slack m0 CLO SHWO ULR UFS SHWU).
Local Notation shwG_now := (H_puri_seg1.shwG_now FI U O ulen lo q ustr slack m0 CLO SHWO ULR).
Local Notation liveU := (H_puri_seg1.liveU FI U O ulen lo ustr slack st m0 RF0 OLB ULR).
Local Notation sub_fp_O := (H_puri_seg1.sub_fp_O FI U O ulen lo q ustr slack ULR).
Local Notation sub_fp_cons2 := (H_puri_seg1.sub_fp_cons2 FI U ulen slack ULR UFS).
Local Notation sub_fp_stk := (H_puri_seg1.sub_fp_stk FI U O ulen lo q ustr slack ULR).
Local Notation out_open := (H_puri_seg1.out_open U O ulen lo ustr slack ULR).
Local Notation out_close := (H_puri_seg1.out_close U O ulen lo ustr slack ULR).
Local Notation memsetO := (H_puri_seg1.memsetO FI IC U O ulen lo q kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UHI UFS).
Local Notation memsetOo := (H_puri_seg1.memsetOo FI IC U O ulen lo q kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UHI UFS).
Local Notation sub_fp_WEU := (H_puri_seg1.sub_fp_WEU FI U O ulen lo q ustr slack st m0 RF0 OLB ULR).
Local Notation exitU := (H_puri_seg1.exitU FI SET_SHADOW_F5 U O ulen lo q kq ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 CLO LO AL16 RF0 Q47 OLB ULEN ULR PAD UHI).
Local Notation puricO := (H_puri_seg1.puricO FI IC U O ulen lo q kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS SHWU SHWMARK SHWRESV).
Local Notation WEU_dj_O := (H_puri_seg1.WEU_dj_O FI U O ulen lo q ustr slack st m0 CLO RF0 OHI OLB ULR).
Local Notation WEU_dj_U := (H_puri_seg1.WEU_dj_U FI U O ulen lo q ustr slack st m0 CLO RF0 OLB ULR UHI UFS UBAND).
Local Notation WEU_dj_low := (H_puri_seg1.WEU_dj_low FI U O ulen lo q ustr slack st m0 CLO RF0 OLB ULR).
Local Notation pinvR_rframe := (H_puri_seg1.pinvR_rframe FI U O ulen lo q ustr slack st m0 canary CLO RF0 OLB ULEN ULR UHI UFS UBAND).
Local Notation XU_rframe := (H_puri_seg1.XU_rframe FI U O ulen lo q ustr slack st m0 canary CLO RF0 OHI OLB ULEN ULR UHI UFS UBAND).
Local Notation tail2U := (H_puri_seg1.tail2U FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).
Local Notation slti0_nonnegU := (H_puri_seg1.slti0_nonnegU U ulen lo ustr slack ULR).
Local Notation Z_to_le_bytes_appU := (H_puri_seg1.Z_to_le_bytes_appU U ulen lo ustr slack ULR).
Local Notation le8_small_splitU := (H_puri_seg1.le8_small_splitU U ulen lo ustr slack ULR).
Local Notation rw_cells_C8_C4C4U := (H_puri_seg1.rw_cells_C8_C4C4U FI U ulen lo ustr slack ULR UFS).
Local Notation rw_cells_C4C4_C8U := (H_puri_seg1.rw_cells_C4C4_C8U FI U ulen lo ustr slack ULR UFS).
Local Notation tailU := (H_puri_seg1.tailU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).
Local Notation nohpU := (H_puri_seg1.nohpU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).

Local Notation stackcallU := (H_puri_seg2.stackcallU FI U O ulen lo q ustr slack st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 CLO RF0 OLB ULR).
Local Notation stack_dj := (H_puri_seg2.stack_dj lo q CLO).
Local Notation pinvR_stack := (H_puri_seg2.pinvR_stack U ulen lo q ustr slack canary CLO ULEN ULR UHI).
Local Notation out_stack := (H_puri_seg2.out_stack U O ulen lo q ustr slack CLO OHI ULR).
Local Notation shwW_now := (H_puri_seg2.shwW_now FI U O ulen lo ustr slack st m0 RF0 OLB ULR).
Local Notation sub_fp_SF := (H_puri_seg2.sub_fp_SF FI U O ulen lo q ustr slack st m0 RF0 OLB ULR).
Local Notation failU := (H_puri_seg2.failU FI SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 OAL OLO OHI OLB ULEN ULR PAD UHI UFS UBAND).
Local Notation hpendU := (H_puri_seg2.hpendU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).
Local Notation inetU := (H_puri_seg2.inetU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).
Local Notation fam4U := (H_puri_seg2.fam4U FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV).
Local Notation fam6U := (H_puri_seg2.fam6U FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV).
Local Notation portfamU := (H_puri_seg2.portfamU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV).
Local Notation wb_nthU := (H_puri_seg2.wb_nthU U ulen lo ustr slack ULR).
Local Notation wb_decomp := (H_puri_seg2.wb_decomp U ulen lo ustr slack ULR).
Local Notation wb_sh0 := (H_puri_seg2.wb_sh0 FI U O ulen lo ustr slack st m0 RF0 OLB ULR).
Local Notation wrap_sub_ltU := (H_puri_seg2.wrap_sub_ltU U ulen lo ustr slack ULR).
Local Notation wrap_sub_geU := (H_puri_seg2.wrap_sub_geU U ulen lo ustr slack ULR).
Local Notation sub_fp_errno := (H_puri_seg2.sub_fp_errno FI U O ulen lo q ustr slack ULR).
Local Notation portU := (H_puri_seg2.portU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).
Local Notation sub_fp_F := (H_puri_seg2.sub_fp_F FI U O ulen lo q ustr slack st m0 RF0 OLB ULR).
Local Notation v6brU := (H_puri_seg2.v6brU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).
Local Notation v6loopU := (H_puri_seg2.v6loopU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).
Local Notation v6U := (H_puri_seg2.v6U FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).

Local Notation v4exitU := (H_puri_seg3.v4exitU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).
Local Notation v4loopU := (H_puri_seg3.v4loopU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).
Local Notation v4U := (H_puri_seg3.v4U FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).
Local Notation nul_splitU := (H_puri_seg3.nul_splitU FI U ulen lo ustr slack ULR UFS).
Local Notation mod8_shiftU := (H_puri_seg3.mod8_shiftU U ulen lo ustr slack ULR).
Local Notation stpnA_length := (H_puri_seg3.stpnA_length U ulen lo ustr slack ULR).
Local Notation stpnA_nth_lt := (H_puri_seg3.stpnA_nth_lt U ulen lo ustr slack ULR).
Local Notation stpnA_nth_z := (H_puri_seg3.stpnA_nth_z U ulen lo ustr slack ULR).
Local Notation wb_join255 := (H_puri_seg3.wb_join255 FI U ulen lo ustr slack st ULR).
Local Notation hpBU := (H_puri_seg3.hpBU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).
Local Notation hpU := (H_puri_seg3.hpU FI IC SET_SHADOW_F5 U O ulen lo q kq kO ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV).

Ltac mv_tacU := unfold H_puri_seg1.minvU; split; [eexists; eassumption|]; split; [assumption|];
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eexists; split; eassumption.

Ltac pr_tacU := unfold H_puri_seg1.pinvR; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eassumption| eexists; eassumption].
Ltac pv_tacU := unfold H_puri_seg1.pinvU; split; [eassumption| pr_tacU].

Ltac ub_ptr := rewrite ?slti0_nonnegU by lia; ub_b2z; cbn [Z.b2z]; change (Z.lxor (Z.lxor 0 0) 1) with 1.

Notation XOK := (XU (fun r => r = 1)).

Notation XALL := (XU (fun r => r = 1 \/ r = -108)).

Ltac chkW r c SHF HC :=
  let a := reg_val r in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHR := fresh "SHR" in
    assert (SHR : ov_read_bytes asegs mm a 1 = Some [Z_to_bv 8 0]) by (apply (wb_sh0 mm c a SHF HC); shadow_addr_tac) end;
  step; clear_shr.

Definition https6A : list byte := map (Z_to_bv 8) [104; 116; 116; 112; 115; 0].
#[using="U ulen lo ustr slack ULR"] Lemma https_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m HTTPS_A https6A.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m HTTPS_A https6A MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
#[using="U lo ULEN ULR PAD"] Lemma nth_UA : forall i, 0 <= i <= ulen -> exists b, nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat i) = Some b.
Proof.
  intros i Hi. destruct (nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat i)) as [b|] eqn:Hb; [exists b; reflexivity|].
  exfalso. apply nth_error_None in Hb. rewrite length_app in Hb. cbn [length] in Hb. lia.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma hp80U : forall (bp : Z) q' m v0 v8 v16 v24 v32 wb junk
         x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x28 x29 x30 x31,
  minvU q' m 248 v0 v8 v16 v24 v32 (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvU m junk -> 0 <= bp -> bp + 1 < ulen ->
  evt asegs (postU XALL)
    (USTP 0x8d720 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) (Z_to_bv 64 (Z.lxor U 18446744073709551615)) (Z_to_bv 64 F) x23 (Z_to_bv 64 O) x25 (Z_to_bv 64 bp) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP BPL.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (munch_refl [(q' + 24, q' + 32)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step.
  step; fix_lit_store.
  step.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 24) (q' + 32) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  step.   ubr3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (hpU (bp + 2) 80 q' mm v0 v8 v16 v32 wb junk); [mv_tacU| pv_tacU| lia| left; reflexivity] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma hp443U : forall (bp : Z) q' m v0 v8 v16 v24 v32 wb junk
         x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x28 x29 x30 x31,
  minvU q' m 248 v0 v8 v16 v24 v32 (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvU m junk -> 0 <= bp -> bp + 1 < ulen ->
  evt asegs (postU XALL)
    (USTP 0x8da14 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) (Z_to_bv 64 (Z.lxor U 18446744073709551615)) (Z_to_bv 64 F) x23 (Z_to_bv 64 O) x25 (Z_to_bv 64 bp) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP BPL.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (munch_refl [(q' + 24, q' + 32)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step.
  step; fix_lit_store.
  step.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 24) (q' + 32) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  step.   ubr.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (hpU (bp + 2) 443 q' mm v0 v8 v16 v32 wb junk); [mv_tacU| pv_tacU| lia| right; reflexivity] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma slashU : forall (bp sbuf ssize : Z) q' m v0 v8 v32 wb ja jc
    x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31,
  minvU q' m 248 v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) v32 (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvR m ->
  rw_cells asegs m O [CB 8 ja] -> rw_cells asegs m (O + 8) [C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 ssize)] -> rw_cells asegs m (O + 24) [CB 192 jc] ->
  0 <= bp -> bp + 1 < ulen -> 0 <= ssize < 2^64 -> (ssize = 5 -> sbuf = U /\ 5 <= ulen) ->
  evt asegs (postU XALL)
    (USTP 0x8d678 q' x1 x5 x6 x7 x10 (Z_to_bv 64 (bp + 1)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 bp) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PR O1 O2 O3 BP0 BP1 SS HS.
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j64 & QC) & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & FK & AE & _).
  pose proof PR as PR'. destruct PR' as (TXT & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHWT : shw m U (ulen + 1)) by (apply (shwU_now m _ _ MU); lia).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (OUTJ : exists junk, rw_cells asegs m O [CB 216 junk]).
  { replace (O + 24) with (O + Z.of_nat 8 + Z.of_nat 16) in O3 by lia. exact (out_close m 8 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)). }
  assert (NOHP : forall y1 y10 y11 y12 y13 y21, evt asegs (postU XALL)
            (USTP 0x8d7b8 q' y1 x5 x6 x7 y10 y11 y12 y13 x14 x15 x16 x17 (Z_to_bv 64 F) y21 (Z_to_bv 64 F) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 bp) x28 x29 x30 x31 m)).
  { intros y1 y10 y11 y12 y13 y21. destruct OUTJ as [junk OUT]. eapply evt_mono; [apply (nohpU bp q' m 248 v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) v32 (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk); [exact INV| split; [exact OUT| exact PR]| lia]|].
    intros ms' H. exact (postU_mono _ _ ms' XOK_ALL H). }
  destruct (nth_UA bp ltac:(lia)) as [b0 Hb0]. destruct (nth_UA (bp + 1) ltac:(lia)) as [b1 Hb1].
  pose proof (u8ro_read asegs m U _ bp b0 (Z_to_bv 64 (U + bp)) TXT Hb0 ltac:(lia) eq_refl) as RD0.
  pose proof (u8ro_read asegs m U _ (bp + 1) b1 (Z_to_bv 64 (U + (bp + 1))) TXT Hb1 ltac:(lia) eq_refl) as RD1.
  step.
  step. ubr.
  zstep. zstep. ub_b2z. step. lit_branch_safe.
  ub_null.
  step. step.
  gen2 CONT1 0x8d6a0 12%nat 13%nat.
  { intros yi yj.
    step. step.
    step. if_cases K0; zify_cond K0. { apply NOHP. }
    step.   rewrite (unsigned_lit U) by lia.
    step. ubr.
    step. step. step.
    gen2 CONT2 0x8d6c8 11%nat 12%nat.
    { intros zi zj.
      step. step.
      step. if_cases K1; zify_cond K1. { apply NOHP. }
      step. step. step.
      chk8N 11 (O + 16) SHWO'. step. lit_branch.
      step.
      step.
      step. if_cases K2; zify_cond K2.
      { destruct OUTJ as [junk OUT]. apply (hp80U bp q' m v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) v32 wb junk); [exact INV| split; [exact OUT| exact PR]| lia| lia]. }
      rewrite ?(unsigned_lit ssize) in K2 by lia. rewrite ?unsigned_lit in K2 by lia.
      destruct (HS ltac:(lia)) as [-> UL5].
      step. step. step.
      chk8N 11 (O + 8) SHWO'. step. lit_branch.
      step.
      step. step. step.
      step.
      pose proof (https_bytesA _ MI) as HB6.
      destruct (P0.H_memptr_cmp.strncasecmp_model_some (map (Z_to_bv 8) [104; 116; 116; 112; 115]) (ustr ++ Z_to_bv 8 0 :: slack) [] 5 ltac:(lia)
                  ltac:(rewrite length_app; cbn [length]; lia)) as (v & HM & HV).
      change (map (Z_to_bv 8) [104; 116; 116; 112; 115] ++ [Z_to_bv 8 0]) with https6A in HM.
      assert (SHWH : shw m HTTPS_A 6) by (apply (shwG_now m _ _ SHWHTTPS MU); lia).
      pose proof (bytes_at_bound _ _ _ _ TXT) as TB. rewrite length_app in TB. cbn [length] in TB.
      assert (SHWT5 : shw m U 5) by (apply (shw_sub m U (ulen + 1) U 5 SHWT); lia).
      assert (SHWH5 : shw m HTTPS_A 5) by (apply (shw_sub m HTTPS_A 6 HTTPS_A 5 SHWH); lia).
      eapply evt_cut.
      { eapply (ic_strncasecmp IC) with (A := U) (B := HTTPS_A) (n := 5) (ls := ustr ++ Z_to_bv 8 0 :: slack) (rs := https6A) (v := v) (lo := lo) (q := q');
        [ exact TXT | exact HB6 | exact HM
        | replace (Z.min 5 _) with 5 by (rewrite length_app; cbn [length]; lia); exact (proj1 SHWT5)
        | replace (Z.min 5 _) with 5 by (rewrite length_app; cbn [length]; lia); exact (proj1 (proj2 SHWT5))
        | replace (Z.min 5 _) with 5 by (cbn; lia); exact (proj1 SHWH5)
        | replace (Z.min 5 _) with 5 by (cbn; lia); exact (proj1 (proj2 SHWH5))
        | replace (Z.min 5 _) with 5 by (rewrite length_app; cbn [length]; lia); rng_tac
        | replace (Z.min 5 _) with 5 by (cbn; lia); rng_tac
        | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia
        | left; rewrite length_app; cbn [length]; lia | left; cbn; lia | exact MI | reflexivity | reflexivity | reflexivity | lia ]. }
      intros ms' PO. unfold strncmp_post_A in PO.
      destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & ST' & AE' & TXT' & HB').
      pose proof (stackcallU q' m m' 248 _ _ _ _ _ _ _ _ wb INV MUc WMc MI' ST' AE') as INV2.
      pose proof (pinvR_stack q' m m' Hq PR MUc WMc) as PR2.
      destruct OUTJ as [junk OUT]. pose proof (out_stack q' m m' junk Hq OUT MUc WMc) as OUT2.
      replace (ret_pc (Z_to_bv 64 579356)) with (Z_to_bv 64 579356) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step.   if_cases K3; zify_cond K3.
      - apply (hp443U bp q' m' v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) v32 wb junk); [exact INV2| split; [exact OUT2| exact PR2]| lia| lia].
      - apply (hp80U bp q' m' v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) v32 wb junk); [exact INV2| split; [exact OUT2| exact PR2]| lia| lia]. }
    chkbN 11 (U + (bp + 1)) SHWT kk SHRk Hk.
    destruct Hk as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT2.
    - step. rewrite (sxb_small kk) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT2. }
  chkbN 12 (U + bp) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT1.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT1.
Qed.

#[using="Type"] Lemma zero16_cells : forall m X, rw_cells asegs m X [CB 16 (repeat (Z_to_bv 8 0) 16)] -> rw_cells asegs m X [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m X H. splitcb H 0%nat [8; 8]%nat. recell H 0%nat. recell H 1%nat.
  lazymatch type of H with rw_cells _ _ _ [C8 ?a; C8 ?b] =>
    replace a with (Z_to_bv 64 0) in H by (apply bv_eq; vm_compute; reflexivity);
    replace b with (Z_to_bv 64 0) in H by (apply bv_eq; vm_compute; reflexivity) end.
  exact H.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma noschU : forall q' m v0 v8 wb ja jc
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 248 v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvR m ->
  rw_cells asegs m O [CB 8 ja] -> rw_cells asegs m (O + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells asegs m (O + 24) [CB 192 jc] ->
  evt asegs (postU XALL)
    (USTP 0x8d624 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PR O1 O2 O3.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PR as (TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  pose proof (munch_refl [(O, O + 32)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step.
  step. step.
  chk8N 10 O SHWO'. step. lit_branch.
  step. step.
  step; fix_lit_store.
  assert (AIV : app_ivs [(O, O + 32)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step.
  chk8N 12 (O + 24) SHWO1. step. lit_branch.
  step.
  step; fix_lit_store.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  absorbW MU WM MU0 WM0 (sub_fp_O O (O + 32) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear SHWO' SHWO1 AIV.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q' + 40, q' + 48)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  hideW MU WM.
  step. step. step.
  step.
  zstep. ub_b2z.
  step; fix_lit_store.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 40) (q' + 48) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  destruct (rw_cells_forget asegs _ _ _ O1) as [ja' O1']. destruct (rw_cells_forget asegs _ _ _ O3) as [jc' O3'].
  cbn [cells_size csize Nat.add] in O1', O3'. clear O1 O3.
  step.   if_cases K1; zify_cond K1.
  -
    replace (O + 24) with (O + Z.of_nat 8 + Z.of_nat 16) in O3' by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (out_close mm 8 16 _ _ _ O1' eq_refl O2 eq_refl O3' eq_refl ltac:(lia)) as [junk OUT];
      eapply evt_mono; [apply (nohpU 0 q' mm 248 v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) (Z_to_bv 64 F) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk); [mv_tacU| split; [exact OUT| pr_tacU]| lia]|] end.
    intros ms' H. exact (postU_mono _ _ ms' XOK_ALL H).
  - rewrite ?unsigned_lit in K1 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (slashU 0 0 0 q' mm v0 v8 (Z_to_bv 64 F) wb ja' jc'); [mv_tacU| pr_tacU| exact O1'| exact O2| exact O3'| lia| lia| lia| intros X; exfalso; lia] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma foundschU : forall (i : Z) q' m v0 v8 wb ja jc
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
  minvU q' m 248 v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvR m ->
  rw_cells asegs m O [CB 8 ja] -> rw_cells asegs m (O + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells asegs m (O + 24) [CB 192 jc] ->
  1 <= i < ulen ->
  evt asegs (postU XALL)
    (USTP 0x8d734 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (i + 1)) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PR O1 O2 O3 HI.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PR as (TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (AIV : app_ivs [(O, O + 32)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  pose proof (munch_refl [(O, O + 32)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step. step.
  chk8N 11 (O + 16) SHWO'. step.   step. lit_branch.
  step.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step.
  chk8N 10 (O + 8) SHWO1. step. step. step. step.   step. lit_branch.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO2 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step.
  chk8N 10 O SHWO2. step. lit_branch.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO3 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step. step.
  chk8N 11 (O + 24) SHWO3. step. lit_branch.
  step.
  step; fix_lit_store.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  absorbW MU WM MU0 WM0 (sub_fp_O O (O + 32) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear SHWO' SHWO1 SHWO2 SHWO3 AIV.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q' + 40, q' + 48)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  hideW MU WM.
  step.
  zstep. ub_b2z.
  step; fix_lit_store.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 40) (q' + 48) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  destruct (rw_cells_forget asegs _ _ _ O1) as [ja' O1']. destruct (rw_cells_forget asegs _ _ _ O3) as [jc' O3'].
  cbn [cells_size csize Nat.add] in O1', O3'. clear O1 O3.
  step.   if_cases K1; zify_cond K1.
  - rewrite ?unsigned_lit in K1 by lia.
    replace (Z_to_bv 64 (i + 2)) with (Z_to_bv 64 (i + 1 + 1)) by (f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (slashU (i + 1) U i q' mm v0 v8 (Z_to_bv 64 F) wb ja' jc'); [mv_tacU| pr_tacU| exact O1'| exact O2| exact O3'| lia| lia| lia| intros X; split; [reflexivity| lia]] end.
  - replace (O + 24) with (O + Z.of_nat 8 + Z.of_nat 16) in O3' by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (out_close mm 8 16 _ _ _ O1' eq_refl O2 eq_refl O3' eq_refl ltac:(lia)) as [junk OUT];
      eapply evt_mono; [apply (nohpU (i + 1) q' mm 248 v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) (Z_to_bv 64 F) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk); [mv_tacU| split; [exact OUT| pr_tacU]| lia]|] end.
    intros ms' H. exact (postU_mono _ _ ms' XOK_ALL H).
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma schloopU : forall (k : nat) (i : Z) q' m v0 v8 wb ja jc
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31,
  ulen - i < Z.of_nat k -> 1 <= i < ulen ->
  minvU q' m 248 v0 v8 (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvR m ->
  rw_cells asegs m O [CB 8 ja] -> rw_cells asegs m (O + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells asegs m (O + 24) [CB 192 jc] ->
  evt asegs (postU XALL)
    (USTP 0x8d5c8 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 114349209288704) (Z_to_bv 64 (1 - ulen)) (Z_to_bv 64 (U + 1)) (Z_to_bv 64 58)
          (Z_to_bv 64 2) x25 (Z_to_bv 64 (i + 1)) x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until x31; intros HK HI INV PR O1 O2 O3; [lia|].
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j64 & QC) & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & FK & AE & _).
  pose proof PR as PR'. destruct PR' as (TXT & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHWT : shw m U (ulen + 1)) by (apply (shwU_now m _ _ MU); lia).
  destruct (nth_UA i ltac:(lia)) as [b Hb]. pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.

  assert (NOSCH : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31, evt asegs (postU XALL)
            (USTP 0x8d624 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 m)).
  { intros. apply (noschU q' m v0 v8 wb ja jc); assumption. }
  assert (NEXT : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31, evt asegs (postU XALL)
            (USTP 0x8d5bc q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 114349209288704) (Z_to_bv 64 (1 - ulen)) (Z_to_bv 64 (U + 1)) (Z_to_bv 64 58)
                  (Z_to_bv 64 2) y25 (Z_to_bv 64 (i + 1)) y28 y29 y30 y31 m)).
  { intros. step.
    step.
    step.   if_cases K1; zify_cond K1.
    - apply NOSCH.
    - assert (I1 : i + 1 < ulen) by (destruct (Z.eq_dec (i + 1) ulen) as [E|]; [exfalso; apply K1; replace (1 - ulen + (i + 2)) with 2 by lia; reflexivity| lia]).
      clear K1. replace (Z_to_bv 64 (i + 2)) with (Z_to_bv 64 (i + 1 + 1)) by (f_equal; lia).
      apply (IH (i + 1) q' m v0 v8 wb ja jc); try assumption; lia. }
  step. step.
  replace (Z_to_bv 64 (U + (i + 1) + -1)) with (Z_to_bv 64 (U + i)) by (f_equal; lia).
  step. ubr.
  step. step.
  gen2 CONT 0x8d5e4 11%nat 12%nat.
  { intros yi yj.
    step.
    pose proof (u8ro_read asegs m U _ i b (Z_to_bv 64 (U + 1 + (i + 1) + -2)) TXT Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    step.
    step.   if_cases K2; zify_cond K2.
    { apply (foundschU i q' m v0 v8 wb ja jc); assumption. }
    step. ubr.
    step.   step.
    eapply evt_cut.
    { eapply (isalnum_spec_A); [unfold zxb; rewrite unsigned_lit by lia; lia| exact MI]. }
    intros ms' PO. unfold ctype_post_A in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & _ & _ & _).
    replace (ret_pc (Z_to_bv 64 579068)) with (Z_to_bv 64 579068) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step.   if_cases K3; zify_cond K3.
    { apply NEXT. }
    step.
    step.   if_cases K4; zify_cond K4.
    { apply NOSCH. }
    step. step.
    step.   if_cases K5; zify_cond K5.
    { apply NEXT. }
    step.   apply NOSCH. }
  chkbN 11 (U + i) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma bodyU : forall q' m v0 v8 v16 v24 v32 v40 v48 v56 wb junk
    x1 x5 x6 x7 x11 x12 x13 x14 x16 x17 x22 x23 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 248 v0 v8 v16 v24 v32 v40 v48 v56 wb -> pinvU m junk ->
  evt asegs (postU XALL)
    (USTP 0x8d524 q' x1 x5 x6 x7 (Z_to_bv 64 F) x11 x12 x13 x14 (Z_to_bv 64 F) x16 x17 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  pose proof (munch_refl [(q' + 8, q' + 56)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  ub_null.
  step.
  replace (Z.land (bv_unsigned (Z_to_bv 64 O)) 7) with 0 by (symmetry; rewrite unsigned_lit by lia; rewrite land7_mod8; clear - OAL; Z.div_mod_to_equations; lia).
  step; fix_lit_store.
  step. lit_branch.
  step; fix_lit_store.
  step; fix_lit_store.
  step.
  step; fix_lit_store.
  step.
  step; fix_lit_store.
  step.
  step; fix_lit_store.
  step.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 8) (q' + 56) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (memsetOo 8 16 0x8d558 q' mm 248 v0 (Z_to_bv 64 0) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 O) v56 wb junk);
      [mv_tacU| pv_tacU| lia| lia| apply ret_pc_even; [lia| reflexivity]|] end.
  clear - CLO LO AL16 QHI Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV RF0 FCO FE0 SHZ SHR IC STACK_MALLOC_3 SET_SHADOW_F5.
  intros m' ja jc y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV PR O1 O2 O3.
  apply zero16_cells in O2. change (O + Z.of_nat 8) with (O + 8) in O2.
  change (216 - 8 - 16)%nat with 192%nat in O3. replace (O + Z.of_nat 8 + Z.of_nat 16) with (O + 24) in O3 by lia.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PR as (TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  pose proof (munch_refl [(q' + 56, q' + 64)]%Z m') as MU0. pose proof (wmono_refl asegs m') as WM0.
  hideW MU WM.
  step; fix_lit_store.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 56) (q' + 64) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (INV2 : minvU q' mm 248 v0 (Z_to_bv 64 0) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (O + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb) by mv_tacU;
    assert (PR2 : pinvR mm) by pr_tacU;
    assert (SHWT : shw mm U (ulen + 1)) by (apply (shwU_now mm _ _ MU); lia) end.
  assert (NOSCH : forall y1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z20 z21 z22 z23 z24 z25 z26 z28 z29 z30 z31, evt asegs (postU XALL)
            (USTP 0x8d624 q' y1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z20 z21 z22 z23 z24 z25 z26 z28 z29 z30 z31 m)).
  { intros. apply (noschU q' m v0 (Z_to_bv 64 0) wb ja jc); assumption. }
  step.   if_cases K0; zify_cond K0.
  { apply NOSCH. }
  rewrite ?unsigned_lit in K0 by lia.
  ub_null.
  destruct (nth_UA 0 ltac:(lia)) as [b Hb].
  pose proof (u8ro_read asegs m U _ 0 b (Z_to_bv 64 U) TXT Hb ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. step.
  gen3v CONT 0x8d578 10%nat 11%nat 12%nat (Z_to_bv 64 ulen).
  { intros yi yj.
    step.
    step.   if_cases K1; zify_cond K1.
    { apply NOSCH. }
    rewrite ?unsigned_lit in K1 by lia.
    step.
    step. step. step.
    step.   if_cases K2; zify_cond K2.
    { apply NOSCH. }
    step. step. step. step. step.
    step.
    step.
    step. step.
    step.
    rewrite (unsigned_lit ulen) by lia.
    apply (schloopU (Datatypes.S (Z.to_nat ulen)) 1 q' m v0 (Z_to_bv 64 0) wb ja jc); try assumption; lia. }
  chkbN 10 U SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step.   step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="ulen CLO RF0 OLB ULEN ULR UHI UFS UBAND"] Lemma pinvU_pro : forall m junk,
  pinvU m0 junk -> munch ((lo, q) :: FSIV [])%Z m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m -> pinvU m junk.
Proof.
  intros m junk (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)) MU WM FK.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  assert (DJL : forall X n, 0 <= n -> X + n <= 0x609000 -> disjoint_from ((lo, q) :: FSIV [])%Z X n).
  { intros X n H0 H1. cbn [disjoint_from]. repeat (split; [left; clear - H0 H1 CLO ACR FSB1 ESHB EKB; lia|]). exact I. }
  unfold H_puri_seg1.pinvU, pinvR.
  split; [apply (rw_cells_fkeep FI [] st m0 m _ _ OUT FK WM); [left; apply (lb_sub _ O 216 _ _ OLB); cbn [cells_size csize Nat.add]; lia| exact I]|].
  split; [apply (bytes_at_transport asegs _ m0 m _ _ TXT MU); rewrite length_app; cbn [length disjoint_from];
          split; [left; clear - UHI CLO ULEN; lia|]; split; [clear - UFS ULEN; lia|]; split; [clear - UBu ULEN ESHB EKB FSB1 FSB2 ACR; lia| exact I]|].
  split; [exists ev; apply (rw_cells_transport asegs _ m0 m _ _ ERRC MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m0 m _ _ SSPG MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m0 m _ _ SSPC MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m0 m _ _ GOTG MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  exists gv. apply (rw_cells_transport asegs _ m0 m _ _ GIFC MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

#[using="IC STACK_MALLOC_3 SET_SHADOW_F5 kq kO CLO LO AL16 QHI RF0 FCO FE0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma puri_evt : forall junk t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 -> pinvU m0 junk ->
  evt asegs (postU XALL)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 U) (Z_to_bv 64 ulen) (Z_to_bv 64 O) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 puri_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros junk t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE PINV.
  apply (prologueU t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE).
  intros q' m v0 v8 v16 v24 v32 v40 v48 v56 wb x1 x5 x6 x7 x11 x12 x13 x14 x16 x17 x28 x29 x30 x31 MV MUP FKP.
  assert (PV : pinvU m junk).
  { destruct MV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WM & _). exact (pinvU_pro m junk PINV MUP WM FKP). }
  apply (bodyU q' m v0 v8 v16 v24 v32 v40 v48 v56 wb junk); [exact MV| exact PV].
Qed.

End W.
