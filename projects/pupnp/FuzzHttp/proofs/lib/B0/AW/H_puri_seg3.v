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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import H_puri_seg1 H_puri_seg2.

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

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v4exitU : forall (bp2 z j ld defport s8v s10v : Z) (bc : byte) q' m wb junk
    x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk ->
  0 <= bp2 -> 0 <= j <= z -> z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  nth_error wb (Z.to_nat j) = Some bc ->
  (ld = 0 \/ exists d, ld = F + 32 + d /\ 0 <= d < j) ->
  s8v = F + 32 + j -> s10v = F + 32 + j + 1 ->
  evt asegs (postU XALL)
    (USTP 0x8dbe0 q' x1 (Z_to_bv 64 (F + 32)) x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) (zxb bc) (Z_to_bv 64 F) (Z_to_bv 64 ld) (Z_to_bv 64 s8v) x25 (Z_to_bv 64 s10v) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP JZ Z255 BPZ DP WZ WNZ Hbc LD -> ->.
  lazymatch type of LD with ?T => change (hid2 T) in LD end.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  pose proof (bv_unsigned_in_range 8 bc) as BR. unfold bv_modulus in BR. cbn in BR.
  assert (HJ255 : 0 <= j <= 255) by lia.
  pose proof (munch_refl [(F + 32 + j, F + 32 + j + 1)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  destruct (cb_split1 m (F + 32) 256 wb (Z.to_nat j) bc WBC Hbc ltac:(lia)) as [TX1 TX23]. clear WBC.
  rewrite Z2Nat.id in TX23 by lia.
  remember (256 - Z.to_nat j - 1)%nat as nr eqn:Enr.
  step. step.
  chkW 10 j SHF HJ255.
  step. lit_branch.
  step.
  step.
  remember (F + 32 + j) as V eqn:EV.
  step; fix_lit_store.
  subst V.
  apply (rw_cells_reshape asegs _ _ _ [CB 1 [zbU]; CB nr (skipn (Z.to_nat j + 1) wb)]) in TX23;
    [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
  subst nr.
  pose proof (cb_join1 _ (F + 32) 256 wb (Z.to_nat j) zbU TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) LWB) as WBC.
  clear TX1 TX23.
  absorbW MU WM MU0 WM0 (sub_fp_F (F + 32 + j) (F + 32 + j + 1) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.

  assert (LW' : length (setb wb (Z.to_nat j) zbU) = 256%nat) by (rewrite setb_length; lia).
  assert (WZj : nth_error (setb wb (Z.to_nat j) zbU) (Z.to_nat j) = Some zbU) by (apply setb_same; lia).
  assert (WOTH : forall i, i <> Z.to_nat j -> nth_error (setb wb (Z.to_nat j) zbU) i = nth_error wb i) by (intros i Hi; apply setb_other; lia).
  set (wb' := setb wb (Z.to_nat j) zbU) in *. clearbody wb'.
  assert (WNZh : forall j' b, 0 <= j' < j -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
  destruct (wb_decomp wb' 0 j ltac:(lia) WZj WNZh) as (pre & host & rest & EWB & LPRE & LHOST & NONUL).
  assert (JLT : bv_unsigned bc <> 0 -> j < z).
  { intros Hc0. destruct (Z.eq_dec j z) as [E|]; [|lia]. exfalso. subst j. rewrite WZ in Hbc. injection Hbc as <-. apply Hc0. reflexivity. }
  assert (WZ' : j < z -> nth_error wb' (Z.to_nat z) = Some zbU) by (intros Hjz; rewrite WOTH by lia; exact WZ).
  assert (WNZ' : forall j' b, j + 1 <= j' < z -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
  clear WNZh WNZ WZ Hbc.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (DIG : forall d e y10 y11, 0 <= d < j -> (bv_unsigned bc = 58 -> e = j + 1) -> (bv_unsigned bc <> 58 -> e = j) ->
            evt asegs (postU XALL)
              (USTP 0x8dc20 q' x1 (Z_to_bv 64 (F + 32)) x6 x7 y10 y11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) (zxb bc) (Z_to_bv 64 F) (Z_to_bv 64 (F + 32 + d)) (Z_to_bv 64 (F + 32 + j)) x25 (Z_to_bv 64 (F + 32 + e)) x28 x29 x30 x31 mm)) end.
  { intros d e y10 y11 Hd E1 E2. clear LD.
    lazymatch type of E1 with ?T => change (hid2 T) in E1 end. lazymatch type of E2 with ?T => change (hid2 T) in E2 end.
    pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
    destruct (wb_nthU wb' (d + 1) LW' ltac:(lia)) as [bd Hbd]. pose proof (bv_unsigned_in_range 8 bd) as BRd. unfold bv_modulus in BRd. cbn in BRd.
    lazymatch type of WBB with bytes_at _ ?mm _ _ =>
      pose proof (u8ro_read asegs mm (F + 32) wb' (d + 1) bd (Z_to_bv 64 (F + 32 + d + 1)) WBB Hbd ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    assert (HD255 : 0 <= d + 1 <= 255) by lia.
    step.
    step. ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia).
    step. step. step.
    chkW 11 (d + 1) SHF HD255.
    step. lit_branch.
    step.
    step. step. step. step.
    lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned (v_sltiu ?x 10) ≪ 1)] =>
      assert (EF : exists fam, 0 <= fam < 2^64 /\ Z_to_bv 64 (bv_unsigned (v_sltiu x 10) ≪ 1) = Z_to_bv 64 fam)
        by (unfold v_sltiu; destruct (bv_unsigned x <? bv_wrap 64 10); [exists 2| exists 0]; (split; [lia| reflexivity])) end.
    destruct EF as (fam & HF & ->).
    step.
    clear RD WBB.
    step.   if_cases K1; zify_cond K1.
    + rewrite (unsigned_lit (bv_unsigned bc)) in K1 by lia. unfold hid2 in E1. rewrite (E1 K1).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (portU bp2 (j + 1) z fam (F + 32) pre host rest q' mm (Z_to_bv 64 defport) wb' junk);
          [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia| apply WZ'; lia| exact WNZ'] end.
    + rewrite (unsigned_lit (bv_unsigned bc)) in K1 by lia. unfold hid2 in E2. rewrite (E2 K1). clear K1. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (portfamU bp2 j fam defport (F + 32) pre host rest q' mm wb' junk);
          [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia] end. }
  step.   if_cases K1; zify_cond K1.
  -
    rewrite (unsigned_lit (bv_unsigned bc)) in K1 by lia.
    unfold hid2 in LD. destruct LD as [-> | (d & -> & Hd)].
    + clear DIG. step.   lit_branch.
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (portfamU bp2 j 0 defport (F + 32) pre host rest q' mm wb' junk);
          [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia] end.
    + step.   if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
      step.
      apply (DIG d j); [lia| intros X; exfalso; lia| reflexivity].
  -
    rewrite (unsigned_lit (bv_unsigned bc)) in K1 by lia.
    step.
    step. ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia).
    unfold hid2 in LD. destruct LD as [-> | (d & -> & Hd)].
    + clear DIG. step.   lit_branch.
      step. step. step.
      replace (Z_to_bv 64 (F + 32 + j + 1)) with (Z_to_bv 64 (F + 32 + (j + 1))) by (f_equal; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (portU bp2 (j + 1) z 0 (F + 32) pre host rest q' mm (Z_to_bv 64 defport) wb' junk);
          [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia| apply WZ'; lia| exact WNZ'] end.
    + step.   if_cases K0; zify_cond K0; [| exfalso; lia]. clear K0.
      replace (Z_to_bv 64 (F + 32 + j + 1)) with (Z_to_bv 64 (F + 32 + (j + 1))) by (f_equal; lia).
      apply (DIG d (j + 1)); [lia| reflexivity| intros X; exfalso; lia].
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v4loopU : forall (k : nat) (bp2 z j ld defport s8v s10v : Z) (bc : byte) q' m wb junk
    x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  z - j < Z.of_nat k ->
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk ->
  0 <= bp2 -> 0 <= j <= z -> z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  nth_error wb (Z.to_nat j) = Some bc ->
  (ld = 0 \/ exists d, ld = F + 32 + d /\ 0 <= d < j) ->
  s8v = F + 32 + j -> s10v = F + 32 + j + 1 ->
  evt asegs (postU XALL)
    (USTP 0x8db68 q' x1 (Z_to_bv 64 (F + 32)) x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) (zxb bc) (Z_to_bv 64 F) (Z_to_bv 64 ld) (Z_to_bv 64 s8v) (Z_to_bv 64 47) (Z_to_bv 64 s10v) x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until x31; intros HK INV PINV BP JZ Z255 BPZ DP WZ WNZ Hbc LD ES8 ES10; [lia|]. subst s8v s10v.
  lazymatch type of LD with ?T => change (hid2 T) in LD end.
  pose proof INV as INV'.
  destruct INV' as (_ & Hq & _ & (j64 & QC) & WBC & _ & _ & _ & _ & SHF & _ & MI & _).
  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  clear WBC.
  pose proof (bv_unsigned_in_range 8 bc) as BR. unfold bv_modulus in BR. cbn in BR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & _ & PFS1 & PFS2 & FSB1 & FSB2 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.

  assert (EXIT : forall y1 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31, evt asegs (postU XALL)
            (USTP 0x8dbe0 q' y1 (Z_to_bv 64 (F + 32)) y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 F) (zxb bc) (Z_to_bv 64 F) (Z_to_bv 64 ld) (Z_to_bv 64 (F + 32 + j)) (Z_to_bv 64 47) (Z_to_bv 64 (F + 32 + j + 1)) y28 y29 y30 y31 m)).
  { intros. apply (v4exitU bp2 z j ld defport (F + 32 + j) (F + 32 + j + 1) bc q' m wb junk); first [assumption | reflexivity]. }
  step.
  step.   if_cases K1; zify_cond K1.
  { apply EXIT. }
  step.
  step.
  replace (Z.land (bv_unsigned (zxb bc)) 255) with (bv_unsigned bc)
    by (unfold zxb; rewrite unsigned_lit by lia; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  eapply evt_cut.
  { eapply (isalnum_spec_A); [rewrite unsigned_lit by lia; lia| exact MI]. }
  intros ms' PO. unfold ctype_post_A in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & _ & _ & _).
  replace (ret_pc (Z_to_bv 64 580472)) with (Z_to_bv 64 580472) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite (unsigned_lit (bv_unsigned bc)) by lia.
  step.
  clear QC.
  assert (CONT4c : forall (ld' : Z) z11 z12, bv_unsigned bc <> 0 ->
            hid2 (ld' = 0 \/ exists d, ld' = F + 32 + d /\ 0 <= d < j + 1) ->
            evt asegs (postU XALL)
              (USTP 0x8dba4 q' (Z_to_bv 64 580472) (Z_to_bv 64 (F + 32)) y6 y7 (Z_to_bv 64 ld') z11 z12 y13 y14 y15 y16 y17 (Z_to_bv 64 F) (zxb bc) (Z_to_bv 64 F) (Z_to_bv 64 ld) (Z_to_bv 64 (F + 32 + j)) (Z_to_bv 64 47) (Z_to_bv 64 (F + 32 + j + 1)) y28 y29 y30 y31 m)).
  { intros ld' z11 z12 BNZ LD'.
    assert (JLT : j < z). { destruct (Z.eq_dec j z) as [E|]; [|lia]. exfalso. subst j. rewrite WZ in Hbc. injection Hbc as <-. apply BNZ. reflexivity. }
    destruct (wb_nthU wb (j + 1) LWB ltac:(lia)) as [bn Hbn]. pose proof (bv_unsigned_in_range 8 bn) as BRn. unfold bv_modulus in BRn. cbn in BRn.
    pose proof (u8ro_read asegs m (F + 32) wb (j + 1) bn (Z_to_bv 64 (F + 32 + j + 1)) WBB Hbn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    assert (HJ1 : 0 <= j + 1 <= 255) by lia.
    step. step. step.
    chkW 12 (j + 1) SHF HJ1.
    step. lit_branch.
    step.
    step. step. step.
    step.   if_cases K5; zify_cond K5.
    - clear K5. unfold hid2 in LD'. apply (IH bp2 z (j + 1) ld' defport _ _ bn q' m wb junk); first [assumption | lia].
    - clear K5. step.   unfold hid2 in LD'. apply (v4exitU bp2 z (j + 1) ld' defport _ _ bn q' m wb junk); first [assumption | lia]. }
  assert (CONT40 : forall z10 z11 z12, bv_unsigned bc <> 0 ->
            evt asegs (postU XALL)
              (USTP 0x8db8c q' (Z_to_bv 64 580472) (Z_to_bv 64 (F + 32)) y6 y7 z10 z11 z12 y13 y14 y15 y16 y17 (Z_to_bv 64 F) (zxb bc) (Z_to_bv 64 F) (Z_to_bv 64 ld) (Z_to_bv 64 (F + 32 + j)) (Z_to_bv 64 47) (Z_to_bv 64 (F + 32 + j + 1)) y28 y29 y30 y31 m)).
  { intros z10 z11 z12 BNZ.
    step.   step.
    step. ubr_by ltac:(rewrite ?unsigned_lit_wrap in KU; change ((-1) mod 18446744073709551616) with 18446744073709551615 in KU; lia).
    step.
    step.   if_cases K4; zify_cond K4.
    - clear K4. replace (Z_to_bv 64 (F + 32 + j + 1 + -1)) with (Z_to_bv 64 (F + 32 + j)) by (f_equal; lia).
      apply (CONT4c (F + 32 + j)); [exact BNZ|]. unfold hid2. right. exists j. split; [reflexivity| lia].
    - clear K4. step.
      apply (CONT4c ld); [exact BNZ|]. unfold hid2 in *. destruct LD as [L0 | (d & L1 & L2)]; [left; exact L0| right; exists d; split; [exact L1| lia]]. }
  step. step.
  step.   if_cases K2; zify_cond K2.
  { apply CONT40. intros E0. rewrite E0 in K2. vm_compute in K2. discriminate K2. }
  clear K2.
  step.   if_cases K3; zify_cond K3.
  { apply EXIT. }
  apply CONT40. intros E0. rewrite E0 in K3. discriminate K3.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v4U : forall (bp2 z defport : Z) (b0 : byte) q' m wb junk
    x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk ->
  0 <= bp2 -> 0 <= z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  nth_error wb 0%nat = Some b0 ->
  evt asegs (postU XALL)
    (USTP 0x8db54 q' x1 (Z_to_bv 64 (F + 32)) x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) (zxb b0) (Z_to_bv 64 F) x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP Z255 BPZ DP WZ WNZ Hb0.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & _ & PFS1 & PFS2 & FSB1 & FSB2 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bv_unsigned_in_range 8 b0) as BR. unfold bv_modulus in BR. cbn in BR.
  step. step. step. step.
  step.   if_cases K0; zify_cond K0.
  - clear K0.
    apply (v4exitU bp2 z 0 0 defport _ _ b0 q' m wb junk); first [assumption | lia | (left; reflexivity)].
  - clear K0.
    apply (v4loopU (S (Z.to_nat z)) bp2 z 0 0 defport _ _ b0 q' m wb junk); first [assumption | lia | (left; reflexivity)].
Qed.

#[using="HC FI U ulen lo ustr slack ULR UFS"] Lemma nul_splitU : forall (l1 l2 : list byte), exists s r, l1 ++ zbU :: l2 = s ++ zbU :: r /\ ~ In zbU s /\ (length s <= length l1)%nat.
Proof.
  induction l1 as [|a l1 IH]; intros l2.
  - exists [], l2. cbn. repeat split; [LiaTuning.ctauto| lia].
  - destruct (Z.eq_dec (bv_unsigned a) 0) as [E|NE].
    + exists [], (l1 ++ zbU :: l2). assert (a = zbU) as -> by (apply bv_eq; rewrite E; reflexivity).
      cbn. repeat split; [LiaTuning.ctauto| lia].
    + destruct (IH l2) as (s & r & E & NI & L). exists (a :: s), r. cbn. rewrite E. repeat split; [| cbn in *; lia].
      intros [H|H]; [| exact (NI H)]. apply NE. subst a. reflexivity.
Qed.
#[using="U ulen lo ustr slack ULR"] Lemma mod8_shiftU : forall x d, 0 <= d -> (x + d) mod 8 <= x mod 8 + d.
Proof. intros x d Hd. rewrite <- Z.add_mod_idemp_l by lia. apply Z.mod_le; [| lia]. pose proof (Z.mod_pos_bound x 8). lia. Qed.
#[using="U ulen lo ustr slack ULR"] Lemma stpnA_length : forall (str : list byte), length (stpn_result_A str 255) = 255%nat.
Proof. intros str. unfold stpn_result_A, stpn_k_A. rewrite length_app, firstn_length, repeat_length. lia. Qed.
#[using="U ulen lo ustr slack ULR"] Lemma stpnA_nth_lt : forall (str : list byte) j, (j < stpn_k_A str 255)%nat -> nth_error (stpn_result_A str 255 ++ [zbU]) j = nth_error str j.
Proof.
  intros str j Hj. unfold stpn_result_A. pose proof (Nat.le_min_l (length str) 255). unfold stpn_k_A in *.
  rewrite nth_error_app1. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
  rewrite nth_error_app1 by (rewrite firstn_length; lia).
  rewrite nth_error_firstn. destruct (Nat.ltb_spec0 j (Nat.min (length str) 255)); [reflexivity| lia].
Qed.
#[using="U ulen lo ustr slack ULR"] Lemma stpnA_nth_z : forall (str : list byte), nth_error (stpn_result_A str 255 ++ [zbU]) (stpn_k_A str 255) = Some zbU.
Proof.
  intros str. unfold stpn_result_A. pose proof (Nat.le_min_l (length str) 255). pose proof (Nat.le_min_r (length str) 255). unfold stpn_k_A in *.
  set (k := Nat.min (length str) 255) in *.
  destruct (Nat.eq_dec k 255).
  - rewrite nth_error_app2. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
    rewrite length_app, firstn_length, repeat_length. replace (k - (Nat.min k (length str) + (255 - k)))%nat with 0%nat by lia. reflexivity.
  - rewrite nth_error_app1. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
    rewrite nth_error_app2 by (rewrite firstn_length; lia). rewrite firstn_length.
    replace (k - Nat.min k (length str))%nat with 0%nat by lia.
    destruct (255 - k)%nat eqn:E; [lia|]. reflexivity.
Qed.

#[using="U ulen lo ustr slack ULR"] Lemma wb_join255 : forall m (xs : list byte), rw_cells asegs m (F + 32) [CB 255 xs] -> rw_cells asegs m (F + 287) [CB 1 [zbU]] ->
  rw_cells asegs m (F + 32) [CB 256 (xs ++ [zbU])].
Proof.
  intros m xs W1 W2.
  pose proof (proj2 (rw_cells_app asegs m (F + 32) [CB 255 xs] [CB 1 [zbU]])) as J.
  cbn [cells_size csize Nat.add] in J. replace (F + 32 + Z.of_nat 255) with (F + 287) in J by lia.
  specialize (J (conj W1 W2)). cbn [app] in J.
  pose proof (rw_cells_merge asegs m (F + 32) [] [CB 255 xs; CB 1 [zbU]] []) as M.
  rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  specialize (M J). exact M.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma hpBU : forall (bp2 defport : Z) q' m v8 v32 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 bp2) v8 (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) v32 (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb ->
  pinvU m junk -> 0 <= bp2 <= ulen -> 0 <= defport < 2^16 ->
  evt asegs (postU XALL)
    (USTP 0x8dac4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 F) x23 x24 x25 (Z_to_bv 64 (U + bp2)) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP DP.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.

  destruct (nul_splitU (skipn (Z.to_nat bp2) ustr) slack) as (str & rest & ES & NI & LS). rewrite length_skipn in LS.
  assert (LR : Z.of_nat (length rest) = ulen - bp2 - Z.of_nat (length str) + Z.of_nat (length slack)).
  { pose proof (f_equal (@length byte) ES) as EL. rewrite !length_app, length_skipn in EL. cbn [length] in EL. lia. }
  assert (PAD' : (- (U + bp2 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length rest)).
  { replace (- (U + bp2 + Z.of_nat (length str) + 1)) with (- (U + ulen + 1) + (ulen - bp2 - Z.of_nat (length str))) by lia.
    etransitivity; [apply mod8_shiftU; lia|]. lia. }
  assert (SHWs : shw m (U + bp2) (Z.min 255 (Z.of_nat (length str) + 1))) by (apply (shwU_now m _ _ MU); lia).
  assert (SHWd : shw m (F + 32) 255) by (apply (shw_sub m (F + 32) 256 _ _ (shwW_now m SHF)); lia).
  splitcb WBC 0%nat [255; 1]%nat. name_junk WBC. split_chunk WBC 1%nat WB1 WB2.
  assert (SRC : bytes_at asegs m (U + bp2) (str ++ zbU :: rest)).
  { rewrite <- ES. pose proof TXT as T. rewrite <- (firstn_skipn (Z.to_nat bp2) (ustr ++ zbU :: slack)) in T. apply bytes_at_app in T. destruct T as [_ T].
    rewrite firstn_length, Nat.min_l in T by (rewrite length_app; cbn [length]; lia). rewrite Z2Nat.id in T by lia.
    rewrite skipn_app in T. replace (Z.to_nat bp2 - length ustr)%nat with 0%nat in T by lia. cbn [skipn] in T. exact T. }
  pose proof (munch_refl [(F + 287, F + 288); (q' + 8, q' + 16)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step; fix_lit_store.
  step. step.
  step; fix_lit_store.
  step.
  step.
  clear SHWs SHWd.
  absorbW MU WM MU0 WM0 (sub_fp_cons2 _ _ W0 (sub_fp_F (F + 287) (F + 288) ltac:(lia) ltac:(lia)) (sub_fp_stk (q' + 8) (q' + 16) ltac:(lia) ltac:(lia))).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SHWs : shw mm (U + bp2) (Z.min 255 (Z.of_nat (length str) + 1))) by (apply (shwU_now mm _ _ MU); lia);
    assert (SHWd : shw mm (F + 32) 255) by (apply (shw_sub mm (F + 32) 256 _ _ (shwW_now mm SHF)); lia) end.
  hideW MU WM.
  eapply evt_cut.
  { eapply (ic_strncpy IC) with (D := F + 32) (S := U + bp2) (n := 255) (str := str) (slack := rest) (lo := lo) (q := q');
    [ exact WB1 | lia | exact SRC | exact NI | exact PAD'
    | exact (proj1 SHWs) | exact (proj1 (proj2 SHWs)) | exact (proj2 (proj2 SHWs))
    | exact (proj1 SHWd) | exact (proj1 (proj2 SHWd)) | exact (proj2 (proj2 SHWd))
    | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia
    | lia | lia | lia | lia | lia
    | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold strncpy_post_A in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & ST' & AE' & WB1' & _).
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  lazymatch type of MUt with munch _ ?ma _ => clear WB1 ST AE MI SHWs SHWd SRC end.
  lazymatch type of MUt with munch _ ?ma ?mb => transport_after_call asegs ma mb MUt WMt end.
  absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) (sub_fp_F (F + 32) (F + 32 + 255) ltac:(lia) ltac:(lia))).
  clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 580316)) with (Z_to_bv 64 580316) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  change (Z.to_nat 255) with 255%nat in WB1'.
  apply (rw_cells_reshape asegs _ _ _ [CB 1 [zbU]]) in WB2; [| cbn; LiaTuning.ctauto | reflexivity | reflexivity].
  pose proof (wb_join255 _ _ WB1' WB2) as WBC. clear WB1' WB2.

  set (wb' := stpn_result_A str 255 ++ [zbU]) in *.
  assert (LW : length wb' = 256%nat) by (subst wb'; rewrite length_app, stpnA_length; reflexivity).
  set (zn := stpn_k_A str 255).
  assert (ZN : (zn <= length str /\ zn <= 255)%nat) by (subst zn; unfold stpn_k_A; split; [apply Nat.le_min_l| apply Nat.le_min_r]).
  assert (WZ : nth_error wb' (Z.to_nat (Z.of_nat zn)) = Some zbU) by (rewrite Nat2Z.id; subst wb' zn; apply stpnA_nth_z).
  assert (WNZ : forall j' b, 0 <= j' < Z.of_nat zn -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb E0. subst wb'. rewrite stpnA_nth_lt in Hb by (subst zn; lia). apply NI.
    assert (b = zbU) as <- by (apply bv_eq; rewrite E0; reflexivity). eapply nth_error_In. exact Hb. }
  clearbody wb' zn.
  destruct (wb_nthU wb' 0 LW ltac:(lia)) as [b0 Hb0]. change (Z.to_nat 0) with 0%nat in Hb0.
  pose proof (bv_unsigned_in_range 8 b0) as BR0. unfold bv_modulus in BR0. cbn in BR0.
  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  pose proof (u8ro_read asegs m' (F + 32) wb' 0 b0 (Z_to_bv 64 (F + 32)) WBB Hb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  pose proof (munch_refl [(q' + 32, q' + 40)]%Z m') as MU0. pose proof (wmono_refl asegs m') as WM0.
  hideW MU WM.
  step.
  hide WBC. step.   unhide WBC.
  step.
  step; fix_lit_store.
  clear RD WBB.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 32) (q' + 40) ltac:(lia) ltac:(lia)).
  env_sync AE' MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  step.   if_cases K0; zify_cond K0.
  - clear K0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (v4U bp2 (Z.of_nat zn) defport b0 q' mm wb' junk);
        [mv_tacU| pv_tacU| lia| lia| lia| lia| exact WZ| exact WNZ| exact Hb0] end.
  - rewrite (unsigned_lit (bv_unsigned b0)) in K0 by lia.
    assert (Z1 : 1 <= Z.of_nat zn).
    { destruct zn as [|zn']; [| lia]. exfalso. change (Z.to_nat (Z.of_nat 0)) with 0%nat in WZ. rewrite WZ in Hb0. injection Hb0 as E0. subst b0. vm_compute in K0. discriminate K0. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (v6U bp2 (Z.of_nat zn) defport q' mm wb' junk);
        [mv_tacU| pv_tacU| lia| lia| lia| lia| exact WZ| exact WNZ] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma hpU : forall (bp2 defport : Z) q' m v0 v8 v16 v32 wb junk
         x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x25 x28 x29 x30 x31,
  minvU q' m 248 v0 v8 v16 (Z_to_bv 64 defport) v32 (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb -> pinvU m junk -> 0 <= bp2 <= ulen -> (defport = 80 \/ defport = 443) ->
  evt asegs (postU XALL)
    (USTP 0x8da24 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) x23 (Z_to_bv 64 O) x25 (Z_to_bv 64 bp2) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP DPd.
  assert (DP : 0 <= defport < 2^16) by lia. clear DPd.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold H_puri_seg1.UBANDd in UBu.
  pose proof (munch_refl [(q', q' + 8)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step.
  step; fix_lit_store.
  step. step.
  absorbW MU WM MU0 WM0 (sub_fp_stk q' (q' + 8) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.

  hideW MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 32 sstep.
  unhide_transport MUs WMs.
  pose proof sub_fp_SF as SFS. absorbW MU WM MUs WMs SFS. clear SFS.
  env_sync AE MUs WMs. fs_sync FI RF MUs WMs FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q' + 16, q' + 24)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  hideW MU WM.
  step.
  step; fix_lit_store.
  step.
  step.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 16) (q' + 24) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (memsetO 64 152 0x8dac4 q' mm 0 (Z_to_bv 64 bp2) v8 (Z_to_bv 64 (O + 64)) (Z_to_bv 64 defport) v32 (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) wb junk);
      [mv_tacU| pv_tacU| lia| lia| apply ret_pc_even; [lia| reflexivity]|] end.
  intros m' junk' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV2 PINV2.
  apply (hpBU bp2 defport q' m' v8 v32 wb junk'); [exact INV2| exact PINV2| lia| lia].
Qed.

End W.
