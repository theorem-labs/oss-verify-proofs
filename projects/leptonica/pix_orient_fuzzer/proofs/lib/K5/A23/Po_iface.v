(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk D_iface D_defs Bi_fktw Bi_fkweak Bi_iface2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Po_rows.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_iface () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List9fold_leftC46Stdlib5Lists4List5splitc69OSSVerify5KrLib2K53A238Po_iface5res0dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6p_xresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6p_yresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_dC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53A23:Lept_iface5p_sppC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c69OSSVerify5KrLib2K53A238Po_iface4res0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib2K53A23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib2K53A238Po_ifaceFprocessMorphArgs1_caseC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A238RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_iface5pix1cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_iface7sel_objC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib2K53A23:Lept_iface3p_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_hC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_iface:pix_chunksC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI46Stdlib5Lists4List5NoDup00C69OSSVerify5KrLib2K53A23:Lept_iface5optrFC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4LSTKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4lenvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53A23:Lept_iface4lresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4LIBHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6io_sspC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53A238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53A238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235RT_fk7ret_stFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5lpostC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53A23:Lept_iface6keepsLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_iface6pix1rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6p_cmapC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3eqbc69OSSVerify5KrLib2K53A238Po_iface=pix_copy_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib2K53A23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2K53A238Po_iface4selv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4TP_AC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_iface3RC1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c69OSSVerify5KrLib2K53A238Po_ifaceCe_processMorphArgs1C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib2K53A238Po_ifaceEprocessMorphArgs1_cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3s32C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53A23:Lept_iface5cmapv01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface7pix_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235RT_fk>ret_stF_ret_stC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53A236D_defs;ASTA_conseqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:cps_conseqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceIpixCreateHeader_res0_cpsFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_ifaceAe_pixCreateHeaderC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceHpixCreateHeader_res0_cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5rsizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceCpixCreate_res0_cpsFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface;RASTER_COSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface;e_pixCreateC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceBpixCreate_res0_cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239Pm_iface4;hdr_args_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceLpixCreateHeader_nn_res0_cpsFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceKpixCreateHeader_nn_res0_cpsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceLpixCreateNoInit_nn_res0_cpsFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4uctxC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2Inc69OSSVerify5KrLib2K53A238Po_ifaceKpixCreateNoInit_nn_res0_cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239RT_traces=CLIENT_TRACESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Pm_iface<pm_copy_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239Pm_iface2;pm_hdr_copyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceTpixCreateTemplateNoInit_nn_res0_cpsFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Pm_ifaceIe_pixCreateTemplateNoInitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceSpixCreateTemplateNoInit_nn_res0_cpsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceDpixCopy_nn_res0_cpsFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Pm_iface9e_pixCopyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Po_ifaceCpixCopy_nn_res0_cpsC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_po_fuzz : Z := 0xf9ad0.                 (* [comment removed for export] *)
Definition e_pixOrientCorrect : Z := 0x16e164.       (* [comment removed for export] *)
Definition e_pixUpDownDetect : Z := 0x16e68c.        (* [comment removed for export] *)
Definition e_makeOrientDecision : Z := 0x16f094.     (* [comment removed for export] *)
Definition e_pixDebugFlipDetect : Z := 0x16f348.     (* [comment removed for export] *)
Definition e_pixRotate90 : Z := 0x144054.            (* [comment removed for export] *)
Definition e_pixRotateOrth : Z := 0x143f24.          (* [comment removed for export] *)
Definition e_pixRotate180 : Z := 0x1452d8.           (* [comment removed for export] *)
Definition e_pixFlipLR : Z := 0x145480.              (* [comment removed for export] *)
Definition e_pixFlipTB : Z := 0x1461a0.              (* [comment removed for export] *)
Definition e_rasteropHipLow : Z := 0x12f888.         (* [comment removed for export] *)
Definition e_selCreate : Z := 0x15ac38.              (* [comment removed for export] *)
Definition e_selCreateBrick : Z := 0x15b1c0.
Definition e_selCreateComb : Z := 0x15b448.          (* [comment removed for export] *)
Definition e_selCreateFromString : Z := 0x15c0d4.    (* [comment removed for export] *)
Definition e_selSetElement : Z := 0x15ba08.
Definition e_selDestroy : Z := 0x15aa18.             (* [comment removed for export] *)
Definition e_selGetParameters : Z := 0x15af38.
Definition e_selFindMaxTranslations : Z := 0x15bc58.
Definition e_selectComposableSels : Z := 0x157c34.
Definition e_selectComposableSizes : Z := 0x157f1c. (* [comment removed for export] *)
Definition e_pixMorphCompSequence : Z := 0x15d6c4.   (* [comment removed for export] *)
Definition e_morphSequenceVerify : Z := 0x15d0c4.    (* [comment removed for export] *)
Definition e_sarrayCreate : Z := 0x102398.
Definition e_sarrayDestroy : Z := 0x102678.
Definition e_sarrayAddString : Z := 0x1028c8.        (* [comment removed for export] *)
Definition e_sarraySplitString : Z := 0x102ce4.      (* [comment removed for export] *)
Definition e_sarrayGetCount : Z := 0x1036fc.
Definition e_sarrayGetString : Z := 0x1037ac.
Definition e_strtokSafe : Z := 0xfb30c.              (* [comment removed for export] *)
Definition e_stringRemoveChars : Z := 0xfb770.
Definition e_stringNew : Z := 0xfa81c.               (* [comment removed for export] *)
Definition e_pixCloseSafeCompBrick : Z := 0x15a288. (* [comment removed for export] *)
Definition e_pixAddBorder : Z := 0x113fd0.
Definition e_pixAddBorderGeneral_po : Z := 0x114080. (* [comment removed for export] *)
Definition e_pixRemoveBorder : Z := 0x1145a8.
Definition e_pixRemoveBorderGeneral : Z := 0x114654. (* [comment removed for export] *)
Definition e_pixDilate : Z := 0x154098.              (* [comment removed for export] *)
Definition e_pixErode : Z := 0x1549e8.               (* [comment removed for export] *)
Definition e_pixHMT : Z := 0x15500c.                 (* [comment removed for export] *)
Definition e_processMorphArgs1 : Z := 0x154534.      (* [comment removed for export] *)
Definition e_pixClearAll : Z := 0x112608.
Definition e_pixSetAll : Z := 0x112720.
Definition e_pixOr : Z := 0x1284d0.
Definition e_pixRasterop_po : Z := 0x1296ac.         (* [comment removed for export] *)
Definition e_rasteropLow_po : Z := 0x12a358.         (* [comment removed for export] *)
Definition e_rasteropUniLow_po : Z := 0x129b88.      (* [comment removed for export] *)
Definition e_pixReduceRankBinaryCascade : Z := 0x15e050.  (* [comment removed for export] *)
Definition e_pixReduceRankBinary2 : Z := 0x15e588.   (* [comment removed for export] *)
Definition e_makeSubsampleTab2x : Z := 0x15df70.
Definition e_pixScaleResolution : Z := 0x111814.     (* [comment removed for export] *)
Definition e_pixCopyResolution_po : Z := 0x10eca0.    (* [comment removed for export] *)
Definition e_pixCountPixels : Z := 0x128754.         (* [comment removed for export] *)
Definition e_pixCopySpp : Z := 0x10eb04.
Definition e_pixCopyInputFormat : Z := 0x10f4b4.     (* [comment removed for export] *)
Definition e_pixGetSpp : Z := 0x111510.              (* [comment removed for export] *)
Definition e_pixcmapGetCount : Z := 0x1189f8.        (* [comment removed for export] *)
Definition e_pixResizeImageData : Z := 0x11008c.     (* [comment removed for export] *)
Definition e_pixCopy_po : Z := 0x10fab8.             (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fs32 (bits : Z) : word := nan_box (Z_to_bv 32 bits).
Definition F_1_0 : Z := 0x3f800000.   Definition F_0_5 : Z := 0x3f000000.   (* [comment removed for export] *)
Definition r_fa0 : reg := Z_to_bv 5 10.   Definition r_fa1 : reg := Z_to_bv 5 11.   Definition r_fa2 : reg := Z_to_bv 5 12.   Definition r_fa3 : reg := Z_to_bv 5 13.
Definition PIX_SRC : Z := 12.   Definition PIX_CLR : Z := 0.
Definition pix_new_live (pix : Z) (v : pixv) (live : list (Z * Z)) : list (Z * Z) := (p_data v, rsize v) :: (pix, 64) :: live.
Definition e_pixCreateTemplate_po : Z := 0x10e3f4.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PIX_NOT_SRC : Z := 3.   Definition PIX_SRC_AND_DST : Z := 8.   Definition PIX_NOTSRC_AND_DST : Z := 2.
Definition PIX_SRC_OR_DST : Z := 14. Definition PIX_DST : Z := 10.
Definition PO_OPS : list Z := [PIX_SRC; PIX_NOT_SRC; PIX_SRC_AND_DST; PIX_NOTSRC_AND_DST; PIX_SRC_OR_DST].   (* [comment removed for export] *)
Definition SEL_HIT : Z := 1.  Definition SEL_MISS : Z := 2.  Definition SEL_DONT_CARE : Z := 0.
Definition L_HORIZ : Z := 1.  Definition L_VERT : Z := 2.
Definition ORIENT_MAX : Z := 4.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RC1 : Z := RASTER_COST + 64.
Definition CSC_COST : Z := 4 * RC1 + 2^12.            (* [comment removed for export] *)
Definition CSC_SECB : Z := 4 * 2^26.                  (* [comment removed for export] *)
Definition MCS_COST : Z := RC1 + 2 * CSC_COST + 2^12. (* [comment removed for export] *)
Definition MCS_SECB : Z := 2^26 + CSC_SECB.
Definition HMT_COST : Z := RC1 + 2^8.                 (* [comment removed for export] *)
Definition CASC_COST : Z := 2 * RC1 + 2^8.            (* [comment removed for export] *)
Definition UDD_COST : Z := MCS_COST + 4 * HMT_COST + 2 * CASC_COST + 2^12.   (* [comment removed for export] *)
Definition UDD_SECB : Z := MCS_SECB.                  (* [comment removed for export] *)
Definition OC_COST : Z := 2 * UDD_COST + 2 * RC1 + 2^10.                     (* [comment removed for export] *)
Definition OC_SECB : Z := 2^26 + UDD_SECB.            (* [comment removed for export] *)
Definition PO_FUZZ_COST : Z := OC_COST + RC1 + 2^10.  (* [comment removed for export] *)
Definition PO_FUZZ_SECB : Z := 2^26 + OC_SECB.        (* [comment removed for export] *)
Definition PO_FUZZ_LIVE : Z := 128.                   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition res0 (v : pixv) : Prop := p_xres v = 0 /\ p_yres v = 0 /\ p_spp v = 1.
(* [comment removed for export] *)
Definition res0d (v : pixv) : Prop := p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1).
Lemma res0d_1 : forall v, res0d v -> p_d v = 1 -> res0 v.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_iface ()) [] "h01Hh11Dh21Sh31Xh41Yh51vp;1p;2p;4p;3p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cp4p710p8P0p1001DR1p4p710p8P0P1p4p7210p8P0p1001ap4p710p8P0p1002Ap4p7210p8P0p1002_p4p7210p8g0039j1;Tg0043j16Tg0050j14Tg005mj12Tg006gj1:Tg007Ej13Tg008AR0j25Tg008\j18Tg009Uj47Tg00:0j39Tg00:JR1f0R2g00:h39p=1f1R3=912p=0g00;F%;2P0%63#1%43#1%23g00<C#:R1'0f2R4#3/01['5%24/01f3R5#8[P2%65#1f4R5#4#1%25/01f5R5#3/01['5P0%45#1%25/01f6R5#3/01[%25/01f7R0#8[P2%40#1f8#2/01f9R0#3/01[%20/01f:R0#6#1%40#1R6%30/01R1'5P5P6P1P4P3P2O1C7C7W1W2W4P3P2O2n2001000000120000000W0W3P3P2O2n2001000000120000000W0W5o"). Qed.
(* [comment removed for export] *)
Definition pix1c (live : list (Z * Z)) (m : mem) (pix : Z) (v : pixv) (cv : cmapv) : Prop :=
  pix_obj live m pix v cv /\ p_d v = 1 /\ p_data v <> 0 /\ res0 v.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pix1rc (live : list (Z * Z)) (m : mem) (pix : Z) (v : pixv) (cv : cmapv) (rc : Z) : Prop :=
  pix_obj_rc live m pix v cv rc /\ p_d v = 1 /\ p_data v <> 0 /\ res0 v.
(* [comment removed for export] *)
Definition pix_chunks (pix : Z) (v : pixv) (cv : cmapv) : list Z :=
  pix :: p_data v :: (if p_cmap v =? 0 then [] else [p_cmap v; c_arr cv]).
(* [comment removed for export] *)
Definition pix_copy_live := pm_copy_live.
(* [comment removed for export] *)
Definition dims1 (v : pixv) : Prop := 1 <= p_w v <= 20000 /\ 1 <= p_h v <= 20000 /\ p_wpl v = (p_w v + 31) / 32 /\ 4 * (p_wpl v * p_h v) <= 0x4000000.

(* [comment removed for export] *)
Record selv : Type := mkSelv { s_sy : Z; s_sx : Z; s_cy : Z; s_cx : Z; s_data : Z; s_rowp : list Z; s_rows : list (list Z) }.
Definition sel_cells (sv : selv) : list cell :=
  [C4 (Z_to_bv 64 (s_sy sv)); C4 (Z_to_bv 64 (s_sx sv)); C4 (Z_to_bv 64 (s_cy sv)); C4 (Z_to_bv 64 (s_cx sv));
   C8 (Z_to_bv 64 (s_data sv)); C8 (Z_to_bv 64 0)].
Definition sel_obj (live : list (Z * Z)) (m : mem) (sel : Z) (sv : selv) : Prop :=
  rw_cells asegs m sel (sel_cells sv) /\ chunk live sel 32
  /\ chunk live (s_data sv) (8 * s_sy sv) /\ u64arr asegs m (s_data sv) (map (Z_to_bv 64) (s_rowp sv))
  /\ Z.of_nat (length (s_rowp sv)) = s_sy sv /\ Z.of_nat (length (s_rows sv)) = s_sy sv
  /\ Forall2 (fun rp row => chunk live rp (4 * s_sx sv) /\ u32arr asegs m rp (map (Z_to_bv 64) row) /\ Z.of_nat (length row) = s_sx sv)
             (s_rowp sv) (s_rows sv)
  /\ 1 <= s_sy sv <= 30 /\ 1 <= s_sx sv <= 30 /\ 0 <= s_cy sv < s_sy sv /\ 0 <= s_cx sv < s_sx sv
  /\ List.NoDup (sel :: s_data sv :: s_rowp sv).
(* [comment removed for export] *)
Definition sel_chunks (sel : Z) (sv : selv) : list Z := sel :: s_data sv :: s_rowp sv.
Definition sel_new_live (sel : Z) (sv : selv) (live : list (Z * Z)) : list (Z * Z) :=
  rev (map (fun rp => (rp, 4 * s_sx sv)) (s_rowp sv)) ++ (s_data sv, 8 * s_sy sv) :: (sel, 32) :: live.
(* [comment removed for export] *)
Definition sel_destroy_live (sel : Z) (sv : selv) (live : list (Z * Z)) : list (Z * Z) :=
  live_remove sel (live_remove (s_data sv) (fold_left (fun l rp => live_remove rp l) (s_rowp sv) live)).
(* [comment removed for export] *)
Definition tsel_rows (k : Z) : list (list Z) :=
  match k with
  | 1 => [[1;0;0;2;2;0]; [1;0;2;2;2;0]; [1;0;0;2;0;0]; [1;0;0;0;0;0]; [1;1;1;1;1;1]]
  | 2 => [[0;2;2;0;0;1]; [0;2;2;2;0;1]; [0;0;2;0;0;1]; [0;0;0;0;0;1]; [1;1;1;1;1;1]]
  | 3 => [[1;1;1;1;1;1]; [1;0;0;0;0;0]; [1;0;0;2;0;0]; [1;0;2;2;2;0]; [1;0;0;2;2;0]]
  | _ => [[1;1;1;1;1;1]; [0;0;0;0;0;1]; [0;0;2;0;0;1]; [0;2;2;2;0;1]; [0;2;2;0;0;1]]
  end.
Definition tsel_cy (k : Z) : Z := if k <=? 2 then 1 else 3.          (* [comment removed for export] *)
Definition tsel_cx (k : Z) : Z := if (k =? 1) || (k =? 3) then 3 else 2.
Definition tsel_shape (k : Z) (sv : selv) : Prop := s_sy sv = 5 /\ s_sx sv = 6 /\ s_cy sv = tsel_cy k /\ s_cx sv = tsel_cx k /\ s_rows sv = tsel_rows k.
(* [comment removed for export] *)
Definition ones (n : nat) : list Z := repeat 1 n.
Definition comb_row (sx f1 : Z) : list Z := map (fun j => if (j mod f1 =? f1 / 2) then 1 else 0) (map Z.of_nat (seq 0 (Z.to_nat sx))).
Definition brick_h6 (sv : selv) : Prop := s_sy sv = 1 /\ s_sx sv = 6 /\ s_cy sv = 0 /\ s_cx sv = 3 /\ s_rows sv = [ones 6].
Definition comb_h30 (sv : selv) : Prop := s_sy sv = 1 /\ s_sx sv = 30 /\ s_cy sv = 0 /\ s_cx sv = 15 /\ s_rows sv = [comb_row 30 6].
Definition brick_v4 (sv : selv) : Prop := s_sy sv = 4 /\ s_sx sv = 1 /\ s_cy sv = 2 /\ s_cx sv = 0 /\ s_rows sv = repeat [1] 4.
Definition comb_v8 (sv : selv) : Prop := s_sy sv = 8 /\ s_sx sv = 1 /\ s_cy sv = 4 /\ s_cx sv = 0 /\ s_rows sv = map (fun z => [z]) (comb_row 8 4).
(* [comment removed for export] *)
Definition csc_sels (hs vs : Z) (sv1 sv2 : selv) : Prop :=
  (hs = 30 /\ vs = 1 /\ brick_h6 sv1 /\ comb_h30 sv2) \/ (hs = 1 /\ vs = 8 /\ brick_v4 sv1 /\ comb_v8 sv2).
(* [comment removed for export] *)
Definition small3 (row : list Z) : Prop := Forall (fun e => 0 <= e <= 2) row.
Definition sel_small (sv : selv) : Prop := Forall small3 (s_rows sv).
(* [comment removed for export] *)
Definition sel_maxtrans (sv : selv) : Z * Z * Z * Z :=
  let hits := flat_map (fun ir => let '(i, row) := ir in
                 flat_map (fun jr => let '(j, e) := jr in if e =? 1 then [(i, j)] else [])
                          (combine (map Z.of_nat (seq 0 (length row))) row))
               (combine (map Z.of_nat (seq 0 (length (s_rows sv)))) (s_rows sv)) in
  (fold_left Z.max (map (fun ij => s_cx sv - snd ij) hits) 0, fold_left Z.max (map (fun ij => s_cy sv - fst ij) hits) 0,
   fold_left Z.max (map (fun ij => snd ij - s_cx sv) hits) 0, fold_left Z.max (map (fun ij => fst ij - s_cy sv) hits) 0).

(* [comment removed for export] *)
Definition cstr (live : list (Z * Z)) (m : mem) (p : Z) (bs : list Z) : Prop :=
  (exists n, chunk live p n /\ Z.of_nat (length bs) + 1 <= n) /\ bytes_at asegs m p (map (Z_to_bv 8) (bs ++ [0])) /\ Forall (fun b => 0 < b < 256) bs.
(* [comment removed for export] *)
Record sav : Type := mkSav { sa_n : Z; sa_arr : Z; sa_strs : list (Z * list Z) }.   (* [comment removed for export] *)
Definition sarray_obj (live : list (Z * Z)) (m : mem) (sa : Z) (av : sav) : Prop :=
  (exists pad rc, rw_cells asegs m sa [C4 (Z_to_bv 64 50); C4 (Z_to_bv 64 (sa_n av)); C4 rc; CB 4 pad; C8 (Z_to_bv 64 (sa_arr av))])
  /\ chunk live sa 24 /\ chunk live (sa_arr av) 400 /\ 0 <= sa_n av <= 50 /\ Z.of_nat (length (sa_strs av)) = sa_n av
  /\ (exists junk, u64arr asegs m (sa_arr av) (map (fun s => Z_to_bv 64 (fst s)) (sa_strs av) ++ junk) /\ Z.of_nat (length junk) = 50 - sa_n av)
  /\ Forall (fun s => cstr live m (fst s) (snd s)) (sa_strs av)
  /\ List.NoDup (sa :: sa_arr av :: map fst (sa_strs av)).
Definition sarray_chunks (sa : Z) (av : sav) : list Z := sa :: sa_arr av :: map fst (sa_strs av).
(* [comment removed for export] *)
Definition SEQ_TEXT : list Z := [99;49;46;56;32;43;32;99;51;48;46;49].          (* [comment removed for export] *)
Definition RAWOP1 : list Z := [99;49;46;56;32].  Definition RAWOP2 : list Z := [32;99;51;48;46;49].   (* [comment removed for export] *)
Definition OP1 : list Z := [99;49;46;56].        Definition OP2 : list Z := [99;51;48;46;49].          (* [comment removed for export] *)
Definition A_SEQ_TEXT : Z := 0x46300.   (* [comment removed for export] *)
Definition A_TSEL (k : Z) : Z := 0x46460 + 0x40 * (k - 1).  (* [comment removed for export] *)
Definition A_FMT_DD : Z := 0x41140.     (* [comment removed for export] *)
Definition A_SEPS_PLUS : Z := 0x410c0.  Definition A_SEPS_WS : Z := 0x41120.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PO_TR (fn : Z) : list (list Z * nat) := po_tr_table fn.   (* [comment removed for export] *)
Definition po_row (t : list Z) (mode : nat) (ra : word) (ras : list Z) : list Z :=
  match mode with 0%nat => t | 1%nat => t ++ ras | _ => t ++ bv_unsigned ra :: ras end.
Definition po_rows (fn : Z) (ra : word) (ras : list Z) : Prop :=
  Forall (fun tm : list Z * nat => In (po_row (fst tm) (snd tm) ra ras) CLIENT_TRACES) (PO_TR fn).

Section PoIface.
Variable RT : rt_sig.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixClearAll_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> pix1c (rt_live RT Σ) m pix v cv ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixClearAll m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data v, p_data v + rsize v)] m m'
          /\ pix1c (rt_live RT Σ') m' pix v cv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixSetAll_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> pix1c (rt_live RT Σ) m pix v cv ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 0 2 ->     (* [comment removed for export] *)
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixSetAll m)))
    (fun c => exists (Σ' : rts RT) (rv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data v, p_data v + rsize v)] m m'
          /\ pix1c (rt_live RT Σ') m' pix v cv /\ (rv = 0 \/ (rv = 1 /\ p_cmap v <> 0 /\ c_n cv < c_nalloc cv))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition hdr_same (v v' : pixv) : Prop :=
  p_w v' = p_w v /\ p_h v' = p_h v /\ p_d v' = p_d v /\ p_wpl v' = p_wpl v /\ p_cmap v' = p_cmap v /\ p_data v' = p_data v
  /\ p_xres v' = p_xres v /\ p_yres v' = p_yres v.
Definition pixCopyHdrField_cps (entry off : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv) (rcs : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs -> pixd <> pixs ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> pix_obj_rc (rt_live RT Σ) m pixs vs cvs rcs ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 0 1 ->     (* [comment removed for export] *)
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (vd' : pixv) (rv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pixd + off, pixd + off + 4)] m m'
          /\ pix_obj (rt_live RT Σ') m' pixd vd' cvd /\ hdr_same vd vd' /\ (rv = 0 \/ rv = 1)) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').
(* [comment removed for export] *)
Definition pixCopyInputFormat_cps : Prop := pixCopyHdrField_cps e_pixCopyInputFormat 32.
(* [comment removed for export] *)
Definition pixCopySpp_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv) (rcs : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs -> pixd <> pixs ->
  pix_obj (rt_live RT Σ) m pixd vd cvd -> pix_obj_rc (rt_live RT Σ) m pixs vs cvs rcs -> p_spp vs = 1 ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopySpp m)))
    (fun c => exists (Σ' : rts RT) (vd' : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pixd + 12, pixd + 12 + 4)] m m'
          /\ pix_obj (rt_live RT Σ') m' pixd vd' cvd /\ hdr_same vd vd' /\ p_spp vd' = 1) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition getter_cps (entry : Z) (obj : list (Z * Z) -> mem -> Z -> Prop) (fld : mem -> Z -> Z -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (p : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 p -> obj (rt_live RT Σ) m p ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (rv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m' /\ fld m p rv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).
(* [comment removed for export] *)
Definition pixGetSpp_cps : Prop :=
  getter_cps e_pixGetSpp (fun live m p => exists v cv, pix1c live m p v cv) (fun m p rv => rv = 1).
Definition pixcmapGetCount_cps : Prop :=
  getter_cps e_pixcmapGetCount (fun live m p => exists cv, cmap_obj live m p cv) (fun m p rv => exists cv L, cmap_obj L m p cv /\ rv = c_n cv).

(* [comment removed for export] *)
Definition pixScaleResolution_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> reg_get F r_fa0 = fs32 F_0_5 -> reg_get F r_fa1 = fs32 F_0_5 -> pix_obj (rt_live RT Σ) m pix v cv -> res0 v ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixScaleResolution m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pix + 24, pix + 32)] m m'
          /\ pix_obj (rt_live RT Σ') m' pix v cv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixCopyResolution_po_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd ps : Z) (vd vs : pixv) (cvd cvs : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> a1 = Z_to_bv 64 ps -> pix_obj (rt_live RT Σ) m pd vd cvd -> res0 vd ->
  pix_obj_rc (rt_live RT Σ) m ps vs cvs rc -> 1 <= rc <= 2 -> res0 vs -> pd <> ps ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopyResolution_po m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pd + 24, pd + 32)] m m'
          /\ pix_obj (rt_live RT Σ') m' pd vd cvd) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selGetParameters_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sel psy psx pcy pcx : Z) (sv : selv) (x1 x2 x3 x4 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sel -> a1 = Z_to_bv 64 psy -> a2 = Z_to_bv 64 psx -> a3 = Z_to_bv 64 pcy -> a4 = Z_to_bv 64 pcx ->
  sel_obj (rt_live RT Σ) m sel sv ->
  optrF RT Σ m psy 4 -> optrF RT Σ m psx 4 -> optrF RT Σ m pcy 4 -> optrF RT Σ m pcx 4 ->
  rw_cells asegs m psy [C4 x1] -> rw_cells asegs m psx [C4 x2] -> rw_cells asegs m pcy [C4 x3] -> rw_cells asegs m pcx [C4 x4] ->
  List.NoDup [psy; psx; pcy; pcx] ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selGetParameters m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(psy, psy + 4); (psx, psx + 4); (pcy, pcy + 4); (pcx, pcx + 4)] m m'
          /\ rw_cells asegs m' psy [C4 (Z_to_bv 64 (s_sy sv))] /\ rw_cells asegs m' psx [C4 (Z_to_bv 64 (s_sx sv))]
          /\ rw_cells asegs m' pcy [C4 (Z_to_bv 64 (s_cy sv))] /\ rw_cells asegs m' pcx [C4 (Z_to_bv 64 (s_cx sv))]
          /\ sel_obj (rt_live RT Σ') m' sel sv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selFindMaxTranslations_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sel pxp pyp pxn pyn : Z) (sv : selv) (x1 x2 x3 x4 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sel -> a1 = Z_to_bv 64 pxp -> a2 = Z_to_bv 64 pyp -> a3 = Z_to_bv 64 pxn -> a4 = Z_to_bv 64 pyn ->
  sel_obj (rt_live RT Σ) m sel sv -> sel_small sv ->
  optrF RT Σ m pxp 4 -> optrF RT Σ m pyp 4 -> optrF RT Σ m pxn 4 -> optrF RT Σ m pyn 4 ->
  rw_cells asegs m pxp [C4 x1] -> rw_cells asegs m pyp [C4 x2] -> rw_cells asegs m pxn [C4 x3] -> rw_cells asegs m pyn [C4 x4] ->
  List.NoDup [pxp; pyp; pxn; pyn] ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selFindMaxTranslations m)))
    (fun c => exists (Σ' : rts RT),
       let '(xp, yp, xn, yn) := sel_maxtrans sv in
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pxp, pxp + 4); (pyp, pyp + 4); (pxn, pxn + 4); (pyn, pyn + 4)] m m'
          /\ rw_cells asegs m' pxp [C4 (Z_to_bv 64 xp)] /\ rw_cells asegs m' pyp [C4 (Z_to_bv 64 yp)]
          /\ rw_cells asegs m' pxn [C4 (Z_to_bv 64 xn)] /\ rw_cells asegs m' pyn [C4 (Z_to_bv 64 yn)]
          /\ sel_obj (rt_live RT Σ') m' sel sv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition makeSubsampleTab2x_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  uctx m sp s0 ras -> po_rows e_makeSubsampleTab2x ra ras ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeSubsampleTab2x m)))
    (fun c => exists (Σ' : rts RT) (tab : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 tab) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ chunk (rt_live RT Σ') tab 256 /\ wr_at asegs m' tab 256) c
       /\ rt_live RT Σ' = (tab, 256) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition stringNew_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (src : Z) (bs : list Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 src -> Z.of_nat (length bs) < 96 -> Forall (fun b => 0 < b < 256) bs ->
  (cstr (rt_live RT Σ) m src bs \/ (exists l, In (src, l) LEPT_LITS /\ bytes_at asegs m src (map (Z_to_bv 8) (bs ++ [0])))) ->
  uctx m sp s0 ras -> po_rows e_stringNew ra ras ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stringNew m)))
    (fun c => exists (Σ' : rts RT) (dst : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 dst) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ cstr (rt_live RT Σ') m' dst bs) c
       /\ rt_live RT Σ' = (dst, Z.of_nat (length bs) + 1) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition selGetParameters_sxsy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sel psy psx : Z) (sv : selv) (x1 x2 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sel -> a1 = Z_to_bv 64 psy -> a2 = Z_to_bv 64 psx -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 0 ->
  sel_obj (rt_live RT Σ) m sel sv ->
  optrF RT Σ m psy 4 -> optrF RT Σ m psx 4 ->
  rw_cells asegs m psy [C4 x1] -> rw_cells asegs m psx [C4 x2] -> psy <> psx ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selGetParameters m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(psy, psy + 4); (psx, psx + 4)] m m'
          /\ rw_cells asegs m' psy [C4 (Z_to_bv 64 (s_sy sv))] /\ rw_cells asegs m' psx [C4 (Z_to_bv 64 (s_sx sv))]
          /\ sel_obj (rt_live RT Σ') m' sel sv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition pixResizeImageData_same_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv) (rcd rcs : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs -> pixd <> pixs ->
  pix_obj_rc (rt_live RT Σ) m pixd vd cvd rcd -> pix_obj_rc (rt_live RT Σ) m pixs vs cvs rcs ->
  p_w vd = p_w vs -> p_h vd = p_h vs -> p_d vd = p_d vs ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixResizeImageData m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m'
          /\ pix_obj_rc (rt_live RT Σ') m' pixd vd cvd rcd /\ pix_obj_rc (rt_live RT Σ') m' pixs vs cvs rcs) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition processMorphArgs1_case (AL : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs sel ppixt : Z) (vd vs : pixv) (cvd cvs : cmapv) (sv : selv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 sel -> a3 = Z_to_bv 64 ppixt ->
  pix1c (rt_live RT Σ) m pixs vs cvs -> sel_obj (rt_live RT Σ) m sel sv ->
  (pixd = 0 \/ (pixd <> pixs /\ pix1c (rt_live RT Σ) m pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs
                /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs))) ->
  optrF RT Σ m ppixt 8 -> rw_cells asegs m ppixt [C8 x] ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 4 4 (RC1 + 1) -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  bv_unsigned sp mod 32 = AL ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_processMorphArgs1 m)))
    (fun c => exists (Σ' : rts RT) (rv : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(ppixt, ppixt + 8); (pixs + 20, pixs + 24)] m m'
          /\ rv <> 0 /\ rw_cells asegs m' ppixt [C8 (Z_to_bv 64 pixs)] /\ pix1rc (rt_live RT Σ') m' pixs vs cvs 2
          /\ pix1c (rt_live RT Σ') m' rv v' cv' /\ p_w v' = p_w vs /\ p_h v' = p_h vs
          /\ (pixd <> 0 -> rv = pixd /\ v' = vd /\ cv' = cvd)
          /\ (pixd = 0 -> (p_cmap vs = 0 -> p_cmap v' = 0) /\ List.NoDup (pix_chunks rv v' cv' ++ pix_chunks pixs vs cvs))) c
       /\ rt_live RT Σ' = (if pixd =? 0 then pix_copy_live rv v' cv' (rt_live RT Σ) else rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RC1 + 1) <= rt_credit RT Σ').
Definition processMorphArgs1_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs sel ppixt : Z) (vd vs : pixv) (cvd cvs : cmapv) (sv : selv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 sel -> a3 = Z_to_bv 64 ppixt ->
  pix1c (rt_live RT Σ) m pixs vs cvs -> sel_obj (rt_live RT Σ) m sel sv ->
  (pixd = 0 \/ (pixd <> pixs /\ pix1c (rt_live RT Σ) m pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs
                /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs))) ->
  optrF RT Σ m ppixt 8 -> rw_cells asegs m ppixt [C8 x] ->
  lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 4 4 (RC1 + 1) -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_processMorphArgs1 m)))
    (fun c => exists (Σ' : rts RT) (rv : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(ppixt, ppixt + 8); (pixs + 20, pixs + 24)] m m'
          /\ rv <> 0 /\ rw_cells asegs m' ppixt [C8 (Z_to_bv 64 pixs)] /\ pix1rc (rt_live RT Σ') m' pixs vs cvs 2
          /\ pix1c (rt_live RT Σ') m' rv v' cv' /\ p_w v' = p_w vs /\ p_h v' = p_h vs
          /\ (pixd <> 0 -> rv = pixd /\ v' = vd /\ cv' = cvd)
          /\ (pixd = 0 -> (p_cmap vs = 0 -> p_cmap v' = 0) /\ List.NoDup (pix_chunks rv v' cv' ++ pix_chunks pixs vs cvs))) c
       /\ rt_live RT Σ' = (if pixd =? 0 then pix_copy_live rv v' cv' (rt_live RT Σ) else rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RC1 + 1) <= rt_credit RT Σ').
Lemma processMorphArgs1_of_cases : processMorphArgs1_case 0 -> processMorphArgs1_case 16 -> processMorphArgs1_cps.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_iface ()) ["PoIface"] "p'0h01Hh12ALh22H5h32H0h42H1h52H2h62H3h72H4h82H6h92H7h:2H8h;4__x1h<4__x2h=4__x3h>4__x4h?4__x5h@2C0hA3C16hB3ENVhC1FhD3H10hE3H11hF3H12hG3H14hH3H15hI2H9hJ3PMchK3SPAhL2_HhM3_H0hN3_H1hO3_H2hP3_H3hQ3_H4hR3_H5hS3_H6hT3_H7hU7__arithhV4__ffhW8__varmaphX5__withY2a0hZ2a1h[2a2h\2a3h]2a4h^2a5h_2a6h`2a7ha1chb3cv'hc3cvdhd3cvshe2fchf2gphg2lohh1mhi2m'hj2mshk4pixdhl4pixshm5ppixthn1qho2q0hp1rhq2r0hr2rahs2rvht2s0hu2s1hv3s10hw3s11hx2s2hy2s3hz2s4h{2s5h|2s6h}2s7h~2s8i002s9i013seli022spi032svi042t0i052t1i062t2i072t3i082t4i092t5i0:2t6i0;2tpi0<2v'i0=2vdi0>2vsi0?1xi0@2Σi0A3Σ'p%0p&0p;1p;2p;3p;5p;4p;6p;7p;Sp;Dp;8g00<hk106Tg00>3j14Tg006gj1<Tg00>Xk10NTg00?Pj1^Tg00?nj1gTg00@Qk101Tg00A6k20\Tg00Abk10XTg00BDk10STg00CBk10MTg00D>j2TTg00:0j33k20FTg00Ddj2ATg00E`j5hTg00FZk40]Tg00GVj1PTg00Goj1ZTg00Hij1YTg00Icj3XTg00Jbj3}Tg00K?j2yTg00K[k50WTg00LWj1tTg00MOj1fTg00Moj3FTg00NOj4rTg00OHk10PTg00PCk60LTg00Q>j27Tg00Q[k50DTg00RVk10@Tg00STj1kTg00TOj1UTg00UJj3LTg00VBj20Tg00Vlj21Tg00WgS00j2]Tg00XAj26Tg00X]k200Tg00Y>j2KTg00Y[j2STg00Z8j28Tg00ZXj2~Tg00[?j2;Tg00[[j2|Tg00\Bj2xTg00\hj2wTg00]Nj2vTg00]oj2bTg00^Ik10[Tg00^gk20ZTg00_Hj1CTg00_gj3aTg00`Pj2uTg00a9k20VTg00aej2WTg00bQj1dTg00c1j2sTg00cOk10UTg00cmj4eTg00dKk10RTg00dik10QTg00eTj2`Tg00f7k10OTg00fYj2MTg00g<j3lTg00g_j3oTg00hBj4_Tg00hmk70KTg00iQk70JTg00j5k20ITg00jWk20CTg00kCk30ATg00kbk40BTg00lTmS0ETg00mQk40>k50:Tg00nJmD0GTg00oCk70HTg010?j2mTg010_j4nTg011?k70<Tg012<k60;Tg0137j1pTg008AR0j22Tg0144j2RTg014Nk209Tg014kk40TTg015mj2zTg016kk208Tg017ij2jTg018Fk30bTg019;k20aTg01:2k407Tg01:gj3iTg01;Pk70`Tg01<4k60_Tg01<Xk80^Tg00:JR1f1R2f0R333p=5f4R4f3R5f2R61223'2'2'2p=Gg00:hR79312/]3p>0Y%43#4#4#4p=N1762/63p=cg01=<R800a3p=BP8P6P2P3H07p=Jf5R9/74g01>4R:'61856=3171623'2'2p=9g01?3R;,j9/641756/62/23'2p==1062/83p=:A3137p=>P8P5P6P2H07/23p=\1223,26p=IA3167A3123']p=@1j2;/63p>051856=3171623'2p=[1794/651762/6:/23'2p>041723/6:p>031823=317p>021662/23p=O1623,26p={1u13p=HAi123p=QAi1239i16p=VP1P2g01@1P3C_p=DP2g01@XR:g01A7R;P;g01AWR<P3g01B7K0`p=?P2P:P;P;P<P3J0_p=qP5P:P;P;P<P6P2P3L0^p=EA3123,]6p>0?%43#4p>0=&067g00<CR=#4R>#4R?#4R@#4RA#<RB$06p,2RTRC$0NRDg01BWp-0[%4ARA#4RE#^RF#gRG&01>RH#^00\G%^A#g%^@#g$0X\GRIg00;FRJg01CMRKg01DKf]RL$0Sf^RM$0Mf[RNg01EF,TF53GfVROf<RP,TF53GRQfeS01,ACfBRRf?S02f;RSf9RTDhffS03,ACfCS04Q02PTH0]fARU,5R#PfgRV,ACfDS05PRf>RWPPDh%ZWf=RX#Z'5%YW%YX'5AXRWPAXUXS5}1,y1DG-0YRPCfhRYfES06f@S07%<@S08I0WP8fFR@PUg01F=RZ%tS%fZS093FCrPCfjR[fGS0:PVP@%4HS0;#<$0PR\J0LPCfkR]%<?R^P^g01G5%<='7S0<I0DflR^,AC$0@%NE#N#N#N#N#<g01Gm3cP0fJRE#k%UEfmR_=LCE%BEfIR`10F[Ra5JE11C_RbP`P`P\PaPaPBPaPBPaPbE9E=DG%<ARA9:F]Rb#>S0=15bBS0>']P6fLRb#kfMRc#UfpRd=LCc%Bc10F_Re9Jcb11CdRfPbPbP\PePePBPePBPePfE9E=DGP0fNRf#UfqRe=LCf%BfPfPcfnRg,0FRh11CeRiPcPcP\PhPhPBPhPBPhPiE9E=C\3IfoRi=:FARh?@hBP3fPRh#UftRjfQRk5LC%BkPkPh10FeRl11CjRmPhPhP\PlPlPBPlPBPlPmE9E=C\3IP0fuRlfRRn5LC%BnfrS0?,0FRo9Jnk11ClRpPkPkP\PoPoPBPoPBPoPpE9E=3IfsRp=:FARo?@oBP3fwRofTRq5LCfURr#B10FlRl9Jrqfx,1CRsPqPqP\PlPlPBPlPBPlPsE9E=3IP0%BOPOPrfvRs,0FRlfyRt,1CRuPrPrP\PlPlPBPlPBPlPuE9E=C\A:FoARo?@oBP3fXRo#BfYRuPo10FtRtf|Rl,1CRvPoPoP\PtPtPBPtPBPtPvE9E=C\P0fZRvfz,0FRt7Juf}Rw,1CRxPuPuP\PtPtPBPtPBPtPxE9E=f{=:FARx?@xBP3f\Rx10Fl7JNp+01A,1CRlPxPxP\10FwRwPwPBPwPBPwPlE9E=P0p+01BRl,1CRw005LPLP\f~,0FRtPtPBPtPBPtPwC[J04p+01@=:FARw?@wBP3p+01DRw,1Cf_Rt+05f`RyP\10FlRlPlPBPlPBPlp+01ERl,1CC[J04P0faRzp+01C,0FR{7c\P{PBP{PBP{p+01FR{,1CE9A:FwARw?@wBP3fcRw10Fl7c\10F{R{PBP{PBP{p+01IR{,1CE9P0p+01G,0FR\003BP\PBP\p+01JR\,1CC[p+01H=:FARl?@lBP310F{003B10F\R\PBP\p+01MR\,1CC[P0p+01K,0FR0002Bp+01NR{,1C,60p+01L=:FAR0?@0BP310F\002B10F{p+01QR{,1C'6p+01O,0F000A%>AR\#Pp+01P,0FR01K0A,SA180A'7'5[1~0A1;7AR010F{R{/8ARl1;lA5O7[1|{A1;A7p+01R,0FR{/8ARl,;A?{l7[1x{Ap+01S,0FR{/KA#>\\1w{Ap+01T,0FR{/8A/5{\\1K{AP1p+01U=:FAP1p+01V,0F000B%>BR{#Pp+01W,0FRl1KlB,SB18lB'7'5[1~lB1;7BRlp+01X,0FR|/8BR}1;}B5O7[1||B1;B7p+01Y,0FR|/8BR},;B?{}7[1x|Bp+01Z,0FR|/KB#>\{1w|Bp+01[,0FR|/8B/5|\{1K|BP1p+01\=:FBP1P9g01HkR|1v7B'bPleO11;3B9O73PX1v7A,b|P0eO1f8R01;0A5O7g01IQR|&0[=-0Z1Rlg01J=S0@#CS0A#CR}#CR~#CS0B#C#CS0C#H5a1S0D%H~R~%H}S0E9a1lS0FQ0@,u1R}'Q3VQ0C#C#HS0CQ0B#HS0B9a1lS0@Q0E,Q~3VQ0A#HRl/Q}g01J\+0VR}'W'WQ0DQ0BQ0F,Q~3VQ0CQ0@1Q~l3V/W}'W%f|5F|3F%d|P1P11s14P6&0U1R|CeP2P11s19P5P|CeCe&0R1&0Q1R|P|1`1BR}1`17Rl'D,?|,q|&0O;R~&01=S0@,M1S0C1M1H9l1}1M1>S0B5o1'D,?|CEP~P|P|P:P;P;P<P1Plg01KH1M1=R=C_,?|P1P=g01Ko1`1ARHC_,?|K0KP~P|P|1DHl,?|,q|P~Q0C1M1?9l1H=o1='D,?|CEP~P|Q0B/Dl,?|P~P|P:P;P;P<1D=l,?|1D=},?|K0JCECECECE20I|<P3P6g01LVR|g01M6R<'b20C36=3|<dB0A172H0BbVbWbXX;1X<1X=1X>1X?1g01MVR<\{1SB9/76,55[1;2A9O72P<\\f6R\,SA/75,59[%>4R<B0?<4B[[[[^;1^<1^=1^>1^?1P3P4PSp+01`,0FP5f:R{PTP2Q07PRO9bUb3b2bqbob:b9b8b2b7bpbnb6b5b4b3b0WTWKP2P3O2n2001000000121000000W0WSP2P3O2n2001000000121000000W0WRP2P3O2n2001000000121000000W0WQP2P3O2n2001000000121000000W0WPP2P3O2n2001000000121000000W0WOP2P3O2n2001000000121000000W0WNP2P3O2n2001000000121000000W0WMP2P3O2n2001000000121000000W0WLP2P3O2n200100000012100000018aARa?@aBQ00Q0=Q0>PCPiPgg01N3RaP_P^P]P[fiR=PYPVQ03Q01fdR}PwfbRlPzPyPtPMPLPxPNPvPuPofWR;POPrPqfSR:PnPkPhfOR~PfPcg01O:PbNS0E+0FH0>g01PBPCP5PpPjPpQ0?PeP_P^PwPlPzPyPtPMPLPxPNPv1TF4PrP3P2ND0GPCPsP9P:P3PpPnK0HPC1ACsPsPp1m11RpP1P1PfQ08,7fCnP1P1Q0;#4#<,7hQ0@#4$0=#<,7hCn%fp5Fp3FP:P3K0<%P<P8P3Pf1TFh#tQ095FZCr1AC9RZP3PhPbPE%<>J0;PZP3P4P5P6Dh%Z5%Zb'5%Y5%Yb'5%>kRZ#P159nA3J4fA3K5b3I[%pc#>%p9#>[AX945fKR>9Xkc5}1,y1'2\Z3IDGDGXiI,RIXjaP4I0:%dpRp1AC5P|Pp209~7P6P2P31ACjR2H0TP2n010000002000033g01Q7,m1#d1zC51zCj3311C5/5m208CjQ0<'j208C5'6DGXbK,RKZ0<J,RJXs1,R1Z0AD,RDWa60b8P3A:F^ARA#>Q0?PdPiPgP_P^P]P[P=PYPVQ03Q01P}PwPlPzPyPtPMPLPxPNPvPuPoP;POPrPqP:PnPkPhP~PfPcPbP>PEP`fHRFQ0:P@Q06Q05Q04PRPUQ07Q02PWPXPPPSP{PTP0f7R8P\P9P4P5P3OoW1P3O115ABPePdPiPgP_P^P]P[P=PYPVQ03Q01P}PwPlPzPyPtPMPLPxPNPvPuPoP;POPrPqP:PnPkPhP~PfPcPbP>PEP`PFQ0:P@Q06Q05Q04PRPUQ07Q02PWPXPPPSP{PTP0P8P\P9P4P5P3OoW1P3O1n200100001021000010000b1WHWGWBWFWEWDWIW:X9QX8QX2QW7W6W5W4Z0?GY03XdKWcZ0>JY0=Xm1Z011Xl1Xk1Xg1WhWeWCZ0:GZ09GZ08GZ07GXwGXvGZ00GX~GX}GX|GX{GXzGXyGXxGX`GX_GX^GX]GX\GX[GXZGXYGXuGXtGZ06GZ05GZ04GZ0;GXfGZ02GWrWJY0@g01QVeWAW@o"). Qed.

(* [comment removed for export] *)
Definition pixOr_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixd -> a2 = Z_to_bv 64 pixs -> pixd <> pixs ->
  pix1c (rt_live RT Σ) m pixd vd cvd -> pix1c (rt_live RT Σ) m pixs vs cvs -> p_w vs = p_w vd -> p_h vs = p_h vd -> p_data vs <> p_data vd ->
  List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs) ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 5 0 16 ->     (* [comment removed for export] *)
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixOr m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data vd, p_data vd + rsize vd)] m m'
          /\ pix1c (rt_live RT Σ') m' pixd vd cvd /\ pix1c (rt_live RT Σ') m' pixs vs cvs) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 16 <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition legal1 (w h : Z) : Prop := 1 <= w <= 20000 /\ 1 <= h <= 20000 /\ 4 * (((w + 31) / 32) * h) <= 0x4000000.
(* [comment removed for export] *)
Definition pixCreate1_sure_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> a2 = Z_to_bv 64 1 -> legal1 w h ->
  (* [comment removed for export] *)
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreate m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix1c (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_cmap v = 0) c
       /\ rt_live RT Σ' = pix_new_live pix v (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').
(* [comment removed for export] *)
Definition pix_clone1_sure_cps (entry : Z) (cost : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  (entry = e_pixCopy_po -> a0 = Z_to_bv 64 0 /\ a1 = Z_to_bv 64 pixs) -> (entry <> e_pixCopy_po -> a0 = Z_to_bv 64 pixs) ->
  pix1c (rt_live RT Σ) m pixs vs cvs ->
  (* [comment removed for export] *)
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 4 cost -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pixd <> 0 /\ pix1c (rt_live RT Σ') m' pixd vd cvd
          /\ p_w vd = p_w vs /\ p_h vd = p_h vs /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = pix_copy_live pixd vd cvd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - cost <= rt_credit RT Σ').
Definition pixCreateTemplate1_sure_cps : Prop := pix_clone1_sure_cps e_pixCreateTemplate_po (RASTER_COST + 64).   (* [comment removed for export] *)
Definition pixCopyNew1_sure_cps : Prop := pix_clone1_sure_cps e_pixCopy_po (RASTER_COST + 64).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixCreateHeader_res0_cpsF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 1 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateHeader m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v = 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)))) c
       /\ rt_live RT Σ' = (if pix =? 0 then rt_live RT Σ else (pix, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

Definition pixCreateHeader_res0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 1 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateHeader m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v = 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)))) c
       /\ rt_live RT Σ' = (if pix =? 0 then rt_live RT Σ else (pix, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreate_res0_cpsF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreate m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)))) c
       /\ rt_live RT Σ' = (if pix =? 0 then rt_live RT Σ else (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

Definition pixCreate_res0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreate m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)))) c
       /\ rt_live RT Σ' = (if pix =? 0 then rt_live RT Σ else (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixDeserialize_res0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (dp n : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 dp -> a1 = Z_to_bv 64 n -> 0 <= n < 2^26 -> 0 < dp -> (n < 28 \/ (dp mod 8 = 0 /\ own_live (rt_live RT Σ) dp n)) ->
  uctx m sp s0 ras ->
  Forall (fun r => Forall (fun f => In (f :: r :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS) DESER_DESTROY_RAS ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 6 5 (RASTER_COST + 64) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDeserialize m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v cv /\ p_data v <> 0 /\ res0d v))) c
       /\ (pix = 0 -> rt_live RT Σ' = rt_live RT Σ)
       /\ (pix <> 0 -> live_destroy pix v cv (rt_live RT Σ') = rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ'
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4).

Lemma pixCreateHeader_res0_cps_of_F : pixCreateHeader_res0_cpsF -> pixCreateHeader_res0_cps.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_iface ()) ["PoIface"] "p'0h02m'h12msh21vh33pixh43Σ'h52H8h61ch73H10h83H11h93H13h:3H14h;2H9h<2Hch=1Fh>1Hh?3H12h@3H15hA3HmshB3PMchC2a0hD2a1hE2a2hF2a3hG2a4hH2a5hI2a6hJ2a7hK1dhL2fchM2gphN1hhO2lohP1mhQ2rahR2s0hS2s1hT3s10hU3s11hV2s2hW2s3hX2s4hY2s5hZ2s6h[2s7h\2s8h]2s9h^2sph_2t0h`2t1ha2t2hb2t3hc2t4hd2t5he2t6hf2tphg1whh1xi001xhi2x0hj2x1hk2x2hl2Σp%0p&0p;1p;2p;3p;6p;5p;Sp;4p;Dp;Cp;7p;Ep;8g00>Xk10>Tg00>3j1XTg00?Pj1fTg00?nj1gTg00@Qj1uTg00A6k209Tg00Abk106Tg00BDk104Tg00CBk101Tg00D>j2@Tg00:0j33j2rTg01R`j2vTg006gj1bTg00OHk10=Tg00PCk60;Tg00Q[k50:Tg00lTlSsTg00mQk408j5_Tg00nJlDATg00Ddj21Tg010?j2qTg00MOk103Tg01SZk402Tg00Goj1[Tg00Hij1kTg005mj19Tg008AS00j20Tg0144S01j22Tg00bQj1nTg00Moj3CTg015mj2;Tg00Vlj2ETg016kj2WTg01TXlC6Tg00oCj74Tg01USj5PTg00XAj2JTg011?j7ZTg01VQj1\Tg01WNlE}Tg009Uj4QTg01XNj4eTg01Xhj8|Tg01Yfj8{Tg007Ej1zTg0137k105Tg0043j1yTg0050k107Tg00Wgj2^Tg014Nj2xTg010_j4tTg017ij2mTg00:JR0f0R1g00:hR233p=Sf5R3f4R4'1f3R5f2R6f1R7P1DPp>00A3071p=5%z7=301p=<&055=302%y6=302&077=302/01'0'0p=:%\7=302/01p=wA3045A3067/01'0p=?A3067/01,05,^4p=Hf7R8f6R9P3P4P5P6P7FZ/01p=8P8P9P3P4P5P6P7F4/01p=Y1x12p=LP0P0P7P1Ctp>0<1W56/m7/J1p=a1E679305/01p=`A38931;679345/01'0p=VP3P4P5P6P7D_/01p=7g00;FR:/21p=>1201p=D1071,06p==1W45/m61W71'Jp=I1E451E67530/01p=NA38931;56=347/01'0p=MP81193P4P5P6P7P1FZp=UA3067/01p=K1^71,06,05,04p=G1W67/m1p=TA3934A3567/01'0p=]1193P4P5P6P7DP/01p=l1W71,J6p=R1E56=307/01p=dA3092P3P4P5P6P7DP/01'^p=pP0P0P6P7Ct=C51p=OA30821193P4P5P6P7DP/01'^p=F%[8=309%k3=304A3056%\7=302/01'0'0'0p=B1;56=347/01p=o1;67=351p=h1E67=301p=iP8P9P3P4P5DPA3067/01'0p=c%k3=304A3056A3072/01'0'0p=j1^71,06p=~g01Zbp,2RTR;$0>R<g01BWp-0[g00<CR=#XR>#X#XR?#X#XR@#XRA#fRB#gRC%u>#f009C%f@#g%f?#g$06\CR?fVS02$04fWR@$01fTRDg01EF,@B53CfORE/v3S03Q03Q03P;f]RFf:RGfZRHf9RI%u=#b$0=J0;P;f^RJ%b=R=P=%b>R>I0:g01=<P;f_S04PJg01N3RKPFf\RLf[RMPHfYS05fXRNP@Q02fUROPDfSRPfRRQfQRRfPRSPEfNRTfMRUfLRVfKRWfJRXfIRYfHRZfGR[fFR\fER]fDR^fCR_fBS06fAS07f@R`f?S08f>Raf=Rbg01\0Rcf<S09MSs'rH08RdPdg01PBS0:P;P6fbRdfcRePdfaS0;f`S0<PLPMPQPRPSPEPTPUPVPWPXPY1@B5S0=P^P1P7MDAP;feRfP4Q06P1PdQ07P;11;fRgPfPd1q00Rh$03RiQ06P1%S5S0>P;P4P1P5P6P2P2P2P2H02R2J00S0?%[6RjP`%k6RkQ08%96RlPaP6P6P615l=1<5=[C:,w6RmD?DHG8GYRn'0X0?,2?X1KP5%nhRo11;6S0@g01LVRpPo%L7S0A11;eRq%bAS0B-0<7RA=Chqn0100000020000g01Q7,q0#nRq1;;6S0CP;Pe1E;6RrP;PeP;PeP>1W;6RsCaC`GVRtE7X2:#>X30#DX4<,2<W6Q0:P;P6PdPePdQ0;Q0<PLPMPQPRPSPEPTPUPVPWPXPYQ0=P1P7MC6/0nX0?,2?X1KP5PtE7X2:#>X30#DX4<,2<W6Q0<Q04PJPFPLPMPHQ05PNP@Q02POPDPPPQPRPSPEPTPUPVPWPXPYPZP[P\P]P^P_Q06Q07P`Q08PaPbQ09f;S0DPGPIf8S0EP8P9P3P4P5P6P7P1O`Q0:P;Q0<Q04PJPFPLPMPHQ05PNP@Q02POPDPPPQPRPSPEPTPUPVPWPXPYPZP[P\P]P^P_Q06Q07P`Q08PaPcPbMSs,rKP1D_P1W<W6Q0:Q0:P;P6PefdRcPePdQ0;PFPLPPPQPRPSPEPTPUPVPWPXQ0=P]P1P7MDAP;ffRaP4P_P1PeQ06P;11;aRtPaPePiP_P1Q0>Q0?PjQ07PkP`PlQ08PmD?DHG8GYS0F'0X0?,2?X1KRnP5PoQ0@PpPoQ0A11;cRuAChAun0100000020000PqQ0CP;PcPrP;PcP;PcP>PsCaC`GVS0GE7X2:#>X30#DX4<,2<W6P1O1Q01P<P;P6PePnP4Q0GE7X2:#>X30#DX4<P;P6PcPfPcPePdPJPFPDPPPQPRPSPEPTPUPVPWQ0=P1P7MC6P;fgRnP4P^P1PcP_F4P;11;nRuPnPcPiP^P1Q0>Q0?PjQ06PkQ07PlP`PmD?DHG83=X0?,2?X1KP3PoQ0@PpPoQ0APgAChAgn0100000020000PqQ0CP;PfPrP;PfP;PfP>PsCaC`GVE7X2:#>X30#DX4<,2<P1P;P6PfPaPfPcPeQ04PJPOPDPPPQPRPSPEPTPUPVQ0=P[P1P7MDAP;fhRgP4P]P1PfP^F4P;11;gPgPfPiP]P1Q0>Q0?PjP_PkQ06PlQ07PmD?DHG83=X0?,2?X1KP9PoQ0@PpPoQ0APtAChAtn0100000020000PqQ0CP;PaPrP;PaP;PaP>PsCaC`GVE7X2:#>X30#DQ01P0P;P5PaPnPaPfPcQ0<Q04Q02POPDPPPQPRPSPEPTPUQ0=PZP1P7MDAP;fiRtP3P\P1PaP]F4P;11;tRvPtPaPiP\P1Q0>11;3RwP1P5P6P2DPPjP^PkP_PlQ06PmD?DHG83=X0?,2?X1KP8Po11;5PpPoQ0APuAChAun0100000020000PqP;P51;;nP;P5P;PnP;PnP>P;P5DIDNGME7X2:#>X30P;P6PgPtPgPnPaPdQ0;PNP@Q02POPDPPPQPRPSPEQ0=P1P7MC6P;fkRuP4PZP1PgP[F4P;P;PuPuPgPiPZP1GURxQ0>Q0?PjP\PkP]AKl^mD?Ry'0DGX0?,2?X1KPIPoQ0@PpPoQ0APvAChAvn0100000020000RvPqQ0C1;;tRz1E;tR{AT;t>R|/Js5KrF]E7X2:#>X30#DX4<,2<P1P;P3PgPtPgPnPaPdQ0;PNP@Q02POPDPPPQPRPSPEQ0=PXP1P7MDAP;PuP8PZP1PgP[F4PxQ0>P;P8P1P5P6P2PyFlDGX0?,2?X1KPIPoPwPvPqP;P3PzP;P3P{AR|;3CdGME7X2:#>Q01P:P;P9PtfjR|PtPgPnPePdQ05PNP@Q02POPDPPPQPRPS1@B4PWP1P7MDAP;flR{Q0EPYP1PtPZF4P;11;{RzP{PtPiPYP1P4Q0E,1;S0HP1P4P6P2PjP[PkP\AKl]mD?FpG83=X0?,2?X1KPGPo11;9PpPo%L611;|RvPhP6Q0BPvCOn0100000020000PqP;P91;;|P;P9P;P|P;P|P>P;P9DIDNGME7X2:P;P6P{fmRvP{PuP|PaPfPLPMPHQ05PNP@Q02POPDPPQ0=P1P7MC6P;foS0IP4PVP1P{PWF4P;P;Q0IQ0IP{PiPVP1GURwQ0>Q0?15jXPkPYPlPZPmD?3=DGX0?,2?X1KPbPoQ0@PpPoQ0A11;vRyAChAyn0100000020000PqQ0C1;;vS0J1E;vRxAT;v>R}/Js5KrF]E7X2:#>X30#DX4<,2<P1P;Q0EPuP{PuP|PtPfPcPMPHQ05PNP@Q02POPDPPPQ1@B9PUP1P7MDAP;fnR~PGPWP1PuPXF4P;11;~P~PuPiPWP1P9P;PGP1P9P6P2PjPYPkPZAKl[mD?GFG83=X0?,2?X1KQ09PoQ0HPpPo%L4PzPhP4Q0BPzCOn0100000020000PqP;Q0E1;;{P;Q0EP;P{P;P{P>P;Q0EDIDNGME7Q00P;PIP{PvP{PuP|PaPfPLPMPHQ05PNP@Q02POPDPP1@B8PTP1P7MDAP;Q0IQ0DPVP1P{PWF4Pw%S8P;Q0DP1P8P5P2P5PXP5PY%95RwPZP5P5P5P515w=1<4=[C:GBFlDGX0?,2?X1KPbD_Po11;IPpPo%L3PyPhP3Q0BPyCOn0100000020000PqP;PIQ0JP;PIPxAR};ICdGMP;P6fpS0JfqR}Q0JQ0IP~P|PtQ0<Q04PJPFPLPMPHQ05PNP@Q0=P1P7MC6P;fsS0HP4PSP1Q0JPEF4P;Q0H,1;RxQ0HQ0JPiPSP1Q0>Q0?PjPTPkPUPlPVPmD?DHG83=X0?,2?X1KQ07PoQ0@PpPoQ0A11;}RyAChAyn0100000020000PqQ0C1;;}S0K1E;}S0LAT;}>Rw/Js5KrF]E7X2:#>X30#DX4<,2<P1P;Q0DP~Q0IP~PvP{PgPnPJPFPLPMPHQ05PNP@Q02PO1@BIPSP1P7MDAP;P}PbPTP1P~PUF4P;PyP}P~PiPTP1PI11;bRzP1PIP3P2P3PVP3PW%93RGPXP3P3P3P315G=1<9=[C:GBFpG83=X0?,2?X1KQ08D_PoQ09,1;PpPoQ0E#LQ0J,1;R9PhQ0EQ0BP9COn0100000020000PqP;Q09Q0J,;;P;Q09P;Q0JP;Q0JP>P;Q09DIDNGMQ00PpPo%LIPyPhPIQ0BPyCOn010000002000093ozPqP;PbQ0KP;PbQ0LARw;bCdDoP;P6ftS0LfuRwQ0LQ0HfrS0KP~PvPcPePdQ0;Q0<Q04PJPFPLPMQ0=P1P7MC6P;fwRzP4PDP1Q0LPPF4P;11;zPzQ0LPiPDP1Q0>Q0?PjPQPkPRPlPSPmD?DHG83=X0?,2?X1KP]PoQ0@PpPoQ0A11;wRyAChAyn0100000020000PqQ0C1;;wRy1E;wR9AT;w>RG/Js5KrF]E7X2:#>X30#DX4<,2<P1Q08,1;PpPoQ0D#LPxPhQ0DQ0BPxCOn010000002000053oPqP;P`Q0L,;;P;P`P;Q0LP;Q0LP>P;P`DIDNDoQ00PqP;Q07PyChP;Q07P9Q079RG;CdP;P6fxS0MfyS0NQ0MPzfvS0OQ0KP}PgPnPaPfPcPePdQ0;Q0<Q04Q0=P1P7MC6P;f{RGP4PNP1Q0MP@F4P;11;GPGQ0MPiPNP1Q0>Q0?PjQ02PkPOPlPDPmD?DHG83=X0?,2?X1KPYPoQ0@PpPoQ0AQ0N,1;R9AChA9n0100000020000PqQ0CP;Q0NQ0N,E;R9Q0N=T;>Ry/Js5KrGVE7X2:#>X30#DX4<,2<P1PqP;P_1;;zChP;P^P;Q0MP;Q0MP>P;P^DIDNQ00Ai;]9ARy;]P;P6f|Ryf}R9PyPGfzS0PQ0OPwP{PuP|PtPgPnPaPfPcPeQ0=P1P7MC6P;p+01@R`P4PLP1PyPMF4P;11;`S0QP`PyPiPLP1FZS0RQ0>Q0?15jHPkQ05PlPNPmD?3=DGX0?,2?X1KPUPoQ0@PpPoQ0A11;9S0SQ0S9ChAn0100000020000PqQ0C1;;9S0T1E;9S0UAT;9>S0V/Js5KrF]E7X2:#>X30#DX4<,2<P11E;G9i;[P;PyP>P;PZDIP<P;P6P`p+01AS0WP`f~RxP9Q0NQ0MQ0IP~PvP{PuP|PtPgPnPaQ0=P1P7MC6P;p+01CS0XP4Q04P1P`PJF4P;P;Q0XQ0XP`PiQ04P1GUS0YQ0>Q0?15jFPkPLPlPMPmD?3=DGX0?,2?X1KPSPoQ0@PpPoQ0AQ0W,1;S0@Q0@9ChAn0100000020000PqQ0CP;Q0WPrP;Q0WP;Q0WP>PsCaC`GVE7X2:#>X30#DX4<PYP0P;PWPxP`PxP9PyQ0MPzP~PvP{PuP|PtPgPnPaPfQ0=P1P7MC6P;p+01BRsPUPJP1PxPFF4S0CP;P;PsPsPxPiPJP1GUS0?Q0>11;US0>P1P5P6P2PjPLPkPMPlPHPmD?GcDGX0?,2?X1KPEPo11;WS0ZPpPoQ0AQ0QQ0Q9ChAn0100000020000PqP;PW1;;`P;PWP;P`P;P`P>P;PWDIDNGME7X2:#>X30P]P:P;PXP9PxP9PyPGPzQ0OPvP{PuP|PtPgPnPaPfPc1@BZRAP1P7MC6P;Q0WPVPFP1P9PLF4S0QP;Q0@Q0WP9PiPFP1FZRr%SZS0@11;VS0AP1PZP6P2PjPMPkPHPlQ05PmD?GcDGX0?,2?X1KPTPo11;XPpPo%L\11;xRmPhP\Q0BPmCOn0100000020000PqP;PX1;;xP;PXP;PxP;PxP>P;PXDIDNGME7X2:Q07P;PYPyP9PyPGQ0PQ0OPwP{PuP|PtPgPnPaPfPcPe1@B[R>P1P7MC6P;P`PWPLP1PyPMQ0R%S[Q0ZP1P[P_P2%[_PHP_Q05%9_RmPN%\_P_P_P_15m=1<^=[C:EjGc3~GYRm'0X0?,2?X1KR_PUD_11;YPpPo%L]Q0SPhP]Q0BQ0SCOn010000002000053oRoPqP;PYQ0TChRqQ0U9i;YRhQ0V?R;YRp'0Rl'0Rk'0P;PYPyP9PyPGQ0PQ0OPwP{PuP|PtPgPnPaPfPcPeP>PJP1P7MDA/0mX0?,2?X1KP_PUPbPxP9PyPGPzQ0OPvP{PuP|PtPgPnPaPfPcPAQ04P1P7MDAQ0QQ0@Q0AP1PZP^P2DP%[^PMP^PH%9^R_Q05%\^P^P^P^15_=1<]=[C:EjDH7=rRr'0X0?,2?X1KP1O1Q01P?PxP9PyPGPzQ0OPvP{PuP|PtPgPnPaPfPcPAQ04P1P6MDA/0rX0?P`PxP9PyQ0MPzP~PvP{PuP|PtPgPnPaPf1@BYP1P5MC6Q0CQ0?%SYQ0>P1PYP]P2%[]PLP]PM%9]R_PH%\]P]P]P]15_=1<\=[C:EjGcDGX0?,2?P1Q0WP`PxP9Q0NQ0MQ0IP~PvP{PuP|PtPgPnPa1@BXQ0;P1P4MDAP;Q0XPTQ04P1P`PJF4Q0Y%SXP;PTP1PXP\P2P\PFP\PL%9\R_PMP\P\P\P\15_=1<[=[C:GBFlDGQ00PsQ0WP`PxQ0PQ0NQ0JQ0IP~PvP{PuP|PtPgPn1@BWPdP7P3MDAP;p+01DR_PEQ0<P7Q0WQ04P;11;_P_Q0WPiQ0<P7PWP;PEP7PWP[P2P[PJP[PF%9[R\PLP[P[P[P[15\=1<Z=[C:GBGFG8GYP_Q0XPsQ0WPyPGQ0KP}Q0JQ0IP~PvP{PuP|Pt1@BURZP1P8MC6P;p+01FR\PRPdP1Q0XQ0;F4P;11;\P\Q0XPiPdP1PUP;PRP1PUPYP2PYQ0<PYQ04%9YR[PJPYPYPYPY15[=1<X=[C:GBGFG83=X0?,2?P1P_Q0XPsQ0WPyPGQ0KP}Q0JQ0IP~PvP{PuP|PtPZPcP5P8MDAP;p+01GR5PQPeP4P_PdP;11;5P5P_PiPeP4PTP;PQP4PTPXP2PXQ0;PXQ0<%9XRZQ04PXPXPXPX15Z=1<W=[C:GBGFG8GYQ00P;p+01HRZPPPcP3p+01ERsPeF4P;11;ZPZPsPiPcP3PEP;PPP3PEPWP2PWPdPWQ0;%9WR[Q0<PWPWPWPW15[=1<V=[C:GBGFG8PZP5P\PsQ0WP`Q0OPwQ0LQ0HQ0KP}Q0JQ0IP~Pv1@BRP1Q0DMC6P;p+01JR`POPaP1P5PfF4P;11;`P`P5PiPaP1PRP;POP1PRPUP2PUPcPUPe%9UR[PdPUPUPUPU15[=1<T=[C:GBGFG83=X0?,2?P1P;P`POPaP8P5PfF4P;p+01KR8,1;P8PZPiPnQ0EPQP;Q02Q0EPQPTP2PTPfPTPc%9TR[PePTPTPTPT15[=1<E=[C:GBGFG8Q00P;P;p+01LR[P[p+01IRYPiPgPIGUPPP;P@PIPPPEP2PEPaPEPf%9ERJPcPEPEPEPE15J=1<S=[C:GBGFP[P8P`PYPsP_Q0PQ0NQ0MPzQ0OPwQ0LQ0HQ0KP}1@BOP1Q08MC6P;p+01NR}Q05P|P1P8PtF4P;11;}R_P}P8PiP|P1POP;Q05P1POPRP2PRPgPRPn%9RRsPaPRPRPRPR15s=1<Q=[C:GBGFG83=X0?,2?P1P;P_P}P8PiP|Q0DFZQ02P;PHQ09Q02PQP2PQPtPQPg%9QRHPnPQPQPQPQ15H=1<P=[C:GBGFP?p+01OP}p+01MRHP[PZP5P9PyPGQ0PQ0NQ0MPzQ0OPwQ0L1@BNP1Q06MC6P;p+01QRZPLPvP1P}P{F4P;11;ZPZP}PiPvP1PNP;PLP1PNPDP2PDPuPDP|%9DRNPtPDPDPDPD15N=1<O=[C:GBGFG83=X0?PbP}PHP[P8P5P\PyPGQ0PQ0NQ0MPzQ0OPwQ0LQ0H1@B@RBPbQ07MC6P;p+01PROPMP{PbPHPuF4RNP;P;POPOPHPiP{PbGURiP@P;PMPbP@PPP2PPP|PPPt%9PR2PgPPPPPPPP152=1<D=[C:GBGFR='0RD'0P}PHP[P8P5P\PyPGQ0PQ0NQ0MPzQ0OPwQ0LQ0HPBP~PbQ07PIME}PNPDP3PiP=P7P1CQCQCQCeW@W:P7P1O2n2001000000121000000W:W9P7P1O2n2001000000121000000W9W5P7P1O2n2001000000121000000W5Xk?P7P1O2n2001000000121100000PxP9PyPGPzQ0OPvP{PuP|PtPgPnPaPfPcPAP1P6MC6/0rX0?,2?eWAX1KG|PoPkPIPqPlP3PhPpP7P1CQCQCQCQCeCeCeW?W8P7P1O2n2001000010121000000W8W7P7P1O2n2001000010121000000W7W;P7P1O2n2001000010121000000W;W5P7P1O2n2001000010121000000W5Xj:P7P1O2n2011000010121100000W5Xi0P7P1O2n2011000010121100000W5Xh<P7P1O2n2011000010121100000P;P6PePcPePdQ0;PFPLPPPQPRPSPEPTPUPVPWPXQ0=P1P7MC6Q0F'0X0?,2?X1KP4Q0GE7X2:#>X30#DX4<,2<R<eP<eW<W6G{UUUUUUUUXK0XN0Xg0XO0WPWLW=XeCXdCXcCXbCXUCXTCX]CX\CX[CXZCXYCXXCXWCXVCXJCXICXHCXGCXFCXECXDCXCCXSCXRCXaCX`CX_CXfCXMCX^CWQWBWlg01]8eW>o"). Qed.
Lemma pixCreate_res0_cps_of_F : pixCreate_res0_cpsF -> pixCreate_res0_cps.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_iface ()) ["PoIface"] "p'0h02m'h12msh21vh33pixh43Σ'h52H9h61ch73H10h83H11h93H12h:3H14h;3H15h<2Hch=1Fh>1Hh?3H13h@3H16hA3HmshB3PMchC2a0hD2a1hE2a2hF2a3hG2a4hH2a5hI2a6hJ2a7hK1dhL2fchM2gphN1hhO2lohP1mhQ2rahR2s0hS2s1hT3s10hU3s11hV2s2hW2s3hX2s4hY2s5hZ2s6h[2s7h\2s8h]2s9h^2sph_2t0h`2t1ha2t2hb2t3hc2t4hd2t5he2t6hf2tphg1whh1xi001xhi2x0hj2x1hk2x2hl2Σp%0p&0p;1p;2p;3p;6p;5p;Sp;4p;Dp;Cp;7p;Ep;8g00>Xk10ITg00>3j1QTg00?Pj1jTg00?nj1sTg00@Qj1~Tg00A6k20ETg00Abk10CTg00BDk10ATg00CBk10<Tg00D>j2?Tg00:0j32j2{Tg01R`k203Tg006gj1UTg00OHk10HTg00PCk60GTg00Q>k200Tg00Q[k50FTg00Ddj21Tg00RVk10DTg00XAj2HTg00lTlS|Tg00mQk40Bj5`Tg00nJlDBTg010?j2xTg00MOk10=Tg01SZk40;Tg00Goj1[Tg00Hij1kTg005mj19Tg008AS00j20Tg0144S01j23Tg00bQk101Tg01VQj1LTg01^Ej1\Tg015mj2:Tg00Vlj2ETg016kj2ZTg01TXlC6Tg00oCj74Tg01USj5RTg011?j7]Tg01WNmE08Tg009Uj4STg01XNj4fTg01Xhk809Tg01Yfk806Tg007Ek105Tg0137j1uTg0043j1tTg0050j1wTg00GVj1iTg00Wgj2dTg014Nk204Tg010_j4}Tg00Moj3oTg017ij2nTf0R0#Q#Qp=z%Q0#Q#Q#Qp=_g00:JR1g00:hR2720p=Tf5R3f4R4'1f3R5f2R6f1R7P0DRp>07A2170p=5&057=210p=;%u5=212%t6=212%w7=212/00'0'0p=<%L7=212#i/00p>02A2145A2167/00'0p=AA2167/00,05,d4p=Kf7R8f6R9P3P4P5P6P7F]/00p=8P8P9P3P4P5P6P7F4/00p=e20402p=NP1P1P7P0C}p=cAo6709o45p=@1Z56/n7/H0p=b1E679215/00p=aA28931:679245/00'0p=YP3P4P5P6P7D`/00p=7g00;FR:/30p=>1310p=C1070,06p==1Z45/n61Z70'Hp=J1E451E67521/00p=PA28931:56=247/00'0p=OP81193P4P5P6P7P0F]p=XA2167/00p=M1d70,06,05,04p=I1Z67/n0p=VA2934A2567/00'0p=^1193P4P5P6P7DR/00p=r1Z70,H6p=W1E56=217/00p=hA2192P3P4P5P6P7DR/00'dp=yA21821193P4P5P6P7DR/00'dp=F%[8=219%k3=214A2156%L7=212#i/00'0'0'0p=DP1P1P6P7C}=o50p=G%t6=212%w7=212/00'0p>0@A2145%i6%u7=212/00'0'0p>0?%[4=215%k6=217/00'0p>0>1:56=247/00p=v1:67=250p=l1E67=210p=mP8P9P3P4P5DRA2167/00'0p=g%L0=212p=q%k3=214A2156%i7/00'0'0p=p1d70,06p>0:g01_Ap,2RTR;$0IR<g01BWp-0[g00<CR=#QR>#zR?#zR@#QRA#jRB#sRC%~>RD#j00EC%j@#s%j?#s$0C\CR@fVRE$0AfWRF$0<fTRGg01EF,?B52CfORH0033S02Q02Q02P;f]RIf:RJfZS03f9RK%UD$0HJ0GP;f^RD%~=#U%U>g01`I%U?+00R?I0Ff_S04,1;$0D%_A#_#_#_#_#U+00g01Gm'Hg01=<P;f`S05Q04g01N3R>PDPIf\RLf[RMQ03fYRNfXS06PFPEfUROPGfSRPfRRQfQRRfPS07PHfNRSfMRTfLRUfKRVfJRWfIRXfHRYfGRZfFR[fER\fDR]fCR^fBS08fAR_f@R`f?S09f>Rag01aKRbf=RcMS|'{H0BRdPdg01PBS0:P;P6fcRdfdRePdfbS0;faS0<PIPLPPPQPRQ07PHPSPTPUPVPW1?B5S0=P\P0P7MDBP;ffRfP4P^P0PdQ08P;11;fRgPfPd1x11Rh$0=RiP^P0%T5S0>P;P4P0P5P6P2P2P2P2H0;R2J07S0?%[6RjP_%k6RkP`%96RlQ09P6P6P6%U=R=,5l1;5=[C<-026RmDADKG8GeRn'0X0@,3@X1>P5&01hRo11;6S0@g01LVRpPo%N7S0A11;eRqPh%L0%\0'cRrPh%UAS0B,c7S0CPqD@n0100000020000g01Q7,x1$01Rq1:;6S0DP;Pe1E;6RAP;PeP;PeP?1Z;6RsCbCaGYRtE7X2:#>X31#CX4<,3<W6Q0:P;P6PdPePdQ0;Q0<PIPLPPPQPRQ07PHPSPTPUPVPWQ0=P0P7MC6/0nX0@,3@X1>P5PtE7X2:#>X31#CX4<,3<W6Q0<Q05Q04PDPIPLPMQ03PNQ06PFPEPOPGPPPQPRQ07PHPSPTPUPVPWPXPYPZP[P\P]P^Q08P_P`Q09PaPcf<S0Ef;S0FPJPKf8S0GP8P9P3P4P5P6P7P0OaQ0:P;Q0<Q05Q04PDPIPLPMQ03PNQ06PFPEPOPGPPPQPRQ07PHPSPTPUPVPWPXPYPZP[P\P]P^Q08P_P`Q09PbPaMS|,{>P0D`P0W<W6Q0:Q0:P;P6PefeRaPePdQ0;PDPIPGPPPQPRQ07PHPSPTPUPVQ0=P[P0P7MDBP;fgRbP4P]P0PeP^P;11;bRtPbPePiP]P0Q0>Q0?PjQ08PkP_PlP`PmDADKG8GeS0H'0X0@,3@X1>RnP5PoQ0@PpPoQ0A11;aRuPhPrPhQ0CPuD@n0100000020000PqQ0DP;PaPAP;PaP;PaP?PsCbCaGYS0IE7X2:#>X31#CX4<,3<W6P0O1Q01P<P;P6PePnP4Q0IE7X2:#>X31#CX4<P;P6PaPfPaPePdQ04PDPOPGPPPQPRQ07PHPSPTPUQ0=P0P7MC6P;fhRnP4P\P0PaP]F4P;11;nRuPnPaPiP\P0Q0>Q0?PjP^PkQ08PlP_PmDADKG83=X0@,3@X1>P3PoQ0@PpPoQ0APgPhPrPhQ0CPgD@n0100000020000PqQ0DP;PfPAP;PfP;PfP?PsCbCaGYE7X2:#>X31#CX4<,3<P0P;P6PfPbPfPaPeQ05Q04PEPOPGPPPQPRQ07PHPSPTQ0=PYP0P7MDBP;fiRgP4P[P0PfP\F4P;11;gPgPfPiP[P0Q0>Q0?PjP]PkP^PlQ08PmDADKG83=X0@,3@X1>P9PoQ0@PpPoQ0APtPhPrPhQ0CPtD@n0100000020000PqQ0DP;PbPAP;PbP;PbP?PsCbCaGYE7X2:#>X31#CQ01P1P;P5PbPnPbPfPaQ0<Q05PFPEPOPGPPPQPRQ07PHPSQ0=PXP0P7MDBP;fjRtP3PZP0PbP[F4P;11;tRvPtPbPiPZP0Q0>11;3RwP0P5P6P2DRPjP\PkP]PlP^PmDADKG83=X0@,3@X1>P8Po11;5PpPoQ0APuPhPrPhQ0CPuD@n0100000020000PqP;P51:;nP;P5P;PnP;PnP?P;P5DJDPGOE7X2:#>X31P;P6PgPtPgPnPbPdQ0;PNQ06PFPEPOPGPPPQPRQ07Q0=P0P7MC6P;flRuP4PXP0PgPYF4P;P;PuPuPgPiPXP0GXRxQ0>Q0?PjPZPkP[AMl\mDARy'0DIX0@,3@X1>PKPoQ0@PpPoQ0APvPhPrPhQ0CPvD@n0100000020000RvPqQ0D1:;tRz1E;tR{AV;t?R|/Hs5MAF^E7X2:#>X31#CX4<,3<P0P;P3PgPtPgPnPbPdQ0;PNQ06PFPEPOPGPPPQPRQ07Q0=PVP0P7MDBP;PuP8PXP0PgPYF4PxQ0>P;P8P0P5P6P2PyFrDIX0@,3@X1>PKPoPwPvPqP;P3PzP;P3P{AW|;3ChGOE7X2:#>Q01P:P;P9PtfkR|PtPgPnPePdQ03PNQ06PFPEPOPGPPPQPR1?B4PUP0P7MDBP;fmR{Q0GPWP0PtPXF4P;11;{RzP{PtPiPWP0P4Q0G,1;S0JP0P4P6P2PjPYPkPZAMl[mDAFyG83=X0@,3@X1>PJPo11;9PpPo%N611;|RvPhPrPhQ0B,c6PvD@n0100000020000PqP;P91:;|P;P9P;P|P;P|P?P;P9DJDPGOE7X2:P;P6P{fnRvP{PuP|PbPfPIPLPMQ03PNQ06PFPEPOPGQ0=P0P7MC6P;fpS0KP4PTP0P{PUF4P;P;Q0KQ0KP{PiPTP0GXRwQ0>Q0?15jVPkPWPlPXPmDA3=DIX0@,3@X1>PcPoQ0@PpPoQ0A11;vRyPhPrPhQ0CPyD@n0100000020000PqQ0D1:;vS0L1E;vRxAV;v?R}/Hs5MAF^E7X2:#>X31#CX4<,3<P0P;Q0GPuP{PuP|PtPfPaPLPMQ03PNQ06PFPEPOPGPP1?B9PSP0P7MDBP;foR~PJPUP0PuPVF4P;11;~P~PuPiPUP0P9P;PJP0P9P6P2PjPWPkPXAMlYmDAGFG83=X0@,3@X1>Q0EPoQ0JPpPo%N4PzPhPrPhQ0B,c4PzD@n0100000020000PqP;Q0G1:;{P;Q0GP;P{P;P{P?P;Q0GDJDPGOE7Q00P;PKP{PvP{PuP|PbPfPIPLPMQ03PNQ06PFPEPOPG1?B8PHP0P7MDBP;Q0KQ0FPTP0P{PUF4Pw%T8P;Q0FP0P8P5P2P5PVP5PW%95RwPXP5P5P5P515w=1;4=[C<GDFrDIX0@,3@X1>PcD`Po11;KPpPo%N3PyPh%L7%\7PhP3Q0BPyCGCGn0100000020000PqP;PKQ0LP;PKPxAW};KChGOP;P6fqS0LfrR}Q0LQ0KP~P|PtQ0<Q05Q04PDPIPLPMQ03PNQ06Q0=P0P7MC6P;ftS0JP4PRP0Q0LQ07F4P;Q0J,1;RxQ0JQ0LPiPRP0Q0>Q0?PjPHPkPSPlPTPmDADKG83=X0@,3@X1>P_PoQ0@PpPoQ0A11;}RyPhPrPhQ0CPyD@n0100000020000PqQ0D1:;}S0M1E;}S0NAV;}?Rw/Hs5MAF^E7X2:#>X31#CX4<,3<P0P;Q0FP~Q0KP~PvP{PgPnQ04PDPIPLPMQ03PNQ06PFPE1?BKPRP0P7MDBP;P}PcPHP0P~PSF4P;PyP}P~PiPHP0PK11;cRzP0PKP3P2P3PTP3PU%93RJPV%L3S0O#TP315J=1;9=[:0@33I0?I0>FyG83=X0@,3@X1>Q09D`PoQ0E,1;PpPoQ0G#NQ0L,1;R9Ph%L4%\4PhQ0GQ0BP9CGCGn0100000020000PqP;Q0EQ0L,:;P;Q0EP;Q0LP;Q0LP?P;Q0EDJDPGOQ00PpPo%NKPyPhQ0O%\3PhPKQ0BPyCGCGn010000002000092ozPqP;PcQ0MP;PcQ0NAWw;cChDvP;P6fuS0NfvRwQ0NQ0JfsS0MP~PvPaPePdQ0;Q0<Q05Q04PDPIPLQ0=P0P7MC6P;fxRzP4POP0Q0NPGF4P;11;zPzQ0NPiPOP0Q0>Q0?PjPPPkPQPlPRPmDADKG83=X0@,3@X1>P\PoQ0@PpPoQ0A11;wRyPhPrPhQ0CPyD@n0100000020000PqQ0D1:;wRy1E;wR9AV;w?RJ/Hs5MAF^E7X2:#>X31#CX4<,3<P0Q09,1;PpPoQ0F#NPxPh%L8%\8PhQ0FQ0BPxCGCGn010000002000052oPqP;P`Q0N,:;P;P`P;Q0NP;Q0NP?P;P`DJDPDvQ00PqP;P_PyClP;P_P9AWJ;_ChP;P6fyS0OfzS0PQ0OPzfwS0QQ0MP}PgPnPbPfPaPePdQ0;Q0<Q05Q0=P0P7MC6P;f|RJP4PNP0Q0OQ06F4P;11;JPJQ0OPiPNP0Q0>Q0?PjPFPkPEPlPOPmDADKG83=X0@,3@X1>PXPoQ0@PpPoQ0AQ0P,1;R9PhPrPhQ0CP9D@n0100000020000PqQ0DP;Q0PQ0P,E;R9Q0P=V;?Ry/Hs5MAGYE7X2:#>X31#CX4<,3<P0PqP;P^1:;zClP;P]P;Q0OP;Q0OP?P;P]DJDPQ00Am;\9AWy;\P;P6f}Ryf~R9PyPJf{S0RQ0QPwP{PuP|PtPgPnPbPfPaPeQ0=P0P7MC6P;p+01AR`P4PIP0PyPLF4P;11;`S0SP`PyPiPIP0F]S0TQ0>Q0?15jMPkQ03PlPNPmDA3=DIX0@,3@X1>PTPoQ0@PpPoQ0A11;9S0UPhPrPhQ0CQ0UD@n0100000020000PqQ0D1:;9S0V1E;9S0WAV;9?S0X/Hs5MAF^E7X2:#>X31#CX4<,3<P01E;J9m;ZP;PyP?P;PYDJP<P;P6P`p+01BS0YP`p+01@RxP9Q0PQ0OQ0KP~PvP{PuP|PtPgPnPbQ0=P0P7MC6P;p+01DS0ZP4Q05P0P`Q04F4P;P;Q0ZQ0ZP`PiQ05P0GXS0[Q0>Q0?15jDPkPIPlPLPmDA3=DIX0@,3@X1>Q07PoQ0@PpPoQ0AQ0Y,1;S0@PhPrPhQ0CQ0@D@n0100000020000PqQ0DP;Q0YPAP;Q0YP;Q0YP?PsCbCaGYE7X2:#>X31#CX4<PXP1P;PVPxP`PxP9PyQ0OPzP~PvP{PuP|PtPgPnPbPfQ0=P0P7MC6P;p+01CRsPTQ04P0PxPDF4S0DP;P;PsPsPxPiQ04P0GXS0?Q0>11;TS0>P0P5P6P2PjPIPkPLPlPMPmDAGgDIX0@,3@X1>PHPo11;VS0\PpPoQ0AQ0SPhPrPhQ0CQ0SD@n0100000020000PqP;PV1:;`P;PVP;P`P;P`P?P;PVDJDPGOE7X2:#>X31P\P:P;PWP9PxP9PyPJPzQ0QPvP{PuP|PtPgPnPbPfPa1?BYRAP0P7MC6P;Q0YPUPDP0P9PIF4S0SP;Q0@Q0YP9PiPDP0F]S0@%TYS0C11;US0AP0PYP6P2PjPLPkPMPlQ03PmDAGgDIX0@,3@X1>PSPo11;WPpPo%N[11;xRmPhPrPhQ0B,c[PmD@n0100000020000PqP;PW1:;xP;PWP;PxP;PxP?P;PWDJDPGOE7X2:P_P;PXPyP9PyPJQ0RQ0QPwP{PuP|PtPgPnPbPfPaPe1?BZR?P0P7MC6P;P`PVPIP0PyPLQ0T%TZQ0\P0PZP^P2%[^PMP^Q03%9^RmPN%q^P^P^P^15m=1;]=[C<EpGg40:GeRm'0X0@,3@X1>R^PTD`11;XPpPo%N\Q0UPh%L_%\_PhP\Q0BQ0UCGCGn010000002000052oRoPqP;PXQ0VClRqQ0W9m;XRhQ0X?W;XRp'0Rr'0Rl'0P;PXPyP9PyPJQ0RQ0QPwP{PuP|PtPgPnPbPfPaPeP?Q04P0P7MDB/0mX0@,3@X1>P^PTPcPxP9PyPJPzQ0QPvP{PuP|PtPgPnPbPfPaPAQ05P0P7MDBQ0SQ0@Q0CQ0AP0PYP]P2DR%[]PLP]PM%9]R^Q03%q]P]P]P]15^=1;\=[C<EpDK3=R^'0X0@,3@X1>P0O1Q01P@PxP9PyPJPzQ0QPvP{PuP|PtPgPnPbPfPaPAQ05P0P6MDB/0^X0@P`PxP9PyQ0OPzP~PvP{PuP|PtPgPnPbPf1?BXP0P5MC6Q0DQ0?%TXQ0>P0PXP\P2%[\PIP\PL%9\R]PM%q\P\P\P\15]=1;[=[C<EpGgDIX0@,3@P0Q0YP`PxP9Q0PQ0OQ0KP~PvP{PuP|PtPgPnPb1?BWQ0;P0P4MDBP;Q0ZPSQ05P0P`Q04F4Q0[%TWP;PSP0PWP[P2P[PDP[PI%9[R]PLP[P[P[P[15]=1;Z=[C<GDFrDIQ00PsQ0YP`PxQ0RQ0PQ0LQ0KP~PvP{PuP|PtPgPn1?BVPdP7P3MDBP;p+01ER]PHQ0<P7Q0YQ05P;11;]P]Q0YPiQ0<P7PVP;PHP7PVPZP2PZQ04PZPD%9ZR[PIPZPZPZPZ15[=1;Y=[C<GDGFG8GeP]Q0ZPsQ0YPyPJQ0MP}Q0LQ0KP~PvP{PuP|Pt1?BTRYP0P8MC6P;p+01GR[PRPdP0Q0ZQ0;F4P;11;[P[Q0ZPiPdP0PTP;PRP0PTPXP2PXQ0<PXQ05%9XRZQ04PXPXPXPX15Z=1;W=[C<GDGFG83=X0@,3@P0P]Q0ZPsQ0YPyPJQ0MP}Q0LQ0KP~PvP{PuP|PtPYPaP5P8MDBP;p+01HR5PQPeP4P]PdP;11;5P5P]PiPeP4PSP;PQP4PSPWP2PWQ0;PWQ0<%9WRYQ05PWPWPWPW15Y=1;V=[C<GDGFG8GeQ00P;p+01IRYPPPaP3p+01FRWPeF4P;11;YPYPWPiPaP3PHP;PPP3PHPVP2PVPdPVQ0;%9VRsQ0<PVPVPVPV15s=1;U=[C<GDGFG8PYP5P[PWQ0YP`Q0QPwQ0NQ0JQ0MP}Q0LQ0KP~Pv1?BRP0Q0FMC6P;p+01KR`POPbP0P5PfF4P;11;`P`P5PiPbP0PRP;POP0PRPTP2PTPaPTPe%9TRsPdPTPTPTPT15s=1;S=[C<GDGFG83=X0@,3@P0P;P`POPbP8P5PfF4P;p+01LR8,1;P8PYPiPnQ0GPQP;PEQ0GPQPSP2PSPfPSPa%9SRsPePSPSPSPS15s=1;H=[C<GDGFG8Q00P;P;p+01MRsPsp+01JRZPiPgPKGXPPP;PFPKPPPHP2PHPbPHPf%9HRXPaPHPHPHPH15X=Q07/;=[C<GDGFPsP8P`PZPWP]Q0RQ0PQ0OPzQ0QPwQ0NQ0JQ0MP}1?BOP0Q09MC6P;p+01OR}PNP|P0P8PtF4P;11;}R]P}P8PiP|P0POP;PNP0POPRP2PRPgPRPn%9RRNPbPRPRPRPR15N=1;Q=[C<GDGFG83=X0@,3@P0P;P]P}P8PiP|Q0FF]PEP;Q03Q0EPEPQP2PQPtPQPg%9QREPnPQPQPQPQ15E=1;P=[C<GDGFP@p+01PP}p+01NREPsPYP5P9PyPJQ0RQ0PQ0OPzQ0QPwQ0NQ06,?BP0Q08MC6P;p+01RRYPLPvP0P}P{F4P;11;YPYP}PiPvP0Q06P;PLP0Q06PGP2PGPuPGP|%9GRLPtPGPGPGPG15L=1;O=[C<GDGFG83=X0@PcP}PEPsP8P5P[PyPJQ0RQ0PQ0OPzQ0QPwQ0NQ0J1?BFRBPcP_MC6P;p+01QROPMP{PcPEPuF4RLP;P;POPOPEPiP{PcGXRiPFP;PMPcPFPPP2PPP|PPPt%9PR2PgPPPPPPPP152=1;G=[C<GDGFR='0R2'0P}PEPsP8P5P[PyPJQ0RQ0PQ0OPzQ0QPwQ0NQ0JPBP~PcP_PKNE08PLP2P3PiP=P7P0CSCSCSCfW@W;P7P0O2n2001000000121000000W;W:P7P0O2n2001000000121000000W:W5P7P0O2n2001000000121000000W5Xk@P7P0O2n2001000000121100000PxP9PyPJPzQ0QPvP{PuP|PtPgPnPbPfPaPAP0P6MC6/0^X0@,3@eWAX1>L09PoPlPKPqPrP3PhPpP7P0CSCSCSCSCfCfCfW?W9P7P0O2n2001000010121000000W9W8P7P0O2n2001000010121000000W8W7P7P0O2n2001000010121000000W7W5P7P0O2n2001000010121000000W5Xj:P7P0O2n2011000010121100000W5Xi1P7P0O2n2011000010121100000W5Xh<P7P0O2n2011000010121100000P;P6PePaPePdQ0;PDPIPGPPPQPRQ07PHPSPTPUPVQ0=P0P7MC6Q0H'0X0@,3@X1>P4Q0IE7X2:#>X31#CX4<,3<R<eP<eW<W6L06UUUUUUUUUXK1XN1Xg1XO1WPWLW=XeCXdCXcCXbCXUCXTCX]CX\CX[CXZCXYCXXCXWCXVCXJCXICXHCXGCXFCXECXDCXCCXSCXRCXaCX`CX_CXfCXMCX^CWQWBWlg01bMeW>o"). Qed.

(* [comment removed for export] *)
Definition pixCreateHeader_nn_res0_cpsF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 1 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateHeader m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v = 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)) c
       /\ rt_live RT Σ' = (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

Definition pixCreateHeader_nn_res0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 1 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateHeader m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v = 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)) c
       /\ rt_live RT Σ' = (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

Definition pixCreateNoInit_nn_res0_cpsF (entry msite : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  uctx m sp s0 ras -> In (msite :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)) c
       /\ rt_live RT Σ' = (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

Definition pixCreateNoInit_nn_res0_cps (entry msite : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  uctx m sp s0 ras -> In (msite :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)) c
       /\ rt_live RT Σ' = (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

Definition pixCreate_nn_res0_cpsF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d -> hdr_args_ok w h d ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreate m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix <> 0 /\ pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0 /\ p_xres v = 0 /\ p_yres v = 0 /\ (p_d v = 1 -> p_spp v = 1)) c
       /\ rt_live RT Σ' = (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

Definition pixCreateTemplateNoInit_nn_res0_cpsF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (v : pixv) (cv : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> pix_obj_rc (rt_live RT Σ) m pixs v cv rc -> 1 <= rc <= 2 ->
  res0 v ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 3 4 (RASTER_COST + 32) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateTemplateNoInit m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pixd <> 0 /\ pix_obj (rt_live RT Σ') m' pixd v' cv' /\ pm_hdr_copy v v' cv cv' /\ res0 v') c
       /\ rt_live RT Σ' = pm_copy_live pixd v' cv' (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (RASTER_COST + 32) <= rt_credit RT Σ').

Definition pixCreateTemplateNoInit_nn_res0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs v cv ->
  res0 v ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 3 4 (RASTER_COST + 32) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateTemplateNoInit m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pixd <> 0 /\ pix_obj (rt_live RT Σ') m' pixd v' cv' /\ pm_hdr_copy v v' cv cv' /\ res0 v') c
       /\ rt_live RT Σ' = pm_copy_live pixd v' cv' (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (RASTER_COST + 32) <= rt_credit RT Σ').

Definition pixCopy_nn_res0_cpsF : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs v cv -> p_data v <> 0 ->
  res0 v ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 4 (RASTER_COST + 64) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopy m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pixd <> 0 /\ pix_obj (rt_live RT Σ') m' pixd v' cv' /\ pm_hdr_copy v v' cv cv' /\ res0 v') c
       /\ rt_live RT Σ' = pm_copy_live pixd v' cv' (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ').

Definition pixCopy_nn_res0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> pix_obj (rt_live RT Σ) m pixs v cv -> p_data v <> 0 ->
  res0 v ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 4 (RASTER_COST + 64) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopy m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pixd <> 0 /\ pix_obj (rt_live RT Σ') m' pixd v' cv' /\ pm_hdr_copy v v' cv cv' /\ res0 v') c
       /\ rt_live RT Σ' = pm_copy_live pixd v' cv' (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ').

Lemma pixCreateHeader_nn_res0_cps_of_F : pixCreateHeader_nn_res0_cpsF -> pixCreateHeader_nn_res0_cps.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_iface ()) ["PoIface"] "p'0h02m'h12msh21vh33pixh43Σ'h52H9h61ch73H10h83H11h93H12h:3H14h;3H15h<3H16h=3H17h>3H18h?3H19h@3H20hA3H21hB3H22hC3H23hD3H24hE2HchF1FhG1HhH3H13hI3H25hJ3HmshK3PMchL2a0hM2a1hN2a2hO2a3hP2a4hQ2a5hR2a6hS2a7hT1dhU2fchV2gphW1hhX2lohY1mhZ2rah[2s0h\2s1h]3s10h^3s11h_2s2h`2s3ha2s4hb2s5hc2s6hd2s7he2s8hf2s9hg2sphh2t0hi2t1hj2t2hk2t3hl2t4hm2t5hn2t6ho2tphp1whq1xi001xhr2x0hs2x1ht2x2hu2Σp%0p&0p;1p;2p;3p;6p;5p;Sp;4p;Dp;Cp;7p;Ep;8g00>Xk10NTg00>3j1YTg00?Pj1pTg00?nj1wTg00@Qk109Tg00A6k20KTg00Abk10ITg00BDk10GTg00CBk10ETg00D>j2<Tg00:0j32k207Tg01R`k20<Tg01cTk30;Tg006gj1vTg00OHk10MTg00PCk60LTg00Q[k50JTg00lTmS08Tg00mQk40Hj5cTg00nJlDATg00Ddj21Tg010?k206Tg00MOk10FTg01SZk40DTg00Goj1eTg00Hij1_Tg005mj16Tg008AS00j20Tg0144S01j23Tg00bQk10:Tg015mj2=Tg00Vlj2FTg016kj2ZTg01TXlC9Tg00oCj77Tg01USj5ITg00Moj3rTg00XAj2JTg011?j7hTg01WNmE0?Tg01XNj4oTg01Xhk80>Tg01Yfk80=Tg00GVj1}Tg007Ek10CTg0137j1aTg0043j1fTg0050j1lTg01VQj1bTg010_k403Tg017ik201Tg009Uk402Tg00:JR0f0R1g00:hR232#}p=Mf5R3f4R4'1f3R5f2R6f1R7P1DIp=zA2071p=5&0C7=201p=4%a5=202%f6=202%l7=202/01'0'0p=8%b7=202/01p=]A2045A2067/01'0p=CA2067/01,05,04p=Df7R8f6R9P3P4P5P6P7Fh/01p=:P8P9P3P4P5P6P7F7/01p=[P0P0P7P1H03p=u1Z560017/J1p=g1F679205/01p=d1=679245/01p=XAr5679234/01p=GP3P4P5P6P7Dc/01p=>g00;FR:/31p=@1301p=B1071,06p=;1Z4500161Z71'Jp=K1F451F67520/01p=O1=56=247/01p=sP81193P4P5P6P7P1Fhp=WA2067/01p=N1071,06,05,04p=H1Z670011p=VA2934A2567/01'0p=T1193P4P5P6P7DI/01p=`1Z71,J6p=U1F56=207/01p=qP8P9P3P4P5DIA2067/01'0p>00A2072#}/01p=SP0P0P6P7H03=r51p=\A2345A2067/01'0p=nA2082#}1193P4P5P6P7DI/01'0p=E%e8=209%_3=204A2056%b7=202/01'0'0'0p=?%_3=204A2056%b7=202/01'0'0p=RP8P9P3P4P5DI%e6=207/01'0p=QAr6719245p=~1=67=251p={1F67=201p=|%e7=201p=y%_7=201p=kP3P4P5P6P7DI/01p>0B%l7=202/01p=^A2034%b5=202%a6=202%f7=202/01'0'0'0p>05%b1=202p=m%_6=207/01p>04%67=201p=L%a1=202p=t%f6=202%l7=202/01'0p=x%f1=202p=i%l1=202p=j%a7=202/01p>0A%a6=202%f7=202/01'0p>0@P9P3P4P5P6P7P1H02H02p=Pg01dUp,2RTR;$0NR<g01BWp-0[g00<CR=#YR>#Y#YR?#Y#YR@#YRA#pRB#wRC&09>#p00KC%p@#w%p?#w$0I\CR?fVR@$0GfWRD$0EfTS02g01EF,<B52CfORE00<3S03Q03Q03f8S04@0;89P;f^RFf;S05f[RGf:RH&09=#v$0MJ0LP;f_RI%v=R=P=%v>R>I0Jg01=<P;f`S06PIg01N3RJPFf]RKf\RLPGfZRMfYRNfXS07PDP@fUROQ02fSRPfRRQfQRRfPS08PEfNRSfMRTfLRUfKRVfJRWfIRXfHS09fGRYfFRZfER[fDR\fCR]fBR^fAS0:f@S0;f?S0<f>R_g01\0R`f=S0=NS08+07H0HRaPag01PBS0>P;P6fcRafdRbPafbRcfaRdPKPLPPPQPRQ08PEPSPTPUPVPW1<B5S0?P[P1P7MDAP;ffReP4P]P1PaP^P;11;eRfPePa20600Rg$0FRhP]P1%M5S0@P;P4P1P5P6P2P2P2P2H0DR2EzS0A%e6RiQ0:%_6S0BQ0;%66RjQ0<P6P6P615j=145=[C8,]6RkDCDDG:G[Rl'0X0?,3?X1JP5&0:gRm11;6S0CPg%vAS0D,u7S0E11;bg01Q7-060$0:RA1=;6S0FP;Pb1F;6S0GP;PbP;PbP>1Z;6S0HCgCdDXEGRnE>X2:#@X30#BX4<,3<W6Q0>P;P6PaPbPaPcPdPKPLPPPQPRQ08PEPSPTPUPVPWQ0?P1P7MC9/0lX0?,3?X1JP5PnE>X2:#@X30#BX4<,3<W6PdQ06PIPFPKPLPGPMPNQ07PDP@POQ02PPPQPRQ08PEPSPTPUPVPWPXQ09PYPZP[P\P]P^Q0:Q0;Q0<P_Q0=f<S0IQ05PHf9RnQ04P8P9P3P4P5P6P7P1OaQ0>P;PdQ06PIPFPKPLPGPMPNQ07PDP@POQ02PPPQPRQ08PEPSPTPUPVPWPXQ09PYPZP[P\P]P^Q0:Q0;Q0<P`P_NS08-07JP1DcP1WEW6Q0>Q0>P;P6PbfeR_PbPaPcPFPKQ02PPPQPRQ08PEPSPTPUPVQ0?PZP1P7MDAP;fgR`P4P\P1PbP]P;11;`RlP`PbPhP\P1Q0@Q0APiP^Q0BQ0:PjQ0;PkDCDDG:G[S0J'0X0?,3?X1JRoP5PmQ0CPgQ0E11;_S0KPAQ0FP;P_Q0GP;P_P;P_P>Q0HCgCdDXEGS0LE>X2:#@X30#BX4<,3<W6P1O1Q01P<P;P6PbPoP4Q0LE>X2:#@X30#BX4<P;P6P_PeP_PbPaPIPFPOQ02PPPQPRQ08PEPSPTPUQ0?P1P7MC9P;fhRoP4P[P1P_P\F7P;11;oRpPoP_PhP[P1Q0@Q0APiP]Q0BP^PjQ0:PkDCDDG:3;X0?,3?X1JP3PmQ0CPgQ0EPfPAQ0FP;PeQ0GP;PeP;PeP>Q0HCgCdDXEGE>X2:#@X30#BX4<,3<P1P;P6PeP`PeP_PbQ06PIP@POQ02PPPQPRQ08PEPSPTQ0?Q09P1P7MDAP;fiRfP4PZP1PeP[F7P;11;fS0MPfPePhPZP1Q0@Q0APiP\Q0BP]PjP^PkDCDDG:3;X0?,3?X1JP9PmQ0CPgQ0EPlPAQ0FP;P`Q0GP;P`P;P`P>Q0HCgCdDXEGE>X2:#@X30#BQ01P0P;P5P`PoP`PeP_PdQ06PDP@POQ02PPPQPRQ08PEPSQ0?PXP1P7MDAP;fjRlP3PYP1P`PZF7P;11;lR^PlP`PhPYP1Q0@11;3RqP1P5P6P2DIPiP[Q0BP\PjP]PkDCDDG:3;X0?,3?X1JP8Pm11;5PgQ0EPpPAP;P51=;oP;P5P;PoP;PoP>P;P5DKDODsEGE>X2:#@X30P;P6PfPlPfPoP`PaPcPNQ07PDP@POQ02PPPQPRQ08Q0?P1P7MC9P;flRpP4PXP1PfQ09F7P;P;PpPpPfPhPXP1GWRrQ0@Q0APiPYQ0BPZANj[kDCRs'0DHX0?,3?X1JPnPmQ0CQ0E=rg^R^PAQ0F1=;lRtQ0G1F;lRuAV;l>RvQ0H'J3NFTE>X2:#@X30#BX4<,3<P1P;P3PfPlPfPoP`PaPcPNQ07PDP@POQ02PPPQPRQ08Q0?PVP1P7MDAP;PpP8PXP1PfQ09F7PrQ0@P;P8P1P5P6P2PsF`DHX0?,3?X1JPnPmPqP^PA1=;3PtP;P3PuAUv;3CqFTE>X2:#@Q01P:P;P9PlfkRvPlPfPoPbPaPMPNQ07PDP@POQ02PPPQPR1<B4PUP1P7MDAP;fmRuQ04PWP1PlPXF7P;11;uS0NPuPlPhPWP1Q04,1;RtP1P4P6P2PiQ09Q0BPYPjPZPkDCL00,S4G:3;X0?,3?X1JPHPm11;9PgP6Q0D11;vC\PA1=;91=;vP;P9P;PvP;PvP>P;P9DKDOFTE>X2:P;P6PufnR^PuPpPvP`PePKPLPGPMPNQ07PDP@POQ02Q0?P1P7MC9P;fpS0OP4PTP1PuPUF7P;P;Q0OQ0OPuPhPTP1GWRqQ0@Q0A15iVQ0BPWANjXkDDDHX0?,3?X1JQ0=PmQ0CPgQ0E11;^RsPAQ0F1=;^RrQ0G1F;^RwAV;^>RxQ0H'JEnEGE>X2:#@X30#BX4<,3<P1P;Q04PpPuPpPvPlPeP_PLPGPMPNQ07PDP@POQ02PP1<B9PSP1P7MDAP;foRyPHPUP1PpPVF7P;11;yPyPpPhPUP1P9P;PHP1P9P6P2PiPWQ0BPXQ09=NjkDCGEG:3;X0?,3?X1JQ0IPmPtPgP4Q0DQ0NC\PAQ04,=;1=;uP;Q04P;PuP;PuP>P;Q04DKDOFTE>Q00P;PnPuP^PuPpPvP`PePKPLPGPMPNQ07PDP@POQ021<B8PEP1P7MDAP;Q0OQ05PTP1PuPUF7Pq%M8P;Q05P1P8P5P2P5PVP5PW%65RqPXP5P5P5P515q=144=[C8G?F`DHX0?,3?X1JQ0=DcPm11;nPgP3Q0DPsC\PA1=;nPrP;PnPwAUx;nCqFTP;P6fqRxfrRwPxQ0OPyPvPlPdQ06PIPFPKPLPGPMPNQ07Q0?P1P7MC9P;ftS0PP4PRP1PxQ08F7P;Q0P,1;RrQ0PPxPhPRP1Q0@Q0APiPEQ0BPSPjPTPkDCDDG:3;X0?,3?X1JQ0:PmQ0CPgQ0E11;wRsPAQ0F1=;wRqQ0G1F;wRtAV;w>RHQ0H'JEnEGE>X2:#@X30#BX4<,3<P1P;Q05PyQ0OPyP^PuPfPoPIPFPKPLPGPMPNQ07PDP@1<BnPRP1P7MDAP;PwQ0=PEP1PyPSF7P;PsPwPyPhPEP1Q0=,1;RzP1PnP3P2P3PTP3PU%63R{PVP3P3P3P315{=149=[C8ERGQ,SnG:3;X0?,3?X1JQ0<DcPmQ0I,1;PgQ04Q0D11;xS0QC\PAQ0I,=;1=;xP;Q0IP;PxP;PxP>P;Q0IDKDOFTQ00PmPzPgQ0D,unPsD~PAP;Q0=PqP;Q0=PtQ0=9UH;CqDsP;P6fuRHfvRtPHQ0PfsS0RPyP^P_PbPaPcPdQ06PIPFPKPLQ0?P1P7MC9P;fxRqP4POP1PHQ02F7P;11;qPqPHPhPOP1Q0@Q0APiPPQ0BPQPjPRPkDCDDG:3;X0?,3?X1JP[PmQ0CPgQ0E11;tPAQ0F1=;tRsQ0G1F;tRzAV;t>R9Q0H'JEnEGE>X2:#@X30#BX4<,3<P1PmQ0<,1;PgQ05Q0D'uPrD~PAP;Q0;1=;HP;Q0;P;PHP;PHP>P;Q0;DKDODsQ00PAP;Q0:PsC{P;Q0:PzQ0:9U9;CqP;P6fyR9fzS0SP9PqfwRzQ0RPwPfPoP`PeP_PbPaPcPdQ06Q0?P1P7MC9P;f|RsP4PNP1P9Q07F7P;11;sPsP9PhPNP1Q0@Q0APiPDQ0BP@PjPOPkDCDDG:3;X0?,3?X1JPXPmQ0CPgQ0EQ0S,1;PAQ0FP;Q0SQ0GQ0S,F;RrQ0S=V;>R{Q0H'J3NDXEGE>X2:#@X30#BX4<,3<P1PAP;P]1=;qC{P;P\P;P9P;P9P>P;P\DKDOQ00A|;[rAU{;[P;P6f}R{f~RrP{Psf{S0TPzPtPuPpPvPlPfPoP`PeP_PbQ0?P1P7MC9P;p+01AR|P4PKP1P{PLF7P;11;|S0UP|P{PhPKP1FhS0VQ0@Q0A15iGQ0BPMANjNkDDDHX0?,3?X1JPTPmQ0CPgQ0E11;rS0WPAQ0F1=;rS0XQ0G1F;rS0YAV;r>S0ZQ0H'JEnEGE>X2:#@X30#BX4<,3<P11F;s9|;YP;P{P>P;Q09DKP<P;P6P|p+01BR}P|p+01@R~PrQ0SP9Q0OPyP^PuPpPvPlPfPoP`Q0?P1P7MC9P;p+01DS0[P4Q06P1P|PIF7P;P;Q0[Q0[P|PhQ06P1GWS0\Q0@Q0A15iFQ0BPKANjLkDDDHX0?,3?X1JQ08PmQ0CPgQ0E11;}S0CPAQ0FP;P}Q0GP;P}P;P}P>Q0HCgCdDXEGE>X2:#@X30#BX4<PXP0P;PVP~P|P~PrP{P9PqPyP^PuPpPvPlPfPoP`PeQ0?P1P7MC9P;p+01CS0HPTPIP1P~PFF7S0GP;P;Q0HQ0HP~PhPIP1GWS0FQ0@11;TS0@P1P5P6P2PiPKQ0BPLPjPGPkDCL00DHX0?,3?X1JPEPm11;VS0APgQ0EQ0UPAP;PV1=;|P;PVP;P|P;P|P>P;PVDKDODsEGE>X2:#@X30P[P:P;PWPrP~PrP{PsPqPzP^PuPpPvPlPfPoP`PeP_Q09,<BS0EP1P7MC9P;P}PUPFP1PrPKF7S0]P;Q0CP}PrPhPFP1FhS0CQ09#MS0^11;US0_P1Q09P6P2PiPLQ0BPGPjPMPkDCL00DHX0?,3?X1JPSPm11;WPgPZQ0D11;~S0BC\PA1=;W1=;~P;PWP;P~P;P~P>P;PWDKDOFTE>X2:Q0:P;PXP{PrP{PsQ0TPzPtPuPpPvPlPfPoP`PeP_Pb1<BYR>P1P7MC9P;P|PVPKP1P{PLQ0V%MYQ0AP1PYP]P2P]PGP]PM%6]RkPNP]P]P]P]15k=14\=[C8ERGQ3;G[Rk'0X0?,3?X1JRjPTDcPm11;XPgQ0D,u[Q0WD~S0WPAP;PXQ0XC{S0XQ0Y9|;XS0YQ0Z?U;XS0Z'0S0D'0S0V'0P;PXP{PrP{PsQ0TPzPtPuPpPvPlPfPoP`PeP_PbP>PIP1P7MDA/0kX0?,3?X1JPjPTQ0=P~PrP{PsPqPzP^PuPpPvPlPfPoP`PeP_Q0EQ06P1P7MDAQ0]Q0CQ0^Q0_P1Q09P\P2DIP\PLP\PG%6\RjPMP\P\P\P\15j=14[=[C8G?DHS0_'0X0?,3?X1JP1O1Q01P?P~PrP{PsPqPzP^PuPpPvPlPfPoP`PeP_Q0EQ06P1P6MDAQ0_'0X0?P|P~PrP{P9PqPyP^PuPpPvPlPfPoP`Pe1<BXP1P5MC9Q0GQ0F%MXQ0@P1PXP[P2P[PKP[PL%6[RjPGP[P[P[P[15j=14Z=[C8ERGQDHX0?,3?P1P}P|P~PrQ0SP9Q0OPyP^PuPpPvPlPfPoP`1<BWPcP1P4MDAP;Q0[PSQ06P1P|PIF7Q0\%MWP;PSP1PWPZP2PZPFPZPK%6ZRjPLPZPZPZPZ15j=14Y=[C8G?F`DHQ00Q0HP}P|P~Q0TQ0SPxQ0OPyP^PuPpPvPlPfPo1<BVPaP7P3MDAP;p+01ERjPEPdP7P}Q06P;11;jPjP}PhPdP7PVP;PEP7PVPYP2PYPIPYPF%6YRZPKPYPYPYPY15Z=Q09/4=[C8G?GEG:G[PjQ0[Q0HP}P{PsQ0RPwPxQ0OPyP^PuPpPvPl1<BTRZP1P8MC9P;p+01GR\PRPaP1Q0[PcF7P;11;\P\Q0[PhPaP1PTP;PRP1PTPXP2PXPdPXQ06%6XRkPIPXPXPXPX15k=14W=[C8G?GEG:3;X0?,3?P1PjQ0[Q0HP}P{PsQ0RPwPxQ0OPyP^PuPpPvPlPZP_P5P8MDAP;p+01HR5PQPbP4PjPaP;11;5P5PjPhPbP4PSP;PQP4PSPWP2PWPcPWPd%6WRZQ06PWPWPWPW15Z=14V=[C8G?GEG:G[Q00P;p+01IRZPPP_P3p+01FS09PbF7P;11;ZPZQ09PhP_P3PEP;PPP3PEPVP2PVPaPVPc%6VRWPdPVPVPVPV15W=14U=[C8G?GEG:PZP5P\Q09P}P|PzPtPHQ0PQ0RPwPxQ0OPyP^1<BRP1Q05MC9P;p+01KRWPOP`P1P5PeF7P;11;WPWP5PhP`P1PRP;POP1PRPTP2PTP_PTPb%6TRkPaPTPTPTPT15k=14S=[C8G?GEG:3;X0?,3?P1P;PWPOP`P8P5PeF7P;p+01LR8,1;P8PZPhPoQ04PQP;P@Q04PQPSP2PSPePSP_%6SRkPbPSPSPSPS15k=14E=[C8G?GEG:Q00P;P;p+01MS04Q04p+01JS0\PhPfPnGWPPP;PDPnPPPEP2PEP`PEPe%6ERkP_PEPEPEPE15k=Q08/4=[C8G?GEQ04P8PWQ0\Q09PjQ0TQ0SP9PqPzPtPHQ0PQ0RPw1<BOP1Q0<MC9P;p+01ORkPNPvP1P8PlF7P;11;kR>PkP8PhPvP1POP;PNP1POPRP2PRPfPRPo%6RRAP`PRPRPRPR15A=14Q=[C8G?GEG:3;X0?,3?P1P;P>PkP8PhPvQ05FhP@P;PMQ0IP@PQP2PQPlPQPf%6QR>PoPQPQPQPQ15>=14P=[C8G?GEQ00%MDP;PGQ0=PDPPP2PPPvPPPl%6PR>PfPPPPPPPP15>=Q02/4=[C8G?F`p+01QS0Ip+01PR>Pkp+01NS05Q0\PZP~PrP{PsQ0TQ0SP9PqPzPt1<BNP1P]MC9P;p+01SRAPKPyP1P>P^F7P;11;APAP>PhPyP1%MNS0<P;PKP1PNPOP2Ez%eOPuPOPp%6ORgPvPOPOPOPO15g=14@=[C8ERDDG:3;X0?,3?P1Q0<P;PFQ0;PMP@P2P@P^P@Pu%6@RgPpP@P@P@P@15g=14D=[C8G?F`Q00P;PIQ0:PGPDP2EzPDPyPDP^%6DRgPuPDPDPDPD15g=Q07/4=[C8G?p+01US07p+01TRgPAp+01RR@Q05Q04Q0[Q0HP}P|P~PrP{PsQ0TQ0S1<BKP1PYMC9P;p+01WRYPdQ0RP1PgPwF7P;11;YPYPgPhQ0RP111;dRmP1PKPNP2PNPxPNQ0O%6NRiPyPNPNPNPN15i=14M=[C8ERGQ,SKG:3;X0?,3?P1PmP]PKPNP2DIPMPwPMPx%6MR]Q0OPMPMPMPM15]=14G=[C8G?Q00Q0R,yGPGPw%6GR]PxPGPGPGPG15]=14L=[C8ERp+01YS0;p+01XS0@PYp+01VS0FP@Q0IP5P\Q09PjQ0[Q0HP}P|P~Pr1<BdP1PVMC9P;p+01[RLP_PzP1Q0@PtF7P;11;LPLQ0@PhPzP1Q0KP1PdPKP21yKHS0KQ0P,kK%6KR]Q0RPKPKPK15]=14F=[C8,]KDDJ0B,SdG:3;X0?,3?P1Q0KPFPH%6FR]Q0PPFPFPFPF15]=14I=[C8ERQ001kIt%6IR]PHPIPIPI15]=Q06/4=[,^IJ05p+01]S06p+01\R]PLp+01ZRMQ0FQ07P8PWQ0\PZP5P\Q09PjQ0[Q0H1<B_P1PEMC9P;p+01_RmPfQ0TP1P]Q0SF7P;11;mPmP]PhQ0TP1Q0MP1P_PdP2PdP91kdqS0M%6dRi/5zPdPdPd15i=14c=[C8,]d3;GQ,S_G:3;X0?,3?P1Q0M%6cRiPqPcPcPc15i=14a=[,^cJ05Q00%6aRi/59PaPaPa15i=14b=[C8,]ap+01aS0Sp+01`RiPmp+01^S0GPMQ0;P>PkQ05Q04P8PWQ0\PZP5P\1<BfP1PPMC9P;p+01cS01PuP~P1PiPrF7P;Q01,1;Q01PiPhP~P1Q0NP1PfP_P2P_P{%6_S0NQ0T'5S0^%m_P_P_P_Q0N/5=14e=[C83;:04_sGQ,SfG:3;X0?,3?P1Q0^PePePe1Le=14`=[C8,]eQ00%m`P`P`P`1L`=14o=[C8p+01eS0Np+01dS0CQ01p+01bS0]Q0GQ06PgPAP@Q0IP>PkQ05Q04P8PW1<BuP1PDMC9P;p+01gRDPxQ0[P1Q0CQ0HF7P;11;DPDQ0CPhQ0[P1Q0QP1PuPfP2PfP}%6fR}%mfS0Q%tf15}=14l=[9xff3;7N~:04f|GQ,SuG:3;X0?,3?P1Q0QPlPlPl1Ll=14v=[C8Q00%tv1Lv=14p=[9xvvp+01iS0Cp+01hR}PDp+01fRDQ0]Q0SQ0@PYQ0FQ07PgPAP@Q0IP>Pk1<BxP1PGMC9P;p+01kRGPHP5P1P}P\F7P;11;GPGP}PhP5P1PxP;PHP1PxPuP2PuQ09PuPj%6uRjQ0[Pu%tuR}%iu15j=14^=[,^u3;G?GEG:3;X0?,3?P11L^=14y=[9x^^Q00%iy1Ly=Q0O/4=[,^yp+01mRyp+01lRjPGp+01jR\PDQ0NP]PLPMQ0;Q0@PYQ0FQ07PgPA1<BHP1PIMC9P;p+01oRIP9P8P1PjPWF7P;11;IPIPjPhP8P1PHP;P9P1PHPxP2PxQ0\PxPZ%6xRZP5Px%ixR5%jx15Z=14w=[3;-0AxG?GEG:3;X0?,3?P11Lw=Q0R/4=[,^wQ00Q0R#jQ0R/L=Q0P/4=[p+021Rwp+020RxPIp+01nP\Q0CPiPmQ0GQ06P]PLPMQ0;Q0@PY1<B9P1PaMC9P;p+023RYP{P>P1PxPkF7P;11;YPYPxPhP>P1P9P;P{P1P9PHP2PHQ05PHQ04%6HR\P8PH%jHR815\=14t=['0:0@HHG?GEG:3;X0?,3?P11Lt=14z=[P?p+024PYp+022RtPwPyPjQ01Q0]Q0SPiPmQ0GQ06P]PLPM1<BsP1PeMC9P;p+026RyP|PAP1PYP@F7P;11;yPyPYPhPAP1Q0UP1PsPqP2PqQ0IPqP>%6qRAPkPqPqPqPq15A=149=[C8ERGQ,SsG:3;X0?PdPYPtPwPxPjPGQ0]Q0SPiPmQ0GQ06P]PLPMQ0;Q0T,<BS0UPdP_MC9P;p+025RBP~P@PdPtQ0IF7S0IP;P;PBPBPtPhP@PdGWS01Q0T#MS04Q0BPdQ0TPzP2DIS0T1yz>S0B1kzkRk%6zR>Q05'5R2%mzR@%tzRh%izRB%jzR915>=14q=[R='0R>'0RA'0Ry'0R|'0RH'0R\'0RI'0RZ'0RW'0RD'0PYPtPwPxPjPGQ0]Q0SPiPmQ0GQ06P]PLPMQ0;Q0UPgPdP_PKNE0?Q0IPDPNQ01PWPOQ04PZPRQ0TPIPTQ0BP\PXPkPHP[P2P|Q0:P@PyQ0=PhPAPnPBP>P3P9P=P7P1FPFPFPFPFPFPCoWIXD8P7P1O2n2001000000121000000WDXC5P7P1O2n2001000000121000000WCXB}P7P1O2n2001000000121000000WBWAP7P1O2n2001000000121000000WAW@P7P1O2n2001000000121000000W@W?P7P1O2n2001000000121000000W?W>P7P1O2n2001000000121000000W>W=P7P1O2n2001000000121000000W=W<P7P1O2n2001000000121000000W<W;P7P1O2n2001000000121000000W;W:P7P1O2n2001000000121000000W:W5P7P1O2n2001000000121000000W5Xt?P7P1O2n2001000000121100000P~PrP{PsPqPzP^PuPpPvPlPfPoP`PeP_Q0EP1P6MC9Q0_'0X0?,3?eWJX1JL0>Q0WQ0VPnQ0XQ0DP3Q0YQ0ZP7P1FPFPCoCoCoWHW9P7P1O2n2001000010121000000W9W8P7P1O2n2001000010121000000W8W7P7P1O2n2001000010121000000W7W5P7P1O2n2001000010121000000W5Xs:P7P1O2n2011000010121100000W5Xr0P7P1O2n2011000010121100000W5Xq<P7P1O2n2011000010121100000P;P6PbP_PbPaPcPFPKQ02PPPQPRQ08PEPSPTPUPVQ0?P1P7MC9Q0J'0X0?,3?X1JP4Q0LE>X2:#@X30#BX4<,3<R<eP<eWEW6L0=UUUUUUUUUXT0XW0Xp0XX0WYWUWFXnCXmCXlCXkCX^CX]CXfCXeCXdCXcCXbCXaCX`CX_CXSCXRCXQCXPCXOCXNCXMCXLCX\CX[CXjCXiCXhCXoCXVCXgCWZWKWug01efeWGo"). Qed.
Lemma pixCreateNoInit_nn_res0_cps_of_F : forall entry msite, pixCreateNoInit_nn_res0_cpsF entry msite -> pixCreateNoInit_nn_res0_cps entry msite.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_iface ()) ["PoIface"] "p'0h02m'h12msh21vh33pixh43Σ'h53H12h61ch73H13h83H14h93H15h:3H17h;3H18h<3H19h=3H20h>3H21h?3H22h@3H23hA3H24hB3H25hC3H26hD3H27hE2HchF1FhG1HhH3H16hI3H28hJ3HmshK3PMchL2a0hM2a1hN2a2hO2a3hP2a4hQ2a5hR2a6hS2a7hT1dhU5entryhV2fchW2gphX1hhY2lohZ1mh[5msiteh\2rah]3rash^2s0h_2s1h`3s10ha3s11hb2s2hc2s3hd2s4he2s5hf2s6hg2s7hh2s8hi2s9hj2sphk2t0hl2t1hm2t2hn2t3ho2t4hp2t5hq2t6hr2tphs1wht1xi001xhu2x0hv2x1hw2x2hx2Σp%0p&0p;2p;1p;3p;4p;6p;5p;Sp;Dp;Cp;7p;Ep;8g01g6k20YTg00>Xk10XTg00>3j1LTg00?Pj1yTg00?nk101Tg00@Qk10;Tg00A6k20QTg00Abk10NTg00bQj1}Tg00BDk10DTg00CBk10BTg00D>j2<Tg00:0j32k208Tg01R`k20WTg01cTk30VTg01hGk40UTg00VBk20TTg01iBk30STg006gj1ZTg00OHk10RTg00PCk60PTg00Q>k20:Tg00Q[k50OTg00Ddj21Tg00RVk10MTg00XAj2KTg00lTmS09Tg00mQk40Cj5gTg00nJlDATg010?k205Tg00MOk10ATg01SZk40?Tg00Goj1iTg00Hij1dTg005mj16Tg008AS00j20Tg0144S01j23Tg01VQj1DTg01^Ej1eTg015mj2=Tg00Vlj2GTg016kj2bTg01TXlC9Tg00oCj77Tg01USj5TTg011?j7lTg01WNmE0@Tg01XNj4xTg01Xhk80JTg01Yfk80KTg01iYk20LTg00Moj3_Tg00GVj1PTg007Ek10>Tg0137j1aTg0043j1[Tg0050j1oTg010_k404Tg017ik203Tg009Uk40=Tf0R0#L#Lp>0Ef4R1f3R2f2R3f1R4;_03_p>0<%L0#L#L#Lp=kg00:JR5g00:hR6720#Pp=Hf5R7/11P2P3P4P0DTp=pA2540p=5&0>4=250p=4%a2=256%[3=256%o4=256/00'0'0p=8%D4=256#P/00p=nA2512A2534/00'0p=FA2534/00,02,01p=If7R8f6R9P7P1P2P3P4Fl/00p=;P8P9P7P1P2P3P4F7/00p=mP5P5P4P0H04p=V1b230034/K0p=j1G349252/00p=h1=349212/00p=cA_2349_719289/00p=BP7P1P2P3P4Dg/00p=>g00;FR:/30p=@1350p=C1040,03p=:1b1200331b40'Kp=O1G121G34525/00p=S1=23=214/00p=YP81197P1P2P3P4P0Flp=`A2534/00p=W1040,03,02,01p=J1b340030p=^A2971A2234/00'0p=v1197P1P2P3P4DT/00p=f1b40,K3p=\1G23=254/00p=uP8P9P7P1P2DTA2534/00'0p=~A2546#P/00p=UA2712A2534/00'0p=tA2586#P1197P1P2P3P4DT/00'0p=E%i8=259%d7=251A2523%D4=256#P/00'0'0'0p=?P5P5P3P4H04=_20p=XA2506p>0I%o4=256/00p=]%d8=259A2571%P2%a3=256%[4=256/00'0'0'0'0p>0HP8P9P7P1P2DT%i3=254/00'0p=NA_3409212p=|1=34=220p>021G34=250p>00%d7=251A2523%D4=256#P/00'0'0p=Q%i4=250p={%d4=250p=qA2571%D2=256#P%a3=256%[4=256/00'0'0'0p>07%d3=254/00p>06%64=250p=M%a0=256p=r%[3=256%o4=256/00'0p=z%[0=256p=w%o0=256p=s%a4=256/00p>0F%a3=256%[4=256/00'0p>0GP9P7P1P2P3P4P0H0=H0=p=R20Y40p,2RTR;$0XR<g01BWp-0[g00<CR=#LR>#LR?#LR@$0ERA#LRB#yRC$01RD&0;>#y00QD%yA$01%y@$01$0N\DRA%}5REfWRF$0DfXS02$0BfURGg01EF,<C52DfPS0300W9S04Q04Q04f9RHf8S05<0V8f<S06f\S07fVRIP8H0UP5fbRJP5f^RK-0TCQ05I0<g01ji60SEP;faREf>RLPKf=S08%Z?$0RJ0PP;PJ&0;=#Z%Z>g01`I%Z@+0:R@I0OfcR>,1;$0M%kB#k#k#k#k#Z+0:g01Gm'Kg01=<P;fdS09P>g01N3R?PJPEf`RMf_RNPKf]ROQ07f[RPfZRQfYRRQ02PFPIPGfTS0:fSRSfRRTfQRUQ03fORVfNRWfMRXfLS0;fKRYfJRZfIR[fHS0<fGR\fFR]fER^fDS0=fCS0>fBR_fgR`fAS0?NS09+08H0CRaPag01PBS0@P;P3P`fhRaP`ffRbfeRcPEPMPFPIPGQ0:PSPTPUQ03PVPW1<C2S0AP[P0P4MDAP;fjRdP1P\P0P`P]P;11;dRePdP`20555Rf$0ARgP\P0%H2S0BP;P1P0P2P3P6P6P6P6H0?R6EpS0C%i3RhP^%d3S0DQ0=%63RiQ0>P3P3P3%Z=R=,5i142=[C8,n3RjDFDIG;GmRk'0X0A,3AX1?P2%}fRl11;3S0EPf%D0%e0'VS0FPf%ZBS0G,V4S0H11;ag01Q7-055#}RB1=;3S0IP;Pa1G;3S0JP;PaP;PaP@1b;3S0KCjChDcGBRmE>X2:#@X35#CX4<,3<W6Q0@P;P3P`PaP`PbPcPEPMPFPIPGQ0:PSPTPUQ03PVPWQ0AP0P4MC9/0kX0A,3AX1?P2PmE>X2:#@X35#CX4<,3<W6PcQ09P>PJPEPMPNPKPOQ07PPPQPRQ02PFPIPGQ0:PSPTPUQ03PVPWPXQ0;PYPZP[Q0<P\P]P^Q0=Q0>P_Q0?f@S0Lf?S0MPLQ08Q06f;S0Nf:RLPHQ05P8P9P7P1P2P3P4P0OeQ0@P;PcQ09P>PJPEPMPNPKPOQ07PPPQPRQ02PFPIPGQ0:PSPTPUQ03PVPWPXQ0;PYPZP[Q0<P\P]P^Q0=Q0>PaP_NS09-08?P0DgP0WEW6Q0@Q0@P;P3PafiR_PaP`PbPJPEQ02PFPIPGQ0:PSPTPUQ03PVQ0APZP0P4MDAP;fkRmP1Q0<P0PaP\P;11;mRkPmPaPgQ0<P0Q0BQ0CPhP]Q0DP^PiQ0=PjDFDIG;GmS0O'0X0A,3AX1?RnP2PlQ0EPfQ0FPfQ0H11;_S0PPBQ0IP;P_Q0JP;P_P;P_P@Q0KCjChDcGBS0QE>X2:#@X35#CX4<,3<W6P0O1Q01P<P;P3PaPnP1Q0QE>X2:#@X35#CX4<P;P3P_PdP_PaP`P>PJPRQ02PFPIPGQ0:PSPTPUQ03Q0AP0P4MC9P;flRnP1P[P0P_Q0<F7P;11;nRoPnP_PgP[P0Q0BQ0CPhP\Q0DP]PiP^PjDFDIG;3:X0A,3AX1?P7PlQ0EPfQ0FPfQ0HPePBQ0IP;PdQ0JP;PdP;PdP@Q0KCjChDcGBE>X2:#@X35#CX4<,3<P0P;P3PdPmPdP_PaQ09P>PQPRQ02PFPIPGQ0:PSPTPUQ0AQ0;P0P4MDAP;fmReP1PZP0PdP[F7P;11;eS0RPePdPgPZP0Q0BQ0CPhQ0<Q0DP\PiP]PjDFDIG;3:X0A,3AX1?P9PlQ0EPfQ0FPfQ0HPkPBQ0IP;PmQ0JP;PmP;PmP@Q0KCjChDcGBE>X2:#@X35#CQ01P5P;P2PmPnPmPdP_PcQ09PPPQPRQ02PFPIPGQ0:PSPTQ0APXP0P4MDAP;fnRkP7PYP0PmPZF7P;11;kRpPkPmPgPYP0Q0B11;7RqP0P2P3P6DTPhP[Q0DQ0<PiP\PjDFDIG;3:X0A,3AX1?P8Pl11;2PfQ0FPfQ0HPoPBP;P21=;nP;P2P;PnP;PnP@P;P2DODSDYGBE>X2:#@X35P;P3PePkPePnPmP`PbPOQ07PPPQPRQ02PFPIPGQ0:Q0AP0P4MC9P;fpRoP1PXP0PeQ0;F7P;P;PoPoPePgPXP0G`RrQ0BQ0CPhPYQ0DPZAWi[jDFRs'0DJX0A,3AX1?PHPlQ0EPfQ0FPfQ0HPpI0<RpPBQ0I1=;kRtQ0J1G;kRuA^;k@RvQ0K'K3WFvE>X2:#@X35#CX4<,3<P0P;P7PePkPePnPmP`PbPOQ07PPPQPRQ02PFPIPGQ0:Q0APVP0P4MDAP;PoP8PXP0PeQ0;F7PrQ0BP;P8P0P2P3P6PsFfDJX0A,3AX1?PHPlPqPpPB1=;7PtP;P7PuA\v;7CuFvE>X2:#@Q01P:P;P9PkfoRvPkPePnPaP`PKPOQ07PPPQPRQ02PFPIPG1<C1Q03P0P4MDAP;fqRuQ05PWP0PkPXF7P;11;uS0SPuPkPgPWP0Q05,1;RtP0P1P3P6PhQ0;Q0DPYPiPZPjDFG~,U1G;3:X0A,3AX1?PLPl11;9PfQ0FPfQ0G,V311;vPBP;P91=;vP;P9P;PvP;PvP@P;P9DODSDYGBE>X2:P;P3PufrRpPuPoPvPmPdPEPMPNPKPOQ07PPPQPRQ02Q0AP0P4MC9P;ftS0TP1PUP0PuQ03F7P;P;Q0TQ0TPuPgPUP0G`RqQ0BQ0C15hVQ0DPWAWiXjDIDJX0A,3AX1?Q08PlQ0EPfQ0FPfQ0H11;pRsPBQ0I1=;pRrQ0J1G;pRwA^;p@RxQ0K'KEtGBE>X2:#@X35#CX4<,3<P0P;Q05PoPuPoPvPkPdP_PMPNPKPOQ07PPPQPRQ02PF1<C9PTP0P4MDAP;fsRyPLQ03P0PoPVF7P;11;yPyPoPgQ03P0P9P;PLP0P9P3P6PhPWQ0DPXQ0;=WijDFGEG;3:X0A,3AX1?Q06PlPtPfQ0FPfQ0G,V1Q0SPBP;Q051=;uP;Q05P;PuP;PuP@P;Q05DODSDYGBE>Q00P;PHPuPpPuPoPvPmPdPEPMPNPKPOQ07PPPQPRQ021<C8PSP0P4MDAP;Q0TQ0NPUP0PuQ03F7Pq%H8P;Q0NP0P8P2P6P2PVP2PW%62RqPXP2P2P2P215q=141=[C8G?FfDJX0A,3AX1?Q08DgPl11;HPf%D4%e4PfP7Q0GPsCXCXPB1=;HPrP;PHPwA\x;HCuFvP;P3fuRxfvRwPxQ0TPyPvPkPcQ09P>PJPEPMPNPKPOQ07Q0AP0P4MC9P;fxRrP1PGP0PxQ0:F7P;11;rRsPrPxPgPGP0Q0BQ0CPhPSQ0DPTPiPUPjDFDIG;3:X0A,3AX1?Q0?PlQ0EPfQ0FPfQ0H11;wRqPBQ0I1=;wRtQ0J1G;wRLA^;w@RzQ0K'KEtGBE>X2:#@X35#CX4<,3<P0P;Q0NPyQ0TPyPpPuPePnP>PJPEPMPNPKPOQ07PPPQ1<CHPGP0P4MDAP;PwQ08PSP0PyPTF7P;PqPwPyPgPSP0Q08,1;R{P0PHP7P6P7PUP7Q03%67R|PV%D7R}$0IP7P715|=149=[,]7L0HGN,UHG;3:X0A,3AX1?Q0MDgPlQ06,1;Pf%D1%e1PfQ05Q0G11;xS0UCXCXPBQ06,=;1=;xP;Q06P;PxP;PxP@P;Q06DODSFvQ00PlP{Pf%e7,V}PfPHQ0GPqCXD|PBP;Q08PtP;Q08PLQ089\z;CuDYP;P3fyRzfzS0VPzPrfwRLPyPpP_PaP`PbPcQ09P>PJPEPMQ0AP0P4MC9P;f|RtP1PRP0PzQ02F7P;11;tPtPzPgPRP0Q0BQ0CPhPFQ0DPIPiPGPjDFDIG;3:X0A,3AX1?P^PlQ0EPfQ0FPfQ0HQ0V,1;PBQ0IQ0V,=;RqQ0JQ0V,G;R}Q0V=^;@R{Q0K'KEtGBE>X2:#@X35#CX4<,3<P0PlQ0M,1;Pf%D8%e8'VPfQ0NQ0GPsCXD|PBP;Q0L1=;zP;Q0LP;PzP;PzP@P;Q0LDODSDYQ00PBP;Q0?PqH02P;Q0?P}Q0?9\{;CuP;P3f}S0Wf~S0XQ0WPtf{R{PLPwPePnPmPdP_PaP`PbPcQ09Q0AP0P4MC9P;p+01AR}P1POP0Q0WQ07F7P;11;}S0YP}Q0WPgPOP0Q0BQ0CPhPPQ0DPQPiPRPjDFDIG;3:X0A,3AX1?P[PlQ0EPfQ0FPfQ0HQ0X,1;PBQ0IP;Q0XQ0JQ0X,G;RqQ0X=^;@RsQ0K'K3WDcGBE>X2:#@X35#CX4<,3<P0PBP;Q0>1=;tH02P;Q0=P;Q0WP;Q0WP@P;Q0=DODSQ00B00;^qA\s;^P;P3p+01BRsp+01CRqPsP}p+01@S0ZP{Q0VPuPoPvPkPePnPmPdP_PaQ0AP0P4MC9P;p+01ER9P1PEP0PsPMF7P;11;9S0[P9PsPgPEP0FlS0\Q0BQ0C15hNQ0DPKAWiOjDIDJX0A,3AX1?PXPlQ0EPfQ0FPfQ0H11;qS0]PBQ0I1=;qS0^Q0J1G;qS0_A^;q@S0`Q0K'KEtGBE>X2:#@X35#CX4<,3<P01G;}:00;\P;PsP@P;Q0<DOP<P;P3P9p+01FR|P9p+01DR~PqQ0XQ0WQ0TPyPpPuPoPvPkPePnPmQ0AP0P4MC9P;p+01HS0aP1Q09P0P9P>F7P;P;Q0aQ0aP9PgQ09P0G`S0bQ0BQ0C15hJQ0DPEAWiMjDIDJX0A,3AX1?Q03PlQ0EPfQ0FPfQ0H11;|S0EPBQ0IP;P|Q0JP;P|P;P|P@Q0KCjChDcGBE>X2:#@X35#CX4<P[P5P;PYP~P9P~PqPsQ0WPtPyPpPuPoPvPkPePnPmPdQ0AP0P4MC9P;p+01GS0KPXP>P0P~PJF7S0JP;P;Q0KQ0KP~PgP>P0G`S0IQ0B11;XS0BP0P2P3P6PhPEQ0DPMPiPNPjDFG~DJX0A,3AX1?PVPl11;YS0CPfQ0FPfQ0HQ0[PBP;PY1=;9P;PYP;P9P;P9P@P;PYDODSDYGBE>X2:#@X35P^P:P;PZPqP~PqPsP}PtP{PpPuPoPvPkPePnPmPdP_Q0<,<CS0[P0P4MC9P;P|Q0;PJP0PqPEF7S0HP;Q0EP|PqPgPJP0FlS0EQ0<#HS0cQ0;,1;S0dP0Q0<P3P6PhPMQ0DPNPiPKPjDFG~DJX0A,3AX1?PWPl11;ZPfQ0FPfQ0G,V]11;~PBP;PZ1=;~P;PZP;P~P;P~P@P;PZDODSDYGBE>X2:Q0?P;P[PsPqPsP}Q0ZP{Q0VPuPoPvPkPePnPmPdP_Pa1<C\R@P0P4MC9P;P9PYPEP0PsPMQ0\%H\Q0CP0P\Q0>P6Q0>PNQ0>PKQ0>#6RjPOQ0>Q0>Q0>Q0>15j=Q0=/4=[C8EQGN3:GmRj'0X0A,3AX1?RiPXDgPl11;[PfQ0?#DQ0?#e'VPfP^Q0GQ0]CXD|S0]PBP;P[Q0^H02S0^Q0_:00;[S0_Q0`?\;[S0`'0S0G'0S0\'0P;P[PsPqPsP}Q0ZP{Q0VPuPoPvPkPePnPmPdP_PaP@P>P0P4MDA/0jX0A,3AX1?PiPXQ08P~PqPsP}PtP{PpPuPoPvPkPePnPmPdP_Q0[Q09P0P4MDAQ0HQ0EQ0cQ0dP0Q0<Q0=P6DTQ0=PMQ0=PNQ0=#6RiPKQ0=Q0=Q0=Q0=15i=14^=[C8G?DJS0='0X0A,3AX1?P0O1Q01PAP~PqPsP}PtP{PpPuPoPvPkPePnPmPdP_Q0[Q09P0P3MDAQ0='0X0AP9P~PqPsQ0WPtPyPpPuPoPvPkPePnPmPd1<C[P0P2MC9Q0JQ0I%H[Q0BP0P[P^P6P^PEP^PM%6^RiPNP^P^P^P^15i=14]=[C8EQGNDJX0A,3AP0P|P9P~PqQ0XQ0WQ0TPyPpPuPoPvPkPePnPm1<CZPbP0P1MDAP;Q0aPWQ09P0P9P>F7Q0b%HZP;PWP0PZP]P6P]PJP]PE%6]RiPMP]P]P]P]15i=14\=[C8G?FfDJQ00Q0KP|P9P~Q0ZQ0XPxQ0TPyPpPuPoPvPkPePn1<CYP`P4P7MDAP;p+01IRiPVPcP4P|Q09P;11;iPiP|PgPcP4PYP;PVP4PYP\P6P\P>P\PJ%6\R]PEP\P\P\P\15]=Q0</4=[C8G?GEG;GmPiQ0aQ0KP|PsP}PLPwPxQ0TPyPpPuPoPvPk1<CXR]P0P8MC9P;p+01KRjPUP`P0Q0aPbF7P;11;jPjQ0aPgP`P0PXP;PUP0PXP[P6P[PcP[Q09%6[R@P>P[P[P[P[15@=14Z=[C8G?GEG;3:X0A,3AP0PiQ0aQ0KP|PsP}PLPwPxQ0TPyPpPuPoPvPkP]P_P2P8MDAP;p+01LR2PTPaP1PiP`P;11;2P2PiPgPaP1PWP;PTP1PWPZP6PZPbPZPc%6ZR]Q09PZPZPZPZ15]=14Y=[C8G?GEG;GmQ00P;p+01MR]PSP_P7p+01JS0<PaF7P;11;]P]Q0<PgP_P7PVP;PSP7PVPYP6PYP`PYPb%6YRZPcPYPYPYPY15Z=Q0;/4=[C8G?GEG;P]P2PjQ0<P|P9P{Q0VPzPrPLPwPxQ0TPyPp1<CUP0Q0NMC9P;p+01ORZPGPmP0P2PdF7P;11;ZPZP2PgPmP0PUP;PGP0PUPXP6PXP_PXPa%6XR@P`PXPXPXPX15@=14W=[C8G?GEG;3:X0A,3AP0P;PZPGPmP8P2PdF7P;p+01PR8,1;P8P]PgPnQ05PTP;PIQ05PTPWP6PWPdPWP_%6WR@PaPWPWPWPW15@=14V=[C8G?GEG;Q00P;P;p+01QS05Q05p+01NS0;PgPePHG`PSP;PFPHPSPVP6PVPmPVPd%6VR@P_PVPVPVPV15@=Q03/4=[C8G?GEQ05P8PZQ0;Q0<PiQ0ZQ0XQ0WPtP{Q0VPzPrPLPw1<CGP0Q0MMC9P;p+01SR@PRPvP0P8PkF7P;11;@RWP@P8PgPvP0PGP;PRP0PGPUP6PUPePUPn%6URBPmPUPUPUPU15B=14T=[C8G?GEG;3:X0A,3AP0P;PWP@P8PgPvQ0NFlPIP;PQQ06PIPTP6PTPkPTPe%6TRWPnPTPTPTPT15W=14S=[C8G?GEQ00%HFP;PPQ08PFPSP6PSPvPSPk%6SRWPePSPSPSPS15W=Q0:/4=[C8G?Ffp+01US06p+01TRWP@p+01RS0NQ0;P]P~PqPsP}Q0ZQ0XQ0WPtP{Q0V1<CRP0Q0>MC9P;p+01WRBPOPyP0PWPpF7P;11;BPBPWPgPyP0%HRS0MP;POP0PRPGP6Ep%iGPuPGPo%6GRfPvPGPGPGPG15f=14I=[C8EQDIG;3:X0A,3AP0Q0MP;PKQ0LPQPIP6PIPpPIPu%6IRfPoPIPIPIPI15f=14F=[C8G?FfQ00P;PNQ0?PPPFP6EpPFPyPFPp%6FRfPuPFPFPFPF15f=Q02/4=[C8G?p+01YS0Lp+01XRfPBp+01VRlQ0NQ05Q0aQ0KP|P9P~PqPsP}Q0ZQ0X1<COP0P\MC9P;p+01[R\PEPLP0PfPwF7P;11;\P\PfPgPLP011;ES0bP0POPRP6PRPxPRQ0T%6RRhPyPRPRPRPR15h=14Q=[C8EQGN,UOG;3:X0A,3AP0Q0bQ0>POPRP6DTPQPwPQPx%6QRhQ0TPQPQPQPQ15h=14P=[C8G?Q001{PLPPPw%6PRhPxPPPPPPPP15h=Q07/4=[C8EQp+01]S07p+01\S0>P\p+01ZS0bPlQ06P2PjQ0<PiQ0aQ0KP|P9P~Pq1<CEP0PYMC9P;p+01_RYPcP{P0Q0>Q0VF7P;11;YPYQ0>PgP{P0PEP;PcP0PEPOP61{OzS0B1qOr%6ORhPLPOPOPO15h=14K=[C8,nODIGEG;3:X0A,3AP0Q0BPKPz%6KRhPrPKPKPKPK15h=14N=[C8EQQ00Q0V,qN%6NRhPzPNPNPN15h=14M=[,]NJ07p+01aS0Vp+01`RMPYp+01^RhQ0bQ0LP8PZQ0;P]P2PjQ0<PiQ0aQ0K1<CcP0PVMC9P;p+01cRKP_Q0ZP0PMQ0XF7P;11;KPKPMPgQ0ZP0Q0PP0PcPEP6PEQ0W1qEtS0P%6ERQ/5{PEPEPE15Q=14J=[C8,nE3:GN,UcG;3:X0A,3AP0Q0P%6JRQPtPJPJPJ15Q=14>=[,]JJ07Q00%6>RQQ0W'5P>P>P>15Q=Q09/4=[C8,n>p+01eS09p+01dRQPKp+01bS0XPhQ07PWP@Q0NQ05P8PZQ0;P]P2Pj1<C_P0PSMC9P;p+01gS0IPeP~P0PQPqF7P;Q0I,1;Q0IPQPgP~P0Q0RP0P_PcP6PcPs%6cS0RQ0Z'5S0J%Dc#HPcPcPcQ0R/5=14b=[C83::06c}GN,U_G;3:X0A,3AP0Q0JPbPbPb1Mb=14`=[C8,nbQ00%D`#HP`P`P`1M`=14a=[C8p+01iS0Rp+01hS01Q0Ip+01fS0dQ0XQ0VPfPBPlQ06PWP@Q0NQ05P8PZ1<CeP0PFMC9P;p+01kS0cPuQ0aP0Q01Q0KF7P;Q0c,1;Q0cQ01PgQ0aP0Q0SP0PeP_P6P_P|%6_R|%D_#HS0S%r_15|=14d=[9z__3:7W~:06_9GN,UeG;3:X0A,3AP0Q0SPdPdPd1Md=14m=[C8Q00%rm1Mm=14n=[9zmmp+01mS01p+01lR9Q0cp+01jR|Q0dQ09Q0>P\Q0bQ0LPfPBPlQ06PWP@1<CuP0PPMC9P;p+01oRPPxP2P0P9PjF7P;11;PPPP9PgP2P0Q0UP0PuPeP6PeQ0<PePi%6eRiQ0aPe%reR9%we15i=14k=[,]e3:EQGN,UuG;3:X0A,3AP01Mk=14v=[9zkkQ00%wv1Mv=14o=[,]vp+021S0ap+020RiPPp+01nRjP|Q0RPMPYPhQ07Q0>P\Q0bQ0LPfPB1<CxP0PNMC9P;p+023RNPzP8P0PiPZF7P;11;NPNPiPgP8P0PxP;PzP0PxPuP6PuQ0;PuP]%6uR]P2Pu%wuR2%su15]=14p=[3:-0FuG?GEG;3:X0A,3AP01Mp=14y=[,]pQ00%sy1My=Q0T/4=[p+025Ryp+024R]PNp+022PjQ01PQPKQ0XQ0VPMPYPhQ07Q0>P\1<CzP0P>MC9P;p+027R>Q0WPWP0P]P@F7P;11;>P>P]PgPWP0PzP;Q0WP0PzPxP6PxQ0NPxQ05%6xR\P8Px%sxR815\=14w=['0:0GxxG?GEG;3:X0A,3AP01Mw=14L=[PAp+028P>p+026RwPyQ0aPiQ0IQ0dQ09PQPKQ0XQ0VPMPYPh1<CtP0PbMC9P;p+02:RxP}PBP0P>PlF7P;11;xPxP>PgPBP0Q0YP0PtPrP6PrQ06PrPW%6rRBP@PrPrPrPr15B=14z=[C8EQGN,UtG;3:X0APEP>PwPyP]PiPPQ0dQ09PQPKQ0XQ0VPMPYPhQ071<C{S0YPEPcMC9P;p+029RCQ0ZPlPEPwQ06F7S06P;P;PCPCPwPgPlPEG`S0I%H{S0aP;Q0ZPEP{PLP6EpS0Z1{LWS051qL@R@%6LRWQ0N'5R6%DL#HRl%rLRg%wLRC%sLRL15W=14r=[Rr'0R='0RW'0Rz'0RB'0Rx'0R\'0Rj'0RN'0RZ'0R|'0P>PwPyP]PiPPQ0dQ09PQPKQ0XQ0VPMPYPhQ07Q0YPfPEPcPONE0@Q06P|PRQ0IPZPGQ0aPNPUQ0ZPjPXQ05P\P[P@PxP^P6PBQ0?PlPzQ08PgPWPHPCP=P7PLPrP4P0FRFRFRFRFRFRCxWIXD8P4P0O2n2001000000121000000WDXC2P4P0O2n2001000000121000000WCXB9P4P0O2n2001000000121000000WBWAP4P0O2n2001000000121000000WAW@P4P0O2n2001000000121000000W@W?P4P0O2n2001000000121000000W?W>P4P0O2n2001000000121000000W>W=P4P0O2n2001000000121000000W=W<P4P0O2n2001000000121000000W<W;P4P0O2n2001000000121000000W;W:P4P0O2n2001000000121000000W:W5P4P0O2n2001000000121000000W5XwAP4P0O2n2001000000121100000P~PqPsP}PtP{PpPuPoPvPkPePnPmPdP_Q0[P0P3MC9Q0='0X0A,3AeWJX1?L0JQ0]Q0\PHQ0^Q0GP7Q0_Q0`P4P0FRFRCxCxCxWHW9P4P0O2n2001000010121000000W9W8P4P0O2n2001000010121000000W8W7P4P0O2n2001000010121000000W7W5P4P0O2n2001000010121000000W5Xv:P4P0O2n2011000010121100000W5Xu5P4P0O2n2011000010121100000W5Xt<P4P0O2n2011000010121100000P;P3PaP_PaP`PbPJPEQ02PFPIPGQ0:PSPTPUQ03PVQ0AP0P4MC9Q0O'0X0A,3AX1?P1Q0QE>X2:#@X35#CX4<,3<R<eP<eWEW6L0KUUUUUUUUUUUUW]XT5XX5Xs5XY5WZWVWFXqDXpDXoDXnDXaDX`DXiDXhDXgDXfDXeDXdDXcDXbDXSDXRDXQDXPDXODXNDXMDXLDX_DX^DXmDXlDXkDXrDXWDXjDW\WKWx20L34eWGX[5XU5o"). Qed.
Lemma pixCreateTemplateNoInit_nn_res0_cps_of_F : pixCreateTemplateNoInit_nn_res0_cpsF -> pixCreateTemplateNoInit_nn_res0_cps.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_iface ()) ["PoIface"] "p'0h02m'h12msh23cv'h32v'h44pixdh53Σ'h62H9h71ch83H10h93H11h:3H12h;3H14h<3H15h=3H16h>3H17h?3H18h@2HchA1FhB1HhC3H13hD3H19hE3HmshF3PMchG7__arithhH4__ffhI8__varmaphJ5__withK2a0hL2a1hM2a2hN2a3hO2a4hP2a5hQ2a6hR2a7hS2cvhT2fchU2gphV2lohW1mhX4pixshY2rahZ2s0h[2s1h\3s10h]3s11h^2s2h_2s3h`2s4ha2s5hb2s6hc2s7hd2s8he2s9hf2sphg2t0hh2t1hi2t2hj2t3hk2t4hl2t5hm2t6hn2tpho1vhp1xi001xhq2x0hr2x1hs2x2ht2x3hu2Σp%0p&0p;1p;2p;3p;5p;6p;Sp;4p;Dp;Cp;7p;Ep;8g00>Xk10CTg00>3j1ITg00?Pj1]Tg00?nj1fTg00@Qj1uTg00A6k209Tg00Abk101Tg00BDj1~Tg00CBj1{Tg00D>j29Tg00:0j37j2lTg00Ddj20Tg01USj5NTg008\j1LTg006gj1STg00OHk10ATg00PCk60>Tg00Q>j2qTg00Q[k508Tg00RVk103Tg00XAj2KTg00lTlSmTg00mQj4}j5XTg00nJlD>Tg010?j2iTg00MOj1nTg008AS00j21Tg0144S01j22Tg00bQj1^Tg015mj2BTg00Vlj2CTg016kj2TTg01TXlC5Tg00cOk10BTg00dKk10@Tg00dik10?Tg00eTj2tTg00hBj4sTg00hmk70=Tg00j5k20<Tg00]ok20;Tg00jWk20:Tg00kCk307Tg00kbk405Tg00oCj73Tg01klj4ZTg011?j7UTg01lmj4PTg01WNmE06Tg01XNj4YTg01Xhj8xTg01Yfj8wTg00GVj1_Tg017ij2eTg01;Pj7vTg009Uj4gTf0R0#I#Ip>02%I0#I#I#Ip=Wg00:JR1g00:hR2770#_p=Of5R3f4R4'0f3R5f2R6f1R7P0DNp=df6R8P4P5P6P7CP/10,13'1p=Ef7R9P8P3P4P5P6P7FU/10p=4P9P8P3P4P5P6P7F3/10p=V1T56/e7/K0p=M1B3497981C679715/10'1p=JP4P5P6P7CZ9783/10p=;P3P4P5P6P7DX/10p=6g01CMR:/20p=:g00;FR;/20p==1210p=?P7g01@XR<g01A7R=P=g01AWR>P0g01B7Fvp=r1K70,16p>041170,16p=81T45/e61T70'Kp=@1C451C67571/10p=D1B451B67573/10p=HP91083P4P5P6P7P0FUp=\P4P5P6P7CP/10p=Q1170,16,15,14p=G1T67/e0p=aA7167/10p>00A7834A7567/10'1p=k1083P4P5P6P7DN/10p=h1T70,K6p=`1C56=717/10p=|P3P4P5P6P7DN/10p=AA7172#_/10p=RA7345A7167/10'1p=jA7192#_1083P4P5P6P7DN/10'1p=FP4P5P6P7CP%L0'1p=<1B83=7941C56=717/10'1p=oP5P6P7P0CZ9734p=z1067=750p=p1B67=750p=b1C67=710p=c%L0,17p=yP8P3P4P5P6P7P0CgCgp=[g01mnp,2RTR?$0CR@g01BWp-0[g00<CRA#IRB#IRC#IRD$02RE#IRF#]RG#fRH%uB#]009H%]E#f%]D#f$01\HRIfVRJ#~fWRK#{fTRLg01EF,9G57HfORM19G3RN57Hf[RO,0?S02f8S03P8P3P4DN%L8S04P?f]RPf:RQfZRRf9RS%SD$0AJ0>P?f^RD%uA#S%SCg01`I%SE'qREI08f_RC,0?S05$03%WF#W#W#W#W#S'qg01Gm'Kg01=<P?f`RFPCg01N3RTPDPPf\RUPOPRfYRVfXRWPKPJfURXPLfSRYfRRZfQR[fPR\PMfNR]fMR^fLR_fKR`fJRafIRbfHS06fGRcfFS07fES08fDS09fCS0:fBRdfARef@S0;f?S0<f>Rfg01oGRgf=RhMSm'lC}RiPig01PBS0=P?P5fdRifeRjPifcRkfbRlPDPPPLPYPZP[P\PMP]P^P_P`19G4RmQ07P0P7MD>P?fgRnP3Q09P0PiQ0:P?10?nRoPnPi1i11Rp#nRqQ09P0%O4S0>P?P3P0P4P5P6EdS0?PeP5Q0;P6%L5RrFEG4GVRs'1X0I,2IX1TP4%^pRp10?5S0@P6P7P010?jS0Ag01Q7,i1#^Rt1B?5S0BP?Pj1C?5S0CP?PjP?PjPE1T?5S0DCMGJF;RuE6X2:#:X3;#=X41#?X5@,2@W7Q0=P?P5PiPjPiPkPlPDPPPLPYPZP[P\PMP]P^P_P`PmP0P7MC5/1sX0I,2IX1TP4PuE6X2:#:X3;#=X41#?X5@,2@W7faRuPFPCPDPPPUPOPRPVPWPKPJPXPLPYPZP[P\PMP]P^P_P`PaPbQ06PcQ07Q08Q09Q0:PdPeQ0;Q0<PfPhf<S0Ef;S0FPQPS%SARAQ03P9P8P3P4g01IQRs#n%^s&0B1&0@1&0?1RsP<P=P=P>P11t1AR=g01KHR<P=Cs,rsP1P=P<%SBRB,t1Cs,rsK0=20<s>P0P6g01LVRsg01M6R>+0;20:06=7s>dB07127H05bHbIbJ1KAA@04ABP0bGP5P6P7P0OcQ0=P?PuPFPCPDPPPUPOPRPVPWPKPJPXPLPYPZP[P\PMP]P^P_P`PaPbQ06PcQ07Q08Q09Q0:PdPeQ0;Q0<PgPfMSm,lTP0DXP0W@W7Q0=Q0=P?P5PjffRgPjPiPkPCPDPXPLPYPZP[P\PMP]P^P_PmPcP0P7MD>P?fhRBP3Q08P0PjQ09P?10?BRAPBPjPqQ08P0Q0>Q0?PdP5PeP6PrFEG4GVS0G'1X0I,2IX1TR2P4PpQ0@P6P7P010?gPtQ0BP?PgQ0CP?PgP?PgPEQ0DCMGJF;S0HE6X2:#:X3;#=X41#?X5@,2@W7P0O1Q01P@P?P5PjP2P3Q0HE6X2:#:X3;#=X41#?X5@P?P5PgPnPgPjPiPFPCPJPXPLPYPZP[P\PMP]P^PmP0P7MC5P?fiR2P3Q07P0PgQ08F3P?10?2S0IP2PgPqQ07P0Q0>Q0?Q0:P5PdP6PrFEG438X0I,2IX1TP8PpQ0@P6P7P0PoPtQ0BP?PnQ0CP?PnP?PnPEQ0DCMGJF;E6X2:#:X3;#=X41#?X5@,2@P0P?P5PnPBPnPgPjPuPFPKPJPXPLPYPZP[P\PMP]PmPbP0P7MD>P?fjRoP3PcP0PnQ07F3P?10?oPoPnPqPcP0Q0>Q0?Q09P5Q0:P6PrFEG438X0I,2IX1TP9PpQ0@P6P7P0PAPtQ0BP?PBQ0CP?PBP?PBPEQ0DCMGJF;E6X2:#:X3;#=X41#?Q01P1P?P4PBP2PBPnPgPlPuPWPKPJPXPLPYPZP[P\PMPmPaP0P7MD>P?fkRAP8Q06P0PBPcF3P?10?AS0JPAPBPqQ06P0Q0>10?8R>P0P4P5P6DNQ08P5Q09P6PrFEG438X0I,2IX1TQ03Pp10?4P6P7P0Q0IPtP?P4P?P2P?P4P?P2P?P2PEP?P4D@DDEHF;E6X2:#:X3;#=X41P?P5PoPAPoP2PBPiPkPRPVPWPKPJPXPLPYPZP[PmP0P7MC5P?fmRsP3PaP0PoPbF3P?P?PsPsPoPqPaP0G\R<Q0>Q0?PcP5Q07P6PrDQR='1DGX0I,2IX1TPQPpQ0@P6P7P0Q0JCZRvPtQ0B1B?ARwQ0C1C?ARxAa?AERyQ0D'K400FkE6X2:#:X3;#=X41#?X5@,2@P0P?P8PoPAPoP2PBPiPkPRPVPWPKPJPXPLPYPZP[PmP_P0P7MD>P?PsQ03PaP0PoPbF3P<Q0>P?Q03P0P4P5P6P=FhDGX0I,2IX1TPQPpP>PvPt1B?8PwP?P8PxA`y?8C|FkE6X2:#:X3;#=Q01P;P?P9PAflRyPAPoP2PjPiPOPRPVPWPKPJPXPLPYPZPNP^P0P7MD>P?fnRNPSP`P0PAPaF3P?10?NRxPNPAPqP`P010?SRwP0P3P5P6Q06P5PcP6PrDQEA,R3G438X0I,2IX1TQ0FPp10?9P5P7P010?yS0KPtP?P9P?PyP?P9P?PyP?PyPEP?P9D@DDEHF;E6X2:#:X3;P?P5PNfoRvPNPsPyPBPnPDPPPUPOPRPVPWPKPJPXPmP0P7MC5P?fqR>P3P]P0PNP^F3P?10?>R=P>PNPqP]P0FUR<Q0>Q0?P`P5PaP6CP;8rDGX0I,2IX1TPfPpQ0@P6P7P010?vRzPtQ0B1B?vR{Q0C1C?vR|Aa?vER}Q0D'KEjF;E6X2:#:X3;#=X41#?X5@,2@P0P?PSPsPNPsPyPAPnPgPPPUPOPRPVPWPKPJPXPL19G9PMP0P7MD>P?fpR~Q0FP^P0PsP_F3P?10?~P~PsPqP^P0P9P?Q0FP0P9P5P6PaP5PbP6PrDQGFG438X0I,2IX1TPhPpPwP3P7P0PxPtP?PSP?PNP?PSP?PNP?PNPEP?PSD@DDEHF;E6X2:#:Q01P:P?PQPNPvPNPsPyPBPnPDPPPUPOPRPVPWPKPJPXQ03,9GP\P0P7MD>P?P>Q0EP]P0PNP^F3P<Q03#OQ0E,0?R<P0Q03P4P6P`P4PaP6P4D<EADGX0I,2IX1TPfPp10?QP8P6P0PzPtP?PQP{P?PQP|A`}?QGoF;E6X2:P?P5frR}fsR|P}P>P~PyPAPlPuPFPCPDPPPUPOPRPVPmP0P7MC5P?fuS0LP3PZP0P}P[F3P?Q0L,0?R{Q0LP}PqPZP0Q0>Q0?PMP5P]P6PrFEG438X0I,2IX1TPdPpQ0@P6P7P010?|RdPtQ0BP?P|Q0CP?P|P?P|PEQ0DCMGJF;E6X2:#:X3;#=X41#?X5@,2@P0P?Q0EP~P>P~PvPNPoP2PFPCPDPPPUPOPRPVPWPK19GQPZP0P7MD>P?P|PfP\P0P~PMF3P?PdP|P~PqP\P0PQP?PfP0PQP8P6P^P8P_P6Q04DQGFG438X0I,2IX1TQ0;PpP<Q03P4P0P=PtP?Q0EP?P>P?Q0EP?P>P?P>PEP?Q0ED@DDEHF;E6Q00P?PhP>P}P>P~PvPAPoPuPFPCPDPPPUPOPRPVPWQ0F,9GPYP0P7MD>P?ftRWQ0<P[P0P>P\F3P?10?WPWP>PqP[P0Q0FP?Q0<P0Q0FP9P5P]P9P^P5P9D<GFG438X0I,2IX1TPeDXPp10?hPSP3P710?}PtP?PhP?P}P?PhP?P}P?P}PEP?PhD@DDEHF;P?P5fvR=fwS04P=Q0LPWP~PvPgPjPiPkPlPuPFPCPDPPPmP0P7MC5P?fyS0MP3PJP0P=PXF3P?Q0M,0?Q0MP=PqPJP0Q0>Q0?PYP5PZP6PrFEG438X0I,2IX1TQ07PpQ0@P6P7P0Q04,0?PtQ0BP?Q04Q0CP?Q04P?Q04PEQ0DCMGJF;E6X2:#:X3;#=X41#?X5@,2@P0P?Q0<P|PWP|P}P>PsPyPkPlPuPFPCPDPPPUPOPR19GhPXP0P7MD>P?P=PePYP0P|PZF3P?10?=RUP=P|PqPYP010?eR<P0PhPSP3P\PSPMP3PSD<EA,RhG438X0I,2IX1TQ0:DXPpQ0;,0?Q0EQ03P4P{PtP?Q0;P?Q0LP?Q0;P?Q0LP?Q0LPEP?Q0;D@DDEHF;Q00PpP<PhPSP3PUEzPtP?PeP?P=P?PeP?P=P?P=PEP?PeD@DDEHP?P5fzRUf{R<PUQ0MfxS0NPWP|PoP2PBPnPgPjPiPkPlPuPmP0P7MC5P?f}R{P3PRP0PUPVF3P?10?{P{PUPqPRP0Q0>Q0?PKP5PJP6PrFEG438X0I,2IX1TPaPpQ0@P6P7P010?<PtQ0BP?P<Q0CP?P<P?P<PEQ0DCMGJF;E6X2:#:X3;#=X41#?X5@,2@P0PpP?Q0:Q0<Q0FP9Q0N,0?CZCpPtP?Q09P?Q0MP?Q09P?Q0MP?Q0MPEP?Q09D@DDEHQ00PtP?Q081B?UCbP?Q08P?PUP?PUPEP?Q08D@DDP?P5f~R8p+01@S0OP8P{f|S0PQ0NQ04PNPsPyPAPoP2PBPnPgPjPmP0P7MC5P?p+01BRQP3PDP0P8PPF3P?10?QPQP8PqPDP0Q0>Q0?POP5PRP6PrFEG438X0I,2IX1TP]PpQ0@P6P7P0Q0O,0?PtQ0BP?Q0OQ0CP?Q0OP?Q0OPEQ0DCMGJF;E6X2:#:X3;#=X41#?X5@,2@P0PtP?PcQ0P,B?CbP?Q06P?P{P?P{PEP?Q06D@DDQ001C?89c?bP?P8PEP?PbD@P?P5p+01CRfp+01DRdPfPQp+01AS0QQ0PP<P}P>P~PvPNPsPyPAPoP2PmP0P7MC5P?p+01FRzP3PlP0PfPuF3P?10?zS0RPzPfPqPlP0FUS0SQ0>Q0?PCP5PDP6CP;8rDGX0I,2IX1TPZPpQ0@P6P7P010?dS0TPtQ0B1B?dS0UQ0C1C?dS0VAa?dES0WQ0D'KEjF;E6X2:#:X3;#=X41#?X5@,2@P0Q0Q,C?9c?`P?PQPEP?P_D@P@P?P5Pzp+01GRxPzp+01ERwPdQ0OP8Q0LPWP|P}P>P~PvPNPsPyPmP0P7MC5P?p+01IS0XP3PjP0PzPiF3P?Q0X,0?S0YQ0XPzPqPjP0Q0>Q0?PlP5PuP6PrFEG438X0I,2IX1TPXPpQ0@P6P7P010?xS0@PtQ0BP?PxQ0CP?PxP?PxPEQ0DCMGJF;E6X2:#:X3;#=X41#?X5@P^P1P?P\PwPzPwPdPfP8P{PWP|P}P>P~PvPNPsPyPAPmP0P7MC5P?p+01HS0DPZPiP0PwPkF3S0CP?P?Q0DQ0DPwPqPiP0G\S0BQ0>10?ZS0>P0P4P5P6PuP5PFP6PrDQEADGX0I,2IX1TPLPp10?\S0?P6P7P0Q0RPtP?P\P?PzP?P\P?PzP?PzPEP?P\D@DDEHF;E6X2:#:X3;#=X41PbP;P?PMPdPwPdPfPQP{Q0PP|P}P>P~PvPNPsPyPAPo19G^S0RP0P7MC5P?PxP[PkP0PdPlF3S0ZP?Q0@PxPdPqPkP0FUS0@%O^S0[10?[S0\P0P^P5P6PFP5PCP6PrDQEADGX0I,2IX1TPYPp10?MS0]P`P7P010?wRrPtP?PMP?PwP?PMP?PwP?PwPEP?PMD@DDEHF;E6X2:#:X3;Q08P:P?P]PfPdPfPQQ0QQ0PP<P}P>P~PvPNPsPyPAPoP219G_S0^P0P7MC5P?PzP\PlP0PfPuF3S0_Q0S%O_S0`Q0?P0P_Q06P6PCQ06PDP6Q06#LS0aDQEADGX0I,2IX1TPZPp10?]PaQ07P0Q0TPtP?P]Q0UP?P]Q0VQ0W?`?]GoF;E6X2:PeP?P^PQPfPQQ0QQ0OP<PUP>P~PvPNPsPyPAPoP2PB19G`S0WP0P7MC5P?PwPMPuP0PQPFP?PrPwPQPqPuP0Q0]P0P`PcQ0:PDPcPPQ0:PcD<EA,R`G4GVRr'1X0I,2IX1TS0]P[DXPpP?P^PbQ08Pe10?fCZCpS0VPtP?P^1B?fCbS0U1C?f9c?^S0TP?PfPEP?P^D@S0b'1S0c'1S0d'1P?P^PQPfPQQ0QQ0OP<PUP>P~PvPNPsPyPAPoP2PBQ0WPkP0P7MD>/1rX0I,2IX1TQ0]P[PhPdPfPQQ0QQ0PP<P}P>P~PvPNPsPyPAPoP2Q0^PiP0P7MD>Q0_Q0SQ0`Q0?P0P_Q06Q09DNPCQ06PDQ09Q0aDQDGS0a'1X0I,2IX1TP0O1Q01PIPdPfPQQ0QQ0PP<P}P>P~PvPNPsPyPAPoP2Q0^PiP0P6MD>Q0a'1X0IPwPdPfPQP{Q0PP|P}P>P~PvPNPsPyPAPoQ0RP0P5MC5Q0ZQ0@Q0[Q0\P0P^PbQ08PFPbPCQ08PbD<EADGX0I,2IP0PzPwPdPfP8P{PWP|P}P>P~PvPNPsPyPA19G]PgP0P4MD>Q0CQ0B%O]Q0>P0P]PaQ07PuPaPFQ07PaD<EADGQ00PxPzPwPdQ0OP8Q0LPWP|P}P>P~PvPNPsPy19GMPnP7P3MD>P?Q0XPYPjP7PzPiP?Q0YQ0XPzPqPjP7PMP?PYP7PMP`PcPlP`PuPcP`D<GFG4GVQ0XQ0DPxPzPQQ0QQ04P=Q0LPWP|P}P>P~PvPN19G[RrP0P9MC5P?p+01KREPXPnP0Q0DPgF3P?10?EPEQ0DPqPnP0P[P?PXP0P[P^PbPiP^PkPbP^D<GFG438X0I,2IP0Q0XQ0DPxPzPQQ0QQ04P=Q0LPWP|P}P>P~PvPNPrP2P5P9MD>P?p+01LRrPJPBP4Q0XPnP?10?rPrQ0XPqPBP4PZP?PJP4PZP]PaPjP]PiPaP]D<GFG4GVQ00P?p+01MRaPKP2P3p+01JR4PBF3P?10?aPaP4PqP2P3PYP?PKP3PYPMP`PgPMPjP`PMD<GFG4PaPrPEP4PzPwP<PUQ0MQ0NQ04P=Q0LPWP|P}19GXP0Q0FMC5P?p+01ORtPVPAP0PrPoF3P?10?tPtPrPqPAP0PXP?PVP0PXP[P^PBP[PnP^P[D<GFG438X0I,2IP0P?PtPVPAP9PrPoF3P?p+01PR9,0?P9PaPqPyQ03PJP?PRQ03PJPZP]P2PZPBP]PZD<GFG4Q00P?P?p+01QS03Q03p+01NS0YPqPsPSG\Q02PSPKPYPMPoPYP2PMPYD<EA,RKQ03P9PtQ0YP4Q0XQ0OP8P{Q0PP<PUQ0MQ0NQ04P=19GVP0Q0<MC5P?p+01SRpPPPvP0P9PNF3P?10?pS0<PpP9PqPvP0PVP?PPP0PVPXP[PyPXPAP[PXD<GFG438X0I,2IP0P?Q0<PpP9PqPvQ0FFUPRP?PDQ0EPRPJPZPsPJPyPZPJD<GFQ00%OOQ05PhPOPKPYPNPKPsPYPKD<EAp+01US05p+01TR9Ppp+01RS0EQ0YPaPdPfPQQ0QQ0OP8P{Q0PP<PU19GPP0Q0:MC5P?p+01WRpPuP|P0P9P}F3P?10?pPpP9PqP|P0%OPR9P?PuP0PPPVPXEdP~PVPvPX%LVFEG438X0I,2IP0P?PlQ0;PDPRPJP>PRP~PJPRD<FhQ00P?PkPePCPOPKEdP}POP>PKPOD<p+01YS0;p+01XRKPpp+01VRJQ0EQ03Q0DPxPzPwPdPfPQQ0QQ0OP819GuP0PcMC5P?p+01[RcPjQ04P0PKP=F3P?10?cPcPKPqQ04P0Q0AP0PuPPPVPWPPP|PVPPD<EA,RuG438X0I,2IP0Q0AQ0:PuPPPVDNQ0LPDPWPRPDD<Q00P=PCQ0LPOCP%LCp+01]ROp+01\R=Pcp+01ZPJQ05PrPEP4Q0XQ0DPxPzPwPdPf19GjP0P`MC5P?p+01_R`P2P<P0P=PUF3P?10?`P`P=PqP<P0Q0IP0PjPuPPQ0NPuQ04PPCPRP/yuEA,RjG438X0I,2IP0%LlPIp+01`P`p+01^RlPOQ0;PKPtQ0YPaPrPEP4Q0XQ0DPxPz19GBP0P]MC5P?p+01bRtPyP8P0P`P{F3P?10?tPtP`PqP8P0Q0KP0PBPiPFP<PiPUPFPiD<EA,RBG438X0IPbP`PlPOP=PKPpQ0YPaPrPEP4Q0XQ0DPxPzPw19GnRGPbP^MC5P?p+01aRBPAP{PbPlQ0PF3RFP?P?PBPBPlPqP{PbG\R{%OnRqQ0JPbPnPkPCDNRnPUPkQ0MPCCPRU%LkRB'1R8'1Rt'1Ru'1RJ'1P`PlPOP=PKPpQ0YPaPrPEP4Q0XQ0DPxPzPwPGQ0OPbP^Q08NE06PFPJPeP{PuPhPqPtPSPnP8P3PUPBP7P0F[F[F[CYWDX?PP7P0O2n2001000000121000000W?W>P7P0O2n2001000000121000000W>X=9P7P0O2n2001000000121000000W=W<P7P0O2n2001000000121000000W<W;P7P0O2n2001000000121000000W;W6P7P0O2n2001000000121000000W6XtIP7P0O2n2001000000121100000PdPfPQQ0QQ0PP<P}P>P~PvPNPsPyPAPoP2Q0^P0P6MC5Q0a'1X0I,2IeWEX1TGxQ0VQ0dPSQ0UQ0cP3Q0TQ0bP7P0F[F[CYCYCYCYWCW:P7P0O2n2001000000121000000W:W9P7P0O2n2001000000121000000W9W8P7P0O2n2001000000121000000W8W6P7P0O2n2001000000121000000W6Xs:P7P0O2n2001000000121100000W6Xr;P7P0O2n2001000000121100000W6Xq1P7P0O2n2001000000121100000W6Xp@P7P0O2n2001000000121100000P?P5PjPgPjPiPkPCPDPXPLPYPZP[P\PMP]P^P_PmP0P7MC5Q0G'1X0I,2IX1TP3Q0HE6X2:#:X3;#=X41#?X5@,2@R@eP@eW@W7GwUUUUUUUUUXS:Xo;XX1XV1WWWTWAXmHXlHXkHXjHX]HX\HXeHXdHXcHXbHXaHX`HX_HX^HXRHXQHXPHXOHXNHXMHXLHXKHX[HXZHXiHXhHXgHXnHXUHXfHWYWFWug020UeWBo"). Qed.
Lemma pixCopy_nn_res0_cps_of_F : pixCopy_nn_res0_cpsF -> pixCopy_nn_res0_cps.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_iface ()) ["PoIface"] "p'0h02m'h12msh23cv'h32v'h44pixdh53Σ'h63H11h71ch83H12h93H13h:3H14h;3H16h<3H17h=3H18h>3H19h?3H20h@2HchA1FhB1HhC3H15hD3H21hE3HmshF3PMchG2a0hH2a1hI2a2hJ2a3hK2a4hL2a5hM2a6hN2a7hO2cvhP2fchQ2gphR2lohS1mhT4pixshU2rahV2s0hW2s1hX3s10hY3s11hZ2s2h[2s3h\2s4h]2s5h^2s6h_2s7h`2s8ha2s9hb2sphc2t0hd2t1he2t2hf2t3hg2t4hh2t5hi2t6hj2tphk1vhl1xi001xhm2x0hn2x1ho2x2hp2x3hq2Σp%0p&0p;1p;2p;3p;6p;5p;Sp;4p;Dp;Cp;7p;Ep;8g00>Xk107Tg00>3j1HTg00?Pj1\Tg00?nj1iTg00@Qj1hTg00A6k203Tg00Abj1{Tg00BDj1xTg00CBj1tTg00D>j28Tg00:0j37j2qTg01VQk106Tg008\j1KTg006gj1ZTg00OHk105Tg00PCk604Tg00Q>j2rTg00Q[k502Tg00Ddj20Tg00RVj1zTg00XAj2QTg00lTlSpTg00mQj4uj5[Tg00nJlD>Tg010?j2kTg00MOj1sTg008AS00j21Tg0144S01j22Tg00bQj1jTg015mj29Tg00Vlj2BTg016kj2UTg01TXlC5Tg00oCj73Tg01USj5JTg01klj4]Tg011?j7STg01lmj4OTg01WNlEvTg01XNj4WTg01Xhj8~Tg01Yfk800Tg00GVj1eTg017ij2gTg009Uj4lTf0R0#H#Hp=|f5R1f4R2'0f3R3f2R4f1R5P0DJp=`g00:JR6g00:hR7770#ep=L%H0#H#H#Hp=Xf6R8P2P3P4P5CO/10,11'1p=Gf7R9P8P1P2P3P4P5FS/10p=4P9P8P1P2P3P4P5F3/10p=VP2P3P41050C]p=I1B1297681U34/g5/Q0'1p=NA7812A7345/10'1p=MP1P2P3P4P5D[/10p=6g01CMR:/20p=<g00;FR;/20p==1260p=@1150,14p=;19459723/10p=_P2P3P4P5C]9781/10p=A1U23/g41U50'Qp=?1B231B45576/10p=E19231945571/10p=PP91081P2P3P4P5P0FSp=^P2P3P4P5CO/10p=R1150,14,13,12p=F1U45/g0p=fA7645/10p>011081P2P3P4P5DJ/10p=b1U50,Q4p=d1B34=765/10p=}P1P2P3P4P5DJ/10p=CA7657#e/10p=TA7123A7645/10'1p=oA7697#e1081P2P3P4P5DJ/10'1p=DP2P3P4P5CO%K0'1p=:1981=7921B34=765/10'1p=mP3P4P5P0C]9712p=y1045=730p=n1945=730p=a1B45=760p=c%K0,15p=wP8P1P2P3P4P5P0ClClp=Yg021mp,2RTR<$07R=g01BWp-0[g00<CR>#HR?#HR@#HRA#|RB#HRC#\RD#iRE%h?#\003E%\B#i%\A#i#{\ERAfVRB#xfWR?#tfTRFg01EF,8D57EfORG18D757E18D897EGP<f\R7f9RHP9P8P1E`&069#Lf8S02#KP<f_RIf<S03P7f;S04%h@#Z$05J04P<f`RJ%h>#Z%Z@g01`I%ZC'rR@I02faR>,0<S05#z%XC#X#X#X#X#Z'rg01Gm'Qg01=<P<fbRCP>g01N3RKPJPIf^S06f]RLP7f[RMfZRNfYROfXRPP?PBfURQPFfSRRfRRSfQRTfPRUPGfNRVfMRWfLRXfKRYfJS07fIRZfHR[fGS08fFS09fES0:fDS0;fCS0<fBR\fAS0=f@S0>g0236R]f?S0?MSp'qCuR^P^g01PBS0@P<P3ffR^fgR_P^feR`fdRaPJPIPBPQPFPRPSPTPUPGPVPW18D2RbP[P0P5MD>P<fiRcP1Q09P0P^Q0:P<10<cS0APcP^1k66Rd#sReQ09P0%L2S0BP<P1P0P2P3P4E`S0CQ0<P3P\P4%K3RfFGG4GVRg'1X0A,2AX1KP2%jdRd10<3S0DP4P5P0P<P_DIg01Q7,k6#jRh19<3S0E19<_1B<3S0FP<P_P<P_P@1U<3S0GFNFMRiE6X2:#<X3;#=X46#@X5=,2=W7Q0@P<P3P^P_P^P`PaPJPIPBPQPFPRPSPTPUPGPVPWPbP0P5MC5/1gX0A,2AX1KP2PiE6X2:#<X3;#=X46#@X5=,2=W7fcRiPCP>PJPIQ06PLP7PMPNPOPPP?PBPQPFPRPSPTPUPGPVPWPXPYQ07PZP[Q08Q09Q0:Q0;Q0<P\Q0=Q0>Q0?f>Rgf=RjQ03Q04f:RkPHQ02P9P8P1P2P3P4P5P0OcQ0@P<PiPCP>PJPIQ06PLP7PMPNPOPPP?PBPQPFPRPSPTPUPGPVPWPXPYQ07PZP[Q08Q09Q0:Q0;Q0<P\Q0=P]Q0>MSp,qKP0D[P0W@W7Q0@Q0@P<P3P_fhR]P_P^P`P>PJP?PBPQPFPRPSPTPUPGPVPbPZP0P5MD>P<fjRlP1Q08P0P_Q09P<10<lRmPlP_PeQ08P0Q0BQ0CQ0;P3Q0<P4PfFGG4GVS0H'1X0A,2AX1KRnP2PdQ0DP4P5P0P<P]DIPhQ0E19<]Q0FP<P]P<P]P@Q0GFNFMS0IE6X2:#<X3;#=X46#@X5=,2=W7P0O1Q01P=P<P3P_PnP1Q0IE6X2:#<X3;#=X46#@X5=P<P3P]PcP]P_P^PCP>PPP?PBPQPFPRPSPTPUPGPbP0P5MC5P<fkRnP1P[P0P]Q08F3P<10<nS0JPnP]PeP[P0Q0BQ0CQ0:P3Q0;P4PfFGG43;X0A,2AX1KP8PdQ0DP4P5P0Q0APhQ0EP<PcQ0FP<PcP<PcP@Q0GFND_FAE6X2:#<X3;#=X46#@X5=,2=P0P<P3PcPlPcP]P_PiPCPOPPP?PBPQPFPRPSPTPUPbPYP0P5MD>P<flRoP1PZP0PcP[F3P<10<oS0KPoPcPePZP0Q0BQ0CQ09P3Q0:P4PfFGG43;X0A,2AX1KP9PdQ0DP4P5P0PmPhQ0EP<PlQ0FP<PlP<PlP@Q0GFND_FAE6X2:#<X3;#=X46#@Q01P6P<P2PlPnPlPcP]PaPiPNPOPPP?PBPQPFPRPSPTPbPXP0P5MD>P<fmRmP8Q07P0PlPZF3P<10<mRpPmPlPeQ07P0Q0B10<8RqP0P2P3P4DJQ08P3Q09P4PfFGG43;X0A,2AX1KQ02Pd10<2P4P5P0Q0JPhP<P2P<PnP<P2P<PnP<PnP@P<P2D?DEEPFAE6X2:#<X3;#=X46P<P3PoPmPoPnPlP^P`P7PMPNPOPPP?PBPQPFPRPbP0P5MC5P<foRrP1PXP0PoPYF3P<P<PrPrPoPePXP0G^RsQ0BQ0CPZP3P[P4PfDRRt'1DFX0A,2AX1KPkPdQ0DP4P5P0PpC]RpPhQ0E19<mRuQ0F1B<mRvAf<m@RwQ0G'Q401FME6X2:#<X3;#=X46#@X5=,2=P0P<P8PoPmPoPnPlP^P`P7PMPNPOPPP?PBPQPFPRPbPVP0P5MD>P<PrQ02PXP0PoPYF3PsQ0BP<Q02P0P2P3P4PtFbDFX0A,2AX1KPkPdPqPpPh19<8PuP<P8PvAdw<8C}FME6X2:#<X3;#=Q01P;P<P9PmfnRwPmPoPnP_P^PLP7PMPNPOPPP?PBPQPF18D1PGP0P5MD>P<fpRvPHPWP0PmPXF3P<10<vRuPvPmPePWP010<HRpP0P1P3P4Q07P3PZP4PfDREC,T1G43;X0A,2AX1KQ04Pd10<9P3P5P0P<PwDIPh19<919<wP<P9P<PwP<PwP@P<P9D?DEFME6X2:#<X3;P<P3PvfqRqPvPrPwPlPcPJPIQ06PLP7PMPNPOPPP?PbP0P5MC5P<fsRtP1PUP0PvPGF3P<10<tRsPtPvPePUP0FSRxQ0BQ0CPWP3PXP4CO;;fDFX0A,2AX1KPgPdQ0DP4P5P010<qRyPhQ0E19<qRzQ0F1B<qR{Af<q@R|Q0G'QEoFAE6X2:#<X3;#=X46#@X5=,2=P0P<PHPrPvPrPwPmPcP]PIQ06PLP7PMPNPOPPP?PB18D9PTP0P5MD>P<frR}Q04PGP0PrPVF3P<10<}P}PrPePGP0P9P<Q04P0P9P3P4PXP3PYP4PfDRGDG43;X0A,2AX1KPjPdPpP1P5P0PuPhP<PHP<PvP<PHP<PvP<PvP@P<PHD?DEEPFAE6X2:#<Q01P:P<PkPvPqPvPrPwPlPcPJPIQ06PLP7PMPNPOPPP?Q02,8DPSP0P5MD>P<PtQ03PUP0PvPGF3PxQ02#LQ03,0<RxP0Q02P2P4PWP2PXP4P2D:ECDFX0A,2AX1KPgPd10<kP8P4P0PyPhP<PkPzP<PkP{Ad|<kGmFAE6X2:P<P3ftR|fuR{P|PtP}PwPmPaPiPCP>PJPIQ06PLP7PMPbP0P5MC5P<fwS0LP1PFP0P|PRF3P<Q0L,0<RzQ0LP|PePFP0Q0BQ0CPTP3PUP4PfFGG43;X0A,2AX1KP\PdQ0DP4P5P010<{R\PhQ0EP<P{Q0FP<P{P<P{P@Q0GFND_FAE6X2:#<X3;#=X46#@X5=,2=P0P<Q03P}PtP}PqPvPoPnPCP>PJPIQ06PLP7PMPNPO18DkPFP0P5MD>P<P{PgPSP0P}PTF3P<P\P{P}PePSP0PkP<PgP0PkP8P4PGP8PVP4P8D:GDG43;X0A,2AX1KQ0>PdPxQ02P2P0PsPhP<Q03P<PtP<Q03P<PtP<PtP@P<Q03D?DEEPFAE6Q00P<PjPtP|PtP}PqPmPoPiPCP>PJPIQ06PLP7PMPNQ04,8DPQP0P5MD>P<fvRsQ0?PRP0PtPSF3P<10<sPsPtPePRP0Q04P<Q0?P0Q04P9P3PUP9PGP3P9D:GDG43;X0A,2AX1KQ0=D[Pd10<jPHP1P5P<P|DIPh19<j19<|P<PjP<P|P<P|P@P<PjD?DEFMP<P3fxRxfyS0MPxQ0LPsP}PqP]P_P^P`PaPiPCP>PJPIPbP0P5MC5P<f{S0NP1PPP0PxP?F3P<Q0N,0<Q0NPxPePPP0Q0BQ0CPQP3PFP4PfFGG43;X0A,2AX1KQ09PdQ0DP4P5P0P<Q0MDIPhQ0EQ0M,9<Q0FP<Q0MP<Q0MP@Q0GFNFME6X2:#<X3;#=X46#@X5=,2=P0P<Q0?P{PsP{P|PtPrPwP`PaPiPCP>PJPIQ06PLP718DjP?P0P5MD>P<PxQ0=PQP0P{PFF3P<10<xR8PxP{PePQP0Q0=,0<RkP0PjPHP1PSPHPTP1PHD:EC,TjG43;X0A,2AX1KQ0<D[PdQ0>,0<Q03Q02P2PzPhP<Q0>P<Q0LP<Q0>P<Q0LP<Q0LP@P<Q0>D?DEEPFAQ00PdPkPjPHP1P8EyPhP<Q0=P<PxP<Q0=P<PxP<PxP@P<Q0=D?DEEPP<P3f|R8f}RkP8Q0NfzS0OPsP{PoPnPlPcP]P_P^P`PaPiPbP0P5MC5P<p+01@RzP1P7P0P8PMF3P<10<zPzP8PeP7P0Q0BQ0CPOP3PPP4PfFGG43;X0A,2AX1KQ07PdQ0DP4P5P0P<PkDIPhQ0E19<kQ0FP<PkP<PkP@Q0GFNFME6X2:#<X3;#=X46#@X5=,2=P0PdP<Q0<Q0?Q04P9P<Q0ODICnPhP<Q0;P<Q0NP<Q0;P<Q0NP<Q0NP@P<Q0;D?DEEPQ00PhP<Q0:19<8CaP<Q0:P<P8P<P8P@P<Q0:D?DEP<P3p+01ARPp+01BS0PPPPzf~S0QQ0OQ0MPvPrPwPmPoPnPlPcP]P_PbP0P5MC5P<p+01DRgP1PJP0PPPIF3P<10<gPgPPPePJP0Q0BQ0CPLP3P7P4PfFGG43;X0A,2AX1KPVPdQ0DP4P5P0P<Q0PDIPhQ0EQ0P,9<Q0FP<Q0PP<Q0PP@Q0GFNFME6X2:#<X3;#=X46#@X5=,2=P0PhP<Q08Q0Q,9<CaP<P[P<PzP<PzP@P<P[D?DEQ001B<P9c<ZP<PPP@P<PZD?P<P3p+01ER7p+01FR\P7Pgp+01CS0RQ0QPkP|PtP}PqPvPrPwPmPoPnPbP0P5MC5P<p+01HRyP1PaP0P7PiF3P<10<yS0SPyP7PePaP0FSS0TQ0BQ0CP>P3PJP4CO;;fDFX0A,2AX1KPSPdQ0DP4P5P010<\S0UPhQ0E19<\S0VQ0F1B<\S0WAf<\@S0XQ0G'QEoFAE6X2:#<X3;#=X46#@X5=,2=P0Q0R,B<9c<YP<PgP@P<PXD?P=P<P3Pyp+01IRuPyp+01GRpP\Q0PPPQ0LPsP{P|PtP}PqPvPrPwPbP0P5MC5P<p+01KR~P1P_P0PyP^F3P<10<~S0YP~PyPeP_P0Q0BQ0CPaP3PiP4PfFGG43;X0A,2AX1KPQPdQ0DP4P5P010<uS0DPhQ0EP<PuQ0FP<PuP<PuP@Q0GFND_FAE6X2:#<X3;#=X46#@X5=PWP6P<PUPpPyPpP\P7PPPzPsP{P|PtP}PqPvPrPwPmPbP0P5MC5P<p+01JS0GPSP^P0PpP`F3S0FP<P<Q0GQ0GPpPeP^P0G^S0EQ0B10<SS0BP0P2P3P4PiP3PCP4PfDRECDFX0A,2AX1KPFPd10<US0CP4P5P0Q0SPhP<PUP<PyP<PUP<PyP<PyP@P<PUD?DEEPFAE6X2:#<X3;#=X46PZP;P<PGP\PpP\P7PgPzQ0QP{P|PtP}PqPvPrPwPmPo18DWS0SP0P5MC5P<PuPTP`P0P\PaF3S0ZP<Q0DPuP\PeP`P0FSS0D%LWS0[10<TS0\P0PWP3P4PCP3P>P4PfDRECDFX0A,2AX1KPRPd10<GS0]PYP5P010<pRfPhP<PGP<PpP<PGP<PpP<PpP@P<PGD?DEEPFAE6X2:#<X3;Q0:P:P<PVP7P\P7PgQ0RQ0QPkP|PtP}PqPvPrPwPmPoPn18DXS0^P0P5MC5P<PyPUPaP0P7PiF3S0_Q0T%LXS0`Q0CP0PXP[P4P>P[PJP4%K[S0aDRECDFX0A,2AX1KPSPd10<VQ07Q09P0Q0UPhP<PVQ0VP<PVQ0WQ0X?d<VGmFAE6X2:Q0=P<PWPgP7PgQ0RQ0PPkP8PtP}PqPvPrPwPmPoPnPl18DYS0XP0P5MC5P<PpPGPiP0PgPCP<PfPpPgPePiP0Q0]P0PYQ08Q0<PJQ08PIQ0<Q08D:EC,TYG4GVRf'1X0A,2AX1KS0]PTD[PdP<PWPZQ0:Q0=P<P7DICnS0WPhP<PW19<7CaS0V1B<79c<WS0UP<P7P@P<PWD?S0b'1S0c'1S0d'1P<PWPgP7PgQ0RQ0PPkP8PtP}PqPvPrPwPmPoPnPlQ0XP`P0P5MD>/1fX0A,2AX1KQ0]PTPjP\P7PgQ0RQ0QPkP|PtP}PqPvPrPwPmPoPnQ0^P^P0P5MD>Q0_Q0TQ0`Q0CP0PXP[Q0;DJP>P[PJQ0;Q0aDRDFS0a'1X0A,2AX1KP0O1Q01PAP\P7PgQ0RQ0QPkP|PtP}PqPvPrPwPmPoPnQ0^P^P0P4MD>Q0a'1X0APpP\P7PgPzQ0QP{P|PtP}PqPvPrPwPmPoQ0SP0P3MC5Q0ZQ0DQ0[Q0\P0PWPZQ0:PCPZP>Q0:PZD:ECDFX0A,2AP0PyPpP\P7PPPzPsP{P|PtP}PqPvPrPwPm18DVP]P0P2MD>Q0FQ0E%LVQ0BP0PVQ07Q09PiQ07PCQ09Q07D:ECDFQ00PuPyPpP\Q0PPPQ0LPsP{P|PtP}PqPvPrPw18DGPcP5P1MD>P<P~PRP_P5PyP^P<Q0YP~PyPeP_P5PGP<PRP5PGPYQ08PaPYPiQ08PYD:GDG4GVP~Q0GPuPyPgQ0RQ0MPxQ0LPsP{P|PtP}PqPv18DTR[P0P9MC5P<p+01MRXPQPcP0Q0GP]F3P<10<XPXQ0GPePcP0PTP<PQP0PTPWPZP^PWP`PZPWD:GDG43;X0A,2AP0P~Q0GPuPyPgQ0RQ0MPxQ0LPsP{P|PtP}PqPvP[PnP3P9MD>P<p+01NR[PBPlP2P~PcP<10<[P[P~PePlP2PSP<PBP2PSPVQ07P_PVP^Q07PVD:GDG4GVQ00P<p+01OR2P?PnP1p+01LRfPlF3P<10<2P2PfPePnP1PRP<P?P1PRPGPYP]PGP_PYPGD:GDG4P2P[PXPfPyPpPkP8Q0NQ0OQ0MPxQ0LPsP{P|18DQP0Q04MC5P<p+01QR@POPmP0P[PoF3P<10<@P@P[PePmP0PQP<POP0PQPTPWPlPTPcPWPTD:GDG43;X0A,2AP0P<P@POPmP9P[PoF3P<p+01RR9,0<P9P2PePwQ02PBP<PNQ02PBPSPVPnPSPlPVPSD:GDG4Q00P<P<p+01SRlPlp+01PRhPePrPHG^P?P<PMPHP?PRPGPoPRPnPGPRD:GDPlP9P@PhPfP~Q0PPPPzQ0QPkP8Q0NQ0OQ0MPx18DOP0Q0?MC5P<p+01URdPLPqP0P9PvF3P<10<dS0?PdP9PePqP0POP<PLP0POPQPTPwPQPmPTPQD:GDG43;X0A,2AP0P<Q0?PdP9PePqQ04FSPNP<Q06Q03PNPBPSPrPBPwPSPBD:GDQ00%LMP<PIPjPMP?PRPvP?PrPRP?D:Fbp+01WS03p+01VR9Pdp+01TS04PhP2P\P7PgQ0RQ0PPPPzQ0QPkP818DLP0Q0<MC5P<p+01YRdP>P{P0P9P|F3P<10<dPdP9PeP{P0%LLS0?Q05P0PLPOPQDJP}POPqPQ%KOFGG43;X0A,2AP0Q0?P<PCQ0>Q06PNPBPtPNP}PBPND:FbQ00P<PiQ0=PIPMP?E`P|PMPtP?PMD:p+01[S0>p+01ZR9Pdp+01XS05Q04PlQ0GPuPyPpP\P7PgQ0RQ0PPP18D>P0Q08MC5P<p+01]RlP`Q0MP0P9PxF3P<10<lPlP9PeQ0MP010<`S08P0P>PLPOPsPLP{POPLD:EC,T>G43;X0A,2AP0Q08Q0<P>PLPODJQ0LQ06PsPNQ06D:Q00PxPIQ0LPMCO%KIp+01_RMp+01^RxPlp+01\Q05Q03P[PXPfP~Q0GPuPyPpP\P718D`P0PYMC5P<p+01aRYPcPkP0PxP8F3P<10<YPYPxPePkP0Q0AP0P`P>PLQ0OP>Q0MPLCORL/w>EC,T`G43;X0A,2AP0%KCPAp+01bPYp+01`RCPMQ0>P9P@PhP2P[PXPfP~Q0GPuPy18D]P0PVMC5P<p+01dR@PoPPP0PYPzF3P<10<@P@PYPePPP0Q0KP0P]PaPJPkPaP8PJPaD:EC,T]G43;X0APZPYPCPMPxP9PdPhP2P[PXPfP~Q0GPuPyPp18D_RDPZPWMC5P<p+01cRaPnPzPZPCQ0QF3RPP<P<PaPaPCPePzPZG^Rz%L_ReQ0JPZP_PiPIDJRaP8PiQ0NPICORI%KiRi'1R8'1R@'1Rc'1Rl'1PYPCPMPxP9PdPhP2P[PXPfP~Q0GPuPyPpPDQ0PPZPWQ0:MEvPPPlQ0=PzPcPjPeP@PHPaP8P1PIPiP5P0FYFYFYCWWDX?LP5P0O2n2001000000121000000W?W>P5P0O2n2001000000121000000W>W=P5P0O2n2001000000121000000W=W<P5P0O2n2001000000121000000W<W;P5P0O2n2001000000121000000W;W6P5P0O2n2001000000121000000W6XpAP5P0O2n2001000000121100000P\P7PgQ0RQ0QPkP|PtP}PqPvPrPwPmPoPnQ0^P0P4MC5Q0a'1X0A,2AeWEX1KG~Q0WQ0dPHQ0VQ0cP1Q0UQ0bP5P0FYFYCWCWCWCWWCW:P5P0O2n2001000000121000000W:W9P5P0O2n2001000000121000000W9W8P5P0O2n2001000000121000000W8W6P5P0O2n2001000000121000000W6Xo:P5P0O2n2001000000121100000W6Xn;P5P0O2n2001000000121100000W6Xm6P5P0O2n2001000000121100000W6Xl=P5P0O2n2001000000121100000P<P3P_P]P_P^P`P>PJP?PBPQPFPRPSPTPUPGPVPbP0P5MC5Q0H'1X0A,2AX1KP1Q0IE6X2:#<X3;#=X46#@X5=,2=R=eP=eW@W7L00UUUUUUUUUUUXO:Xk;XT6XR6WSWPWAXiEXhEXgEXfEXYEXXEXaEX`EX_EX^EX]EX\EX[EXZEXNEXMEXLEXKEXJEXIEXHEXGEXWEXVEXeEXdEXcEXjEXQEXbEWUWFWqg0244eWBo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rop_novalign (dx sx : Z) : Prop := (dx mod 32 = 0 /\ sx mod 32 = 0) \/ (sx = 0 /\ - 31 <= dx <= 31).
Definition pixRasterop_po_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd ps : Z) (vd vs : pixv) (cvd cvs : cmapv) (dx dy dw dh op sx sy rcs : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> s32 a1 dx -> s32 a2 dy -> s32 a3 dw -> s32 a4 dh -> a5 = Z_to_bv 64 op -> a6 = Z_to_bv 64 ps -> s32 a7 sx ->
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 sy)] -> - 2^31 <= sy < 2^31 ->
  pix1c (rt_live RT Σ) m pd vd cvd -> 1 <= dw <= 20064 -> 1 <= dh <= 20064 -> - 2^16 <= dx <= 2^16 -> - 2^16 <= dy <= 2^16 ->
  ((op = PIX_CLR /\ ps = 0)
   \/ (In op PO_OPS /\ ps <> pd /\ pix1rc (rt_live RT Σ) m ps vs cvs rcs /\ 1 <= rcs <= 2 /\ p_data vs <> p_data vd
       /\ - 2^16 <= sx <= 2^16 /\ - 2^16 <= sy <= 2^16 /\ rop_novalign dx sx /\ List.NoDup (pix_chunks pd vd cvd ++ pix_chunks ps vs cvs))) ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 5 0 8 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRasterop_po m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data vd, p_data vd + rsize vd)] m m'
          /\ pix1c (rt_live RT Σ') m' pd vd cvd /\ (ps <> 0 -> pix1rc (rt_live RT Σ') m' ps vs cvs rcs)) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 8 <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition selCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sy sx : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sy -> a1 = Z_to_bv 64 sx -> a2 = Z_to_bv 64 0 -> 1 <= sy <= 30 -> 1 <= sx <= 30 ->
  uctx m sp s0 ras -> po_rows e_selCreate ra ras ->
  (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 (2 + sy) 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selCreate m)))
    (fun c => exists (Σ' : rts RT) (sel : Z) (sv : selv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sel) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ sel_obj (rt_live RT Σ') m' sel sv /\ s_sy sv = sy /\ s_sx sv = sx /\ s_cy sv = 0 /\ s_cx sv = 0
          /\ s_rows sv = repeat (repeat 0 (Z.to_nat sx)) (Z.to_nat sy)) c
       /\ rt_live RT Σ' = sel_new_live sel sv (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition list_upd2 (rows : list (list Z)) (i j v : Z) : list (list Z) :=
  map (fun ir => if fst ir =? i then map (fun je => if fst je =? j then v else snd je) (combine (map Z.of_nat (seq 0 (length (snd ir)))) (snd ir)) else snd ir)
      (combine (map Z.of_nat (seq 0 (length rows))) rows).
Definition selSetElement_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sel i j ty : Z) (sv : selv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sel -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 j -> a3 = Z_to_bv 64 ty -> sel_obj (rt_live RT Σ) m sel sv ->
  0 <= i < s_sy sv -> 0 <= j < s_sx sv -> In ty [0; 1; 2] ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selSetElement m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(nth (Z.to_nat i) (s_rowp sv) 0 + 4 * j, nth (Z.to_nat i) (s_rowp sv) 0 + 4 * j + 4)] m m'
          /\ sel_obj (rt_live RT Σ') m' sel (mkSelv (s_sy sv) (s_sx sv) (s_cy sv) (s_cx sv) (s_data sv) (s_rowp sv) (list_upd2 (s_rows sv) i j ty))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (psel sel : Z) (sv : selv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 psel -> rw_cells asegs m psel [C8 (Z_to_bv 64 sel)] ->
  (sel = 0 \/ sel_obj (rt_live RT Σ) m sel sv) ->
  optrL RT (if sel =? 0 then rt_live RT Σ else sel_destroy_live sel sv (rt_live RT Σ)) Σ m psel 8 ->
  uctx m sp s0 ras -> po_rows e_selDestroy ra ras ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(psel, psel + 8)] m m' /\ rw_cells asegs m' psel [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = (if sel =? 0 then rt_live RT Σ else sel_destroy_live sel sv (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selCreateBrick_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (h w cy cx : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 h -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 cy -> a3 = Z_to_bv 64 cx -> a4 = Z_to_bv 64 SEL_HIT ->
  ((h = 1 /\ w = 6 /\ cy = 0 /\ cx = 3) \/ (h = 4 /\ w = 1 /\ cy = 2 /\ cx = 0)) ->
  uctx m sp s0 ras -> po_rows e_selCreateBrick ra ras ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 (2 + h) 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selCreateBrick m)))
    (fun c => exists (Σ' : rts RT) (sel : Z) (sv : selv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sel) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ sel_obj (rt_live RT Σ') m' sel sv /\ (h = 1 -> brick_h6 sv) /\ (h = 4 -> brick_v4 sv)) c
       /\ rt_live RT Σ' = sel_new_live sel sv (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selCreateComb_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (f1 f2 dir : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 f1 -> a1 = Z_to_bv 64 f2 -> a2 = Z_to_bv 64 dir ->
  ((f1 = 6 /\ f2 = 5 /\ dir = L_HORIZ) \/ (f1 = 4 /\ f2 = 2 /\ dir = L_VERT)) ->
  uctx m sp s0 ras -> po_rows e_selCreateComb ra ras ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 0 10 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selCreateComb m)))
    (fun c => exists (Σ' : rts RT) (sel : Z) (sv : selv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sel) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ sel_obj (rt_live RT Σ') m' sel sv /\ (dir = L_HORIZ -> comb_h30 sv) /\ (dir = L_VERT -> comb_v8 sv)) c
       /\ rt_live RT Σ' = sel_new_live sel sv (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition selectComposableSels_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (size dir p1 p2 : Z) (x1 x2 : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 size -> a1 = Z_to_bv 64 dir -> a2 = Z_to_bv 64 p1 -> a3 = Z_to_bv 64 p2 ->
  ((size = 30 /\ dir = L_HORIZ) \/ (size = 8 /\ dir = L_VERT)) ->
  optrF RT Σ m p1 8 -> optrF RT Σ m p2 8 -> (p1 + 8 <= p2 \/ p2 + 8 <= p1) -> rw_cells asegs m p1 [C8 x1] -> rw_cells asegs m p2 [C8 x2] ->
  uctx m sp s0 ras -> po_rows e_selectComposableSels ra ras ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 2 16 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selectComposableSels m)))
    (fun c => exists (Σ' : rts RT) (sel1 sel2 : Z) (sv1 sv2 : selv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(p1, p1 + 8); (p2, p2 + 8)] m m'
          /\ rw_cells asegs m' p1 [C8 (Z_to_bv 64 sel1)] /\ rw_cells asegs m' p2 [C8 (Z_to_bv 64 sel2)]
          /\ sel_obj (rt_live RT Σ') m' sel1 sv1 /\ sel_obj (rt_live RT Σ') m' sel2 sv2
          /\ (size = 30 -> brick_h6 sv1 /\ comb_h30 sv2) /\ (size = 8 -> brick_v4 sv1 /\ comb_v8 sv2)
          /\ List.NoDup (sel_chunks sel1 sv1 ++ sel_chunks sel2 sv2)) c
       /\ rt_live RT Σ' = sel_new_live sel2 sv2 (sel_new_live sel1 sv1 (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixAddBorderGeneral32_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (rcs : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 32 -> a2 = Z_to_bv 64 32 -> a3 = Z_to_bv 64 32 -> a4 = Z_to_bv 64 32 -> a5 = Z_to_bv 64 0 ->
  pix1rc (rt_live RT Σ) m pixs vs cvs rcs -> 1 <= rcs <= 2 ->
  uctx m sp s0 ras -> po_rows e_pixAddBorderGeneral_po ra ras ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 9 4 RC1 -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddBorderGeneral_po m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1rc (rt_live RT Σ') m' pixs vs cvs rcs
          /\ (pixd = 0 <-> (20000 < p_w vs + 64 \/ 20000 < p_h vs + 64))
          /\ (pixd <> 0 -> pix1c (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs + 64 /\ p_h vd = p_h vs + 64
                          /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
                          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs))) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_copy_live pixd vd cvd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - RC1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixAddBorder32_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (rcs : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 32 -> a2 = Z_to_bv 64 0 ->
  pix1rc (rt_live RT Σ) m pixs vs cvs rcs -> 1 <= rcs <= 2 ->
  uctx m sp s0 ras -> po_rows e_pixAddBorderGeneral_po ra ras ->   (* [comment removed for export] *)
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 9 4 RC1 -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixAddBorder m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1rc (rt_live RT Σ') m' pixs vs cvs rcs
          /\ (pixd = 0 <-> (20000 < p_w vs + 64 \/ 20000 < p_h vs + 64))
          /\ (pixd <> 0 -> pix1c (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs + 64 /\ p_h vd = p_h vs + 64
                          /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
                          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs))) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_copy_live pixd vd cvd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - RC1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixRemoveBorder32_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 32 -> (entry = e_pixRemoveBorderGeneral -> a2 = Z_to_bv 64 32 /\ a3 = Z_to_bv 64 32 /\ a4 = Z_to_bv 64 32) ->
  pix1c (rt_live RT Σ) m pixs vs cvs -> 65 <= p_w vs -> 65 <= p_h vs ->
  uctx m sp s0 ras -> po_rows e_pixRemoveBorderGeneral ra ras ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 9 4 RC1 -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pixd <> 0
          /\ pix1c (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs - 64 /\ p_h vd = p_h vs - 64
          /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = pix_copy_live pixd vd cvd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - RC1 <= rt_credit RT Σ').
Definition pixRemoveBorder_cps : Prop := pixRemoveBorder32_cps e_pixRemoveBorder.
Definition pixRemoveBorderGeneral_cps : Prop := pixRemoveBorder32_cps e_pixRemoveBorderGeneral.

(* [comment removed for export] *)
Definition cmap_rm_live (cm : Z) (cv : cmapv) (live : list (Z * Z)) : list (Z * Z) :=
  if cm =? 0 then live else live_remove cm (live_remove (c_arr cv) live).
Definition cmap_add_live (cm : Z) (cv : cmapv) (live : list (Z * Z)) : list (Z * Z) :=
  if cm =? 0 then live else (c_arr cv, 4 * c_nalloc cv) :: (cm, 24) :: live.
Definition pixCopy_given_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs : Z) (vd vs : pixv) (cvd cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs -> pixd <> pixs ->
  pix1c (rt_live RT Σ) m pixd vd cvd -> pix1c (rt_live RT Σ) m pixs vs cvs -> p_w vs = p_w vd -> p_h vs = p_h vd ->
  List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs) ->
  uctx m sp s0 ras -> po_rows e_pixCopy_po ra ras ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 3 2 64 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopy_po m)))
    (fun c => exists (Σ' : rts RT) (vd' : pixv) (cvd' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (cmap_rm_live (p_cmap vd) cvd (rt_live RT Σ)) Σ sp [(pixd, pixd + 64); (p_data vd, p_data vd + rsize vd)] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pix1c (rt_live RT Σ') m' pixd vd' cvd'
          /\ p_w vd' = p_w vd /\ p_h vd' = p_h vd /\ p_wpl vd' = p_wpl vd /\ p_data vd' = p_data vd
          /\ (p_cmap vs = 0 -> p_cmap vd' = 0) /\ (p_cmap vd' <> 0 -> c_n cvd' = c_n cvs /\ c_nalloc cvd' = c_nalloc cvs /\ c_depth cvd' = c_depth cvs)
          /\ List.NoDup (pix_chunks pixd vd' cvd' ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = cmap_add_live (p_cmap vd') cvd' (cmap_rm_live (p_cmap vd) cvd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 64 <= rt_credit RT Σ').
Definition pixCopy_same_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 pix -> pix1c (rt_live RT Σ) m pix v cv ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCopy_po m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m' /\ pix1c (rt_live RT Σ') m' pix v cv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition morph_new_cps (entry : Z) (selp : selv -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs sel : Z) (vs : pixv) (cvs : cmapv) (sv : selv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 sel ->
  pix1c (rt_live RT Σ) m pixs vs cvs -> sel_obj (rt_live RT Σ) m sel sv -> selp sv ->
  uctx m sp s0 ras -> po_rows entry ra ras ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 8 4 HMT_COST -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(pixs + 20, pixs + 24)] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pixd <> 0
          /\ pix1c (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs
          /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = pix_copy_live pixd vd cvd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - HMT_COST <= rt_credit RT Σ').
Definition pixDilate_cps : Prop := morph_new_cps e_pixDilate (fun sv => brick_h6 sv \/ comb_h30 sv \/ brick_v4 sv \/ comb_v8 sv).
Definition pixHMT_cps : Prop := morph_new_cps e_pixHMT (fun sv => exists k, 1 <= k <= 4 /\ tsel_shape k sv).
(* [comment removed for export] *)
Definition morph_null_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd sel : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 sel ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 3 0 3 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 3 <= rt_credit RT Σ').
Definition pixDilate_null_cps : Prop := morph_null_cps e_pixDilate.
Definition pixErode_null_cps : Prop := morph_null_cps e_pixErode.

(* [comment removed for export] *)
Definition pixErode_given_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixd pixs sel : Z) (vd vs : pixv) (cvd cvs : cmapv) (sv : selv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixd -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 sel -> pixd <> pixs ->
  pix1c (rt_live RT Σ) m pixd vd cvd -> pix1c (rt_live RT Σ) m pixs vs cvs -> p_w vd = p_w vs -> p_h vd = p_h vs ->
  List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs) ->
  sel_obj (rt_live RT Σ) m sel sv -> (brick_h6 sv \/ comb_h30 sv \/ brick_v4 sv \/ comb_v8 sv) ->
  uctx m sp s0 ras -> po_rows e_pixErode ra ras ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 8 0 (2^8) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixErode m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data vd, p_data vd + rsize vd); (pixs + 20, pixs + 24)] m m'
          /\ pix1c (rt_live RT Σ') m' pixd vd cvd /\ pix1c (rt_live RT Σ') m' pixs vs cvs) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2^8 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCloseSafeCompBrick_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix1 hs vs : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix1 -> a1 = Z_to_bv 64 pix1 -> a2 = Z_to_bv 64 hs -> a3 = Z_to_bv 64 vs -> ((hs = 1 /\ vs = 8) \/ (hs = 30 /\ vs = 1)) ->
  pix1c (rt_live RT Σ) m pix1 v cv ->
  uctx m sp s0 ras -> po_rows e_pixCloseSafeCompBrick ra ras ->
  lenv RT Σ m sp lo (LSTK 13) -> lres RT Σ 11 40 CSC_COST -> sec_bytes (rt_live RT Σ) + CSC_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCloseSafeCompBrick m)))
    (fun c => exists (Σ' : rts RT) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix1) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (cmap_rm_live (p_cmap v) cv (rt_live RT Σ)) Σ sp [(pix1, pix1 + 64); (p_data v, p_data v + rsize v)] m m'
          /\ pix1c (rt_live RT Σ') m' pix1 v' cv'
          /\ p_w v' = p_w v /\ p_h v' = p_h v /\ p_wpl v' = p_wpl v /\ p_data v' = p_data v
          /\ (p_cmap v = 0 -> p_cmap v' = 0) /\ (p_cmap v' <> 0 -> c_n cv' = c_n cv /\ c_nalloc cv' = c_nalloc cv /\ c_depth cv' = c_depth cv)
          /\ ((20000 < p_w v + 64 \/ 20000 < p_h v + 64) -> v' = v /\ cv' = cv)) c
       /\ rt_live RT Σ' = (if (20000 <? p_w v + 64) || (20000 <? p_h v + 64) then rt_live RT Σ
                           else cmap_add_live (p_cmap v') cv' (cmap_rm_live (p_cmap v) cv (rt_live RT Σ)))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - CSC_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition selCreateFromString_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (k : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 (A_TSEL k) -> a1 = Z_to_bv 64 5 -> a2 = Z_to_bv 64 6 -> a3 = Z_to_bv 64 0 -> 1 <= k <= 4 ->
  uctx m sp s0 ras -> po_rows e_selCreateFromString ra ras ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ 0 7 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_selCreateFromString m)))
    (fun c => exists (Σ' : rts RT) (sel : Z) (sv : selv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sel) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ sel_obj (rt_live RT Σ') m' sel sv /\ tsel_shape k sv) c
       /\ rt_live RT Σ' = sel_new_live sel sv (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition sarrayCreate0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 0 ->
  uctx m sp s0 ras -> po_rows e_sarrayCreate ra ras -> ras <> nil ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 2 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sarrayCreate m)))
    (fun c => exists (Σ' : rts RT) (sa arr : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 sa) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m' /\ sarray_obj (rt_live RT Σ') m' sa (mkSav 0 arr [])
          /\ rw_cells asegs m' (sa + 8) [C4 (Z_to_bv 64 1)] (* [comment removed for export] *)) c
       /\ rt_live RT Σ' = (arr, 400) :: (sa, 24) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sarraySplitSeq_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sa arr : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 A_SEQ_TEXT -> a2 = Z_to_bv 64 A_SEPS_PLUS -> sarray_obj (rt_live RT Σ) m sa (mkSav 0 arr []) ->
  rw_cells asegs m (sa + 8) [C4 (Z_to_bv 64 1)] ->
  uctx m sp s0 ras -> po_rows e_sarraySplitString ra ras ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 1 3 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sarraySplitString m)))
    (fun c => exists (Σ' : rts RT) (p1 p2 : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(sa, sa + 24); (arr, arr + 16)] m m'
          /\ sarray_obj (rt_live RT Σ') m' sa (mkSav 2 arr [(p1, RAWOP1); (p2, RAWOP2)])
          /\ rw_cells asegs m' (sa + 8) [C4 (Z_to_bv 64 1)]) c
       /\ rt_live RT Σ' = (p2, 7) :: (p1, 6) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition sarrayAddString_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sa p : Z) (av : sav) (bs : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  sarray_obj (rt_live RT Σ) m sa av -> sa_n av < 50 ->
  cstr (rt_live RT Σ) m p bs -> ~ In p (sarray_chunks sa av) ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sarrayAddString m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp [(sa + 4, sa + 8); (sa_arr av + 8 * sa_n av, sa_arr av + 8 * sa_n av + 8)] m m'
          /\ sarray_obj (rt_live RT Σ') m' sa (mkSav (sa_n av + 1) (sa_arr av) (sa_strs av ++ [(p, bs)]))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sarrayGetCount_cps : Prop :=
  getter_cps e_sarrayGetCount (fun live m p => exists av, sarray_obj live m p av) (fun m p rv => exists av L, sarray_obj L m p av /\ rv = sa_n av).
Definition sarrayGetString_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sa i : Z) (av : sav),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 0 (* [comment removed for export] *) -> sarray_obj (rt_live RT Σ) m sa av -> 0 <= i < sa_n av ->
  lenv RT Σ m sp lo (LSTK 1) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sarrayGetString m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (fst (nth (Z.to_nat i) (sa_strs av) (0, [])))) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m' /\ sarray_obj (rt_live RT Σ') m' sa av) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition stringRemoveWS_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (src : Z) (raw : list Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 src -> a1 = Z_to_bv 64 A_SEPS_WS -> cstr (rt_live RT Σ) m src raw -> (raw = RAWOP1 \/ raw = RAWOP2) ->
  uctx m sp s0 ras -> po_rows e_stringRemoveChars ra ras ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 1 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stringRemoveChars m)))
    (fun c => exists (Σ' : rts RT) (dst : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 dst) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ cstr (rt_live RT Σ') m' dst (if list_eq_dec Z.eq_dec raw RAWOP1 then OP1 else OP2) /\ cstr (rt_live RT Σ') m' src raw) c
       /\ rt_live RT Σ' = (dst, Z.of_nat (length raw) + 1) :: rt_live RT Σ    (* [comment removed for export] *)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition morphSequenceVerify_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (sa : Z) (av : sav) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 sa -> sarray_obj (rt_live RT Σ) m sa av -> map snd (sa_strs av) = [RAWOP1; RAWOP2] ->
  uctx m sp s0 ras -> po_rows e_morphSequenceVerify ra ras ->
  lenv RT Σ m sp lo (LSTK 6) -> lres RT Σ 2 1 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_morphSequenceVerify m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m' /\ sarray_obj (rt_live RT Σ') m' sa av) c
       /\ rt_live RT Σ' = rt_live RT Σ    (* [comment removed for export] *)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition sarray_destroy_live (sa : Z) (av : sav) (live : list (Z * Z)) : list (Z * Z) :=
  live_remove sa (live_remove (sa_arr av) (fold_left (fun l s => live_remove (fst s) l) (sa_strs av) live)).
Definition sarrayDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (psa sa : Z) (av : sav) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 psa -> rw_cells asegs m psa [C8 (Z_to_bv 64 sa)] -> sarray_obj (rt_live RT Σ) m sa av ->
  sa_n av = 2 -> rw_cells asegs m (sa + 8) [C4 (Z_to_bv 64 1)] ->
  optrL RT (sarray_destroy_live sa av (rt_live RT Σ)) Σ m psa 8 -> uctx m sp s0 ras -> po_rows e_sarrayDestroy ra ras ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sarrayDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(psa, psa + 8)] m m' /\ rw_cells asegs m' psa [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = sarray_destroy_live sa av (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixMorphCompSequence_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 A_SEQ_TEXT -> a2 = Z_to_bv 64 0 -> pix1c (rt_live RT Σ) m pixs vs cvs ->
  uctx m sp s0 ras -> po_rows e_pixMorphCompSequence ra ras ->
  lenv RT Σ m sp lo (LSTK 15) -> lres RT Σ 13 48 MCS_COST -> sec_bytes (rt_live RT Σ) + MCS_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixMorphCompSequence m)))
    (fun c => exists (Σ' : rts RT) (pix1 : Z) (v1 : pixv) (cv1 : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix1) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pix1 <> 0 /\ pix1c (rt_live RT Σ') m' pix1 v1 cv1
          /\ p_w v1 = p_w vs /\ p_h v1 = p_h vs /\ (p_cmap vs = 0 -> p_cmap v1 = 0)
          /\ (p_cmap v1 <> 0 -> c_n cv1 = c_n cvs /\ c_nalloc cv1 = c_nalloc cvs /\ c_depth cv1 = c_depth cvs)
          /\ List.NoDup (pix_chunks pix1 v1 cv1 ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = pix_copy_live pix1 v1 cv1 (rt_live RT Σ)
            (* [comment removed for export] *)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - MCS_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixRotate90_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs dir : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 dir -> (dir = 1 \/ dir = -1) -> pix1c (rt_live RT Σ) m pixs vs cvs ->
  uctx m sp s0 ras -> po_rows e_pixRotate90 ra ras ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 6 4 RC1 -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRotate90 m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pixd <> 0 /\ pix1c (rt_live RT Σ') m' pixd vd cvd
          /\ p_w vd = p_h vs /\ p_h vd = p_w vs /\ (p_cmap vs = 0 -> p_cmap vd = 0)
          /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = pix_copy_live pixd vd cvd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - RC1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition rasteropHipLow_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (data pixh wpl shift : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 data -> s32 a1 pixh -> a2 = Z_to_bv 64 1 -> s32 a3 wpl -> a4 = Z_to_bv 64 0 -> s32 a5 pixh -> s32 a6 shift ->
  1 <= wpl <= 626 -> 1 <= pixh <= 20000 -> 1 <= shift <= 31 ->
  own_live (rt_live RT Σ) data (4 * wpl * pixh) -> data mod 16 = 0 ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rasteropHipLow m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(data, data + 4 * wpl * pixh)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition flip_inplace_cps (entry : Z) (frames : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 pix -> pix1c (rt_live RT Σ) m pix v cv ->
  uctx m sp s0 ras -> po_rows entry ra ras ->
  lenv RT Σ m sp lo (LSTK 5) -> lres RT Σ frames 3 4 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p_data v, p_data v + rsize v)] m m' /\ pix1c (rt_live RT Σ') m' pix v cv) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 4 <= rt_credit RT Σ').
Definition pixFlipLR_cps : Prop := flip_inplace_cps e_pixFlipLR 3.
Definition pixFlipTB_cps : Prop := flip_inplace_cps e_pixFlipTB 2.

(* [comment removed for export] *)
Definition rot_new_cps (entry : Z) (argok : Z -> Prop) (swap : Z -> bool) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs q : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  (entry = e_pixRotate180 -> a0 = Z_to_bv 64 0 /\ a1 = Z_to_bv 64 pixs) -> (entry = e_pixRotateOrth -> a0 = Z_to_bv 64 pixs /\ a1 = Z_to_bv 64 q) ->
  argok q -> pix1c (rt_live RT Σ) m pixs vs cvs ->
  uctx m sp s0 ras -> po_rows entry ra ras ->
  lenv RT Σ m sp lo (LSTK 11) -> lres RT Σ 7 6 (RC1 + 16) -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs /\ pixd <> 0 /\ pix1c (rt_live RT Σ') m' pixd vd cvd
          /\ (if swap q then p_w vd = p_h vs /\ p_h vd = p_w vs else p_w vd = p_w vs /\ p_h vd = p_h vs)
          /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
          /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)) c
       /\ rt_live RT Σ' = pix_copy_live pixd vd cvd (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RC1 + 16) <= rt_credit RT Σ').
Definition pixRotate180_cps : Prop := rot_new_cps e_pixRotate180 (fun _ => True) (fun _ => false).
Definition pixRotateOrth_cps : Prop := rot_new_cps e_pixRotateOrth (fun q => 1 <= q <= 3) (fun q => negb (q =? 2)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rb2_fp (pixs : Z) (vs : pixv) : list (Z * Z) := if pixs =? 0 then [] else [(p_data vs, p_data vs + rsize vs)].

(* [comment removed for export] *)
Definition pixReduceRankBinary2_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs tab : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 tab -> (pixs = 0 \/ pix1c (rt_live RT Σ) m pixs vs cvs) ->
  chunk (rt_live RT Σ) tab 256 -> (pixs <> 0 -> ~ In tab (pix_chunks pixs vs cvs)) ->
  uctx m sp s0 ras -> po_rows e_pixReduceRankBinary2 ra ras ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 6 2 RC1 -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixReduceRankBinary2 m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp (rb2_fp pixs vs) m m'   (* [comment removed for export] *)
          /\ (pixs <> 0 -> pix1c (rt_live RT Σ') m' pixs vs cvs)
          /\ (pixd = 0 <-> (pixs = 0 \/ p_h vs <= 1 \/ p_w vs <= 1))
          /\ (pixd <> 0 -> pix1c (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_w vd = p_w vs / 2 /\ p_h vd = p_h vs / 2
                          /\ List.NoDup (pix_chunks pixd vd (mkCmapv 0 0 0 0) ++ pix_chunks pixs vs cvs))) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - RC1 <= rt_credit RT Σ').   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixReduceRankBinaryCascade_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 0 -> pix1c (rt_live RT Σ) m pixs vs cvs ->
  uctx m sp s0 ras -> po_rows e_pixReduceRankBinaryCascade ra ras ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 7 5 CASC_COST -> sec_bytes (rt_live RT Σ) + 0x6000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixReduceRankBinaryCascade m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [(p_data vs, p_data vs + rsize vs)] m m'
          /\ pix1c (rt_live RT Σ') m' pixs vs cvs
          /\ (pixd = 0 <-> (p_h vs <= 3 \/ p_w vs <= 3))
          /\ (pixd <> 0 -> pix1c (rt_live RT Σ') m' pixd vd (mkCmapv 0 0 0 0) /\ p_cmap vd = 0 /\ p_w vd = p_w vs / 2 / 2 /\ p_h vd = p_h vs / 2 / 2
                          /\ List.NoDup (pix_chunks pixd vd (mkCmapv 0 0 0 0) ++ pix_chunks pixs vs cvs))) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_new_live pixd vd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - CASC_COST <= rt_credit RT Σ').   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixCountPixels_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix pcount : Z) (v : pixv) (cv : cmapv) (x : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 pcount -> a2 = Z_to_bv 64 0 -> (pix = 0 \/ pix1c (rt_live RT Σ) m pix v cv) ->
  optrF RT Σ m pcount 4 -> rw_cells asegs m pcount [C4 x] ->
  uctx m sp s0 ras -> po_rows e_pixCountPixels ra ras ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 3 1 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCountPixels m)))
    (fun c => exists (Σ' : rts RT) (rv cnt : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pcount, pcount + 4)] m m'
          /\ (pix = 0 -> rv = 1 /\ rw_cells asegs m' pcount [C4 (Z_to_bv 64 0)])
          /\ (pix <> 0 -> rv = 0 /\ rw_cells asegs m' pcount [C4 (Z_to_bv 64 cnt)] /\ 0 <= cnt <= 32 * (p_wpl v * p_h v) /\ pix1c (rt_live RT Σ') m' pix v cv)) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixUpDownDetect_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs pconf : Z) (vs : pixv) (cvs : cmapv) (x : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 pconf -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 0 ->
  pix1c (rt_live RT Σ) m pixs vs cvs -> optrF RT Σ m pconf 4 -> rw_cells asegs m pconf [C4 x] ->
  uctx m sp s0 ras -> po_rows e_pixUpDownDetect ra ras ->
  lenv RT Σ m sp lo (LSTK 17) -> lres RT Σ 14 80 UDD_COST -> sec_bytes (rt_live RT Σ) + UDD_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixUpDownDetect m)))
    (fun c => exists (Σ' : rts RT) (confbits : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pconf, pconf + 4); (pixs + 20, pixs + 24)] m m'
          /\ rw_cells asegs m' pconf [C4 confbits] /\ pix1c (rt_live RT Σ') m' pixs vs cvs) c
       /\ rt_live RT Σ' = rt_live RT Σ     (* [comment removed for export] *)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - UDD_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition makeOrientDecision_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (porient : Z) (upbits leftbits : Z) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  reg_get F r_fa0 = fs32 upbits -> reg_get F r_fa1 = fs32 leftbits -> reg_get F r_fa2 = fs32 F_1_0 -> reg_get F r_fa3 = fs32 F_1_0 ->
  a0 = Z_to_bv 64 porient -> a1 = Z_to_bv 64 0 -> optrF RT Σ m porient 4 -> rw_cells asegs m porient [C4 x] ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeOrientDecision m)))
    (fun c => exists (Σ' : rts RT) (o : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(porient, porient + 4)] m m'
          /\ rw_cells asegs m' porient [C4 (Z_to_bv 64 o)] /\ 0 <= o <= ORIENT_MAX) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixDebugFlipDetect_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a3 = Z_to_bv 64 0 ->
  lenv RT Σ m sp lo (LSTK 2) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDebugFlipDetect m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixOrientCorrect_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs pup pleft prot : Z) (vs : pixv) (cvs : cmapv) (x1 x2 x3 : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> reg_get F r_fa0 = fs32 F_1_0 -> reg_get F r_fa1 = fs32 F_1_0 ->
  a1 = Z_to_bv 64 pup -> a2 = Z_to_bv 64 pleft -> a3 = Z_to_bv 64 prot -> a4 = Z_to_bv 64 0 ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_data vs <> 0 ->
  optrF RT Σ m pup 4 -> optrF RT Σ m pleft 4 -> optrF RT Σ m prot 4 -> List.NoDup [pup; pleft; prot] ->
  rw_cells asegs m pup [C4 x1] -> rw_cells asegs m pleft [C4 x2] -> rw_cells asegs m prot [C4 x3] ->
  uctx m sp s0 ras -> po_rows e_pixOrientCorrect ra ras ->
  lenv RT Σ m sp lo (LSTK 19) -> lres RT Σ 15 88 OC_COST -> sec_bytes (rt_live RT Σ) + OC_SECB <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixOrientCorrect m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv) (ub lb : word) (rot : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (rt_live RT Σ) Σ sp [(pup, pup + 4); (pleft, pleft + 4); (prot, prot + 4); (pixs + 20, pixs + 24); (p_data vs, p_data vs + rsize vs)] m m'
          /\ pix_obj (rt_live RT Σ') m' pixs vs cvs
          /\ (p_d vs <> 1 -> pixd = 0 /\ rw_cells asegs m' pup [C4 x1] /\ rw_cells asegs m' pleft [C4 x2] /\ rw_cells asegs m' prot [C4 x3])
          /\ (p_d vs = 1 -> pixd <> 0 /\ pix1c (rt_live RT Σ') m' pixd vd cvd
                           /\ ((p_w vd = p_w vs /\ p_h vd = p_h vs) \/ (p_w vd = p_h vs /\ p_h vd = p_w vs))
                           /\ (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs)
                           /\ List.NoDup (pix_chunks pixd vd cvd ++ pix_chunks pixs vs cvs)
                           /\ rw_cells asegs m' pup [C4 ub] /\ rw_cells asegs m' pleft [C4 lb] /\ rw_cells asegs m' prot [C4 (Z_to_bv 64 rot)]
                           /\ In rot [0; 90; 180; 270])) c
       /\ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ else pix_copy_live pixd vd cvd (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - OC_COST <= rt_credit RT Σ').
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition po_fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 TP_A -> bv_unsigned ra = RA_TOP ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n /\ d mod 8 = 0) \/ bs = []) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + PO_FUZZ_LIVE <= LIVE_MAX -> PO_FUZZ_COST <= rt_credit RT Σ ->
  sec_bytes (rt_live RT Σ) + PO_FUZZ_SECB <= SEC_BYTES ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_po_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - PO_FUZZ_COST <= rt_credit RT Σ').

End PoIface.

(* [comment removed for export] *)
Definition g_MORPH_BC : Z := 0x216160.   (* [comment removed for export] *)
Definition LIB_PO (m : mem) : Prop := rw_cells asegs m g_MORPH_BC [C4 (Z_to_bv 64 1)].
(* [comment removed for export] *)
