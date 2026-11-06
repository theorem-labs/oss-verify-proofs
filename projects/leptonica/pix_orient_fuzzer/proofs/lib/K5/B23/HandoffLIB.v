(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface D_libiface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import HandoffKit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import HandoffImage HandoffCLX RT_state RT_rep RT_init.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_HandoffLIB () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6allowAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23:HandoffLIB9hs_lib_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib2K53B23:HandoffCLX;hs_rw_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib2K53B23:HandoffCLX7hs_wordC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K52AG:HandoffKit2mHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:D_libiface5LIB_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53B23:HandoffCLX;hi_rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53B238RT_iface8e_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6e_freeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237RT_init6sigma0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_state9rtA_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B237RT_init8ri_allowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B23:HandoffLIB:hs_lib_genC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

(* [comment removed for export] *)
Definition hs_lib_ok (ch : acs) : bool :=
  (hs_rw_cells ch 0x22a5e0 [C4 (Z_to_bv 64 3)] && hs_rw_cells ch 0x22a660 [C8 (Z_to_bv 64 e_malloc)]
   && hs_rw_cells ch 0x22a680 [C8 (Z_to_bv 64 e_free)] && hs_rw_cells ch 0x22a600 [C8 (hs_word ch 0x22a600 8)]
   && hs_rw_cells ch 0x22a6e0 [C4 (Z_to_bv 64 1)] (* [comment removed for export] *))%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

(* [comment removed for export] *)
Theorem hs_lib_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_lib_ok ch = true -> LIB_A (mH FULL model A').
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffLIB ()) ["Lib"] "h02HTh12A'h22H1h32H2h42H3h52H4h62H5h73HA'h81hh91pp;2p;1p;3p;4p;Dg0000j2TTg000Pj1STg0010j1RTg001Nj1OTg0021j3NTg0034j2FTg0045j1KTg0055j10Tg005Zj18Tg0068j16Tg006]j2DTg007Cj1GTg008;j1MTg008[j3?Tg009]j1CTg00:Uj2ETg00;3j13Tg00;Rj3LTg00<Pj3BTg00=3R0j27Tg00=Nj3<Tg00>Fj1=Tg00?Bj4@Tg00@;j2JTg00@UlD>Tg00AWj4ATg00B2j4ITg00BLj3PTg00Bfj3QTf0R1#0#0p=4%01#0#0#0p=5g00CFg00Cf7P1p=1%61#0p=2%61#0#6#0p=:%01#6p=9%61#6p=Hg00DFR2f1R3;Q1p=;g00E>R4/T4#Sg00E\R4#4#5#RR5#OR6p,1AR7p,1ER8p,2chR93N/F1#1f2/F3#1[]9%K9#1%04#4#2#:#9#9#H#2#5#8R:%64#8,D5#G%M2R2';R;5?9R<%04#4#2#:#9#2#9#2#5#8R=g00FA,D5#C/;2R>5?9R?'ER@%04#4#2#:#9#:#4#5#8RAg00G>,D5#C/;2RB5?9RC'ERD%04#4#2#:#9#2#5#5#8REg00H9#3#3#3#3#3#3#3#39L9ERF#C/;2RG5?9RH'ERI%04#4#2#:#9#2#H#2#5#8RJ%84,D5#G/;2R55?9R4;B1%1IRI%14R4'7P0PIP4p,4FULLRKp,5modelRLf43<#=P1ABDH3%1DRD%1HRH'7P0PDPHf99<KL#=P1AB@C3%1@R@%1CRC'7P0P@PCf>9<KL#=P1AB<?3%1<R<%1?R?'7P0P<P?fC9<KL#=P1g00HXR0fFRM9<KLRNP:P;C@ROP0PNP=P>C@RPP0PNPAPBC@RQ'7RR'7RSP0fG9<KLPE%C1/;2C@X86R2,J6RT'7P0PNPJP5C@PSPTPOPRP7p,3nx0RRp,5LIMITROp,4SINVRTp,4argHRSp,3FS0R0p,<SEGS_in_hullRUp,7HULL_okRVp,9argH_highRWP8P9p,1RRXPKPLp,2HCRYPMfERZP:P;P3MD>PPPQP7PRPOPTPSP0PUPVPWP8P9PXPKPLPYPMPZP=P>P1MD>P7PRPOPTPSP0PUPVPWP8P9PXPKPLPYPMPZPAPBf5MD>CACAP6P2PFP7PRPOPTPSP0PUPVPWP8P9PXPKPLPYPMPZPEPGf:MD>CICAP7PRPOPTPSP0PUPVPWP8P9PXPKPLPYPMPZPJP5f?MD>CA%=NeX3?X2<P3P1O2n2001000000121000000b0X4CX0@P3P1O2n2001000000121000000b0X5HX0DP3P1O2n2001000000121000000b0X64X0IP3P1O2n2101000000121000000b0W0W7W1o"). Qed.

(* [comment removed for export] *)
Theorem hs_lib : hs_lib_ok ch = true -> LIB_A (mH FULL model (rtA_allow (sigma0 A E ch model))).
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffLIB ()) ["Lib"] "h02HTp;1p;3p;4g0045j15Tg00BLj34Tg00IPj40Tg00JJj11Tg00KHj43Tg00LDj32Tg00CFp,2chR0#5g00Cf34p,1AR1p,1ER2P0p,5modelR3C0#1P1P2P0P3C3f032W0o"). Qed.

End Lib.
