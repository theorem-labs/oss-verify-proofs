(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Lept_objkit Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk Bi_iface Bi_iface2 D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_rop_defs () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53B238Bi_iface6pix8rcC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53B23:Lept_iface5cmapv01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238Cf_iface:pix_obj_rcC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib2K53B238Cf_iface<pix_cells_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface:pix_hdr_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface6p_cmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface5c_arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface5chunkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Lept_objkit@keeps_live_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53B23:Lept_iface3p_dC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53B23;Lept_objkit:keeps_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface5rsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface8cmap_objC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2K53B23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma pix8rc_keep1 : forall L (m m' : mem) pix v rc, pix8rc L m pix v rc -> keeps_live [(pix, 64)] m m' -> pix8rc L m' pix v rc.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_rop_defs ()) [] "h01Hh14__x1h21xh37__arithh44__ffh58__varmaph65__with71mh81Ch92CHh:2CMh;2D8h<2DNh=2HDh>3HOKh?1Kh@1LhA2_HhB2m'hC1nhD3pixhE2rchF1vhG1yp;2p;1p;5p;4p;6p;3p;<p;7p;Bg0000j2{Tg000Pj1NTg0010j1DTg001Uj1OTg0023j1ZTg002Vj1tTg0038j5<Tg0043j4eTg0051j6HTg0060j1RTg006Nj1WTg006nj2ITg007oj4KTg008hj1@Tg009ij13Tg00:fj12Tg00;cj1dTg00<_j3CTg00=[R0j20Tg00>6j18Tg00>Oj2GTg00>ij3LTg00?Ij31Tg00?cj2BTg00@=j3YTg00@Wj2zTg00A5j1yTg00ASj1xTg00B>j2wTg00Baj4VTg00CLj2uTg00Cnj2sTg00DZj3rTg00E9j4qTg00EkR1j2ETg00FGR2j1JTg00FgR3j2FTg00GDj1oTg00Gbj4nTg00HEl<hTg00Hjj2gTg00IMj3kTg00J0j4lTg00J[j1fTg00KWl<mTg00L_j4ATg00M:j1cTg00N4j4TTg00NTj3pTg00OVj1UTg00PRj4XTg00QQj7bTg00R5j1?Tg00RTl<aTg00S9lBvTg00S_R4f1R5#cf0R631p=7%26g00T=R7514p=:%36=147#8p=5f2R81056'0p=4f5R9P4P4f4R:f3R;CT;L8?p56p=9A1497%U89C:;A1456#8'0'Gp=;A149:#8A14;8#8A1456#8'0'0p=6f7R<=147f6R=P9P:P;CXA1485#8/06'0'Gp==AC;85/06p=SA1457/06p=QA1467p=P%U69C85p=`A1456#8p=_1056,G8p=^A1456p=]P9P:P;P8CX%85/06'0p=\P4P4P5P6CTp=[P5g00T[g00U:R>P>g00UZR>P6g00V:Fbp=M%?6#?#?#?#?#?#?#?p=>g00VZR?P4P4P4P2P2P9P:P;P8P5P6M<ap=jP4P4P4P4P4P4P3P6P5P8P3P;P:P9P=P<f8R3f9R2MBvp=i1{44R@#Ng00W9RA#D#D#DRB#D#D#DRC#O#Z%OB#Z#t[RDg00W^P9P:P8P5P6D<P0P=P9P;P8P7P7P7P7CeREP5EH%RBRB,78%:8%5834P@P:%RCRC%W@RFP=P9E9P3P=P9P:P;D<[P6P3P<P9P:PEP;EHP0g00X[R;P3P=1I9:CKP2P=PC%@9%39R:P2P:P9P:P=E;%29R9P2P3P9PEP9P=%dERGP=P9P:PGP:E6G=34CS17=B%:=%5=34P@P3PCPFf:R:P2E9f<R9P:P2P3P<D<[[P6P;P:P31I<=CKP9P2PC%@3%33R<P9P<P3P<P2E;%23R3P9f;RHP3PEP3P2PGP2P3P<PGP<E6G=34CSP0f=R<?C:C%@2%32R3P<P3P2P3P:E;%22R2P<P9P2PEP2P:PGP:P2P3PGP3E6G=3417:B%::%5:34P@P9PCPFf>R:P<E9f@R3P:P<P9PHD<[[P6f?R2?C9C%@9%39RIP3PIP9PIP<E;%29R9P3P2P9PEP9P<PGP<P9PIPGPIE6G=34P0%@<%3<RIfAR9PIP<PIP:E;%2<R<P9P3P<PEP<P:PGP:P<PIPGPIE6G='017:B%::%5:34P@P3PCPFfBR:P9E9fDRIP:P9P3P2D<[[P6%@2%33R<PIP<P3P<P9E;%23R3PIfCRJP3PEP3P9PGP9P3P<PGP<E6G='0P0%39R<fER3P<P9P<P:E;%29R9P3PIP9PEP9P:PGP:P9P<PGP<E6G=17:B%::%5:34P@PIPCPFfFR:P3E9fHR<P:P3PIPJD<[[P6%3JR9fGRKP9PJP9PIE;%2IR9P<PKP9PEP9P3PGP3P9%3IRIPGPIE6G=173B%:3%5334P017:B%2:%5:'QP@P<PCPFfJR:fIR3E9fLRIP:P3P<PKD<[P617<B%23%53'QP0%::%5:P@PIPCPFfNR:fMR0E9fPR3P:P0PIfKD<[P6%:I%50P@fOR0PCPFfQRIP3E9fSR<PIP3P0PEP:EH170BRB%20R9#PRL%30RM#PRN#8RO'0RP'0P;PIP31I0:R:CKAC<3CR;%@0RQA`<M01_M35^NRNP<PIP9PE1]93PGP3P9PMPGPME6E\RM,GLRG'0R9'0RE'01[3CR<=L@FfRPIP3PCP3P:P6A1@<<g00YS1B@<3Yg00Z0R<#WR@%N<R<1z45RF%y4R0%x4RRP41w4ARAg00Z\RSPACV'M1uR>R>P6P8g00[CRTg00[cRU'B1s68=1TUdAr475CqR7b4b5b6X141E66^14P6PIO1RIb3g00\C#>#>#>#>#>#>#>#>RU#JRT,F3RV1F3CRW'E1EWWP4P4P1P6X24RXP11E56#oXG4X24PVPWPXPXPXP4P4g00\b1F56Cn,B4X74XC4P3P31B43PTPCPXPX%J6,B4X2?PUPC1B4CEjM:iPWPW1B4WM<hP@P<PFP0P41g4C9k4ARAPSPACV,MRP>P7b4b5b6X141F6CRC/EC^14PIb3Cl%f:#J,F3/EWePKM<mP;PEPJPQP9P2PNPGPHAYLM8CACACACAPBPPP=PLPOP8P5CACACAW?W<W:P5P6O2n2001000000121000000W0W;P5P6O2n2001000000121000000W0WAW=P5P6O2n2001000000121000000W0W>P5P6O2n2001000000121000000W0W9P5P6O2n2001000000121000000W0W8P5P6O2n2001000000121000000W0P5P6O2n2001000000121000000W0XE4WFXD4XBDW7W@o"). Qed.

Definition ROP_NULL (pd op : Z) : Prop := pd = 0.
Definition ROP_CLR (pd op : Z) : Prop := pd <> 0 /\ op = PIX_CLR.
Definition ROP_SRC (pd op : Z) : Prop := pd <> 0 /\ op = PIX_SRC.

Section RopDefs.
Variable RT : rt_sig.

Definition pixRasterop_case (AL : Z) (CASE : Z -> Z -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pd ps : Z) (vd vs : pixv) (dx dy dw dh op sx sy rcs : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pd -> s32 a1 dx -> s32 a2 dy -> s32 a3 dw -> s32 a4 dh -> a5 = Z_to_bv 64 op -> a6 = Z_to_bv 64 ps -> s32 a7 sx ->
  rw_cells asegs m (bv_unsigned sp) [C8 (Z_to_bv 64 sy)] -> 0 <= sy < 2^31 ->
  (pd = 0 \/ (pix8 (rt_live RT Σ) m pd vd /\ rect_ok vd dx dy dw dh)) ->
  ((op = PIX_CLR /\ ps = 0)
   \/ (op = PIX_SRC /\ pix8rc (rt_live RT Σ) m ps vs rcs /\ 1 <= rcs <= 2 /\ rect_ok vs sx sy dw dh /\ (ps = pd -> vs = vd /\ rcs = 1))) ->
  (op = PIX_SRC -> (dx - sx) mod 4 = 0 -> dx mod 4 = 0) ->
  (op = PIX_SRC -> ps <> pd -> ps <> p_data vd) ->
  bv_unsigned sp mod 32 = AL -> CASE pd op ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 5 0 8 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRasterop m)))
    (fun c => exists (Σ' : rts RT) (rv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rv) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo
          /\ keeps RT Σ Σ' sp (if pd =? 0 then [] else [(p_data vd, p_data vd + rsize vd)]) m m'
          /\ (pd <> 0 -> pix8 (rt_live RT Σ') m' pd vd) /\ (op = PIX_SRC -> pix8rc (rt_live RT Σ') m' ps vs rcs)) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 8 <= rt_credit RT Σ').
End RopDefs.
