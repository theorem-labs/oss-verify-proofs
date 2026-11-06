(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Pm_iface Pm_iface2 Pm_okit Km_kit KmF_kit PmF_kit Cf_iface RT_fk Bi_iface Bi_iface2 Bi_fktw Pm_gaps_iface D_iface D_defs Po_rows Po_rowkit Po_addbg_defs Po_rembg_defs Po_dilate_defs Po_morph2_defs Po_null_defs Po_pmcs_defs Po_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_csc_defs () := "C46Stdlib5Lists4List2InC46Stdlib5Lists4List3revC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2K53A237PmF_kit>live_apart_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C46Stdlib5Lists4List9in_or_appK47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z02C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53A238RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53A238RT_ifaceDsec_bytes_cons_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC69OSSVerify5KrLib2K53A238Po_iface4s_syC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53A238Po_iface4s_sxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53A238Po_iface6s_rowpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface6s_dataC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib2K53A23;Po_csc_defsCsec_bytes_map_smallC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib2K53A236Km_kit=sec_bytes_revC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface=sec_bytes_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface<sel_new_liveC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A238Po_iface4selv00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_revC46Stdlib5Lists4List:length_appC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List9in_app_orC46Stdlib5Lists4List6in_revI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C47Corelib4Init5Logic7f_equalC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib2K53A23>Po_dilate_defs8sel_liveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>rev_involutivec69OSSVerify5KrLib2K53A23;Po_csc_defsKpixCloseSafeCompBrick3_caseC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib2K53A238RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS:mat_stableC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53A238Po_iface5pix1cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4uctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface7po_rowsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4LSTKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4lenvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4lresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface6LIB_POC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface4LIBHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6io_sspC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53A238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC69OSSVerify5KrLib2K53A238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235RT_fk7ret_stFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface7lpost_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6p_cmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface<cmap_rm_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5rsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6keepsLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5p_wplC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3c_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface8c_nallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface7c_depthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC69OSSVerify5KrLib2K53A238Po_iface=cmap_add_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_pmcs_defsJpixCloseSafeCompBrick3_cpsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib2K53A23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_ifaceGe_pixCloseSafeCompBrickC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface8CSC_COSTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface8CSC_SECBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00".
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition csc_descr : Z := 0x2d19e.
Definition csc_epc : Z := 1417864.
(* [comment removed for export] *)
Definition csc_sh : Z := e_pixCloseSafeCompBrick + 0x1b0.   (* [comment removed for export] *)
Definition csc_f  : Z := e_pixCloseSafeCompBrick + 0x55c.   (* [comment removed for export] *)
Definition csc_t  : Z := e_pixCloseSafeCompBrick + 0x6ac.   (* [comment removed for export] *)
Definition csc_ep : Z := e_pixCloseSafeCompBrick + 0x278.   (* [comment removed for export] *)
Definition csc_fl : Z := e_pixCloseSafeCompBrick + 0x32c.   (* [comment removed for export] *)
Definition csc_fs : Z := e_pixCloseSafeCompBrick + 0x330.   (* [comment removed for export] *)
Definition csc_fz : Z := e_pixCloseSafeCompBrick + 0x334.   (* [comment removed for export] *)
Definition CSC_STOPS : list Z :=
  [e_stack_malloc_2; e_selectComposableSels; e_pixAddBorder; e_pixDilate; e_pixErode; e_pixDestroy; e_pixRemoveBorder; e_pixCopy_po;
   e_selDestroy; csc_sh; csc_t; csc_fl].

(* [comment removed for export] *)
Section CSC_K.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma fresh_ne : forall S (mq : mem) X Y p n q k,
  ART RT S mq -> rt_live RT S = X ++ Y -> (forall b j, In (b, j) (rt_live RT S) -> 0 < j) -> In (p, n) X -> In (q, k) Y -> p <> q.
Proof using AF.
ltac2:(KReplay.run1 (kr_t_Po_csc_defs ()) ["CSC_K"] "h02HYh14__p1h24__x1h34__x2h44__x3h51lh61qh71Ah81Dh91Eh:2HXh;2LVh<2P1h=2P2h>3POSh?1Sh@1XhA1YhB7__arithhC4__ffhD8__varmaphE5__withF1bhG1jhH1khI2mqhJ1nhK1pp;1p;2p;3p;>p;5p;6p;4p;7p;8p-1g0000R0p4p710p8p1000Gp4p710g000_R1p4p710p8g001=j1^Tg0025j12Tg002Zj1?Tg0038j1=Tg003[j1]Tg004=j2RTg004]j1ATg005=j3NTg0065j27Tg0071j39Tg007Nj3;TP0j30Tg007hj28Tg008Dl>VTg009Fj24Tg009cj25Tg00:?j2DTg00:Yj3QTg00;3j5CTP1j6@Tg00;Qj3OTg00;kj1MTg00<Kj2>Tg00<ij4LTg00=Gj1KTg00=ej1JTg00>Pj2ITg00?3j1HTg00?Xj2:Tg00@;j43Tg00@fj1GTg00AHj3BTg00Akj7FTg00BOj6PTg00C3j2ETg00CUj2STg00Coj2TTg00D[j3\Tg00E:j4[Tg00Elj7ZTg00FHj1WTg00Faj4XTg00GAj7YTg00Gej8UTg00HIR1P1f1R0f0R2CXp=1P0g00HgR3g00IFR4P4g00IfR5P2g00JFFYp=6f3R6P3P4P4P5f2R7P0P2GUp=<p,2RTR8#^g00JfR9#2R:#2#2R;#2#2#2#?#=%?;#=#][1R11R;#AR<f7R=f6R>5N8f8R?,78f5R@99;>5;<1102f;RA,7850;g00KKRB/80[^G1^F111>@=0;?f4RC,1@=0;?A;1?>R?P1f9RD112==0;Ag00KiRE]0X6111D>f:RF50;P8p,2AFf>RGf=RHf<RIPAPFPDPFP=P>P@P6P2M>V14FD/5F14F=/5F'DP@PAPFP<A9;HI11IA=0;2X5<P;PHPI11AFRJA0;JHA0;JI;QCDCf?,78P>E@O318BFP>PIPDP<A9;GH11HF=0;2X5<P;PGPH11IDRIA0;IGA0;IH;O7DCf@,78P=E@O318BDp-0RDg00LFR8#M%A8P11>17P01>16CL%K1%J1R8P11I1BRIg00M2R;%H9,:1RFC3,68%G4RJP8P1PIP;1:1:R:C3,68PJP8P8P3P4P4P5P11:19R9=B1:g00MYR:P9C3,68P1AB19FP:P9C3,68FFPJP8P3P4P4P5P@EPC<C<C<1E85P2P7g00N@R8g00N`R5'S1T27=;85dA\1B0C[bCbDbEX21X31X41W118B7RB1476/57147C/57'DP>[\B[^21^31^41^1DP2PEPAPHPGP0P7P6O7bBb=b<b8W0P=P2P0FZW9%W?eW0W:W>W;W7XH1X61XJ1XK1XA<W@WIW?o"). Qed.
End CSC_K.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sec_bytes_map_small : forall (rs : list Z) n, n <= 64512 -> sec_bytes (map (fun r => (r, n)) rs) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csc_defs ()) [] "h01rh12rsh22Hnh32IHh41nh51zp;1p;2p;4p;3p;6p;5g004]j1ATg00?3j10Tg00O@j19Tg009cj2@Tg004=j2;Tg00O^j44Tg00P:j12Tg00CUj28Tg00Q8j36Tg00QXj4:Tg000_j6?Tg00Raj5>Tg0025j17Tg00Faj4<Tg007Nj3=Tf0R0#7#7p=1g00HIR1P1f1R2P0C<p=5g00KKR39=10p=3%A1R4g00Jf#0#0#0#0#0#1#1#1#1#1#9,@0P1P11;11R5f3R6,50X01P0C4#2#3X141813P1P5f4R3,50X01P0C4#2#3P1P1P5f5,50X01R7P2C4R8#2%30X51P0f2R0/53=658#2P0P3P8P6C:E?P1P5P7A6102C4#2#3eW3X14X01P0D>W2X41W1o"). Qed.

(* [comment removed for export] *)
Lemma sec_sel_new_live : forall sel sv L, 1 <= s_sy sv <= 30 -> 1 <= s_sx sv <= 30 -> sec_bytes (sel_new_live sel sv L) = sec_bytes L.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csc_defs ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with61zh72rph81Lh92SXh:2SYh;1rh<3selh=2svp;2p;1p;4p;3p;6p;7p;8g004=j2hTg004]j1LTg00O@j17Tg00SCj1@Tg009cj21Tg00?3j1;Tg0025j1>Tg00T<j2ATg00TWj1?Tg00UPj24Tg00Umj1FTg00O^j4BTg000Gj2eTg00P:j10Tg00Vhj1ITg00Q8j3:Tg009Fj25Tg00;kj1ZTg00<Kj2YTg00=Gj1XTg00=ej1WTg00>Pj26Tg00?Xj2VTg00AHj3UTg00@;j4GTg00C3j2RTg00CUj2QTg00Coj2PTg007Nj3DTg00D[j3OTg00E:j4NTg00Wcj2CTg00XLj1ETg00Xkj3MTg00YTj2STg00Z@j2TTg00BOj6gTg00Zlj7fTg00@fj1dTg00[Pj3JTg00\3j3`Tg000_j69Tg00]>j1_Tg00QXj4KTg00]\j1^Tg0071j3]Tg00^\j2\Tg00_^j3aTg00Faj4bTg00GAj7[Tg00Gej8cTf0R0#>#>p=3g00HIR1P1f1R2P0Cbp=8AD120p=2P2g00HgR3g00IFR4P4g00IfR5P0g00JFF[p=<P1P2g00MYP0CGp==f3R6P3P4P4P5f2R7P2P0Gcp=Hg00`_1h11R8#Lg00JfR9#7R:%@2R;'1%;9#;#;R<#>#7R=,1;'A%?7R;,1:11;='AP1P1P8%39R;#7R>f4R?#?R@'4,80RAX71%F6RBCBRC,e8RD#0RE%I6RF%>;R;#7RG%@6'4RH'8%3;#7R;,8?=:87RI5:8RJ#0RK'5%06RL,20X61P1%0CRM%I?%@?RN,4G'8f5RO/8;=:865:8#0,50/2LX61P1%0IRPP1P8%?O,4>,80X71%F?CB#0/50/2LX61ROP1%07RQPOP1g00KKRO150L/2LX61g00LFRR#ZRS%LRRT1Y12RU%X1RV%W1RWP1161O1V19R95U1g00aZP9CG'<1RW5RXP0P7g00N@RYg00N`RZ'Q1P07=DYZdAO1O2CNRZb2b4b5X0115O0/20^01P0PLO1b1P1P8PAX;1PBCB#0%?6,4>p-0RAg00bARL,C1RO%EL#E,C19M1Og00b`'S'T=:RSRRPTPUPVPWPWP3P4P4P5PWP3P4P4P5P6Eg161=,=9,<WFfR5%d4R4161>=J19%;<#;#3#3#3#3#3#7R<,61R3'=,<WCHPXPZb2b4b5X01W3110=,A2R=14>2/1<[^01^3AP011:@P@P2O3b15`BE9PPP?P;P7PSPT%_1PV161;/=3,<WPXPZb2b4b511;<P0b1CKE9PKPFPHPIPRPTPUPVPWP5P4161G=J19/=3,<WCHPXPZb2b4b5X01X3A14G2/1<\=^01^3AP011:NPNP7O3b1CKE915MK/2QePE%^CE9A]8DJ#01\DJE9Aa?67#0/2QeW9W:W8W=X<1o"). Qed.
Lemma len_sel_new_live : forall sel sv L, Z.of_nat (length (s_rowp sv)) = s_sy sv ->
  Z.of_nat (length (sel_new_live sel sv L)) = Z.of_nat (length L) + 2 + s_sy sv.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csc_defs ()) [] "h01xh14__x1h24__x2h34__x3h41nh51Lh63LENh77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=2rph>3selh?2svh@1yp;2p;1p;4p;3p;<p;8p;6p;Bp;7g004=j2nTg004]j1LTg00Umj1>Tg00cLj21Tg00clR0j12Tg00SCj1:Tg0025j18Tg00O@j19Tg00TWj1WTg00UPj2=Tg00O^j4MTg000Gj2mTg00Vhj1ITg00Q8j37Tg00dLj2;Tg009FR1j20Tg00XLR2j1@Tg007Nj1]j3FTg00dcj1[Tg00CUj25Tg00eAl<XTg00efj1BTg009cj2HTg00fKj1VTg00fij2UTg00Wcj2ATg00gJj3QTg00Xkj3PTg00YTj2OTg00;kj1NTg00<Kj2CTg00<ij4RTg00=Gj1STg00=ej1TTg00?Xj2<Tg00?3j1lTg00@;j4KTg00@fj1kTg00>Pj2GTg00AHj36Tg00Gej8hTg00C3j2gTg00Coj2eTg00D[j3aTg00E:j4`Tg00h3j4_Tg00h^j4bTg000_j6?Tg00i=j2^Tg0071j3cTg00i\j3dTg00_^j3\Tg00Faj4fTg00j;l<DTg00j`lBiTg00GAj7jTg00HIR3f1R4f0R53Fp=3P3P3P4P5Cfp=4g00kFR6P6P3P3P2P0P0f3R2g00kef2R7P4P5M<Dp=EP6P6P6P3P3P3g00lIP0P0P0P1g00lif5R1f4R8P2P7P4P5MBip=ZP6P3P3P3P0P0P1P8P2P7P4P5M<Dp=YP4g00HgR0g00IFR9P9g00IfR:P5g00JFFjp=Jg00`_1n33R;#L%>4,13#2%:4'3P6P3P;g00JfR<#8R=#8R>#9%W2'=,45X=3R?%>7R@CMRA,m;RB,1;RC%I7%8>R>#9RD%:7RE'='4%8>#8#9R>,42=7;457;RF,1;RG';%25RH11;7RI#2RJ%9=RK'0%:2RL'0RM'3X46P611;ARN%I21=DL'4148>=7;757;,1;,;5#2/3MX46RMP6113@R>PM11;4RM#@RL#@RD,;>RO#2RP%2MRQ/0K/0ERE'3%2>RR%9<RS,0QRT/0SRU'0RV/3EP3P3%]3RWP5X03RXPW1345#[X@3X03PPPVPXPX153HX06POPVP>PR153RPDPU105SX03RUPLPTPUPMPQ153QCECEEZEYPEPE153EM<X%B>g00KKRQ/HR%BI1HQJg00LFRJ%V<,U3g00bARI#@,A35Q31A3I5P3g00b`'O%NJ37%LJP31C37P41C32CR%S3%T3RJP0P9P9P:P31<3<R0g00aZRI%l<,<3R<CK,JJ%k9P31<3=R=1G3SR9563=6399630PI1G3K963==63<CK,JJGh1gJ:P5P7g00N@RJg00N`R:'51e57=FJ:dAa3Q4C`b8b9b:X13X23X331357107S/0S,04107K/02'3[^13^23^33P5%:111;8#2%>1,13#2P2O4b7b<b;C_1;>G#2/3EePNP3P;P?P@CbE?PC1^;AE?Ac;BF,1;Ad;BFE?A\274,1;#2/3EeW6W5W?X>3o"). Qed.
Lemma pos_sel_new_live : forall sel sv L, 1 <= s_sy sv -> 1 <= s_sx sv -> (forall p n, In (p, n) L -> 0 < n) ->
  forall p n, In (p, n) (sel_new_live sel sv L) -> 0 < n.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csc_defs ()) [] "p'0h01Hh12H0h21xi001xh32rph41Ah54__x1h61lh77__arithh84__ffh98__varmaph:5__with;1nh<1Bh=1eh>1fh?1pi011ph@1yhA1EhB1LhC3POShD2SXhE2SYhF2_HhG3selhH2svi021zp;2p;1p;3p;4p;5p;6p;7p;8g004=R0j2lTg004]j1FTg00O@j1HTg00SCj1ETg009cj2MTg00TWj15Tg0000j30Tg00_^j3[Tg0025j1@Tg00Umj14Tg00O^j4=Tg000GR1j2CTg00Vhj17Tg00mLj5`Tg00:?R2j2_Tg00mjj3]Tg007Nj3<Tg00T<R3j2?Tg00nER4j2GTg00n_j5\Tg00o>j2RTg00XLj1ZTg00Wcj2QTg00ogj3PTg00Xkj3OTg00YTj2NTg00;kj1YTg00Q8j3KTg00<Kj2XTg00=Gj1WTg00=ej1VTg00>Pj2BTg00?Xj2kTg00@;j4UTg00@fj1jTg00[Pj3TTg00C3j2iTg00CUj2eTg00Coj2dTg00D[j3cTg00E:j4aTg00UPj2ATg00Elj6JTg00]>j1bTg00Faj4DTg007hj2fTg010Pj6^Tg00GAj7gTg00Gej8hTg00HIR5P5f1R6f0R7CDp=1g00KKR8/f7p=3P5P5f2R91A67CDp=:%E7,A6p=8f3R:P5P5P9P6CD;K7p=6%57,A6p=;P5P5P9P6CD=<:7p=9f4R;P5P:P9P6P7E^p=>A<567p=2P6g00HgR<g00IFR=P=g00IfR>P7g00JFFgp=IP5P6g00M2P7CUp=LP:P<P=P=P>P9P6P7Ghp=Sg00`_1l55R<#Fg00JfR?#HR@%E6'M%59,M@1167RA=0<;%36[^;5^?5f7RBf6RCf5RD3[90<AP<P5P<%@?#@RA#HREf8RF#55:7X35%4BC=,C<RGP<%7B%@ARA#HRH/8BP<PF%@A#@#HRAPCC6C6RI1196RJP7D`A0<JGA0<JI'_P211:9RJP5P<f9RI#59:7EX35%4FC=,C<50<P<%7F18HFP<PIPAPBC6C690<J%3:P711;:RJP5P<f:RG#59:7EX35%4IC=,C<50<P1p4p710R1%F7RKP3A09761C:990:6RL[1C969097A0:69[RMA0;9:\LA]967P7n2001000000120000000X26W6W4PM^26^6K^41P7P<P5P<f<R1#59:7EX35f;RK#4C=RM11CDRLP6O4A0<LMg010mRMp4p710RNPMp4p7210RMP6\6RO%F9RPP3P;P:P9P6C=90:7P;P7O1=<D9A0C7:'?X2D,GD[RQP:P7O1=<;6A0D79'?X2;,G;PDP;P:P9C=90;6RR[PDP7O1=<C:A0B7;'?X2C,GC\RP;P:P9P6P7D\P6n2001000000120000000X@9W6W>W<W4PQ^@9^6P^>O^<M^4NP7P5P<f>RN#59:7ERMX35f=RO#411FBRPP6O611IFRQ9<<M%4N9057'?X25,G5P4P5P<P7f?R4,;E11GIRMC9%449057'?X25%3IP7P<P7fARR,;E111KC9%4R9057'?P3P<P6fBR3,;E11O1C9%439056%3OP7P<P:fDR:,;E114NC9fE#4905;P<P0P5P5P5P7P7n2001101000120102102X=<RSfF,;ERT,1Df@RU,1RP6D>12TUP<P0P5P5P5P7P6n2001101000120102102X=<R0fG#59:CE113RP9D>12C3fCR3,2BfI,;E/23P5fJ,;E%37X;5R3g00LFRT1R5Eg00bARV#Z,Q5RW5P51Q5VRV5O5g00b`RX'N%YTRY3K%FTRZ1X56R[%W5R\%V5R]P51B5@g00MY1k5?R?CU,I]R^%j=R=1B58R_1B5E=T5?'L,I]CS1i]>R>P7P9g00N@R`g00N`Ra'e1d79=<`adAc586CaR8b8b9b:X551M@7R@1AE6#3[^55P7fK#5fHO2b7P:P7EJW0W0P7O1b0P7O1b0WFWAP6P7O2n2001000000121000000W0X35P6P7O2n2001000000121100000b0b1b0b1W0P7O1P<%7I18HIP<PGPAPFC6C690<JP2P<%7G18HG11D;R;C9P<PKPAPIC690<;%3DP7P<%7K18HKPLC9P<PS%7118H1RD'111BCR;P7D>12DCP<P0%7ORD%EO7:HPPP6D>12DF%7N/2I18H4/2IP518HUP31R5H=P5W=O5V/NX=KTYPZP[P\P]P^P=1B5H=T5?,L_,I]CSP>P8b8b9b:X551AH6#3\@^55P7%ERP4O2b7PGP7EJW0W0P7O1b1P7O1b1W0P7O1P<P1PAPGC690<LP2P<POPAP;C9A0<;K%3BP7P<PNPAPPC9P<PS114APQP7D>12AFP<P011UAPMP6D>12UG12RK12AKP5PAP3PYPZ%b5P\1B5A,L_,I]P>P8b8b9b:%3AP7b7P1P7EJW0W0P7O1b1P7O1b1W0P7O1A0<P1PGPIPFP7O3W0P7O1n200100000021000010000W1P7O1n200100000021100011000W1P7O1n200100000021100011000b0W0X;5X?5WCWDWEWBWHXG5o"). Qed.
Lemma sub_sel_new_live : forall sel sv L e, In e L -> In e (sel_new_live sel sv L).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csc_defs ()) [] "h02Heh11Lh21eh32rph43selh52svp;2p;1p;3p;4p;5g004=j2BTg004]j1ATg0000j30Tg0025j11Tg00O@j12Tg00TWj1@Tg00UPj25Tg00Umj1<Tg00O^j4;Tg000Gj28Tg00Vhj19Tg00SCj1:Tg00Q8j37Tg007Nj36Tg00;Qj34Tg00;3j5?Tg00_^j3=Tg00Faj4>Tg00HIR0P0f1R1f0R2C>p=3g00`_1B00R3#AA0321P3P0P3g00Jf#1#1R4#2f4R5#@'5,32X30f3R6#<C;,83R7%96%14R4#2%:6'5'3R8%14#1#2,35R4f2R9573R:573R;P1A0317A031;A6381A031:A6341A0319;423434D?A=5699031eW0X23W1W5X40o"). Qed.
(* [comment removed for export] *)
Lemma sel_new_live_self : forall sel sv L e, In e (sel_live sel sv) -> In e (sel_new_live sel sv L).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csc_defs ()) [] "h02rph11Hh21eh31lh41Ah52Heh61xh71Lh83selh92svp;2p;1p;3p;5p;6p;4g004=j2LTg004]j1DTg011Jj2KTg0000j30Tg0025j1;Tg00O@j1?Tg007Nj34Tg00Vhj16Tg00SCj17Tg00TWj15Tg00Umj19Tg00Q8j31Tg000GR0j23Tg0071j3@Tg00CUj2CTg00:Yj3<Tg00;Qj3=Tg00;3j5>Tg00Elj6BTg00mjj3JTg012Mj2ITg000_j6HTg00_^j3FTg00Faj4ATg00UPj2GTg00O^j4ETg00HIR1P1f1R2f0R3CAp=8P1P1f2R41G23CAp=2P1P4P2P3CEp=:g00`_1L11R5#DR6f3R7/K49053g00:?R8f4R9g00Jf#;#;R:#;R;#;#;#?R<'8=452%67%?;R;%7732%?:R:%59523X01%975:55159052f5R=#5923:X01%995:5R>,35%69%7972;R?18=<R@=1575155@59054P3A45@4P5f6R@/8<RAf7RB#5923:X01%9@5:5RC,35%6@%7@72;RD18B<=15=5155@5RE9053X25P5%5@923:X01%9=5:5RF,35RG%6=%7=72;RHA15A9RI515RJPAA05AGA05AJA45HAA05AIA45AAA05A91C5A3<3=3=D>P7P3EBW1P3O1A15?>9054P8A45H7A057FA059EP3A45D9P5%6B%7B72;RDf9RE#5923:X01f8RF#95:5RH,35R8%6F%7F72;18E<=15B5155@59053X25P5%5F923:X01%9B5:5,35R:18F<=15@RF915DR<PDA05D:A05D<A45DDA05DF1C5D3<3=D>P=P3EBW1P3O1A059CP5P:P<P=A05=:A05=<P0p4p710R0%D3R<g00T<A043213749072R=[13429043A0724[R:A0947\=AJ423P3n2001000000120000000X62W3W4P:^62^3<^40P3P5P8P@P6PHA05B3X36P213581I5HEHO4b13<D>W5P3O1n200100000021100011000W1P3O1n200100000021100011000AF9749052eW5X25W7W9X81o"). Qed.

Section CSC_DEFS.
Variable RT : rt_sig.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csc_post (Σ : rts RT) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F (m : mem) (lo pix1 : Z) (v : pixv) (cv : cmapv)
  : config -> Prop :=
  fun c => exists (Σ' : rts RT) (v' : pixv) (cv' : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix1) F m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo
          /\ keepsL RT (cmap_rm_live (p_cmap v) cv (rt_live RT Σ)) Σ sp [(pix1, pix1 + 64); (p_data v, p_data v + rsize v)] m m'
          /\ pix1c (rt_live RT Σ') m' pix1 v' cv'
          /\ p_w v' = p_w v /\ p_h v' = p_h v /\ p_wpl v' = p_wpl v /\ p_data v' = p_data v
          /\ (p_cmap v = 0 -> p_cmap v' = 0) /\ (p_cmap v' <> 0 -> c_n cv' = c_n cv /\ c_nalloc cv' = c_nalloc cv /\ c_depth cv' = c_depth cv)
          /\ ((20000 < p_w v + 64 \/ 20000 < p_h v + 64) -> v' = v /\ cv' = cv)) c
       /\ rt_live RT Σ' = (if (20000 <? p_w v + 64) || (20000 <? p_h v + 64) then rt_live RT Σ
                           else cmap_add_live (p_cmap v') cv' (cmap_rm_live (p_cmap v) cv (rt_live RT Σ)))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - CSC_COST <= rt_credit RT Σ'.

Definition pixCloseSafeCompBrick3_case (AL : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix1 hs vs : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix1 -> a1 = Z_to_bv 64 pix1 -> a2 = Z_to_bv 64 hs -> a3 = Z_to_bv 64 vs -> ((hs = 1 /\ vs = 8) \/ (hs = 30 /\ vs = 1)) ->
  pix1c (rt_live RT Σ) m pix1 v cv ->
  uctx m sp s0 ras -> po_rows e_pixCloseSafeCompBrick ra ras ->
  bv_unsigned sp mod 32 = AL ->
  lenv RT Σ m sp lo (LSTK 13) -> lres RT Σ 11 40 CSC_COST -> sec_bytes (rt_live RT Σ) + CSC_SECB <= SEC_BYTES -> LIB_PO m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCloseSafeCompBrick m)))
    (csc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo pix1 v cv).

Lemma pixCloseSafeCompBrick3_of_al : pixCloseSafeCompBrick3_case 0 -> pixCloseSafeCompBrick3_case 16 -> pixCloseSafeCompBrick3_cps RT.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_csc_defs ()) ["CSC_DEFS"] "p'0h01Hh12ALh22H0h32H5h44__x1h54__x2h64__x3h74__x4h84__x5h92A0h:2A1h;2A2h<2A3h=3ENVh>1Fh?3FDOh@2H1hA3H16hB2H2hC2H3hD2H4hE2H6hF2H7hG2H8hH3LIBhI3MSThJ2P1hK3PMchL3REShM3ROWhN4SECBhO2SHhP3SPAhQ2TPhR2UChS2_HhT3_H0hU3_H1hV3_H2hW3_H3hX3_H4hY3_H5hZ3_H6h[3_H7h\7__arithh]4__ffh^8__varmaph_5__with`2a0ha2a1hb2a2hc2a3hd2a4he2a5hf2a6hg2a7hh1chi2cvhj3cv'hk2fchl2gphm2hshn2loho1mhp2m'hq2mshr4pix1hs1qht2q0hu1rhv2r0hw2rahx3rashy2s0hz2s1h{3s10h|3s11h}2s2h~2s3i002s4i012s5i022s6i032s7i042s8i052s9i062spi072t0i082t1i092t2i0:2t3i0;2t4i0<2t5i0=2t6i0>2tpi0?1vi0@2v'i0A2vsi0B2Σi0C3Σ'p%0p&0p;1p;2p;3p;5p;4p;6p;7p;Sp;Dp;8g0130k108Tg0025j17Tg00O@j1@Tg001=k10HTg002Zj1\Tg0038j1gTg00?3j1?Tg014Ck20YTg003[k10TTg004]j1YTg014ok10GTg015mk10>Tg016ij2RTg007Nj32k20BTg00:?S00j2NTg0065j2KTg017Oj5}Tg018Ik40^Tg019Dk30]Tg01:@k10[Tg01;;k60XTg01<6k50VTg00P:k10STg01=1k10OTg01=lj1oTg01>gj1]Tg005=j3GTg01?bj20Tg01@Lj21Tg009cj24Tg01AGk201Tg00FHj1hTg01Ahj2ITg00UPj2XTg01BEj26Tg009Fj23Tg01Bej2~Tg007hj28Tg01CLj2|Tg01D3j2zTg01DYj2yTg01E?j2xTg00CUj2dTg00fKk10\Tg00fik20ZTg00XLj1ETg00gJj3cTg00Wcj2uTg00YTk20WTg00Z@j2VTg00;kj1rTg00Q8j3TTg00<Kj2vTg00]>k10RTg00<ij4bTg00=Gk10QTg00=ek10PTg00>Pj2fTg00@fk10NTg00?Xj2QTg00[Pj3nTg00AHk304Tg00@;j4`Tg00Zlk70MTg00Akk70LTg00C3k20KTg00Cok20JTg00D[k30FTg00E:k40ETg01E`mS0CTg01F]k40@k50<Tg01GVmD0?Tg01HOk70ATg01IMj1MTg01JJj3lTg004=j2mTg00Faj4sTg01KKk103Tg01LHk10=Tg01MDk70ITg01NAj1^Tg01O;j1_Tg01P5j1kTg01Q1j1jTg01Qkk100Tg01Rjj1qTg00T<R0j25Tg00nEj2WTg01Shj2tTg01TEk20;Tg01Tbk30UTg01Udk20:Tg01Vbk209Tg01W`j2iTg01X=k30dTg01Y2k10cTg01ZEk20bTg01[<j4wTg00Xkj3eTg00GAk70aTg01\1k60`Tg00Gek80_Tg00HIR1f1R2f0R332p=;f2R4=212/53p=D%73#7p=[1342/43p=ag01\UR500b3p=CP5P4P2P3Cwp=Hf5R6f4R7'3g01]MR8'4f3R9/64g00KKR:5211423'5'5p=:g01^LR;,i6/471394/42/53'5p==1523,54p=91042/63p=<A213:p=>P5P9P4P2Cw/53p=UA214:A2123'Np=A1i2;/43p>061694=21:1423'5p=Z1367/491342/48/53'5p>071323/48p>051623=21:p>021442/53p=P1423,54p={1u13p=JAe123p=OAe1239e14p=SP1P2g00aZP3C`p=FP2g00HgR8g00IFR;P;g00IfR<P3g00JFK0ap=BP2P8P;P;P<P3J0`p=pP9P8P;P;P<P4P2P3L0_p=LA2123,N4p>0D&08:g00JfR=#7R>#7R?#7R@#7RA#@RB$08p,2RTRC$0HRDg01_Jp-0[%7ARA#7S01#\RE#gRF%?>RG#\00YF%\A#g%\@#g$0T\FRHg01`@RIg01a=RJ%Y1fYRK$0GfZRL$0>fWRMg01b;,RE52FfRRNf8RO,RE52Ff9RP,RE92FNRQf;RR%@=RSf:RT%@@';3D%?=R@#?#?#7#@1;TS5DR'NfbRS,KCf?S02f=RUPTPPD}f@RVf`RWPLPPH0^g01c2S03@0]STPCfeRXfBRYPSfAS04%7@#?#@$0[RZJ0XPCffR[%?G#@%7G#[#@g01d>S05I0VfgR\,KC$0Sg01e;g01f83afER]$0OP0fFR^#o%]^fiR_=GC^%C^10E[R`9H^]11C_RaP]P]PZP`P`PBP`PBP`PaE:E=3939%@ARA9<E\Ra#>S061;aBS07'NP9fHRa#ofIRb#]flRc=GCb%Cb10E_Rd9Hba11CcRePaPaPZPdPdPBPdPBPdPeE:E=3939P0fJRe#]fmRd=GCe%CePePbfjRf,0ERg11CdRhPbPbPZPgPgPBPgPBPgPhE:E=CU39fkRh=<EARg?AgBP3fLRg#]fpRifMRj5GC%CjPjPg10EdRk11CiRiPgPgPZPkPkPBPkPBPkPiE:E=CU39P0fqRifNRk5GC%CkfnRl,0ERm9Hkj11CiRnPjPjPZPmPmPBPmPBPmPnE:E=39foRn=<EARm?AmBP3fsRmfPRo5GCfQRp#C10EiRq9Hpoft,1CRrPoPoPZPqPqPBPqPBPqPrE:E=39P0%CNPNPpfr,0ERrfuRq,1CRsPpPpPZPrPrPBPrPBPrPsE:E=CUA<EmARm?AmBP3fTRm#CfURsPm10EqRqfxRr,1CRtPmPmPZPqPqPBPqPBPqPtE:E=CUP0fVRtfv,0ERq7HsfyRu,1CRvPsPsPZPqPqPBPqPBPqPvE:E=fw=<EARv?AvBP3fXRv10Er7HMf|,1CRrPvPvPZ10EuRuPuPBPuPBPuPrE:E=P0f}Rr,1CRu006KPKPZfz,0ERqPqPBPqPBPqPuCZJ07f{=<EARu?AuBP3p+01@Ru,1Cf[Rq+06f\RwPZ10ErRrPrPBPrPBPrp+01ARr,1CCZJ07P0f]Rxf~,0ERy7aZPyPBPyPBPyp+01BRy,1CE:A<EuARu?AuBP3f_Ru10Er7aZ10EyRyPBPyPBPyp+01ERy,1CE:P0p+01C,0ERZ005BPZPBPZp+01FRZ,1CCZp+01D=<EARr?ArBP310Ey005B10EZRZPBPZp+01IRZ,1CCZP0p+01G,0ER0002Bp+01JRy,1C,40p+01H=<EAR0?A0BP310EZ002B10Eyp+01MRy,1C'4p+01K,0E001A%>ARZ#hp+01L,0ER01I0A,XA160A'3';[1~0A18:AR010EyRy/6ARr18rA5P:[1|yA18A:p+01N,0ERy/6ARr,8A?{r:[1zyAp+01O,0ERy/IA#>\Z1yyAp+01P,0ERy/6A/;y\Z1IyAP1p+01Q=<EAP1p+01R,0E001B%>BRy#hp+01S,0ERr1IrB,XB16rB'3';[1~rB18:BRrp+01T,0ERz/6BR{18{B5P:[1|zB18B:p+01U,0ERz/6BR{,8B?{{:[1zzBp+01V,0ERz/IB#>\y1yzBp+01W,0ERz/6B/;z\y1IzBP1p+01X=<EBP1P6g01g6Rz1x:B'dPreO1183B9P:3PU1x:A,dzP0eO118OA9P:Og00LFR0&0\=-0Z1Rzg00bARr#ES08#ER{#ER|#ER}#E#ER~#J5c1S09%J|R|%J{R{9c1zS0:1u1rRr'O3S%E~#JR~%J}R}9c1zRz1O|{3SQ08#JR{/Org00b`+0WRr'V'VQ09Q0:,O|7S}1O|{9S~z/Vr'V%r05T03T%Y0P1P11v17P4&0R1R0CbP2P11v16P9P0CbCb&0Q1&0P1R0P01f1BRr1f1:Rz'F,B0,p0&0N;R~1Q1@R@1Q1G9n1r1Q1>R>6041'F,B0CLP~P0P0P8P;P;P<P1Pzg00MY1Q1=R=C`,B0P1P=g00M21f1ARGC`,B0K0MP~P0P01FGz,B0,p0P~1Q1?9n1G>041=,F@,B0CLP~P01F>z,B0P~P0P8P;P;P<1F=z,B01F=r,B0K0LCLCLCLCL20K0<P3P4g00N@R0g00N`R<'d20J34=20<dB0F1:2H0Eb]b^b_X41X51X61X71X81g00KiR<\y1XB6/34,;9[182A9P:2P<\Zf6RZ,XA/39,;6[%>7R<B0D<7B[[[[^41^51^61^71^81P3P7PRp+01\,0EP9PTPPP2PVPYO9b\b2b3bvbtbGbFbEb3bDbubsbCbBb@b2b0W[WPP2P3O2n2001000000121000000W0WZP2P3O2n2001000000121000000W0WYP2P3O2n2001000000121000000W0WXP2P3O2n2001000000121000000W0WWP2P3O2n2001000000121000000W0WVP2P3O2n2001000000121000000W0WUP2P3O2n2001000000121000000W0WTP2P3O2n2001000000121000000W0WSP2P3O2n200100000012100000016`AR`?A`BQ00Q06Q07PCPhPfg01g\R`P_fhR<P\P[PXfdR:fcRyPSfaR=PWPuf^RrPxPwPqPLPKPvPMPtPsPmfSRzPNPpPofOR;PkPjPgfKR8PePbQ03PaNS0C+0BH0@g01hcPCP4PlPnPlPdPcP<P\PrPxPwPqPLPKPvPMPtPs1REgPoP3P2ND0?PCPiP7PkP3PlPjK0APC%MbR~1KCi7laPiPl1m11RiP1P1PgQ01#@R>,3gCsP1P1&03bR@&0=b,3@Cs%ri5Ti3TPkP3K0I1KC7P3PgP9P4D}%^9%^bRG%_9%_bR{%k9%kb&039%>~%M7#>[%M9#>#h%j9%jb&009&00b%q9%qb';3D3D[%??#?#?#7#[#?#7#[#[#@R?13G>'813{>,8?'NA2I7eA2J9b'5[397D@3D3D3D3939XpH,WHXq`P9I0<%YiRi1KC4P0PifGRi#^/3>,t?%_i/3>,t?+0;1KCnR?%M2%Mi?l^?80U3n010000002000032g00kF,m1#Y20:C420:Cn3211C411Cn';209CnQ05'i209C4'43939XjJ,WJZ0@I,WIZ0CD,WDWh60d5P3A<E<ARA#>PlPcPhPfP_P<P\P[PXP:PyPSP=PWPuPrPxPwPqPLPKPvPMPtPsPmPzPNPpPoP;PkPjPgP8PePbPaPiP^P]fDRlfCREPYQ04PVQ02f>R5PUf<RDPRPTPPPOf7RIP3PZP6P7P9OkW1P3O11;ABPdPcPhPfP_P<P\P[PXP:PyPSP=PWPuPrPxPwPqPLPKPvPMPtPsPmPzPNPpPoP;PkPjPgP8PePbPaPiP^P]PlPEPYQ04PVQ02P5PUPDPRPTPPPOPIP3PZP6P7P9OkW1P3O1n200100001021000010000b1WHWNWLW=WMWRWJWOX<QX;QW:W9WQWIW?WxWiY0?Z0A1Xm1Xr1Xn1WoWkW>Z0=FZ0<FZ0;FZ0:FX|FX{FZ05FZ04FZ03FZ02FZ01FZ00FX~FX}FXgFXfFXeFXdFXcFXbFXaFX`FXzFXyFZ09FZ08FZ07FZ0>FXlFZ06FWwWKY0B&0cCeWAW2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixAddBorder32_rows_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (rcs : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 32 -> a2 = Z_to_bv 64 0 ->
  pix1rc (rt_live RT Σ) m pixs vs cvs rcs -> 1 <= rcs <= 2 ->
  uctx m sp s0 ras -> In (PMCOPY_CALLOC1 :: RA_ABG_CMAP :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 9 4 (RC1 + 8) -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
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
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RC1 + 8) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixRemoveBorder32_rows_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs : Z) (vs : pixv) (cvs : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pixs -> a1 = Z_to_bv 64 32 ->
  pix1c (rt_live RT Σ) m pixs vs cvs -> 65 <= p_w vs -> 65 <= p_h vs ->
  uctx m sp s0 ras -> In (PMCOPY_CALLOC1 :: RA_RBG_CMAP :: bv_unsigned ra :: ras) CLIENT_TRACES ->
  lenv RT Σ m sp lo (LSTK 9) -> lres RT Σ 9 4 RC1 -> sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixRemoveBorder m)))
    (rembg_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo pixs vs cvs).

End CSC_DEFS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CSC_CUT.
Variable RT : rt_sig.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gp : word) (F : bvmap 5 word)
          (usp lo : Z) (m : mem) (pix1 hs vs : Z) (v : pixv) (cv : cmapv) (ras : list Z).

(* [comment removed for export] *)
Definition csc_PF0 : Z -> Prop := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a.
Definition csc_PF : Z -> Prop :=
  fun a => aclient (cmap_rm_live (p_cmap v) cv (rt_live RT Σ)) (rt_frames RT Σ) usp a /\ outside [(pix1, pix1 + 64); (p_data v, p_data v + rsize v)] a.

(* [comment removed for export] *)
Definition csc_ctx : Prop :=
  fdfs_only PMc /\ mat_stable PMc /\ ART RT Σ m
  /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + LSTK 13 <= usp /\ 0 <= lo
  /\ usp + 16 <= USTACK_TOP /\ usp mod 16 = 0 /\ usp <= rt_sp0 RT Σ
  /\ Z.of_nat (length (rt_frames RT Σ)) + 11 <= Z.of_nat FRAMES_MAX /\ Z.of_nat (length (rt_live RT Σ)) + 40 <= LIVE_MAX
  /\ CSC_COST <= rt_credit RT Σ /\ (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n)
  /\ ((hs = 1 /\ vs = 8) \/ (hs = 30 /\ vs = 1))
  /\ pix1c (rt_live RT Σ) m pix1 v cv
  /\ po_rows e_pixCloseSafeCompBrick ra ras /\ 4096 <= bv_unsigned ra < 2^64 /\ chain_ok m usp (bv_unsigned s0) ras
  /\ sec_bytes (rt_live RT Σ) + CSC_SECB <= SEC_BYTES /\ LIB_PO m.

(* [comment removed for export] *)
Definition csc_Q : config -> Prop :=
  csc_post RT Σ PMc ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo pix1 v cv.

(* [comment removed for export] *)
Definition csc_LS (sel1 sel2 : Z) (sv1 sv2 : selv) : list (Z * Z) := sel_new_live sel2 sv2 (sel_new_live sel1 sv1 (rt_live RT Σ)).

(* [comment removed for export] *)
Definition csc_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition csc_fhdrF (j24 : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 csc_descr); C8 (Z_to_bv 64 csc_epc); CB 104 j24].
Definition csc_fhdr (jh : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 csc_descr); C8 (Z_to_bv 64 csc_epc); CB 8 jh].

(* [comment removed for export] *)
Definition csc_frameT_0 (fr : Z) (j8 j64 : list byte) : list cell :=
  [C8 (Z_to_bv 64 0); CB 8 j8; C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 (fr + 224)); C8 (Z_to_bv 64 (fr + 32)); C8 (Z_to_bv 64 (fr + 192));
   C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 (fr + 160)); CB 16 j64; C8 (Z_to_bv 64 fr);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition csc_frameF_0 (fr : Z) (j8 j32 j64 : list byte) : list cell :=
  [C8 (Z_to_bv 64 0); CB 8 j8; C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 (fr + 224)); CB 8 j32; C8 (Z_to_bv 64 (fr + 192));
   C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 (fr + 160)); CB 16 j64; C8 (Z_to_bv 64 fr);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition csc_frameT_16 (fr : Z) (j0 j64 j88 : list byte) : list cell :=
  [CB 16 j0; C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 (fr + 224)); C8 (Z_to_bv 64 (fr + 32)); C8 (Z_to_bv 64 (fr + 192));
   C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 (fr + 160)); CB 16 j64; C8 (Z_to_bv 64 fr); CB 16 j88;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition csc_frameF_16 (fr : Z) (j0 j32 j64 j88 : list byte) : list cell :=
  [CB 16 j0; C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 (fr + 224)); CB 8 j32; C8 (Z_to_bv 64 (fr + 192));
   C8 (Z_to_bv 64 (fr + 128)); C8 (Z_to_bv 64 (fr + 160)); CB 16 j64; C8 (Z_to_bv 64 fr); CB 16 j88;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition cmap_inh (vs : pixv) (cvs : cmapv) (vd : pixv) (cvd : cmapv) : Prop :=
  (p_cmap vs = 0 -> p_cmap vd = 0) /\ (p_cmap vd <> 0 -> c_n cvd = c_n cvs /\ c_nalloc cvd = c_nalloc cvs /\ c_depth cvd = c_depth cvs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csc_cutT_0 (QF : config -> Prop) : Prop :=
  forall (S : rts RT) (mt : mem) (fr : Z) (Ft : bvmap 5 word) (fct : bv 32)
         (sel1 sel2 pixsb pixt pixdb x128 x160 x192 x224 : Z) (sv1 sv2 : selv) (vb vt vdb : pixv) (cvb cvt cvdb : cmapv)
         (jh j8 j64 j40 j72 j104 j136 j168 j200 j232 : list byte)
         (rat t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S mt -> mem_inv asegs mt -> stk asegs mt lo (usp + -192) -> LIBH mt -> io_ssp mt ->
    rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_live RT S = pix_copy_live pixdb vdb cvdb (pix_copy_live pixt vt cvt (pix_copy_live pixsb vb cvb (csc_LS sel1 sel2 sv1 sv2))) ->
    (forall p n, In (p, n) (rt_live RT S) -> 0 < n) ->
    rt_credit RT Σ - (3 * RC1 + 11 + 2 * 2^8 + 2 * 2^8) <= rt_credit RT S ->
    agree_on csc_PF0 m mt -> fs_agree F Ft ->
    (* [comment removed for export] *)
    rw_cells asegs mt (usp + -192) (csc_frameT_0 fr j8 j64) ->
    rw_cells asegs mt fr (csc_fhdr jh) ->
    rw_cells asegs mt (fr + 32) [C8 (Z_to_bv 64 pixsb)] -> rw_cells asegs mt (fr + 40) [CB 24 j40] ->
    rw_cells asegs mt (fr + 64) [C8 (Z_to_bv 64 pixt)] -> rw_cells asegs mt (fr + 72) [CB 24 j72] ->
    rw_cells asegs mt (fr + 96) [C8 (Z_to_bv 64 pixdb)] -> rw_cells asegs mt (fr + 104) [CB 24 j104] ->
    rw_cells asegs mt (fr + 128) [C8 (Z_to_bv 64 x128)] -> rw_cells asegs mt (fr + 136) [CB 24 j136] ->
    rw_cells asegs mt (fr + 160) [C8 (Z_to_bv 64 x160)] -> rw_cells asegs mt (fr + 168) [CB 24 j168] ->
    rw_cells asegs mt (fr + 192) [C8 (Z_to_bv 64 x192)] -> rw_cells asegs mt (fr + 200) [CB 24 j200] ->
    rw_cells asegs mt (fr + 224) [C8 (Z_to_bv 64 x224)] -> rw_cells asegs mt (fr + 232) [CB 16 j232] ->
    rw_cells asegs mt (fr / 8 + 2147450880) csc_shadow ->
    (* [comment removed for export] *)
    ((hs = 30 /\ x128 = sel1 /\ x160 = sel2 /\ x192 = 0 /\ x224 = 0) \/ (hs = 1 /\ x128 = 0 /\ x160 = 0 /\ x192 = sel1 /\ x224 = sel2)) ->
    sel_obj (rt_live RT S) mt sel1 sv1 -> sel_obj (rt_live RT S) mt sel2 sv2 -> dil_selp sv1 -> dil_selp sv2 ->
    List.NoDup (sel_chunks sel1 sv1 ++ sel_chunks sel2 sv2) ->
    (* [comment removed for export] *)
    pix1c (rt_live RT S) mt pix1 v cv ->
    ~ (20000 < p_w v + 64 \/ 20000 < p_h v + 64) -> pixsb <> 0 -> pixt <> 0 -> pixdb <> 0 ->
    pix1c (rt_live RT S) mt pixsb vb cvb -> p_w vb = p_w v + 64 -> p_h vb = p_h v + 64 -> cmap_inh v cv vb cvb ->
    List.NoDup (pix_chunks pixsb vb cvb ++ pix_chunks pix1 v cv) ->
    pix1c (rt_live RT S) mt pixt vt cvt -> p_w vt = p_w vb -> p_h vt = p_h vb -> cmap_inh vb cvb vt cvt ->
    List.NoDup (pix_chunks pixt vt cvt ++ pix_chunks pixsb vb cvb) ->
    pix1c (rt_live RT S) mt pixdb vdb cvdb -> p_w vdb = p_w vt -> p_h vdb = p_h vt -> cmap_inh vt cvt vdb cvdb ->
    List.NoDup (pix_chunks pixdb vdb cvdb ++ pix_chunks pixt vt cvt) ->
    cps asegs (ASTA RT S PMc (eq (entry_st rat (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 pix1) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 224)) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64))
                                    (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 pixt) (Z_to_bv 64 pixdb) (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 (fr + 96))
                                    t3 t4 t5 t6 Ft fct csc_t mt))) QF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csc_cutF_0 (h30 : bool) (QF : config -> Prop) : Prop :=
  forall (S : rts RT) (mc : mem) (fr : Z) (Fc : bvmap 5 word) (fcc : bv 32)
         (sel1 sel2 pixsb : Z) (sv1 sv2 : selv) (vb : pixv) (cvb : cmapv)
         (j8 j32 j64 j24 j136 j168 j200 j232 : list byte)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -192) -> LIBH mc -> io_ssp mc ->
    rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_live RT S = (if pixsb =? 0 then csc_LS sel1 sel2 sv1 sv2 else pix_copy_live pixsb vb cvb (csc_LS sel1 sel2 sv1 sv2)) ->
    (forall p n, In (p, n) (rt_live RT S) -> 0 < n) ->
    rt_credit RT Σ - (RC1 + 11) <= rt_credit RT S ->
    agree_on csc_PF0 m mc -> fs_agree F Fc ->
    rw_cells asegs mc (usp + -192) (csc_frameF_0 fr j8 j32 j64) ->
    rw_cells asegs mc fr (csc_fhdrF j24) ->
    rw_cells asegs mc (fr + 128) [C8 (Z_to_bv 64 (if h30 then sel1 else 0))] -> rw_cells asegs mc (fr + 136) [CB 24 j136] ->
    rw_cells asegs mc (fr + 160) [C8 (Z_to_bv 64 (if h30 then sel2 else 0))] -> rw_cells asegs mc (fr + 168) [CB 24 j168] ->
    rw_cells asegs mc (fr + 192) [C8 (Z_to_bv 64 (if h30 then 0 else sel1))] -> rw_cells asegs mc (fr + 200) [CB 24 j200] ->
    rw_cells asegs mc (fr + 224) [C8 (Z_to_bv 64 (if h30 then 0 else sel2))] -> rw_cells asegs mc (fr + 232) [CB 16 j232] ->
    rw_cells asegs mc (fr / 8 + 2147450880) csc_shadow ->
    (if h30 then hs = 30 /\ vs = 1 /\ brick_h6 sv1 /\ comb_h30 sv2 else hs = 1 /\ vs = 8 /\ brick_v4 sv1 /\ comb_v8 sv2) ->
    sel_obj (rt_live RT S) mc sel1 sv1 -> sel_obj (rt_live RT S) mc sel2 sv2 ->
    List.NoDup (sel_chunks sel1 sv1 ++ sel_chunks sel2 sv2) ->
    pix1c (rt_live RT S) mc pix1 v cv ->
    (pixsb = 0 <-> (20000 < p_w v + 64 \/ 20000 < p_h v + 64)) ->
    (pixsb <> 0 -> pix1c (rt_live RT S) mc pixsb vb cvb /\ p_w vb = p_w v + 64 /\ p_h vb = p_h v + 64
                   /\ (p_cmap v = 0 -> p_cmap vb = 0) /\ (p_cmap vb <> 0 -> c_n cvb = c_n cv /\ c_nalloc cvb = c_nalloc cv /\ c_depth cvb = c_depth cv)
                   /\ List.NoDup (pix_chunks pixsb vb cvb ++ pix_chunks pix1 v cv)) ->
    cps asegs (ASTA RT S PMc (eq (entry_st (Z_to_bv 64 csc_f) (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 pixsb) a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 pix1) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64))
                                    (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 hs) (Z_to_bv 64 vs) (Z_to_bv 64 pix1) (Z_to_bv 64 (fr + 96))
                                    t3 t4 t5 t6 Fc fcc csc_f mc))) QF.
Definition csc_cutF30_0 := csc_cutF_0 true.
Definition csc_cutF8_0 := csc_cutF_0 false.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition csc_cutR_0 (h30 : bool) (QF : config -> Prop) : Prop :=
  forall (S : rts RT) (mc : mem) (fr : Z) (Fc : bvmap 5 word) (fcc : bv 32)
         (sel1 sel2 : Z) (sv1 sv2 : selv)
         (j8 j32 j64 j24 j136 j168 j200 j232 : list byte)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -192) -> LIBH mc -> io_ssp mc ->
    rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_live RT S = csc_LS sel1 sel2 sv1 sv2 ->
    (forall p n, In (p, n) (rt_live RT S) -> 0 < n) ->
    rt_credit RT Σ - (RC1 + 11) <= rt_credit RT S ->
    agree_on csc_PF0 m mc -> fs_agree F Fc ->
    rw_cells asegs mc (usp + -192) (csc_frameF_0 fr j8 j32 j64) ->
    rw_cells asegs mc fr (csc_fhdrF j24) ->
    rw_cells asegs mc (fr + 128) [C8 (Z_to_bv 64 (if h30 then sel1 else 0))] -> rw_cells asegs mc (fr + 136) [CB 24 j136] ->
    rw_cells asegs mc (fr + 160) [C8 (Z_to_bv 64 (if h30 then sel2 else 0))] -> rw_cells asegs mc (fr + 168) [CB 24 j168] ->
    rw_cells asegs mc (fr + 192) [C8 (Z_to_bv 64 (if h30 then 0 else sel1))] -> rw_cells asegs mc (fr + 200) [CB 24 j200] ->
    rw_cells asegs mc (fr + 224) [C8 (Z_to_bv 64 (if h30 then 0 else sel2))] -> rw_cells asegs mc (fr + 232) [CB 16 j232] ->
    rw_cells asegs mc (fr / 8 + 2147450880) csc_shadow ->
    (if h30 then hs = 30 /\ vs = 1 /\ brick_h6 sv1 /\ comb_h30 sv2 else hs = 1 /\ vs = 8 /\ brick_v4 sv1 /\ comb_v8 sv2) ->
    sel_obj (rt_live RT S) mc sel1 sv1 -> sel_obj (rt_live RT S) mc sel2 sv2 ->
    List.NoDup (sel_chunks sel1 sv1 ++ sel_chunks sel2 sv2) ->
    pix1c (rt_live RT S) mc pix1 v cv ->
    (20000 < p_w v + 64 \/ 20000 < p_h v + 64) ->
    cps asegs (ASTA RT S PMc (eq (entry_st (Z_to_bv 64 csc_f) (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 pix1) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64))
                                    (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 hs) (Z_to_bv 64 vs) (Z_to_bv 64 pix1) (Z_to_bv 64 (fr + 96))
                                    t3 t4 t5 t6 Fc fcc csc_f mc))) QF.

(* [comment removed for export] *)
Definition csc_cutT_16 (QF : config -> Prop) : Prop :=
  forall (S : rts RT) (mt : mem) (fr : Z) (Ft : bvmap 5 word) (fct : bv 32)
         (sel1 sel2 pixsb pixt pixdb x128 x160 x192 x224 : Z) (sv1 sv2 : selv) (vb vt vdb : pixv) (cvb cvt cvdb : cmapv)
         (jh j0 j64 j88 j40 j72 j104 j136 j168 j200 j232 : list byte)
         (rat t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S mt -> mem_inv asegs mt -> stk asegs mt lo (usp + -208) -> LIBH mt -> io_ssp mt ->
    rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_live RT S = pix_copy_live pixdb vdb cvdb (pix_copy_live pixt vt cvt (pix_copy_live pixsb vb cvb (csc_LS sel1 sel2 sv1 sv2))) ->
    (forall p n, In (p, n) (rt_live RT S) -> 0 < n) ->
    rt_credit RT Σ - (3 * RC1 + 11 + 2 * 2^8 + 2 * 2^8) <= rt_credit RT S ->
    agree_on csc_PF0 m mt -> fs_agree F Ft ->
    (* [comment removed for export] *)
    rw_cells asegs mt (usp + -208) (csc_frameT_16 fr j0 j64 j88) ->
    rw_cells asegs mt fr (csc_fhdr jh) ->
    rw_cells asegs mt (fr + 32) [C8 (Z_to_bv 64 pixsb)] -> rw_cells asegs mt (fr + 40) [CB 24 j40] ->
    rw_cells asegs mt (fr + 64) [C8 (Z_to_bv 64 pixt)] -> rw_cells asegs mt (fr + 72) [CB 24 j72] ->
    rw_cells asegs mt (fr + 96) [C8 (Z_to_bv 64 pixdb)] -> rw_cells asegs mt (fr + 104) [CB 24 j104] ->
    rw_cells asegs mt (fr + 128) [C8 (Z_to_bv 64 x128)] -> rw_cells asegs mt (fr + 136) [CB 24 j136] ->
    rw_cells asegs mt (fr + 160) [C8 (Z_to_bv 64 x160)] -> rw_cells asegs mt (fr + 168) [CB 24 j168] ->
    rw_cells asegs mt (fr + 192) [C8 (Z_to_bv 64 x192)] -> rw_cells asegs mt (fr + 200) [CB 24 j200] ->
    rw_cells asegs mt (fr + 224) [C8 (Z_to_bv 64 x224)] -> rw_cells asegs mt (fr + 232) [CB 16 j232] ->
    rw_cells asegs mt (fr / 8 + 2147450880) csc_shadow ->
    (* [comment removed for export] *)
    ((hs = 30 /\ x128 = sel1 /\ x160 = sel2 /\ x192 = 0 /\ x224 = 0) \/ (hs = 1 /\ x128 = 0 /\ x160 = 0 /\ x192 = sel1 /\ x224 = sel2)) ->
    sel_obj (rt_live RT S) mt sel1 sv1 -> sel_obj (rt_live RT S) mt sel2 sv2 -> dil_selp sv1 -> dil_selp sv2 ->
    List.NoDup (sel_chunks sel1 sv1 ++ sel_chunks sel2 sv2) ->
    (* [comment removed for export] *)
    pix1c (rt_live RT S) mt pix1 v cv ->
    ~ (20000 < p_w v + 64 \/ 20000 < p_h v + 64) -> pixsb <> 0 -> pixt <> 0 -> pixdb <> 0 ->
    pix1c (rt_live RT S) mt pixsb vb cvb -> p_w vb = p_w v + 64 -> p_h vb = p_h v + 64 -> cmap_inh v cv vb cvb ->
    List.NoDup (pix_chunks pixsb vb cvb ++ pix_chunks pix1 v cv) ->
    pix1c (rt_live RT S) mt pixt vt cvt -> p_w vt = p_w vb -> p_h vt = p_h vb -> cmap_inh vb cvb vt cvt ->
    List.NoDup (pix_chunks pixt vt cvt ++ pix_chunks pixsb vb cvb) ->
    pix1c (rt_live RT S) mt pixdb vdb cvdb -> p_w vdb = p_w vt -> p_h vdb = p_h vt -> cmap_inh vt cvt vdb cvdb ->
    List.NoDup (pix_chunks pixdb vdb cvdb ++ pix_chunks pixt vt cvt) ->
    cps asegs (ASTA RT S PMc (eq (entry_st rat (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208)) a0 a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 pix1) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 224)) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64))
                                    (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 pixt) (Z_to_bv 64 pixdb) (Z_to_bv 64 (fr + 128)) (Z_to_bv 64 (fr + 96))
                                    t3 t4 t5 t6 Ft fct csc_t mt))) QF.

Definition csc_cutF_16 (h30 : bool) (QF : config -> Prop) : Prop :=
  forall (S : rts RT) (mc : mem) (fr : Z) (Fc : bvmap 5 word) (fcc : bv 32)
         (sel1 sel2 pixsb : Z) (sv1 sv2 : selv) (vb : pixv) (cvb : cmapv)
         (j0 j32 j64 j88 j24 j136 j168 j200 j232 : list byte)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -208) -> LIBH mc -> io_ssp mc ->
    rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_live RT S = (if pixsb =? 0 then csc_LS sel1 sel2 sv1 sv2 else pix_copy_live pixsb vb cvb (csc_LS sel1 sel2 sv1 sv2)) ->
    (forall p n, In (p, n) (rt_live RT S) -> 0 < n) ->
    rt_credit RT Σ - (RC1 + 11) <= rt_credit RT S ->
    agree_on csc_PF0 m mc -> fs_agree F Fc ->
    rw_cells asegs mc (usp + -208) (csc_frameF_16 fr j0 j32 j64 j88) ->
    rw_cells asegs mc fr (csc_fhdrF j24) ->
    rw_cells asegs mc (fr + 128) [C8 (Z_to_bv 64 (if h30 then sel1 else 0))] -> rw_cells asegs mc (fr + 136) [CB 24 j136] ->
    rw_cells asegs mc (fr + 160) [C8 (Z_to_bv 64 (if h30 then sel2 else 0))] -> rw_cells asegs mc (fr + 168) [CB 24 j168] ->
    rw_cells asegs mc (fr + 192) [C8 (Z_to_bv 64 (if h30 then 0 else sel1))] -> rw_cells asegs mc (fr + 200) [CB 24 j200] ->
    rw_cells asegs mc (fr + 224) [C8 (Z_to_bv 64 (if h30 then 0 else sel2))] -> rw_cells asegs mc (fr + 232) [CB 16 j232] ->
    rw_cells asegs mc (fr / 8 + 2147450880) csc_shadow ->
    (if h30 then hs = 30 /\ vs = 1 /\ brick_h6 sv1 /\ comb_h30 sv2 else hs = 1 /\ vs = 8 /\ brick_v4 sv1 /\ comb_v8 sv2) ->
    sel_obj (rt_live RT S) mc sel1 sv1 -> sel_obj (rt_live RT S) mc sel2 sv2 ->
    List.NoDup (sel_chunks sel1 sv1 ++ sel_chunks sel2 sv2) ->
    pix1c (rt_live RT S) mc pix1 v cv ->
    (pixsb = 0 <-> (20000 < p_w v + 64 \/ 20000 < p_h v + 64)) ->
    (pixsb <> 0 -> pix1c (rt_live RT S) mc pixsb vb cvb /\ p_w vb = p_w v + 64 /\ p_h vb = p_h v + 64
                   /\ (p_cmap v = 0 -> p_cmap vb = 0) /\ (p_cmap vb <> 0 -> c_n cvb = c_n cv /\ c_nalloc cvb = c_nalloc cv /\ c_depth cvb = c_depth cv)
                   /\ List.NoDup (pix_chunks pixsb vb cvb ++ pix_chunks pix1 v cv)) ->
    cps asegs (ASTA RT S PMc (eq (entry_st (Z_to_bv 64 csc_f) (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208)) (Z_to_bv 64 pixsb) a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 pix1) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64))
                                    (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 hs) (Z_to_bv 64 vs) (Z_to_bv 64 pix1) (Z_to_bv 64 (fr + 96))
                                    t3 t4 t5 t6 Fc fcc csc_f mc))) QF.

Definition csc_cutR_16 (h30 : bool) (QF : config -> Prop) : Prop :=
  forall (S : rts RT) (mc : mem) (fr : Z) (Fc : bvmap 5 word) (fcc : bv 32)
         (sel1 sel2 : Z) (sv1 sv2 : selv)
         (j0 j32 j64 j88 j24 j136 j168 j200 j232 : list byte)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ART RT S mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -208) -> LIBH mc -> io_ssp mc ->
    rt_frames RT S = (fr, 2%nat) :: rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
    rt_live RT S = csc_LS sel1 sel2 sv1 sv2 ->
    (forall p n, In (p, n) (rt_live RT S) -> 0 < n) ->
    rt_credit RT Σ - (RC1 + 11) <= rt_credit RT S ->
    agree_on csc_PF0 m mc -> fs_agree F Fc ->
    rw_cells asegs mc (usp + -208) (csc_frameF_16 fr j0 j32 j64 j88) ->
    rw_cells asegs mc fr (csc_fhdrF j24) ->
    rw_cells asegs mc (fr + 128) [C8 (Z_to_bv 64 (if h30 then sel1 else 0))] -> rw_cells asegs mc (fr + 136) [CB 24 j136] ->
    rw_cells asegs mc (fr + 160) [C8 (Z_to_bv 64 (if h30 then sel2 else 0))] -> rw_cells asegs mc (fr + 168) [CB 24 j168] ->
    rw_cells asegs mc (fr + 192) [C8 (Z_to_bv 64 (if h30 then 0 else sel1))] -> rw_cells asegs mc (fr + 200) [CB 24 j200] ->
    rw_cells asegs mc (fr + 224) [C8 (Z_to_bv 64 (if h30 then 0 else sel2))] -> rw_cells asegs mc (fr + 232) [CB 16 j232] ->
    rw_cells asegs mc (fr / 8 + 2147450880) csc_shadow ->
    (if h30 then hs = 30 /\ vs = 1 /\ brick_h6 sv1 /\ comb_h30 sv2 else hs = 1 /\ vs = 8 /\ brick_v4 sv1 /\ comb_v8 sv2) ->
    sel_obj (rt_live RT S) mc sel1 sv1 -> sel_obj (rt_live RT S) mc sel2 sv2 ->
    List.NoDup (sel_chunks sel1 sv1 ++ sel_chunks sel2 sv2) ->
    pix1c (rt_live RT S) mc pix1 v cv ->
    (20000 < p_w v + 64 \/ 20000 < p_h v + 64) ->
    cps asegs (ASTA RT S PMc (eq (entry_st (Z_to_bv 64 csc_f) (Z_to_bv 64 (usp + -208)) gp (Z_to_bv 64 TP_A) t0 t1 t2
                                    (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -208)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 pix1) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 fr) (Z_to_bv 64 (fr + 64))
                                    (Z_to_bv 64 (fr / 8 + 2147450880)) (Z_to_bv 64 hs) (Z_to_bv 64 vs) (Z_to_bv 64 pix1) (Z_to_bv 64 (fr + 96))
                                    t3 t4 t5 t6 Fc fcc csc_f mc))) QF.
Definition csc_cutF30_16 := csc_cutF_16 true.
Definition csc_cutF8_16 := csc_cutF_16 false.

End CSC_CUT.
