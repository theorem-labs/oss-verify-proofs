(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PropExec StoreOk Hoare AgentLib.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS23 Require Import AsanTablesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanPlanSoundSums.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS23 Require Import AsanPlanImages.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require AsanHeapSortDef AsanHeapSort.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanHeapSortA () := "C47Corelib7Classes?RelationClasses9ReflexiveI47Corelib4Init9Datatypes4list00c69OSSVerify5KrLib2K54AS23=AsanHeapSortA;hs_code_okbC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addI47Corelib4Init5Logic3and00C46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib5Lists7ListDef3nthC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K52AS?AsanHeapSortDef8HS_WORDSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib2K52AS?AsanHeapSortDef4HS_NC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C79OSSVerify5KrLib2K52AS8AsanPlan2AP7x_hsortC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23;AsanTablesA6ASAN_AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3powc69OSSVerify5KrLib2K54AS23=AsanHeapSortAAhs_code_okb_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<AsanHeapSortBhsort_spec_of_codeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03c69OSSVerify5KrLib2K54AS23=AsanHeapSortA@asan_hs_code_allC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52ASAAsanPlanSoundSums4APSXFnode_x_sound_XHeapSortC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23>AsanPlanImages7asan_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23>AsanPlanImages<asan_in_hullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23>AsanPlanImages<asan_hull_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS23=AsanHeapSortA?asan_hsort_specC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition hs_code_okb (segs : list Segment) (p : Z) : bool :=
  forallb (fun k => match fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat k)) with
                    | Some w => Z.eqb (bv_unsigned w) (bv_unsigned (nth k AsanHeapSortDef.HS_WORDS (Z_to_bv 32 0)))
                    | None => false
                    end) (seq 0 AsanHeapSortDef.HS_N).

Lemma hs_code_okb_sound : forall segs p, hs_code_okb segs p = true ->
  forall k, (k < AsanHeapSortDef.HS_N)%nat ->
  fetch_word segs (Z_to_bv 64 (p + 4 * Z.of_nat k)) = Some (nth k AsanHeapSortDef.HS_WORDS (Z_to_bv 32 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanHeapSortA ()) [] "p'0h01Hh11nh21kh32H0h44__x1h54__x2h62b1h72b2h83lenh91mh:5starth;1xi001xh<2Hkh=3Hk0h>7__arithh?4__ffh@8__varmaphA5__withB4cstrhC5cstr0hD1ehE5lemmahF1oi011ohG1phH4segshI1wi021wi031bp;1p;2p;3p;6p;4p;7p;8p;<p;Bp-1p10000p4p710p9g000\j1OTg001<j2uTg002BR0j2<Tg002Zj1:Tg003?j1KTg003]j15Tg004@j1]Tg004^R1j17Tg005>j2CTg005[R2j22Tg0068j24Tg006^j29Tg007`j21Tg008Jj2?Tg008gj2ATg009Cj3JTg009_j3BTg00:6j2aTg00:Oj3_Tg00;@j3^Tg00;cR3j2GTg00<=j2DTg00<TR4j2=Tg00<oj3ZTg00=JR5j2;Tg00=fR6j2@Tg00>Bj2>Tg00>\j6VTg00?Ej4RTg00?lj1ITg00@Qj1QTg00A1j2PTg00AOj1STg00Amj4TTg00BKj1tTg00Bij1sTg00CTj2rTg00D7j2NTg00DZj4HTg00EEj1MTg00Egj3pTg00FJj7oTg00Fnj2hTg00GPj2gTg00H<j3fTg00H[j4eTg00IMj4dTg00J8R7j1bTg00JZj2cj1iTg00K<j33Tg00KVj2`Tg00L6j3jTg00LZj8kTg00M7j6lTg00MSj2mTg00N2j4nTg00NNl<FTg00O3lB\Tg00OYj7[Tg00P=j8qTg00PaR8f0R9g00QAR:33p=0f2R;f1R<g00QaP9Cnp=8g00RdR=g00SCR>P3P1P5g00Sag00TCR5g00TbR3f3R?P;P<P9M<Fp=YP=P=P=P>P>P>g00U@P1P1P1P2g00U`P5P3P;g00VCR2P<P9MB\p=XP=P>P0P1P6g00WBR@f5RAf4RBP?P;P<P9M<Fp=WP=P>P0P1P6P@PBP?P;P2P<P9M<Fp=UP<g00WdR@g00XCR6P6g00XcR1P9g00YCF[p=EP?P@P6P6P1P;P<P9Gqp=LA3><9p=6g00Yc#O1u<9#01<92P7g00ZbR0#:RC#:RD#:#:#:RE#KRF#5RGP8%:E#KRE%]DRD%79'CRH,2B'4,9A11F9RI14F3RJ98G<,1F'?RKg00[GRLn10110000021010200X2=RM1A52RN5J=#0AB=9NROP7PGP8f7RPf6RQ/2H,4E'9PKPLn10110000021010200X2=P<O1#0[^;=RR'aP7PGP812AH,4E,9QPKPLn10110000021010200X2==J=N#0P7PGP8f8RS12PH,4E'9PKPLn10110000021010200X2=P<O1#0\O^;=;_9WEA^=MNP;O2PRP9P;P41A<;9B=91G;<1D;?,<<'=RR[1G<91D<;,<9'=1A;?9B=<[RN1A?B9B=;\RAZ;<9P9n2001000000120000000X1=X:=X8=PN^1=^:=^8=P9P2P5P?1G5?RN1D52R5,<?RR'=%7?RM,;3RO%72RK,23RH,@MRT'=PNPRPOPT1>>3RTP?PM1>>MROCYP?PMPOP5PH1>>KRH9XTKEWEV1<?21@MKRTP?PMPOPKPHDUP;CRPT%IB%7B,;3%I21;3Kg00[gR2#Q%O2P>1P>;P<%S>CT%t>%s>R2P>1r>3RTg00\S1N>0R0CH,E2RH%M6ROP2P>P0g00]:R51N>CRCCH,E2POP2P@P6P6P1PHP>P0P5Ap>TCCH,E2FoCLCL1h21P9P;1>8:1g9;#0dAf>3<Ceb?b@bAX4>X5>1;391@<;1;3;123?,@;'=[[^4>^5>P9PK%7PP;P?O4b>bCbBb=CdO4b3O2P7PGP8%7;,CD,2B,4E,9AA8G?J,1F,?IPLn10110000021010200#01CDM,2A,4E,9Q%bGREP7PGP7PGP8P9A8GQJRQ,1F,?IRIPLn10110000021010200#01cGQRQ93E<]0P9%0IP41?<9#016;<[RI16<91?;<#0R7[16?;\71`<9P<n2001000000120000000X9>X1>PI^9>^1>P911F;RIA8GSJ,1FRSP<O316ISPGPE%iGRSPSP?f9=8GJPE\G/>Sg00]aRS%59RI%5<R7P4%5;?3<911?;11?<'6R4[11;<11;9'6%5??3;<[RA%5B?3?;\4Aj;<9P9n2001000000120000000W7W6W1PA^77^6I^1SP9PFPBf:=8GJP<O4b3Gkb0b3W0XIGP9O1A38L:P8PLP8p-0P9g00^?RLg00^\n0110300020000XD8g00_8P:P9ElPL%MG=3EQ/m9b3W0n10110100021110300P<O1bFb0b0W<X2=W0XG>WHo"). Qed.

Lemma asan_hs_code_all : hs_code_okb ASEGS (AP.x_hsort ASAN_A) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanHeapSortA ()) [] "p;2p;1p;3g00>Bj23Tg00_Tj12Tg001<j20Tg00K<j31Tg00PaR0g00QAR1'3g00`Rg00aS#2'0=101do"). Qed.

Theorem asan_hsort_spec : AsanHeapSort.hsort_spec ASEGS (AP.x_hsort ASAN_A).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanHeapSortA ()) [] "p'0h01Hh11eh21xi001cp;1p;3p;6p;2p;5g00_Tj1@Tg00K<j3?Tg00M7j6;Tg00MSj28Tg00=Jj24Tg002Zj11Tg004@j13Tg00bRj10Tg004^j15Tg005>j26Tg005[j27Tg00c1j2>Tg00cNj3=Tg00dZj5<Tf0R0#0#0p=:%00#0#0#0p=9%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=2g00`RR1g00aS#@R2g00edR3g00fJR4g00g0R53?P3P4P3p-0P0g00^?R4g00^\P4n011000003000000X13g00_8P5P0E;P41840b0W2R4g00Tb/42dP4g00Zb#1R4#1R0#3R5g00TC#0#:#9#2#2#2#2#2#5'6,72%34%10#1#1#1#3'>R0'4dg00VC#5,65,72/40eg00gV9=12D<o"). Qed.

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> AP.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

Theorem asan_node_x_sound_XHeapSort : APS.x_stmt ASEGS ASAN_A nx0 LIMIT SINV argH FS0 AP.XHeapSort.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanHeapSortA ()) ["AsanNodes"] "p;?g00hal?0Tg00`Rg00aSf0f1g00j9g00k<g00lDf2f3f4f5f6f7f8g00mLM?0p=1p,3nx0p,5LIMITp,4SINVp,4argHp,9argH_highp,:argH_agreep,:SINV_framep,:SINV_agreep,3FS0M91o"). Qed.
End AsanNodes.
