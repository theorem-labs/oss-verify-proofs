(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2StartupDefs () := "C47Corelib7Program6Basics4flipK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Peano2le00c5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs@after_last_slashC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib7Classes?RelationClassesCPreOrder_TransitiveK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib7Classes?RelationClasses<transitivityK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib5Arith8PeanoNat3Nat;le_preorderc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefsCafter_last_slash_leC46Stdlib9micromega;ZifyClasses:impl_morphc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs<progname_offC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs2RBC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List@firstn_length_leK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201c5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs9length_RBc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs3rbac5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs3rbbC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4v_lwC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission6Common7CatExecDlength_N_to_le_bytesC46Stdlib5Lists4List:length_appc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs3rwac5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs3rwbc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs;guard_bytesC5ARocqVerifyHarness?AgentSubmission6Common8PropExecCbytes_le_to_Z_boundC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission6Common8PropExecDbytes_le_to_Z_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00c5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs9bytes_valc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs:length_rbac5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs:length_rbbc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefsBlength_guard_bytesc5ARocqVerifyHarness?AgentSubmission2V2=V2StartupDefs8canary_wI47Corelib4Init9Datatypes6option00C47Corelib7Classes?RelationClasses=eq_TransitiveC5ARocqVerifyHarness?AgentSubmission6Common7CatExec6wbytesC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryK47Corelib4Init9Datatypes6option01C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec>rdn_wbytes_hitC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec:rdn_firstnC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission6Common7CatExec>rdn_wbytes_outC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec9rdn_skipnC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec7rdn_appI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["VP1"] "p'0h04__x1h14__x2h22H0h37__arithh44__ffh58__varmaph65__with74cstrh85cstr0h93acch:1ih;1sh<1Hh=2IHh>1bi001bh?1ch@5cstr1hA1xp;1p;2p;3p;4p;8p;5p;Bp;<p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g000Nj1@Tg0013j1cTg001Qj1TTg0024j1BTg002TR1j22Tg002nj3=Tg0044j24Tg004Tj25Tg004kR0j13Tg005KR2j21Tg005hR3j20Tg006Dj26Tg006^j4JTg007Ej1?Tg007jj1FTg008Jj2GTg008hj1YTg009Fj4XTg009dj1WTg00:Bj1VTg00:mj2ETg00;Pj1STg00<2j2DTg00<Uj38Tg00=8j2RTg00=Zj2QTg00>Fj3PTg00>`j3OTg00??j4NTg00@1j4<Tg00@\j3MTg00ARR4j1;Tg00B1j1>Tg00BVj1ITg00C4j2UTg00CZj3bTg00DGj8aTg00E6j3`Tg00EVj5_Tg00F8lBHTg00F^l<]Tg00GCj4\Tg00Gnj7[Tg00HRj8ZTg00I6l<^Tg00I[R5P5P5g00J:R6P6P6g00JXR7P0P0P0P2g00K8R8f3R9f2R:f1R;g00K[R<g00L:R=f0R>MBHp=LP5P6P1P0P3g00LXf5R3f4R?P9P:P;P>M<]p=7P6P;g00M:P>C\p=:P;g00MaR@g00N@RAPAg00N`RBP>g00O@F[p=9P9P@PAPAPBP:P;P>GZp=CP5P5P6P6P4P0P0P9g00O`P:P;P>M<^p=AP5P5P5P6P6P6P7P0P0P0P2P8P3P?P9P:P;P>MBHp=Kg00PDR8#@R2#@#@#cR0#TR7#BR4P712>;R@A=9:;1479,5:'2[^95^:5RCX;415:<R<,2;%3;RD%3:RE/1=RF'0P;PD166DRGP<PFP:PE166ERF166=CLE712;:10DER<P;PDPGP:PEPFE7P>CJRGP<%?9RD%39RH,0=RIPDPIg00PiRJ#FRK%BJRJP61G6:P;%Y6CXRL%W6RM%V6RN1E68RO1E62RP':,9NRQ%SARA1D6=986P,:O,9NCC1RNBRBP>P:g00QURRg00R5RS'61Q>:=PRSdAO6=;CNRSb4b5b6X06X1610>;RT11:=,0;[^06^16P>f6RU#3RV%33P9O3b3b8b7b2C<%F7RW?=:;147W,5:'2eX<@X95X:5P5P1g00RU9M51%;:R1PRP5%>2#>#>#>#I,U09b03R0P1P;n0100000020000R25=?147?RW,51RX%;WRY,5:RZP9P1P2P0PRPRPRP5P>%;?RRP9n0100000020000/2RP>%;9RR/2R%I8R8,1HR0/00PRP011>8R2XA6R[P9PH166HR\CAR]PRP0P]E712:910EHR^P:PEPFP9PHP\E7P;CJR\P^%??RH%3?,0=R_PHP_PKPJ1G6;PM1D68R`986ORa/:a,9NPBPSb4b5b6X061022^06P>f7#3RbO1b3b8b7b2C<12:R10E0P:PEPFPRP0P]E7P\P^PHP_PHP_PKPJPLPMPNPQPAA86P`R`,:O,9NCCPBPSb4b5b6X06X1611:8,0;\T^06^16P>PbPVP9O3b3b8b7b2C<n0110000020001b>O312XZ11E8R9%3WRV'1RT11V8RA,1ERQ'0PXPTP1P9P[P:PEPFCAPWPV166VR9EKPZPQP:PEPFPYPAP[PWPVP9CAEKE7PGP<PDPI147URU#?%3U,0=PHP_PKPJPLPMA86aPA86O`':,9NPBPSb4b5b6X06X16112;11;8,1>'0^06^16P>f9,47#3PbO2b3b@b8b7b2C<GaA`73?R??=:;147?,5:'2eX<@X95X:5X=CX;4X?7P>D_W;o"). Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["VP2"] "h04__x1h14__x2h21Hh32H0h47__arithh54__ffh68__varmaph75__with84cstrh95cstr0h:1sp;1p;3p;2p;6p;4p;<p;Bp;7p;8g000Nj18Tg0013j1\Tg001Qj1JTg0024j1:Tg00S=j3[Tg002TR0j23Tg0044j22Tg004Tj2<Tg004kR1j11Tg005hR2j20Tg006Dj24Tg005KR3j29Tg00TFj6RTg006^j4QTg007Ej1>Tg007jj1NTg008Jj2MTg008hj1LTg009Fj4ITg009dj1HTg00:Bj1GTg00<2j2FTg00;Pj1ETg00:mj2;Tg00<Uj3KTg00=8j2DTg00=Zj2CTg00>Fj3BTg00>`j3OTg00??j4PTg00@1j4ATg00U0j1STg002nj3TTg00F^l<@Tg00F8lBZTg00GCj4YTg00Gnj7WTg00HRj8XTf0R4g00K[R5;T5p=5g00I[R6g00J:R7P0P1P2g00LXR8f5R9f4f3R:f2R;f1R<P4M<@p=?P6P7P0P1P2P8P5g00L:R8P<P5P8P4M<@p=VP6P6P6P7P7P7g00JXP1P1P1P3g00K8P5P8P:P;P<P4MBZp=UP7P<g00M:P4CYp=6P<g00MaR3g00N@R1P1g00N`R6P4g00O@FWp=7P:P3P1P1P6P;P<P4GXp==g00PDR3#8R2#8#8#\#JR0#:A[4551355R=%5<R>120<R?,<5R@'3RA[13>?%1>RB%1?RC'0P>PB147BRDP?PC147CREE?%5;RF120;RG,<5'3\=1088R5%1FRH%1G,98'0[RGP=PAP5198CRA,0B1478R=/V=P>PBPDP@PAP=P?PCPECUE?ERP4CQPG%>F108H120:RH#>%1H,08g00PiRH#N%:HP71M7;P<%L7CI%H7%G7RHPH1F78RF/6F,7H%E1R11;73R31;72R29K7F'6,7HC=P11632,7HC=1DH6P4P;g00QURHg00R5R6'41C4;=BH6dAO78<CPb5b6b7X07X17198;,0<\510<;[^07^17P41209#1%59#1P:O3b4b9b8b3CAb2%S41204'3eW:o"). Qed.
End VP2.

Section Canary.
Context {fx : FPState}.
  Variable drw : EntryDraw.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition RB : list byte := at_random_bytes (ed_random drw).
  Definition rba : list byte := firstn 4 (skipn 0 RB).
  Definition rbb : list byte := firstn 4 (skipn 4 RB).
  Definition rwa : word := Z_to_bv 64 (bytes_le_to_Z rba).
  Definition rwb : word := Z_to_bv 64 (bytes_le_to_Z rbb).
  Definition guard_bytes : list byte :=
    firstn 1 (word_to_le_bytes 4 (v_lw rwa)) ++ [Z_to_bv 8 0]
    ++ skipn 2 (word_to_le_bytes 4 (v_lw rwa)) ++ word_to_le_bytes 4 (v_lw rwb).
  Definition canary_w : word := Z_to_bv 64 (bytes_le_to_Z guard_bytes).

  Lemma length_RB : length RB = 16%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "p;1p;2p;3g00V2j18Tg00W0j17Tg000Nj11Tg0013j13Tg001Qj16Tg0044j25Tg00>Fj34Tg00ARj12Tf0#2#2p=0p,3drw#8#7g00I[g00PD#1#1#1#3#6g00X;'5g00K[#0#0#0#0#0#0#0#034eo"). Qed.
  Lemma length_rba : length rba = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "h01nh14__p1h24__p2h34__x1h42H0h57__arithh64__ffh78__varmaph85__with91mh:2z0p;1p;3p;2p;4p;7p;8p;6p;Bp;<g00ARj14Tg00>Fj30Tg006Dj22Tg000Nj16Tg0013j1YTg001Qj1UTg00Y3j3STg00YQj3PTg0044j23Tg00Z0j28Tg002TR0j27Tg00BVj1BTg00ZGj2CTg00Zdj2ATg005hR1j2;Tg00[Aj2VTg00[cj2TTg00\?j25Tg00\Zj2@Tg00]4j1RTg00]Rj2QTg00^3j2?Tg00^\j3OTg00_Ej3NTg00_nj2LTg007jj1ITg00E6j3JTg0024j1KTg008Jj2HTg009dj1GTg00:Bj1MTg00:mj2FTg00<2j2:Tg00`Zj3ETg00GCj4=Tg00a=j7hTg00;Pj1gTg00HRj8fTg00=8j2eTg00=Zj2dTg00>`j3ZTg00??j4[Tg00@1j4\Tg00aaj69Tg00b?j3]Tg00b`j4^Tg00F8lB_Tg00F^l<`Tg00cEj6aTg00Gnj7bTg00cij7cTf0R2#4#4p=1g00I[R3P3P3g00J:R4P4P4g00dMg004kR5P5P5f4R6g00dmf3R7f2R8f1R9g00K[R:g00L:R;P2MB_p=XP3P4P0P5P1g00LXf5P6P7P8P9P2M<`p=WP9g00MaR1g00N@R5P5g00N`R0P2Eap=>P9P1P5P5P0P2g00O@Fbp=<P8P1P5P5P0P9P2Fcp=DP3%4:R<#4#1R=A032=X03123=g00PDR>#6#6R?#6R@#Y#URAg00X;RB9SA:RC9PA='3PAPCP=P313ABRD/8:17=2X03P3%1=#1#1#1#1#1RE182:,7=X0318E:RF,7=%B?R?%6@#BR@/C;RG,A;RH';P=P?124?PFPH1C92,A;X94X04PEP@124@124;DXEW1V;G1T;GREA04HG'51;G;RFA04H;'5'@PHP4p-0RHg00PiRI%R>,Q41?4<5O41?4:5N4g00eT'L%II3J%KI1H49%G4%M4RIP1P5P5P0PIP1P5P5P01>I7P41F4>R>g00f@1:4@1:4;R@5E4R7C=,<I5DIP4P7g00M:R7P@C=,<I1>I65DIFh%g5P41:4?P7P>C=,<IGf1eI0P2P8g00QURIg00R5R0'21d28=0I0dAZ4;9C[b6b7b8X34X1HW2A042G,5915F8'@1;?9[^34^1H^2HP2A049;PEP9P8O4b5b:b4C\PDg00fgE913ACA]A:BE9C^E9g00gf,3A=03=eo"). Qed.
  Lemma length_rbb : length rbb = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "h01nh14__p1h24__p2h34__x1h42H0h57__arithh64__ffh78__varmaph85__with91mh:2z0p;1p;3p;2p;4p;7p;8p;6p;Bp;<g00ARj13Tg00>Fj31Tg006Dj25Tg000Nj16Tg0013j1YTg001Qj1UTg00Y3j3STg00YQj3PTg0044j22Tg00Z0j28Tg002TR0j27Tg00BVj1BTg00ZGj2CTg00Zdj2ATg005hR1j2;Tg00[Aj2VTg00[cj2TTg00\?j24Tg00\Zj2@Tg00]4j1RTg00]Rj2QTg00^3j2?Tg00^\j3OTg00_Ej3NTg00_nj2LTg007jj1ITg00E6j3JTg0024j1KTg008Jj2HTg009dj1GTg00:Bj1MTg00:mj2FTg00<2j2:Tg00`Zj3ETg00GCj4=Tg00a=j7hTg00;Pj1gTg00HRj8fTg00=8j2eTg00=Zj2dTg00>`j3ZTg00??j4[Tg00@1j4\Tg00aaj69Tg00b?j3]Tg00b`j4^Tg00F8lB_Tg00F^l<`Tg00cEj6aTg00Gnj7bTg00cij7cTf0R2#3#3p=0g00I[R3P3P3g00J:R4P4P4g00dMg004kR5P5P5f6g00dmf5R6f4R7f3R8f2R9f1R:P2MB_p=XP3P4P0P5P1g00LXP6P7P8P9P:P2M<`p=WP:g00MaR6g00N@R1P1g00N`R5P2Eap=>P:P6P1P1P5P2g00O@Fbp=<P9P6P1P1P5P:P2Fcp=DP3g00K[R0#3R;#3#0R<A132<X03153<g00PDR=#6#6R>#6R?#Y#UR@g00X;RA9S@<RB9P@<'2P@PBP<P312@ARC/8<17<2X03P3%0<#0#0#0#0#0RD182<,7<X0318D<RE,7<%B>R>g00L:RF%6?#BR?/C>RG'ARH';P<P>154>RIPEPH1C:2,AFX94X04PDP?154?P<P>PIFXEW1VFG1TFGRIA14HG'41;GFRDA14HF'4'@PHP4p-0RHg00PiRE%R=,Q41?4;5O41?405N4g00eT'L%IE3J%KE1H4:%G4%M4REP6P1P1P5PEP6P1P1P51>E8P41F4=R=g00f@1:4?1:4>R?5E4R8C=,<E5DEP4P8g00M:R81:4FC=,<E1>E75DEFh%g1P4P?P8P=C=,<EGf1eE5P2P9g00QUREg00R5R5'51d29=1E5dAZ4F:C[b6b7b8X34X1HW2A142G,4:14D9'@1;>:[^34^1H^2HP2A14:FPIP:P9O4b5b:b4C\PCg00fgE912@BA]@<AE9C^E9g00h_,2@=13<eo"). Qed.
  Lemma length_guard_bytes : length guard_bytes = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "h01nh17__arithh24__ffh38__varmaph45__witp;1p;2p;3p;4p;7p;<p;6g000Nj1:Tg0013j1YTg001Qj1RTg00ARj14Tg00iXj1BTg00jQj2ATg00YQj3VTg0044j21Tg00C4j2LTg007jj1<Tg00E6j3FTg00Y3j3DTg00kYj39Tg004Tj20Tg00Z0j28Tg006Dj26Tg002TR0j2@Tg00BVj1?Tg005hR1j2UTg0024j1QTg008hj1PTg009dj1OTg00:Bj1KTg00<2j2;Tg00GCj4HTg00Gnj7GTg00=8j2ITg00=Zj2JTg00>Fj3=Tg00>`j3ETg00??j4MTg00@1j4NTg00l6j2>Tg00b`j4CTg00b?j3STg00m>j37Tg00F^l<XTg00aaj6WTg00I[R2f1R3f0R43=p=2f2R51034'0p=5P2g00J:R6P0g004kP1g00LXf5f4R1f3R0P5P3P4M<Xp=TP2P1P0P5P3P4EWp=3g00PDR0#:#:R1#:#YR7#RR8g00K[#4R9%49R:#4#4R;g00m]#BR<'AR=5V8R>'1R?g00L:R@,L7%<85F8R7AD8:=RAg00nV#BRB,A;RC598RD598RE,18RF'0%4;#4#4#4RG,24X021187RH118DRI'010?4/2GX02118ARJ118CRK'0A5?H4/2GX02118=RL/8:104K95?H/2GX02P;184:/0K95?H/2GX02P;18;:RM/0495?H/2GX02P910M;954H/2GX02162GP?P8P=P9P;1@94X021@9;%?0R0%?1R1'UR2P9P01660P;P11661ETg00PiR9#<%Q9%P6%O6%K6R9g00Mag00N@R?P?g00N`R?P61;60g00M:1;61CHg00O@FG1I9?P4P5g00QUR?g00R5R9'61J45==?9dAE6@3CMb2b3b4P2P4b1CNPL1>;<R<D3CCD3PK1>;BD3PLP<D3PJAS8:=D3PIA78ACD3PFA787DD3A98>E,18A78>ED3g00oO,18/2Geo"). Qed.
  Lemma bytes_val : forall bs, (length bs <= 8)%nat ->
    bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "h02Hah14__x1h23Hl0h37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with94cstrh:6__sat2h;6__sat3h<4__x2h=1Hh>2Hbh?2Hlh@2HnhA2bshB1zp;1p;2p;4p;3p;5p;6p;<p;7p;8g000Nj19Tg0013j1NTg001Qj1[Tg0024j1MTg0044j21Tg00ARj14Tg002TR0j2DTg010Pj1ZTg011Xj1:Tg00BVj1ETg004kR1j12Tg012Uj23Tg0132j28Tg00[cj26Tg013Oj1hTg005hR2j27Tg006Dj2;Tg006^j4JTg007Ej1ITg014Xj2CTg015@j3BTg007jj1YTg008hj1XTg009dj1WTg00:Bj1VTg00<2j2<Tg00=8j2UTg00=Zj2TTg00>Fj3GTg00>`j3STg00??j4RTg00^3j2@Tg00_Ej3?Tg00_nj2FTg015dj2QTg00E6j3HTg008Jj2PTg00:mj2OTg00;Pj1gTg016Pj3fTg0173j5eTg00C4j2dTg017Zj2bTg009Fj4_Tg018Dj3^Tg018gj3`Tg00aaj6]Tg00F^l<aTg00GCj4KTg00Gnj7\Tg00HRj8cTg00L:R3f0R4'7p=0g00I[g00J:R5P0P1P2g00LXf5R2f4R1f3R0f2R6f1R7P4M<ap=LP5P7g019aP4CKp=AP7g00MaR8g00N@R9P9g00N`R:P4g00O@F\p=5P5P7g00M:P4CKp=>P0P8P9P9P:P6P7P4Gcp==g00PDR8#9R;#9#9R<#N#[R=#M11=4g00K[R>#4R?#4R@#4#4#4#4#4#4RA'D%Z7%:7%E;RB%E<RC11=7#2'3'8'6%h6%:6#0PB11=0RD#2RE,3CRF%9<#9#9R<#ERG1DDA17ECRHPDPE1;5EPAPC1;5CREELP6CJRDPH11=1RI#IRJ%2IRK#0RL11=2RM#2RN,3C,CBRO163BRPf6,1=#2,3CRQ#0f7RR,1=#2,3CRS,8B,63[[RT%0BRUg01:HRVf8RW,1=#2RX,3CRY=BB7UW0RZ18BYRY#0\V^0UR[g00PiR\#YR]%M\R^%X5R_%W5R`%V5Ra1<53Rb1<5BRc'A'51Ua:R:P4P6g00QURdg00R5Re';1T46=GdedAS537CRReb4b7b8PPP4b3b5b6b9b2PDPHPJPLPOPTPZP[1@5>R>1@5@R@9?5>g00eTR['F'Q=H\]P^1P57RZP`Pa1O58R81<5CRT'>,5a%g9R9Af5T81<5G'>,5aC=P:Peb4b7b8X15174C13C7/7G[^15P4PXP1O2b3b5b6b9b2De18BF18BGRF'7P5%:1R1%:2=G54XB51;51%N<R<1d<1'b1DIA17KCR2PIPK1;5KPAPCPEELP0CJR0P2%IMRM%0NRN1CBQRQ%0S163Y[\PRYf9RS,1=#2,3CRE=BB7VVX0URA18BE#0\V^0URE1CBGRK%0G163F[\PRPABBG7VVX0URG%0F\V^0URUP]P^PZP`Pa1>b8,5aRbP9PbC=P:Peb4b7b8X15%04%07[^15P4f;Rb#:RZPWO2b3b5b6b:b;b9b2P0P2PMPNPQPYPAPEPKPPPGPU1@5?=?5>9?5@/F[=H\]P^P51P56P7P_C_P`Pa1O5;R;A^5c<R<'>,5aP9Pa1A8;,5aP91A8<,5aC=C=P:Peb4b7b8X15X<5177F1676166F[[^15^<5P411=b#2,3C,8BPZPRPSO4b3b5b6b:b;b9b25`1E]b=b@b>W?WAo"). Qed.
  Lemma rwa_val : bytes_le_to_Z rba = bv_unsigned rwa.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00ARj10Tg002TR0j27Tg000Nj11Tg00BVj13Tg005hR1j2LTg006Dj22Tg007jj1=Tg0024j1;Tg008hj1:Tg009dj18Tg00:Bj19Tg00<2j24Tg00GCj4KTg00Gnj7JTg00=8j2ITg00=Zj2BTg00>Fj35Tg00>`j3ATg00??j4?Tg00@1j4@Tg0013j16Tg001Qj1<Tg0044j2CTg00aaj6DTg01:dj2ETg011Xj1FTg017Zj2GTg00F^l<HTg00I[R2g00J:R3P0g004kP1g00LXf5f4f3f2R1f1R0f0R4M<Hp=>g00gfR5P2g00K[#0#0#0#0R6%06#0#0#0R7,74X421767g00PD#1#1R2#3R8%12R2#3R9'LR:P6P81238P7P91239E>g00PiR7#=%;7%:3%83%93R7g00Mag00N@R6P6g00N`R6P31438g00M:1439CKg00O@FJ1I76P4P1g00QUR6g00R5R7'21B41=567dg00L:=A30C?b1b2b3P:P4b0C@%62#</C5g01;cED'E%F5%12#1#1#6g00m]'G553eo"). Qed.
  Lemma rwb_val : bytes_le_to_Z rbb = bv_unsigned rwb.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00ARj10Tg002TR0j27Tg000Nj11Tg00BVj13Tg005hR1j2LTg006Dj22Tg007jj1=Tg0024j1;Tg008hj1:Tg009dj18Tg00:Bj19Tg00<2j24Tg00GCj4KTg00Gnj7JTg00=8j2ITg00=Zj2BTg00>Fj35Tg00>`j3ATg00??j4?Tg00@1j4@Tg0013j16Tg001Qj1<Tg0044j2CTg00aaj6DTg01:dj2ETg011Xj1FTg017Zj2GTg00F^l<HTg00I[R2g00J:R3P0g004kP1g00LXf5f4f3f2R1f1R0f0R4M<Hp=>g00h_R5P2g00K[#0#0#0#0R6%06#0#0#0R7,74X421767g00PD#1#1R2#3R8%12R2#3R9'LR:P6P81238P7P91239E>g00PiR7#=%;7%:3%83%93R7g00Mag00N@R6P6g00N`R6P31438g00M:1439CKg00O@FJ1I76P4P1g00QUR6g00R5R7'21B41=567dg00L:=A30C?b1b2b3P:P4b0C@%62#</C5g01<cED'E%F5%12#1#1#6g00nV'G553eo"). Qed.
  Lemma canary_val : bytes_le_to_Z guard_bytes = bv_unsigned canary_w.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00ARj10Tg002TR0j25Tg000Nj11Tg00BVj16Tg005hR1j2LTg006Dj22Tg007jj1=Tg0024j1;Tg008hj1:Tg009dj17Tg00:Bj18Tg00<2j29Tg00GCj4KTg00Gnj7JTg00=8j2ITg00=Zj2BTg00>Fj33Tg00>`j3ATg00??j4?Tg00@1j4@Tg0013j14Tg001Qj1<Tg0044j2CTg00aaj6DTg01:dj2ETg011Xj1FTg017Zj2GTg00F^l<HTg00I[R2g00J:R3P0g004kP1g00LXf5f4f3f2R1f1R0f0R4M<Hp=>g00oOR5P2g00K[#0#0#0#0#0#0#0#0R61546X421566g00PD#1#1#1R2#6R7/L7R8P6P71237R9P6P7P9E>g00PiR9#=%;9%:3%73%83R9g00Mag00N@R6P6g00N`R6P31937R7g00M:P7CKg00O@FJ1I96P4P1g00QUR6g00R5R9'21B41=369dg00L:=A30C?b1b2b3P8P4b0C@%42#</C5g01=cED'E%F5%12#1#1#4g01>k'G533eo"). Qed.

  (* [comment removed for export] *)
  Lemma rdn_guard : forall segs D,
    rdn segs (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x764d8) (word_to_le_bytes 4 (v_lw rwa)))
      (Z_to_bv 64 0x764dc) (word_to_le_bytes 4 (v_lw rwb)))
      (Z_to_bv 64 0x764d9) [Z_to_bv 8 0]) (Z_to_bv 64 0x764d8) 8 = Some guard_bytes.
Proof.
ltac2:(KReplay.run1 (kr_t_V2StartupDefs ()) ["Canary"] "h03HA0h13HB0h24cstrh35cstr0h47__arithh54__ffh68__varmaph75__with86__sat1h96__sat2h:1zh;1nh<1xh=1oh>2Hah?1ah@5lemmahA1yhB1AhC1BhD1DhE2HAhF2HBhG3HinhH1mhI4segsp%0p&0p;1p;2p;3p;4p;8p;6p;;p;9p;5p;<p;Bp;7g0024j1cTg000Nj1<Tg0013j1gTg001Qj1zTg01?ij1wTg00ARj1ATg00iXj1pTg00jQj2mTg00l6j2iTg0044j2DTg00>Fj1Hj37Tg01@Kk10HTg00BVj1?Tg00C4j2KTg01A;j3=Tg01B5S00j45j2qj1nTg01Bmj4ZTg01CTk107Tg01DCj4WTg01E:k304Tg01F0k403Tg01F]j2CTg01GIj8Xl;uTg01HDk101Tg01I3k600Tg01I^j2TTg01J@l9dTg017Zj2VTg004kR0j1:Tg005KR1j21Tg0132j2{Tg005hR2j20Tg01K:k10GTg01KXk40FTg01L;k20ETg01L^k30DTg006^j4\Tg007Ej1xTg014Xk20CTg00[cj2JTg015@k30BTg007jj1vTg008hk10ATg009dk10?Tg00:Bk10>Tg00<Uj3PTg018Dk30=Tg00=8k20<Tg006Dj2tTg00=Zk20;Tg00>`k309Tg00??k408Tg00<2j2oTg018gj3LTg00aaj68Tg01M;j5_Tg00E6k305Tg004Tj2lTg00YQj3kTg00Y3j3fTg00kYj3rTg002TR3j2jTg00@1j4^Tg01N=k802Tg00\Zj26Tg01O;j6STg01Ocl9MTg01Pek10:Tg01Q`j3sTg01REj8~Tg01SBl9`Tg00B1j1GTg00I6l<}Tg00F8mB0@Tg00F^l<aTg00GCj4eTg00Gnj7yTg00a=j7|Tf0R4#<#<p=Eg00I[R5f1R6;74p=I%G4#G#<#Gp=B%G4#<p=@%<4#Gp=Og00J:R7/t4p=4P5P7P7P7P0P0f5R8f4R9f3R:f2R;P6P4M<}p=bP7P7P7P7P7P7P1P4P6P;P1P:P9P8f6R1f7R<f8R=f9NB0@p=RP7P7P2P<P2P1P8P9P:P;P6P4M<ap=3P5P7P4P0P6P;P:P9P8P1P<P=M<ap=]g00L:R=/04p=>1o74p=FP;g00MaR>g00N@R?P?g00N`R@P7P6g00M:P4Ceg00O@RAFyp=2P7P6g019aP4Cep=YP6P>P?P?P@P4PAFyp=[P7P<P1P8P9P:P;C^P6P4E8p=;%G4#Gp>06P5P7P3P0P2g00LXP8P9P:P;P6P4M<ap=h10;6/64p=91064,6;p=UP;P>P?P?P@P6P4F|p=QP7P9P:P;P6P4E8p=Ng01T=#cR?g00PDR>#<R2#<R0#<R3#<#ERA#gRB#zRC%g3R3#zRD#w[REg00K[#ARF#ARG#A#ARHg00m]#pRI'mS01%cDRJg00nV#pRK,mHS02PJ1iHI1DD6/IHRI1iHKPI1DD:RI/IHS03%wJRK%HKS04&0HKS05P1%B>#@#O#E#B#@#E#?RL,KBRM==89RNPMPHC5P1PNPM1DD9ROC5PCPK^;5S06%HCS07P5PK%H5RPQ04CZS081q1NPEQ06\CS09%HES0:PCQ06Q07Q08CZS0;%n1P?Q09\ES0<%H?S0=PEQ09Q0:Q0;CZS0>Q00Q0<\?RQP?Q0<Q0=Q0>CZRRP?Q0<Q0>PEQ09Q0;PCQ06Q08P5PKQ04&07KCWCWCWCW:04QRQ00H03S0?P11C?1GXPN1CENGXPM1CCMPHPOP5PP&015POPHP4J00S0@M;u1TJ9RRPR1CKRS0AM9dW@P6P8P:P9PMP5PH1VBMRQ%:4RS'1%?2R2%?ARA'{RT'0X;5PL%:HRU,14RV/0TX:7S0B11LURW/0T%?0R0,1LRX/0TRYP4X<7RZ1064$0GXA7X<7R[PWPXPZPZPZP7P7g01U<1164H0F#4XH7X;7S0CPLPL%4LS0DPUP0PZPZ%4SX<5S0EPHP0%40RXEbS0FM:RPTPT%4TS0GG31DD;RW/IH%:WR\=770R]PP%H7R^%:6=77S1I6420E6440DXA5X<5R_PWP\%4\PHP0PXM9]P4C\R\P]1IOH%:ORW=770R`PPP^P_POPW%4WPHP0PXM9]P;C\RWP`1DD8Ra#xRb%:aRc#>RdPbPd20C2ARe1J=2Rf%>A1J=TRg[[Rh%>2Rig01:HRjB0B2A6UW>RA%>T\jRj^>iRiP4P;O1RkPjP:P4P9O2X?fRlPg^?fRfg00PiRg#vRm%cgRg&0A7Rn&0?7Ro&0>7Rp%FLRq%F0Rr5P7%F2S0H>0=7BRs3220<p@R@P4P;g00QURtg00R5Ru't20;4;=7tudB097=6H08Rub5b6b7PYP4b4b9b8b8b9b3b2b0b1PQP\P]PWP`PbPdPbPdPmPgPnPo1o7=RY=2pqP@Pub5b6b7%>LP4b4S0Ib3b2b0b1P\P]PWP`PbPdPbPdPePhPAPiPkPjPlPfPmPgPnPo1Yqs,[pP@Pub5b6b71JLTP4b4b9b8b8b9S0Jb3b2b0b15LLG;PIP6E8D_O2P8A=9M:PMPHC51TJ:57KP1%B>#@#O#E#B$06#E#?Rd,KBRb==N:R`%B>#@#O#E#B#@#O#?RW,KBR]1K3=%vD605DR33=R=PF1lGHS0K,lFPMAkDF9AfDG9S0L=rD:S0M9rD3PKP1P`PMPFC5R\AkDF8,TJ97K4X=KRtPKP1PNPMPFC5PtP1PNPHPMP9PFP41jFH%?>Rt/00R;PFPt%4tS0NPHP0PXEhQ03%:IRv=770RwPPP^P_PIPv%4vPHP0PXM9]P6C\RvPw1IaHA77c0RxPPP^P_PaPc%4cPHP0PXM9]P:C\RcPx1DD1Ra#xR_%:a#>RaP_PaPmPgPnPo%FtS0O=2prP@Pub5b6b7P;P4b4b3b2b0b1C^L02P\P1P:PNPbPMPFP5PH%:FR\,1QS0P1VBbR;11;SS0Q/0Q39X;5PL114\RS11;US0R/04S0S79;X:7Pd11L\R^/04RP?UVLX:710^dS0T11dURy/0LRz'611LtR{/0dR|11d0R}/0LR~'6S0UQ0TPzP|P~PZP[P^P{PZPZPZQ0CPLPLQ0DP\PtPZPZQ0EPFPtQ0NEbS0NM:RS0TPdPd%4dS0VG3PZP[PyP}PZPZPZQ0CPdPdQ0VPUP0Q0FM:RS0FPLPLQ0DG3ESPvPwPcPxP_PaP_PaPmPgPnPoQ0O9P7qS0W%FdRU52pAP7UrR~=2pq5QpP@Pub5b6b7Q0UP4b4b3b2b0b1P;PvPwPcPxP_PaP_PaPmPgPnPoA2pYUP@Pub5b6b7%>dP4b4b3b2b0b1PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPo1YUs,[pP@Pub5b6b71JdTP4b4b9b8b8b9b3b2b0b15LdS0UG;PQPvPwPcPxP_PaP_PaQ0Ib3b2b0b1PvPwPcPxP_PaP_PaQ0Jb3b2b0b15LLS0JDNPIP6E8PL10STX:7S0I10^T10{TR|PZP[P^P{Q0TPTPTQ0GG3PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPoQ0W=2psP@Pub5b6b7P|P4b4b9b8b8b9b3b2b0b1PQQ0JG;S0XP5PHQ0Q/0TX;5PdQ0B10yT10}TR|PZP[PyP}Q0FPTPTQ0GG3PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPoA2p~sP@Pub5b6b7P|P4b4b9b8b8b9b3b2b0b1P;Q0UG;S0BPIP6E8S0YM9ME8P1P=PMPFC5P1P3P`P]PMPFPL1VB]R|11|\/04S0Z59SX:7PWAUPSLX:710^WS0[11W\RP/0LS0\'610{WS0]11WtRz/0LS0^'6S0_Q0[Q0\Q0]Q0^PZP[P^P{Q0TPWPW%4WR{G3PZP[PPPzPZPZPZQ0CPWPWP{P\PtQ0NM:RRtPLPLQ0DG3ESPvPwPcPxP_PaP_PaPmPgPnPoQ0W%FWRL52pQ0O9P7LR\=2pq5QpP@Pub5b6b7Q0_P4b4b3b2b0b1P|PvPwPcPxP_PaP_PaPmPgPnPoA2pYLP@Pub5b6b7%>WP4b4b3b2b0b1PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPo1YLs,[pP@Pub5b6b71JWTP4b4b9b8b8b9b3b2b0b15LWRqG;PQQ0JDNQ0P1DD3#:,1|R^/0Q79|eQ0XQ0P/0TePWQ0I10PT10zTRQPZP[PPPzPtPTPTQ0GG3PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPoA2p\sP@Pub5b6b7PQP4b4b9b8b8b9b3b2b0b1P|PqG;10^TeRQM9ME8P1P=PFQ0K&0:FS0K9sBMRFP3Q0MP1P3P`P]PQD_P1P=PGPHQ0K9sBFQ0LP:PKP1P`%B>#@#O#E#B#@#@#?R>,KBRFPGC5S0LAfDG8,TJ97K4X=KRDPKP1PNPFPGC5PDP1PNPHPMP9PGP41jGH1020RDPGP2%42S0KPHP0PXEhPvPwPcPxP_PaP_PaPmPgPnPoQ0H=2prP@Pub5b6b7PDP4b4b3b2b0b1C^G~Q0LP1P:PNPbPFPGP5PH1VBFRB%:GRD'1RrQ0Q/0B79;X;5P>114DR5Q0S79;X:7Pd11>DRX/04S0S?UV>X:710XdS0Q10y>S0L'611>2R0/0dS0M10}>S0I'6S0PQ0QQ0LQ0MQ0IPZP[PXP0PZPZPZQ0CP>P>%4>S0CPDP2PZPZQ0EPGP2Q0KEbM:RS0KPdPdQ0VG3PZP[PyP}Q0FP>P>Q0CG3ESPvPwPcPxP_PaP_PaPmPgPnPo%F>R2Q0H5P7RD=2pUA2p~25QpP@Pub5b6b7Q0PP4b4b3b2b0b1P;Q0UG;PBPvPwPcPxP_PaP_PaPmPgPnPoA2pY2P@Pub5b6b7%>>P4b4b3b2b0b1PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPo1Y2s,[pP@Pub5b6b71J>TP4b4b9b8b8b9b3b2b0b15L>RYDNPIP6E8P>105TX:710XT100TRIPZP[PXP0Q0KPTPTQ0GG3PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPoA2pDsP@Pub5b6b7PIP4b4b9b8b8b9b3b2b0b1PBPYG;RIQ0YM9ME8P1P=PFPGC5P1P3P`P]PFPGP>Q0Z995|X:7PWQ0S?US>X:710XWR510P>RG'6100WRF10z>Rs'6RfP5PGPFPsPZP[PXP0Q0KPWPWP{G3PZP[PPPzPtP>P>Q0CG3ESPvPwPcPxP_PaP_PaPmPgPnPoA2pDLA2p\25QpP@Pub5b6b7PfP4b4b3b2b0b1P|PqG;PBPYDN10^B99r|ePI10rTePQM9ME8PKP1P`PbPHC5A7K4RX=KQ03PKQ04Q05P<A=1M8?=b9R9PbPHC5P<P9PbPOC5PCQ06Q07Q081q<9PEQ09Q0:Q0;%n<P?Q0<Q0=Q0>Q00Q0?P<1C?<GXP91CE9GXPb1CCbPHPOQ0@M;uPRPRQ0AM9dW@P6P1P:PNPbQ0YD_O2P1P=PbPHC5P1P3P`P]PbPHPdQ0Z99V|X:7PW10Sd99y4X:710yWR710PdRS'610}WRV10zdR`'6R1P7PSPVP`PZP[PyP}Q0FPWPWP{G3PZP[PPPzPtPdPdQ0VG3ESPvPwPcPxP_PaP_PaPmPgPnPoA2p~LA2p\U5QpP@Pub5b6b7P1P4b4b3b2b0b1P|PqG;P;Q0UDNQ0R10^;79|eQ0BQ0R/0TePQM9ME8M9`M9`M9`bGbFbEbCbBP6Q019=4MQ027=b?=]3PM%AH#A#A#AC5g00oO,TJ57KeWDWIo"). Qed.

End Canary.

Section Defs.
Context {fx : FPState}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variables (hw : word) (drw : EntryDraw).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN av.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x561a0) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x76500) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x76560) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0x76528) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x764f0) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x764e8) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x3b98c)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x17868)).

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x76298) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x762a8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x762a0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x76510) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x76518) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x56280) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x56268) (word_to_le_bytes 8 (Z_to_bv 64 0x56280)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x561a8) (word_to_le_bytes 8 (Z_to_bv 64 0x561a8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x764f8) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x561d0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x561c8) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x56240) (word_to_le_bytes 8 (Z_to_bv 64 0x76530)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x56220) (word_to_le_bytes 8 (Z_to_bv 64 0x56220)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x561b0) (word_to_le_bytes 8 (Z_to_bv 64 0x561a8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x561b8) (word_to_le_bytes 8 (Z_to_bv 64 0x561a8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x561c0) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x764d8) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x764dc) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x764d9) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (Z_to_bv 64 0x56260) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x46120) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
