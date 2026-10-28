(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23StartupDefs () := "C47Corelib7Program6Basics4flipK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Peano2le00c5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs@after_last_slashC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib7Classes?RelationClassesCPreOrder_TransitiveK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib7Classes?RelationClasses<transitivityK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib5Arith8PeanoNat3Nat;le_preorderc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefsCafter_last_slash_leC46Stdlib9micromega;ZifyClasses:impl_morphc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs<progname_offC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs2RBC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List@firstn_length_leK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201c5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs9length_RBc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs3rbac5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs3rbbC5ARocqVerifyHarness?AgentSubmission6Common8PropExec4v_lwC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission6Common7CatExecDlength_N_to_le_bytesC46Stdlib5Lists4List:length_appc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs3rwac5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs3rwbc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs;guard_bytesC5ARocqVerifyHarness?AgentSubmission6Common8PropExecCbytes_le_to_Z_boundC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission6Common8PropExecDbytes_le_to_Z_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common7StepTac6u_Z2bvK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00c5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs9bytes_valc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs:length_rbac5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs:length_rbbc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefsBlength_guard_bytesc5ARocqVerifyHarness?AgentSubmission3V23>V23StartupDefs8canary_wI47Corelib4Init9Datatypes6option00C47Corelib7Classes?RelationClasses=eq_TransitiveC5ARocqVerifyHarness?AgentSubmission6Common7CatExec6wbytesC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryK47Corelib4Init9Datatypes6option01C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec>rdn_wbytes_hitC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec:rdn_firstnC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission6Common7CatExec>rdn_wbytes_outC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec9rdn_skipnC5ARocqVerifyHarness?AgentSubmission6Common7SeqExec7rdn_appI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
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
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["VP1"] "p'0h04__x1h14__x2h22H0h37__arithh44__ffh58__varmaph65__with74cstrh85cstr0h93acch:1ih;1sh<1Hh=2IHh>1bi001bh?1ch@5cstr1hA1xp;1p;2p;3p;4p;8p;5p;Bp;<p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g000Nj1@Tg0013j1cTg001Qj1TTg0024j1BTg002TR1j22Tg002nj3=Tg0046j24Tg004Vj25Tg004mR0j13Tg005MR2j21Tg005jR3j20Tg006Fj26Tg006`j4JTg007Gj1?Tg007lj1FTg008Lj2GTg008jj1YTg009Hj4XTg009fj1WTg00:Dj1VTg00:oj2ETg00;Rj1STg00<4j2DTg00<Wj38Tg00=:j2RTg00=\j2QTg00>Hj3PTg00>bj3OTg00?Aj4NTg00@3j4<Tg00@^j3MTg00ATR4j1;Tg00B3j1>Tg00BXj1ITg00C6j2UTg00C\j3bTg00DIj8aTg00E8j3`Tg00EXj5_Tg00F:lBHTg00F`l<]Tg00GEj4\Tg00H0j7[Tg00HTj8ZTg00I8l<^Tg00I]R5P5P5g00J<R6P6P6g00JZR7P0P0P0P2g00K:R8f3R9f2R:f1R;g00K]R<g00L<R=f0R>MBHp=LP5P6P1P0P3g00LZf5R3f4R?P9P:P;P>M<]p=7P6P;g00M<P>C\p=:P;g00McR@g00NBRAPAg00NbRBP>g00OBF[p=9P9P@PAPAPBP:P;P>GZp=CP5P5P6P6P4P0P0P9g00ObP:P;P>M<^p=AP5P5P5P6P6P6P7P0P0P0P2P8P3P?P9P:P;P>MBHp=Kg00PFR8#@R2#@#@#cR0#TR7#BR4P712>;R@A=9:;1479,5:'2[^95^:5RCX;415:<R<,2;%3;RD%3:RE/1=RF'0P;PD166DRGP<PFP:PE166ERF166=CLE712;:10DER<P;PDPGP:PEPFE7P>CJRGP<%?9RD%39RH,0=RIPDPIg00PkRJ#FRK%BJRJP61G6:P;%Y6CXRL%W6RM%V6RN1E68RO1E62RP':,9NRQ%SARA1D6=986P,:O,9NCC1RNBRBP>P:g00QWRRg00R7RS'61Q>:=PRSdAO6=;CNRSb4b5b6X06X1610>;RT11:=,0;[^06^16P>f6RU#3RV%33P9O3b3b8b7b2C<%F7RW?=:;147W,5:'2eX<@X95X:5P5P1g00RW9M51%;:R1PRP5%>2#>#>#>#I,U09b03R0P1P;n0100000020000R25=?147?RW,51RX%;WRY,5:RZP9P1P2P0PRPRPRP5P>%;?RRP9n0100000020000/2RP>%;9RR/2R%I8R8,1HR0/00PRP011>8R2XA6R[P9PH166HR\CAR]PRP0P]E712:910EHR^P:PEPFP9PHP\E7P;CJR\P^%??RH%3?,0=R_PHP_PKPJ1G6;PM1D68R`986ORa/:a,9NPBPSb4b5b6X061022^06P>f7#3RbO1b3b8b7b2C<12:R10E0P:PEPFPRP0P]E7P\P^PHP_PHP_PKPJPLPMPNPQPAA86P`R`,:O,9NCCPBPSb4b5b6X06X1611:8,0;\T^06^16P>PbPVP9O3b3b8b7b2C<n0110000020001b>O312XZ11E8R9%3WRV'1RT11V8RA,1ERQ'0PXPTP1P9P[P:PEPFCAPWPV166VR9EKPZPQP:PEPFPYPAP[PWPVP9CAEKE7PGP<PDPI147URU#?%3U,0=PHP_PKPJPLPMA86aPA86O`':,9NPBPSb4b5b6X06X16112;11;8,1>'0^06^16P>f9,47#3PbO2b3b@b8b7b2C<GaA`73?R??=:;147?,5:'2eX<@X95X:5X=CX;4X?7P>D_W;o"). Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["VP2"] "h04__x1h14__x2h21Hh32H0h47__arithh54__ffh68__varmaph75__with84cstrh95cstr0h:1sp;1p;3p;2p;6p;4p;<p;Bp;7p;8g000Nj18Tg0013j1\Tg001Qj1JTg0024j1:Tg00S?j3[Tg002TR0j22Tg0046j24Tg004Vj2<Tg004mR1j11Tg005jR2j20Tg006Fj25Tg005MR3j29Tg00TJj6RTg006`j4QTg007Gj1>Tg007lj1NTg008Lj2MTg008jj1LTg009Hj4ITg009fj1HTg00:Dj1GTg00<4j2FTg00;Rj1ETg00:oj2;Tg00<Wj3KTg00=:j2DTg00=\j2CTg00>Hj3BTg00>bj3OTg00?Aj4PTg00@3j4ATg00U4j1STg002nj3TTg00F`l<@Tg00F:lBZTg00GEj4YTg00H0j7WTg00HTj8XTf0R4g00K]R5;T5p=3g00I]R6g00J<R7P0P1P2g00LZR8f5R9f4f3R:f2R;f1R<P4M<@p=?P6P7P0P1P2P8P5g00L<R8P<P5P8P4M<@p=VP6P6P6P7P7P7g00JZP1P1P1P3g00K:P5P8P:P;P<P4MBZp=UP7P<g00M<P4CYp=6P<g00McR3g00NBR1P1g00NbR6P4g00OBFWp=7P:P3P1P1P6P;P<P4GXp==g00PFR3#8R2#8#8#\#JR0#:A[4551255R=%3<R>140<R?,<5R@'2RA[12>?%1>RB%1?RC'0P>PB157BRDP?PC157CREE?%3;RF140;RG,<5'2\=1088R5%1F%1GRF,98'0[RHP=PAP5198CRA,0B1578R=/V=P>PBPDP@PAP=P?PCPECUE?ERP4CQPH%>G108F%3:RF#>%1F,08g00PkRF#N%:FP71M7;P<%L7CI%H7%G7RFPF1F78RG/6G,7F%E1R11;73R31;72R29K7G'6,7FC=P11632,7FC=1DF6P4P;g00QWRFg00R7R6'51C4;=BF6dAO78<CPb5b6b7X07X17198;,0<\510<;[^07^17P41409#1%39#1P:O3b4b9b8b3CAb2%S41404'2eW:o"). Qed.
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
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "p;1p;2p;3g00V8j18Tg00W6j17Tg000Nj11Tg0013j13Tg001Qj16Tg0046j25Tg00>Hj34Tg00ATj12Tf0#2#2p=0p,3drw#8#7g00I]g00PF#1#1#1#3#6g00XA'5g00K]#0#0#0#0#0#0#0#034eo"). Qed.
  Lemma length_rba : length rba = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "h01nh14__p1h24__p2h34__x1h42H0h57__arithh64__ffh78__varmaph85__with91mh:2z0p;1p;3p;2p;4p;7p;8p;6p;Bp;<g00ATj14Tg00>Hj30Tg006Fj22Tg000Nj16Tg0013j1YTg001Qj1UTg00Y;j3STg00YYj3PTg0046j23Tg00Z8j28Tg002TR0j27Tg00BXj1BTg00ZOj2CTg00Zlj2ATg005jR1j2;Tg00[Ij2VTg00[kj2TTg00\Gj25Tg00\bj2@Tg00]<j1RTg00]Zj2QTg00^;j2?Tg00^dj3OTg00_Mj3NTg00`6j2LTg007lj1ITg00E8j3JTg0024j1KTg008Lj2HTg009fj1GTg00:Dj1MTg00:oj2FTg00<4j2:Tg00`bj3ETg00GEj4=Tg00aEj7hTg00;Rj1gTg00HTj8fTg00=:j2eTg00=\j2dTg00>bj3ZTg00?Aj4[Tg00@3j4\Tg00aij69Tg00bGj3]Tg00bhj4^Tg00F:lB_Tg00F`l<`Tg00cMj6aTg00H0j7bTg00d1j7cTf0R2#4#4p=1g00I]R3P3P3g00J<R4P4P4g00dUg004mR5P5P5f4R6g00e5f3R7f2R8f1R9g00K]R:g00L<R;P2MB_p=XP3P4P0P5P1g00LZf5P6P7P8P9P2M<`p=WP9g00McR1g00NBR5P5g00NbR0P2Eap=>P9P1P5P5P0P2g00OBFbp=<P8P1P5P5P0P9P2Fcp=DP3%4:R<#4#1R=A032=X03123=g00PFR>#6#6R?#6R@#Y#URAg00XARB9SA:RC9PA='3PAPCP=P313ABRD/8:17=2X03P3%1=#1#1#1#1#1RE182:,7=X0318E:RF,7=%B?R?%6@#BR@/C;RG,A;RH';P=P?124?PFPH1C92,A;X94X04PEP@124@124;DXEW1V;G1T;GREA04HG'51;G;RFA04H;'5'@PHP4p-0RHg00PkRI%R>,Q41?4<5O41?4:5N4g00e\'L%II3J%KI1H49%G4%M4RIP1P5P5P0PIP1P5P5P01>I7P41F4>R>g00fH1:4@1:4;R@5E4R7C=,<I5DIP4P7g00M<R7P@C=,<I1>I65DIFh%g5P41:4?P7P>C=,<IGf1eI0P2P8g00QWRIg00R7R0'21d28=0I0dAZ4;9C[b6b7b8X34X1HW2A042G,5915F8'@1;?9[^34^1H^2HP2A049;PEP9P8O4b5b:b4C\PDg00foE913ACA]A:BE9C^E9g00h0,3A=03=eo"). Qed.
  Lemma length_rbb : length rbb = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "h01nh14__p1h24__p2h34__x1h42H0h57__arithh64__ffh78__varmaph85__with91mh:2z0p;1p;3p;2p;4p;7p;8p;6p;Bp;<g00ATj13Tg00>Hj31Tg006Fj25Tg000Nj16Tg0013j1YTg001Qj1UTg00Y;j3STg00YYj3PTg0046j22Tg00Z8j28Tg002TR0j27Tg00BXj1BTg00ZOj2CTg00Zlj2ATg005jR1j2;Tg00[Ij2VTg00[kj2TTg00\Gj24Tg00\bj2@Tg00]<j1RTg00]Zj2QTg00^;j2?Tg00^dj3OTg00_Mj3NTg00`6j2LTg007lj1ITg00E8j3JTg0024j1KTg008Lj2HTg009fj1GTg00:Dj1MTg00:oj2FTg00<4j2:Tg00`bj3ETg00GEj4=Tg00aEj7hTg00;Rj1gTg00HTj8fTg00=:j2eTg00=\j2dTg00>bj3ZTg00?Aj4[Tg00@3j4\Tg00aij69Tg00bGj3]Tg00bhj4^Tg00F:lB_Tg00F`l<`Tg00cMj6aTg00H0j7bTg00d1j7cTf0R2#3#3p=0g00I]R3P3P3g00J<R4P4P4g00dUg004mR5P5P5f6g00e5f5R6f4R7f3R8f2R9f1R:P2MB_p=XP3P4P0P5P1g00LZP6P7P8P9P:P2M<`p=WP:g00McR6g00NBR1P1g00NbR5P2Eap=>P:P6P1P1P5P2g00OBFbp=<P9P6P1P1P5P:P2Fcp=DP3g00K]R0#3R;#3#0R<A132<X03153<g00PFR=#6#6R>#6R?#Y#UR@g00XARA9S@<RB9P@<'2P@PBP<P312@ARC/8<17<2X03P3%0<#0#0#0#0#0RD182<,7<X0318D<RE,7<%B>R>g00L<RF%6?#BR?/C>RG'ARH';P<P>154>RIPEPH1C:2,AFX94X04PDP?154?P<P>PIFXEW1VFG1TFGRIA14HG'41;GFRDA14HF'4'@PHP4p-0RHg00PkRE%R=,Q41?4;5O41?405N4g00e\'L%IE3J%KE1H4:%G4%M4REP6P1P1P5PEP6P1P1P51>E8P41F4=R=g00fH1:4?1:4>R?5E4R8C=,<E5DEP4P8g00M<R81:4FC=,<E1>E75DEFh%g1P4P?P8P=C=,<EGf1eE5P2P9g00QWREg00R7R5'51d29=1E5dAZ4F:C[b6b7b8X34X1HW2A142G,4:14D9'@1;>:[^34^1H^2HP2A14:FPIP:P9O4b5b:b4C\PCg00foE912@BA]@<AE9C^E9g00hk,2@=13<eo"). Qed.
  Lemma length_guard_bytes : length guard_bytes = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "h01nh17__arithh24__ffh38__varmaph45__witp;1p;2p;3p;4p;7p;<p;6g000Nj1:Tg0013j1YTg001Qj1RTg00ATj14Tg00ifj1BTg00j_j2ATg00YYj3VTg0046j21Tg00C6j2LTg007lj1<Tg00E8j3FTg00Y;j3DTg00kgj39Tg004Vj20Tg00Z8j28Tg006Fj26Tg002TR0j2@Tg00BXj1?Tg005jR1j2UTg0024j1QTg008jj1PTg009fj1OTg00:Dj1KTg00<4j2;Tg00GEj4HTg00H0j7GTg00=:j2ITg00=\j2JTg00>Hj3=Tg00>bj3ETg00?Aj4MTg00@3j4NTg00lDj2>Tg00bhj4CTg00bGj3STg00mLj37Tg00F`l<XTg00aij6WTg00I]R2f1R3f0R43=p=2f2R51034'0p=5P2g00J<R6P0g004mP1g00LZf5f4R1f3R0P5P3P4M<Xp=TP2P1P0P5P3P4EWp=3g00PFR0#:#:R1#:#YR7#RR8g00K]#4R9%49R:#4#4R;g00mk#BR<'AR=5V8R>'1R?g00L<R@,L7%<85F8R7AD8:=RAg00nf#BRB,A;RC598RD598RE,18RF'0%4;#4#4#4RG,24X021187RH118DRI'010?4/2GX02118ARJ118CRK'0A5?H4/2GX02118=RL/8:104K95?H/2GX02P;184:/0K95?H/2GX02P;18;:RM/0495?H/2GX02P910M;954H/2GX02162GP?P8P=P9P;1@94X021@9;%?0R0%?1R1'UR2P9P01660P;P11661ETg00PkR9#<%Q9%P6%O6%K6R9g00Mcg00NBR?P?g00NbR?P61;60g00M<1;61CHg00OBFG1I9?P4P5g00QWR?g00R7R9'61J45==?9dAE6@3CMb2b3b4P2P4b1CNPL1>;<R<D3CCD3PK1>;BD3PLP<D3PJAS8:=D3PIA78ACD3PFA787DD3A98>E,18A78>ED3g00oa,18/2Geo"). Qed.
  Lemma bytes_val : forall bs, (length bs <= 8)%nat ->
    bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "h02Hah14__x1h23Hl0h37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with94cstrh:6__sat2h;6__sat3h<4__x2h=1Hh>2Hbh?2Hlh@2HnhA2bshB1zp;1p;2p;4p;3p;5p;6p;<p;7p;8g000Nj19Tg0013j1NTg001Qj1[Tg0024j1MTg0046j21Tg00ATj14Tg002TR0j2DTg010dj1ZTg011lj1:Tg00BXj1ETg004mR1j12Tg012ij23Tg013Fj28Tg00[kj26Tg013cj1hTg005jR2j27Tg006Fj2;Tg006`j4JTg007Gj1ITg014lj2CTg015Tj3BTg007lj1YTg008jj1XTg009fj1WTg00:Dj1VTg00<4j2<Tg00=:j2UTg00=\j2TTg00>Hj3GTg00>bj3STg00?Aj4RTg00^;j2@Tg00_Mj3?Tg00`6j2FTg0168j2QTg00E8j3HTg008Lj2PTg00:oj2OTg00;Rj1gTg016dj3fTg017Gj5eTg00C6j2dTg017nj2bTg009Hj4_Tg018Xj3^Tg019;j3`Tg00aij6]Tg00F`l<aTg00GEj4KTg00H0j7\Tg00HTj8cTg00L<R3f0R4'7p=0g00I]g00J<R5P0P1P2g00LZf5R2f4R1f3R0f2R6f1R7P4M<ap=LP5P7g01:5P4CKp=AP7g00McR8g00NBR9P9g00NbR:P4g00OBF\p=5P5P7g00M<P4CKp=>P0P8P9P9P:P6P7P4Gcp==g00PFR8#9R;#9#9R<#N#[R=#M11=4g00K]R>#4R?#4R@#4#4#4#4#4#4RA'D%Z7%:7%E;RB%E<RC11=7#2'3'8'6%h6%:6#0PB11=0RD#2RE,3CRF%9<#9#9R<#ERG1DDA17ECRHPDPE1;5EPAPC1;5CREELP6CJRDPH11=1RI#IRJ%2IRK#0RL11=2RM#2RN,3C,CBRO163BRPf6,1=#2,3CRQ#0f7RR,1=#2,3CRS,8B,63[[RT%0BRUg01:\RVf8RW,1=#2RX,3CRY=BB7UW0RZ18BYRY#0\V^0UR[g00PkR\#YR]%M\R^%X5R_%W5R`%V5Ra1<53Rb1<5BRc'A'51Ua:R:P4P6g00QWRdg00R7Re';1T46=GdedAS537CRReb4b7b8PPP4b3b5b6b9b2PDPHPJPLPOPTPZP[1@5>R>1@5@R@9?5>g00e\R['F'Q=H\]P^1P57RZP`Pa1O58R81<5CRT'>,5a%g9R9Af5T81<5G'>,5aC=P:Peb4b7b8X15174C13C7/7G[^15P4PXP1O2b3b5b6b9b2De18BF18BGRF'7P5%:1R1%:2=G54XB51;51%N<R<1d<1'b1DIA17KCR2PIPK1;5KPAPCPEELP0CJR0P2%IMRM%0NRN1CBQRQ%0S163Y[\PRYf9RS,1=#2,3CRE=BB7VVX0URA18BE#0\V^0URE1CBGRK%0G163F[\PRPABBG7VVX0URG%0F\V^0URUP]P^PZP`Pa1>b8,5aRbP9PbC=P:Peb4b7b8X15%04%07[^15P4f;Rb#:RZPWO2b3b5b6b:b;b9b2P0P2PMPNPQPYPAPEPKPPPGPU1@5?=?5>9?5@/F[=H\]P^P51P56P7P_C_P`Pa1O5;R;A^5c<R<'>,5aP9Pa1A8;,5aP91A8<,5aC=C=P:Peb4b7b8X15X<5177F1676166F[[^15^<5P411=b#2,3C,8BPZPRPSO4b3b5b6b:b;b9b25`1E]b=b@b>W?WAo"). Qed.
  Lemma rwa_val : bytes_le_to_Z rba = bv_unsigned rwa.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00ATj10Tg002TR0j27Tg000Nj11Tg00BXj13Tg005jR1j2LTg006Fj22Tg007lj1=Tg0024j1;Tg008jj1:Tg009fj18Tg00:Dj19Tg00<4j24Tg00GEj4KTg00H0j7JTg00=:j2ITg00=\j2BTg00>Hj35Tg00>bj3ATg00?Aj4?Tg00@3j4@Tg0013j16Tg001Qj1<Tg0046j2CTg00aij6DTg01;8j2ETg011lj1FTg017nj2GTg00F`l<HTg00I]R2g00J<R3P0g004mP1g00LZf5f4f3f2R1f1R0f0R4M<Hp=>g00h0R5P2g00K]#0#0#0#0R6%06#0#0#0R7,74X421767g00PF#1#1R2#3R8%12R2#3R9'LR:P6P81238P7P91239E>g00PkR7#=%;7%:3%83%93R7g00Mcg00NBR6P6g00NbR6P31438g00M<1439CKg00OBFJ1I76P4P1g00QWR6g00R7R7'21B41=567dg00L<=A30C?b1b2b3P:P4b0C@%62#</C5g01<9ED'E%F5%12#1#1#6g00mk'G553eo"). Qed.
  Lemma rwb_val : bytes_le_to_Z rbb = bv_unsigned rwb.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00ATj10Tg002TR0j27Tg000Nj11Tg00BXj13Tg005jR1j2LTg006Fj22Tg007lj1=Tg0024j1;Tg008jj1:Tg009fj18Tg00:Dj19Tg00<4j24Tg00GEj4KTg00H0j7JTg00=:j2ITg00=\j2BTg00>Hj35Tg00>bj3ATg00?Aj4?Tg00@3j4@Tg0013j16Tg001Qj1<Tg0046j2CTg00aij6DTg01;8j2ETg011lj1FTg017nj2GTg00F`l<HTg00I]R2g00J<R3P0g004mP1g00LZf5f4f3f2R1f1R0f0R4M<Hp=>g00hkR5P2g00K]#0#0#0#0R6%06#0#0#0R7,74X421767g00PF#1#1R2#3R8%12R2#3R9'LR:P6P81238P7P91239E>g00PkR7#=%;7%:3%83%93R7g00Mcg00NBR6P6g00NbR6P31438g00M<1439CKg00OBFJ1I76P4P1g00QWR6g00R7R7'21B41=567dg00L<=A30C?b1b2b3P:P4b0C@%62#</C5g01=;ED'E%F5%12#1#1#6g00nf'G553eo"). Qed.
  Lemma canary_val : bytes_le_to_Z guard_bytes = bv_unsigned canary_w.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00ATj10Tg002TR0j25Tg000Nj11Tg00BXj16Tg005jR1j2LTg006Fj22Tg007lj1=Tg0024j1;Tg008jj1:Tg009fj17Tg00:Dj18Tg00<4j29Tg00GEj4KTg00H0j7JTg00=:j2ITg00=\j2BTg00>Hj33Tg00>bj3ATg00?Aj4?Tg00@3j4@Tg0013j14Tg001Qj1<Tg0046j2CTg00aij6DTg01;8j2ETg011lj1FTg017nj2GTg00F`l<HTg00I]R2g00J<R3P0g004mP1g00LZf5f4f3f2R1f1R0f0R4M<Hp=>g00oaR5P2g00K]#0#0#0#0#0#0#0#0R61546X421566g00PF#1#1#1R2#6R7/L7R8P6P71237R9P6P7P9E>g00PkR9#=%;9%:3%73%83R9g00Mcg00NBR6P6g00NbR6P31937R7g00M<P7CKg00OBFJ1I96P4P1g00QWR6g00R7R9'21B41=369dg00L<=A30C?b1b2b3P8P4b0C@%42#</C5g01>=ED'E%F5%12#1#1#4g01?G'G533eo"). Qed.

  (* [comment removed for export] *)
  Lemma rdn_guard : forall segs D,
    rdn segs (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x158440) (word_to_le_bytes 4 (v_lw rwa)))
      (Z_to_bv 64 0x158444) (word_to_le_bytes 4 (v_lw rwb)))
      (Z_to_bv 64 0x158441) [Z_to_bv 8 0]) (Z_to_bv 64 0x158440) 8 = Some guard_bytes.
Proof.
ltac2:(KReplay.run1 (kr_t_V23StartupDefs ()) ["Canary"] "h03HA0h13HB0h24cstrh35cstr0h47__arithh54__ffh68__varmaph75__with86__sat1h96__sat2h:1zh;1nh<1xh=1oh>2Hah?1ah@5lemmahA1yhB1AhC1BhD1DhE2HAhF2HBhG3HinhH1mhI4segsp%0p&0p;1p;2p;3p;4p;8p;6p;;p;9p;5p;<p;Bp;7g0024j1cTg000Nj14Tg0013j1gTg001Qj1zTg01@Gj1wTg00ATj1ATg00ifj1pTg00j_j2mTg00lDj2iTg0046j2ETg00>Hj1Gj37Tg01@ik10HTg00BXj1@Tg00C6j2KTg01AYj3=Tg01BSS00j46j2qj1nTg01CKj4ZTg01D2k107Tg01Daj4VTg01EXk304Tg01FNk403Tg01G;j2DTg01Ggj8Wl;uTg01Hbk101Tg01IQk600Tg01J<j2STg01J^l9dTg017nj2UTg004mR0j1:Tg005MR1j21Tg013Fj2{Tg005jR2j20Tg01KXk10GTg01L6k40FTg01LYk20ETg01M<k30DTg006`j4YTg007Gj1xTg014lk20CTg00[kj2ITg015Tk30BTg007lj1vTg008jk10ATg009fk10?Tg00:Dk10>Tg00<Wj3OTg018Xk30=Tg00=:k20<Tg006Fj2tTg00=\k20;Tg00>bk309Tg00?Ak408Tg00<4j2oTg019;j3LTg00aij6;Tg01MYj5_Tg00E8k305Tg004Vj2lTg00YYj3kTg00Y;j3fTg00kgj3rTg002TR3j2jTg00@3j4^Tg01N[k802Tg00\bj28Tg01OYj6RTg01PAl9MTg01QCk10:Tg01R>j3sTg01Rcj8~Tg01S`l9`Tg00B3j1\Tg00I8l<}Tg00F:mB0@Tg00F`l<aTg00GEj4eTg00H0j7yTg00aEj7|Tf0R4#4#4p=Bg00I]R5f1R6;74p=H%44#\p=C%\4#4p=P%44#\#4#4p=>g00J<R7/t4p=5P5P7P7P7P0P0f5R8f4R9f3R:f2R;P6P4M<}p=bP7P7P7P7P7P7P1P4P6P;P1P:P9P8f6R1f7R<f8R=f9NB0@p=QP7P7P2P<P2P1P8P9P:P;P6P4M<ap=3P5P7P4P0P6P;P:P9P8P1P<P=M<ap=]g00L<R=/04p=?1o74p=FP;g00McR>g00NBR?P?g00NbR@P7P6g00M<P4Ceg00OBRAFyp=2P7P6g01:5P4Cep=XP6P>P?P?P@P4PAFyp=[P7P<P1P8P9P:P;C^P6P4E;p=<%44#4#4#\p>06P5P7P3P0P2g00LZP8P9P:P;P6P4M<ap=h10;6/84p=91064,8;p=TP;P>P?P?P@P6P4F|p=JP7P9P:P;P6P4E;p=Ng01T[#cR?g00PFR>#4R2#4R0#4R3#4#BRA#gRB#zRC%g3R3#zRD#w[REg00K]#ARF#ARG#A#ARHg00mk#pRI'mS01%cDRJg00nf#pRK,mHS02PJ1iHI1ED6/HHRI1iHKPI1ED:RI/HHS03%wJRK%GKS04&0HKS05P1%C>#C#P#B#>#>#B#B#@RL,KBRM==89RNPMPHC6P1PNPM1ED9ROC6PCPK^;5S06%GCS07P5PK%G5RPQ04CZS081q1NPEQ06\CS09%GES0:PCQ06Q07Q08CZS0;%n1P?Q09\ES0<%G?S0=PEQ09Q0:Q0;CZS0>Q00Q0<\?RQP?Q0<Q0=Q0>CZRRP?Q0<Q0>PEQ09Q0;PCQ06Q08P5PKQ04&07KCVCVCVCV:04QRQ00H03S0?P11D?1GWPN1DENGWPM1DCMPHPOP5PP&015POPHP4J00S0@M;u1SJ9RRPR1DKRS0AM9dW@P6P8P:P9PMP5PH1UBMRQ%:4RS'1%@2R2%@ARA'{RT'0X;5PL%:HRU,14RV/0TX:7S0B11LURW/0T%@0R0,1LRX/0TRYP4X<7RZ1064$0GXA7X<7R[PWPXPZPZPZP7P7g01UZ1164H0F#5XH7X;7S0CPLPL%5LS0DPUP0PZPZ%5SX<5S0EPHP0%50RXEbS0FM:QPTPT%5TS0GG31ED;RW/HH%:WR\=770R]PP%G7R^%:6=77S1H6420E6440DXA5X<5R_PWP\%5\PHP0PXM9]P4CYR\P]1HOH%:ORW=770R`PPP^P_POPW%5WPHP0PXM9]P;CYRWP`1ED8Ra#xRb%:aRc#?RdPbPd20C2ARe1I=2Rf%?A1I=TRg[[Rh%?2Rig01:\RjB0B2A6UW>RA%?T\jRj^>iRiP4P;O1RkPjP:P4P9O2X?fRlPg^?fRfg00PkRg#vRm%cgRg&0A7Rn&0?7Ro&0>7Rp%FLRq%F0Rr5O7%F2S0H>0=7BRs3220<p@R@P4P;g00QWRtg00R7Ru't20;4;=7tudB097=6H08Rub5b6b7PYP4b4b9b8b8b9b3b2b0b1PQP\P]PWP`PbPdPbPdPmPgPnPo1o7=RY=2pqP@Pub5b6b7%?LP4b4S0Ib3b2b0b1P\P]PWP`PbPdPbPdPePhPAPiPkPjPlPfPmPgPnPo1Xqs,[pP@Pub5b6b71ILTP4b4b9b8b8b9S0Jb3b2b0b15LLG<PIP6E;D_O2P8A=9M:PMPHC61SJ:57KP1%C>#C#P#B#>#>#>#@Rd,KBRb==N:R`%C>#C#P#B#>#>$06#@RW,KBR]1K3=%vD605DR33=R=PF1lGHS0K,lFPMAkDF9AfDG9S0L=rD:S0M9rD3PKP1P`PMPFC6R\AkDF8,SJ97K4X=KRtPKP1PNPMPFC6PtP1PNPHPMP9PFP41jFH%@>Rt/00R;PFPt%5tS0NPHP0PXEhQ03%:IRv=770RwPPP^P_PIPv%5vPHP0PXM9]P6CYRvPw1HaHA77c0RxPPP^P_PaPc%5cPHP0PXM9]P:CYRcPx1ED1Ra#xR_%:a#?RaP_PaPmPgPnPo%FtS0O=2prP@Pub5b6b7P;P4b4b3b2b0b1C^L02P\P1P:PNPbPMPFP5PH%:FR\,1QS0P1UBbR;11;SS0Q/0Q39X;5PL114\RS11;US0R/04S0S79;X:7Pd11L\R^/04RP?TVLX:710^dS0T11dURy/0LRz'811LtR{/0dR|11d0R}/0LR~'8S0UQ0TPzP|P~PZP[P^P{PZPZPZQ0CPLPLQ0DP\PtPZPZQ0EPFPtQ0NEbS0NM:QS0TPdPd%5dS0VG3PZP[PyP}PZPZPZQ0CPdPdQ0VPUP0Q0FM:QS0FPLPLQ0DG3ERPvPwPcPxP_PaP_PaPmPgPnPoQ0O9O7qS0W%FdRU52pAO7UrR~=2pq5JpP@Pub5b6b7Q0UP4b4b3b2b0b1P;PvPwPcPxP_PaP_PaPmPgPnPoA2pYUP@Pub5b6b7%?dP4b4b3b2b0b1PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPo1XUs,[pP@Pub5b6b71IdTP4b4b9b8b8b9b3b2b0b15LdS0UG<PQPvPwPcPxP_PaP_PaQ0Ib3b2b0b1PvPwPcPxP_PaP_PaQ0Jb3b2b0b15LLS0JDNPIP6E;PL10STX:7S0I10^T10{TR|PZP[P^P{Q0TPTPTQ0GG3PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPoQ0W=2psP@Pub5b6b7P|P4b4b9b8b8b9b3b2b0b1PQQ0JG<S0XP5PHQ0Q/0TX;5PdQ0B10yT10}TR|PZP[PyP}Q0FPTPTQ0GG3PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPoA2p~sP@Pub5b6b7P|P4b4b9b8b8b9b3b2b0b1P;Q0UG<S0BPIP6E;S0YM9ME;P1P=PMPFC6P1P3P`P]PMPFPL1UB]R|11|\/04S0Z59SX:7PWATPSLX:710^WS0[11W\RP/0LS0\'810{WS0]11WtRz/0LS0^'8S0_Q0[Q0\Q0]Q0^PZP[P^P{Q0TPWPW%5WR{G3PZP[PPPzPZPZPZQ0CPWPWP{P\PtQ0NM:QRtPLPLQ0DG3ERPvPwPcPxP_PaP_PaPmPgPnPoQ0W%FWRL52pQ0O9O7LR\=2pq5JpP@Pub5b6b7Q0_P4b4b3b2b0b1P|PvPwPcPxP_PaP_PaPmPgPnPoA2pYLP@Pub5b6b7%?WP4b4b3b2b0b1PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPo1XLs,[pP@Pub5b6b71IWTP4b4b9b8b8b9b3b2b0b15LWRqG<PQQ0JDNQ0P1ED3#:,1|R^/0Q79|eQ0XQ0P/0TePWQ0I10PT10zTRQPZP[PPPzPtPTPTQ0GG3PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPoA2p\sP@Pub5b6b7PQP4b4b9b8b8b9b3b2b0b1P|PqG<10^TeRQM9ME;P1P=PFQ0K&0:FS0K9sBMRFP3Q0MP1P3P`P]PQD_P1P=PGPHQ0K9sBFQ0LP:PKP1P`%C>#C#P#B#>#>#B#P#@R>,KBRFPGC6S0LAfDG8,SJ97K4X=KRDPKP1PNPFPGC6PDP1PNPHPMP9PGP41jGH1020RDPGP2%52S0KPHP0PXEhPvPwPcPxP_PaP_PaPmPgPnPoQ0H=2prP@Pub5b6b7PDP4b4b3b2b0b1C^G~Q0LP1P:PNPbPFPGP5PH1UBFRB%:GRD'1RrQ0Q/0B79;X;5P>114DR5Q0S79;X:7Pd11>DRX/04S0S?TV>X:710XdS0Q10y>S0L'811>2R0/0dS0M10}>S0I'8S0PQ0QQ0LQ0MQ0IPZP[PXP0PZPZPZQ0CP>P>%5>S0CPDP2PZPZQ0EPGP2Q0KEbM:QS0KPdPdQ0VG3PZP[PyP}Q0FP>P>Q0CG3ERPvPwPcPxP_PaP_PaPmPgPnPo%F>R2Q0H5O7RD=2pUA2p~25JpP@Pub5b6b7Q0PP4b4b3b2b0b1P;Q0UG<PBPvPwPcPxP_PaP_PaPmPgPnPoA2pY2P@Pub5b6b7%?>P4b4b3b2b0b1PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPo1X2s,[pP@Pub5b6b71I>TP4b4b9b8b8b9b3b2b0b15L>RYDNPIP6E;P>105TX:710XT100TRIPZP[PXP0Q0KPTPTQ0GG3PvPwPcPxP_PaP_PaPePhPAPiPkPjPlPfPmPgPnPoA2pDsP@Pub5b6b7PIP4b4b9b8b8b9b3b2b0b1PBPYG<RIQ0YM9ME;P1P=PFPGC6P1P3P`P]PFPGP>Q0Z995|X:7PWQ0S?TS>X:710XWR510P>RG'8100WRF10z>Rs'8RfP5PGPFPsPZP[PXP0Q0KPWPWP{G3PZP[PPPzPtP>P>Q0CG3ERPvPwPcPxP_PaP_PaPmPgPnPoA2pDLA2p\25JpP@Pub5b6b7PfP4b4b3b2b0b1P|PqG<PBPYDN10^B99r|ePI10rTePQM9ME;PKP1P`PbPHC6A7K4RX=KQ03PKQ04Q05P<A=1M8?=b9R9PbPHC6P<P9PbPOC6PCQ06Q07Q081q<9PEQ09Q0:Q0;%n<P?Q0<Q0=Q0>Q00Q0?P<1D?<GWP91DE9GWPb1DCbPHPOQ0@M;uPRPRQ0AM9dW@P6P1P:PNPbQ0YD_O2P1P=PbPHC6P1P3P`P]PbPHPdQ0Z99V|X:7PW10Sd99y4X:710yWR710PdRS'810}WRV10zdR`'8R1P7PSPVP`PZP[PyP}Q0FPWPWP{G3PZP[PPPzPtPdPdQ0VG3ERPvPwPcPxP_PaP_PaPmPgPnPoA2p~LA2p\U5JpP@Pub5b6b7P1P4b4b3b2b0b1P|PqG<P;Q0UDNQ0R10^;79|eQ0BQ0R/0TePQM9ME;M9`M9`M9`bGbFbEbCbBP6Q019=4MQ027=b?=]3PM%AH#A#A#AC6g00oa,SJ57KeWDWIo"). Qed.

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
      (Z_to_bv 64 0x138100) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x158468) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x1584c8) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0x158490) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x158458) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x158450) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x10deb0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x63140)).

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
      (Z_to_bv 64 0x1581f8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x158208) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x158200) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x158478) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x158480) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x1381e0) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x1381c8) (word_to_le_bytes 8 (Z_to_bv 64 0x1381e0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x138108) (word_to_le_bytes 8 (Z_to_bv 64 0x138108)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x158460) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x138130) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x138128) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x1381a0) (word_to_le_bytes 8 (Z_to_bv 64 0x158498)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x138180) (word_to_le_bytes 8 (Z_to_bv 64 0x138180)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x138110) (word_to_le_bytes 8 (Z_to_bv 64 0x138108)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x138118) (word_to_le_bytes 8 (Z_to_bv 64 0x138108)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x138120) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (Z_to_bv 64 0x158440) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x158444) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x158441) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (Z_to_bv 64 0x1381c0) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x127ec0) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
