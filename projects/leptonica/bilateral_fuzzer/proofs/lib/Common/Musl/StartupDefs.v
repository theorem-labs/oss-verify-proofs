(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import StartupBase.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_StartupDefs () := "C47Corelib7Program6Basics4flipK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Peano2le00c69OSSVerify5KrLib6Common4Musl;StartupDefs@after_last_slashC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib7Classes?RelationClassesCPreOrder_TransitiveK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib7Classes?RelationClasses<transitivityK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib5Arith8PeanoNat3Nat;le_preorderc69OSSVerify5KrLib6Common4Musl;StartupDefsCafter_last_slash_leC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses:impl_morphc69OSSVerify5KrLib6Common4Musl;StartupDefs<progname_offC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesc69OSSVerify5KrLib6Common4Musl;StartupDefs2RBC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List@firstn_length_leK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201c69OSSVerify5KrLib6Common4Musl;StartupDefs9length_RBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl;StartupDefs3rbaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl;StartupDefs3rbbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4v_lwC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appc69OSSVerify5KrLib6Common4Musl;StartupDefs3rwaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl;StartupDefs3rwbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl;StartupDefs;guard_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExecCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib6Common8PropExecDbytes_le_to_Z_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00c69OSSVerify5KrLib6Common4Musl;StartupDefs9bytes_valC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl;StartupDefs:length_rbaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl;StartupDefs:length_rbbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl;StartupDefsBlength_guard_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl;StartupDefs8canary_wC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib6Common5Reloc5Reloc;rl_delta_bdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryK47Corelib4Init9Datatypes6option01C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC69OSSVerify5KrLib6Common5Reloc5Reloc:rl_delta_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib6Common7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib6Common4Musl;StartupBase:rl_add_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7SeqExec9rdn_skipnC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common7SeqExec7rdn_appC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := RPH0.

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
End GD_1.
Section GD_2.
  Context {RL : Reloc}.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.
End GD_2.

Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["VP1"] "p'0h04__x1h14__x2h22H0h37__arithh44__ffh58__varmaph65__with74cstrh85cstr0h93acch:1ih;1sh<1Hh=2IHh>1bi001bh?1ch@5cstr1hA1xp;1p;2p;3p;4p;8p;5p;Bp;<p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g000Nj1@Tg0013j1cTg001Qj1TTg0024j1BTg002TR1j22Tg002nj3=Tg004;j24Tg004[j25Tg0052R0j13Tg005RR2j21Tg005oR3j20Tg006Kj26Tg006ej4JTg007Lj1?Tg0081j1FTg008Qj2GTg008oj1YTg009Mj4XTg009kj1WTg00:Ij1VTg00;4j2ETg00;Wj1STg00<9j2DTg00<\j38Tg00=?j2RTg00=aj2QTg00>Mj3PTg00>gj3OTg00?Fj4NTg00@8j4<Tg00@cj3MTg00AYR4j1;Tg00B8j1>Tg00B]j1ITg00C;j2UTg00Caj3bTg00DNj8aTg00E=j3`Tg00E]j5_Tg00F?lBHTg00Fel<]Tg00GJj4\Tg00H5j7[Tg00HYj8ZTg00I=l<^Tg00IbR5P5P5g00JAR6P6P6g00J_R7P0P0P0P2g00K?R8f3R9f2R:f1R;g00KbR<g00LAR=f0R>MBHp=LP5P6P1P0P3g00L_f5R3f4R?P9P:P;P>M<]p=7P6P;g00MAP>C\p=:P;g00MhR@g00NGRAPAg00NgRBP>g00OGF[p=9P9P@PAPAPBP:P;P>GZp=CP5P5P6P6P4P0P0P9g00OgP:P;P>M<^p=AP5P5P5P6P6P6P7P0P0P0P2P8P3P?P9P:P;P>MBHp=Kg00PKR8#@R2#@#@#cR0#TR7#BR4P712>;R@A=9:;1479,5:'2[^95^:5RCX;415:<R<,2;%3;RD%3:RE/1=RF'0P;PD166DRGP<PFP:PE166ERF166=CLE712;:10DER<P;PDPGP:PEPFE7P>CJRGP<%?9RD%39RH,0=RIPDPIg00Q0RJ#FRK%BJRJP61G6:P;%Y6CXRL%W6RM%V6RN1E68RO1E62RP':,9NRQ%SARA1D6=986P,:O,9NCC1RNBRBP>P:g00Q\RRg00R<RS'61Q>:=PRSdAO6=;CNRSb4b5b6X06X1610>;RT11:=,0;[^06^16P>f6RU#3RV%33P9O3b3b8b7b2C<%F7RW?=:;147W,5:'2eX<@X95X:5P5P1g00R\9M51%;:R1PRP5%>2#>#>#>#I,U09b03R0P1P;n0100000020000R25=?147?RW,51RX%;WRY,5:RZP9P1P2P0PRPRPRP5P>%;?RRP9n0100000020000/2RP>%;9RR/2R%I8R8,1HR0/00PRP011>8R2XA6R[P9PH166HR\CAR]PRP0P]E712:910EHR^P:PEPFP9PHP\E7P;CJR\P^%??RH%3?,0=R_PHP_PKPJ1G6;PM1D68R`986ORa/:a,9NPBPSb4b5b6X061022^06P>f7#3RbO1b3b8b7b2C<12:R10E0P:PEPFPRP0P]E7P\P^PHP_PHP_PKPJPLPMPNPQPAA86P`R`,:O,9NCCPBPSb4b5b6X06X1611:8,0;\T^06^16P>PbPVP9O3b3b8b7b2C<n0110000020001b>O312XZ11E8R9%3WRV'1RT11V8RA,1ERQ'0PXPTP1P9P[P:PEPFCAPWPV166VR9EKPZPQP:PEPFPYPAP[PWPVP9CAEKE7PGP<PDPI147URU#?%3U,0=PHP_PKPJPLPMA86aPA86O`':,9NPBPSb4b5b6X06X16112;11;8,1>'0^06^16P>f9,47#3PbO2b3b@b8b7b2C<GaA`73?R??=:;147?,5:'2eX<@X95X:5X=CX;4X?7P>D_W;o"). Qed.
End VP1.

Section VP2.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["VP2"] "h04__x1h14__x2h21Hh32H0h47__arithh54__ffh68__varmaph75__with84cstrh95cstr0h:1sp;1p;3p;2p;6p;4p;<p;Bp;7p;8g000Nj18Tg0013j1\Tg001Qj1JTg0024j1:Tg00SDj3[Tg002TR0j23Tg004;j22Tg004[j2<Tg0052R1j11Tg005oR2j20Tg006Kj24Tg005RR3j29Tg00TTj6RTg006ej4QTg007Lj1>Tg0081j1NTg008Qj2MTg008oj1LTg009Mj4ITg009kj1HTg00:Ij1GTg00<9j2FTg00;Wj1ETg00;4j2;Tg00<\j3KTg00=?j2DTg00=aj2CTg00>Mj3BTg00>gj3OTg00?Fj4PTg00@8j4ATg00U>j1STg002nj3TTg00Fel<@Tg00F?lBZTg00GJj4YTg00H5j7WTg00HYj8XTf0R4g00KbR5;T5p=5g00IbR6g00JAR7P0P1P2g00L_R8f5R9f4f3R:f2R;f1R<P4M<@p=?P6P7P0P1P2P8P5g00LAR8P<P5P8P4M<@p=VP6P6P6P7P7P7g00J_P1P1P1P3g00K?P5P8P:P;P<P4MBZp=UP7P<g00MAP4CYp=6P<g00MhR3g00NGR1P1g00NgR6P4g00OGFWp=7P:P3P1P1P6P;P<P4GXp==g00PKR3#8R2#8#8#\#JR0#:A[4551355R=%5<R>120<R?,<5R@'3RA[13>?%1>RB%1?RC'0P>PB147BRDP?PC147CREE?%5;RF120;RG,<5'3\=1088R5%1FRH%1G,98'0[RGP=PAP5198CRA,0B1478R=/V=P>PBPDP@PAP=P?PCPECUE?ERP4CQPG%>F108H120:RH#>%1H,08g00Q0RH#N%:HP71M7;P<%L7CI%H7%G7RHPH1F78RF/6F,7H%E1R11;73R31;72R29K7F'6,7HC=P11632,7HC=1DH6P4P;g00Q\RHg00R<R6'41C4;=BH6dAO78<CPb5b6b7X07X17198;,0<\510<;[^07^17P41209#1%59#1P:O3b4b9b8b3CAb2%S41204'3eW:o"). Qed.
End VP2.

Section Canary.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
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
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "p;1p;2p;3g00VGj18Tg00WEj17Tg000Nj11Tg0013j13Tg001Qj16Tg004;j25Tg00>Mj34Tg00AYj12Tf0#2#2p=0p,3drw#8#7g00Ibg00PK#1#1#1#3#6g00XP'5g00Kb#0#0#0#0#0#0#0#034eo"). Qed.
  Lemma length_rba : length rba = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "h01nh14__p1h24__p2h34__x1h42H0h57__arithh64__ffh78__varmaph85__with91mh:2z0p;1p;3p;2p;4p;7p;8p;6p;Bp;<g00AYj14Tg00>Mj30Tg006Kj22Tg000Nj16Tg0013j1YTg001Qj1UTg00YOj3STg00Ymj3PTg004;j23Tg00ZLj28Tg002TR0j27Tg00B]j1BTg00Zcj2CTg00[@j2ATg005oR1j2;Tg00[]j2VTg00\?j2TTg00\[j25Tg00]6j2@Tg00]Pj1RTg00]nj2QTg00^Oj2?Tg00_8j3OTg00_aj3NTg00`Jj2LTg0081j1ITg00E=j3JTg0024j1KTg008Qj2HTg009kj1GTg00:Ij1MTg00;4j2FTg00<9j2:Tg00a6j3ETg00GJj4=Tg00aYj7hTg00;Wj1gTg00HYj8fTg00=?j2eTg00=aj2dTg00>gj3ZTg00?Fj4[Tg00@8j4\Tg00b=j69Tg00b[j3]Tg00c<j4^Tg00F?lB_Tg00Fel<`Tg00caj6aTg00H5j7bTg00dEj7cTf0R2#4#4p=1g00IbR3P3P3g00JAR4P4P4g00dig0052R5P5P5f4R6g00eIf3R7f2R8f1R9g00KbR:g00LAR;P2MB_p=XP3P4P0P5P1g00L_f5P6P7P8P9P2M<`p=WP9g00MhR1g00NGR5P5g00NgR0P2Eap=>P9P1P5P5P0P2g00OGFbp=<P8P1P5P5P0P9P2Fcp=DP3%4:R<#4#1R=A032=X03123=g00PKR>#6#6R?#6R@#Y#URAg00XPRB9SA:RC9PA='3PAPCP=P313ABRD/8:17=2X03P3%1=#1#1#1#1#1RE182:,7=X0318E:RF,7=%B?R?%6@#BR@/C;RG,A;RH';P=P?124?PFPH1C92,A;X94X04PEP@124@124;DXEW1V;G1T;GREA04HG'51;G;RFA04H;'5'@PHP4p-0RHg00Q0RI%R>,Q41?4<5O41?4:5N4g00f0'L%II3J%KI1H49%G4%M4RIP1P5P5P0PIP1P5P5P01>I7P41F4>R>g00f\1:4@1:4;R@5E4R7C=,<I5DIP4P7g00MAR7P@C=,<I1>I65DIFh%g5P41:4?P7P>C=,<IGf1eI0P2P8g00Q\RIg00R<R0'21d28=0I0dAZ4;9C[b6b7b8X34X1HW2A042G,5915F8'@1;?9[^34^1H^2HP2A049;PEP9P8O4b5b:b4C\PDg00gCE913ACA]A:BE9C^E9g00hI,3A=03=eo"). Qed.
  Lemma length_rbb : length rbb = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "h01nh14__p1h24__p2h34__x1h42H0h57__arithh64__ffh78__varmaph85__with91mh:2z0p;1p;3p;2p;4p;7p;8p;6p;Bp;<g00AYj13Tg00>Mj31Tg006Kj25Tg000Nj16Tg0013j1YTg001Qj1UTg00YOj3STg00Ymj3PTg004;j22Tg00ZLj28Tg002TR0j27Tg00B]j1BTg00Zcj2CTg00[@j2ATg005oR1j2;Tg00[]j2VTg00\?j2TTg00\[j24Tg00]6j2@Tg00]Pj1RTg00]nj2QTg00^Oj2?Tg00_8j3OTg00_aj3NTg00`Jj2LTg0081j1ITg00E=j3JTg0024j1KTg008Qj2HTg009kj1GTg00:Ij1MTg00;4j2FTg00<9j2:Tg00a6j3ETg00GJj4=Tg00aYj7hTg00;Wj1gTg00HYj8fTg00=?j2eTg00=aj2dTg00>gj3ZTg00?Fj4[Tg00@8j4\Tg00b=j69Tg00b[j3]Tg00c<j4^Tg00F?lB_Tg00Fel<`Tg00caj6aTg00H5j7bTg00dEj7cTf0R2#3#3p=0g00IbR3P3P3g00JAR4P4P4g00dig0052R5P5P5f6g00eIf5R6f4R7f3R8f2R9f1R:P2MB_p=XP3P4P0P5P1g00L_P6P7P8P9P:P2M<`p=WP:g00MhR6g00NGR1P1g00NgR5P2Eap=>P:P6P1P1P5P2g00OGFbp=<P9P6P1P1P5P:P2Fcp=DP3g00KbR0#3R;#3#0R<A132<X03153<g00PKR=#6#6R>#6R?#Y#UR@g00XPRA9S@<RB9P@<'2P@PBP<P312@ARC/8<17<2X03P3%0<#0#0#0#0#0RD182<,7<X0318D<RE,7<%B>R>g00LARF%6?#BR?/C>RG'ARH';P<P>154>RIPEPH1C:2,AFX94X04PDP?154?P<P>PIFXEW1VFG1TFGRIA14HG'41;GFRDA14HF'4'@PHP4p-0RHg00Q0RE%R=,Q41?4;5O41?405N4g00f0'L%IE3J%KE1H4:%G4%M4REP6P1P1P5PEP6P1P1P51>E8P41F4=R=g00f\1:4?1:4>R?5E4R8C=,<E5DEP4P8g00MAR81:4FC=,<E1>E75DEFh%g1P4P?P8P=C=,<EGf1eE5P2P9g00Q\REg00R<R5'51d29=1E5dAZ4F:C[b6b7b8X34X1HW2A142G,4:14D9'@1;>:[^34^1H^2HP2A14:FPIP:P9O4b5b:b4C\PCg00gCE912@BA]@<AE9C^E9g00iI,2@=13<eo"). Qed.
  Lemma length_guard_bytes : length guard_bytes = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "h01nh17__arithh24__ffh38__varmaph45__witp;1p;2p;3p;4p;7p;<p;6g000Nj1:Tg0013j1YTg001Qj1RTg00AYj14Tg00jIj1BTg00kBj2ATg00Ymj3VTg004;j21Tg00C;j2LTg0081j1<Tg00E=j3FTg00YOj3DTg00lJj39Tg004[j20Tg00ZLj28Tg006Kj26Tg002TR0j2@Tg00B]j1?Tg005oR1j2UTg0024j1QTg008oj1PTg009kj1OTg00:Ij1KTg00<9j2;Tg00GJj4HTg00H5j7GTg00=?j2ITg00=aj2JTg00>Mj3=Tg00>gj3ETg00?Fj4MTg00@8j4NTg00lgj2>Tg00c<j4CTg00b[j3STg00moj37Tg00Fel<XTg00b=j6WTg00IbR2f1R3f0R43=p=2f2R51034'0p=5P2g00JAR6P0g0052P1g00L_f5f4R1f3R0P5P3P4M<Xp=TP2P1P0P5P3P4EWp=3g00PKR0#:#:R1#:#YR7#RR8g00Kb#4R9%49R:#4#4R;g00nN#BR<'AR=5V8R>'1R?g00LAR@,L7%<85F8R7AD8:=RAg00oN#BRB,A;RC598RD598RE,18RF'0%4;#4#4#4RG,24X021187RH118DRI'010?4/2GX02118ARJ118CRK'0A5?H4/2GX02118=RL/8:104K95?H/2GX02P;184:/0K95?H/2GX02P;18;:RM/0495?H/2GX02P910M;954H/2GX02162GP?P8P=P9P;1@94X021@9;%?0R0%?1R1'UR2P9P01660P;P11661ETg00Q0R9#<%Q9%P6%O6%K6R9g00Mhg00NGR?P?g00NgR?P61;60g00MA1;61CHg00OGFG1I9?P4P5g00Q\R?g00R<R9'61J45==?9dAE6@3CMb2b3b4P2P4b1CNPL1>;<R<D3CCD3PK1>;BD3PLP<D3PJAS8:=D3PIA78ACD3PFA787DD3A98>E,18A78>ED3g010N,18/2Geo"). Qed.
  Lemma bytes_val : forall bs, (length bs <= 8)%nat ->
    bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "h02Hah14__x1h23Hl0h37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with94cstrh:6__sat2h;6__sat3h<4__x2h=1Hh>2Hbh?2Hlh@2HnhA2bshB1zp;1p;2p;4p;3p;5p;6p;<p;7p;8g000Nj19Tg0013j1NTg001Qj1[Tg0024j1MTg004;j21Tg00AYj14Tg002TR0j2DTg011Vj1ZTg012^j1:Tg00B]j1ETg0052R1j12Tg013[j23Tg0148j28Tg00\?j26Tg014Uj1hTg005oR2j27Tg006Kj2;Tg006ej4JTg007Lj1ITg015^j2CTg016Fj3BTg0081j1YTg008oj1XTg009kj1WTg00:Ij1VTg00<9j2<Tg00=?j2UTg00=aj2TTg00>Mj3GTg00>gj3STg00?Fj4RTg00^Oj2@Tg00_aj3?Tg00`Jj2FTg016jj2QTg00E=j3HTg008Qj2PTg00;4j2OTg00;Wj1gTg017Vj3fTg0189j5eTg00C;j2dTg018`j2bTg009Mj4_Tg019Jj3^Tg019mj3`Tg00b=j6]Tg00Fel<aTg00GJj4KTg00H5j7\Tg00HYj8cTg00LAR3f0R4'7p=0g00Ibg00JAR5P0P1P2g00L_f5R2f4R1f3R0f2R6f1R7P4M<ap=LP5P7g01:gP4CKp=AP7g00MhR8g00NGR9P9g00NgR:P4g00OGF\p=5P5P7g00MAP4CKp=>P0P8P9P9P:P6P7P4Gcp==g00PKR8#9R;#9#9R<#N#[R=#M11=4g00KbR>#4R?#4R@#4#4#4#4#4#4RA'D%Z7%:7%E;RB%E<RC11=7#2'3'8'6%h6%:6#0PB11=0RD#2RE,3CRF%9<#9#9R<#ERG1DDA17ECRHPDPE1;5EPAPC1;5CREELP6CJRDPH11=1RI#IRJ%2IRK#0RL11=2RM#2RN,3C,CBRO163BRPf6,1=#2,3CRQ#0f7RR,1=#2,3CRS,8B,63[[RT%0BRUg01;NRVf8RW,1=#2RX,3CRY=BB7UW0RZ18BYRY#0\V^0UR[g00Q0R\#YR]%M\R^%X5R_%W5R`%V5Ra1<53Rb1<5BRc'A'51Ua:R:P4P6g00Q\Rdg00R<Re';1T46=GdedAS537CRReb4b7b8PPP4b3b5b6b9b2PDPHPJPLPOPTPZP[1@5>R>1@5@R@9?5>g00f0R['F'Q=H\]P^1P57RZP`Pa1O58R81<5CRT'>,5a%g9R9Af5T81<5G'>,5aC=P:Peb4b7b8X15174C13C7/7G[^15P4PXP1O2b3b5b6b9b2De18BF18BGRF'7P5%:1R1%:2=G54XB51;51%N<R<1d<1'b1DIA17KCR2PIPK1;5KPAPCPEELP0CJR0P2%IMRM%0NRN1CBQRQ%0S163Y[\PRYf9RS,1=#2,3CRE=BB7VVX0URA18BE#0\V^0URE1CBGRK%0G163F[\PRPABBG7VVX0URG%0F\V^0URUP]P^PZP`Pa1>b8,5aRbP9PbC=P:Peb4b7b8X15%04%07[^15P4f;Rb#:RZPWO2b3b5b6b:b;b9b2P0P2PMPNPQPYPAPEPKPPPGPU1@5?=?5>9?5@/F[=H\]P^P51P56P7P_C_P`Pa1O5;R;A^5c<R<'>,5aP9Pa1A8;,5aP91A8<,5aC=C=P:Peb4b7b8X15X<5177F1676166F[[^15^<5P411=b#2,3C,8BPZPRPSO4b3b5b6b:b;b9b25`1E]b=b@b>W?WAo"). Qed.
  Lemma rwa_val : bytes_le_to_Z rba = bv_unsigned rwa.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00AYj10Tg002TR0j27Tg000Nj11Tg00B]j13Tg005oR1j2LTg006Kj22Tg0081j1=Tg0024j1;Tg008oj1:Tg009kj18Tg00:Ij19Tg00<9j24Tg00GJj4KTg00H5j7JTg00=?j2ITg00=aj2BTg00>Mj35Tg00>gj3ATg00?Fj4?Tg00@8j4@Tg0013j16Tg001Qj1<Tg004;j2CTg00b=j6DTg01;jj2ETg012^j1FTg018`j2GTg00Fel<HTg00IbR2g00JAR3P0g0052P1g00L_f5f4f3f2R1f1R0f0R4M<Hp=>g00hIR5P2g00Kb#0#0#0#0R6%06#0#0#0R7,74X421767g00PK#1#1R2#3R8%12R2#3R9'LR:P6P81238P7P91239E>g00Q0R7#=%;7%:3%83%93R7g00Mhg00NGR6P6g00NgR6P31438g00MA1439CKg00OGFJ1I76P4P1g00Q\R6g00R<R7'21B41=567dg00LA=A30C?b1b2b3P:P4b0C@%62#</C5g01=0ED'E%F5%12#1#1#6g00nN'G553eo"). Qed.
  Lemma rwb_val : bytes_le_to_Z rbb = bv_unsigned rwb.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00AYj10Tg002TR0j27Tg000Nj11Tg00B]j13Tg005oR1j2LTg006Kj22Tg0081j1=Tg0024j1;Tg008oj1:Tg009kj18Tg00:Ij19Tg00<9j24Tg00GJj4KTg00H5j7JTg00=?j2ITg00=aj2BTg00>Mj35Tg00>gj3ATg00?Fj4?Tg00@8j4@Tg0013j16Tg001Qj1<Tg004;j2CTg00b=j6DTg01;jj2ETg012^j1FTg018`j2GTg00Fel<HTg00IbR2g00JAR3P0g0052P1g00L_f5f4f3f2R1f1R0f0R4M<Hp=>g00iIR5P2g00Kb#0#0#0#0R6%06#0#0#0R7,74X421767g00PK#1#1R2#3R8%12R2#3R9'LR:P6P81238P7P91239E>g00Q0R7#=%;7%:3%83%93R7g00Mhg00NGR6P6g00NgR6P31438g00MA1439CKg00OGFJ1I76P4P1g00Q\R6g00R<R7'21B41=567dg00LA=A30C?b1b2b3P:P4b0C@%62#</C5g01>7ED'E%F5%12#1#1#6g00oN'G553eo"). Qed.
  Lemma canary_val : bytes_le_to_Z guard_bytes = bv_unsigned canary_w.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "h07__arithh14__ffh28__varmaph35__with41np;1p;2p;4p;7p;3p;6p;<g00AYj10Tg002TR0j25Tg000Nj11Tg00B]j16Tg005oR1j2LTg006Kj22Tg0081j1=Tg0024j1;Tg008oj1:Tg009kj17Tg00:Ij18Tg00<9j29Tg00GJj4KTg00H5j7JTg00=?j2ITg00=aj2BTg00>Mj33Tg00>gj3ATg00?Fj4?Tg00@8j4@Tg0013j14Tg001Qj1<Tg004;j2CTg00b=j6DTg01;jj2ETg012^j1FTg018`j2GTg00Fel<HTg00IbR2g00JAR3P0g0052P1g00L_f5f4f3f2R1f1R0f0R4M<Hp=>g010NR5P2g00Kb#0#0#0#0#0#0#0#0R61546X421566g00PK#1#1#1R2#6R7/L7R8P6P71237R9P6P7P9E>g00Q0R9#=%;9%:3%73%83R9g00Mhg00NGR6P6g00NgR6P31937R7g00MAP7CKg00OGFJ1I96P4P1g00Q\R6g00R<R9'21B41=369dg00LA=A30C?b1b2b3P8P4b0C@%42#</C5g01?>ED'E%F5%12#1#1#4g01@M'G533eo"). Qed.

  (* [comment removed for export] *)
  Lemma rdn_guard : forall segs D,
    rdn segs (wbytes (wbytes (wbytes D
      (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw rwa)))
      (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw rwb)))
      (rl dA_2f848 0x2f849) [Z_to_bv 8 0]) (rl dA_2f848 0x2f848) 8 = Some guard_bytes.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupDefs ()) ["Canary"] "h06__sat1h16__sat2h26__sat3h36__sat4h44__x1h56__sat5h66__sat6h73HA0h83HB0h94cstrh:5cstr0h;7__arithh<4__ffh=8__varmaph>5__with?1zh@4__p1hA1ahB2HahC1bhD1nhE1xhF1ohG2SKhH5lemmahI1yhJ1AhK1BhL1DhM2HAhN2HBhO2HdhP3HinhQ1mhR4segsp%0p%1p&0p;1p;2p;3p;4p;8p;6p;;p;9p;5p;<p;Bp;7g0024j1nTg000Nj13Tg0013j1OTg001Qj1rTg01ARk102Tg00B8j1:Tg01B4k20GTg00B]j1>Tg0148j2XTg01C7k10;Tg01CTk209Tg005oR0j20Tg00\[j2MTg00AYj1GTg00jIk101Tg00kBk200Tg00lgj2}Tg004;j2DTg00>Mj1Kj3@Tg01DTk10LTg01EDj2_Tg01F>j3?Tg01G8S00j47j2xj1wTg01H0j4]Tg01HWk10?Tg01IFj4\Tg01J=k30=Tg01K3k40:Tg01K`j2ITg01LLj8^l;zTg01MGk108Tg01N6k607Tg01Naj2FTg01OCl9~Tg018`j2fTg0052R1j1;Tg005RR2j21Tg01P=k10WTg01P[k40VTg01Q>k20UTg01Qak30TTg006ej4dTg007Lj1cTg015^j2bTg00\?j2CTg016Fj3[Tg0081j1|Tg008Qk20QTg009kk10PTg00:Ik10OTg00cak60NTg00;4k20MTg019Jj3`Tg00;Wk10FTg00=?k20ETg006Kj2yTg00=ak20DTg00>gk30CTg00?Fk40BTg008ok10ATg01R>j4STg00b=j65Tg01S@j5mTg00C;k20@Tg00E=k30>Tg004[j2vTg00Ymj3uTg00YOj3hTg00lJj3tTg002TR3j2pTg00@8j4iTg01TBk80<Tg00]6j28Tg01U@j6PTg01Uhl9WTg01Vjj1qTg01Wej3ETg01XJj5gTg01YQk80HTg00ZLk20ITg01ZNk60JTg01Zjl9kTg00I=m<06Tg00F?mB0KTg00Fel<jTg00<9k205Tg00GJj4oTg00H5j7{Tg00dEk704Tg00<\k30RTg00HYk80STg00aYk703Tf0R4#:#:p=Jg00IbR5f1R6;@4p=Lg00JAR7/y4p=4P5P7P7P7P1P1f5R8f4R9f3R:f2R;P6P4N<06p=lP7P7P7P7P7P7P2P4P6P;P2P:P9P8f6R2f7R<f8R=f9S01NB0Kp=VP7P7P0P<P0P2P8P9P:P;P6P4M<jp=6P5P7P4P1P6P;P:P9P8P2P<P=M<jp=eg00LAR>/04p=920574p=HP;g00MhR?g00NGR@P@g00NgRAP7P6g00MAP4Cog00OGRBF{p=2P;P?P@P@PAP6P4K04p=UB0R764p=BP:P?P@P@PAP;P6P4L0Sp=TP7P6g01:gP4Cop=YP6P?P@P@PAP4PBF{p=aP7P<P2P8P9P:P;CiP6P4E5p=AP9P:P;P6C7=@84p=<P5P7P3P1P0g00L_P8P9P:P;P6P4M<jp=s10:;1064'8p==10;6/84p=N1064,8;p=ZP;P?P@P@PAP6P4K03p=QP7P9P:P;P6P4E5p=Rg01[e#nR0g00PKR1#3R3#3RB#3RC#3RD#3RE#3RF#ORG#rRH%OCRC#rRI$02[RJp,2RLS02%:B#J#3#:#3#3#:#JS03+0G%>3RK%>DRL'XRM$0;Q02Q03+09RN'0RO%>ERP,XKRQ,0N'Mg00Kb#GRR#GRS#G#GRTg00nN$01RU+00S04%nIRVg00oN$01RW-00TS05PV1}TU1DI6/LTRU1}TWPU1DI:S06/LTS07&02VRU%KUS08&0LUS09P<%:3#J#J#3#3#3#3#:#3#3#:R3#3S0:#3RW#3#>RX,_NRY=?29RZPYPTC7P<PZPY1DI9R[C7PHPU^D5S0;%KHS0<P5PU%K5R\Q08C]S0=1x<ZPJQ0;\HS0>%KJS0?PHQ0;Q0<Q0=C]S0@%w<P0Q0>\JS0A%K0S0BPJQ0>Q0?Q0@C]S0CQ00Q0A\0R]P0Q0AQ0BQ0CC]R^P0Q0AQ0CPJQ0>Q0@PHQ0;Q0=P5PUQ08&0?UC\C\C\C\:0=]^Q00H0:S0DP<1I0<G^PZ1IJZG^PY1IHYPTP[P5P\&085P[PTP4J07S0EM;z1FV9R^P^1IU^S0FM9~WHP6P2P:P8PYP5PT1fGYS0G%;4R]'1%>FRF,XKR_'0XD511XNR`%;TRa,14S0H/0_X?7S0I11`aRb/0_%>BRB,1`Rc/0_P4XE7Rd1064$0WXI7XE7RePbPcPdPdPdP7P7g01\d1164H0V#4XQ7XD7S0JP`P`%4`S0KPaPBPdPd%4]XE5S0LPTPB%4BS0MElS0NM:VP_P_%4_S0OG61DI;Rc/LT%;cRb=@7BRfP\%K7Rg%;6=@7]1L6420U6440TXI5XE5RhPcPb%4bPTPBQ0MM9eP4CdS0PPf1L[T%;[Rb=@7BRcP\PgPhP[Pb%4bPTPBQ0MM9eP;CdRiPc%c[Rj%9bRb1DI2Rk#cRl%;k#9Rk1bKPRm1C>KRn%9P1C>QRo[[Rp%9KRqg01;NRrA[KP6UWBRP%9Q\rRs^BqRt1bKFS0Q%9F1C>_Ru[\nS0RA[KF6VrXBqS0S%9_\rS0T^BqS0U1bKLRF%9L1C>MRv[\nRwA[KL6VrXBqRL%9M\rRx^BqRyP4P2O1S0VPxP:P<O1S0WQ0TP2P=O1S0XPsP8P4f:O2XAnS0YPv^AnRvP=P4f;RzO2XAnS0ZPu^AnS0[PzP4f<O2XAnS0\Po^AnRop-0Rzg00Q0Ru#|R{%nuRu20Q76S0]&0P7R|&0O7R}P}P?P@P@PAP:J0N20M71S0^%HKR?%OE5`752}5U}S0_&0F@S0`%HXR@Q0^'BS0a%HBS0b'BA`7?GS0c52}CT20E}ARAP4P;g00Q\REg00R<R~'y20D4;=@E~dB0C7>6H0BR~b<b=b>X47W@104Q,M6S0d11X6RQ/1B/0_[^47^@zP4POPNfEO3b;b6b3b1b5b2b0b0b1b2b3b5b6b:b9b7b8Q0GQ02Q03PXQ0PPfPiPcPjPbPlPk%:1#J#JRk#>Rl,bKS0P%9l1XKlRb,C>Rj[\nS0eA[Kl6VrXBqS0f%9b\rS0g^BqS0hPmPpPPPtPFPwPLPyQ0VPxQ0WPsQ0XQ0gQ0YPvQ0ZPoQ0\Pj^AnS0iP{Pu&0A7S0jP|%OD9`7?S0k=2}@%Ok9`7?S0l,Y@,a}5U}PAP~b<b=b>10MX1CXb'MP4b;b6b3b1b5b2b0b0b1b2b3b5b6S0mb:b9b7b8CSGAQ06P6E5DmO2PUP2A?8Y:PYPT1FV:E<P<%:3#3#3#>R3,_NR@=?Z:S0n%:W#>RW,_NRk20@C>%|I60>IRC3?S0oPR1vSTS0p,vRPYAuIR9AhIS9S0q=tI:S0r9tICPUP<Q0nPYPRC7R>AuIR8,FV9@U4XFURDPUP<PZPYPRC7PDP<PZPTPYP9PRP41pRT%>1R1/0BRDPRP1%41S0sPTPBQ0MEsQ07Q06#;Rj=@7BRqP\PgPhQ06Pj%4jPTPBQ0MM9eP6CdRjPq1DI8Rr/LT%;rRl=@7BRcP\PgPhPrPl%4lPTPBQ0MM9eP:CdRhPc%crRr%9lRl1DI<Rg#cR\%;g#9RgPmPpPPPtPFPwPLPyP4P9O1S0tPxP:P8O1S0uPsP9P4P<O2XAnS0vPvP<P4P=O2XAnS0wPoP{PuQ0jP|%H1S0xQ0b52}PAP~b<b=b>PDP4b;b3b1b2b0b0b1b2b3b:b9b7b8CiL0<P>P<P:PZP@PYPRP5PTQ0G%;RR>'1S0y1fG@RD11D]S0zQ0GC=XD5P`114>R]11DaS0{/04S0|7NDX?7113NRn11`>Ri/04RfQ0H;Z`X?710inS0}11naRE/0`S0~'811`1S10/0nS1111nBR;/0`S12'8Q0}Q0~Q11Q12PdPePiQ10PdPdPdQ0JP`P`Q0KP>P1PdPdQ0LPRP1Q0sElS0sM:VS12PnPn%4nS11G6PdPePEP;PdPdPdQ0JPnPnQ11PaPBQ0NM:VS0NP`P`Q0KG6EPPjPqPhPcPrPlP\PgPmPpPPPtPFPwPLPyQ0tPxQ0uPsQ0vPvQ0wPoP{PuQ0]P|Q0aQ0x'BS0~%H3RaQ0^'BS0}52}Q0}Q0b'BS13Q0a52}5Q}PAP~b<b=b>X4711X4S14/11S151134S16Q16/1BS17Q14C=^47P4PNO1S18b;b3b1b2b0b0b1b2b3b:b9b7b8PDQ02Q03P3PjPqPhPcPrPlP\PgQ0PQ0eQ0fQ0hPmPpPPPtPFPwPLPyQ0VPxQ0WPsQ0XQ0gQ0YPvQ0ZPoQ0\Q0iP{PuQ0jP|Q0k=2}aQ0l,Ya,a}5U}PAP~b<b=b>10M31C3b'MP4b;b6b3b1b5b2b0b0b1b2b3b5b6b:b9b7b8CSS19GAQ0GQ02Q03PXPjPqPhPcPrPlP\PgQ0mb:b9b7b8CSS0mDRQ06P6E5P`10]_X?7S1:10i_Q10/0_PdPePiQ10Q12P_P_Q0OG6PjPqPhPcPrPlP\PgPmPpPPPtQ0QQ0RQ0SQ0UPFPwPLPyQ0VPxQ0WQ0TQ0XPsQ0YPvQ0ZQ0[Q0\PoP{PuQ0]P|P}Q0_Q0`Q0~Q0c52}CTPAP~b<b=b>X47X@zQ0d11Q1/0_[^47^@zP4POPNfFO3S1;b;b6b3b1b5b2b0b0b1b2b3b5b6b:b9b7b8Q0GQ0mGAS1<P5PTQ0z/0_XD5PnQ0I10E_10;_PdPePEP;Q0NP_P_Q0OG6PjPqPhPcPrPlP\PgPmPpPPPtQ0QQ0RQ0SQ0UPFPwPLPyQ0VPxQ0WQ0TQ0XPsQ0YPvQ0ZQ0[Q0\PoP{PuQ0]P|P}Q0_Q0`Q13Q0c52}CTPAP~b<b=b>X47X@zQ0d1136/1B/0_[^47^@zQ1;b;b6b3b1b5b2b0b0b1b2b3b5b6b:b9b7b8PDQ19GAS0IQ06P6E5S1=M9WE5P<Q0oPYPRC7P<PCQ0nPkPYPRP`1fGkRO11O>/04S1>5N]X?711WNRQAZf]`X?710iQS1?11Q>Rf/0`S1@'8Q10/0QS1A11Q1Ra/0`S1B'8Q1?Q1@Q1AQ1BPdPePiQ10Q12PQPQ%4QS12G6PdPePfPaPdPdPdQ0JPQPQQ12P>P1Q0sM:VS0sP`P`Q0KG6EPPjPqPhPcPrPlP\PgPmPpPPPtPFPwPLPyQ0tPxQ0uPsQ0vPvQ0wPoP{PuQ0]P|Q0~%HWR`Q0^'BS0K52}Q0KQ0x'BS0xQ0a52}5Q}PAP~b<b=b>X47Q1511W4S15Q15/11S0aQ14C=^47Q18b;b3b1b2b0b0b1b2b3b:b9b7b8POQ02Q03PWPjPqPhPcPrPlP\PgQ0PQ0eQ0fQ0hPmPpPPPtPFPwPLPyQ0VPxQ0WPsQ0XQ0gQ0YPvQ0ZPoQ0\Q0iP{PuQ0jP|Q0k=2}`Q0l,Y`,a}5U}PAP~b<b=b>10MW1CWb'MP4b;b6b3b1b5b2b0b0b1b2b3b5b6b:b9b7b8CSS14GAQ0GQ0mDRQ0yPO1DIC#;,1OS0mQ0GC=eQ1<Q0y/0_ePQQ1:10f_10a_PdPePfPaQ0sP_P_Q0OG6PjPqPhPcPrPlP\PgPmPpPPPtQ0QQ0RQ0SQ0UPFPwPLPyQ0VPxQ0WQ0TQ0XPsQ0YPvQ0ZQ0[Q0\PoP{PuQ0]P|P}Q0_Q0`Q0xQ0c52}CTPAP~b<b=b>X47X@zQ0d11W6/11/0_[^47^@zQ1;b;b6b3b1b5b2b0b0b1b2b3b5b6b:b9b7b8POQ14GAQ0m/0_eS1:M9WE5P<Q0oPRQ0p%qRR19EGYS0pPCQ0rPHPkPUP=A?<Y8S0r??@9R`??kCS0yP4PR1FVCE<XCHP<PCQ0nPkQ1:DmQ0pPNPXPRPW11X>#4DgS1<E5P<Q0oPSPTQ0p=EG1Q0qP:PHPkPUP=Q0yAEG41S0GPSAhIS8,FVS0~E<XCHPHQ0:#:#3#>R8,_NRiPUP=Q0yP4PSQ0~E<XCHPUP<Q0nPiPSC7S0:Q0~9@U4XFUS10PUP<PZPiPSC7Q10P<PZPTPYP9PSP41pST10KBR9PSPK%4KS10PTPBQ0MEsPjPqPhPcPrPlP\PgPmPpPPPtPFPwPLPyQ0tPxQ0uPsQ0vPvQ0wPoP{PuQ0jP|Q0b92}?PAP~b<b=b>P9P4b;b3b1b2b0b0b1b2b3b:b9b7b8CiL0HPUP<PZ%qSR99EGYS0b20ITSRBQ0q,FVE<PHQ0bPUQ01A?=Y2P4PBAhIS2,FVE<XCHP4PiPNPXPSP8%;SRI,1X#4DgJ0JPUP=Q0rPiPBQ0~E<P4bGbGQ0:P<P:PZP@PiPSP5PT1fGiRB/1IS0:PDQ0zPBC=XD5118NR5114IS0zQ0|7NDX?7Pn115IRX/04S0|Q0H;Z5X?710XnS0~10E5S0r'8115KR2/0nS0110;5S0b'8Q0~Q0rQ01Q0bPdPePXP2PdPdPdQ0JP5P5%45S0JPIPKPdPdQ0LPSPKQ10ElM:VS10PnPnQ11G6PdPePEP;Q0NP5P5Q0JG6EPPjPqPhPcPrPlP\PgPmPpPPPtPFPwPLPyQ0tPxQ0uPsQ0vPvQ0wPoP{PuQ0]P|%H8S0LQ0^'BS0^/B?R?Q0}52}Q13Q0^52}5Q}PAP~b<b=b>X471184S0b/1KS01Q16Q17Q0bC=^47Q18b;b3b1b2b0b0b1b2b3b:b9b7b8PDQ19GAPBQ02Q03P8PjPqPhPcPrPlP\PgQ0PQ0eQ0fQ0hPmPpPPPtPFPwPLPyQ0VPxQ0WPsQ0XQ0gQ0YPvQ0ZPoQ0\Q0iP{PuQ0jP|Q0kQ0L52}Q0LQ0l'Y,a}5U}PAP~b<b=b>10M81C8b'MP4b;b6b3b1b5b2b0b0b1b2b3b5b6b:b9b7b8CSRbDRQ06P6E5P5Q0z/0_X?710X_102_PdPePXP2Q10P_P_Q0OG6PjPqPhPcPrPlP\PgPmPpPPPtQ0QQ0RQ0SQ0UPFPwPLPyQ0VPxQ0WQ0TQ0XPsQ0YPvQ0ZQ0[Q0\PoP{PuQ0]P|P}Q0_Q0`Q0c92}?CTPAP~b<b=b>X47X@zQ0d1186/1K/0_[^47^@zQ1;b;b6b3b1b5b2b0b0b1b2b3b5b6b:b9b7b8PBPbGAS1;Q1=M9WE5P<Q0oPiPSC7P<PCQ0nPkPiPSP5Q0zQ1>7NOX?7PQQ0|?Z]5X?710XQS0|10f5Rz'8102QRK10a5RM'8Q0|PzPKPMPdPePXP2Q10PQPQQ12G6PdPePfPaQ0sP5P5Q0JG6EPPjPqPhPcPrPlP\PgPmPpPPPtPFPwPLPyQ0tPxQ0uPsQ0vPvQ0wPoP{PuQ0]P|Q0K92}?Q0xQ0^52}5Q}PAP~b<b=b>X47Q01Q15Q0aQ0bC=^47Q18b;b3b1b2b0b0b1b2b3b:b9b7b8POQ14GAPBPbDRQ0:POQ0mPBC=eQ1;Q0:/0_eQ1:M9WE5AEGk1R1PNPWPRP811W>#4DgR>E5Q0pQ1<E5PHPkPUP=Q0yQ0G=EG9PTP^E<XCHPHPiPUP=Q0yAEG49PTP^E<XCHPHP@PUP=Q0yP4PTP^E<XCHPUP<Q0nP@PTC7A@U4^XFUQ07PUQ08Q09P=P`P@PTC7P=P`P@P[C7PHQ0;Q0<Q0=1x=`PJQ0>Q0?Q0@%w=P0Q0AQ0BQ0CQ00Q0DP=1I0=G^P`1IJ`G^P@1IH@PTP[Q0EM;zP^P^Q0FM9~WHP6P<P:PZP@Q1=DmO2P<Q0oP@PTC7P<PCQ0nPkP@PTPnQ0HQ1>7NOX?7PQPEP4P]PnC=X?710EQR]10fnR<'810;QRZ10anR:'8P]P<PZP:PdPePEP;Q0NPQPQQ12G6PdPePfPaQ0sPnPnQ11G6EPPjPqPhPcPrPlP\PgPmPpPPPtPFPwPLPyQ0tPxQ0uPsQ0vPvQ0wPoP{PuQ0]P|Q13Q0K52}Q0xQ0}52}5Q}PAP~b<b=b>X47Q17Q15Q0aQ16C=^47Q18b;b3b1b2b0b0b1b2b3b:b9b7b8POQ14GAPDQ19DRQ0{POQ0mPDC=eQ0IQ0{/0_eQ1:M9WE5AEGi9PNP8PSP3118I#4DgE5P1P>E5Q0pQ1<E5M9kM9kM9kbPbNbMbKbJbOPUP6Q049?4YQ057?@??kCPY%GT#G#G#Gg010N,FVE<eWLWRo"). Qed.

End Canary.

Section Defs.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
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
      (rl dA_2f6b0s 0x2f6b0) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (rl dA_2f848 0x2f870) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (rl dA_2f848 0x2f8d0) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (rl dA_2f848 0x2f898) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (rl dA_2f848 0x2f860) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (rl dA_2f848 0x2f858) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (rl dF_153e8 0x1541c)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (rl dF_131d0 0x131d0)).

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
      (rl dA_2f6b8 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (rl dA_2f6b8 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (rl dA_2f6b8 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0)))  (* [comment removed for export] *)
      (rl dA_2f848 0x2f868) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0)))  (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (rl dA_2f848 0x2f849) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (rl dA_1f630 0x1f630) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
