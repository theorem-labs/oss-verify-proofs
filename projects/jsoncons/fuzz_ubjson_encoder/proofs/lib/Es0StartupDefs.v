(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import StartupTac ArgvEnv RefLayout RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0StartupDefs () := "C47Corelib7Program6Basics4flipK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Peano2le00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs@after_last_slashC13~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib7Classes?RelationClassesCPreOrder_TransitiveK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib7Classes?RelationClasses<transitivityK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib5Arith8PeanoNat3Nat;le_preorderc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefsCafter_last_slash_leC13~~~C46Stdlib9micromega;ZifyClasses:impl_morphc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs<progname_offC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs4rnd4C13~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3minC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z8min_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List<length_skipnC47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List=length_firstnK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecDbytes_le_to_Z_nonnegC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExecCbytes_le_to_Z_boundC13~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StepTac6u_Z2bvC13~~~C47Corelib4Init5Logic6eq_symc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs5rnd4wC13~~~K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExecDlength_Z_to_le_bytesC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs3rlwC13~~~C47Corelib4Init9Datatypes3appc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefsGlength_word_to_le_bytesC13~~~C46Stdlib5Lists4List:length_appc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs;guard_bytesC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefsBlength_guard_bytesC13~~~C47Corelib4Init5Logic6eq_indc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs8canary_wC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs:canary_valC13~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLibAZ_to_le_bytes_lezC13~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare3at_C13~~~C35stdpp7tactics<f_equal_helpC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib6at_natC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec6wbytesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib3subC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec>rdn_wbytes_hitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec:rdn_firstnC13~~~C46Stdlib9micromega;ZifyClasses8or_morphC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec>rdn_wbytes_outC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib7rdn_subC13~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec7rdn_appC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_Zc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Es0StartupDefs<rd_guard_genC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "p'0h04__x1h14__x2h22H0h37__arithh44__ffh58__varmaph65__with74cstrh85cstr0h93acch:1ih;1sh<1Hh=2IHh>1bi001bh?1ch@5cstr1hA1xp;1p;2p;3p;4p;8p;5p;Bp;<p;7p-1R0p10000R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9g000Nj1@Tg0013j1cTg001Qj1TTg0024j1BTg002TR1j22Tg002nj3=Tg004Hj24Tg004hj25Tg005?R0j13Tg005_R2j21Tg006<R3j20Tg006Xj26Tg0072j4JTg007Yj1?Tg008>j1FTg008^j2GTg009<j1YTg009Zj4XTg00:8j1WTg00:Vj1VTg00;Aj2ETg00;dj1STg00<Fj2DTg00<ij38Tg00=Lj2RTg00=nj2QTg00>Zj3PTg00?4j3OTg00?Sj4NTg00@Ej4<Tg00A0j3MTg00AfR4j1;Tg00BEj1>Tg00Bjj1ITg00CHj2UTg00Cnj3bTg00D[j8aTg00EJj3`Tg00Ejj5_Tg00FLlBHTg00G2l<]Tg00GWj4\Tg00HBj7[Tg00Hfj8ZTg00IJl<^Tg00IoR5P5P5g00JNR6P6P6g00JlR7P0P0P0P2g00KLR8f3R9f2R:f1R;g00KoR<g00LNR=f0R>MBHp=LP5P6P1P0P3g00Llf5R3f4R?P9P:P;P>M<]p=7P6P;g00MNP>C\p=:P;g00N5R@g00NTRAPAg00O4RBP>g00OTF[p=9P9P@PAPAPBP:P;P>GZp=CP5P5P6P6P4P0P0P9g00P4P:P;P>M<^p=AP5P5P5P6P6P6P7P0P0P0P2P8P3P?P9P:P;P>MBHp=Kg00PXR8#@R2#@#@#cR0#TR7#BR4P712>;R@A=9:;1479,5:'2[^95^:5RCX;415:<R<,2;%3;RD%3:RE/1=RF'0P;PD166DRGP<PFP:PE166ERF166=CLE712;:10DER<P;PDPGP:PEPFE7P>CJRGP<%?9RD%39RH,0=RIPDPIg00Q=RJ#FRK%BJRJP61G6:P;%Y6CXRL%W6RM%V6RN1E68RO1E62RP':,9NRQ%SARA1D6=986P,:O,9NCC1RNBRBP>P:g00QiRRg00RIRS'61Q>:=PRSdAO6=;CNRSb4b5b6X06X1610>;RT11:=,0;[^06^16P>f6RU#3RV%33P9O3b3b8b7b2C<%F7RW?=:;147W,5:'2eX<@X95X:5P5P1g00Ri9M51%;:R1PRP5%>2#>#>#>#I,U09b03R0P1P;n0100000020000R25=?147?RW,51RX%;WRY,5:RZP9P1P2P0PRPRPRP5P>%;?RRP9n0100000020000/2RP>%;9RR/2R%I8R8,1HR0/00PRP011>8R2XA6R[P9PH166HR\CAR]PRP0P]E712:910EHR^P:PEPFP9PHP\E7P;CJR\P^%??RH%3?,0=R_PHP_PKPJ1G6;PM1D68R`986ORa/:a,9NPBPSb4b5b6X061022^06P>f7#3RbO1b3b8b7b2C<12:R10E0P:PEPFPRP0P]E7P\P^PHP_PHP_PKPJPLPMPNPQPAA86P`R`,:O,9NCCPBPSb4b5b6X06X1611:8,0;\T^06^16P>PbPVP9O3b3b8b7b2C<n0110000020001b>O312XZ11E8R9%3WRV'1RT11V8RA,1ERQ'0PXPTP1P9P[P:PEPFCAPWPV166VR9EKPZPQP:PEPFPYPAP[PWPVP9CAEKE7PGP<PDPI147URU#?%3U,0=PHP_PKPJPLPMA86aPA86O`':,9NPBPSb4b5b6X06X16112;11;8,1>'0^06^16P>f9,47#3PbO2b3b@b8b7b2C<GaA`73?R??=:;147?,5:'2eX<@X95X:5X=CX;4X?7P>D_W;o"). Qed.

Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h04__x1h14__x2h21Hh32H0h47__arithh54__ffh68__varmaph75__with84cstrh95cstr0h:1sp;1p;3p;2p;6p;4p;<p;Bp;7p;8g000Nj18Tg0013j1\Tg001Qj1JTg0024j1:Tg00SQj3[Tg002TR0j23Tg004Hj22Tg004hj2<Tg005?R1j11Tg006<R2j20Tg006Xj24Tg005_R3j29Tg00Tnj6RTg0072j4QTg007Yj1>Tg008>j1NTg008^j2MTg009<j1LTg009Zj4ITg00:8j1HTg00:Vj1GTg00<Fj2FTg00;dj1ETg00;Aj2;Tg00<ij3KTg00=Lj2DTg00=nj2CTg00>Zj3BTg00?4j3OTg00?Sj4PTg00@Ej4ATg00UXj1STg002nj3TTg00G2l<@Tg00FLlBZTg00GWj4YTg00HBj7WTg00Hfj8XTf0R4g00KoR5;T5p=5g00IoR6g00JNR7P0P1P2g00LlR8f5R9f4f3R:f2R;f1R<P4M<@p=?P6P7P0P1P2P8P5g00LNR8P<P5P8P4M<@p=VP6P6P6P7P7P7g00JlP1P1P1P3g00KLP5P8P:P;P<P4MBZp=UP7P<g00MNP4CYp=6P<g00N5R3g00NTR1P1g00O4R6P4g00OTFWp=7P:P3P1P1P6P;P<P4GXp==g00PXR3#8R2#8#8#\#JR0#:A[4551355R=%5<R>120<R?,<5R@'3RA[13>?%1>RB%1?RC'0P>PB147BRDP?PC147CREE?%5;RF120;RG,<5'3\=1088R5%1FRH%1G,98'0[RGP=PAP5198CRA,0B1478R=/V=P>PBPDP@PAP=P?PCPECUE?ERP4CQPG%>F108H120:RH#>%1H,08g00Q=RH#N%:HP71M7;P<%L7CI%H7%G7RHPH1F78RF/6F,7H%E1R11;73R31;72R29K7F'6,7HC=P11632,7HC=1DH6P4P;g00QiRHg00RIR6'41C4;=BH6dAO78<CPb5b6b7X07X17198;,0<\510<;[^07^17P41209#1%59#1P:O3b4b9b8b3CAb2%S41204'3eW:o"). Qed.

(* [comment removed for export] *)
Definition rnd4 (rnd : bv 128) (j : nat) : list byte := firstn 4 (skipn j (at_random_bytes rnd)).
Definition rnd4w (rnd : bv 128) (j : nat) : word := Z_to_bv 64 (bytes_le_to_Z (rnd4 rnd j)).
Definition rlw (rnd : bv 128) (j : nat) : word := v_lw (rnd4w rnd j).
Definition guard_bytes (rnd : bv 128) : list byte :=
  firstn 1 (word_to_le_bytes 4 (rlw rnd 0)) ++ [Z_to_bv 8 0] ++ sub (word_to_le_bytes 4 (rlw rnd 0)) 2 2
  ++ word_to_le_bytes 4 (rlw rnd 4).
Definition canary_w (rnd : bv 128) : word := Z_to_bv 64 (bytes_le_to_Z (guard_bytes rnd)).

Lemma rnd4_eq : forall rnd j, firstn 4 (skipn j (at_random_bytes rnd)) = rnd4 rnd j.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h01jh13rndp;1p;2g000Nj10Tg0013j12Tg001Qj11Tg0024j13Tg00Vnj25Tg006Xj24Tg00PX#0#0#0R0#0#0#0#0#2#1g00Io%20#1#3f1f0'5'4W0W1o"). Qed.
Lemma length_rnd4 : forall rnd j, (j + 4 <= 16)%nat -> length (rnd4 rnd j) = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h01nh14__p1h24__p2h34__p3h44__x1h54__x2h64__x3h72H0h82H1h92Hjh:3Hj0h;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@1jhA1mhB3rndhC1xhD1yhE2z0hF2z1p&0p;1p;2p;3p;<p;4p;6p;Bp;7p;8g000Nj12Tg0013j1PTg001Qj1RTg00Afj1:Tg004hj2YTg002TR0j2TTg00X<j1lTg00Y@j3gTg004Hj2?Tg00Y^j2@Tg00Z5j2DTg00Bjj1[Tg005?R1j14Tg00ZLj27Tg00Zij2CTg00[FR2j2MTg00>Zj1Qj3;Tg00[cj2xTg00\Fj3pTg006Xj2BTg00G2l<VTg005_R3j2WTg006<R4j23Tg0072j4aTg007Yj1`Tg00\cj2_Tg00]Ej2=Tg00]aj21Tg00^<j2>Tg00^Vj2^Tg00_8j1]Tg00_Vj2\Tg00`7j2<Tg00``j3ZTg00aIj2NTg008>k103Tg00EJj3LTg0024k102Tg008^j2XTg009Zk401Tg00:8k100Tg00:Vj1~Tg00;Aj2KTg00<Fj2ETg00BEj1{Tg00;dj1yTg00b5j3wTg00<ij3vTg00=Lj2oTg00=nj2nTg00?4j3mTg00?Sj4kTg00@Ej4jTg00bXj1qTg00ccj6OTg00dAj3rTg00dbj3sTg00eAj3tTg00Vnj2uTg00FLlBITg00ecj3fTg00fLj6zTg00GWj4UTg00HBj7eTg00g0j7|Tg00gTj7}Tg00Hfj8dTf0R5#:#:p=6g00IoR6f1R7;;5p=9g00JNR8?;75p=0P6P6P6P8P8P8g00h8P1P1P1f6R9g00hXf5R:f4R;f3R<f2R=P7P5MBIp=iP6P6P6P8P8P8g00i?P1P1P1P2g00i_P:P;P<P=P7P5MBIp=hP6P6P6P8P8P8g00JlP1P1P1P3g00KLP:P;P<P=P7P5MBIp=cP6P8P0P1P4g00LlP:P;P<P=P7P5M<Vp=bAf875p=8P7g00N5R4g00NTR0P0g00O4R3P5Ezp=JP8P7g00jBP5CUp=FP7P4P0P0P3P5g00OTFep=5P=P4P0P0P3P7P5F|p=AP8P7g00MNP5CUp=HP=P4P0P0P3P7P5F}p=SP<P4P0P0P3P=P7P5Gdp=Gg00PXR4#2R2#2R>#2R?#2R@#2#2#2#P#Rg00KoRA#:RB#:RC#:RD#:RE,Y5%6E#6#6#6#6#6RF'TP6%P?#RR?%l=RG9g?7RH'?RI,@E195EX06P61??GRJ/D71@E5/9EX06P6PF1D5=,@E/9EX061DF7RK,@ERL/9E%[>R>g00LNRM%[@R@%47RN'7'CRO'MRP/0>P6P8%Q6P1%Q8%45,0N19751x753pXD6XC6PLPPPEP>1B8>RPPKPO1775,CMXA8X08PFP@1B8@ROP7PN1B8NRKFiEhPEP>PPM<V1Y7ERL/TF1WN>R1/3@RQPLP1P7PNPKPEP>PPEcPFP@POEbP5CaPQ%`=%4=,3M%4<,7@RQ,_M1=MQ1CMQRO/0Q'113QMA;8OM'1'>%4;,7@,CMP81^>51=>51M>5RO/0>'1135>10O5'1'>1M>7P8p-0ROg00Q=RQ%]4,\8RF1<8DRD5Z8RP1<8C9Z8F1<8B1<8ARA'8'8'8g00jiRB'N1<8E18DA'8/NB18PA/NB&03Q5LQ5LQ3L&02QP81X8=P71X8<H01&008%~8RQ1JQ:1K84RB1E8>RA'F,5QRP5AQ%{4,K8R4/HA,5Q1FB4,5Q5AQ5SQ%y0R0PQ1JQ91E8@RB1K82R25w8RD,F4,5Q5AQ1E8M,HD,5Qf7,JQ5AQ5SQP0PQAv82A/HB,5QP0PPCGCGCG1oQ3P5P=g00QiRQg00RIR3'B1n5==;Q3dAm8M7Ckb<b=b>X48X58X68X1OX2OW3105>,1<13=>105='1'>17@=R3,0<,1:133M/19'>1W<>/3@10<>[[[^48^58^68^1O^2O^3OP5A;8<Mf8#4R8,7@,=M1=><P<P8P7P=P;P9O9b;bFb8bEb7b?b:CjPJ%q=EOPIAr?7GEOAs?EH,??At?EHEO1u=7,??/9EeW9X@6WBo"). Qed.
Lemma rnd4_val : forall rnd j, bytes_le_to_Z (rnd4 rnd j) = bv_unsigned (rnd4w rnd j).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h02Hah14__x1h27__arithh34__ffh48__varmaph55__with64cstrh73Hl0h86__sat1h94__x2h:6__sat2h;6__sat3h<4__p1h=6__sat0h>6__sat4h?1Hh@2H0hA2H1hB2HbhC2HlhD6__sat5hE6__sat6hF5cstr0hG1jhH1nhI3rndhJ2z1p&0p;1p;2p;3p;4p;6p;7p;5p;Bp;<p;8g000Nj18Tg0013j1NTg001Qj1XTg00Vnj29Tg00kUj1HTg00CHj2uTg00lRj2YTg00m<j1gTg00nTj1`Tg00Bjj1@Tg004Hj24Tg00okj21Tg00]Ej2=Tg00Afj1KTg00X<j1ATg00Y@j3DTg00Y^j2rTg002TR0j2FTg005?R1j16Tg00[FR2j2QTg006<R3j22Tg006Xj2BTg007Yj1MTg00^Vj2_Tg00>Zj3<Tg00]aj2ITg00^<j2WTg010Hj2;Tg0110j2?Tg011Mj3>Tg00`7j2PTg00ecj3OTg00aIj2VTg008>k101Tg00EJj3^Tg0024k100Tg009<j1~Tg008^j2\Tg009Zj4TTg00:8j1}Tg00:Vj1|Tg00fLj6zTg00;Aj2RTg00<Fj2ETg00GWj4LTg00BEj1tTg00gTj7qTg00;dj1pTg00=Lj2mTg00=nj2lTg00?4j3iTg00?Sj4jTg00@Ej4kTg00dbj3hTg00eAj3nTg00ccj6oTg0072j4ZTg0121j2fTg012]j3eTg013@j5sTg013gj3]Tg014Jj3vTg015Sj4wTg015oj2xTg00FLlBcTg00G2l<bTg00HBj7yTg00g0j7aTg00Hfj8{Tg00LNR4f0R5'2p=0f1R6%65'?p=7g00IoR7P7P7g00JNR8P8P8g00i?P1P1P1P2g00i_f5R2f4R9f3R:f2R;P6P5MBcp=dP7P8P0P1P3g00LlP2P9P:P;P6P5M<bp=S1965,4;p=51465#6p=J1=45p=:P6g00N5R3g00NTR1P1g00O4R0P5g00OTFyp=3P;P3P1P1P0P6P5Fap=[P8P6g00MNP5CLp=CP:P3P1P1P0P;P6P5G{p=GP8P6g017>P5CLp=Ug00PXR<#8R=#8R>#8R?#8#8R@#8RA#8#N#XP8%NARB1965RC#HRD,uB'YPD%gC%0D19;6RC#`%HC%@=RE%@?RF%N?#XR?/4C'7'1'=P7g00KoRC#KRG#KRH#K#KRI%A:9D?;RJ,4?RK'rRL1F5IXH71FLI%@>R>%6KRM'QRN/2>PLPNPIP>1B8>RNPKPM1B8MEdPIP>PNESA5?:;RM#M%6M#0%A99D?:,4?RK#M%6K#0%A29D?9,J?RK,_>1=>K1Q>KRL=<8>'I12K>A<8LK'I'Wf6RL#A9D?2,J?,Q>P8f7RK=5?L,7FRO,;E%:ERPf8RQ=5?K,7FRK#0f9RR/9Q,J?RQ,?FRS,1ERT#:[[%0ERUg017eRVf:RW=5?R,7FRX=>E6UW011EX#0\V^0Up-0RYg00Q=RZ1P8HRH1P8G1P8CRC5O85O8g00jiRG'V&01ZR[3^R\&00ZR]P8%~8R^P6P81\8;R_P;P^CTCT%}8R`%|8RaPaP3P1P1P0PaP3P1P1P0P9EzP81R8<R<g00jBR31E8>RbCL,3a5[a%t=,R8Rc/Cb,3aP8P<P3PcCL,3a5[aFq%p1R11C<b,3aRbCG1ma0R0P5P;g00QiRcg00RIR3'B1l5;=<c3dAi846CjR3b3b4b5X18X98W<A<85>,I;126>RcA<856'I'WPc[^18^98^<YP5%AW9D?R,J?RY,=>PYP:P9O4b2b:b;bJbAbFb6CkAh?IJ,4?An?IJEo1FMIRMePMPEA5?9:R:#6RM,?FRJ%@@RY1F:I12M>RcP:PM1B8MPIP>PNESP5CZRMPc1929R:,4?Rd#MRe%6dRf#0RgA5?L2RL#6R2,?F,;ERh%0O11EK#:[\PRKA>ES6VVX0URO%0T\V^0URTP[P]P^P`1E84R41E8ERi'U,3aP0P3b3b4b5PPP5b2b=b8b6b7PMPcPePgPhPKPOPTAO8CH/VG,fC=^Z[P]1\86RZP`PaPbP11E8F=e8<1E8Y'C,3aCGP0P3b3b4b5X18125>1?F6/2Y[^18P5PQP9O2b2b=b8b6b7Ds11EJ11EYRJ'2%H:1FdI12f>R:PdPf1B8fPIP>PNESP6CZRNP:%MLRL%02R21;EYR>%0Y%:J[\PRIA>EY6VVX0URY%0J\V^0URf1;ES%0Xf;RX=5?W,7FRS,1E#:[\Pf<Rd/9XR9,4?,7FRQ=>E6VVX0U11EQ#0\V^0UP[P]PZP`Pa1C4<,3aR4P1P4CGP0P3b3b4b5X18%05%06[^18P5%H9PWO2b2b8b:b;b>b6b7PNP:PLP2P>PIPYPf%@ARA,;E%0A11EARf#:[\PA>EA6VVX0U%0f\V^0U1;ES%0Qf=RQ=5?d,7F,1E#:[\Pf>/9QRQ,4?,7FRF=>E6VVX0U11EFRF#0\V^0UP\P]P8P_P6P^CTP`Pa1R8=R=%N@9]8i'C,3aP1Pa1U<=,3aP1A]8iB,U<,3aCGCGP0P3b3b4b5X18X98126J1=6;1=;f[[^18^98P5PF%HQPRPXO4b2b8b:b;b>bDbEb6b73vb@bCbBb?Cw1x65,YB9<8DeXG7WIo"). Qed.
Lemma length_word_to_le_bytes : forall n v, length (word_to_le_bytes n v) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h01nh11vp;1p;2p;3g000Nj10Tg0013j12Tg001Qj11Tg00lRj23Tg018Aj27Tg019Xj26Tg004Hj25Tg00>Zj34Tg00IoR0g00PX#0#0#0R1#0#0#0#2R2#1f1R3f0R4,32'7%21#11634'5=403eW1W0o"). Qed.
Lemma length_guard_bytes : forall rnd, length (guard_bytes rnd) = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h01nh13rndp;1p;2p;3p;6g000Nj16Tg0013j1BTg001Qj1@Tg00Afj14Tg01:`j2:Tg019Xj29Tg00dbj38Tg004Hj20Tg00CHj2ETg008>j1DTg00EJj3CTg00Y@j3>Tg01;mj3;Tg004hj21Tg00Y^j23Tg00Z5j2=Tg006Xj2JTg01<Jj2ATg00dAj3ITg00eAj3?Tg01=kj3<Tg01>Jj1FTg00>Zj3GTg00ccj6HTg00IoR0f1R1f0R23Gp=2f2R31112'1p=7P0f4f3P3P1P2EHp=5g00PX#6#6#6R3#6#6#6#6#B#@%B3R3#@R4g00KoR5#4R6%46R7#4#4R81:25R9'9R:584R;'0R<g00LN,E3%D45C4R3A>47:R=9847R>1:28R?,98R@5;4RA5;4RB,04RC'1%48#4#4#4RD,22X001043RE104ARF'11:15,98R59846,04RG/12/2DX00104>RH104@RI'1A7GE2/2DX00104:RG,36A>4759847,041:18,98,04R1'1972E/2DX00104=RJ,371045,36R5112177E/2DX001=G71372/11975E/2DX00P813621=27,37/1177E/2DX00P813681=87,37/1277E/2DX001J0DPI1A8?D5PG1A89D5PJAI47:D5PHA?47=D5P<A?46:D5PFA<4>@D5PCA<43AD5A;4;B,04A<4;BD5%F2,04/2DeW1o"). Qed.
Lemma canary_val : forall rnd, bytes_le_to_Z (guard_bytes rnd) = bv_unsigned (canary_w rnd).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h04__x1h12Hah22Hbh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91Hh:1nh;3rndp;1p;2p;6p;3p;4p;7p;8g000Nj11Tg0013j19Tg001Qj1@Tg01>Jj15Tg00kUj14Tg00CHj2WTg00lRj2BTg00m<j1NTg00nTj1GTg00Bjj17Tg004Hj2;Tg005?j18Tg0110j2:Tg00okj26Tg00]Ej22Tg00Afj10Tg01?_j1VTg01A;j6UTg010Hj2RTg011Mj3QTg008>j1OTg0024j1MTg008^j2LTg00:8j1KTg00:Vj1ITg00<Fj2>Tg00;Aj2HTg00GWj4?Tg00;dj1JTg00=Lj2FTg006Xj2ETg00=nj2DTg00>Zj3ATg00?4j3PTg00?Sj4CTg013gj3STg014Jj3TTg015Sj4\Tg01AWj1[Tg006<j2ZTg00HBj7YTg00Hfj8XTg00LNR0f0R1'Zp=3f1R2g00N5R3g00NTR4P4g00O4R5P1g00OTFYp=<f3R6P3P4P4P5f2R3P2P1GXp==g00PXR7#1R8#1#1R9#1#1#1R:#1#9#@g00JNR;%9:R<%51R=#4R>,W<'BP>%N=%3>%52R=#G%4=%78R8%79R?%99#@R9/;=#8':'6'2g00IoR=%53R@,;9%56#4R9%81,:?,68'2X:=P1g00Ko#0#0#0#0#0#0#0#0R=%V3EU%4@%8=,:?,68'2%7:R:,R8R?1208%3:168:R=,20[[R@%38RAg017eRBAQ8:2UW1R:%3=\B^1ARAg00Q=RB#ORC%MBRB1L;2RD%K;RE%I;RFP;1>;0g00MN1H;7R7C?,<FRG%J4R4PGC=1FF5R5P1P3g00QiRGg00RIRH'E1D13=AGHdAP;02CCR0b4b7b8X0;%31%32[^0;P1f6#5#4RHf5O2b3b5b6P?P@P:PAPCPBPDPEPFP;P7g017>1>;8=S;<C?,<FRFP4PFC=P5P0b4b7b8X0;121=122=[^0;P1PHP6O2b3b5b65T9b2b2b9C\%[1,B<9A;>eW;o"). Qed.
Lemma canary_bytes : forall rnd, word_to_le_bytes 8 (canary_w rnd) = guard_bytes rnd.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h01zh12Hvh25lemmah31nh43rndp;1p;2p;3p;4p;6p;:p;9g000Nj11Tg0013j14Tg001Qj1:Tg01Bij1>Tg01>Jj15Tg00kUj13Tg01AWj1FTg00lRj2<Tg00>Zj32j17Tg0024j1?Tg00Afj10Tg01D=R0j26Tg004Hj28Tg01E:j1LTg01Ejj4=Tg01FQj1KTg01G@j4;Tg01H7j3JTg01Hmj1ETg01I\j6CTg01JGj29Tg01K3l:BTg01K`l9ATg01?_j1DTg01LZj1@Tg00CHj2GTg01A;j6HTg019Xj2ITg00PX#1#1#1R1#1#1#1R2#1#4#:f0R3#>g00JNR4%53R5#3%42R2%F3R6'<32P4f1R7#5R8#3R9%41#:R1#?R:g00Ko#0#0#0#0#0#0#0#0R;/63f2#5R<32X04g00IoR=1818;2;P:%7:R>%L:%3<R?,6;181<R1/6?P:^04R@^3=RAP=P@%7=RBP4P:%74P>C=RCC=RDP=P@PCP4P:P>%K:C;C;9JADP0P;P1P=PB%E=P1P;P3ECP?P?194?M:BP<P<19:<M9AW2%D7%@8O21G29,<2P3EHb11I;6=2:5eW4o"). Qed.

(* [comment removed for export] *)
Lemma rd_guard_gen : forall segs (D : word -> option byte) (w0 w4 : list byte) (g : Z),
  length w0 = 4%nat -> length w4 = 4%nat ->
  (0 <= g)%Z -> (g + 8 < 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) w0)
                          (Z_to_bv 64 (g + 4)) w4)
                  (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0]) (Z_to_bv 64 g) 8 = Some (firstn 1 w0 ++ [Z_to_bv 8 0] ++ sub w0 2 2 ++ w4).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h02L1h14__x1h24cstrh35cstr0h47__arithh56__sat5h66__sat6h74__ffh88__varmaph95__with:1zh;1nh<4__x2h=1bh>1xh?4__p1h@1khA1HhB1ohC1yhD2HahE4__x3hF5cstr1hG1jhH1AhI1DhJ3Hg0hK3Hg1hL2HjhM2HkhN2L0hO2L4hP1UhQ2U0hR1ghS5lemmahT1mhU4segshV2w0hW2w4p%0p&0p;1p;2p;3p;4p;6p;8p;5p;9p;;p;<p;7p;Bg0024j1wTg000Nj1NTg0013j1~Tg001Qk100Tg01N3k107Tg004Hj2<Tg00Afj1fTg00Bjj1UTg005_R0j20Tg00okk20>Tg00]Ej2LTg006<R1j21Tg00]aj2MTg005?R2j15Tg00>Zj1Qj34Tg00[ck20RTg00\Fk30QTg0072k402Tg007Yj1DTg010Hk20JTg011Mk30HTg00`7j2_Tg00ecj3jTg00aIj2zTg008>j1yTg00EJj3pTg008^j2oTg009<k10?Tg009Zj4aTg00:8k10<Tg00:Vk10;Tg00<Fj2XTg00;Aj2kTg00fLk60\Tg00;dk10YTg00=Lk20XTg006Xj2\Tg00=nk20WTg00?4k30VTg00?Sk40UTg013gk30TTg014Jk305Tg00CHj23k10PTg00lRj2>Tg01NUj1eTg01OPj3PTg01P5j2dTg00BEk10OTg01Q9k80NTg01QVk203Tg00ccj6ATg01Rdj3FTg004hj2rTg00dbk301Tg01Smj4bTg01;mj3ZTg01U8S00j4;k20Ck10DTg01V?j2KTg01Vaj1}Tg01W?k40ITg01Wbj5lTg01A;j6cTg002TR3j2|Tg00@Ej4CTg01Y3k80ETg00^<j2?Tg01Z@j6YTg01Zhl9VTg01\9m90ATg01E:k10@Tg01Ejj4hTg01FQk10=Tg01G@j4`Tg01H7k30FTg01K3k40GTg01JGj2mTg01]Hk804m;0MTg01Hmk10KTg01I\k60LTg01K`m90:Tg00G2l<[Tg01^Cl9nTg00GWj4gTg00HBj7uTg00g0k709Tg00<ik30STg00Hfk806Tg00IJm<0[Tg00FLmB08Tg00gTk70ZTg00IoR4f1R5f0R634p=sg00LNR7/16p=8g00JNR8?456p=:1\86p=7P4P8P6P2P5f2R9f3R:f4R;f5R<f6R=f7R>f8R?M<[p=GA44;:P9P5P6H02p=HP9g00N5R@g00NTRAPAg00O4RBP8P5g00MNRCP6Cgg00OTRDFup=2P9P@PAPAPBP5P6K09p=TB0S856p==P8P5PCP6Cgp=SP;P@PAPAPBP:P9P5P@PAPAPBP6PDFuL06p=JP:P@PAPAPBP9P5P6L06p=RP8P5g017>P6Cgp=vP5P@PAPAPBP6PDFup=i1095/16p=BP8P5g00jBP6Cgp=tP8P;P:P9P5P6EAp=6P4P8P8P8P2P2P<P;P:P9P5P6N<0[p=qP8P8P8P8P8P8P0P6P5P9P0P:P;P<P=P>P?f9RDNB08p=EP8P8P1P>P1P=P<P;P:P9P5P6M<[p=911<;11:9P5P6CCp=IP4P;P:P9P5P6EAp=OP4P8P3P2P1g00LlP<P;P:P9P5P6M<[p={1156,?9p=^1195/?6p=]11:91156'?p=@P9P@PAPAPBP5P6K0Zp=WP4P4P4P8P8P8g00JlP2P2P2P0g00KLP<P;P:P9P5P6NB08p>0B11;:P9P5P6CCp=xg01_M#wS01g00PXR0#NR2#NR1#NR3#N#N#NRC#~RE$00RF%~3S02$00RG$07[S03%wGRH1<G9g00KoRI#fRJ#fRK#fS04#fRL'sS05Q05%89RM%U3R3,0:%U2RN%UCRC+0>RO'L%86RP1163'MRQ10=5RR1<G>RSPL%5SRT%U1RU':RV%Q4RW%Q8RX%55%56RY':1s5620R5640QXC4X>4S06PSPT%7TPLPU%7URTM9GP;DHRSPV1<GDRZ/sLS07%5ZR[/:UR\PWPXQ06PZP[%7[PLPUPTM9GP=H02R]P\%DZR^%8[R_f;R`,<GS08#DRaQ08#5S09#8Rb20JNCRc1L7N%8C1L7O[[Rd%8NS0:g017eReB0HNC5UWDRCQ0:%8O\e]DRep-0Rfg00Q=Rg1_8KS0;1_8J1_8IS0<5j85j8g00jiS0='z%ygRI3pRh%wgRiP81o89S0>P5&0?8RjCaRk&0<8Rl&0;8Rm1X87Rn1k82R252mPmP@PAPAPBP;J0\R@5Tm&0YARAPm1k80Ro92mnRpPAPm1=o2Rq,SnDJCR20XmBRBP6P9g00QiRrg00RIRs'\20W69=4rsdB0V875H0URsb7b8b9X18X<8W?%85Rr/M9109:Rt#8\r[^18^<8^?fP611?3P?f=RuP>f:RvO5b4b5b6b3b2b0b0PSPVP]P\P^P_PaPbPcPdPCPePhPiPkPlPm1X83Rk92m29Tm@PAPm1=ok1X8NR@>0T8ERh'v,imS0?PAPm1vqhDJCRPBPsb7b8b9X18X<8X?f1153,M91053/LO1LtO[[^18^<8^?fP6%8?P?PuP>PDO5b4b5b6b3b2b0b0405UX@813ER,>E/:R\Q^@81<G=RQPL%5QRR/:URfPWPXQ06PQPR%7RPLPUPTM9GP:DHRRPf1<G?S0@PLQ0@#5RQ/:URtPWPXQ06Q0@PQ%7QPLPUPTM9GP<DHR_PtQ0@#DR^%8QRQ1<GvS0A#DRVQ0A#5RS#8RwPcPdPCPePIPi1o85RxPlPmPpPAPpCRPBPsb7b8b9X18Pr\P^18P6f<RPPDO2b4b5b6b3b2b0b0PRPfP_PtP^PQPVPwPcPdPCPePIPiPxPlPmQ0?PAPm1vohDJPBPsb7b8b9X181063/LORQ1L5O[^18P6PPP?O2b4b5b6b3b2b0b0605<13E<,>E/:<%59=B:3R^%5:,0;,:9Rf%5;RR,0<Ry10u=,3E%e<5PE10u6,3E54FX:8PF10P<Rz,3ER{/dRR|%5<R},0=,0u,3ER~94F6X=FPz106},3E=4F~X:8P8PF&0PER~P~10zR10PyRyPF\8/\~1<GuS0BPLQ0B#5S0C/:UR~PWPXQ06Q0BQ0CQ0C#7PLPUPTM9GPvDHS0DP~f?S0E,<GRzPL%5zRR/:UR}PWPXQ06PzPR%7RPLPUPTM9GPPDHS0FP}%D=S0G%5=#8S0Hf@S0I,<GRR#DS0J%5R#8S0KfB,<GRR#DS0L%5R#8RRPcPdPCPePIPiP8Q0>P51o8:CaPl&0O0,k8Rz,=q1=2z,=o't,imPBPsb7b8b9X18X<8XE81065/091059Rz,06':^18^<8^E8P6%5PR2PufDO3b4b5b6bFb3b2b0b0L0N1>E{P>P<Q0DP~Q0FP}Q0GQ0HQ0JQ0KQ0LPRPcPdPCPeQ04,_8Q0;Q0<5j85j8Q0='z=pgIPiP8P8Q0>P9PjCaP5PjCaPlPm1k81R192mnPAPm1=o1=2mkPAPmPpPAA2mok9TmpCRCRCRPBPsb7b8b9X18X<811z3%8:11:3'M\M[\r^18^<8P6P2PuP<PDPvO5b4b5b6bFb3b2b0b0O2D613Ey94F|e%e;9PE{R|203{;EAP:P6D6WAWLXMMX:8XG4X@810P:,3E94F|\f\^\M^:8^G4^@8P`13E>RM=FvDR^10>URf,3ES0>;F?S0=%U0R0,0>R|,3ES0<Q02/37%yG5pGR73FS02PJ1rKLS0;,rJS04PMB01GJDPGPDPKPKCb=ZG?9ZG7&07HR{P`Q0=PMPJC;R;B01GJv,KH94{6XB{RyP{P`P^PMPJC;PyP`P^PLPMPDPJP4PZPP13E?S0L=F`vS0KQ0LP6C;1KHvS0J54{X;4P`PDPvPMP>106SS0H/1OX:8S0GPLAB?YOX;4%5LRy,0>R2POPfPOP6X>8Rr1156#}XC8X>8RzP2PfPrPrPrP8P8g01`L1056H0I#7XT8X;8R2P>P>%7>S0FPyPUPrPr%7YX>4S0DPLPUPTEqS0MM:EPOPO%7OS0NG9P_PtQ0APL1:SURpPWPXQ06Q0APS%7SPLPUPTM9GP>DHR1PpPVPw1<GPS0O#DRgQ0O#5S0P#8RRPcPdPCPePIPiPxPlPmQ0?PAPm1X8UR},=oS0Q/ShDJPBPsb7b8b9X18S0R105US0S/1O\Q^18S0TP6f>S0UPvO2S0Vb4b5b6b3b2b0b0EIPZP=DO1>EMS0WP5D6DlPLP=Ec1|JL110UR~PJP0%70S0XPLPUPTE{P_PtP1PpPVPwPgPRPcPdPCPePIPiPjPl1X80Rq=2m}PBPsb7b8b9P~P6b4b5b6b3b2b0b0CCL0EP;P`P?P^Q0>PMPJPfQ0L,>ES0Y%5JR^;B6S0Z106[S0[Q0Y3^X:8P>106^R;10?UR~AB~[63]X:8PL10?^P~10~YS0\P?C@X;410>^S0]/1fS0^10fyS0_/1>S0`'?11|fS0a10fUS0b/1>R['?Q0^Q0`Q0aP[PrPzQ0]P|PrPrPrP2P>P>Q0FP^P0PrPrQ0DPJP0Q0XEqS0aM:ES0`PfPf%7fR[G9PrPzQ0_Q0bPrPrPrP2PfPfP[PyPUQ0MM:ES0^P>P>Q0FG9EYP_PtP1PpPVPwPgPRPcPdPCPePIPiPxPl1=oqR[Q0Q52mQ0Q/=}S0c=2mo5WmPBPsb7b8b9X181060S0d106US0eQ0e/0US0fP6C@^18P6Q0UO1S0gb4b5b6b3b2b0b0CCQ0@P<DOQ0WP5D6Q0>,>ES0>P9PUP_PtP1PpPVPwPgPRPcPdPCPePIPiPjPlA2mn}A2m}k5TmPBPsb7b8b9%8U11U3'MP6b4b5b6S0hb3b2b0b0O2S0iD6P>11;OX:8S0jQ0]POP|POPrPzQ0]P|Q0`POPOQ0NG9P_PtP1PpPVPwPgPRPcPdPCPePIPiPxPlPmQ0?PAPm1S[hDJPBPsb7b8b9X181050S0k/1O\Q^18Q0Vb4b5b6b3b2b0b0EIQ0WP5D6S0lPfQ0[/1OX:8PLQ0\/1OX;4Q0_POQ0bPOPrPzQ0_Q0bQ0^POPOQ0NG9P_PtP1PpPVPwPgPRPcPdPCPePIPiPxPlPmQ0?PAPmQ0c/ShDJPBPsb7b8b9X18S0^Q0S?BUO\Q^18S0SQ0Vb4b5b6b3b2b0b0EIQ0@P<DOQ0>Q0iD6M9VEAP`Q02PMPJC;P`P7Q0=Q0<PMPJP|Q0ZQ0Y7^;X:8P>P;10?0R<10<^S0ZP6C@X:8Q0]/1|S0=10|^S02/1>S0i'?11||S0>10|0S0@/1>Rf'?Q0=Q0iQ0>PfPrPzQ0]P|Q0`P|P|%7|RfG9PrPzQ02Q0@PrPrPrP2P|P|PfP^P0Q0aM:ES0`P>P>Q0FG9EYP_PtP1PpPVPwPgPRPcPdPCPePIPiPxPlA2m[[1=[qS0F=2mo5WmPBPsb7b8b9X18Q0dQ0dQ0d/00S0>P6C@^18Q0gb4b5b6b3b2b0b0CCQ0WP5D6Q0<,>ERfP9P0P_PtP1PpPVPwPgPRPcPdPCPePIPiPjPlA2mnqS0gA2mqk5TmPBPsb7b8b9%80S0i1103'MP6b4b5b6S0=b3b2b0b0O2S0bD6Q0W/0^S0_Pf1<G7#5S0\,0fS0[Q0WC@eQ0lQ0_/1OeP|Q0jQ02POQ0@POPrPzQ02Q0@Q0`POPOQ0NG9P_PtP1PpPVPwPgPRPcPdPCPePIPiPxPlPmQ0?PAPmQ0F/ShDJPBPsb7b8b9X18RwQ0k?B0O\Q^18RVQ0Vb4b5b6b3b2b0b0EIPfQ0bD6Q0[/1OeM9VEAPF1dM^Rf13E<Rt=4F6X=FP>13E;94FtX:8Q0],3E,\FQ0WP5D6Q0<=4Ffe%eJS0W9PEMRf203MJEAQ0<=4FfPFPtPu13EDS0<=FP`S0]10DUS0[,3ES0b;FvS0V10D0,3ES0k;F7S0`P6Q04C;PGP`PKPKCbS04=ZGvRf9ZG7,KH54{X=FPPQ0K13E~S0@;FDS02?Ft7S0_PJQ0;PtP7PGPvPKPKCbS0l=ZGDPPP7Q02PtP<Q0jQ0ZPO10<0S0jPOPrPzQ0ZQ0jPrPrPrP2P<P<%7<S0mP^P0Q0aM:ES0nPOPOQ0NG9P]P\Q08PLQ09/:URMPWPXQ06Q08Q09Q09#7PLPUPTM9GP?DHR>PMPaPbQ0B#DR_Q0C#8R|PcPdPCPePwPVP6Q0EP`O2S0Cb4b5b6b3b2b0b0EI1>EtS0BP:P0P]P\P>PMPaPbP_P|Q0=b3b2b0b0O2S0=D6Q0BQ0\'0S0\/1OeS09DlPF10?NRV,3ERwPuQ0`P6Q0;C;1KHf54{X=FPPQ0_PKPLPwQ0lPDP{PPQ02PwPKC;S0lQ04,KH94{6XB{RfP{PPQ0KPwPKC;PfP?%5KRf,06S04,3E10DNS0;,3ES0o54FX:81\FwQ0YP9D6Q0L/df=4FwR9eP9PFQ0</dfQ0U13EvS0Y=FuPR9P6PKC;PGPPPKPKCb,KH54{X=FPuQ0]PLQ0<P`PKPKP4Q08Q0UP9Q0YP6C;1KHP54{X;4PuP`PPQ0<PDQ0P=B6OX:8PLABvYOX;410DyRvPOQ0[POPrPzPvQ0[PrPrPrP2PDPD%7DPyPUQ0MM:EPOPOQ0NG9P1PpQ0OPLQ0P/:URvPWPXQ06Q0OQ0PQ0P#7PLPUPTM9GPDDHS0PPvPgPRQ0U,<GRG#DS0U%5G#8RGPcPdPCPeQ0RQ0TP6Q0IPPO2b4b5b6b3b2b0b0EIQ08P?DOQ0<,>EP:D6DlPLP?Ec1rKKR?/|L10NNR`/1UR9P?P`PKPN%7NR?PKPNP?J0BPLPUPTE{P1PpQ0PPvPgPRQ0UPGPcPdPCPePIPiPjPl1=@@RG=2m}PBPsb7b8b9P9P6b4b5b6b3b2b0b0CCN90AQ0oP6EcbAQ0lPPPDQ0KQ0@PwPKPVQ04Q0b,>ER9AB9S63]X:8P~Q0;/0fR9/16S0lQ0HQ0;3^X:8PLP9Q0[Q0[/0YS0HQ0;C@X;410VfRY/1~R910~yRS/1VRR'?10VNRg/1~Rv10~URp/1VR1'?P9PRPvP1PrPzPYPgPrPrPrP2PVPV%7VS0oPfPNPrPrQ0DPKPNP?EqS0DM:ES0UP~P~%7~S0PG9PrPzPSPpPrPrPrP2P~P~Q0PPyPUQ0MM:ES0MPVPVQ0oG9EYP]P\P>PMPaPbP_P|PcPdPCPePIPiPxPl1=o@Ro/=@R1Q0Q52mQ0c=2mo5WmPBPsb7b8b9X18106NS0</0NS08Q0eQ0fQ0<C@^18P6Q0EO1S0Eb4b5b6b3b2b0b0CCPZP=DOQ0@,>ERvP:PUP]P\P>PMPaPbP_P|Q0hb3b2b0b0O2RRD61>EwR9P:PNP]P\P>PMPaPbP_P|PcPdPCPePIPiPjPlA2mn@S0hA2m@k5TmPBPsb7b8b9Q0:11N3'MP6b4b5b6b3b2b0b0O2RnD6PVQ04/1OX:8PYPOPgPOPrPzPYPgQ0UPOPOQ0NG9P]P\P>PMPaPbP_P|PcPdPCPePIPiPxPlPmQ0?PAPm1S1hDJPBPsb7b8b9X18105N?BNO\Q^18Q0Cb4b5b6b3b2b0b0EIP9PnD6S0?P~Q0GPLQ0H/1OX;4PSPOPpPOPrPzPSPpQ0MPOPOQ0NG9P]P\P>PMPaPbP_P|PcPdPCPeQ0^Q0SQ0Cb4b5b6b3b2b0b0EIS0CPZP=DOPvPRD6S0SM9VEAPPQ0_PwPKC;PPP7Q02PtPwPKPVQ04Q0k,>ERZABZ^6RQ3]X:8P<Q0lQ0;7^;X:811Y<S0lQ0Z/1VRh'?11g<RAQ0j/1VR:'?Q0lPhPAP:PrPzPYPgQ0UP<P<Q0mG9PrPzQ0ZQ0jQ0nPVPVQ0oG9EYP]P\P>PMPaPbP_P|PcPdPCPePIPiPxPlA2m1[Q0F=2mo5WmPBPsb7b8b9X18Q08Q0dQ0>Q0<C@^18Q0Eb4b5b6b3b2b0b0CCQ0BQ0=D6P9PnD6109fRnQ0BQ0\P9C@eQ0?11nOeQ09M9VEAPFQ0@PuQ0`P6PLC;Q0J54{X=FP{PPQ02Q0@PLC;Q0J94{6XB{Q07P{%Q{Rn&0@{PuQ0VQ0bPLC;PuQ0VQ0bQ0AC;PFP{^;4R9%QFRoP4P{PWPnChR1Q0V-0CuQ03P9\FRVQ03#QRgPFP9PoP1ChRo&0DuQ01Q03PV[RYQ01#QR:Q03PVPgPoChRgQ00Q01PY[RAQ01PYP:PgChR:Q01PYPgQ03PVPoPFP9P1P4P{Pn&0={C`C`C`C`:0FA:Q00H0GPuQ01/muL04Q0VQ03Q0V'mL04Q0bQ0b,mFPLQ0AP4PW&0K4Q0APLP6J0LN;0MQ0JQ0JQ0J,m{N90:WSP=PPPDQ0KQ0@Q0SDlO2PPQ0_Q0@PLC;PPP7Q02PtQ0@PLP~106yRL?]ZQX:8P<Q0[/0yP6P;Q0[C@X:811S<R;Q0Z/1~RQ'?11p<RZQ0j/1~R7'?P;PQPZP7PrPzPSPpQ0MP<P<Q0mG9PrPzQ0ZQ0jQ0nP~P~Q0PG9EYP]P\P>PMPaPbP_P|PcPdPCPePIPiPxPlQ0c=2m[Q0FQ0Q52m5WmPBPsb7b8b9X18Q0fQ0dQ0>Q0eC@^18Q0Eb4b5b6b3b2b0b0CCQ0BQ0=D6PvPRD610vyRyQ0BQ0\PvC@eP~11LOX:8Q0CPvPRD611yOeQ09M9VEA%eK9PEwP5PNPKPUP]P\P>PMPaPbP_P|PcPdPCPePIPiPjPlQ0hPBPsb7b8b9Q0:P6b4b5b6b3b2b0b010NfRKP311`3RwPrPzPKP`PrPrPrP2PNPNP?PfPNQ0DM:ERfP3P3%73RyG9P]P\P>PMPaPbP_P|PcPdPCPePIPiPjPlA2mGkPBPsb7b8b9PwP6b4b5b6b3b2b0b0Dx1:UK1:U`RwP8P8PXPrPX1:56#}XC8X>8ROPUPUPTPKP`PfM<[P]P\P>PMPaPbP_P|PcPdPCPePIPiPjPl1t}G,imPBPsb7b8b9PwP6b4b5b6b3b2b0b0CCO6EAM9nQ0W9PEtP5P0PJPNP]P\P>PMPaPbP_P|PcPdPCPePIPiPjPlQ0gPBPsb7b8b9Q0iP6b4b5b6b3b2b0b0100^RJP31000R5/13RtPrPzPJP5PrPrPrP2P0P0Q0XP^P0Q0aM:ER0P3P3PyG9P]P\P>PMPaPbP_P|PcPdPCPePIPiPjPl1=qqRq=2mkPBPsb7b8b9PtP6b4b5b6b3b2b0b0Dx1:NJ1:N5RtP8P8PXPrPXPOPNPNP?PJP5P0M<[P]P\P>PMPaPbP_P|PcPdPCPePIPiPjPl1t@q,imPBPsb7b8b9PtP6b4b5b6b3b2b0b0CCO6EAM9nQ0LQ0W5PEP6EcbAM9nbHbQbPWKWJWOWNXR8XWHWVWIWUo"). Qed.

Lemma rd_guard_at : forall segs (D : word -> option byte) rnd (g : Z),
  (0 <= g)%Z -> (g + 8 < 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) (word_to_le_bytes 4 (rlw rnd 0)))
                          (Z_to_bv 64 (g + 4)) (word_to_le_bytes 4 (rlw rnd 4)))
                  (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0]) (Z_to_bv 64 g) 8 = Some (guard_bytes rnd).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0StartupDefs ()) ["FPX_1"] "h01Dh11gh23rndh34segsp;1p;2p;9p;3p;4g0024j1:Tg000Nj11Tg0013j14Tg001Qj17Tg01N3j1;Tg006<j2ETg00Bjj12Tg005_j26Tg00okj2>Tg00]Ej2=Tg00Afj10Tg01:`j28Tg019Xj29Tg01<Jj2<Tg01a0l9FTg00CHj23Tg01Rdj35Tg008>j1DTg00EJj3CTg01U8j4@Tg01>Jj1ATg01V?j2BTg00>Zj3?Tg01_M#:g00PXR0#1R1#1R2#1R3#1#1#1R4#4R5#7%43R6#7R7#;[%14#4#7g00JNg00LNR8f0R9'Ef1R:%23'6%21%24'>'=f5R4f4R1g00KoR3#0#0#0#0R;f3R</83R3'9R=18<;R>,9;R?f2R@1<;31<;>P:P9M9F%:7R9#;P4135@R4=51=%22,6@,35;5?%20,6@,351368%D75C735P4%0;#0#0#0C@%A<,B93?eUUW1W2W0W3o"). Qed.

Section Defs.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rnd : bv 128.

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
      (Z_to_bv 64 0xcaf70) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xeb2d8) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xeb338) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0xeb300) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0xeb2c8) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0xeb2c0) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x9b73c)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x34544)).

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
      (Z_to_bv 64 0xeb068) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xeb078) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xeb070) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xeb2e8) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0xeb2f0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xcb050) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xcb038) (word_to_le_bytes 8 (Z_to_bv 64 0xcb050)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xcaf78) (word_to_le_bytes 8 (Z_to_bv 64 0xcaf78)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xeb2d0) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0xcafa0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xcaf98) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0xcb010) (word_to_le_bytes 8 (Z_to_bv 64 0xeb308)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xcaff0) (word_to_le_bytes 8 (Z_to_bv 64 0xcaff0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xcaf80) (word_to_le_bytes 8 (Z_to_bv 64 0xcaf78)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xcaf88) (word_to_le_bytes 8 (Z_to_bv 64 0xcaf78)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xcaf90) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xeb2b0) (word_to_le_bytes 4 (rlw rnd 0)))   (* [comment removed for export] *)
      (Z_to_bv 64 0xeb2b4) (word_to_le_bytes 4 (rlw rnd 4)))   (* [comment removed for export] *)
      (Z_to_bv 64 0xeb2b1) [Z_to_bv 8 0])                       (* [comment removed for export] *)
      (Z_to_bv 64 0xcb030) (word_to_le_bytes 8 (canary_w rnd)). (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0xb95c0) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.

End FPX_1.
