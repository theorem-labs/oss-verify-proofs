(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Export Walk.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Export SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SFModel () := "K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z3b2zK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec9SoftFloat6wrap64C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec9SoftFloat:wrap64_modC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec9SoftFloat5mk128C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec9SoftFloat4lo64C13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SFModel;lo64_mk128'C13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:shiftl_0_rC56Stdlib6ZArith6BinInt1Z8sub_diagC56Stdlib6ZArith6BinInt1Z?shiftr_shiftl_lC56Stdlib6ZArith6BinInt1Z:shiftr_lorC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec9SoftFloat4hi64C13~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic3and01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SFModel:hi64_mk128C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SFModel:lo64_mk128C13~~~C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z8lxor_lorK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z9land_commc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SFModel@lor_disjoint_addC13~~~C56Stdlib6ZArith6BinInt1Z@land_lor_distr_rK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SFModel6land_1C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SFModel8land_W64C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7SFModel>land_even_maskC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7ZBridge;Z_to_bv_eqmC13~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signed".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma b2z_Zb2z : b2z = Z.b2z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01bp;2g0000j20Tg000Jg000j]0g001H'0o"). Qed.

Ltac zb_masks_in H :=
  repeat match type of H with
  | context [Z.land ?x ?m] =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z in H
        by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  end.

(* [comment removed for export] *)
Ltac zs_wrap e ::= zs_wrap_land e.
Ltac zs_wrap_in e H ::= zs_wrap_land_in e H.
Ltac zs_idioms ::= zs_idioms_land.
Ltac zs_idioms_in H ::= zs_idioms_land_in H.

Ltac unfold_sf_in H :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H.
Ltac unfold_sf :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI].

Ltac norm_model H := unfold_sf_in H; zb_fold_lits_in H.

Ltac get_head t := lazymatch t with ?g _ => get_head g | _ => t end.

(* [comment removed for export] *)
Tactic Notation "model_hyp" ident(HR) constr(t) :=
  assert (HR : t = t) by reflexivity;
  let h := get_head t in unfold h in HR at 2;
  norm_model HR.

(* [comment removed for export] *)
Notation W64 := 18446744073709551615%Z.

(* [comment removed for export] *)
Ltac model_eval :=
  lazy -[Z.shiftr Z.shiftl Z.land Z.lor Z.lxor Z.lnot Z.mul Z.add Z.sub Z.opp Z.modulo Z.div
         Z.ltb Z.eqb Z.leb Z.pow bv_unsigned].

(* [comment removed for export] *)
Tactic Notation "model_end" constr(X) constr(t) :=
  replace (Z_to_bv 64 X) with (Z_to_bv 64 t) by (f_equal; model_eval; reflexivity).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lo64_mk128' : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi)%Z -> lo64 (mk128 hi lo) = lo.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "p'0h06__sat1h14__x1h27__arithh34__ffh46__sat0h58__varmaph65__with71bh84__p1h93Hloh:1Hh;2Hah<1ah=2loh>2H0h?3Hhih@2HihA1ei001ehB2hihC1ihD1ni011nhE1ohF1si021shG1zp;1p;2p;3p;4p;6p;7p;5p;8g001ej1;Tg002Jj1KTg002hj2CTg003Ej20Tg003aR0j27Tg004<j2ITg004\j2JTg0059j2YTg005Yj36Tg0063j1OTg006Qj2HTg006oj21Tg007Pj25Tg007nj29Tg008Kj2?Tg008hj2oTg009Mj2:Tg009iR1j2bTg00:Cj1`Tg00:bj2_Tg00;Jj3^Tg00;nj2[Tg0000j2LTg00<Oj1XTg00<oj1WTg00=Oj2VTg00=mj1UTg00>Kj1TTg00?6j2QTg00?Yj2BTg00@<j1NTg00@^j3PTg00AAj2MTg00Acj2RTg00BOj3STg00Bnj4~Tg00C`j3}Tg00DGj3|Tg00Dnj6<j7nTg00ELj2{Tg00Elj1ETg00FER2j2qTg00Fej1pTg00GEj6eTg00Gij1@Tg00HGj3cTg00Hmj4DTg00IXj6dTg00J<j1aTg00JZj3fTg00K=j5gTg00Kbj4hTg00LKj4iTg00Lgj1jTg00MGj3kTg00Moj4lTg00NTj3mTg00O6j3]Tg00OYj3\Tg00P<j1rTg00PZj3sTg00Q=j6tTg00QYj1uTg00Rlj1ZTg00TCj2vTg00UUj1wTg00Vfj7xTg00WJj8yTg00Wnj7zTg00XRR3f0R4':p=8g000JR5f1R6;64p=3g000jR7P6g00Y0P4CDp==P6g00YWR8g00Z6R9P9g00ZVR:P4g00[6Fxp=4f3R;P8P9P9P:f2R<P6P4Gyp=2P5g00[VR=P;P<P6P4E<p=GP7P6g00\6P4CDp=FP<P8P9P9P:P6P4Fzp=>A6743p=A%84R>g00\]R?#;R@#KRA%;@#;#;#;#;R@#KRB'CRC,04RD'7RE%8<RFP71I;B/J<RG/YCRHA674;XG7RIP7%OBRJ,HGRKPIP5f5RI/IBRLf4RM'JRN/16RO11J6'511I<RP,34X75P511L6RQ11M6'911J<RR,54/3PX75P51?6BRS,1I194P/5R/3PX751o6B106B1:B6RP'bP110<BR11:B<f7RR1?;B'1f6RT/1;RU'911J;'5/3UP410;BP5g00]BRUf9RV1?IB'1f8RW/1IRX'9/54/3XX75RY194X/5U/3XX7511RMRZ#`19=Z/5U/3Ze1?MBR[,1WR\1_ABR]103AR^%8BR_103CR`[Ra[Rb%8ARcg00]bRdA^AB6UW;Re%8C\d^;cRcP6g00^>1[3A'LP^eO1R^Pag00^dRd#XRf%WdRd1V76Rg%U7Rh%T7Ri1Q7?R?1B7BRj'=,4iRk%N9RlAP7?j1B73Rm'=,4iC21Mi:RnP4P<1L5U1R4<=65UdAS736C~RUb3b5b6X17104BRo10S3[^17P4PWPMO2RSb2b0b4b09}W[CG11JMR[P]PbPePcP^PaPfPdPgPhPiPkPlPi1Fm?,4iRpPlA>ipkC2C2PnPUb3b5b6X17%86Rk17F1[\o^17P4PWPMPRO3b2b0b4b09|BME<W:P4O11:B;PY134XX75P5PZP=1{R3%ARRX%EX'qP2%AWR2%E211VT=65=P4%AVRTP7P3116V=65=^9EX=71:33/7`%pWW9f:RWP4PVFnWAP4O1%ETPWPRP]PbPePcP^Pap-0RTPfPdPgPhPiPiP8P9P9P:P;EeRV9>ipR`PlPpC2PnPUb3b5b6X17W817>6Pk[^17^8TP4f>RE/0CPEf=O3b2b0b4b0%@WPBPR1036RWP01CA6,0<%@;/0<[R0%@</061CA<,0;R5[%@M/0;\5Ac<64P6n2001000000120000000UX77X<7P0\W^77^<7P4f;RWPBP]PbPePcP^PaPfPdPgPhPiPiP8P9P9P:P7P?g00_PPmCD,4iEdPlPiP`Pl1=m?,4iC2C2PnPUb3b5b6X17X8T%A4g00`7[17k<103<[[^17^8TP4f?R3/0CP3PIPEO4b2b0b4b0P]PbPePcP^PaPfPdPgPhPi1B7A%a@5f7,=?,4iR@9>iVPlP@C2PnPUb3b5b6X17X8T176D106C[^17^8TP4%83P3PEO3b2b0b4b0O4b>P]PbPePcP^PaPfPdPgPhPi1Fj?,4iR?PlP?C2PnPUb3b5b6X171:B4REPP[^17P4PWPRO2b2b0b4b0DgChWDP4O1n200110200021010011101bFCi19\ZR\/5=%j\CGP[P]PbPePcP^PaPfPdPgPhPiP?Pl1Fmj,4iRm=>i?C2PnPUb3b5b6X1717_P\E^17PSb2b0b4b09kBMCGW:P4O1n200100000021100011000bEPQPIPBP6P]PbPePcP^PaPfPdPgPhPiPpPlPpC2PnPUb3b5b6X17Pk\>^17P4PIPMO2b2b0b4b0ClE<POAmLM6E<1HNJ/16A]NJ6E<X@>XC79\K<PHP]PbPePcP^PaPfPd%r7PhPmPnPUb3b5b6P_P4b2b0b4b09sGBEt%uG%ZGE<1v;<#w=67<eW?W9X=7XB7o"). Qed.

Lemma lo64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> lo64 (mk128 hi lo) = lo.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h06__sat2h14__x1h22Hah37__arithh44__ffh54__p1h66__sat1h78__varmaph85__with92hih:2lop;1p;2p;3p;4p;6p;7p;8g001ej12Tg002Jj19Tg002hj2>Tg003Ej20Tg003aj23Tg00:bj2ITg00;Jj3BTg00;nj2@Tg0000j26Tg00<Oj1=Tg00<oj1<Tg00=Oj2;Tg00=mj1RTg00>Kj1QTg00?Yj2:Tg00?6j2PTg00Hmj48Tg00J<j1HTg00JZj3CTg00@<j1ATg00AAj2DTg00Acj2ETg005Yj3FTg00BOj3GTg00Bnj4?Tg00GEj6JTg00`Tj4KTg009Mj2LTg00Vfj7MTg00Wnj7NTg00WJj8OTg00XRR0f0R1'Lp=1f1R2g00YWR3g00Z6R4P4g00ZVR5P1g00[6FMp=5f2R6P3P4P4P5P2P1FNp=4f3R7P3P4P4P5P6P2P1GOp=7g000jR8%11R9g00\]R:#2R;#9R<%2;#2#2#2#2R;#9R='>R>,01'3R?%16106>'3P7P61I<=R@100<RA%1=100>[RB[RC%1<RDg00]bREAB<=2UW2R=%1>\E^2DRDP2g00^>1@0<'6PAeO1RAPBg00^dRE#=RF%<ERE1;82RG%R8RH%Q8RIP81:80g00\61P8:R:C8,5IRJP8P:g00Y01:8<%H;5C8C8,5I54IR;%A4R<P;C71DI5R;P1P6g000JR:g00]BRK'61E16=F:KdAG802C?R0b4b7b8X18%12RK102>'3\?^18P1f6f5O2b3b0b6b0P@PCP=PDPAPBp-0RBPFPEPGPHPIPIP3P4P4P5P7EJ94IJP<PJC7P;P0b4b7b8X18W51392PK[^18^5BP1f7R1/0>P1f4O3b3b0b6b0CKUUX:8W9o"). Qed.

Lemma hi64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (mk128 hi lo) = hi.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h06__sat1h11zh27__arithh36__sat0h42Hah54__ffh68__varmaph75__with84__x1h93Hhih:3Hloh;2hih<2lop;1p;2p;3p;4p;7p;8p;6g001ej10Tg002Jj1>Tg002hj2DTg003Ej26Tg003aj2:Tg004<j28Tg004\j22Tg00aij27Tg0059j25Tg008Kj2BTg00bIj2ATg00:bj2dTg00;Jj3aTg00;nj2XTg0000j2@Tg00<Oj1UTg00<oj1TTg00=Oj2NTg00=mj1MTg00>Kj1KTg00?Yj2;Tg00?6j2GTg00Hmj49Tg00J<j1FTg00JZj3HTg00Wnj7ETg00@<j1ITg00WJj8JTg00AAj2CTg00Acj2LTg005Yj3?Tg00BOj3OTg00Bnj4PTg00bfj3QTg00cIj1RTg00cjj3STg00Dnj6=Tg00P<j1cTg00dMj3bTg00e6j1`Tg00eZj1]Tg00f<j4\Tg00fej3YTg00QYj1ZTg00Rlj1[Tg00TCj2WTg00gIj1VTg009Mj2^Tg00Vfj7_Tg00XRR0f0R1'^p=4g000jR2f1R3;?1p=1P3g00YWR4g00Z6R5P5g00ZVR6P1g00[6F_p=<P2f4R7f3R8f2R9P3P1E=p=3%41g00\]R:#0R;#>R<%0;#0#0#0#0R;#>R='DR>,61':R?%49169>':188=R@/29/7=RA/5>1117X1217@=RB179=RC'2151>/17X12RD1B==RE,88178=RF,21/5>/17X12RGP2P01871/2F/5>/17X12P8PG1A9>RG1271/5>/17X12RFP2P0PFP8PD1d<=RD160<RF%4=RH160>[RI[RJ%4<RKg00]bRLAa<=3UW4RM%4>\L^4KRKP3g00^>1X0<'@PFeO1RFPIg00^dRL#URN%TLRL1N23%M2RO%K2RPP4P5P5P6PPP4P5P5P6P21;20R4g00\6RQ1G2:R:C9,<PP2P:g00Y01;2<%F;5H2C9,<PFER;%I5P;GJ1CP6R6P1P9g000JR;g00]BR5'@1L19=?;5dAO203CPR5b5b6b7X82R;%43163>':\?^82R?P1f7P7O2b2b0b3b09Q8>1280%R8D3PGPDPJPMPKPFPIP;P?P1f6f5O2b2b0b3b09S9>E=PCPDPJPMPKPFPIPNPL%c2POP2P4PQ1;2=C9,<PP6P5b5b6b7PHP1b2b0b3b0R19b9=D31880%`8D3PE%]=E=PBP8P=P=P1C\D3PAAY@9=D3%ZA%[AD31W89#V/18eW9W:X<2X;2o"). Qed.

(* [comment removed for export] *)
Lemma mk128_regs : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z ->
  Z_to_bv 64 (lo64 (mk128 hi lo)) = Z_to_bv 64 lo /\ Z_to_bv 64 (hi64 (mk128 hi lo)) = Z_to_bv 64 hi.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h06__sat2h12Hah27__arithh36__sat1h44__x1h51zh64__ffh78__varmaph85__with92hih:2lop;1p;2p;3p;4p;7p;8p;6g001ej10Tg002Jj18Tg002hj2ATg003Ej24Tg003aj25Tg00J<j1LTg00hZj1ETg00i=j23Tg005Yj32Tg00TCj2<Tg00gIj17Tg0000j26Tg00icj4WTg00:bj2VTg00;Jj3UTg00;nj2RTg00<Oj1QTg00<oj1OTg00=Oj2KTg00=mj1HTg00>Kj1FTg00?Yj2:Tg00?6j2DTg00Hmj49Tg00JZj3CTg00Wnj7GTg00@<j1BTg00WJj8ITg00AAj2JTg00Acj2@Tg00BOj3MTg00Bnj4NTg00j>j4?Tg00Dnj6=Tg00UUj1PTg00kRj4>Tg009Mj2STg00Vfj7TTg00XRR0f0R1'Sp=1f1R2g00YWR3g00Z6R4P4g00ZVR5P1g00[6FTp=;g000jR6%11g00\]R7#0R8#8R9%08#0#0#0#0R8#8R:'AR;,41'5R<f2R=#114=;'5P6P=%L8R8#ER>1381R?f3R@,38RA32f4RB/<@#7,38138BRC52>'5X56P6P@A2>AARDA2>?C'5X56138=RC=2>CPD16>C16>ACW1<@=RA#7P@P=1V9:R>1409RC%1:140;[RD[R?%19REg00]bRFAU9:2UW1R:%1;\F^1EREP2g00^>1R09'6PCeO1RCPDg00^dRF#Q%OF1K62%H6%F6RFP3P4P4P5PFP3P4P4P5P61:60g00\61D67R7C9,;FP6P7g00Y01:69=C68C9,;FFGR8%B4P8GI1JF5P1P=g000JRFg00]BR5'61@1==2F5dAM602CNb6b7b8X46R0%12142;'5\<^46R<P1f6f5O2b2b0b3b0R;P>P?P:PEPCPDP0P<P1f7PBO2b2b0b3b0RBC?E=%PAP@P=P;PBC>E=UUX:6W9o"). Qed.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01Hh11ah21bh31zp;2p;3p;4p;6g006Qj28Tg005Yj31Tg00lfj22Tg00mDj20Tg00maj37Tg00LKj46Tg004\j23Tg00nKj34Tg00Q=j65Tg000jR0f1R1f0R2'8g00XR510P0f2R3/21R4f3/039102X30P01031P4A7312C61331A4312E5W0X20W1o"). Qed.

(* [comment removed for export] *)
Lemma land_even_mask : forall y, Z.land y 18446744073709551614 = (Z.land y 18446744073709551615 - Z.land y 1)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01zh14__x1h24__x2h37__arithh44__ffh58__varmaph65__with71yp;1p;2p;3p;4p;7p;6g001ej17Tg002Jj1=Tg006Qj20Tg004\j2:Tg008Kj29Tg005Yj34Tg00mDj28Tg00<Oj1ATg00<oj1?Tg00=Oj2>Tg00P<j1STg00nmj4RTg00=mj1PTg00>Kj1MTg00?6j2;Tg00oKj3LTg00@^j3JTg00Hmj4ITg00Vfj7HTg00AAj2ETg0000j2DTg00Acj2FTg00BOj3CTg00Bnj4GTg00onj1BTg010Pj36Tg00Q=j6KTg0114j1@Tg011Wj2<Tg012:j3NTg013Tj3OTg014>j11Tg00Dnj6QTf0R0#1#1p=U%10#1#1#1p=T%10#1#1#1#1#1#1#1p=2g000jR1g00XRR2740p=5P1f4f3f2R3f1R4P0EQp=3g00\]R5#U#T#2#2#2#2#2#2#2#7#=R6,00R7%=5R8,00R9':R:1046R;1048R<,90541X01R=1879P=g00^dR=#A%?=P11>13P4%S1CR%P1%M1R=g00YWg00Z6R>P>g00ZVR>P11;15R?g00_P%75,;1R59L1?=J15CIg00[6FH1E=>P0P3g000JR>g00]BR='D1F03=4>=dAC124CGb4b5b6X11X211804/949410^11^21P0P<P;O2b3P:1097R:%50X01R;1090R</06P;1009R4%57X01R21000R=/08P2P01096R2#5X01P11086,00P;%B0P2A6086EKP=%@0D3P4A6008D3P<1<90D3P:A6906D310791<79D39N79D31:68,00AO068D3X71o"). Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yh51zp;1p;2p;3p;4p;7p;6g001ej1FTg002Jj12Tg002hj2;Tg0059j20Tg005Yj31Tg0000j23Tg0063j1<Tg006Qj2:Tg00<Oj17Tg00<oj16Tg00P<j15Tg00=mj18Tg00>Kj19Tg00?Yj24Tg00Hmj4ETg00Vfj7DTg00AAj2=Tg00Acj2>Tg00BOj3?Tg00Bnj4@Tg009Mj2ATg00PZj3BTg00Dnj6CTg000jR0P0f0R1g00\]R2#F#2R3%22R2';'0f1R4/039101X501013,30%<2,:1g00^dR3#7%63%50%80%90R3g00YWg00Z6R5P5g00ZVR5P0g00XRR6,40g00\61402CEg00[6FD1=35P1f2R5g000JR3g00]BR7'31>15=137dA?064C@b1b2b31A62P1b09B12ECW4o"). Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yp;1p;2p;4p;7p;3g001ej10Tg002Jj1ATg00<Oj13Tg00<oj12Tg00P<j1@Tg00=mj1:Tg00>Kj14Tg00?Yj21Tg00Hmj45Tg00Vfj76Tg00AAj27Tg0000j28Tg00Acj29Tg005Yj3?Tg00BOj3>Tg00Bnj4;Tg009Mj2<Tg00PZj3=Tg000jR0f0R1g00\]#0#0#0#0#0#0#AR2g00^dR3#3%23%@0%:0%40R3g00YWg00Z6R4P4g00ZVR4P0g00XRR5,10g00\61102C5g00[6F61734P1f2R4g000JR3g00]BR6'81914=?36df19>05C;b1b2b31<52P1b03=W4o"). Qed.

(* [comment removed for export] *)
Lemma round_even_idiom : forall x, (0 <= x)%Z ->
  Z_to_bv 64 (Z.land (x + 1) 18446744073709551614) = Z_to_bv 64 (x + Z.land x 1).
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01zh12H0h23H10h33H15h43H20h52H5h62Hah77__sat25h84__x1h95__x10h:5__x11h;4__x2h<4__x3h=4__x4h>4__x5h?4__x6h@4__x7hA4__x8hB4__x9hC1HhD2H1hE3H11hF3H12hG3H13hH3H14hI3H16hJ3H17hK3H18hL3H19hM2H2hN3H21hO3H22hP3H23hQ2H3hR2H4hS2H6hT2H7hU2H8hV2H9hW2HxhX7__arithhY4__ffhZ7__sat24h[8__varmaph\5__with]1qh^2q0h_2q1h`2q2ha2q3hb1rhc2r0hd2r1he2r2hf2r3hg1xp%0p&0p;1p;2p;3p;4p;6p;7p;8g002Jj1CTg00mDj21Tg014>j16Tg001ej14Tg006Qj2KTg008Kj2;Tg002hj2wTg0059j20Tg014cj2[Tg00Elj1pTg00bIj27Tg015Dj2RTg003Ej2<Tg015kj2VTg009Mj2FTg003aj2GTg016Rj2STg0178j2QTg00;nj2lTg0000j2dTg00:bj2vTg00;Jj3tTg017^j12Tg018=j1sTg018[j2aTg019<j2gTg019ej2_Tg01:Nj2fTg01;:j2ZTg01;fk40ATg01<Gk30@Tg01<hk30?Tg00<Ok10<Tg01=Tj3oTg00<ok10;Tg00=Oj2]Tg00P<k10:Tg00=mk106Tg00>Kk105Tg00?Yj2bTg00@<k104Tg01>4j3UTg00J<k103Tg00JZk302Tg00?6j2jTg00@^k301Tg00AAk200Tg00Acj2~Tg005Yj3LTg00BOj3|Tg00Bnj4}Tg01>Wj2iTg01?4j1qTg00Dnj6\Tg01@Dj1{Tg01AVj1zTg01Bnj3yTg01DCk307Tg01Dlj3^Tg01EUk308Tg00nmk409Tg00Hmj4cTg00Vfj7nTg00Wnj7uTg00IXk60=Tg00oKk30>Tg00WJj8eTg00XRR0f0R1'Fp=`%61#6#6#6p>0C%61#6#6#6#6#6#6#6p=J%41#4p=mg000jR2f2R3f1R4'0;L1p=AAL241p=rAL210p=If3R51i34/115L2p=@1F031<41'Gp=91041,13p=D1<41,G3p=x1g21p=3B07241p=8A^241p==A^2419^23p=5B08241p=O%41#4#4#4p>0B%41#4#4#4#4#4#4#4p=NA^234/Z1p=:1Z41,Z3p=MP2P3P4P1H09p=H1j21p=?P2P4g00\6P1Ccp=WP4g00YWR6g00Z6R7P7g00ZVR8P1g00[6R9Fnp=>P2P4g00Y0P1Ccp=YP3P6P7P7P8P4P1Fup=XP3P6P7P7P8P2P4g00_PP1CcP9Fnp=BP4P6P7P7P8P1J0=p=kB0>241p=EP5P6P7P7P8P3P4P1Gep=Pf6R9P6P7P7P8f5R:f4R;P5P6P7P7P8P3P4P1GeGep=T11419L23p=h%`1R6g00\]R<#CR=,14R>%6<R?#6R@$0C#J#J#J#J#J#J#JRA#4#C'KS001K4=RB,14P2%6A#C,K>RA1K>=RC';%4<RD#CRE%4DRF#4RG#4#mRH#CRI'wRJ1K3=,13/0JRK5A1X02P210>JRL113=RM/K=,;1?AJKX02P210>ERN10MJRO/;1?AJKX02P2104E10ME,;ORO/0JRM1131/0J'rX021;LN/[J%IJRN#pRLPOPJ17OJPMC@[1ROJ1<0JRO115=RM/0J10ME';RM/0JRK?9KJ[1VMJ1<J0RM11;=RK/0J10KE';RP/0JRQ,<J1FQ0'G[1SPJ11:=RP/0J10PE';RP/7J#I\N1QPJ119=RP/0J10PE';RQ?AJQ\N17QJP2f7RQ/1=RR/0J10RE';/0JP2f8RR?DRE/[Jf9RS?DSERTPJ17TJ10TJC@\L1RTJf:RT?DTERU/0JRV?9VJ\O1VUJf;RU?DUERV/0JRW,<J1FW0'G\M1SVJf<RV?DVERW/7J#I\N1QWJf=RW?DWERX?AJX\N17XJP2f>RX?DXE/0JP2f?RY/[E%IERZ#pR[f@R\PE17\E10\EC@[1R\E1<0ER]fAR^/0ER_?9_E[1V^E1<E0R_fBR`/0ERa,<E1Fa0'G[1S`EfCR`/7E#I\Z1Q`EfDR`?AE`\Z17`EP2fER`/0EP2fFRa/1=/[JfGRb/1=RcPJ17cJ10cJC@\L1RcJfHRc/1=RL/0JRd?9dJ\O1VLJfI/1=RL/0JRd,<J1Fd0'G\M1SLJfJ/1=RL/7J#I\N1QLJfK/1=RL?AJL\N17LJP2fL/1=/0JP2fMRL/1=/[EfNRM/1=RdPE17dE10dEC@\[1RdEfORd/1=R[/0ERe?9eE\]1V[EfPR[/1=Re/0ERf,<E1Ff0'G\_1SeEfQ/1=Re/7E#I\Z1QeEfR/1=Re?AEe\Z17eEP2fS/1=/0EP2P:g00^>Re1l0E'dP]eR_O1Ax61EPW1l0J,dePOeReO1A9RRJR6P`P_O1A9\\EPLPeO1A9ccJfUR`PeO1A9[[J1vEI%`IPO[RO\]%`ER]g00]bR[AtEI4UW6%`J\[^6]P4P_O1POg00^dROg01F>R_#2R]#2R[#2RI#2Re#2Rf#2Rg#2Rh#2Ri#2Rj#2Rk#2#2Rl#2Rm#2Rn#2Ro#3Rp%s<,a2Rq%3mRm'8Rr%3jRj%3hRh'=Rs'=1g2_R_18qpRt%3lRl%3gRg,8q%3IRI%3[R['=55j35%3]R]18ql%3kRk;5j%2oRo#2Ru#2#2Rv#2Rw#3Rx%3vRv%3nRn;5r1_2ERy/O]1Oy_Ry%3uRu,8qRz%3i,8q75k75x%2wRw#2Ri#2R{#3R|%3iRi%3oRo,8q,=u35%3f%4H#m$0B#N#N#N#N#N#NRf#4Ru#C,_2/O_?5Ikg01F]R}'f,Z_5:_5M_3:3:5M_5:_3M3:18qkR~/=s18qj,=k95op%3e,8q=5hI95r~%3wRw18qvR~1=pm351=ot95iw%6DRtP2%CfRf,a2P<1a2=H0A60@2A5ix~A5xvz1_2fRf/O_1Of[1=Ig35/f}5:y5:|%2{#2R{#3,8qA5inm%2{R{#2#3%3{18qx75w%4u#C,_2/O[/=l95]_/f}3:3:40?,Z_9:_I5M_5M_9:]_5:o5M_5:l&0<O5oO3o&0;O1]2R&0:2RO7H;1]2T?H9O7H31]2S?H:O1]2U?HQO7H57H4&062&052R51b20RO%?tRl'W,>51b2ER_,Yl,>55X5&047R7P5P5AB5_O,k5RoP7%??R]1b2='ER=%6t#?9U2_/El5B5CPP7P5%?FRI,WO,>5&03H:022_RH,YI,>55X5P7P5P5AB5HO,k5R}P7%4t#?9U2H/EI9B5=CPP7P5%?@R@,WO,>51Y@_,>55X5P7P5P5PoP7%6F#?9U2_/E@9B5]CPP7P5%?DRD,WO,>51YDH,>55X5P7P5P5P}P71E]@%?G9U2H/ED5B5CPP7P51j2<R<,WO,>51Y<H,>55X5P7P5P5P}P7B012Il%4?#?9U2H/E<5B5CPP7AB5<DFTFTFTFTFT20058P1P3g000JR5g00]BR8'd1~13=L58dA|204C}bYb[b\X82X;2X<2X=2X>2X?2X@2XA2XB2X92X:2A9;;Eg00`7R0\ZRZPKPEPVP9C@[A9::JP0\NRNPPPJPWPQC@[A9TTEPRPEPXPVC@\ZA9QQJ11TX1iJYRJ;hS\N1;WX?hJT\N1rTU[\6[[[[[[[[^82^;2^<2^=2^>2^?2^@2^A2^B2^92^:2P1PTP^PcPdPbfVPSP\f]PMP`PRPYPQPaP9PLP:fTP;f[OEbXb7bZb7b1b5b2b3b4bfbabPbObNb4bLbeb`bKbJbIb3bHbdb_bGbFbEb2bVbcb^bUbTbSb5bRbbb]bQbMbDb1bCPB%q4E\PC%q>E\PA%{>E\Q00%z>E\3yWWXg2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac bool_atom_cases :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec0 a b)
  end.

(* [comment removed for export] *)
Ltac weq :=
  first [ reflexivity
        | f_equal; zeq
        | rewrite round_even_idiom by zrange_nonneg; weq_arith
        | weq_arith ]
with weq_arith :=
  apply Z_to_bv_eqm; rewrite ?land_even_mask, ?land_1; zb_masks; cbv delta [Z.b2z]; cbn [negb];
  bool_atom_cases; cbn [negb]; pose_word_ranges; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac ms_eq :=
  first [ reflexivity
        | lazymatch goal with
          | |- Z_to_bv 64 _ = Z_to_bv 64 _ => weq
          | |- _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
          | |- Z_to_bv 64 (bv_unsigned _) = _ => apply Z_to_bv_bv_unsigned
          | |- context [mkR] => unfold mkR; ms_eq
          | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; ms_eq
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; ms_eq
          | |- Some _ = Some _ => f_equal; ms_eq
          end ].

(* [comment removed for export] *)
Ltac sf_finish :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P end; hnf;
  rewrite ?lo64_mk128, ?hi64_mk128 by zrange;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [ ms_eq | repeat match goal with |- _ /\ _ => split end; try assumption ].

(* [comment removed for export] *)
Lemma signed_of_Z : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h02Hah16__sat1h24__x1h31zh42Hzh57__arithh64__ffh76__sat0h88__varmaph95__witp;1p;2p;3p;4p;7p;8p;6g001ej10Tg002Jj15Tg014>j13Tg002hj2?Tg01GIj1;Tg009Mj21Tg003Ej22Tg003aj24Tg00J<j16Tg01Gfj2@Tg005Yj39Tg00:bj2=Tg00;Jj3<Tg00;nj2WTg0000j2:Tg00<Oj1VTg00<oj1UTg00=Oj2TTg00=mj1KTg00>Kj1FTg00?Yj2ETg00JZj3DTg01HMj2CTg00?6j2BTg00Hmj48Tg00Wnj7ATg00@<j1GTg00WJj8HTg00AAj2ITg00Acj2JTg00BOj3>Tg00Bnj4LTg01I0j1MTg01I^j3NTg00i=j2OTg01JKj2PTg01K3j2QTg00Dnj6RTg00Vfj7STf1R0g00YWR1g00Z6R2P2g00ZVR3f0R4g00[6FSp=7g000jR5g00\]R6#0R7#5R8%36#3#3#3#3R9#5R:'?R;#;R</14124;'4R=P5%07#0#0#0#0#6R7/@0f2R>9954X351=8:g00XRR?/28R@11?:12?;[RA[11?8RBg00]bRCA<8:0UW011?;\C^0BP0g00^>1W?8':P@eO1PAg00^dRA#V%UA1T50%K5%F5RAP1P2P2P3PAP1P2P2P3P51E58%695D5R9,C5g00\61B56R6C8,7AP5P6g00Y0P9C8,7AFAR9%G2P9GH1IA3P4P>g000JRAg00]BR3':1J4>=9A3dA>5?0CLb6b8b9X2511<0120;'4\=^25P4f5f4O2b5b1b7b1%M7R4#;/101204'4e9N701O70,P71Q70ERW4W3o"). Qed.
Ltac signed_lits_in H :=
  repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_of_Z z) in H by lia
  end.

(* [comment removed for export] *)
Lemma mod64_land63 : forall y, (y mod 64 = Z.land y 63)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yh51zp;1p;2p;3p;4p;7p;6g001ej10Tg002Jj11Tg014>j1=Tg002hj26Tg0059j25Tg005Yj32Tg0000j23Tg0063j1<Tg006Qj2;Tg00<Oj1:Tg00<oj17Tg00P<j18Tg00=mj19Tg00>Kj1GTg00?Yj24Tg00Hmj4FTg00Vfj7ETg00AAj2DTg00Acj2?Tg00BOj3>Tg00Bnj4@Tg009Mj2ATg00PZj3BTg00Dnj6CTg000jR0P0f0R1g00\]R2#0R3#1%=2#0#1R2'6'5R4f1R5%03#0#0#0#0#1'5=201X501304%<2,;1g00^dR4#:%74%80%90%G0R4g00YWg00Z6R3P3g00ZVR3P0g00XRR6,40g00\61402CFg00[6FE1D43P1f2R3g000JR4g00]BR7'31?13=247dA>065C@b1b2b31A62P1b09B12ECW4o"). Qed.
Lemma land63_idem : forall y, Z.land (Z.land y 63) 63 = Z.land y 63.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01yh11zp;1p;2p;3p;6g014>j11Tg002Jj16Tg006Qj20Tg005Yj32Tg0000j25Tg010Pj34Tg00Q=j63Tg000jR0P0f0R1g00\]#1#1#1#1#1#6R2/02'0f1/029201X101012R3,501032A4122E3W0o"). Qed.

Ltac zs_idioms_sf :=
  match goal with
  | |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
  | |- context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem
  end.
Ltac zs_idioms_sf_in H :=
  match type of H with
  | context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
  | context [(?y mod 64)%Z] => rewrite (mod64_land63 y), ?land63_idem in H
  end.
Ltac zs_idioms ::= zs_idioms_sf.
Ltac zs_idioms_in H ::= zs_idioms_sf_in H.
