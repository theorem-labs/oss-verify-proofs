(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export Walk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Export SoftFloat.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SFModel () := "K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z3b2zK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool;andb_true_rK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=testbit_neg_rC56Stdlib6ZArith6BinInt1Z=ones_spec_lowC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z6bits_0K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z>ones_spec_highC56Stdlib6ZArith6BinInt1Z;shiftl_specC56Stdlib6ZArith6BinInt1Z8lor_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Common9SoftFloat6wrap64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat:wrap64_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat5mk128C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat4lo64C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Common7SFModel;lo64_mk128'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z:shiftl_0_rC56Stdlib6ZArith6BinInt1Z8sub_diagC56Stdlib6ZArith6BinInt1Z?shiftr_shiftl_lC56Stdlib6ZArith6BinInt1Z:shiftr_lorC59OSSVerify5KrLib6Common9SoftFloat4hi64C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic3and01c59OSSVerify5KrLib6Common7SFModel:hi64_mk128C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common7SFModel:lo64_mk128C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z8lxor_lorK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z8land_0_rC56Stdlib6ZArith6BinInt1Z:land_assocC56Stdlib6ZArith6BinInt1Z9land_diagC56Stdlib6ZArith6BinInt1Z9land_commc59OSSVerify5KrLib6Common7SFModel@lor_disjoint_addC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@land_lor_distr_rK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulc59OSSVerify5KrLib6Common7SFModel6land_1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common7SFModel8land_W64C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common7SFModel>land_even_maskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions8bv_swrapK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions?bv_half_modulusC45stdpp9bitvector;definitions>bv_swrap_smallC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signed".
Import ListNotations.
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
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with51bh64__p1h73Hloh81Hh92Hah:6__sat1h;1ah<2loh=2H0h>3Hhih?2Hih@6__sat0hA1ei001ehB2hihC1ihD1ni011nhE1ohF1si021shG1zp;1p;2p;3p;4p;6p;7p;5p;8g001ej1:Tg002Jj1LTg002hj2BTg003Ej21Tg003aR0j28Tg004<j2JTg004\j2KTg0059j2WTg005Yj36Tg0063j1QTg006Qj2ITg006oj20Tg007Pj24Tg007nj27Tg008Kj2@Tg008hj2fTg009Mj2;Tg009iR1j2`Tg00:Cj1^Tg00:bj1]Tg00;Bj1\Tg00;bj2YTg00<@j1XTg00<^j1VTg00=Ij2UTg00=lj2CTg00>Oj1TTg00?1j3PTg00?Tj2OTg0000j2HTg00@6j2NTg00@bj3RTg00AAj4MTg00B3j3STg00BZj3~Tg00CAj6<j7pTg00C_j2}Tg00D?j1FTg00DXR2j2|Tg00E8j1{Tg00EXj6oTg00F<j1?Tg00FZj3eTg00G@j2cTg00Ghj3bTg00HLj2aTg00Hmj4DTg00IXj6dTg00J<j1_Tg00JZj3gTg00K=j5hTg00Kbj4iTg00LKj4jTg00Lgj1kTg00MGj3lTg00Moj4mTg00NTj3nTg00O6j3[Tg00OYj3ZTg00P<j1qTg00PZj3rTg00Q=j6sTg00QYj1tTg00RUj1uTg00SUj2vTg00TPj1wTg00UJj7xTg00Unj8yTg00VRj7zTg00W6R3f0R4';p=9g000JR5f1R6;64p=3g000jR7P6g00WTP4CDp==P6g00X;R8g00XZR9P9g00Y:R:P4g00YZFxp=5f3R;P8P9P9P:f2R<P6P4Gyp=2P5g00Z:R=P;P<P6P4E<p=EP7P6g00ZZP4CDp=GP<P8P9P9P:P6P4Fzp=>A6743p=A%94R>g00[AR?#:R@#LRA%:@#:#:#:#:R@#LRB'BRC,14RD'8RE%9<RFP71J;B/K<RG/WCRHA674;XG7RIP7%QBRJ,IGRKPIP5f5RI/JBRLf4RM'KRN/06RO10J6'410I<RP,34X55P510L6RQ10M6'710J<RR,44/3PX55P51@6BRS,0I174P/4R/3PX551f6B116B1;B6RP'`P111<BR11;B<f7RR1@;B'0f6RT/0;RU'710J;'4/3UP411;BP5g00[fRUf9RV1@IB'0f8RW/0IRX'7/44/3XX55RY174X/4U/3XX5510RMRZ#^17=Z/4U/3Ze1@MBR[,0WR\g00\FR]#]R^%\]R]1Y76R_%X7R`%V7Ra1U7?R?1C7BRb'=,5aRc%T9RdAP7?b1C73Re'=,5aC21Oa:RfP4P<1H5U1N4<=65UdAR736CMRUb2b3b4X07114BRg11S3[^07P4PIP6O2RSb19SW[CE10JMR[P^P]P_P`PaPcPdPa1Ge?,5aRhPdA>ahcC2C2PfPUb2b3b4X07%96Rc18F1[\g^07P4PIP6PMO3b19~BME<W8P4O11;B;PY134XX55P5PZP=1}R3%ARRX%FX'|P2%AWR2%F210VT=65=P4%AVRTP7P3106V=65=^7EX<71;33113CRE'8%{WW7f:R5P4PVFpWAP4O1%FTP5PRp-0RTP^P]P_P`PaPaP8P9P9P:P;EoRV9>ahR2PdPhC2PfPUb2b3b4X07W618>6Pc[^07^6TP4f;RX/1CPXP5O3b1%?5PBPR1136RRP01BA6,1<%?;/1<[R0%?</161BA<,1;R5[%?M/1;\5Ae<64P6n2001000000120000000UX57X;7P0\R^57^;7P4PXPB1cAB113ARR%9BR0PE[RE[%9AR5g00]2RYAbAB6UW9%9C\Y^95P6g00]N1a3A'HPReO1PEP^P]P_P`PaPaP8P9P9P:P7P?g00^4PeCD,5aEdPdPaP2Pd1=e?,5aC2C2PfPUb2b3b4X07X6T%A4g00^[[18c<113<[[^07^6TP4f?R3/1CP3PIf>O4b1b:b@b:P^P]P_P`Pa1C7A%_@5g7,=?,5aR@9>aVPdP@C2PfPUb2b3b4X07X6T186D116C[^07^6TP4f<RT#9PTPXO3b1O4b=P^P]P_P`Pa1Gb?,5aR?PdP?C2PfPUb2b3b4X071;B4RXPP[^07P4PWPMO2b1DhCiWDP4O1n200110200021010011101bFCj17\ZR\/4=%k\CEP[P^P]P_P`PaP?Pd1Geb,5aRe=>a?C2PfPUb2b3b4X07180P\X^07PSb19lBMCEW8P4O1n200100000021100011000bEPQPIPBP6P^P]P_P`PaPhPdPhC2PfPUb2b3b4X07Pc\>^07P4P<P6O2b1CmE<POAnLM6E<1INJ/06A[NJ6E<X?>XC79ZK<PHP^P]%q7P`PePfPUb2b3b4P0P4b19rGBEs%tG%uGE<1v;<#w=67<eW>W7X<7XB7o"). Qed.

Lemma lo64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> lo64 (mk128 hi lo) = lo.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h04__x1h17__arithh24__ffh34__p1h48__varmaph55__with62hih72lop;2p;1p;4p;3p;6p;7p;8g009Mj23Tg001ej10Tg002Jj15Tg002hj2<Tg003Ej21Tg003aj22Tg00:bj1CTg00;Bj1@Tg00;bj2>Tg00<@j1=Tg00<^j1;Tg00=lj24Tg00=Ij2:Tg00Hmj49Tg00J<j1NTg00JZj3MTg00>Oj1LTg00?Tj2BTg0000j2ATg00@6j2?Tg005Yj3DTg00@bj3ETg00AAj4FTg00EXj6GTg00_8j4HTg00UJj7ITg00VRj7JTg00Unj8KTf1R0g00X;R1g00XZR2P2g00Y:R3f0R4g00YZFIp=8f2R5P1P2P2P3P0P4FJp=7f3R6P1P2P2P3P5P0P4GKp=6g000jR7g00W6R8/34R9g00[AR:#0R;#5R<%0;#0#0#0#0R;#5'<R=,14'2R>1385115='2P6P5g00\FR?#CR@%@?R?1>70RA%=7RB%;7RCP71478g00ZZ1:7:R:C9,8CRDP7P:g00WT147<%N;5M7C9,8C57CR;%L2R<P;C61BC3R;P4P5g000JR:g00[fRE'A1?45=D:EdAE780CFREb2b4b5X071380R8110='2\>^07P4P6P5O2b1p-0R5P@P?PAPBPCPCP1P2P2P3P6EG97CDP<PDC6P;PEb2b4b5X07W31290P8[^07^35P4f4R4/1=P4P0O3b1CHUUX77W6o"). Qed.

Lemma hi64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (mk128 hi lo) = hi.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h63Hhih73Hloh82hih92lop;2p;1p;4p;3p;7p;8p;6g009Mj25Tg001ej12Tg002Jj1>Tg002hj2CTg003Ej2=Tg003aj2;Tg004<j27Tg004\j21Tg00`7j26Tg0059j24Tg008Kj2ATg00`Wj2@Tg00:bj1`Tg00;Bj1VTg00;bj2UTg00<@j1RTg00<^j1QTg00=lj28Tg00=Ij2LTg00Hmj4:Tg00J<j1JTg00JZj3ITg00VRj7HTg00>Oj1ETg00Unj8FTg00?Tj2GTg0000j2DTg00@6j2KTg005Yj3?Tg00@bj3BTg00AAj4MTg00a4j3NTg00aWj1OTg00b8j3PTg00CAj6<Tg00P<j1STg00b[j3TTg00cDj1_Tg00chj1^Tg00dJj4]Tg00e3j3WTg00QYj1XTg00RUj1YTg00SUj2ZTg00eWj1[Tg00UJj7\Tg000jR0f1R1f0R23?p=3P1g00X;R3g00XZR4P4g00Y:R5P2g00YZF\p=9P0f4R6f3R7f2R8P1P2E<p=0g00W6R9/52g00[AR:#2R;#>R<%2;#2#2#2#2R;#>R='CR>,=2';R?15981=8>';177=R@/18/6=RA/4>1326X0016@=RB168=RC'1142>/36X00RD1A==RE,77167=RF,12/4>/36X00RGP0P91762/1F/4>/36X00P7PG1@8>RG1162/4>/36X00RFP0P9PFP7PDg00\FRD#`RF%VDRD1U01%R0RH%Q0RIP3P4P4P5PIP3P4P4P5P01809R3g00ZZRJ1L0:R:C:,9IP0P:g00WT180<%J;5I0C:,9IFHR;%E4P;GF1GI5R5P2P8g000JR;g00[fR4'D1K28=?;4dAB091CMR4b2b3b4X50R;15911=1>';\?^50R?P2P6P1O2b19N7>1179%O7D0PGP;P?P2P7P8O2b19P8>E<PCPFPD%S0PHP0P3PJ180=C:,9IP5P4b2b3b4159=P2b1R29T8=D01779%_7D0PE%^=E<PBP7P=P=P2C]D0PAAW@8=D0%XA%YAD01Z78#[/37eW6W7X90X80o"). Qed.

(* [comment removed for export] *)
Lemma mk128_regs : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z ->
  Z_to_bv 64 (lo64 (mk128 hi lo)) = Z_to_bv 64 lo /\ Z_to_bv 64 (hi64 (mk128 hi lo)) = Z_to_bv 64 hi.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__x1h21zh34__ffh48__varmaph55__with62hih72lop;2p;1p;3p;4p;7p;8p;6g009Mj25Tg001ej10Tg002Jj17Tg002hj2@Tg003Ej26Tg003aj23Tg00J<j1ITg00fQj1DTg00g4j22Tg005Yj31Tg00SUj28Tg00eWj1=Tg0000j24Tg00gZj4STg00:bj1RTg00;Bj1QTg00;bj2OTg00<@j1NTg00<^j1LTg00=lj2:Tg00=Ij2HTg00Hmj49Tg00JZj3CTg00VRj7ETg00>Oj1BTg00Unj8FTg00?Tj2GTg00@6j2ATg00@bj3JTg00AAj4KTg00h5j4?Tg00CAj6;Tg00TPj1MTg00i3j4>Tg00UJj7PTf1R0g00X;R1g00XZR2P2g00Y:R3f0R4g00YZFPp=<g000jR5g00W6R6/54g00[AR7#0R8#7R9%08#0#0#0#0R8#7'@R:,64'3R;f2R<,5616<:'3P5P<%I8R8#DR=1284R>f3R?,28R@31f4RA/8?#=,28128ARB51='3X25P5P?A1=@@RCA1=>B'3X25128<RB=1=BPC14=B14=@CS18?<R@#=P?P<g00\FR=#R%Q=1O50%N5%L5R=P1P2P2P3P=P1P2P2P3P51:56g00ZZ1H57R7C9,<=P5P7g00WT1:59=C58C9,<=FER8%B2P8GF1G=3P4P<g000JR=g00[fR3'41A4<=1=3dAJ560CKb3b4b5X15R31560160:'3\;^15R;P4P?P<O2b0R:P3P;P4PAP0O2b0R0C?E;%M@P?P<P:P0C>E;UUX75W6o"). Qed.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0%Z -> Z.lor a b = (a + b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01Hh11ah21bh31zp;2p;3p;4p;6g006Qj28Tg005Yj31Tg00j1j22Tg00jOj20Tg00jlj37Tg00LKj46Tg004\j23Tg00kVj34Tg00Q=j65Tg000jR0f1R1f0R2'8g00W6510P0f2R3/21R4f3/039102X30P01031P4A7312C61331A4312E5W0X20W1o"). Qed.

(* [comment removed for export] *)
Lemma land_even_mask : forall y, Z.land y 18446744073709551614 = (Z.land y 18446744073709551615 - Z.land y 1)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01zh14__x1h24__x2h37__arithh44__ffh58__varmaph65__with71yp;1p;2p;3p;4p;7p;6g001ej17Tg002Jj1=Tg006Qj20Tg004\j2:Tg008Kj29Tg005Yj34Tg00jOj28Tg00:bj1ATg00;Bj1?Tg00;bj2>Tg00P<j1STg00l8j4RTg00<@j1PTg00<^j1MTg00=Ij2;Tg00lVj3LTg00?1j3JTg00Hmj4ITg00UJj7HTg00?Tj2ETg0000j2DTg00@6j2FTg00@bj3CTg00AAj4GTg00m9j1BTg00m[j36Tg00Q=j6KTg00n?j1@Tg00nbj2<Tg00oEj3NTg010Ij3OTg0113j11Tg00CAj6QTf0R0#1#1p=U%10#1#1#1p=T%10#1#1#1#1#1#1#1p=2g000jR1g00W6R2740p=5P1f4f3f2R3f1R4P0EQp=3g00[AR5#U#T#2#2#2#2#2#2#2#7#=R6,00R7%=5R8,00R9':R:1046R;1048R<,90541X01R=1879P=g00\FR=#A%?=P11>13P4%S1CR%P1%M1R=g00X;g00XZR>P>g00Y:R>P11;15R?g00^4%75,;1R59L1?=J15CIg00YZFH1E=>P0P3g000JR>g00[fR='D1F03=4>=dAC124CGb4b5b6X11X211804/949410^11^21P0P<P;O2b3P:1097R:%50X01R;1090R</06P;1009R4%57X01R21000R=/08P2P01096R2#5X01P11086,00P;%B0P2A6086EKP=%@0D3P4A6008D3P<1<90D3P:A6906D310791<79D39N79D31:68,00AO068D3X71o"). Qed.

Lemma land_1 : forall y, Z.land y 1 = (y mod 2)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yh51zp;1p;2p;3p;4p;7p;6g001ej1FTg002Jj12Tg002hj2;Tg0059j20Tg005Yj31Tg0000j23Tg0063j1<Tg006Qj2:Tg00:bj17Tg00;Bj16Tg00P<j15Tg00<@j18Tg00<^j19Tg00=lj24Tg00Hmj4ETg00UJj7DTg00?Tj2=Tg00@6j2>Tg00@bj3?Tg00AAj4@Tg009Mj2ATg00PZj3BTg00CAj6CTg000jR0P0f0R1g00[AR2#F#2R3%22R2';'0f1R4/039101X501013,30%<2,:1g00\FR3#7%63%50%80%90R3g00X;g00XZR5P5g00Y:R5P0g00W6R6,40g00ZZ1402CEg00YZFD1=35P1f2R5g000JR3g00[fR7'31>15=137dA?064C@b1b2b31A62P1b09B12ECW4o"). Qed.
Lemma land_W64 : forall y, Z.land y 18446744073709551615 = (y mod 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yp;1p;2p;4p;7p;3g001ej10Tg002Jj1ATg00:bj13Tg00;Bj12Tg00P<j1@Tg00<@j1:Tg00<^j14Tg00=lj21Tg00Hmj45Tg00UJj76Tg00?Tj27Tg0000j28Tg00@6j29Tg005Yj3?Tg00@bj3>Tg00AAj4;Tg009Mj2<Tg00PZj3=Tg000jR0f0R1g00[A#0#0#0#0#0#0#AR2g00\FR3#3%23%@0%:0%40R3g00X;g00XZR4P4g00Y:R4P0g00W6R5,10g00ZZ1102C5g00YZF61734P1f2R4g000JR3g00[fR6'81914=?36df19>05C;b1b2b31<52P1b03=W4o"). Qed.

(* [comment removed for export] *)
Lemma round_even_idiom : forall x, (0 <= x)%Z ->
  Z_to_bv 64 (Z.land (x + 1) 18446744073709551614) = Z_to_bv 64 (x + Z.land x 1).
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01zh12H0h23H10h33H15h43H20h52H5h62Hah77__sat25h84__x1h95__x10h:5__x11h;4__x2h<4__x3h=4__x4h>4__x5h?4__x6h@4__x7hA4__x8hB4__x9hC1HhD2H1hE3H11hF3H12hG3H13hH3H14hI3H16hJ3H17hK3H18hL3H19hM2H2hN3H21hO3H22hP3H23hQ2H3hR2H4hS2H6hT2H7hU2H8hV2H9hW2HxhX7__arithhY4__ffhZ7__sat24h[8__varmaph\5__with]1qh^2q0h_2q1h`2q2ha2q3hb1rhc2r0hd2r1he2r2hf2r3hg1xp%0p&0p;1p;2p;3p;4p;6p;7p;8g002Jj1CTg00jOj21Tg0113j16Tg001ej14Tg006Qj2KTg008Kj2;Tg002hj2wTg0059j20Tg011Xj2[Tg00D?j1pTg00`Wj27Tg0129j2RTg003Ej2<Tg012`j2VTg009Mj2FTg003aj2GTg013Gj2STg013mj2QTg00HLj2lTg0000j2dTg00G@j2vTg00Ghj3tTg014Sj12Tg0152j1sTg015Pj2aTg0161j2gTg016Zj2_Tg017Cj2fTg017oj2ZTg018[k40ATg019<k30@Tg019]k30?Tg00:bk10<Tg01:Ij3oTg00;Bk10;Tg00;bj2]Tg00P<k10:Tg00<@k106Tg00<^k105Tg00=lj2bTg00>Ok104Tg01:ij3UTg00J<k103Tg00JZk302Tg00=Ij2jTg00?1k301Tg00?Tk200Tg00@6j2~Tg005Yj3LTg00@bj3|Tg00AAj4}Tg01;Lj2iTg01;ij1qTg00CAj6\Tg01<cj1{Tg01=_j1zTg01>aj3yTg01?]k307Tg01@Fj3^Tg01@ok308Tg00l8k409Tg00Hmj4cTg00UJj7nTg00VRj7uTg00IXk60=Tg00lVk30>Tg00Unj8eTg00W6R0f0R1'Fp=`%61#6#6#6p>0C%61#6#6#6#6#6#6#6p=J%41#4p=mg000jR2f2R3f1R4'0;L1p=AAL241p=rAL210p=If3R51i34/115L2p=@1F031<41'Gp=91041,13p=D1<41,G3p=x1g21p=3B07241p=8A^241p==A^2419^23p=5B08241p=O%41#4#4#4p>0B%41#4#4#4#4#4#4#4p=NA^234/Z1p=:1Z41,Z3p=MP2P3P4P1H09p=H1j21p=?P2P4g00ZZP1Ccp=WP4g00X;R6g00XZR7P7g00Y:R8P1g00YZR9Fnp=>P2P4g00WTP1Ccp=YP3P6P7P7P8P4P1Fup=XP3P6P7P7P8P2P4g00^4P1CcP9Fnp=BP4P6P7P7P8P1J0=p=kB0>241p=EP5P6P7P7P8P3P4P1Gep=Pf6R9P6P7P7P8f5R:f4R;P5P6P7P7P8P3P4P1GeGep=T11419L23p=h%`1R6g00[AR<#CR=,14R>%6<R?#6R@$0C#J#J#J#J#J#J#JRA#4#C'KS001K4=RB,14P2%6A#C,K>RA1K>=RC';%4<RD#CRE%4DRF#4RG#4#mRH#CRI'wRJ1K3=,13/0JRK5A1X02P210>JRL113=RM/K=,;1?AJKX02P210>ERN10MJRO/;1?AJKX02P2104E10ME,;ORO/0JRM1131/0J'rX021;LN/[J%IJRN#pRLPOPJ17OJPMC@[1ROJ1<0JRO115=RM/0J10ME';RM/0JRK?9KJ[1VMJ1<J0RM11;=RK/0J10KE';RP/0JRQ,<J1FQ0'G[1SPJ11:=RP/0J10PE';RP/7J#I\N1QPJ119=RP/0J10PE';RQ?AJQ\N17QJP2f7RQ/1=RR/0J10RE';/0JP2f8RR?DRE/[Jf9RS?DSERTPJ17TJ10TJC@\L1RTJf:RT?DTERU/0JRV?9VJ\O1VUJf;RU?DUERV/0JRW,<J1FW0'G\M1SVJf<RV?DVERW/7J#I\N1QWJf=RW?DWERX?AJX\N17XJP2f>RX?DXE/0JP2f?RY/[E%IERZ#pR[f@R\PE17\E10\EC@[1R\E1<0ER]fAR^/0ER_?9_E[1V^E1<E0R_fBR`/0ERa,<E1Fa0'G[1S`EfCR`/7E#I\Z1Q`EfDR`?AE`\Z17`EP2fER`/0EP2fFRa/1=/[JfGRb/1=RcPJ17cJ10cJC@\L1RcJfHRc/1=RL/0JRd?9dJ\O1VLJfI/1=RL/0JRd,<J1Fd0'G\M1SLJfJ/1=RL/7J#I\N1QLJfK/1=RL?AJL\N17LJP2fL/1=/0JP2fMRL/1=/[EfNRM/1=RdPE17dE10dEC@\[1RdEfORd/1=R[/0ERe?9eE\]1V[EfPR[/1=Re/0ERf,<E1Ff0'G\_1SeEfQ/1=Re/7E#I\Z1QeEfR/1=Re?AEe\Z17eEP2fS/1=/0EP2P:g00]NRe1l0E'dP]eR_O1Ax61EPW1l0J,dePOeReO1A9RRJR6P`P_O1A9\\EPLPeO1A9ccJfUR`PeO1A9[[J1vEI%`IPO[RO\]%`ER]g00]2R[AtEI4UW6%`J\[^6]P4P_O1POg00\FROg01AXR_#2R]#2R[#2RI#2Re#2Rf#2Rg#2Rh#2Ri#2Rj#2Rk#2#2Rl#2Rm#2Rn#2Ro#3Rp%s<,a2Rq%3mRm'8Rr%3jRj%3hRh'=Rs'=1g2_R_18qpRt%3lRl%3gRg,8q%3IRI%3[R['=55j35%3]R]18ql%3kRk;5j%2oRo#2Ru#2#2Rv#2Rw#3Rx%3vRv%3nRn;5r1_2ERy/O]1Oy_Ry%3uRu,8qRz%3i,8q75k75x%2wRw#2Ri#2R{#3R|%3iRi%3oRo,8q,=u35%3f%4H#m$0B#N#N#N#N#N#NRf#4Ru#C,_2/O_?5Ikg01B7R}'f,Z_5:_5M_3:3:5M_5:_3M3:18qkR~/=s18qj,=k95op%3e,8q=5hI95r~%3wRw18qvR~1=pm351=ot95iw%6DRtP2%CfRf,a2P<1a2=H0A60@2A5ix~A5xvz1_2fRf/O_1Of[1=Ig35/f}5:y5:|%2{#2R{#3,8qA5inm%2{R{#2#3%3{18qx75w%4u#C,_2/O[/=l95]_/f}3:3:40?,Z_9:_I5M_5M_9:]_5:o5M_5:l&0<O5oO3o&0;O1]2R&0:2RO7H;1]2T?H9O7H31]2S?H:O1]2U?HQO7H57H4&062&052R51b20RO%?tRl'W,>51b2ER_,Yl,>55X5&047R7P5P5AB5_O,k5RoP7%??R]1b2='ER=%6t#?9U2_/El5B5CPP7P5%?FRI,WO,>5&03H:022_RH,YI,>55X5P7P5P5AB5HO,k5R}P7%4t#?9U2H/EI9B5=CPP7P5%?@R@,WO,>51Y@_,>55X5P7P5P5PoP7%6F#?9U2_/E@9B5]CPP7P5%?DRD,WO,>51YDH,>55X5P7P5P5P}P71E]@%?G9U2H/ED5B5CPP7P51j2<R<,WO,>51Y<H,>55X5P7P5P5P}P7B012Il%4?#?9U2H/E<5B5CPP7AB5<DFTFTFTFTFT20058P1P3g000JR5g00[fR8'd1~13=L58dA|204C}bYb[b\X82X;2X<2X=2X>2X?2X@2XA2XB2X92X:2A9;;Eg00^[R0\ZRZPKPEPVP9C@[A9::JP0\NRNPPPJPWPQC@[A9TTEPRPEPXPVC@\ZA9QQJ11TX1iJYRJ;hS\N1;WX?hJT\N1rTU[\6[[[[[[[[^82^;2^<2^=2^>2^?2^@2^A2^B2^92^:2P1PTP^PcPdPbfVPSP\f]PMP`PRPYPQPaP9PLP:fTP;f[OEbXb7bZb7b1b5b2b3b4bfbabPbObNb4bLbeb`bKbJbIb3bHbdb_bGbFbEb2bVbcb^bUbTbSb5bRbbb]bQbMbDb1bCPB%q4E\PC%q>E\PA%{>E\Q00%z>E\3yWWXg2o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h04__x1h11zh22Hzh37__arithh44__ffh58__varmaph65__witp;1p;2p;3p;4p;7p;8p;6g001ej10Tg002Jj15Tg0113j11Tg002hj2>Tg01Bcj1:Tg009Mj23Tg003Ej22Tg003aj24Tg00J<j17Tg01C@j2?Tg005Yj39Tg00:bj1<Tg00;Bj1;Tg00;bj2TTg00<@j1STg00<^j1RTg00=lj2LTg00JZj3KTg01Cgj2ETg00=Ij2CTg00Hmj46Tg00VRj7BTg00>Oj1ATg00Unj8DTg00?Tj2@Tg0000j2FTg00@6j2GTg00@bj3HTg00AAj4ITg01DJj1JTg01E8j3=Tg00g4j2MTg01Eej2NTg01FMj2OTg00CAj6PTg00UJj7QTf1R0g00X;R1g00XZR2P2g00Y:R3f0R4g00YZFQp=8g000jR5g00[AR6#0R7#5R8%16#1#1#1#1R9#5'>R:#:R;/34124:'4R<P5%07#0#0#0#0#7R7/?0f2R=9954X15g00\FR>#<%;>1T50%S5%R5R>P1P2P2P3P>P1P2P2P3P51L58%795K5R9,E5g00ZZ1C56R6C6,8>P5P6g00WTP9C6,8>FBR9%A2P9GD1@>3P4P=g000JR>g00[fR3'F1G4==9>3dg00W6=H50CIb4b5b6X0513;0120:'4\<^05P4P=P0O2b3%J7R=#:/30120='4e9=701M70,N71O70EPW2W1o"). Qed.
Ltac signed_lits_in H :=
  repeat match type of H with
  | context [bv_signed (Z_to_bv 64 ?z)] => rewrite (signed_of_Z z) in H by lia
  end.

(* [comment removed for export] *)
Lemma mod64_land63 : forall y, (y mod 64 = Z.land y 63)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h07__arithh14__ffh28__varmaph35__with41yh51zp;1p;2p;3p;4p;7p;6g001ej10Tg002Jj11Tg0113j1=Tg002hj26Tg0059j25Tg005Yj32Tg0000j23Tg0063j1<Tg006Qj2;Tg00:bj1:Tg00;Bj17Tg00P<j18Tg00<@j19Tg00<^j1GTg00=lj24Tg00Hmj4FTg00UJj7ETg00?Tj2DTg00@6j2?Tg00@bj3>Tg00AAj4@Tg009Mj2ATg00PZj3BTg00CAj6CTg000jR0P0f0R1g00[AR2#0R3#1%=2#0#1R2'6'5R4f1R5%03#0#0#0#0#1'5=201X501304%<2,;1g00\FR4#:%74%80%90%G0R4g00X;g00XZR3P3g00Y:R3P0g00W6R6,40g00ZZ1402CFg00YZFE1D43P1f2R3g000JR4g00[fR7'31?13=247dA>065C@b1b2b31A62P1b09B12ECW4o"). Qed.
Lemma land63_idem : forall y, Z.land (Z.land y 63) 63 = Z.land y 63.
Proof.
ltac2:(KReplay.run1 (kr_t_SFModel ()) [] "h01yh11zp;1p;2p;3p;6g0113j11Tg002Jj16Tg006Qj20Tg005Yj32Tg0000j25Tg00m[j34Tg00Q=j63Tg000jR0P0f0R1g00[A#1#1#1#1#1#6R2/02'0f1/029201X101012R3,501032A4122E3W0o"). Qed.

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
