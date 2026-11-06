(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct
     HeapIface HeapIfaceA HeapIfaceAEx BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_L5DefsA () := "C47Corelib7Classes?RelationClasses9ReflexiveC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct<segs_below_bC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct@wx_segs_nowrap_bC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctCwx_segs_nowrap_of_bC13~~~C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z8bit0_eqbC56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z=pow2_bits_eqbC56Stdlib6ZArith6BinInt1Z7pow_0_rC47Corelib4Init5Logic6eq_indC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z9lnot_specC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04C56Stdlib6ZArith6BinInt1Z6of_natC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~K47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec6v_jalrC13~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9jalr_tgtZC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A<land_m2_evenC13~~~K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;BigLinkGlue2BG<unsigned_litC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SeqExec<step_jalr_x0C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps01C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps02C13~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57hull_loC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57hull_hiC13~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5:hull_apartC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A:hull_hi_eqC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A:hull_lo_eqC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A4avisC13~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4woffC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct<range_avoidsC13~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init5Logic3iffK47Corelib4Init5Logic3and01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5ADrange_avoids_of_avisC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct@rdn_mrestrict_eqC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u64_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u32_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55u8_atC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A8avis_subC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctEstore_ok_mrestrict_eqC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58writableC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctAmrestrict_visibleC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57definedC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5L5KnA4L5KA8zeros_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L59img_clearC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct=page_allowedbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA4ahidC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C47Corelib4Init5Logic9False_indc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A=ahid_not_lazyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA>shadow_allowedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<in_shadow_ofC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A<ahid_allowedC13~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib5Lists4List5NoDup01C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List2InK46Stdlib5Lists4List5NoDup02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA2SBC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A@AS0_ALY_CELLS_D4C13~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes3sndC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7cell_isC13~~~i89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A:as0_layout00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<asan_staticsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:asc_got_loC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:asc_got_hiC13~~~C56Stdlib6ZArith6BinInt1Z6to_natC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9asc_cellsC13~~~I47Corelib5Lists7ListDef6Forall00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A:aly_got_loC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A:aly_got_hiC13~~~C47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A9aly_cellsC13~~~C46Stdlib5Lists4List4inclI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA;asan_layout00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceABasan_statics_cells00C13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5A.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
Lemma segs_below : segs_below_b RSEGS 0x698000 = true.
Proof.
vm_compute; reflexivity. Qed.
Lemma wx_nowrap : wx_segs_nowrap RSEGS.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "p;2p;1p;3g002Cj23Tg008aj12Tg005Uj30Tg00:5j21Tg006oR0g005oR1g006OR2'3%20=012d'1o"). Qed.

Lemma land_m2_even r : 0 <= r -> r mod 2 = 0 -> Z.land r (-2) = r.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "p'0h01Hh11bh24__x1h32H0h42H1h52H2h62H3h77__arithh84__ffh96__sat0h:8__varmaph;5__with<1qh=2r0h>2Hih?1ih@1rhA1xhB1yhC2HehD2HrhE2NZhF1ei001ehG1si011shH1zi021np;1p;2p;3p;4p;6p;7p;8g003Bj1yTg003gj1TTg00;Lj21Tg00;lj1RTg00<Jj2OTg00<hj20Tg00=Ij26Tg00=gj1@Tg00>Ej2\Tg00>ej1>Tg00?>R0j2xTg00?^j2;Tg00@:j2=Tg00@Wj2lTg00A8j3HTg00Aij2FTg00BJj28Tg00Bgj2ETg00CDj2BTg00Caj2ITg00DHj23Tg00DdR1j29Tg00E?j2DTg00Efj2CTg00FLj2GTg00G2j1_Tg00GQj2NTg00H:j2^Tg00H[j3]Tg00IDj3[Tg00Imj2ZTg00JYj1YTg00K9j3XTg00KYj1WTg00L9j2VTg00LWj1wTg00M5j1vTg00M`j2uTg00NCj2UTg00Nfj1rTg00OHj2qTg002Cj2STg00Ojj2pTg005Uj3:Tg00PVj3oTg00Q5j4nTg00Qgj4PTg00RCj1kTg001ej6<j7gTg00Rcj1hTg00SEj2iTg00Sbj1fTg00T@j4KTg00Tkj3jTg00URj1eTg00V3j6QTg00VOj1mTg00Vnj1dTg00WLj3cTg00Woj3bTg00XRj3aTg00Y5j7sTg00YYj6tTg00Z=j8`Tg00ZaR2f0R3';p=4g00[?R4?:32p=5g005oR5f1R6;:3p=7g00[]R79:53p=AA:463p=2P4P6g00\=P3CKp=MP6g00\dR8g00]CR9P9g00]cR:P3g00^CFsp=?P6P8P9P9P:P3Etp=Lf3R;P8P9P9P:f2R8P6P3G`p=J%43R<g008<R=#yR>#TR?,16#5%R>R>,O8P5f4R@/0610>6'6f5RA/08RB,73X15P5%T=RC/06#@RD16B3/7BX151\62%56RB%>B'xP0%58R0%>0f6R0/0;RB10C;#@'6/7BP3%5;RBP4P2f9RE/06RF/6D/7F^><X?41;22RFP5f8RD/1?RG/=CRH10C2#@,63/73X15P5P711E?RI/=C,73X15P5PHP7P11=63#A1286#>R1[1263#>1=86#A[RJ1=;8#A\11l63P3n2001000000120000000XB4XA4R1PJ^B4^A4RJP3PIPCAHE?D%4?RKf:RL/1?RM#4RN[1FL?%5?RO#>RPf;RQ18Q?,E?11Q?RR'B'2[1IQ?132?RSf<RT/1?RU#413U?'9[1DT?13?2RVf=RW/1?RX,3?1;X2'9[1CW?f>RY/8?RZ#5\O1GY?f?R[/1?R\/2[\O18[?P4f@R[/1?P4g00^cR]g00_OR^#_,N4%R=,^41N4^5]45[4g00_n'Z%Y]R^3XR_%W]R]1V46R`%w4Ra%v4Rb1u4=R=1U42Rc'M,?bRd%r9R91U4C,M=,?b,LbCJ1qb:R:P3P8g006ORe,S51p38=:5edAo426CnRfb8b:b;X24%53Rg126Cg00`ZRh[[^24P3P6P[O2b7b=b<b6b5b4b3b0b9O3b0CP16H7%kHE<%@e,6H/7He10D2%hDE<W>P@P3P;FgWFP3O1%>BP510C@RBP7P41i?2RH103A#AXH4P51=2@%A3X15P1PJP3P2PAf7RJ9HD?%4I\K1FE?18L?R1,E?/BM,2L\P1IL?%4R13R?'9\S1DQ?13?U1;U2'9\V1CT?18W?RU#5\O1GW?11Y?R[/2Y\OPZP4P\P4P_P]P`PaPb1LbdP91Mc=,?b,LbCJP:Pfb8b:b;X24Ph\gA:426Ph[[^24P3PYPLO2b7b=b<b6b5b4b3b0b9O3b010H@AHJ?0%4G\K1FD?18E?RH,E?/BI,2E\P1IE?13M?,9N\S1DL?13?R1;R2'9\V1CQ?18T?#5\O1GT?12XW\OPUP4P[P4P^P]%f4PaP4Pcg00a7R[PcCK,?bP:Pfb8b:b;PFP3b7b=b<b6b5b4b3b0b99j2@E<PC%e?EQCPA:57BP5P710E0R7%@3'6/77X15P510DARB1737X151S5B16Be%mBE<10CAP3EQb0WEP3O1n200110100021110011102bG%dC/06AH@?;11A?#4\K1FA?180?,E?110?'B,20\P1I0?11J?R0#4130?'9\S1DJ?13?G1;G2'9\V1CD?%5H\O1GE?12ML\OP1P4PRP4P^P]P`PaPbP4PcP[P=CK,?bRbP9PbCJP:Pfb8b:b;X24%46\<^24P3PLPEO2b7b=b<b6b5b4b3b0b99cC6E<1O@>/06Ab@>6E<X><X?47a8WCWDX@4P3O1X@4o"). Qed.
Lemma ret_to fx R M (pc : Z) (W : bv 32) r :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R pc M) (st fx R r M).
Proof.
intros HF HEC HD H1 Hr He. eapply mst_step; [reflexivity | | apply mst_refl].
assert (D: decode_any W = Some (Jalr 0 (reg 1) (0%bv : bv 12), 4%Z)). { rewrite HD. repeat f_equal; apply bv_eq; reflexivity. }
rewrite (step_jalr_x0 RSEGS R _ M (seg_rom RSEGS) _ (reg 1) (0%bv : bv 12) (Z_to_bv 64 r) HF HEC D H1).
f_equal. f_equal. unfold v_jalr. f_equal. unfold jalr_tgtZ. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r.
rewrite BG.unsigned_lit by lia. apply land_m2_even; lia. Qed.

Lemma hull_lo_eq : L5.hull_lo RSEGS = 0x10000.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "p;1p;2p;3g003gj15Tg002Cj23Tg01B[j12Tg005Uj34Tg003Bj11Tf0#1#1p=0g00[?R0g008<#0#0#0#0#0#0#0#0#5R1'3g006o#2=401do"). Qed.
Lemma hull_hi_eq : L5.hull_hi RSEGS = 0x698000.
Proof.
vm_compute; reflexivity. Qed.
Lemma hull_apart_of a n : (a + n <= 0x10000 \/ 0x698000 <= a) -> L5.hull_apart RSEGS a n.
Proof.
unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. tauto. Qed.
Lemma hull_apart_lit a n : L5.hull_apart RSEGS a n -> (a + n <= 0x10000 \/ 0x698000 <= a).
Proof.
unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. tauto. Qed.

(* [comment removed for export] *)
Definition avis (H : word -> bool) (a n : Z) : Prop := forall i, 0 <= i < n -> H (Z_to_bv 64 (a + i)) = false.
Lemma avis_sub H a n a' n' : avis H a n -> a <= a' -> a' + n' <= a + n -> avis H a' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "h04__x1h14__x2h24__x3h32H0h41Hh52H3h67__arithh74__ffh88__varmaph95__with:4__x4h;4__x5h<1ah=2a'h>1nh?2n'h@2H1hA2H2hB2HihC1VhD1ihE1zp;1p;3p;2p;4p;7p;6p;8g003Bj15Tg00a^j1[Tg00b<j1STg01JNj3ETg00?^j2:Tg00CDj20Tg00DHj21Tg00DdR0j2BTg01KYj27Tg005Uj38Tg00JYj1JTg00KYj1HTg00L9j2ATg01L6j4@Tg00LWj1VTg00M5j1UTg00M`j29Tg01LTj3GTg002]j1FTg00T@j4=Tg00OHj2RTg002Cj2QTg00Ojj2NTg00PVj3MTg00Q5j4LTg00cAj2KTg00G2j1<Tg00GQj26Tg00IDj3;Tg00Imj2CTg00K9j3DTg00Sbj1ITg00Nfj1OTg00NCj2PTg016dj7TTg00V3j6ZTg01M7j3YTg00Y5j7XTg00Z=j8WTg00ZaR1f0R2':p=3g00[?R3f1R4;Y2p=4P4g00\dR5g00]CR6P6g00]cR7P2g00^CFXp=2P3P4g00a7P2C=p=?f3R8P5P6P6P7f2R9P4P2GWp=>g008<R:#5R;#5R<#5#5#5#5#[R=#Sg005oR>[R?f4R@?E891:@91089f5RA/0@':%32112@'BP0%34114Af9RBf7RC/7B/09RD'0RE10C9RF583P2%38RGf8RH,1@g00^cRI#JRJ%HIRKP31A39P41A38C@%V3RL%U3RMP3193:RN193;RO=G3N%F:,93R:'4'4g00\=14O:C='21RM7RPP2P9g006ORQ,Q>1N29=8>QdAM314CLRQb7b8b9X03X13X231742/09,021049583^03^13^23P2f6RRf;RSf=RTO3b6W5W3P4P2O2n200100000012000000017RH/04,0H10R4583P3PEPS1K=2O1g00[]58>XE3PAPDP0%39119Rf:,7H/08R0#3110B'BP4%3@11ABg00_OR0#<RD#<R>#<R=,63163D1630R05;35;3g00_nRD'C%<=,63163>=;305;3/CD=DIJ5DIPKP3P31A3@P9%I3RKC@P4P31A3AP8PKC@C@PLPMP3P:g01B4RL%F;,93R;C=,2M%O6RKPM1P31R1/?:,2MPKPM14N;193<R<,4O'?,2MPKPM1?ON,2MPKPMP5P6P6P7AG3NO/4:R:,?1,2MP3P:PLP<C=,2MFTC>C>C>C>PPPQb7b8b9X03X13X23X:3X;3119@109R108A':1:@817@A/0RRR#311RC'B[[\G[^03^13^23^:3^;3P2PSPTPCf>f<P4P9PHPBO9b6W5W3P4P2O2n2001000000121000000O2PFP2EZb3WBXD3AEC@8eWAW@WCX?3X=3X>3X<3X4?P@P8P9P4P2O5X?3X=3X>3X<3W4o"). Qed.
Lemma range_avoids_of_avis H a (n : nat) : avis H a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> range_avoids H (Z_to_bv 64 a) n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "h04__x1h14__x2h22Hah31Hh43Hk0h57__arithh64__ffh76__sat1h86__sat2h98__varmaph:5__with;4__x3h<1ah=4cstrh>5cstr0h?1nh@2HkhA2HnhB1VhC1khD1zp;1p;3p;2p;4p;6p;<p;7p;8g003Bj15Tg00a^j1iTg00b<j1QTg00hkR0j12Tg01JNj3hTg00CDj2<Tg003gj1DTg00SEj2OTg00?^j2:Tg01MZR1j2BTg00cAj2@Tg005Uj3;Tg00DHR2j21Tg002Cj2=Tg01N2j4ZTg01NYj1HTg013bj2WTg014Jj3VTg00JYj1UTg00KYj1TTg00L9j2ETg00Sbj1PTg01L6j4FTg00LWj1NTg00M5j1MTg00NCj2ATg00M`j29Tg00Nfj1LTg00OHj2KTg00Ojj2RTg00PVj3JTg00Q5j4STg00Ddj2GTg00mFj2gTg00G2j17Tg00GQj26Tg00IDj3>Tg00Imj2fTg00K9j3eTg002]j1_Tg01M7j3\Tg016Aj3[Tg017Hj2YTg001ej6]Tg01O>j2^Tg01PFj3XTg01QVl<aTg00T@j4ITg00Y5j7bTg016dj7cTg00Z=j8dTg00ZaR3f0R4':p=0g01R;R5g00[?R6P1P0P2g01RZf5R2f4R0f3R1f2R7f1R8P4M<ap=`P6P8g00a7P4CIp=8P8g00\dR9g00]CR:P:g00]cR;P4g00^CFbp=4P6P8g01B4P4CIp=?P7P9P:P:P;P8P4Fcp=CP1P9P:P:P;P7P8P4Gdp=3g008<R9#5R<#5#5#5#5#5R=#iR>#Qg005oR?[R@%249h78%07RA%27RB,<1%D<RC%D=R='ORD':1B40P6f6REf8RF1<4B,@>O1g00[]RG5;?XD6P0%28RH1B82%22RI,1HRJP8PH1=6HP2PI1=6IE`P4CZRIPJ%H7RH%0BRBf7RK#HRL%2KRM#0RN1WC=RO113C%0=113D[[RP%0CRQg01AXRRAVC=8UW2R=%0D\R^2QRQg00^cRR#URS%TRRTP61E67RUP8%P6CF%N6RV%M6RW1A63RX1969RY'8,4WRZ%L:R:PW196<R<,?Y,4WR[P:ACWZ[C3C31KW;R;P4P7g006OR[,=?1R47=;?[dAJ638CSR3b6b9b:X06X16%0411871171,GA[[^06^16P4f;#2R[PMP0P2O4b5b7b8b>b=b4O21@>ER\,g>PIPJPHPBPLPNPOPPP=PQg00_ORQ#7#7R=#7RP#7,66166P166=166Q5>65>65>6g00_n'f=eRSPTP6PUP81E61CFPVPW%_9,96R9,8X,4WP:PW1?9<,4WP:PWA\6Y<1A6C=[6>RC'8,4WP:PWPZP:1?YC,4W9CWZC3C3C3C3P;P3b6b9b:X06X16X;611171<71/:D%01%00110D'G[[[\A^06^16^;6P4PMP[f<P0P2PFf9O7b5b7b8b>b=b4,YEE]PK1^\8O1=;?GeW@XC51@>0=X21eWAW2WBX?5X<6X3@P7P8P4O3X?5X<6W3o"). Qed.

Section WithH.
Variable H : word -> bool.
Lemma u64_at_vis M a v : avis H a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS (mrestrict H M) a v <-> L5.u64_at RSEGS M a v.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"; "WithH"] "h01Mh11ah21vh32H0h42Hah52Hnh61Vh71op;1p;3p;2p;4p;6g003Bj11Tg00a^j18Tg00b<j19Tg00b_j16Tg003gj15Tg01JNj3FTg00?^j2:Tg00CDj2@Tg00SEj2?Tg00KYj1>Tg00cAj22Tg00G2j10Tg01S<j44Tg01TCj2=Tg00dij2<Tg005Uj33Tg01UKj2;Tg01Udj4ETg01V?j2DTg01WLj6CTg01Xgj6BTg001ej6ATg01Z;j47Tg008<#1R0#1#1R1#1#1#1R2#8R3#9%81#9R4#6[R5g00[?R6p,1HR7f1R8%51R13Fg00Zaf2R9':f3R:/@1%50%52'?':%>4R4#6R2g006oR0f5R1f4R;,23R<g00_O#0#0#0#0#0#0#0#0R=C4R>f0R?1==<,<4R@532P0f61231P=C4=32@R@';X72123:,==,<4932>R>P@[R@P@P?X3>R>P>CEP01D71R>P<P=C4P0P7P=P1P<P7P;P=P9P8P?ECEBEAP0P>P;P:C7P0P1P;P:C7';eW5W4W6X26X16X05P9P8P?O3X26W1W0o"). Qed.
Lemma u32_at_vis M a v : avis H a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS (mrestrict H M) a v <-> L5.u32_at RSEGS M a v.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"; "WithH"] "h01Mh11ah21vh32H0h42Hah52Hnh61Vh71op;1p;3p;2p;4p;6g003Bj10Tg00a^j18Tg00b<j19Tg00b_j16Tg003gj15Tg01JNj3FTg00?^j2:Tg00CDj2@Tg00SEj2?Tg00KYj1>Tg00cAj22Tg00G2j11Tg01S<j44Tg01TCj2=Tg00dij2<Tg005Uj33Tg01UKj2;Tg01Udj4ETg01V?j2DTg01WLj6CTg01Xgj6BTg001ej6ATg01[Fj47Tg008<#0R0#0R1#0R2#0#0#0R3#8R4#9%82#9R2#6[R5g00[?R6p,1HR7f1R8%51R13Fg00Zaf2R9':f3R:/@1%50%53'?':%>2R2#6R3g006oR0f5R1f4R;,24R<g00_O#1#1#1#1R=C4R>f0R?1==<,<2R@533P0f61241P=C4=33@R@';X73124:,==,<2933>R>P@[R@P@P?X3>R>P>CEP01D71R>P<P=C4P0P7P=P1P<P7P;P=P9P8P?ECEBEAP0P>P;P:C7P0P1P;P:C7';eW5W4W6X26X16X05P9P8P?O3X26W1W0o"). Qed.
Lemma u8_at_vis M a v : avis H a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS (mrestrict H M) a v <-> L5.u8_at RSEGS M a v.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"; "WithH"] "h01Mh11ah21vh32H0h42Hah52Hnh61Vh71op;1p;3p;2p;4p;6g003Bj10Tg00a^j1<Tg00b<j18Tg00b_j15Tg003gj14Tg01JNj3FTg00?^j29Tg00CDj2ATg00SEj2?Tg00KYj1>Tg00cAj21Tg00G2j1=Tg01S<j42Tg00JYj1GTg00K9j3;Tg00dij26Tg005Uj33Tg01UKj2:Tg01Udj4ETg01V?j2DTg01WLj6CTg01Xgj6BTg001ej6@Tg01\Qj47Tg008<R0#0R1#0#0R2#0#0#0R3#<R4#8%<2R2#8R5#5[R6g00[?R7p,1HR8f1R9%40R03Fg00Zaf2R:'9f3R;/A0%41%43'?'9%>5R3#5R1g006oR0f5R<f4R=,14R>g00_O#=R?C2R@f0RA112=%G5RB5;5,63RC531P0f6114<P?C2=31CRC':X71112;=;5B,63931@R@PC[RCPCPAX3@R@P@CEP01D8<R@P>P?C2P0P8P?P<P>P8P=P?P:P9PAECEBE@P0P@P=P;C7P0P<P=P;C7':eW5W4W6X27X17X06P:P9PAO3X27W1W0o"). Qed.
Lemma writable_vis M a n : avis H a n -> 0 <= a -> a + n <= 2 ^ 64 -> L5.writable RSEGS (mrestrict H M) a n <-> L5.writable RSEGS M a n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"; "WithH"] "h04__x1h14__x2h27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with84__x3h94cstrh:1dh;1kh<4__x4h=2Hah>2Hdh?2Hkh@1MhA1WhB1ahC1nhD2HnhE1VhF1bp;1p;3p;2p;4p;8p;6p;7g003Bj15Tg00a^j1GTg00b<j1?Tg00b_j1KTg01JNj3gTg00CDj20Tg003gj1@Tg00SEj2QTg00?^j21Tg00hkj1<Tg01V?j2>Tg00cAj2ETg01][j4:Tg01NYj1^Tg013bj2ZTg00DHj2CTg014Jj3WTg00JYj1VTg00KYj1UTg00L9j2;Tg00LWj1STg00M5j1RTg00NCj2DTg00M`j28Tg00Nfj1PTg00OHj2OTg002Cj2NTg00Ojj2JTg00PVj3LTg00Q5j4MTg01L6j49Tg01M7j37Tg002]j1ITg00Sbj1HTg01^[j8TTg00G2j1ATg00GQj2=Tg00IDj3FTg00Imj2fTg00K9j3eTg016Aj3dTg01WLj6cTg01_jj6]Tg00V3j6\Tg001ej6[Tg01Udj4YTg01aCj4BTg01UKj2_Tg005Uj3XTg00T@j4`Tg00Y5j7aTg00Z=j8bTg00ZaR0f0R1'1p=4g005oR2g006OR37X1p=6f2R4g00\dR5g00]CR6P6g00]cR7g00[?R8f1R9g00a7P1C`g00^CFap=2f3R:P5P6P6P7P4P9P1Gbp=3g008<R5#5R;#5R<#5R=#5#5#5R>#GR?#?%G=#?#K[R=p,1HR@?g91%4410:4%@;RA%@>R>'QRB'1g01R;RC%49RD%<9,04REf6RF'1RGg006oRHf9RI,>@f8RJ/0:,E?RKP4C:#6[[];^:8RLf7RM,1EREPHf:RN10I:RO,E?RPP4C:RQ#6[\D^;C^:8[PHPIPKP4C:#6\G\D^;C^:8RGPH1>@NPPP4C:RK#6\E\D^;C^:8[P2PK%61XF2RRf4RSP:P4%^4RT%<4RU#4RV1ZA>RW1C0A%4>1C0B[[RX%4ARYg01AXRZAWA>9UW=R>%4B\Z^=YRYg00^cRZ#VR[%UZR\1;89%S8R]%R8R^1D80R_1885R`52^Ra%P6R6PaC31O^7R7P1P41N231J14#6dAL809CMR0b3b6b7X08%41PD[^08P1PMf5R3O2b2b4b5b9PTPVPWPXP>PYP[P\P81;84RbP91;8:RcC9P]P^188;R;978`Rd%I5,88R552^ReP6PeC3P7P0b3b6b7X08X18X881019/141094Re/1:Rf[^08^18^88P1f<Rg%<FRFPMPSO4b2b4b5b9O4RhPQPHP@P4PNPPP@POP4P@PIPJPOPUPMPTPVPWPXP>PYP[P\P8PbP9%H8RbC9RUP]P^A2^_;ROP6A2^`dC3P7P0b3b6b7X08X18119e\D^08^18P1PMf=RJP3O3b2b4b5b9PTPVPWPXP>PYP[P\P8P81;8SP4PbC9P9PcC9RcP]P^A78;5188<R<52^R;P6A78d5R5A78`<R<52^C3P7P0b3b6b7X08X18X88X<810e:109SRe'1\f^08^18^88^<8P1PgPFPMPJPSO5b2b4b5b9GTPTPVPWPXP>PYg00_OR`#ARb#A,=81=8b1=8`5F85F8g00_n'f=eZ[R[P\PUP]P^POP6P^PaP6A2^_dC3C3P7P0b3b6b7X08X18104:Rd#4\D\D^08^18P1PMPJP3PNO4b2b4b5b9PTPVPWPXP>PYP[P\PcP]P^P;P6P^1D8A=d8?R?92^<P6A2^5?C3C3P7P0b3b6b7X08X18X88X<811eB10dS/1B[\f^08^18^88^<8P1PgPFPMPJPSPIO6b2b4b5b9EcE]RIE\X?EX>DX;CX:8XALP2PQPRPhPKPIE[X?EX>DX;CX:8XAGCYPH1>@3PSP:CBPHP3PSP:CB'_eWDW=WEXC8XB8X@=P4P9P1O3XC8XB8W@o"). Qed.
Lemma defined_vis M a n : avis H a n -> L5.defined (mrestrict H M) a n <-> L5.defined M a n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"; "WithH"] "h01ih11Dh22Hih31Mh41ah51nh61Vh71op;1p;3p;2p;4p;6g003Bj11Tg00a^j1:Tg00b<j17Tg00b_j1<Tg01JNj3DTg00?^j2ATg00DHj29Tg00Ddj26Tg00CDj24Tg00cAj25Tg01V?j33j2>Tg00Nfj1;Tg005Uj30Tg00>ej12Tg01bPj4CTg00V3j6BTg001ej6@Tg01Udj4?Tg01cej38Tg01UKj2=Tg008<#1#1#1R0#1#1#1#:R1#7%:0#7R0#<R2[R3g00[?R4p,1HR5f1R6f0R73Dg00Za/A7R8f2R9,97'6R:f5R;f4R</46,51R=535%;0R0502#2[^04R>f3R?,97,68R8f6R@14;6,51RAO1=020#2RB[^04[P;P=O1=020#2\:^04R:A35@A=020#2RA\8^04[P9P6P7O2R=PAP2f7RA14@9,51R1535R@A0270#2X72R;P7PAP1O1RCP5PAP1P<P9P6O2CCR<EBA02C0#2P7b1b1X28X04X1>P=PBP2PCP;P7P@P<E@b1X28X04X1:C?1>5??896A8?96'=eW6X54X44X33P9P6P7O3X54W4W3o"). Qed.
Lemma zeros_at_vis M a n : avis H a n -> L5KA.zeros_at (mrestrict H M) a n <-> L5KA.zeros_at M a n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"; "WithH"] "h01ih11Dh22Hih31Mh41ah51nh61Vh71op;1p;3p;2p;4p;6g003Bj10Tg00a^j19Tg00b<j16Tg00b_j1;Tg01JNj3CTg00?^j2?Tg00DHj27Tg00Ddj25Tg00CDj24Tg00cAj22Tg01V?j33j2=Tg00dij2:Tg005Uj31Tg01bPj4BTg00V3j6ATg001ej6@Tg01Udj4>Tg01e1j38Tg01UKj2<Tg008<#0#0#0R0#0#0#0#9R1#6%90R0#6R2#;R3[R4g00[?R5p,1HR6f1R7f0R83Cg00ZaR9/?8R:f2R;,78'5R<f5R=f4R>/47,21R?5361209,:2R2513[^05R9f3R0,78,5:R:f6R@14=7,21RAO1=132RB[^05[P=P?O1=132\<^05R<A36@A=132RA\:^05[P;P7P8O2R?PAP3f7RA14@;,21R1536R@A1382X73R=P8PAP1O1RCP6PAP1P>P;P7O2CBR>EAA13C2P8b1b1X2:X05X19P?PBP3PCP=P8P@P>E@b1X2:X05X1<C>1=60?8;7A80;7'<eW6X55X45X34P;P7P8O3X55W4W3o"). Qed.
Lemma img_clear_mrestrict M lo hi : L5.img_clear M lo hi -> L5.img_clear (mrestrict H M) lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"; "WithH"] "p'0h01Mh12hih22loh31Ch42Hih51bi001bh61ip;1p;3p;2g003Bj10Tg00a^j15Tg00b<j12Tg00b_j16Tg01f?j33Tg00?^j2<Tg00DHj2;Tg00Ddj28Tg00cAj21Tg00Nfj17Tg005Uj34Tg002Cj29Tg01V?j3:j2=Tg008<#0#0#0R0#0#0#0#5R1#2%50#2R0#6R2[R3g00[?R4f2R5f1R6f0R733f3R8/<71;75'8p,1HR91116R:O1g005oR;P;P;P2P7%70R0f71118O1n0100000020000=420P71920P8P5P6O2n0110000020000b5f5=:9:=420eW4X641=98?356eW3X14X24X03P5P6P7O3X14W2W0o"). Qed.
(* [comment removed for export] *)
Lemma mrestrict_agree M lo hi : (forall i, lo <= i < hi -> H (Z_to_bv 64 i) = false) -> forall i, lo <= i < hi -> mrestrict H M (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"; "WithH"] "h01Mh12hih21ih32loh42Hih51Vp;1p;2p;3p;4g003Bj10Tg00a^j15Tg00b<j11Tg00b_j16Tg00?^j24Tg00DHj22Tg00Ddj23Tg00cAj29Tg005Uj38Tg01bPj47Tg008<#0#0#0R0#0#0#0#5R1#1%50#1#6[R0g00[?R2f2R3f0R4'4f1R5,24'3g005op,1HR61915R1O1g00[]38[^22f3/441243'3P6f5P1P3P5P4O2C7W4X22W5X12X32X00P3P5P4O3X12W3W0o"). Qed.
End WithH.

(* [comment removed for export] *)
Lemma ahid_not_lazy A m w : page_in_ranges (page_base w) (m_vm_lazy m) = false -> ahid A m w = false.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "h01Ah11mh21wh31Eh41bp;2p;1p;6p;3g00fKj2?Tg00KYj1>Tg003Bj10Tg00a^j15Tg00b<j1=Tg01gMj12Tg01hEj14Tg01i=j23Tg01j:j26Tg00=gj17Tg00=Ij28Tg002Cj29Tg001ej6<Tg01kKj3:Tg005Uj3;Tg005oR0f0R1g00[]R23;p=1g00[?R3/?3#>R3g01lUR4g008<#0#0#0#0#0#0#5#=R5%21f1R6#4'3#1P0P2f4f2R7#2'6#7,81#1X401902%26%47'3P1E<f3?:76#1eW3X25X14X03P7P6P1O3W2W1W0o"). Qed.
Lemma ahid_allowed A m w : page_allowedb A (page_base w) = true -> ahid A m w = false.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "h01Ah11mh21wh31Eh41bp;2p;1p;3p;6g00fKj2?Tg00KYj1>Tg003Bj10Tg00a^j19Tg00b<j1=Tg01gMj11Tg01j:j28Tg005Uj34Tg01hEj15Tg01i=j26Tg00=gj13Tg00=Ij27Tg00RCj1<Tg001ej6:Tg01kKj3;Tg005oR0f0R1g00[]34p=2g00[?R2/?2#>R2g01lUR3g008<#0#0#0#0#0#0#9#=R4f2R5%11'8g006OR6540P0P6%15f3R7#5'6%31'7#2X40f1R0#1R8%55'6R9#<%36,79#2e1878P1E:A;750#2eW3X24X13X02P5P0P1O3W2W1W0o"). Qed.
(* [comment removed for export] *)
Lemma avis_of_not_lazy A m (P : Z -> Prop) a n :
  (forall w : word, page_in_ranges (page_base w) (m_vm_lazy m) = true -> P (bv_unsigned w)) ->
  (forall i, 0 <= i < n -> ~ P (a + i)) -> 0 <= a -> a + n <= 2 ^ 64 -> avis (ahid A m) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "p'0h01Eh12HLh22Hah31Ah41Ph54__x1h64__x2h74__x3h81ah91ih:1mh;1nh<1Hh=2H0h>2HPh?2Hih@2HnhA7__arithhB4__ffhC6__sat0hD6__sat1hE8__varmaphF5__withG1bi001bhH1whI1zp;2p;1p;3p;4p;7p;6p;8g00fKj2gTg00KYj1KTg003Bj13Tg00a^j1QTg00b<j1fTg01gMj1:Tg01hEj18Tg01i=j29Tg00mFj2@Tg00DHj22Tg00DdR0j2?Tg00CDj20Tg00>ej1cTg003gj1HTg00SEj2YTg00?^j2DTg00cAj26Tg002Cj2CTg005Uj34Tg013bj2UTg014Jj3TTg00G2j1;Tg00GQj27Tg00IDj3>Tg00Imj2GTg00JYj1STg00K9j3FTg00L9j2ITg01L6j4RTg00LWj1PTg00M5j1OTg00M`j2ATg002]j1NTg00T@j4ETg00Nfj1MTg00NCj2JTg01M7j3LTg016Aj3eTg016dj7dTg00OHj2bTg00Ojj2_Tg00PVj3ZTg00Q5j4[Tg017Hj2\Tg00V3j6XTg01mKj2]Tg01mjj4^Tg01kKj2WTg01JNj3`Tg00Y5j7aTg00Z=j8VTg005oR1f0R2g006OR334p=Bg00ZaR4/D2p=1f1R5g00\dR6g00]CR7P7g00]cR8P2g00^CFap=5g00[?R9P5g00a7P2CEp=<f3R:P6P7P7P8f2R;P5P2GVp==1g99#KR<g01lUR=p-0\9R>g008<R?#3R@#3#3#3#3#3RA#QRB#f%:2f4RC#8'9#BPC1@B5O1[]H%12RD122;'?f5RE10C5O1#c[^99%1:RF10C:%H@RG%HARA'YRH'D122E,?Df:RDf9RIf7RJ/05,6BRK%:K%8I'9P11C12f8RK/0;,6B#:%8D'9=412P110DC,6BRL#:f<RM#8'9=412g00[]RN9415]0P510I:,6B#:f;RO#8'9RP#BA413NPJPCP:PKPLP2O2PO1@BLO1P910OERO,6B,@Bf=RLP2O1XI9P2PO1UGA124G%1A124H[[%1GRQg01AXRRATGA5UW2%1H\R^2QP0%1J12JMf>R0/0KRQ#112QH'?f6%1If?,2Dg00^cRDg00_ORI#;RQ#;RR#;RA,79179Q179IRI5>95>9g00_nRQ'G%;A,79179R=>9I5>9/GQ%SD5FD3F%KDP91I9;P51I9:CR%P9%O9RDP91A9@R@g01B4RQ%N?,A9RICE,5D%M7RRPD1J94RA/<@,5DPRPD1A9?R?=L9I1J9G=e9BRB'<,5DPRPD1<A?,5DPRPDP6P7P7P8AL9?@R?,<A,5DP9P?PQPBCE,5DFdC=C=C=C=1bD8P2P;1C131_2;#BdAZ945C[bBbEbFX59X69X79125;%1;10;C/DH10CER4#1124H'?\F[[[^59^69^79P2fAPMfBP5P;PLP0O7bAW=W<P5P2O2n2001000000121000000bCbD,\OEXPMPOO1P2b1b1O3']W0A41PN1C1NW0n0110000020100P2O1b0bGC^W?X991WKJ?`ECeW@W2W>W1X;9X89X4>X:=X3<PCP:P;P5P2O5X;9X89W4W:W3o"). Qed.
Lemma avis_of_shadow_allowed A m p k a n :
  shadow_allowed A p k -> (forall i, 0 <= i < n -> in_shadow_of p k (a + i)) -> avis (ahid A m) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "h01Ah11ah21ih31kh41mh51nh61ph72HIh82Hih92SAp;2p;1p;3p;4g00fKj2=Tg00KYj1<Tg01o>j36Tg00?^j24Tg00DHj23Tg00Ddj21Tg00CDj22Tg020Rj35Tg003Bj10Tg00a^j17Tg00cAj28Tg021dj49Tg01kKj2:Tg01JNj3;Tg00[?R0/=0#<R1g01lUR2f5R3f3R4f2R536g00Zaf0R6'4R71365'1f6R8f4R9f1R:'2753[^201364,17f9f8g008<#0#0#0#0#0#0#7123:R7'8P4P7P5P:P6O2O2C9W8X20f7/:8?;45eW7W9X50X10X30X60X42X01P3P9P4P5P:P6O6X50X10X30X60W4W0o"). Qed.

(* [comment removed for export] *)
Definition SM1 : Z := 0x5e588. Definition SM2 : Z := 0x5e718. Definition SM3 : Z := 0x5e8b4.
(* [comment removed for export] *)
Definition AS0_ALY_CELLS_D4 : list (Z * Z * Z) :=
  [ (0x1419f8, 8, SB); (0x141a00, 4, 1); (0x13b1c8, 8, 0x12b88c); (0x13b158, 8, 0x112324);                     (* [comment removed for export] *)
    (0x1391b8, 8, 0x1419f8);                                                                                (* [comment removed for export] *)
    (0x1391c0, 8, 0x1426e8); (0x1426e8, 8, 0); (0x1391c8, 8, 0x1426f0); (0x1426f0, 8, 0);                        (* [comment removed for export] *)
    (0x1391d0, 8, 0x1426e0); (0x1426e0, 8, 0x7fffffffffff);                                                  (* [comment removed for export] *)
    (0x139d20, 8, 0x1426d9); (0x1426d9, 1, 1);                                                               (* [comment removed for export] *)
    (0x13b1c0, 8, 0x12b488);                                                                                (* [comment removed for export] *)
    (0x1426d8, 1, 1);                                                                                      (* [comment removed for export] *)
    (0x13b0b8, 8, 0x12c46c);                                                                                (* [comment removed for export] *)
    (0x675a78, 8, 0x675aa0); (0x675aa8, 8, 0x676280);                                                     (* [comment removed for export] *)
    (0x141260, 1, 1); (0x141264, 4, 0);                                                                     (* [comment removed for export] *)
    (0x675a28, 8, 0x696f38);                                                                              (* [comment removed for export] *)
    (0x1391a8, 8, 0x1d3528); (0x1d35b1, 1, 1);                                                             (* [comment removed for export] *)
    (0x139208, 8, 0x1d1498); (0x1d1498, 4, 0);                                                             (* [comment removed for export] *)
    (0x139fc0, 8, 8) ].                                                                                    (* [comment removed for export] *)
Lemma AS0_ALY_CELLS_D4_nodup : List.NoDup (map (fun c => fst (fst c)) AS0_ALY_CELLS_D4).
Proof.
unfold AS0_ALY_CELLS_D4; cbn [map fst].
repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H |]). apply List.NoDup_nil.
Qed.
Lemma AS0_ALY_CELLS_D4_img : Forall (fun c => 0x10000 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= 0x698000) AS0_ALY_CELLS_D4.
Proof.
repeat constructor; cbn; lia. Qed.

Record as0_layout (L : asan_layout) (C : asan_statics_cells) : Prop := ALY {
  aly_segs : hl_segs L = RSEGS;
  aly_sm1 : hl_stack_malloc L 1 = SM1; aly_sm2 : hl_stack_malloc L 2 = SM2; aly_sm3 : hl_stack_malloc L 3 = SM3;
  aly_nr : hl_handle_no_return L = 0x81b6c;
  aly_memset : hl_asan_memset L = 0x78ab4; aly_memcpy : hl_asan_memcpy L = 0x78618; aly_memmove : hl_asan_memmove L = 0x78cf4;
  aly_malloc : hl_malloc L = 0x7a19c; aly_free : hl_free L = 0x7a198; aly_aligned : hl_aligned_alloc L = 0x7a1a4;
  aly_img_lo : hl_img_lo L = 0x10000; aly_img_hi : hl_img_hi L = 0x698000;
  aly_scr_sm : hl_scr_stack_malloc L = 512; aly_scr_nr : hl_scr_no_return L = 4160; aly_scr_mem : hl_scr_mem L = 2560;
  aly_scr_malloc : hl_scr_malloc L = 4096; aly_scr_free : hl_scr_free L = 4096; aly_scr_aligned : hl_scr_aligned L = 4096;
  aly_got_lo : asc_got_lo C = 0x132000; aly_got_hi : asc_got_hi C = 0x13a000;
  aly_cells : incl AS0_ALY_CELLS_D4 (asc_cells C);                                       (* [comment removed for export] *)
  aly_static_img : forall a, hl_rt_static L a -> 0x10000 <= a < 0x698000;
  aly_ro_img : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x698000;
  (* [comment removed for export] *)
  aly_static_lo : forall a, hl_rt_static L a -> 0x13a000 <= a;                          (* [comment removed for export] *)
  aly_cost : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Lemma u64_at_of_cell M a v : cell_is RSEGS M a 8 v -> L5.u64_at RSEGS M a v.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "h01Mh11ah21vh31Hp;1p;5g003Bj11Tg00a^j13Tg00b<j12Tg00b_j14Tg00G2j10Tg02:=j55Tg008<#1#1#1R0#1#1#1#3#2%30#2#4[R0g00[?R1g006of2R2f1R3g00_O#0#0#0#0#0#0#0#0f0R4D5P4W3X21X11X00P2P3P4O3X21W1W0o"). Qed.
Lemma u32_at_of_cell M a v : cell_is RSEGS M a 4 v -> L5.u32_at RSEGS M a v.
Proof.
ltac2:(KReplay.run1 (kr_t_L5DefsA ()) ["SCFG_1"] "h01Mh11ah21vh31Hp;1p;5g003Bj10Tg00a^j13Tg00b<j12Tg00b_j14Tg00G2j11Tg02:=j55Tg008<#0#0#0R0#0#0#0#3#2%30#2#4[R0g00[?R1g006of2R2f1R3g00_O#1#1#1#1f0R4D5P4W3X21X11X00P2P3P4O3X21W1W0o"). Qed.
Lemma statics_facts L C M : as0_layout L C -> asan_statics RSEGS C M ->
  L5.img_clear M 0x132000 0x13a000 /\ L5.u64_at RSEGS M 0x1419f8 SB /\ L5.u32_at RSEGS M 0x141a00 1
  /\ L5.u64_at RSEGS M 0x13b1c8 0x12b88c /\ L5.u64_at RSEGS M 0x13b158 0x112324.
Proof.
intros LY (G & CS). rewrite (aly_got_lo L C LY), (aly_got_hi L C LY) in G. rewrite Forall_forall in CS.
pose proof (aly_cells L C LY) as IC.
split. exact G.
split. exact (CS _ (IC _ (or_introl eq_refl))).
split. exact (CS _ (IC _ (or_intror (or_introl eq_refl)))).
split. exact (CS _ (IC _ (or_intror (or_intror (or_introl eq_refl))))). exact (CS _ (IC _ (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
Qed.
End SCFG_1.
End L5A.
