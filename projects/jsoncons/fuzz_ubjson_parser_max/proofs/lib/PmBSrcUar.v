(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA
HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmBSrcKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBSrcUar () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBSrcUar.PMBSU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepAB0.PMKB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2I"; "2and"; "2eq"; "2not"]; ["2or"; "3lt"; "4Z"; "0E"; "0FF"; "0H"; "0L"; "0LB"; "5fetch_word"; "5is_ecall"; "6decode_any"; "7ALU_AND"; "7OpImm"; "7instr"; "8bv_eqb"; "8bvmap"]; ["0M"; "0M1"; "0M1'"; "0M2"; "0M3"; "0R"; "0R'"; "9mrestrict"; ":msteps"; ";ff_addr"; ";ff_bytes"; ";ff_class"; ";fframe"; "<u64_at"; "=ocell13"; "=own13"]; [">ADDR_B"; "?CHUNK"; "?SRC"; "?p_src"; "?parser_at"; "?parser_own"; "?pst"; "?sr_qc"; "@accA"; "@annA"; "@frame_okA"; "@o_p"; "@o_src"; "@with_src"; "Awapp"; "BFPState"]; ["Bgetr"; "Bmkst"; "Bregupd"; "Bseg_rom"; "Bv_andi"; "Cmem_grows"; "Dek"; "Eloaded_segments"; "FIn"; "Fincl"; "Gadd"; "Gland"; "Gle"; "Glt"; "Gmodulo"; "Gof_nat"]; ["Gpow"; "Gsub"; "0W"; "0a"; "0ar"; "0b"; "0de'"; "0f"; "0fb"; "0fx"; "0imm"; "0j"; "0m"; "0ois"; "0pc"; "0q"]; ["0rd"; "0rem'"; "0rs"; "0s"; "0scr"; "0sp"; "0sp0"; "HBV"; "HZ_to_bv"; "Hbv"; "Hbv_signed"; "0x"]]).
Module PMBSU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Definition own13 (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
/\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
/\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
/\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
/\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
/\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26)))
/\ L5.u64_at RSEGS M (E - 104) (bv_unsigned (getr R (reg 27))).
Definition ocell13 (E : Z) (a : Z) : Prop := E - 104 <= a < E.
Lemma own13_agree : ltac2:(TCodec.tc2 tcn__PmBSrcUar "QD'B&Oy5'S9yR0%211%5241'8y8%611%311p061pVH72&R<z&RAr4+S8%3221%6251r5&R@+2+R0%3221%<251&Q?r6%2318<&Q>r8r1%3221'>&S8r2%22Q01%:11r7%113%73N31p091pU8Q:1%A3=5Gp021p0A1p0E1p0L1pR6Q41pR4Q61pR<Q<1pQ8QC1").
Proof. intros E R M1 M1'.
intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) AG. unfold own13, ocell13 in *.
repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.
Lemma own13_vis : ltac2:(TCodec.tc2 tcn__PmBSrcUar "QJ'B&Oy5'S9yR0%211%5241'1pVH31'8y8%811%311p081'=&R<&RAr5+S8%3221r1%6221&R=%1236%:231'>r4&S8r2%22I1%411(3%73I21p091pU8Q21z%E21Ar6&R@+2+R0%3221%K251&Q?r7%2318Cr8&Q7%12;O%63351p051p091p0@1p0C1pR2Q91pQ<Q?1pR<QB1pQ8QI1").
Proof. intros E R H M.
intros HV H0 H1 O. apply (own13_agree E R M (mrestrict H M) H0 H1 O). intros a Ha. unfold ocell13 in Ha.
apply mrestrict_visible. apply HV. exact Ha.
Qed.
Lemma land_m32 : ltac2:(TCodec.tc2 tcn__PmBSrcUar "J'B'=&R<zr1%3221&R=&R@+2+R0%3221%5271%;271'>&R;r2&RA+Q0%2281%5241&R>%1264%6271%:3G41p0<1pVHI1").
Proof. intros x.
intros Hx. replace (2 ^ 64 - 32) with (Z.land (Z.ones 64) (Z.lnot (Z.ones 5))) by reflexivity.
rewrite Z.land_assoc. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32. pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.
Lemma andi_m32 : ltac2:(TCodec.tc2 tcn__PmBSrcUar "Q9'B'S9y<%211'=&R<zr2%3221&R=&R@+2+R0%3221%5271%;271'>&S:%12@;-Q0%43D21yR0%E11&R4&S8r4%2251r3%;2J1%6231&RA&R>+Q0%2281%4291%;2>1%D3>71p0A1p0G1pUFQ41pVHQ81").
Proof. intros x imm.
intros Hx Hi. unfold v_andi. rewrite Hi. rewrite L5.unsigned_lit by lia.
replace (bv_wrap 64 (-32)) with (2 ^ 64 - 32) by reflexivity. rewrite land_m32 by exact Hx. reflexivity.
Qed.
Lemma andi_to : ltac2:(TCodec.tc2 tcn__PmBSrcUar "S<'QO&Oy5'S9yR0%211%5241'8y8%611%311p061'ByQ0%;11%<1=y<%>11'>%<15&H&R7&S8r5%22D1%5241(0r4%22>1%;3:41'1&I%119(3%@3421':'M%221I%O11&Jr6%211(9(L(Kr3%342GC1+4%64<Q421%G2<1%Q03<91&N(S7z(<%33QE21%53QF@1%Q73K1H&R<r9%2271&R=&R:r:%221A&R@+2+R0%3221%8251'Q8&R1r>r=r;%QE2R71r<&R3%11QI%8576431&R2&R4&R0r8%22;1&S:r7%22R71%7241%93@N1%L2@Q;%R52RG1%E5D31@>%G3R8>1p0I1p0Q31p0Q71p0Q?1p0R01p0R61pUFRC1pV6RF1pV2RG1pU6RI1pUNRL1pR2RN1pR<S41pUDS;1").
Proof. intros fx R M pc W rd rs imm.
intros HF HE HD HZ H0 H1. eapply mst_step; [reflexivity| | apply mst_refl].
rewrite (step_andi RSEGS R (Z_to_bv 64 pc) M (seg_rom RSEGS) W rd rs imm HF HE HD). rewrite HZ.
f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
Qed.
Lemma andi_sp : ltac2:(TCodec.tc2 tcn__PmBSrcUar "RA&Oy5'S9yR0%211%5241'By<%611'=&R<zr2%3221&R=&R@+2+R0%3221%5271%;271'>&S:%12@;-Q0%43C21&R0r5&S8&R?u2%211%42O1%7261r4%72Q01%?3Q031&R2r6(S7(<%23Q8I1&R4%A252%F2Q5:%3221%93851r1%F21@&RA&R>+Q0%22>1%42?1%J2QC1%Q23QC71'6&?%Q532;L%211&AuQ0%22QB1r3%Q311%Q52R01%Q82Q01r:%Q:213%Q@3R131p081p0<1pUH@1%R02B1tR>R5L1p0Q71p0QC1p0QI1pUFR61pV>R91pR<R;1").
Proof. intros R sp0 imm.
intros Hs Hi G R'. split.
- unfold R'. rewrite <- L5K.rl2. rewrite getr_same by (intros X; discriminate X). rewrite <- L5K.rl2 in G. rewrite G.
apply andi_m32; assumption.
- intros j Hj Hl. unfold R'. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (2%bv : bv 5)) with 2 in E.
rewrite Z.mod_small in E by lia. lia.
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma src_piece_parserB : ltac2:(TCodec.tc2 tcn__PmBSrcUar "UK'5':'B%2211%411&Q<%611'QF'S9yR0%211'8y8%511%311p051&R8r1r;%33>21'=&R<z&Q9r2%211%5241&R:&Q:&Q;%116%311%5271&R@+2+Q?%3221%@251%B2<1p0D1pU@Q31r=%J3Q7I1&4%13Q:Q:D%H2G1&;%13Q=Q=G%E241%L21=%N251p091pU<QA1(9%14QDQDNQ5r?%Q83QE21'@r3%Q021Q3&QL&Q@r>%3221%Q;251+Y8%Q7231%Q>219%;241p0=1pUJR41pV0R51&QN(2r<%?2>1+X0%QB221+Q8%J4R=R=21(7%11R>%93R?31%;11&QJ%12GQ<&R9&QE%11>r@%43RG21&R6vFvRDrAr:r9%Q52Q4Q:%R721F%Q>4S1S11E%K3S11Cr8r7%<9;:9>87321&R5%1294&QD&R7&QH&QI&QK%12QBA%685QC43A1GQI&Q=rB%QG2QF1+X8%RJ221&QG&QC%11O%311%94?K51rC%R02QO1+X@%S3221&QA%?4ES>21rD%R62R51+XH%S9221%D4JQK1Q7rE%R;2R:1+Y0%S>221%I4OS11Q<%D1:%F11%SH21B%SI2SHC%SD29>rF%J11%L11%SH21D%SO251rI%Q82RI1rH&QMrG(QB%Q412%Q611%331=G%6251%QE8QDS2QCQBR1981p0<1p0C1p0E1p0I1p0O1p0Q51p0Q<1p0QG1p0QO1p0R21p0R@1p0RF1p0RI1p0S61p0SJ1p0T71pR:U11pR8U21pV:U@1pV<UA1pV4UB1pU>UC1pV8U?1pULUE1pUBUF1pQ:UC1pQ@UF1").
Proof. intros LB FF fb ois s de' rem' sp scr M2 M3.
intros FRB BRB APT WS FOK INC EK MG PA C1 C2 C3 C4 Q1 Q2 Q3.
unfold PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_p PMB.AD ADDR_A] in *.
pose proof FOK as ((rs & Hfb) & F1024).
assert (OUTO : forall i, ~ (fb + 464 + 24 + 256 <= i < fb + 464 + 24 + 296) -> L5.outside [(fb + 464 + 24 + 256, 40)] i).
{ intros i N r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
assert (OUTB : forall q m, In (q, m) LB -> forall i, q <= i < q + m -> L5.outside [(fb + 464 + 24 + 256, 40)] i).
{ intros q m Hq i Hi. apply OUTO. destruct (APT q m Hq) as [X|X]; lia. }
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & PVEC & _).
assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (apply INC; unfold PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LB) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
apply (PMBSK.parser_src_fieldsA M2 M3 (fb + 464) ois s de' rem' PA).
- destruct (FRB (fb, 4, rs) Hfb). unfold ff_addr in *. cbn in *. lia.
- destruct (FRB (fb, 4, rs) Hfb). unfold ff_addr, ff_class, ff_bytes in *. cbn in *. lia.
- apply (PMKB.agA_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464) 280 ltac:(apply (PMBSK.aobj_fb FF fb); [exact FOK| lia| lia])). intros i Hi. apply OUTO. lia.
- apply (PMKB.agA_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464 + 320) 64 ltac:(apply (PMBSK.aobj_fb FF fb); [exact FOK| lia| lia])). intros i Hi. apply OUTO. lia.
- apply (PMKB.agsh_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464 + 280) 40 ltac:(apply (PMBSK.aobj_fb FF fb); [exact FOK| lia| lia])).
- destruct (BRB _ QIN). cbn [fst snd] in *. lia.
- destruct (BRB _ QIN). cbn [fst snd] in *. lia.
- apply (PMKB.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ QIN). apply OUTB. exact QIN.
- destruct (BRB _ VIN). cbn [fst snd] in *. lia.
- destruct (BRB _ VIN). cbn [fst snd] in *. lia.
- apply (PMKB.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ VIN). apply OUTB. exact VIN.
- intros c0 n0 p0 E.
assert (TIN : In (p0, c0) LB) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; rewrite E; cbn; right; right; left; reflexivity).
apply (PMKB.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ TIN). apply OUTB. exact TIN.
- exact MG.
- replace (fb + 464 + 288) with (fb + 464 + 24 + 264) by lia. exact C1.
- replace (fb + 464 + 296) with (fb + 464 + 24 + 272) by lia. exact C2.
- replace (fb + 464 + 304) with (fb + 464 + 24 + 280) by lia. exact C3.
- replace (fb + 464 + 312) with (fb + 464 + 24 + 288) by lia. exact C4.
- exact Q1. - exact Q2. - exact Q3.
Qed.
End WithHeap.
End PMBSU.
