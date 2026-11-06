(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBReset1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepAB0.PMKB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0Aw"; "0B"; "0B1"; "0B2"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"]; ["2I"; "2and"; "2eq"; "2not"; "3le"; "4map"; "5Z"; "0FF"; "0HI"; "0L"; "0LB"; "0LB1"; "0LB2"; "0LK"; "6fetch_word"; "6is_ecall"]; ["7decode_any"; "8ALU_SRA"; "8ShiftImm"; "8instr"; "9bv_eqb"; "9bvmap"; "0M"; "0M'"; "0M1"; "0M2"; "0M3"; "0M5"; "0R"; ":msteps"; ";credit"; "<aacc"]; ["<aclient"; "<asan_layout"; "<asan_run"; "<fframe"; "<ri_inv"; "<shadow_zero"; "<vml"; "=defined"; "=range"; "=u32_at"; "=u8_at"; ">ADDR_B"; "?CHUNK"; "?p_b"; "?p_k"; "?p_src"]; ["?p_stk"; "?p_tb"; "?parser_at"; "?ps_root"; "?pst"; "?pstate"; "?sr_qc"; "?vec_at"; "?vstr_at"; "@agA"; "@agsh"; "AaccA"; "AannA"; "Apst_reset"; "Bwapp"; "CFPState"]; ["Cgetr"; "Cmkst"; "Cregupd"; "Cseg_rom"; "Cv_srai"; "Dek"; "Eloaded_segments"; "FIn"; "Gadd"; "Gdiv"; "Gle"; "Glt"; "Gmodulo"; "Gmul"; "Gpow"; "0V"]; ["0W"; "0a"; "0ar"; "0cr"; "0d"; "0fx"; "0g"; "0l"; "0l1"; "0l2"; "0lo"; "0m"; "0m1"; "0m2"; "0n"; "0ois"]; ["0op"; "0pc"; "0q"; "0rd"; "0rs"; "0s"; "0scr"; "0sh"; "0sp"; "HNoDup"; "Helem_of"; "Hlist_elem_of"; "IBV"; "IZ_to_bv"; "Ibv"; "Ibv_unsigned"]; ["0x"; "0y"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBRS1.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Lemma srai_to : ltac2:(TCodec.tc2 tcn__PmBReset1 "S<'R?&Q5y5'SNyR0%211%5241'=y8%611%311p061'FyQ0%;11%<1=y6%>11'B%<15&N&RF&SMr5%22D1%5241(4r4%22>1%;3:41'6&O%119(8%@3421'?'Q3%221I%O11&Q0r6%211(>(Q2(Q1r3%342GC1+4%64<Q421%G2<1%Q03<91&Q4(SLz(@%33QE21%53QF@1%Q73K1H&RJr9%2271&RK&RHr:%221A&RN+2+R0%3221%8251'Q=&RAr>r=r;%QE2R71r<&RC%11QI%8576431&RB&RD&R@r8%22;1&SOr7%22R71%7241%93@N1%L2@Q;%R52RG1%E5D31@>%G3R8>1p0I1p0Q31p0Q71p0Q?1p0R01p0R61pW@RC1pW:RF1pW8RG1pV2RI1pW4RL1pR>RN1pRJS41pV<S;1").
Proof. intros fx R M pc W rd rs sh.
intros HF HE HD HZ H0 H1. eapply mst_step; [reflexivity| | apply mst_refl].
rewrite (step_srai RSEGS R (Z_to_bv 64 pc) M (seg_rom RSEGS) W rd rs sh HF HE HD). rewrite HZ.
f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
Qed.
Lemma v_srai5_small : ltac2:(TCodec.tc2 tcn__PmBReset1 "N'F'A&RJzr1%3221&RK&RN+2+QO%3221%5271%;271'B'SNyR0%211&RD&SMr2%2251+5%5221&RI+Q0%2261%82;1%>3;51p0@1pV:M1").
Proof. intros d.
intros Hd. unfold v_srai. f_equal.
assert (S1 : bv_signed (Z_to_bv 64 d) = d).
{ unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_half_modulus 64) with (2 ^ 63). rewrite (Z.mod_small d) by lia. rewrite (Z.mod_small (d + 2 ^ 63)) by lia. lia. }
rewrite S1. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma elem_of_In : ltac2:(TCodec.tc2 tcn__PmBReset1 "?'F';%112&RGr2r1%33621&SJ'SK%119r3%45;9217p061pV@;1pX2>1").
Proof. intros x l. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma fst_neq_app : ltac2:(TCodec.tc2 tcn__PmBReset1 "Q5';'?'F%2211%411'SI&E&9%1266&5r6r5%33921%74:;51%92<1&RG(>r4%24@@71r7%53A21r3%64DD51%83D14&C'B%13H7?%311p051p091p0@1pVLM1p8N1pVJO1p6Q01pVDO1pVBQ01").
Proof. intros l1 l2 B1 m1 B2 m2.
induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
destruct H1 as [->|H1].
- cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_In. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
- apply IH; assumption.
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LYa : L5A.as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBReset1 "R4';'?'F%2211%411&QC%611&Q>'SNyR0%211'=y8%511%311p051&QF&QDvH&5r=r<%33C21r;r:r9r8r7r6%<8;7654321&RG(>r5%24OO51r>%53Q021'A&RJ%12;6&RK&RH%12>=%32:1%7251&C&Q@vIvS2r?r4%57432@B1F%711p091p0B1p0I1pW>QE1pWBQF1pV4QG1pVHQH1p4QI1pV0Q<1pR>Q>1p2QJ1pV8QH1pQLQJ1pQ@QK1pQJQN1pQHQO1")) (only parsing).
Variable LB1 : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable LB2 : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable V : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SECT) 10%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SECT) 11%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SECT) 12%nat 0%nat).
Lemma own_not_aclient : ltac:(sec_stmt2 constr:(SECT) 13%nat 0%nat).
Proof.
intros HH Hin Ha Hc.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & _ & ND & _).
assert (INB : In (B, m) (LB1 ++ LB2)) by (apply in_or_app; left; exact Hin).
pose proof (WB _ INB) as ((R0 & R1 & R2 & R3 & R4 & R5) & _ & _ & _ & AP & FA & _). cbn [fst snd] in *.
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in R5.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as ((B2 & m2) & H2 & X). cbn [fst snd] in X.
assert (NE : B <> B2) by exact (fst_neq_app LB1 LB2 B m B2 m2 ND Hin H2).
pose proof (L5C.blocks_apart_in B m _ B2 m2 AP (L5C.in_lb_remove_neq B B2 m2 _ (in_or_app _ _ _ (or_intror H2)) (fun E => NE (eq_sym E)))). lia.
- lia.
- destruct R1 as [X|X]; lia.
- destruct Hc as (f & Hf & X & _). destruct (FA f (in_or_app _ _ _ (or_introl Hf))); lia.
- unfold in_shadow_of, S, SB in Hc. lia.
- destruct Hc as (f & Hf & X). destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in FSAPP.
unfold in_shadow_of, S, SB in X. unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *. lia.
- destruct Hc as ((B2 & m2) & H2 & X). pose proof (WB _ (in_or_app _ _ _ (or_intror H2))) as ((Z0 & Z1 & Z2 & Z3 & Z4 & Z5) & _).
cbn [fst snd] in *. unfold app_mem in Z5. unfold in_shadow_of, S, SB in X. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.
End S.
Lemma ri_swap12 : ltac2:(TCodec.tc2 tcn__PmBReset1 "Q>'?'F%2211';%112&QC%311&Q>'SNyR0%211'=y8%511%311p051&QF&QDvH(7r9r8r7%43E21%53F41r6r5r4r3r2r1%>8=7654321r:%>3O1<%?3Q0>1%B8A1=:9876p051pV0E1pR>G1p2Q31pV8Q11pQLQ31pQ@Q41pV@Q71pX4Q:1pX2Q;1").
Proof. intros x y l FF LK cr Aw M V.
intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
apply (HAJ.aior_perm _ _ _ _ _ HIok _ (y :: x :: l) FF FF LK cr Aw M V HH).
- intros b. cbn [In]. tauto.
- cbn [map] in *. assert (P : y.1 :: x.1 :: map fst l ≡ₚ x.1 :: y.1 :: map fst l) by apply perm_swap. rewrite P. exact ND.
- intros f. tauto.
- rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
End WithHeap.
Lemma acc_of_shadow_zero : ltac2:(TCodec.tc2 tcn__PmBReset1 "Q:'SNyR0%211'=y8%511%311p051'F&QEr5r4r3%43321'B&RL+8%2271z%53;21&RJr6%221;&RH%12>=r7&RM%12;6%5231%9251&Q?r9%231;Fp041p0<1p0@1p0G1pVNM1pV4N1pV>O1pVFQ01pR>Q21").
Proof. intros M lo g a n.
intros SZ Hlo H1 H2 x Hx. left.
assert (E : S x = S lo + (x - lo) / 8).
{ unfold S. assert (L8 : lo = (lo / 8) * 8) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
replace x with ((x - lo) + (lo / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
rewrite E. apply SZ. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma agA_trans : ltac2:(TCodec.tc2 tcn__PmBReset1 "J'SNyR0%211'=y8%511%311p051'F&R9r5r4r2r1%544321r3%746514r7%941873p031p061pVN=1pV4>1pRF@1pRDA1pRBB1").
Proof. intros M1 M2 M3 a n.
intros [G1 S1] [G2 S2]. split.
- intros i Hi. rewrite (G2 i Hi). apply G1. exact Hi.
- intros x Hx. rewrite (S2 x Hx). apply S1. exact Hx.
Qed.
Lemma agsh_blk : ltac2:(TCodec.tc2 tcn__PmBReset1 "R0'QA'QB';'?'F%2211%411&QC%611&QH%811'SNyR0%211'=y8%511%311p051&REr;r:r9r8r7r6r5r4r3%:9987654321&R>%116&RG(>%14NN76%33N1?&RJz%221<&RH%12?>&RN+2+Q?%3221%9251&R:%14IHGFp031p0;1p0?1p0D1p0G1pVHQA1pW6QB1pR@Q51pR>Q61pV2Q?1pW>QF1pWBQG1pQ@QD1pQFQG1pV6QM1pQDQO1").
Proof. intros L ar LB FF sp scr W M M' q m.
intros E WAPP Hin Hq Hqm x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
apply E. split; [lia|]. split.
- unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
- apply (PMKB.wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBReset1 "T3'SNyR0%211'=y8%511%311p051'F'R4&R2&RF&QK&R;&R<r5r3r2r1%9887654321'Du1&:'R5&R0%118%4231%7261&RJz%221?&RHr6+\0%3221&RN+2+R0%3221%;251&R6&QO%11K%311%@2?1%41=%611&QL%A221%E21;&R9r;r:r9+8%544321r<+@%K261+Z0%:44921&R:r=%2417<Nr>%H1=%J11%A4351D&QG%1357Q4&QJr?%Q928B+1%44QO321r@+9%Q>261%84R331QA&QIrA+<%QC271%44R831QF&R8rB+Z@%QH271&R1&R=%11C%311%85RAR?751&R7rC+[8%R12;1&QM%11G&QN%11I(7&R3(<%11RA%43RB31%=8RORMRL<:861rD%C1L%S38S2S1S0RO2?H1p041p0C1p0M1p0Q31p0Q81p0Q>1p0QA1p0QF1p0QJ1p0R01p0R71p0R=1p0RC1p0RM1p0S11p0S:1pW<SE1pW0SG1pW2SH1pRHSJ1pR>SK1")) (only parsing).
Variables (M M5 : word -> option byte).
Variable op : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variables (s : PM.pst).
Lemma reset_postA : ltac:(sec_stmt2 constr:(SECT) 5%nat 0%nat).
Proof.
intros (H0 & D & C0 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) LEN Ho Ho' Hq Hq'
AG0 AG16 SH AGQ D5 C8 C9 C12 TB5 VEC5.
destruct AG0 as [G0 _]. destruct AG16 as [G16 S16].
unfold PM.parser_at. cbn [PMSPA.pst_reset PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
split; [apply (L5C.u64_at_agree RSEGS M M5); [exact G0|lia|lia|exact H0]|].
split; [exact D5|].
split; [apply (PMFA.accA_agree M M5); [apply (PMFA.agsh_sub M M5 op 384 op 24 SH); lia| exact C0]|].
split; [exact C8|]. split; [exact C9|]. split; [exact C12|].
split; [apply (L5C.u8_at_agree RSEGS M M5); [apply (L5C.agree_on_sub M M5 (op + 16) 320 (op + 16) 1 G16); lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree RSEGS M M5); [apply (L5C.agree_on_sub M M5 (op + 16) 320 (op + 20) 4 G16); lia|lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M M5 (op + 32)); [lia|lia| apply (PMFA.agA_sub M M5 (op + 16) 320); [split; assumption|lia|lia]| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M5 (op + 24) ois (ois + 16) (PM.p_src s)); [lia|lia|exact Hq|exact Hq'
| apply (PMFA.agA_sub M M5 (op + 16) 320); [split; assumption|lia|lia]| exact AGQ| exact SRC]|].
split; [apply (PMF.u32_at_agree RSEGS M M5); [apply (L5C.agree_on_sub M M5 (op + 16) 320 (op + 320) 4 G16); lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M5); [apply (L5C.agree_on_sub M M5 (op + 16) 320 (op + 328) 8 G16); lia|lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M5); [apply (PMFA.agsh_sub M M5 op 384 (op + 320) 64 SH); lia| exact C320]|].
split; [exact TB5|]. split; [exact VEC5|].
split; [right; reflexivity|]. split; [left; reflexivity|]. unfold PM.MAX_DEPTH; lia.
Qed.
End S.
End PMBRS1.
