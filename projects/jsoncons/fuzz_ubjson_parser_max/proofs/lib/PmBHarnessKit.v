(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Core L5DefsAB0 L5CoreAB0 L5StepARB0 HeapIfaceAJx
PmLayout PmLayoutA PmStatics PmStaticsA PmSpecsA PmSpecsAb PmModelFactsA PmStepAB0 L5ADetailHRB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarnessKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessKit.PMHAK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Ax"; "0C"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"]; ["2not"; "2or"; "3Z"; "0F"; "0FF"; "0FFc"; "0FFx"; "0HI"; "0HIok"; "0Hd"; "0L"; "0LB"; "0LBc"; "0LBx"; "0LKx"; "4SpuriousCfg"]; ["0M"; "0M'"; "0M1"; "0M2"; "0Mv"; "0Mx"; "0P"; "5credit"; "6BIGSHADOW_HI"; "6BIGSHADOW_LO"; "6S"; "6SB"; "6ar_sptop"; "6asan_iface"; "6asan_layout"; "6asan_run"]; ["6asan_statics_cells"; "6ff_addr"; "6ff_bytes"; "6ff_class"; "6fframe"; "6fframes_apart"; "6hl_img_hi"; "6hl_img_lo"; "6ri_inv"; "6shadow_zero"; "6vml"; "7asan_iface_okR"; "8agree_on"; "9outside"; "9range"; "9u32_at"]; ["9u64_at"; "9u8_at"; ":avis"; ";bcell"; ";ecell"; ";far"; ";lcell"; ";scell"; ";statc"; "<AADDR_B"; "<ADDR_B"; "=agA"; ">ST"; ">loc_ok"; ">st"; ">st_err"]; [">st_loc"; ">st_sys"; ">sys_ok"; "?base_okA"; "?err_okA"; "?ls_okA"; "@ahpres"; "Aloaded_segments"; "BIn"; "Cadd"; "Cdiv"; "Cle"; "Clt"; "Cmodulo"; "Cpow"; "Csub"]; ["0Vx"; "0W"; "0W1"; "0W2"; "0Wc"; "0Wp"; "0a"; "0a'"; "0ar"; "0b"; "0c"; "0crx"; "0e'"; "0f"; "0g"; "0j"]; ["0n"; "0n'"; "0o"; "0p"; "0q"; "0r"; "0rs"; "0scfg"; "0scr"; "0scrc"; "0shi"; "0slo"; "0sp"; "0spc"; "DZ_to_bv"; "Dbv"]; ["0v"; "0w"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Module PMHAK.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMB.AD.
Abbreviation AAD := PMB.AAD.
Definition bcell (a : Z) : Prop := (65536 <= a < 0x136000) \/ (0x690b00 <= a < 0x690b08) \/ (0x690d53 <= a < 0x690d54) \/ (0x690e30 <= a < 0x690e34).
Definition lcell (a : Z) : Prop := (0x66f2f2 <= a < 0x66fa30) \/ (0x670158 <= a < 0x6701b0).
Definition scell (a : Z) : Prop := 0x66f2f0 <= a < 0x66f2f2.
Definition ecell (a : Z) : Prop := (0x66f0c0 <= a < 0x66f0c2) \/ (0x690b10 <= a < 0x690d30).
Section Keep.
Variables M M' : word -> option byte.
Lemma base_keep : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "Q9'B'>&RKzr1%3221&RL&RN+2+R0%3221%5271%;271&R3r2%211'?'9'SOy8%211%411vQ1&SNyR0r3%3221%511vQ0%113%>3931p0@1p0D1pV>Q11&RC&RG&R:%33219%4332@p021p071").
Proof.
intros AG BO. unfold PMSTA.base_okA, L5.img_clear in *. cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMB.AD ADDR_A] in *.
destruct BO as (RO0 & (can & Hcan & CAN) & NL & LL).
split; [|split; [|split]].
- intros i Hi. rewrite AG; [apply RO0; exact Hi| lia| left; lia].
- exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| right; left; lia]|lia|lia| exact CAN].
- apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| right; right; left; lia]|lia|lia| exact NL].
- unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat 6884912); [exact LL|lia|cbn; lia|].
intros i Hi. cbn in Hi. apply AG; [lia| right; right; right; lia].
Qed.
Lemma loc_keep : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "Q;'3'B'>&RKzr1%3221&RL&RN+2+R0%3221%5271%;271&R6r2%211'?'9'SOy8%211%411vQ1&SNyR0r3%3221%511vQ0%113%>3931p0@1p0D1pV>Q11&R=&RG&R:%34219G%4432@=p021p071pVDQ:1").
Proof. intros b.
intros AG LOC. unfold PMST.loc_ok in *. cbn [pa_glocale pa_classic_imp pa_loc_foot PMB.AD ADDR_A] in *. destruct b.
- destruct LOC as (G & P). split.
+ apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| left; lia]|lia|lia| exact G].
+ apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| left; lia]|lia|lia| exact P].
- intros iv Hin. pose proof (LOC iv Hin) as X. intros i Hi. rewrite AG; [apply X; exact Hi| |].
+ destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hi; lia.
+ destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hi; unfold lcell; lia.
Qed.
Lemma sys_keep : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "Q;'3'B'>&RKzr1%3221&RL&RN+2+R0%3221%5271%;271&R7r2%211'?'9'SOy8%211%411vQ1&SNyR0r3%3221%511vQ0%113%>3931p0@1p0D1pV>Q11&RB&RG&R:%34219G%4432@=p021p071pVDQ:1").
Proof. intros b.
intros AG SYS. unfold PMST.sys_ok in *. cbn [pa_syscat_guard PMB.AD ADDR_A] in *. destruct b.
- apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| unfold scell; lia]|lia|lia| exact SYS].
- intros i Hi. rewrite AG; [apply SYS; exact Hi| lia| unfold scell; lia].
Qed.
Lemma err_keep : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "Q<'3'B'>&RKzr1%3221&RL&RN+2+R0%3221%5271%;271&R4r2%211'?'9'SOy8%211%411vQ1&SNyR0r3%3221%511vQ0%113%>3931p0@1p0D1pV>Q11&RD&RG&R:&R9%45321:H%55432A>p021p081pVDQ;1").
Proof. intros b.
intros AG (ERG & ATX). split.
- cbn [pa_errcat_guard PMB.AD ADDR_A] in *. destruct b.
+ apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; [lia| left; lia]|lia|lia| exact ERG].
+ intros i Hi. rewrite AG; [apply ERG; exact Hi| lia| left; lia].
- apply (PMSTA.atexit_stA_agree RSEGS AD AAD PMB.addrs_wf_A M M' b); [|exact ATX].
intros i Hi. cbn [pa_atexit PMB.AD ADDR_A] in Hi. apply AG; [lia| right; lia].
Qed.
End Keep.
Definition statc (a : Z) : Prop := bcell a \/ lcell a \/ scell a \/ ecell a.
Lemma statc_range : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "?'B&R8r1%211'>&RK+RPP0r2%3221&RL+VbSaD%2241%8241p0:1pV>>1").
Proof. intros a. unfold statc, bcell, lcell, scell, ecell. lia. Qed.
Lemma ls_agree : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "Q@'R>'SOyR0%211'9y8%511%311p051'B'>&RKzr1%3221&RL&RN+2+R0%3221%5271%;271&R8r2%211'?r4&SNr3%22K1%411r5%113%83J31p0:1p0>1pV>K1&RE&RG&R:&R9%45321?=%55432;>p021p081pR4Q51pR2Q61pVNQ?1").
Proof. intros g M M'.
intros AG (B & LO & SY & ER). split; [|split; [|split]].
- apply (base_keep M M'); [intros a Ha X; apply AG; [exact Ha| left; exact X]| exact B].
- apply (loc_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; left; exact X]| exact LO].
- apply (sys_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; left; exact X]| exact SY].
- apply (err_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; right; exact X]| exact ER].
Qed.
Lemma ls_piece : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "QO'R>'SOyR0%211'9y8%511%311p051'B!p021'>&RKzr1%3221&RL&RN+2+R0%3221%5271%;271&@r3r2%211%411'?r5&SN%12N7%311r6%113%73M31p091p0?1pV>N1%?1I'A+RPP0%J2A1+VbSaD%Q021C%5231p071pV>Q71&RE&RG&R:&R9%45321CGr7%655431Ip031p091p0C1pV<Q@1pR4QD1pR2QE1pVNQN1").
Proof. intros g M M' Wp. intros FR WP. apply ls_agree. intros a Ha X. apply FR; [exact Ha|]. intros Y. apply WP in Y. apply statc_range in X. lia. Qed.
Definition far (W : list L5.range) : Prop := forall r, In r W -> fst r + snd r <= 65536 \/ 0x690e34 <= fst r.
Lemma far_outside : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "A'7&QN%211'B&R5r2%211&R8%113&QMr4r3%3221p051p081pV><1pV4>1").
Proof. intros W a. intros FW X r Hr. apply statc_range in X. specialize (FW r Hr). unfold L5.in_rng. lia. Qed.
Lemma far_nil : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "5&R5(8&QN%211%411").
Proof. intros r []. Qed.
Lemma far_cons : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "O';'B%2211'7&QN%211'A&RK&RI&6r2%23::1&<%13<<3%6231+RPP0%9221+VbSaD%;217%=231&R5%11;(4r4r3%33G21%611p061p091pV4H1pW<L1").
Proof. intros r W. intros H FW r' [<-|Hr]; [exact H| exact (FW r' Hr)]. Qed.
Lemma far_app : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "?'7&QN%211&R5r2%211&2r4r3%33821%711p061p071pV8;1pV6<1").
Proof. intros W1 W2. intros F1 F2 r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (F1 r Hr)| exact (F2 r Hr)]. Qed.
Section Client.
Variables (L : asan_layout) (C : asan_statics_cells).
Hypothesis LY : PMB.layout L C.
Let LYa := PMB.ly_as0 L C LY.
Lemma stat_client (ar : asan_run) {BS ST} LB FF sp scr a :
(forall x, ST x -> hl_rt_static L x) -> (bcell a \/ lcell a \/ scell a \/ ecell a) -> aclient_g BS ST L ar LB FF sp scr a.
Proof.
intros HST Ha. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split.
- unfold bcell, lcell, scell, ecell in Ha. lia.
- intros X. apply HST in X. destruct Ha as [[Y|Y]|Y].
+ pose proof (L5A.aly_static_lo L C LYa a X). lia.
+ refine (PMB.ly_static L C LY a _ X). unfold PMST.dep. destruct Y as [Y|[Y|Y]].
* right; left. cbn [pa_canary PMB.AD ADDR_A]. lia.
* right; right. exists (0x690d53, 0x690d54). split; [cbn; tauto| cbn [fst snd]; lia].
* right; right. exists (0x690e30, 0x690e34). split; [cbn; tauto| cbn [fst snd]; lia].
+ refine (PMB.ly_static L C LY a _ X). destruct Y as [[Y|Y]|[Y|Y]].
* apply (PMST.in_foot_loc AD (0x66f2f2, 0x66fa30)); [cbn; tauto| cbn [fst snd]; lia].
* apply (PMST.in_foot_loc AD (0x670158, 0x6701b0)); [cbn; tauto| cbn [fst snd]; lia].
* apply PMST.in_foot_sysg. cbn [pa_syscat_guard PMB.AD ADDR_A]. unfold scell in Y. lia.
* destruct Y as [Y|Y].
-- apply PMST.in_foot_errg. cbn [pa_errcat_guard PMB.AD ADDR_A]. lia.
-- apply PMST.in_foot_atexit. cbn [pa_atexit PMB.AD ADDR_A]. lia.
Qed.
Lemma ls_ahpres_g : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "R='B!p021'Q?'7';%1266%311&QD%511&QN%711'SOyR0%211'9y8%511%311p051&RFvJr8r7r6r5r4r3r2r1%:9987654321r;%113&R8%116p031pV>Q41r<%119&QM%12A<p031pV>Q:1'>&RKz%221A&RL&RN+2+R0%3221%52G1%:271r>%11K'?&SN%12Q=O%Q411%Q612%53Q;21p071p0:1pV>R01p0G1p0N1p0Q51pR4QA1pR2QB1pV4QK1pWBR71pWJR81pQ:R01pQHR31pVBR81pR>R:1").
Proof. intros P ar LB FF sp scr W M M'.
intros (AK & _ & _) PS PO a Ha X. apply AK. split; [exact Ha|]. split; [| exact (PO a X)].
apply (stat_client ar LB FF sp scr a (fun x X => X)). exact (PS a X).
Qed.
Lemma ls_ahpres : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "QD'R>'Q?'7';'B%2211%411&QD%611&QN%811'SOyR0%211'9y8%511%311p051&RFvJr8r7r6r5r4r3r2r1%:9987654321&R5%116&RE&RG&R:&R9r;%554321<r<%756541>p031p0:1p0=1pR4I1pR2J1pV4Q31pWBQ:1pWJQ;1pQ:Q81pQHQ;1pVBQA1pVNQC1").
Proof. intros g ar LB FF sp scr W M M'.
intros AH FW. apply ls_agree. apply (ls_ahpres_g statc ar LB FF sp scr W M M' AH (fun a X => X)). intros a X. exact (far_outside W a FW X).
Qed.
Lemma ls_ahpres_loc : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "R9'R>'Q?'7';'B%2211%411&QD%611&QN%811'SOyR0%211'9y8%511%311p051&RFvJr8r7r6r5r4r3r2r1%:9987654321'A&R3%114&R7%116&R4%118%7231%8261&QM%12A=p031pV>Q61&RE&RG&R:&R9r;%554321G&R=(=%2476J1(R<&RAr=%211&R?%113%63831%@5?>=1Q3p091p0=1p0D1p0Q21pR4Q>1pR2Q?1pV4QH1pWBQO1pWJR01pQ:QM1pQHR01pVBR61pVNR81").
Proof. intros g ar LB FF sp scr W M M'.
intros AH FW (B & _ & SY & ER) LO'.
pose proof (ls_ahpres_g (fun a => bcell a \/ scell a \/ ecell a) ar LB FF sp scr W M M' AH) as AG.
specialize (AG ltac:(intros a [X|[X|X]]; unfold statc; tauto) FW).
split; [|split; [|split]]; cbn [PMST.st_loc PMST.st_sys PMST.st_err].
- apply (base_keep M M'); [intros a Ha X; apply AG; [exact Ha| left; exact X]| exact B].
- exact LO'.
- apply (sys_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; left; exact X]| exact SY].
- apply (err_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; exact X]| exact ER].
Qed.
Lemma ls_ahpres_sys : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "R9'R>'Q?'7';'B%2211%411&QD%611&QN%811'SOyR0%211'9y8%511%311p051&RFvJr8r7r6r5r4r3r2r1%:9987654321'A&R3%114&R6%116&R4%118%7231%8261&QM%12A=p031pV>Q61&RE&RG&R:&R9r;%554321G&RB(=%2476J1(R<&R@r=%211&R?%113%63381%@5?>=1Q3p091p0=1p0D1p0Q21pR4Q>1pR2Q?1pV4QH1pWBQO1pWJR01pQ:QM1pQHR01pVBR61pVNR81").
Proof. intros g ar LB FF sp scr W M M'.
intros AH FW (B & LO & _ & ER) SY'.
pose proof (ls_ahpres_g (fun a => bcell a \/ lcell a \/ ecell a) ar LB FF sp scr W M M' AH) as AG.
specialize (AG ltac:(intros a [X|[X|X]]; unfold statc; tauto) FW).
split; [|split; [|split]]; cbn [PMST.st_loc PMST.st_sys PMST.st_err].
- apply (base_keep M M'); [intros a Ha X; apply AG; [exact Ha| left; exact X]| exact B].
- apply (loc_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; left; exact X]| exact LO].
- exact SY'.
- apply (err_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; exact X]| exact ER].
Qed.
Lemma ls_ahpres_err : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "R;'R>'3'Q?'7';'B%2211%411&QD%611&QN%811'SOyR0%211'9y8%511%311p051&RFvJr8r7r6r5r4r3r2r1%:9987654321'A&R3%114&R6%116&R7%118%7231%8261&QM%12A=p031pV>Q61&RE&RG&R:&R9r<%554321G&RD%15654I3(R<&R@r>%211&RA%113r=%73421%@5?>=1Q3p0:1p0=1p0D1p0Q21pR4Q>1pR2Q?1pV4QH1pWBQO1pWJR01pQ:QM1pQHR01pVBR61pVJR81pVNR:1").
Proof. intros g e' ar LB FF sp scr W M M'.
intros AH FW (B & LO & SY & _) ER'.
pose proof (ls_ahpres_g (fun a => bcell a \/ lcell a \/ scell a) ar LB FF sp scr W M M' AH) as AG.
specialize (AG ltac:(intros a [X|[X|X]]; unfold statc; tauto) FW).
split; [|split; [|split]]; cbn [PMST.st_loc PMST.st_sys PMST.st_err].
- apply (base_keep M M'); [intros a Ha X; apply AG; [exact Ha| left; exact X]| exact B].
- apply (loc_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; left; exact X]| exact LO].
- apply (sys_keep M M'); [intros a Ha X; apply AG; [exact Ha| right; right; exact X]| exact SY].
- exact ER'.
Qed.
End Client.
Lemma agA_frame : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "R9'SOyR0%211'9y8%511%311p051'B!p021'>&RKzr1%3221&RL&RN+2+R0%3221%5271%;271&@r5r2%211%411'?r7&SNr3%22O1%411r8%113%83N31p0:1p0@1pV>O1%L2K9&RIr4%221<+Q?%L2K1%Q2231r6%Q421Q2%822I%Q22Q41%Q8231%B1K%N11&Q:%11N%F11%Q211%Q?251p081pX6QD1&R;r9%241M@Q7p041p0C1p0J1p0L1pW2QL1pW6QM1pV<QL1pR4R01pR2R11").
Proof. intros M M' Wp o n.
intros FR Ho Hn H. split.
- intros i Hi. apply FR; [lia| exact (proj1 (H i Hi))].
- intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply FR; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| exact (proj2 (H x Hx))].
Qed.
Section Blk.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (scfg : SpuriousCfg) (HI : asan_iface).
Hypothesis HIok : HAJ.asan_iface_okR L ar C scfg HI.
Lemma blk_agA : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "TB'7';'B%2211%411&QD%611&Q7'SOyR0%211'9y8%511%311p051&QJ!p0@1&QHvGr@r?r>r=r<r;r:%9887654321&RH(:r9%24NN51rA%53O21%Q22Q0Q1+4%74Q3Q361r8%94Q4Q521&2%13Q48D%=3731'?&RM+8%22C1z%53Q>21&RK%123H&RI+QP0%22L1&RN+2+Q?%3221%9251'A&Q8%<21Q5%;2Q6:&Q9%?221%6241&RO&Q<vS8%211+XPPP0%5221%G21Q?'>r1%J2L1&RL+R0%H2G1%3251%7251&@r2%QL11%311&SNr3%22R>1%R011%R212%Q?3R<21p071p0<1pV>RK1%R71DrC%Q?21>%Q>22Q=%F2@1%J231&RJ%126QH&Q;%QD221%QG21F+T0%QG231%O2I1%Q3241%QL2R<K%Q22LRI%Q6221%QE241%QF2>1p0D1pV>SA1&R;rD%24RNRM1Gp041p0K1p0QL1p0QB1p0QJ1p0R21p0R;1p0R>1p0RE1p0RN1p0S51pR8SC1pR6SD1pV<SB1pWFT31pWHT41pW>T51pQ8T61pVFT71pW8T81pV2SK1pR<SM1p2T91pVHT71pQNT91pQ>T:1pQLT=1").
Proof. intros LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2.
intros HH Hin HF F8 F0 F1 FBIG SL1 SL2 FR WP.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (D0 : 0 <= F / 8 /\ F / 8 + 128 <= 2 ^ 44) by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
pose proof (WB (p, c) Hin) as ((P0 & _ & P3 & P4 & P5 & P6) & _ & _ & _ & _ & PFA & _). cbn [fst snd] in *.
pose proof (PFA (F, 4, rs) HF) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 4) with 1024 in PF.
unfold app_mem in P6.
apply (agA_frame M1 M2 Wp p c FR); [lia| lia|]. intros x Hx. split.
- intros X. apply WP in X. unfold HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
- intros X. apply WP in X. unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (D1 : 0 <= x / 8 <= 2 ^ 44) by lia.
assert (D2 : p + c <= F -> x / 8 < F / 8) by lia.
assert (D3 : F + 1024 <= p -> F / 8 + 128 <= x / 8) by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
lia.
Qed.
End Blk.
Lemma vis_agree : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "Q5'SOyR0%211'3p021'9y8%711%311p071'B'?r6r1%211(5%53=21r2%611r5%113%:3=31p061pX4E1&R2r3%23>19&QLr4%24:A14p041p081pW2F1pV>G1pR:I1pR2J1pQDQ01").
Proof. intros Hd M Mv a n. intros VV AV i Hi. apply VV. replace i with (a + (i - a)) by lia. apply AV. lia. Qed.
Lemma u32_agree : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "Q8'SOyR0%211'9y8%511%311p051'B&QLr4r3r2+4%544321&RKz%2216&RI%1296&RN+2+R0%3221%9251&QO&RGr7r5%44321Cr6%645413p031p091p0A1p0E1pX2L1pV>M1pR4O1pR2Q01").
Proof. intros M M' a v. intros Hag Ha H4 Hu. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; apply Hag; cbn in Hi; lia. Qed.
Lemma u64_vis : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "QG'SOyR0%211'3p021'9y8%711%311p071'B'?r6r1%211(5%53=21r2%611r5%113%:3=31p061pX4E1&R2r3+8%33?21&RKzr4%3221&RI%12>7&RN+2+R0%3221%:251&R0&RGr7%3421NGr9%54413Q0p031p081p0@1p0E1p0J1pX2Q81pV>Q91pR:Q;1pR2Q<1pQDQB1").
Proof. intros Hd M Mv a v. intros VV AV H0 H1. apply (L5C.u64_at_agree RSEGS Mv M a v (vis_agree Hd M Mv a 8 VV AV) H0 H1). Qed.
Lemma u32_vis : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "QG'SOyR0%211'3p021'9y8%711%311p071'B'?r6r1%211(5%53=21r2%611r5%113%:3=31p061pX4E1&R2r3+4%33?21&RKzr4%3221&RI%12>7&RN+2+R0%3221%:251&QO&RGr7%3421NGr9%54413Q0p031p081p0@1p0E1p0J1pX2Q81pV>Q91pR:Q;1pR2Q<1pQDQB1").
Proof. intros Hd M Mv a v. intros VV AV H0 H1. apply (u32_agree Mv M a v (vis_agree Hd M Mv a 4 VV AV) H0 H1). Qed.
Lemma avis_sub : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "L'SOyR0%211'3p021'B&R2r5r4r3%43321&RK%1253&RI%1265r6%3219%6231r8%=31<;p031p091p0<1pW4B1pV@C1pW2D1pV>E1pQDG1").
Proof. intros Hd a n a' n'. intros AV H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply AV. lia. Qed.
Lemma shz_vis : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "R:'SOyR0%211'3p021'9y8%711%311p071'B'?r7r1%211(5%53=21r2%611r6%113%:3=31p061pX4E1&R2r3%23>91&RI&RJr5+8%3221&Q;%6221%G3H19&RK+Vb\P0r4%3221%<2:D&RN+2+R0%3221%9251'>z%<21Q2&RLr8%22Q51%6241&R1&RGr;%L26Q6%44321:p061pW0Q@1&QIr9%2371<p041p0C1p0J1p0O1p0Q81p0Q<1pW:QJ1pVNQK1pW6QL1pR:QN1pR2QO1pQDR51").
Proof. intros Hd M Mv o g q.
intros VV AV EQ Q0 Q1 U j Hj. unfold byte_at, HeapIfaceA.S. rewrite EQ. rewrite VV; [| apply AV; exact Hj].
apply (L5ADHR.byte_of_u8 Mv _ 0 (U j Hj)); lia.
Qed.
Lemma agA_ahpres_ff : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "S0'Q>'Q?'7';'B%2211%411&QD%611&QN%811'SOyR0%211'9y8%511%311p051&RFr<r;r:r9r8r7r6r5r4%:9987654321&RH%13H39&RK&RI&QA%118+Q0%4221%621:%62<;&RO%71?&QB&QC%11B%311%=251+8%8221%A2:1z%C21I%C2KJ&RN+2+Q?%3221%I251'>r1%L2Q51&RL%M2Q7Q6%2241%6241&QMr>r2%3221&Q:%113%6251%>241p091pX6R61&R;%14QHQGQEQDp031p0E1p0L1p0O1p0Q;1p0QC1p0QF1pW2R@1pW6RA1pVLR?1pR4R51pR2R61pV:R?1pWDRF1pWLRG1pQ<RD1pQJRG1pVBRM1pQFRO1").
Proof. intros L ar LBc FFc spc scrc Wc M M' f o n.
intros (AK & _ & _) Hf H1 H2 H3 H4 OUT. split.
- intros i Hi. apply AK. split; [lia|]. split; [| exact (proj1 (OUT i Hi))]. right; right; right; left. exists f. split; [exact Hf| lia].
- intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply AK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (proj2 (OUT x Hx))].
right; right; right; right; right; left. exists f. split; [exact Hf|]. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
Qed.
Lemma agA_ahpres_blk : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "R>'Q>'Q?'7';'B%2211%411&QD%611&QN%811'SOyR0%211'9y8%511%311p051&RFr;r:r9r8r7r6r5r4r3%:9987654321&RH(:r2%24MM51%43M1=&RKz%221:&RI%12=<&RN+2+Q?%3221%9251'>r1%<2G1&RL%;2IH%2241%6241&QM%12Q1E&Q:%11G%42Q41%<241p071pX6QG1&R;%14Q7Q6Q5Q4p031p0C1p0K1p0O1p0Q51pVFQO1pW8R01pR4QC1pR2QD1pV:QM1pWDR41pWLR51pQ<R21pQJR51pVBR;1pQFR=1").
Proof. intros L ar LBc FFc spc scrc Wc M M' p c.
intros (AK & _ & _) Hin H3 H4 OUT. split.
- intros i Hi. apply AK. split; [lia|]. split; [| exact (proj1 (OUT i Hi))]. left. exists (p, c). split; [exact Hin| cbn [fst snd]; lia].
- intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply AK. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split; [| exact (proj2 (OUT x Hx))].
right; right; right; right; right; right. exists (p, c). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
Qed.
Lemma blk_facts : ltac2:(TCodec.tc2 tcn__PmBHarnessKit "S='Q>'Q?'Q@'O'Q='QKr5r4r3r2r1%6554321'7';'B%2211%411&QD%611&Q7'SOyR0%211'9y8%511%311p051&QJ&QHr;r9r8r7r6%6854321MLK&RH(:%14HHNMr:%43I21'>&RK+TP0%221Q5'?&RM+@%22Q91z%53Q421&RL%123Q<&RI%12Q?Q>&RO&Q<r@%211+XPPP0%5221%C271'A&Q9%F2:1&Q8%H21QK%5231&RN+2+Q?%3221%N2B1&QGrA%211%Q22F1&QF%114%Q521R8%B241&QE&2%13R2Q<QD%33R=R<1%Q<251%Q=2>1%Q>2D1%Q?2K1%Q@2Q51%QA2Q81%QB2Q?1p0QD1p0QJ1pVFR@1pW8RA1pV2R41pR<R61p2RB1pVHR@1pQNRB1pQ>RC1pQLRF1pQBRL1pQ@S41pW@S61p4S81pVBS:1pQFS<1").
Proof. intros L ar C scfg HI HIok LBx FFx LKx crx Ax Mx Vx p c.
intros HH Hin. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
pose proof (WB (p, c) Hin) as ((P0 & P1 & P3 & P4 & P5 & P6) & _ & _ & _ & _ & PFA & _). cbn [fst snd] in *. unfold app_mem in P6.
split; [lia|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [tauto|]. split; [tauto|]. split; [exact P1| exact PFA].
Qed.
End PMHAK.
