(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmTxtKit2 PmBSrcKit PmBReset1 PmBRsKit PmBSrdP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBSrd1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBSrd1.PMBSR1.WithHeap.Call."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepAB0.PMKB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTxtKit2.PMTK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.Sorting.Permutation."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw'"; "0BX"; "1app"; "1bool"; "1cons"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"]; ["2not"; "2or"; "3map"; "4Z"; "0FF"; "0H"; "0HI"; "0K"; "0L"; "0LB"; "0LBX"; "0LK"; "0LK'"; "5Model"; "6bvmap"; "0M"]; ["0M'"; "0M1"; "0M1v"; "0MV"; "0R"; "0R'"; "0R1"; "7mrestrict"; "8msteps"; "9credit"; "9regs_preserved"; ":aclient"; ":ahid"; ":ar_stack_top"; ":fframe"; ":ri_inv"]; [":vml"; "<img_clear"; "<in_rng"; "<outside"; "<ra_ok"; "<range"; "<u32_at"; "<u64_at"; "<writable"; ";SCFG"; "=avis"; ">zeros_at"; "?U"; "?W0"; "?acct"; "?kept_rs"]; ["?locals"; "?lregs"; "?memrel"; "?ois"; "?op"; "?os"; "?saves13"; "?st_ok"; "?tb"; "?tbdst"; "@ADDR_B"; "ACHUNK"; "Ap_b"; "Ap_k"; "Ap_src"; "Ap_tb"]; ["Ap_tg"; "Aparser_own"; "Apst"; "Asm_eg"; "Asm_g"; "Asm_st"; "Asr_qc"; "Asr_rem"; "Asrc_own"; "Asrcst"; "Astrm"; "Aunread"; "Avec_own"; "Avs_cap"; "Avs_own"; "Avs_size"]; ["Avstr"; "BaobjA"; "Bcfg"; "Bconsumed"; "BentryA"; "BffroomA"; "BffrsA"; "Bsrc_step"; "Bwith_src"; "Cwapp"; "Dwith_tb"; "EFPState"; "Egetr"; "Emkst"; "Eseg_rom"; "Fsrealizes"]; ["Gmem_grows"; "Hahpres"; "Iek"; "Jloaded_segments"; "0S"; "0SCFG_P"; "KIn"; "LPermutation"; "Madd"; "Mdiv"; "Mle"; "Mlt"; "Mmodulo"; "Mof_nat"; "Mpow"; "Msub"]; ["0V"; "0W'"; "0X"; "0a"; "0ar"; "0cr"; "0cr'"; "0d"; "0fb"; "0fx"; "0fx'"; "0fx1"; "0h"; "0k"; "0l"; "0l'"]; ["0len"; "0model"; "0model'"; "0model1"; "0n"; "0nn"; "0p"; "0pc"; "0pc1"; "0r0"; "0rs"; "0s"; "0scr'"; "0sm"; "0sm'"; "0src'"]; ["NNoDup"; "OZ_to_bv"; "Obv"; "0tb"; "0tb'"; "0tg"; "0tg'"; "0v"; "0w"; "0w'"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBSR1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMB.AD.
Abbreviation pot := (fun L ar (s : PM.pst) => PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb s) (PM.p_tg s))).
Lemma nodup_perm : ltac2:(TCodec.tc2 tcn__PmBSrd1 "D'7'<'C%2211%411'SGr2r1%33521'U0&B&6%12::r3%44;<21%62=1p011p091pY0>1pXN?1").
Proof. intros l l'.
intros P ND. apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
eapply Permutation_NoDup; [|exact ND]. apply Permutation_map. exact P.
Qed.
Lemma own_with_src : ltac2:(TCodec.tc2 tcn__PmBSrd1 "J'RB'RI'>'C&RFr1%211&R>r2%211%611%93851'7'<%12;;%311&RA&S8r3%221;%411%513%D3721p0<1pZ0G1pYHI1").
Proof. intros s src'. intros E. unfold PM.parser_own, PMSPA.with_src, PM.src_own. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite E. reflexivity. Qed.
Lemma with_src_id : ltac2:(TCodec.tc2 tcn__PmBSrd1 "9'RB'>&S8r1&R>%112%4231%63714pYH81").
Proof. intros s. destruct s; reflexivity. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma perm_tb : ltac2:(TCodec.tc2 tcn__PmBSrd1 "QM'RB'7'<'C%2211%411&Q>%611&Q9'U2yR0%211':y8%511%311p051&Q@&Q?vF&3&RAr8%211r7%53E21r6r5r4r3r2r1%>8=7654321&RN&R?r9%211%411&RH&R>%115%311&RL&R<%119&R=%11;%5231%L3Q<1J%M3Q=81%N3Q>=1%Q18Q01KIHGFEp0D1pX2Q41pR0Q61p2QB1pX<Q@1pQHQB1pQ:QC1pQDQF1pYHQL1").
Proof. intros s LB FF LK cr Aw M V.
intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF FF LK cr Aw M V HH).
- intros b. unfold PM.parser_own. rewrite !in_app_iff. tauto.
- apply (nodup_perm (PM.parser_own s ++ LB)); [|exact ND].
unfold PM.parser_own. set (X := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s)).
replace ((PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own (PM.p_tb s)) ++ LB) with (X ++ PM.vs_own (PM.p_tb s) ++ LB)
by (unfold X; rewrite <- !app_assoc; reflexivity).
replace (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB) with (X ++ LB) by (unfold X; rewrite <- !app_assoc; reflexivity).
apply Permutation_app_swap_app.
- intros f. tauto.
- rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
Lemma perm_tb_back : ltac2:(TCodec.tc2 tcn__PmBSrd1 "R2'RB'S0'C'7'<%1233%311&Q>%511&Q9'U2yR0%211':y8%511%311p051&Q@&Q?vF&3&RNr9%211&RH&R>r:%211%411&RL&R<%115&R=%117%5231r7%@3Q021%A3Q191%B3Q2?1r6r5r4r3r2r1%K8J7654321&RA&S:r;%231GK%411r8%Q03Q@21%Q38Q21B>=<;:p091pX2Q61pR0Q81p2QD1pX<QB1pQHQD1pQ:QE1pQDQH1pZ<QM1pZ8QO1pYHR11").
Proof. intros s tb tg LB FF LK cr Aw M V.
intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF FF LK cr Aw M V HH).
- intros b. unfold PM.parser_own, PMTK2.with_tb. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite !in_app_iff. tauto.
- apply (nodup_perm (PM.vs_own tb ++ (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB))); [|exact ND].
unfold PM.parser_own, PMTK2.with_tb. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb].
set (X := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s)).
replace ((PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own tb) ++ LB) with (X ++ PM.vs_own tb ++ LB)
by (unfold X; rewrite <- !app_assoc; reflexivity).
replace (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB) with (X ++ LB) by (unfold X; rewrite <- !app_assoc; reflexivity).
apply Permutation_sym. apply Permutation_app_swap_app.
- intros f. tauto.
- rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PMSPA.ffroomA 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PMSPA.frame_okA FF fb.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size (PM.p_tb s0) + PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis RSZ : PMB.str_resize_spec L ar HI.
Hypothesis SRD : PMB.src_read_spec L ar HI.
Hypothesis FBT : PMB.fill_buffer_tb_spec L ar HI.
Definition W0 : list L5.range := PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)].
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
PMSPA.consumed (PM.p_src s0) (PM.p_src s') sm0 sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s0) + d ->
PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s' -> PM.iss_at RSEGS AD PMSPA.accA M' (PMSPA.o_is AD fb) str sm' ->
PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
PMSPA.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 5) (PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)]) M0 M' ->
PMSPA.credit_keep cr0 cr' (pot L ar s0) (pot L ar s') ->
model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.
Definition op : Z := PMSPA.o_p AD fb.
Definition os : Z := PMSPA.o_src AD fb.
Definition ois : Z := PMSPA.o_is AD fb.
Definition tb : Z := PMSPA.o_tb AD fb.
Definition U (x : nat) : Z := bv_unsigned (getr R0 (reg x)).
Definition saves13 (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
/\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20) /\ L5.u64_at RSEGS M (S - 56) (U 21) /\ L5.u64_at RSEGS M (S - 64) (U 22)
/\ L5.u64_at RSEGS M (S - 72) (U 23) /\ L5.u64_at RSEGS M (S - 80) (U 24) /\ L5.u64_at RSEGS M (S - 88) (U 25) /\ L5.u64_at RSEGS M (S - 96) (U 26)
/\ L5.u64_at RSEGS M (S - 104) (U 27).
Definition locals (M : word -> option byte) : Prop :=
L5.u64_at RSEGS M (S - 160) len /\ L5.u64_at RSEGS M (S - 152) ((os + 256) / 8 + 2147450880) /\ L5.u64_at RSEGS M (S - 144) (os + 256)
/\ L5.u64_at RSEGS M (S - 136) ((tb + 8) / 8 + 2147450880) /\ L5.u64_at RSEGS M (S - 128) ((tb + 16) / 8 + 2147450880)
/\ L5.u64_at RSEGS M (S - 120) (tb + 16) /\ L5.u64_at RSEGS M (S - 112) (tb + 8).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4]%nat -> getr R (reg x) = getr R0 (reg x).
Definition memrel (M : word -> option byte) : Prop :=
L5SAR.ek L ar LBX FF S 22528 W0 M0 M /\ L5SAR.dk L ar LBX FF S 22528 M0 M /\ L5CA.astk ar M S 22528.
Definition fields_eq (s : PM.pst) : Prop :=
PM.p_more s = PM.p_more s0 /\ PM.p_done s = PM.p_done s0 /\ PM.p_depth s = PM.p_depth s0 /\ PM.p_b s = PM.p_b s0 /\ PM.p_k s = PM.p_k s0 /\ PM.p_stk s = PM.p_stk s0.
Definition acct (s : PM.pst) (sm : PM.strm) (w : Z) : Prop :=
PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = len - w /\ PM.vs_size (PM.p_tb s) = PM.vs_size (PM.p_tb s0) + (len - w)
/\ PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm /\ fields_eq s.
Definition st_ok (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
memrel M /\ saves13 M /\ locals M /\ PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op ois s /\ PM.iss_at RSEGS AD PMSPA.accA M ois str sm
/\ PMSTA.base_okA RSEGS AD M /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
/\ ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model
/\ incl LK LK0 /\ incl Aw0 Aw
/\ PMSPA.credit_le (pot L ar s) cr /\ PMSPA.credit_keep cr0 cr (pot L ar s0) (pot L ar s).
Definition lregs (R : bvmap 5 word) (w : Z) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 176) /\ getr R (reg 8) = Z_to_bv 64 w /\ getr R (reg 9) = Z_to_bv 64 tb
/\ getr R (reg 18) = Z_to_bv 64 os /\ getr R (reg 19) = Z_to_bv 64 (os + 272) /\ getr R (reg 20) = Z_to_bv 64 (tb / 8 + 2147450880)
/\ getr R (reg 21) = Z_to_bv 64 (os + 288) /\ getr R (reg 23) = Z_to_bv 64 ((os + 272) / 8 + 2147450880)
/\ getr R (reg 26) = Z_to_bv 64 (tb + 1) /\ getr R (reg 27) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) /\ kept_rs R.
Lemma geo : ltac2:(TCodec.tc2 tcn__PmBSrd1 "H'='>'C&R4&SHvT8+^@%3221%73651&R5+_8%7261%;3:31&R3+S0%;2:1%?3>31&R8+i0%?2>1%C3B31%E251%F2:1%G2?1").
Proof. unfold op, os, ois, tb, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_p, PMSPA.o_is. cbn [pa_off_p pa_off_is ADDR_B]. repeat split; lia. Qed.
Lemma fbb : ltac2:(TCodec.tc2 tcn__PmBSrd1 "H'='>'C&SLvT8+QP0%3221z%73621'?&SF'<%12::%221;(;+4%24>><1r1%446@21vD%:3721qYFC1%=2D1%G2?1").
Proof. destruct FOK as (X & Y). split; [exact Y| exact X]. Qed.
Lemma inW_W0 : ltac2:(TCodec.tc2 tcn__PmBSrd1 "M'C'?&QE'=&SFr1&QM%33521&QBr2%2251%8241qYD:1%<2;1&SJ&SHvT8+S0%3221+Q8%5221%721<&SK+iH%9281%32@1%G251p0>1pX8L1").
Proof using All. intros a.
intros (r0 & Hin & Hr). unfold W0, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_is, PMSPA.o_p in Hin.
cbn [pa_off_p pa_off_is AD PMB.AD ADDR_B app] in Hin. unfold L5.in_rng in Hr.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_W0 : ltac2:(TCodec.tc2 tcn__PmBSrd1 "D'C'A&SKr1&SHvT8+T8%3221%6251&SJ+iH%7261%3219%<251&QC&QMr2%3221p051pX8C1").
Proof using All. intros a. intros Ha r0 Hr0 Hin. assert (I : exists r1, In r1 W0 /\ L5.in_rng r1 a) by (exists r0; split; assumption). apply inW_W0 in I. lia. Qed.
Lemma wapp_W0 : ltac2:(TCodec.tc2 tcn__PmBSrd1 "?'A&SJ&SHvT8+QP0%3221+QoonlP0%6221+`PQoooPP0%8216%:231&S9&QM%211p041").
Proof using All.
intros X r0 Hr. unfold W0, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_is, PMSPA.o_p in Hr. cbn [pa_off_p pa_off_is AD PMB.AD ADDR_B app] in Hr.
unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; destruct X; [left|right|left|right|left|right|left|right]; lia.
Qed.
Lemma finish : ltac2:(TCodec.tc2 tcn__PmBSrd1 "T@'S;&Ny5'U2yR0%211%5241':y8%611%311p061'M'RB'RJ&Q9'7&Q>%211'<'C%2211%611'>&S<r9&U1&SMu1%211%42L1%7261&QL%115%82N1%<3N41r:u2%;11%=2Q51%@241vSD%@2Q61%D3Q631'8&SFr1(5u8u9uBuCuDuEuFuGuHuIuJuK(9%11A%?3B31%@3C51%A3D71%B3E91%C3F;1%D3G=1%E3H?1%F3IA1%G3JC1%H3KE1%I3LG1%J3MI1%M3NL1r=r2%QB11%QD2R<1%QG241%Q@14%QG2R=1%QK3R=31p091pZFQ81&QOr<%211u:%QN11%R02RH1%R32@1&SOvT@r5%3221%R62RL1%R:3RL61'=&SJzr6%3221%422:%6221&R7r>r;r8%473Q2G2R9RD1&QN%13Q4I3'S?&SC&QIvSE%211&S2rBrA+f]T<r@r?%66:54321vG%=4<921p0?1p0B1p0H1p0Q01p0Q;1p0Q?1p0RI1p0S21pZBSB1p2SA1pQHSF1pX<SJ1pYLSL1pYHSN1pY4T01pR0T21pR:T81pXDT?1").
Proof using All. intros fx R M model s sm cr LK Aw w.
intros E1 E2 ES KP E10 Hw ((EK & DK & STK) & _ & _ & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK) (CONS & SZ & STEP & (F1 & F2 & F3 & F4 & F5 & F6)).
pose proof RAok as (Hr1 & Hr2).
assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
unfold PMSPA.cfg.
apply (PMBSK.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr Aw 0xb348c r (ltac:(oW' 0xb348c%Z)) HH AM (ltac:(oF' 0xb348c%Z)) eq_refl (ltac:(oD' 0xb348c%Z)) RA ltac:(lia) Hr2).
intros model1 MRT1 AM1 HH1.
apply (KONT fx R M model1 LK Aw s sm cr (len - w)); try assumption; try lia.
- apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx.
destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
rewrite (ES x) by (cbn in Hx; cbn; tauto). unfold U. apply Z_to_bv_bv_unsigned.
- change (PMSPA.pm_scr 5) with 22528. apply (L5SAR.ahpres_of L ar LBX FF S 22528 _ M0 M EK); [destruct STK as (_ & _ & _ & _ & D & _); exact D| exact DK].
- eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.
Lemma callee_mem : ltac2:(TCodec.tc2 tcn__PmBSrd1 "S2'U2yR0%211':y8%511%311p051'7'<'C%2211%411&QE%611&R2r5%211&R6r6%211&R0r7%211&SJz%221:&SH+U@%221:+fP0%7221&Q=vT4%211&SN+2+Q?%3221%?251&SAvH&3r9vJ%33Q221vD&SOvSD%221Er8r;r:%=9<D8743O21&Q;r1%27?G<:8J1&QC&QMr2%3221r3%52;1p031p081pX8QG1'=%Q;2B<&SK%12>E%4231%>2D<p021pX8QO1r=%QL11%QJ12%QH13&SBr>%29Q7Q?Q4Q2Q0QBF16%?241%@261%A281p0;1p0D1p0Q11p0Q@1p0QI1p0QO1p0R31p0R71p0R;1pX4R?1pYJRD1p6RC1pR2RI1pR0RJ1").
Proof using All. intros M M' BX scr' W'.
intros (EK & DK & STK) SV LC Hs Hs2 TOP HP HW HWS.
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
assert (EKn : L5SAR.ek L ar LBX FF S 22528 W0 M M').
{ apply (L5SAR.ek_callee L ar LBX BX FF [] S 22528 (S - 176) scr' W0 W' M M' HP); [lia|lia| exact HW]. }
assert (DKn : L5SAR.dk L ar LBX FF S 22528 M M') by (apply (L5SAR.dk_callee L ar LBX BX FF [] S 22528 (S - 176) scr' W' M M' HP); lia).
assert (KEEPS : forall k v, 8 <= k <= 176 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS M' (S - k) v).
{ intros k v Hk X. apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact X].
intros i Hi. destruct HP as (P & _). apply P. split; [lia|]. split.
- apply (L5SAR.stack_client L ar (BX ++ LBX) FF (S - 176) scr' i); lia.
- apply HWS. lia. }
split; [split; [|split]|].
- exact (L5SAR.ek_trans L ar LBX FF S 22528 W0 M0 M M' EK EKn).
- exact (L5SAR.dk_trans L ar LBX FF S 22528 M0 M M' DK DKn).
- apply (PMKB.astk_after_ahpres L ar _ FF M M' S 22528 (S - 176) scr' W' STK HP); lia.
- split; [|split; [|exact EKn]].
+ destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
repeat split; (apply KEEPS; [lia| assumption]).
+ destruct LC as (L1 & L2 & L3 & L4 & L5' & L6 & L7).
repeat split; (apply KEEPS; [lia| assumption]).
Qed.
Lemma centry : ltac2:(TCodec.tc2 tcn__PmBSrd1 "RO&Ny5'U2yR0%211%5241':y8%611%311p061'M'RB'RJ&Q9'7&Q>%211'<'C%2211%611'>&S<r:&U1&SMu1%211%42L1%7261r2%72M1%;3M31&QDr3%211r<u2%=11%?2Q71%B241&SOvSD+U@%3221%E2Q;1%I3Q;61&QOr=%211&R7r;r9r8r7%577C4Q0321'=&SJ+1r6%3221+4%5231%7231&S4&R:vHvT4r@r?%6854321JA@&S5vD%23C1QB&S6%123O%D231%E271p0?1p0H1p0O1p0Q31p0Q?1p0QC1pXJR21pX6R31p2R21pQHR71pX<R;1pYLR=1pYHR?1pY4RA1pR0RC1pR:RI1").
Proof using All. intros R M model s sm cr LK Aw X h.
intros A1 RAX A2 KP SO Hh.
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
pose proof fbb as (F1024 & rs & Hfb).
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in FF2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2.
assert (STKr : L5CA.astk ar M (S - 176) (PMSPA.pm_scr h)).
{ apply (L5SAR.astk_sub ar M M S 22528 176 (PMSPA.pm_scr h) STK (fun _ Y => Y)); unfold PMSPA.pm_scr; [lia|lia|lia|].
replace (S - 176) with (S + (-11) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (WAPP0 : PMKB.wapp W0) by (apply wapp_W0; destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; [left|right]; lia).
assert (STKSH : shadow_zero M (S - 176 - PMSPA.pm_scr h) (PMSPA.pm_scr h / 8)).
{ assert (M8a : (S - 22528) mod 8 = 0) by (apply PMKB.mod16_8'; replace (S - 22528) with (S + (-1408) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
assert (M8b : (S - 176 - PMSPA.pm_scr h) mod 8 = 0).
{ apply PMKB.mod16_8'. unfold PMSPA.pm_scr. replace (S - 176 - (12288 + 2048 * h)) with (S + (-(779 + 128 * h)) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
assert (G8 : PMSPA.pm_scr h / 8 = 1536 + 256 * h).
{ unfold PMSPA.pm_scr. replace (12288 + 2048 * h) with ((1536 + 256 * h) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
rewrite G8. unfold PMSPA.pm_scr in M8b |- *.
apply (PMKB.shadow_zero_sub M (S - 22528) 2816); [exact M8a| exact M8b| lia| lia| lia|].
apply (PMKB.stksh_keepA L ar LBX FF S 22528 W0 M0 M EK WAPP0 (S - 22528) 2816); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
assert (FRM : PMSPA.ffroomA h FF LK) by (apply (PMBRSK.ffroom_incl 5 h FF LK0 LK FRM0 ILK NDF); lia).
split; [|split; [exact FRM| intros f Hf; specialize (FRS f Hf); lia]].
unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
split; [exact STKr| exact STKSH].
Qed.
Lemma call_resize : ltac2:(TCodec.tc2 tcn__PmBSrd1 "U>'S;&Ny5'U2yR0%211%5241':y8%611%311p061'M'RB'RJ&Q9'7&Q>%211'<'C%2211%611'>&S<r:&U1&SMu1%211%42L1%7261r1%72M1%;3M31&QDr2%211r<u2%=11%?2Q71%B241&SOvSD+U@%3221%E2Q;1%I3Q;61&QOr=%211r>u:%K11%M2QE1%Q0241&R8%Q02QF1%Q43QF31r?u;%Q311%Q52QM1%Q8241r7%Q82QN1%Q<3QN31'=&SJzr8%3221&SH&RO&R?%11J%311&R;%6221%;291%=291&SKr9&SN+2+J%3221%?21:%7261&R7rAr@r;%4732Q2Q:Q<QH1'S0&Q:rL%221Kr4%J11rE%R?3RB21rF&RMrK%O11%311%Q7251&RNr6%211%Q51?%411%RK3RL31r5&R@%11D%RO3S231%QC251p0<1&S:%13I<7%Q17S2Q81BHQDQJ'S?&SC&QIvSE%211&S2rG%266RARM1Q6S:vG%948521p0;1p0?1p0Q21p0Q71pX>SK1pZ>SG1pZ:Q=1p4SG1pQJSL1pY6T31pR2T51pR<T;1pXFTB1rD+j\[@rCrB%F6JQB4321%L4KH1Dp071p0QL1p0R21p0R;1p0RJ1p0S31p0S<1p0S@1p0SL1p0T01pX6T?1pY<T@1p2T?1pQHTD1pX<TH1pYLTJ1pYHTL1pY4TN1pR0U01pR:U61pXDU=1").
Proof using All. intros fx R M model s sm cr LK Aw nn X.
intros A1 RAX A2 KP A10 A11 Hn1 Hn2 SO NEXT.
destruct (centry R M model s sm cr LK Aw X 1 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in FF2.
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
pose proof (PMBRSK.tb_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s HH FOK PA) as ((T1 & T8 & TBIG) & _ & _ & _ & _ & AT & TFS1 & TFS2).
fold tb in T1, T8, TBIG, AT, TFS1, TFS2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2, TFS1, TFS2.
pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & VS & VEC & _).
replace (op + 336) with tb in VS by lia.
pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
destruct (BRB _ QIN) as (QB0 & QB1). destruct (BRB _ VIN) as (VB0 & VB1). cbn [fst snd] in QB0, QB1, VB0, VB1.
assert (BLKAP : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q + m <= fb \/ fb + 1024 <= q).
{ intros q m Hq. destruct (WB _ Hq) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
destruct (FA (fb, 4, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 4) with 1024 in X0; [left|right]; lia. }
set (LB' := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LBX).
pose proof (perm_tb s LBX FF LK cr Aw M _ HH) as HH'. fold LB' in HH'.
pose proof RSZ as RS. unfold PMB.str_resize_spec, PMSPA.str_resize_spec in RS. cbn [pa_str_resize AD PMB.AD ADDR_B] in RS.
apply (RS fx R M model K LB' FF LK Aw cr tb nn (S - 176) X (PM.p_tg s) (PM.p_tb s) HH' AM K0 ENT FRM FRS').
{ rewrite L5K.rl10. exact A10. }
{ rewrite L5SAR.r11. exact A11. }
{ exact AT. } { exact T8. } { exact VS. } { exact TBOK. } { exact Hn1. } { exact Hn2. } { exact CRL. }
intros fx' R' M' model' LK' Aw' tb' tg' cr' RP VS' SZ TB' OWN HP CK MRT' ILK' IAW' AM' HH2.
change (PMSPA.pm_scr 1) with 14336 in HP.
apply (NEXT fx' R' M' model' LK' Aw' tb' tg' cr' RP SZ OWN).
assert (HPc : L5CA.ahpres L ar ((PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s)) ++ LBX) FF (S - 176) 14336 [(tb, 24)] M M')
by (rewrite <- app_assoc; exact HP).
destruct (callee_mem M M' _ 14336 [(tb, 24)] MR SV LC ltac:(lia) ltac:(lia) TOP HPc) as (MR' & SV' & LC' & EKn).
{ intros a _ O r0 [<-|[]] Hin. apply (O (PMSPA.o_tb AD fb, 24)); [unfold W0; apply in_or_app; right; left; reflexivity| exact Hin]. }
{ intros a Ha r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia. }
set (Wt := [(tb, 24)]).
assert (WAPPt : PMKB.wapp Wt) by (apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKB.wapp_nil]).
pose proof HP as (EKr & _ & DKr).
assert (EKt : L5SAR.ek L ar LB' FF (S - 176) 14336 Wt M M') by exact EKr.
assert (INLB : forall b, In b LB' -> In b (PM.parser_own s ++ LBX)).
{ intros b Hb. unfold LB' in Hb. unfold PM.parser_own. rewrite !in_app_iff in *. tauto. }
assert (BRB' : forall b, In b LB' -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; exact (BRB b (INLB b Hb))).
assert (OUTB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> forall i, q <= i < q + m -> L5.outside Wt i).
{ intros q m Hq i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (BLKAP q m Hq); lia. }
assert (AOI : PMSPA.aobjA FF ois 272).
{ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (PD' : L5.defined M' op 384).
{ intros i Hi. apply DKr; [lia| |apply PD; exact Hi].
unfold aclient, aclient_g. right; right; right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (PA' : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' op ois (PMTK2.with_tb s tb' tg')).
{ apply (PMBRSK.parser_tb_setA M M' op ois s tb' tg' PA); [lia| lia| | | | lia| unfold PM.CHUNK in *; lia| | lia| lia| | |].
- apply (PMKB.agA_obj L ar LB' FF (S - 176) 14336 Wt M M' EKt WAPPt FRB).
+ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia.
+ intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
- apply (PMKB.agA_obj L ar LB' FF (S - 176) 14336 Wt M M' EKt WAPPt FRB).
+ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia.
+ intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
- apply (PMKB.agsh_obj L ar LB' FF (S - 176) 14336 Wt M M' EKt WAPPt FRB).
exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia.
- apply (PMKB.agA_blk L ar LB' FF (S - 176) 14336 Wt M M' EKt WAPPt BRB'); [unfold LB', PM.src_own; apply in_or_app; left; left; reflexivity| exact (OUTB _ _ QIN)].
- apply (PMKB.agA_blk L ar LB' FF (S - 176) 14336 Wt M M' EKt WAPPt BRB');
[unfold LB', PM.vec_own; apply in_or_app; right; apply in_or_app; left; left; reflexivity| exact (OUTB _ _ VIN)].
- replace (op + 336) with tb by lia. exact VS'.
- exact PD'. }
assert (IA' : PM.iss_at RSEGS AD PMSPA.accA M' ois str sm).
{ apply (PMKB.iss_keepA RSEGS AD L ar LB' FF (S - 176) 14336 Wt M M' EKt WAPPt FRB BRB' _ _ _ AOI); [| | |exact IA].
- intros x Hx. unfold LB'. rewrite !in_app_iff. right; right. apply INCS. exact Hx.
- intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
- intros c n p E i Hi. apply (OUTB p c); [apply in_or_app; right; apply INCS; rewrite E; left; reflexivity| exact Hi]. }
split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
split.
{ apply (PMBSK.base_keep L ar C LY LBX FF S 22528 W0 M M' EKn); [| exact BASE].
intros a Ha. apply outside_W0. pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
split; [exact TB'|]. split; [apply perm_tb_back; exact HH2|]. split; [exact AM'|].
split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
cbn [PMTK2.with_tb PM.p_tb PM.p_tg].
unfold PMSPA.credit_keep, PMSPA.credit_le in *. destruct CRL as (CL1 & CL2). destruct CK as (CK1 & CK2). destruct CRK as (CR1 & CR2). split; split; lia.
Qed.
Definition tbdst (s : PM.pst) (p k : Z) : Prop :=
((exists n, PM.p_tb s = PM.VShort n) /\ tb + 1 <= p /\ p + k <= tb + 24)
\/ (exists c n q, PM.p_tb s = PM.VLong c n q /\ q <= p /\ p + k <= q + c).
Lemma call_srcread : ltac2:(TCodec.tc2 tcn__PmBSrd1 "V1'S;&Ny5'U2yR0%211%5241':y8%611%311p061'M'RB'RJ&Q9'7&Q>%211'<'C%2211%611'>&S<r;&U1&SMu1%211%42L1%7261r1%72M1%;3M31&QDr2%211r=u2%=11%?2Q71%B241&SOvSD+U@%3221%E2Q;1%I3Q;61&QOr>%211r?u:%K11%M2QE1%Q0241&R5%Q02QF1%Q43QF31r@u;%Q311%Q52QM1%Q8241r8%Q82QN1%Q<3QN31rAu<%Q;11%Q=2R51%Q@241%QB3R417'=&SJ+1r9%3221&R;%5231%7231&R9r:%23HQK1&R7rCrB%3721DLQ4Q6QB'RI&Q:rN%221K%R52@Q6%R42RJQJ%R83RJ21zr3%G221rG%I231%K231&S3&R>%11=r6rMr5%644321r4%RG3RJ21&RGrO%:11%311%Q82Q71%Q92Q8;p021%RO3S2=F%81Q:%S13S41H&RE%11QI+2%S53S821%QC251p081&S7rQ1%J11rQ0%442QF1R2&S8rQ2%221QCr<%QC7RFS22QK61S?'S?&SC&QIvSE%211&S2rL%266R<RD1RLRNvG%948521p0;1p0A1p0G1p0Q11p0Q91p0QC1p0QJ1p0QN1pX@T71pYNT>1pZ0R41p4T81pQJT=1pY6TD1pR2TF1pR<TL1pXFU31rF+fQbLrErD%J6NR54321%Q04OL1Hp071p0RC1p0RH1p0RL1p0S51p0S<1p0SE1p0SN1p0T21p0T>1p0TB1pX6U11pXLU21pY>U31p2U21pQHU71pX<U;1pYLU=1pYHU?1pY4UA1pR0UC1pR:UI1pXDV01").
Proof using All. intros fx R M model s sm cr LK Aw p k X.
intros A1 RAX A2 KP A10 A11 A12 Hk DST SO NEXT.
destruct (centry R M model s sm cr LK Aw X 4 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in FF2.
pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
pose proof (PMBRSK.tb_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s HH FOK PA) as ((T1 & T8 & TBIG) & _ & _ & _ & _ & AT & TFS1 & TFS2).
fold tb in T1, T8, TBIG, AT, TFS1, TFS2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2, TFS1, TFS2.
assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
assert (DSTB : 0 <= p /\ p + k <= 2 ^ 47 /\ forall a, p <= a < p + k -> (tb <= a < tb + 24) \/ exists B m, In (B, m) (PM.parser_own s) /\ B <= a < B + m).
{ destruct DST as [(_ & D1 & D2)|(c & n & q & E & D1 & D2)].
- split; [lia|]. split; [lia|]. intros a Ha. left. lia.
- assert (IN : In (q, c) (PM.parser_own s)) by (unfold PM.parser_own; rewrite E; cbn; right; right; left; reflexivity).
destruct (BRB (q, c) ltac:(apply in_or_app; left; exact IN)) as (Q0 & Q4). cbn [fst snd] in Q0, Q4.
split; [lia|]. split; [lia|]. intros a Ha. right. exists q, c. split; [exact IN| lia]. }
destruct DSTB as (Dp0 & Dp1 & DIN).
pose proof SRD as SR. unfold PMB.src_read_spec, PMSPA.src_read_spec, PMSPA.src_spec in SR. cbn [pa_src_read AD PMB.AD ADDR_B] in SR.
apply (SR fx R M model K LBX FF LK Aw cr (S - 176) X fb s str sm [(p, k)] HH AM K0 ENT FRM FRS' FOK).
{ rewrite L5K.rl10. exact A10. }
{ unfold PMSPA.read_args. exists p, k. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. split; [exact Hk|].
unfold PMSPA.read_dst. right. exact DST. }
{ unfold PMSPA.read_W. exists p, k. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. split; [lia|]. split; [unfold PM.CHUNK in Hk; lia| reflexivity]. }
{ exact PA. } { exact IA. } { exact BASE. } { exact INCS. }
intros fx' R' M' model' LK' Aw' src' sm' RP PA' IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
change (PMSPA.pm_scr 4) with 20480 in HP.
unfold PMSPA.read_res in RES. destruct RES as (p' & k' & d & Y11 & Y12 & Hp' & Hk' & Y10 & Hd & CONS & _ & POS & ZERO).
assert (pk : p' = p /\ k' = k).
{ rewrite L5SAR.r11 in Y11. rewrite L5SAR.r12 in Y12. rewrite A11 in Y11. rewrite A12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
unfold PM.CHUNK in Hk, Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
destruct pk as (-> & ->).
assert (QC : PM.sr_qc src' = PM.sr_qc (PM.p_src s)) by (destruct STEP as (E & _); exact E).
apply (NEXT fx' R' M' model' LK' Aw' src' sm' d RP Y10 Hd CONS POS ZERO STEP).
destruct (callee_mem M M' (PM.parser_own s) 20480 (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, k)]) MR SV LC ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & LC' & EKn).
{ intros a CA OW r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
- unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
+ apply (OW r0); [unfold W0; apply in_or_app; left; exact Hr0| exact Hin].
+ apply (PMBRS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ (PM.sr_qc (PM.p_src s)) PM.CHUNK a S 22528 HH);
[left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA].
- unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN a Hin) as [X0|(B & m & HB & Ha)].
+ apply (OW (PMSPA.o_tb AD fb, 24)); [unfold W0; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X0].
+ apply (PMBRS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ B m a S 22528 HH HB Ha CA). }
{ intros a Ha r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
- unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
+ exact (outside_W0 a ltac:(lia) r0 ltac:(unfold W0; apply in_or_app; left; exact Hr0) Hin).
+ destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia.
- unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN a Hin) as [X0|(B & m & HB & Ha')]; [lia|].
destruct (WB (B, m) ltac:(apply in_or_app; left; exact HB)) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. lia. }
split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
split.
{ apply (PMBSK.base_keep L ar C LY LBX FF S 22528 W0 M M' EKn); [| exact BASE].
intros a Ha. apply outside_W0. pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
split; [exact TBOK|]. split; [rewrite (own_with_src s src' QC); exact HH'|]. split; [exact AM'|].
split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
split; [exact CRL| exact CRK].
Qed.
Lemma call_filltb (fx : FPState) R M model s sm cr LK Aw (p X c0 n0 q0 : Z) :
getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 176) -> kept_rs R ->
getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
PM.p_tb s = PM.VLong c0 n0 q0 -> q0 <= p -> p + PM.CHUNK <= q0 + c0 -> st_ok M model s sm cr LK Aw ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (sm' : PM.strm) (c : Z),
regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
(PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
(PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2) ->
PMSPA.src_step (PM.p_src s) (PM.p_src s) sm sm' ->
st_ok M' model' s sm' cr LK' Aw' ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' X M' model') K) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb0e58 M model) K.
Proof using All.
intros A1 RAX A2 KP A10 A11 A12 ETB D1 D2 SO NEXT.
destruct (centry R M model s sm cr LK Aw X 3 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in FF2.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2.
assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
assert (IN : In (q0, c0) (PM.parser_own s)) by (unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
destruct (WB (q0, c0) ltac:(apply in_or_app; left; exact IN)) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4.
pose proof FBT as SR. unfold PMB.fill_buffer_tb_spec, PMSPA.fill_buffer_tb_spec, PMSPA.src_spec in SR. cbn [pa_fill_buffer AD PMB.AD ADDR_B] in SR.
apply (SR fx R M model K LBX FF LK Aw cr (S - 176) X fb s str sm [(p, PM.CHUNK)] HH AM K0 ENT FRM FRS' FOK).
{ rewrite L5K.rl10. exact A10. }
{ unfold PMSPA.tbfill_args. exists p. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. exists c0, n0, q0. split; [exact ETB|]. lia. }
{ unfold PMSPA.tbfill_W. exists p. rewrite L5SAR.r11. split; [exact A11|]. split; [unfold PM.CHUNK in *; lia| reflexivity]. }
{ exact PA. } { exact IA. } { exact BASE. } { exact INCS. }
intros fx' R' M' model' LK' Aw' src' sm' RP PA' IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
change (PMSPA.pm_scr 3) with 18432 in HP.
destruct RES as ((-> & c & Y10 & Hc & G & ST0 & ST2) & _).
rewrite with_src_id in PA'.
apply (NEXT fx' R' M' model' LK' Aw' sm' c RP Y10 Hc G ST0 ST2 STEP).
destruct (callee_mem M M' (PM.parser_own s) 18432 (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, PM.CHUNK)]) MR SV LC ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & LC' & EKn).
{ intros a CA OW r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
- unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
+ apply (OW r0); [unfold W0; apply in_or_app; left; exact Hr0| exact Hin].
+ apply (PMBRS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ (PM.sr_qc (PM.p_src s)) PM.CHUNK a S 22528 HH);
[left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA].
- unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
apply (PMBRS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ q0 c0 a S 22528 HH IN ltac:(unfold PM.CHUNK in *; lia) CA). }
{ intros a Ha r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
- unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
+ exact (outside_W0 a ltac:(lia) r0 ltac:(unfold W0; apply in_or_app; left; exact Hr0) Hin).
+ destruct (WB _ QIN) as ((Q0' & _ & _ & _ & Q4' & _) & _). cbn [fst snd] in Q0', Q4'. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia.
- unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia. }
split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
split.
{ apply (PMBSK.base_keep L ar C LY LBX FF S 22528 W0 M M' EKn); [| exact BASE].
intros a Ha. apply outside_W0. pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
split; [exact TBOK|]. split; [exact HH'|]. split; [exact AM'|].
split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
split; [exact CRL| exact CRK].
Qed.
Lemma unread_nn : ltac2:(TCodec.tc2 tcn__PmBSrd1 "R2'U2yR0%211':y8%511%311p051'M'RB'RJ&Q9'7&Q>%211'<'C%2211%611&R7r7r6r5r4r3r2r1%877654321'=&SJz&RK&R>%11<%321<%6251'A'>&RE%11A%33H1:+2%53J31%7231&RG%11<%A2@1&R;%C231%E231&RD%11M&RC%11O%I231%K261%L2=1%M2F1p0O1p2Q91pQHQ>1pX<QB1pYLQD1pYHQF1pY4QH1pR0QJ1").
Proof using All. intros M model s sm cr LK Aw.
intros (_ & _ & _ & PA & IA & _).
destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.
Lemma lregs_keep : ltac2:(TCodec.tc2 tcn__PmBSrd1 "QN&Ny5'U2yR0%211%5241'C&R1r3r1%3221'8&SF(5u2u3u4u8u9uBuCuDuEuGuJuK(9%11@%?3A31%@3B51%A3C71%B3D91%C3E;1%D3F=1%E3G?1%F3HA1%G3IC1%H3JE1%I3KG1%J3LI1%L3MO1'>&S<r5&U1&SMr2%211%42Q?1%7261r6%9213%;3Q@31p0=1pZFQ;1r4%QA21Q@p031p0Q@1pZBQE1pR>QG1pR:QH1").
Proof. intros R R1 w.
intros (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP) E.
unfold lregs. rewrite !E by (cbn; tauto). repeat split; try assumption.
intros x Hx. rewrite E by (cbn in Hx |- *; tauto). apply KP. exact Hx.
Qed.
Lemma lregs_pres : ltac2:(TCodec.tc2 tcn__PmBSrd1 "D&Ny5'U2yR0%211%5241'C&Q:r3r2%3221&R1r4%2214%3226p021p061pZB;1pR<=1pR:>1").
Proof. intros R R' w. intros RP LR. apply (lregs_keep R R' w LR). intros x Hx. apply (L5SAR.cs_of_preserved R R' x RP). unfold L5SAR.cs_all. cbn in Hx |- *. tauto. Qed.
Lemma lregs_set : ltac2:(TCodec.tc2 tcn__PmBSrd1 "R5&Ny5'U2yR0%211%5241'C&R1r4r2%3221'8&SFr1(5u2u3u4u9uBuCuDuEuGuJuK(9%11@%>3A31%?3B51%@3C71%A3D91%B3E;1%C3F=1%D3G?1%E3HA1%F3IC1%G3JE1%H3KG1%K3LJ1'>&S<r6&U1&SM%11Q4%32Q=1%6251r7%8213%:3Q>31p0<1pZFQ91r5u8%;11%=2QG1%@241r3%@2QH1%D3QH31%QF2CQEp021p0;1p0QF1pZDQK1pZBQL1pR>QN1pR:QO1").
Proof. intros R R1 w w'.
intros (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP) E E25.
unfold lregs. split; [rewrite E by (cbn; tauto); exact A2|]. split; [exact E25|].
rewrite !E by (cbn; tauto). repeat split; try assumption.
intros x Hx. rewrite E by (cbn in Hx |- *; tauto). apply KP. exact Hx.
Qed.
Lemma ro_step : ltac2:(TCodec.tc2 tcn__PmBSrd1 "SA'S;&Ny5'U2yR0%211%5241'C':y8%711%311p071'M'RB'RJ&Q9'7&Q>%211'<%12>>%511&R7r8r7r6r5r4r3r2%877654321'Q8&SC&S=r?r=&U1r<%22Q31&Q7&Q<%12=Br9%4221&S>%11=%=5<;831r>r;r:%>2Q?1%B5431F6%E3D61&S@%>2K<%@216%321L'=&SJzr1%3221&SK&SN+2+R0%3221%5271%;271'>%Q22R3Q9%Q>11%Q02Q@Q3%Q231Q63%53R031p071pX8R61%QG7Q:AMLQ3QFQE'S?&QIvSE%211&S2rCr@%36QE21QCQ6QHvG%94QG621p0;1pY8R=1rA%96QK817QHQF%>4QL;16p041p0B1p0Q71p0Q<1p0R31pR6RG1p2R>1pQHRB1pX<RF1pYLRH1pYHRJ1pY4RL1pR0RN1pYBS41pR>S61pY@S61pR:S81pXHS?1pXDS@1").
Proof using All. intros fx fx1 R pc R1 pc1 M model s sm cr LK Aw M1v.
intros SO MS MG FRZ NEXT.
pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
unfold PMSPA.cfg.
apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v K HH AM MS MG FRZ).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (E : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
apply NEXT. split; [exact MR|]. split; [exact SV|]. split; [exact LC|]. split; [exact PA|]. split; [exact IA|]. split; [exact BASE|].
split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|].
split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|]. split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK].
Qed.
Lemma vpack : ltac2:(TCodec.tc2 tcn__PmBSrd1 "UC'U2yR0%211':y8%511%311p051'M'RB'RJ&Q9'7&Q>%211'<'C%2211%611&R7r7r6r5r4r3r2r1%877654321'4p0K1&Q<%126;&Q7r9%2281'=&QA+RPP0+QVhP0%33=21&QG&SC+QWbaH+QoooPP0%443B21&QF+QWbb0+1%347F21&SJ+SoomohPTV0vSD%3221&SN+2+Q?%3221%8261%G261'>&SL+@%22;1z%53Q@21&QH&SO+V0%22A1%44LQ;12%Q3261%Q42=1+8%H21Q@%I2QA7%Q8221r=%;2JQE%Q64Q521QE%=2LQH%Q84Q7QJ1QHp031p071pZ@R31pXLR41+Vb\P0&R5%Q6221+SooooooofH%Q8231%QG231%O25C%Q13R<1M'A&SH+QoonlP0+`PPPPPTP0%3221%QA21<+Y8%62>1%QD216%9241%R42;1%R52>1&QK&SI%=2EQ3%221Q4%?21R2+Q4%63RE21%Q?4R7RFJ=%R02KRH%D2RJRI%R221?&QJ%13S0RNRMp031p061pY:S81pX8S91&R8%R:2Q61+Soooooooo8%R<231%RK231%R325QG%R53S@1R1%R@2Q07+H%Q5291%RC21Q5%Q8241%S3261%S4291%N2>R0%Q;21RN+3%Q23SA21%R;4S3SBB:%RL2CSD%RM2L;p01Jp031pY:T11pX8T21%S22Q?R?%S32AR@&S1vD%231R1QD%332NF%SF221%SG261%SH281%SI2:1%SJ2A1%SK2C1%SL2H1%SM2Q71%SN2QA1%SO2QC1%T02QK1%T12R@1%T22RN1%T32SF1%T42SK1%T52T11tR8U2T71tQ<T=T;1p0T@1p2TJ1pQHTO1pX<U31pYLU51pYHU71pY4U91pR0U;1").
Proof using All. intros M model s sm cr LK Aw.
intros (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK) H MV.
pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model S 22528 192 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
pose proof (PMBSK.src_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s S 22528 HH FOK PA STK)
as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
pose proof (PMBRSK.tb_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s HH FOK PA)
as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & AT & TFS1 & TFS2).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VIS & _).
fold os in O1, O8, OBIG, OZ, OW, OCE, OAV, AO. fold tb in T1, T8, TBIG, TZ, TW, TCE, TAV, AT.
split; [exact V0|]. split; [exact V1|]. split; [exact V2|].
split; [split; [lia| split; [exact A16| exact V3]]|].
split.
{ intros k v Hk X. apply (proj2 (L5A.u64_at_vis H M (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
split; [split; [lia| split; [exact O8| exact OBIG]]|]. split; [exact OZ|]. split; [exact OW|]. split; [exact OAV|].
split; [split; [lia| split; [exact T8| exact TBIG]]|]. split; [exact TZ|]. split; [exact TW|]. split; [exact TAV|].
split; [lia|]. split; [lia|]. split; [exact AO| exact AT].
Qed.
Lemma eof_step : ltac2:(TCodec.tc2 tcn__PmBSrd1 "T0'S;&Ny5'U2yR0%211%5241'C':y8%711%311p071'M'RB'RJ&Q9'7&Q>%211'<%12>>%511&R7r8r7r6r5r4r3r2%877654321'Q8&SC&S=r?r=&U1r<%22Q31&Q7&Q<%12=Br9%4221&S>%11=%=5<;831r>r;r:%>2Q?1%B5431F6%E3D61&S@%>2K<%@216%321L'=&SJzr1%3221&SK&SN+2+R0%3221%5271%;271&@&SOvSD+UH%3221%@21Q=&SH+8%2241%@2QA1%F251%;11'>%Q>2R?QF%QK11%Q<2QMQA%Q>31Q63%53R<31p071p0D1pX8RC1%R47QMNQEQ:Q9Q@R3'S?&QIvSE%211&S2rDrAr@%46R3321R7R6vG%:4R5721p0<1pY8RK1pR4RM1rC%;6R:198R7R5%@4R;=17p041p0D1p0QF1p0QK1p0RB1pR6S61p2RM1pQHS11pX<S51pYLS71pYHS91pY4S;1pR0S=1pYBSC1pR>SE1pY@SE1pR:SG1pXHSN1pXDSO1").
Proof using All. intros fx fx1 R pc R1 pc1 M model s sm cr LK Aw M1v.
intros SO MS MG FRZ NEXT.
pose proof SO as ((EK & DK & STK) & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof geo as (Eop & Eos & Eois & Etb). pose proof fbb as (F1024 & rs & Hfb).
set (P := fun a => S - 184 <= a < S - 184 + 8).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v P K HH AM MS MG).
{ intros a Ha N. apply FRZ; [exact Ha| exact N]. }
{ intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
apply NEXT.
assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 184 \/ S - 176 <= a) -> L5C.agree_on M M1 a n).
{ intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; lia]. }
pose proof (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
assert (EKn : L5SAR.ek L ar LBX FF S 22528 W0 M M1).
{ apply (L5SAR.ek_piece L ar LBX FF S 22528 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
intros a Ha CA OWx Pa. unfold P in Pa.
destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 22528 a HH SPT (L5SAR.aclient_appb L ar LBX (PM.parser_own s) FF S 22528 a CA)) as [X|X]; lia. }
assert (EKp : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 22528 [] M M1).
{ apply (L5SAR.ek_piece L ar _ FF S 22528 [] M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
intros a Ha CA OWx Pa. unfold P in Pa.
destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ S 22528 a HH SPT CA) as [X|X]; lia. }
assert (AOP : PMSPA.aobjA FF op 384).
{ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (AOI : PMSPA.aobjA FF ois 272).
{ exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
pose proof (PMBSK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 4) with 1024 in FF2. unfold FS_BYTES in FF2.
split; [split; [|split]|].
- exact (L5SAR.ek_trans L ar LBX FF S 22528 W0 M0 M M1 EK EKn).
- apply (L5SAR.dk_trans L ar LBX FF S 22528 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
- exact (L5SAR.astk_grows ar M M1 S 22528 STK MGM1).
- split.
{ destruct SV as (S8 & S16' & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption]). }
split.
{ destruct LC as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption]). }
split; [apply (PMKB.parser_keepA RSEGS AD L ar _ FF S 22528 [] M M1 EKp PMKB.wapp_nil FRB BRB _ _ _ AOP); [apply incl_appl, incl_refl| intros i _ r0 []| | | |exact PA]|].
{ intros i _ r0 []. } { intros i _ r0 []. } { intros c0 n0 p0 _ i _ r0 []. }
split; [apply (PMKB.iss_keepA RSEGS AD L ar _ FF S 22528 [] M M1 EKp PMKB.wapp_nil FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]|].
split; [apply (PMBSK.base_keep L ar C LY LBX FF S 22528 W0 M M1 EKn); [intros a Ha; apply outside_W0; lia| exact BASE]|].
split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK].
Qed.
Definition lstate (R : bvmap 5 word) (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) (w : Z) : Prop :=
lregs R w /\ st_ok M model s sm cr LK Aw /\ acct s sm w /\ 1 <= w <= len.
Definition IHt (mu0 : Z) : Prop :=
forall (fx : FPState) R M model s sm cr LK Aw w, PM.mu_src (PM.p_src s) sm < mu0 -> lstate R M model s sm cr LK Aw w ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb3274 M model) K.
End Call.
End WithHeap.
End PMBSR1.
