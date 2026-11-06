(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegFastLoad SegFastCopy SegFastHavoc FxBlock FxCarry FxExec.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SegPlanFast () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanCore.APC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegPlan.SGP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegPlanFast.SGF."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegPlanFast.SGF.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegRun.SR."; "Stdlib.Lists.List."], [["0A"; "0BF"; "0BFUEL"; "0BR"; "1bool"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2eq"; "3Z"; "0F"; "0IT"; "4Segment"; "0PSS"]; ["5atable"; "5copy_facts"; "5kn_havoc"; "6expr"; "6itab"; "6kentry"; "6sym_state"; "7bfact"; "7cert_ok"; "7region"; "7splan"; "7step1"; "7went_withinX"; "7within1X"; "7withinX"; "9step_block_f"]; ["8cert_ok_fast"; "8cert_ok_g"; "8copy_factsM"; "8step1_f"; "8step1_g"; "8step_block_f"; "8went_withinX_f"; "8within1X_f"; "8withinX_f"; ":post_spec"; ":sstep"; ":step_block"; ":went"; ";forallb"; "0XSTEP"; "0XSTEP'"]; ["0XSTEP2"; "0b"; "0db"; "0dk"; "0fuel"; "0g"; "0k"; "0kn"; "0kn0"; "0n"; "0nx0"; "0p"; "0pc0"; "0r"; "0rh"; "0rl"]; ["0ro_hi"; "0ro_lo"; "0sb"; "0segs"; "0sk"; "0sr0"; "0ss"; "0st"; "0stops"; "0w"; "0x_cpy"; "0x_len"; "0x_set"; "0xc"; "0xl"; "0xs"]]).
Module SGF.
Fixpoint existsb_l {A : Type} (f : A -> bool) (l : list A) : bool :=
match l with [] => false | a :: r => if f a then true else existsb_l f r end.
Lemma existsb_l_eq : forall A (f : A -> bool) l, existsb_l f l = existsb f l.
Proof. induction l as [|a r IH]; cbn; [reflexivity|]. rewrite IH. destruct (f a); reflexivity. Qed.
Fixpoint forallb_l {A : Type} (f : A -> bool) (l : list A) : bool :=
match l with [] => true | a :: r => if f a then forallb_l f r else false end.
Lemma forallb_l_eq : forall A (f : A -> bool) l, forallb_l f l = forallb f l.
Proof. induction l as [|a r IH]; cbn; [reflexivity|]. rewrite IH. destruct (f a); reflexivity. Qed.
Definition within1X_f (kn : list kentry) (b : expr) (k n : Z) (r : SGP.region) : bool :=
let '(rb, rlo, rlen) := r in
if (match rlen with
| ELit m => if Z.leb 0 m then (if Z.ltb m two64 then SR.within1 b k n (rb, rlo, m) else false) else false
| _ => false
end) then true else xinside kn b k (ELit n) rb rlo rlen.
Lemma within1X_f_eq : ltac2:(TCodec.tc2 tcn__SegPlanFast "G'5'E%211'C';&I':'4&Q7r5r4r3r2r1%6554321&M%1576543%;3:31pSL=1pSD?1pS>@1pS4B1pS@D1").
Proof.
intros kn b k n [[rb rlo] rlen]. unfold within1X_f, SGP.within1X.
destruct rlen; try reflexivity. destruct (Z.leb 0 z); [|reflexivity]. destruct (Z.ltb z two64); reflexivity.
Qed.
Definition withinX_f (kn : list kentry) (F : list SGP.region) (b : expr) (k n : Z) : bool :=
if Z.ltb 0 n then (if Z.ltb n two64 then existsb_l (within1X_f kn b k n) F else false) else false.
Lemma withinX_f_eq : ltac2:(TCodec.tc2 tcn__SegPlanFast "H'5'E%211&I%411'C';':'4&Q8r5r4r3r2r1%6554321&N%1576543%;3:31pSD=1pS>>1pS4@1pJB1pS@E1").
Proof.
intros. unfold withinX_f, SGP.withinX. rewrite existsb_l_eq.
replace (within1X_f kn b k n) with (SGP.within1X kn b k n) by (apply functional_extensionality; intros; symmetry; apply within1X_f_eq).
destruct (Z.ltb 0 n); [|reflexivity]. destruct (Z.ltb n two64); reflexivity.
Qed.
Definition went_withinX_f (kn : list kentry) (F : list SGP.region) (g : SR.went) : bool :=
match g with
| SR.WSt (SA b k) wd _ => withinX_f kn F b k (Z.of_nat wd)
| SR.WCopy db dk _ _ n => withinX_f kn F db dk n
| SR.WFill db dk n _ => withinX_f kn F db dk n
end.
Lemma went_withinX_f_eq : ltac2:(TCodec.tc2 tcn__SegPlanFast "C'5'E%211&I%411'Q<':'4&Q6r3r2r1%43321&L%13543%93831pS<;1pJ=1pS@@1").
Proof. intros kn F [[b k] wd v|db dk sb sk n|db dk n c]; cbn [went_withinX_f SGP.went_withinX]; apply withinX_f_eq. Qed.
Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable x_cpy x_set x_len ro_lo ro_hi : Z.
Variable BFUEL : nat.
Definition step_block_f (stops : list Z) (ss : sym_state) (w : list SR.went) : option (sym_state * list SR.went) :=
let bc := BLKF.mkbc_m (facts_of (s_know ss)) in
let '(ss', scs) := EXF.sym_execTXBIFL segs bc (s_know ss) (CARF.mk_bext bc) IT 0%nat BFUEL true stops ss in
match CARF.carryKF_ctx bc (s_log ss') scs (s_know ss') [] with
| (kn', [], _) => Some (SS (s_pc ss') (s_regs ss') [] kn' (s_next ss'), SR.wlog (s_log ss') ++ w)
| _ => None
end.
Lemma step_block_f_eq : ltac2:(TCodec.tc2 tcn__SegPlanFast "I'5';%211'F'Q<%511':'7'8%1264%311&Or3r2r1%43321&Q;vR3v=v2%46321876%?3;61pTDA1pT>D1pTBF1").
Proof.
intros. unfold step_block_f, SR.step_block. rewrite EXF.sym_execTXBIFL_eq. rewrite BLKF.mkbc_m_eq, BLKF.mk_kix_f_eq.
rewrite EXF.sym_execTXBIF_eq by (first [reflexivity | eexists; reflexivity]). rewrite CARF.carryKF_ctx_eq, CARF.carryKF_eq.
rewrite (sym_execTXBI_eq segs (s_know ss)) by reflexivity.
rewrite <- (sym_execTX_know segs IT 0%nat BFUEL true stops ss) at 1.
rewrite carryK_eq. reflexivity.
Qed.
End WithSegs.
Ltac has_const t c := lazymatch t with context [c] => idtac | _ => fail "abstraction target does not occur:" c end.
Definition copy_factsM := AX2Y.copy_factsM2.
Lemma copy_factsM_eq : ltac2:(TCodec.tc2 tcn__SegPlanFast "F':'5'>%211'6'E%511'C';'7%114pSD31pS841pS661pT:61pT681pS>:1pS:=1pT8?1&Q2&A%E3321").
Proof. exact AX2Y.copy_factsM2_eq. Qed.
Lemma step_block_f_eqf : ltac2:(TCodec.tc2 tcn__SegPlanFast "H':'5'>%211&D'6';%611'F'Q<%911'7'8%1253%311pTD51pT>81pTB:1p6=1pL?1pT8A1&Q5&Q;%G3321").
Proof. repeat (apply functional_extensionality; intros ?). apply step_block_f_eq. Qed.
Lemma went_withinX_f_eqf : ltac2:(TCodec.tc2 tcn__SegPlanFast ">':'5'E%211&I%411'Q<'4pS<21pJ41pS@71&Q6&L%=3321").
Proof. repeat (apply functional_extensionality; intros ?). apply went_withinX_f_eq. Qed.
Lemma existsb_l_eqf : @existsb_l = @existsb.
Proof. apply functional_extensionality_dep; intros A. repeat (apply functional_extensionality; intros ?). apply existsb_l_eq. Qed.
Lemma forallb_l_eqf : @forallb_l = @forallb.
Proof. apply functional_extensionality_dep; intros A. repeat (apply functional_extensionality; intros ?). apply forallb_l_eq. Qed.
Definition step1_g :=
ltac:(let t := eval cbv beta delta [SGP.step1 SR.seg_step SR.step_copy SR.step_fill] in @SGP.step1 in
has_const t (@SR.step_block); has_const t (@APC.kn_havoc); has_const t (@APC.copy_facts); has_const t (@SGP.went_withinX); has_const t (@forallb);
let t' := eval pattern (@SR.step_block), (@APC.kn_havoc), (@APC.copy_facts), (@SGP.went_withinX), (@forallb) in t in
lazymatch t' with ?F _ _ _ _ _ => exact F end).
Lemma step1_g_ref : ltac2:(TCodec.tc2 tcn__SegPlanFast "Q1':'5'>%211&D';'6&I%711'Q:'F'7%112pT>31pT@51pJ71p6:1pT2<1pT4=1pTH>1pTJ?1pTF@1pLB1pT8D1&Q4&Q;&B&A&L&Q=%6554321&K%Q03921").
Proof. reflexivity. Qed.
Definition step1_f := step1_g step_block_f AX2H.kn_havocMF copy_factsM went_withinX_f (@forallb_l).
Lemma step1_f_eqf : ltac2:(TCodec.tc2 tcn__SegPlanFast "K':'5'>%211&D';'6&I%711'Q:'F'7%112pT>31pT@51pJ71p6:1pT2<1pT4=1pTH>1pTJ?1pTF@1pLB1pT8D1&Q3&K%J3321").
Proof. unfold step1_f. rewrite step_block_f_eqf, AX2H.kn_havocMF_eq, copy_factsM_eq, went_withinX_f_eqf, forallb_l_eqf. exact step1_g_ref. Qed.
Definition cert_ok_g :=
ltac:(let t := eval cbv beta delta [SGP.cert_ok SGP.check] in @SGP.cert_ok in
has_const t (@SGP.step1);
let t' := eval pattern (@SGP.step1) in t in
lazymatch t' with ?F _ => exact F end).
Lemma cert_ok_g_ref : ltac2:(TCodec.tc2 tcn__SegPlanFast "QK':'5'>%211&D';'6'@'G%811'8'C%2217%3212%=11'F'7%112p031p0=1p061%;266%611p081p0B1p0;1&I%J11'Q9%L11'J%N1D'E%Q011'4pSB21pT<51pSJQ01pSH81pQ0:1pJ=1pS2@1pRNF1p8Q21pSFQ61p2Q61p6Q81pT2Q:1pT4Q;1pTHQ<1pTJQ=1pTFQ>1pLQ@1pT8QB1&Q1&K%211&H%QJ3521").
Proof. reflexivity. Qed.
Definition cert_ok_fast := cert_ok_g step1_f.
Theorem cert_ok_fast_eq : ltac2:(TCodec.tc2 tcn__SegPlanFast "QI':'5'>%211&D';'6'@'G%811'8'C%2217%3212%=11'F'7%112p031p0=1p061%;266%611p081p0B1p0;1&I%J11'Q9%L11'J%N1D'E%Q011'4pSB21pT<51pSJQ01pSH81pQ0:1pJ=1pS2@1pRNF1p8Q21pSFQ61p2Q61p6Q81pT2Q:1pT4Q;1pTHQ<1pTJQ=1pTFQ>1pLQ@1pT8QB1&Q0&H%QH3321").
Proof. unfold cert_ok_fast. rewrite step1_f_eqf. exact cert_ok_g_ref. Qed.
Lemma cert_of_fast : ltac2:(TCodec.tc2 tcn__SegPlanFast "RB'5'>%211&D';'6'@'G%811'8'C%2217%3212%=11'F'7%112p031p0=1p061%;266%611p081p0B1p0;1&I%J11'Q9%L11'J%N1D'E%Q011':'4&Q0rCrBrAr@r?r>r=r<r;r:r9r8r7r6r5r4r3r2r1%DCCBA@?>=<;:987654321(9%H3G21&HrD%2C1HGFEDCBA@?>=<;:987%L3K15p051pSBO1pT<Q21pSJQM1pSHQ51pQ0Q71pJQ:1pS2Q=1pRNQC1p8QO1pSFR31p2R31p4R51pSNR71pT0R81pTNR91pU0R:1pTLR;1pLR=1pT8R?1").
Proof. intros until kn0. rewrite cert_ok_fast_eq. exact (fun H => H). Qed.
Lemma cert_by_fast : ltac2:(TCodec.tc2 tcn__SegPlanFast "RE'5&I%211'6'F'7%112p031p051p071':r2r1%33421'>%?11&D';'@'G%D11'8'C%2216%3212%I11%52FF%F11p0H1p0J1p051'Q9%Q011'J%Q21<'E%Q411'4&Q0rBrAr@r?r>r=r<r;r:r9r8rEr7r6r5r4r3%BCA@?>=<;:987654321Q=Q<(9%Q@3E21&HrC%2C1FEDCBA@?>=;<:9876QB%QD3I15p051pSBL1pT<O1pSJQA1pSHQ21pQ0Q41pJR31pS2Q81p8QC1pSFR51p2QG1p4R71pSNQJ1pT0QK1pTNQL1pU0QM1pTLQN1pLR01pT8R21p0R51pRNR:1pS0R;1").
Proof. intros XSTEP' XSTEP <-. intros. apply cert_of_fast. assumption. Qed.
End SGF.
