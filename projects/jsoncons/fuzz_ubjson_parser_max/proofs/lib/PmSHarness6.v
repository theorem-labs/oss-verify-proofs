(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmTopS PmSHarnessStmts PmSHarnessKit PmSHarnessP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSHarness6 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarnessStmts.PMH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1list"; "1nil"; "1option"; "2eq"; "3Z"; "0HI"; "0K"; "0L"; "0LB0"; "4Model"; "4event"; "5bvmap"; "0M"; "0M0"; "0M1"]; ["0R"; "0R0"; "0R1"; "6credit"; "7SCFG"; "8p_src"; "8p_tb"; "8pst"; "8strm"; "8vstr"; "9H5"; "9H6"; ":cfg"; ";opdel_spec"; "<FPState"; "=srealizes"]; [">loaded_segments"; "0SCFG_P"; "?modulo"; "0be"; "0cr"; "0cr0"; "0fx"; "0fx1"; "0g"; "0model"; "0model0"; "0model1"; "0n"; "0p"; "0ra"; "0s"]; ["0s2"; "0sm"; "0sp"; "@bv"; "0x"]]).
Module PMH6.
Import PMS. Import PMH.
Local Ltac lia := PMK.alia.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ra n : Z).
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PMST.st.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis Hcr0 : PMSP.credit_le (512, 2 ^ 29 + 8 * n) cr0.
Hypothesis Hgp : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Htp : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Lemma m16_2 : ltac2:(TCodec.tc2 tcn__PmSHarness6 ">'5'4&Q2r1+@%3221z%63721r2+2%8221%:3;15p051pS:=1").
Proof. intros x. intros H. apply Z.mod_divide in H; [|lia]. destruct H as (q & ->). replace (q * 16) with ((q * 8) * 2) by lia. apply Z.mod_mul. lia. Qed.
Lemma stage6 : ltac2:(TCodec.tc2 tcn__PmSHarness6 "RM&MvQ1v8v6%43321'N&<y5'QCyR0%211%5241'3y8%611%311p061':&C'I'G'H'0'1';%211!pS:21&JvAv>vQ:vQBvQ>vQ<v9vQ5vQ8r:r9r8r7r6r5r4r3r2%CDQ=Q<BA@?>=<;:987654321(2%11I%411&Kr1r=r<r;&F%11C&E%11E%9EQJQIONMLKJIHG?>876531ED'O&Q0&D%11QO&L+V`XD%265HG1FE%74641Lp091pRHQE1pQ0QG1pQ6QM1pR@R41r>+V`W@%;6>2G1FE%@4?=1Q1p051p0M1p0Q11p@QF1pR8QL1pS4QN1pRLR01pS2R21pS0R31pR:R51pRDR71pLR91pQ2R?1pR>RF1p0RH1").
Proof using All.
intros OPD fx R M model cr s s2 p sm be K (CORE & VS & SZ & IA & PA & HST & EMONO & HH & CK) K0 KONT.
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
set (LBc := PM.parser_own p ++ LBX) in *.
set (LB6 := PM.src_own (PM.p_src p) ++ PM.vs_own (PM.p_tb p) ++ LBX).
assert (BRc : PMHK.brange L LBc) by (apply (PMHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
assert (LBhic : forall x, In x LBc -> fst x + snd x <= hl_ceil L) by (intros (B & m) Hx; destruct (BRc B m Hx) as (_ & _ & Q); exact Q).
assert (SCx : 0 <= 65536 - 752) by lia.
unfold PMH.fb, FRAME in PA.
destruct PA as (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & _).
destruct VEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
set (b := PM.p_b p) in *. set (k := PM.p_k p) in *.
assert (Bv : In (b, 32 * 2 ^ k) LBc) by (unfold LBc, PM.parser_own, PM.src_own, PM.vec_own; cbn; auto).
assert (Bq : In (PM.sr_qc (PM.p_src p), PM.CHUNK) LBc) by (unfold LBc, PM.parser_own, PM.src_own; cbn; auto).
destruct (BRc _ _ Bv) as (Vb0 & Vb1 & Vb4). pose proof (PM.pow2_pos k ltac:(lia)) as P2k.
replace (sp - 752 + 40 + 360) with (sp - 352) in V0 by lia. replace (sp - 752 + 40 + 360 + 16) with (sp - 336) in V16 by lia.
pose proof (m16_2 b Hal) as Hal2.
cfeed P (PMSHP.hnG_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => b | 34%nat => b + 32 * 2 ^ k | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ0 & MS & KS & A1 & A10 & A11 & C0 & C1)); PMK.pvz_clrT.
set (P := fun a => (sp - 712 <= a < sp - 712 + 8) \/ (sp - 344 <= a < sp - 344 + 8)).
assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
assert (PF : forall a, P a -> PMH.fb sp <= a < PMH.fb sp + 752) by (intros a [X|X]; unfold PMH.fb, FRAME; lia).
unfold PMSP.cfg.
apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x340f0 R1 0x54400 M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
{ intros a Pa. apply PF in Pa. unfold PMH.fb, FRAME in Pa. left. lia. }
{ intros a. apply PMK.or_dec; apply PMK.rng_dec. }
intros HH1.
assert (CORE1 : PMH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
{ apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 P CORE MG FRZ); [intros a [X|X]; unfold PMH.fb, FRAME; lia| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k0 Hk0. apply KS. revert k0 Hk0. apply PMH.CSK_in. vm_compute. reflexivity. }
assert (VS1 : PM.vstr_at RSEGS PMH.T3 M1 (sp - 752 + 712) s).
{ eapply (PMHK.vstr_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [lia|lia| | |exact VS].
- intros i Hi [X|X]; lia.
- unfold LBc, LBX. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
assert (IA1 : PM.iss_at RSEGS AD PMH.T3 M1 (sp - 752 + 440) s2 sm).
{ eapply (PMHK.iss_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [lia|lia| | |exact IA].
- intros i Hi [X|X]; lia.
- unfold LBc, LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
assert (TB1 : PM.vstr_at RSEGS PMH.T3 M1 (sp - 752 + 40 + 336) (PM.p_tb p)).
{ eapply (PMHK.vstr_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [lia|lia| | |exact TB].
- intros i Hi [X|X]; lia.
- unfold LBc, PM.parser_own. apply incl_appl. apply incl_appr. apply incl_appr. apply incl_refl. }
assert (SRC1 : PM.src_fields_at RSEGS PMH.T3 M1 (sp - 752 + 40 + 24) (sp - 752 + 440) (sp - 752 + 440 + 16) (PM.p_src p)).
{ eapply (PMHK.src_keep_p L sp LBc M M1 P (65536 - 752) FRZ PF STK SCx BRc); [lia|lia| |exact Bq|exact SRC]. intros i Hi [X|X]; lia. }
assert (NI1 : PM.nullis_at RSEGS AD PMH.T3 M1 (sp - 752 + 40 + 32)).
{ eapply (PMHK.nullis_keep_p M M1 P FRZ); [lia|lia| |exact NI]. intros i Hi [X|X]; lia. }
assert (HST1 : PMH.hstat M1 true true be) by (apply (PMHK.hstat_piece L LY sp LBc M M1 P FRZ PF true _ _ STK LBhic HST)).
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M1 model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
pose proof CORE1 as (_ & Hcs1 & _).
assert (STKd : L5C.stk (hl_sptop L) M1 (sp - 752) PMSP.OPDEL_SCR).
{ apply (PMK.stk_call L M1 (sp - 752) (65536 - 752) (sp - 752) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
apply (OPD fx1 R1 M1 model K LBc cr b (32 * 2 ^ k) (sp - 752) 213268 HH1).
{ repeat split; assumption. }
{ exact K0. }
{ exact Bv. }
{ rewrite L5K.rl10. exact A10. }
{ rewrite L5K.rl1. exact A1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. exact Rsp1. }
{ rewrite L5K.rl4. rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto). exact Htp. }
{ exact STKd. }
intros fx2 R2 M2 model2 RP HP MB HH2.
assert (ELB : lb_remove b LBc = LB6).
{ pose proof (proj1 (proj2 (hio_wf L SCFG HI HIok LBc cr M _ HH))) as ND.
unfold LBc, LB6, PM.parser_own, PM.src_own, PM.vec_own in *. cbn [app map fst] in *. fold b k in ND |- *.
cbn [lb_remove fst]. inversion ND as [|x0 l0 NI0 ND0].
destruct (Z.eqb (PM.sr_qc (PM.p_src p)) b) eqn:EQ; [apply Z.eqb_eq in EQ; exfalso; apply NI0; rewrite EQ; constructor|].
rewrite Z.eqb_refl. reflexivity. }
rewrite ELB in HP, HH2.
assert (EKd : PMK.ek L LB6 (sp - 752) PMSP.OPDEL_SCR [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP).
assert (SCd : 0 <= PMSP.OPDEL_SCR) by (unfold PMSP.OPDEL_SCR; lia).
assert (BR6 : PMHK.brange L LB6) by (apply (PMHK.brange_of_heap L HI LY HIok LB6 LB6 cr M2 _ HH2); apply incl_refl).
assert (WSTD : forall a, PMK.inW [] a -> PMH.fb sp <= a \/ 65536 <= a < 954368) by (intros a (r & [] & _)).
assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
apply (KONT fx2 R2 M2 model2). unfold PMH.H6, PMH.fb, FRAME.
split. { apply (PMHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M1 model R2 M2 model2 LB6 PMSP.OPDEL_SCR [] CORE1 RP HP);
[unfold LB6, LBX; apply incl_appr; apply incl_appr; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
intros a I. destruct (N0 a I). }
split. { eapply (PMHK.vstr_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact VS1].
- intros i _. apply N0.
- unfold LB6, LBX. apply incl_appr. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
split; [exact SZ|].
split. { eapply (PMHK.iss_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact IA1].
- intros i _. apply N0.
- unfold LB6, LBX. apply incl_appr. apply incl_appr. apply incl_appl. apply incl_refl. }
split. { replace (sp - 752 + 376) with (sp - 752 + 40 + 336) by lia.
eapply (PMHK.vstr_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact TB1].
- intros i _. apply N0.
- unfold LB6. apply incl_appr. apply incl_appl. apply incl_refl. }
split. { replace (sp - 752 + 64) with (sp - 752 + 40 + 24) by lia. replace (sp - 752 + 456) with (sp - 752 + 440 + 16) by lia.
eapply (PMHK.src_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd BR6 WSTD); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| | |exact SRC1].
- intros i _. apply N0.
- unfold LB6, PM.src_own. cbn. auto. }
split. { replace (sp - 752 + 72) with (sp - 752 + 40 + 32) by lia.
eapply (PMHK.nullis_keep L LY sp LB6 PMSP.OPDEL_SCR [] M1 M2 EKd STKd SCd); [unfold PMH.fb, FRAME; lia|unfold PMH.fb, FRAME; lia| |exact NI1]. intros i _. apply N0. }
split. { apply (PMHK.hstat_keep L LY LB6 (sp - 752) PMSP.OPDEL_SCR [] M1 M2 EKd); [|exact HST1]. intros a I. destruct (N0 a I). }
split; [exact EMONO|]. split; [exact HH2| exact CK].
Qed.
End Stage.
End PMH6.
