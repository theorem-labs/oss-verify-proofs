(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit PmLayout PmLayoutS PmModel PmModelFacts PmStatics PmSpecs PmSpecsS PmStep PmKeep PmKitS PmTopS PmSHarnessStmts PmSHarnessKit PmSHarnessP.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmSHarness9 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarness9.PMH9.Stage."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSHarnessStmts.PMH."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsS.PMS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTopS.PMTS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1length"; "1list"; "1nil"; "1option"; "2eq"; "2not"; "3Z"; "0HI"; "0K"; "0L"; "0LB0"; "4Model"; "4event"; "4m_vmmaps"; "5bvmap"]; ["0M"; "0M'"; "0M0"; "0M1"; "0R"; "0R'"; "0R0"; "0R1"; "6credit"; "6hi_heap"; "6model_but_vm"; "8outside"; "7SCFG"; "9in_foot"; "9lib_post"; ":vstr"]; [";H9"; "<H8"; "<WF"; "=cfg"; ">opdel_spec"; "?st"; "@TopLS"; "@TopLay"; "AFPState"; "Bsrealizes"; "Cloaded_segments"; "0SCFG_P"; "Dof_nat"; "0a"; "0be"; "0cr"]; ["0cr'"; "0cr0"; "0fx"; "0fx'"; "0fx1"; "0g"; "0g'"; "0model"; "0model'"; "0model0"; "0model1"; "0n"; "0payload"; "0ra"; "0s"; "0sp"]; ["Ebv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMH9.
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
Hypothesis Hsp0 : getr R0 (reg 2) = Z_to_bv 64 sp.
Hypothesis Hra : L5.ra_ok ra.
Definition H9 (R : bvmap 5 word) (M : word -> option byte) (model : Model) (cr : credit) (be : bool) : Prop :=
(exists Rm, PMH.hcore L R0 M0 model0 sp ra LB0 Rm M model)
/\ getr R (reg 1) = Z_to_bv 64 ra /\ getr R (reg 2) = Z_to_bv 64 sp /\ getr R (reg 8) = getr R0 (reg 8) /\ getr R (reg 10) = Z_to_bv 64 0
/\ (forall k, In k CSK -> getr R (reg k) = getr R0 (reg k))
/\ PMH.hstat M true true be /\ (PMST.st_err g = true -> be = true)
/\ hi_heap HI LB0 cr M (m_vmmaps model)
/\ PMSP.credit_keep cr0 cr (PMH.P0 L n) PMSP.cr0.
Lemma s_gone : ltac2:(TCodec.tc2 tcn__PmSHarness9 "RA&Q4vQ;v:v8%43321'Q8&?y5'R0yR0%211%5241'4y8%611%311p061'<&H'O'0'2'=%211!pT421&Q1vFvBvQIvQOvQMvQKv;vQAvQEr7r6r5r4r3r2%@AQ8Q7?>=<;:987654321(3%11F%411&Q0r1r:r8%45:9321'Q9&Q:&L%11QE&Q3+V`_0%265CB1A@%746419p091pSFQ;1pQ8Q=1pQ@QC1pS:QJ1r;+V`]Dr9%<6?3C21B%A4@>1Mp061p0I1p0M1pDQ?1pRNQE1pSNQG1pS0QI1pS@QK1pQ2QM1pQ:R31pS6R:1p0R<1").
Proof using All.
intros OPD fx R M model cr s be K (CORE & VS & HST & EMONO & HH & CK) K0 KONT. unfold PMH.hcore8 in CORE.
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
pose proof STK as (A16f & SLO & SHI & STOP & _).
pose proof CORE as (_ & Hcs & SRA & SS0 & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
unfold PMH.fb, FRAME in VS, SRA, SS0.
pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as Hs0. change (bv_modulus 64) with (2 ^ 64) in Hs0.
assert (ES0 : Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) = getr R0 (reg 8)) by (apply Z_to_bv_bv_unsigned).
set (s0v := bv_unsigned (getr R0 (reg 8))) in *.
destruct Hra as (Hra1 & Hra2).
destruct VS as (SD & _ & VS). destruct s as [ns | c ns p].
-
destruct VS as (Hns & SB0).
pose proof (PMF.even_byte ns) as EVB.
cfeed P (PMSHP.hnMs_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => 2 * ns | 38%nat => ra | 39%nat => s0v | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A2 & A8 & A10)); PMK.pvz_clrT.
assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x341b4 R1 0x341e0 M K Mh Ml MS).
apply (KONT fx1 R1 M model). unfold H9. cbn [PM.vs_own app] in HH.
split; [exists R; exact CORE|]. split; [exact A1|]. split; [exact A2|]. split; [rewrite A8; exact ES0|]. split; [exact A10|].
split. { intros k Hk. rewrite <- (Hcs k Hk). apply KS. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
split; [exact HST|]. split; [exact EMONO|]. split; [exact HH| exact CK].
-
destruct VS as (SW0 & SW8 & SW16 & Hns & Hc & Hc2 & SBP & _).
set (LBc := PM.vs_own (PM.VLong c ns p) ++ LB0) in *.
assert (Bt : In (p, c) LBc) by (unfold LBc, PM.vs_own; cbn; auto).
assert (Hc64 : 0 <= c + 1 < 2 ^ 64) by lia.
pose proof (PMF.u8_of_u64 RSEGS M _ _ Hc64 SW0) as SB0.
pose proof (PMF.odd_byte c Hc2 ltac:(lia)) as ODB.
pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)) as HVB.
set (vb := (c + 1) mod 256) in *.
assert (BRc : PMHK.brange L LBc) by (apply (PMHK.brange_of_heap L HI LY HIok LBc LBc cr M _ HH); apply incl_refl).
destruct (BRc _ _ Bt) as (Pb0 & Pb1 & Pb4).
assert (Hp47 : p < 2 ^ 47) by lia.
cfeed P (PMSHP.hnMl_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => vb | 37%nat => p | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10)); PMK.pvz_clrT.
assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x341b4 R1 0x54400 M K Mh Ml MS).
assert (CORE1 : PMH.hcore L R0 M0 model0 sp ra LB0 R1 M model).
{ apply (PMHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M (fun _ => False) CORE MG); [intros a Ha _; reflexivity| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
intros k Hk. apply KS. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & STK1).
pose proof CORE1 as (_ & Hcs1 & _).
assert (STKd : L5C.stk (hl_sptop L) M (sp - 752) PMSP.OPDEL_SCR).
{ apply (PMK.stk_call L M (sp - 752) (65536 - 752) (sp - 752) PMSP.OPDEL_SCR STK1); [lia| unfold PMSP.OPDEL_SCR; lia| unfold PMSP.OPDEL_SCR; lia| exact A16f]. }
unfold PMS.opdel_spec, PMSP.opdel_spec, PMSP.opdel_spec_at in OPD.
apply (OPD fx1 R1 M model K LBc cr p c (sp - 752) 213456 HH).
{ repeat split; assumption. }
{ exact K0. }
{ exact Bt. }
{ rewrite L5K.rl10. exact A10. }
{ rewrite L5K.rl1. exact A1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. exact Rsp1. }
{ rewrite L5K.rl4. rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto). exact Htp. }
{ exact STKd. }
intros fx2 R2 M2 model2 RP HP MB HH2.
assert (ELB : lb_remove p LBc = LB0).
{ unfold LBc, PM.vs_own. cbn [app lb_remove fst]. rewrite Z.eqb_refl. reflexivity. }
rewrite ELB in HP, HH2.
assert (EKd : PMK.ek L LB0 (sp - 752) PMSP.OPDEL_SCR [] M M2) by (apply (PMK.ek_of_hpres L); exact HP).
assert (N0 : forall a, ~ PMK.inW [] a) by (intros a (r & [] & _)).
assert (CORE2 : PMH.hcore L R0 M0 model0 sp ra LB0 R2 M2 model2).
{ apply (PMHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M model R2 M2 model2 LB0 PMSP.OPDEL_SCR [] CORE1 RP HP);
[apply incl_refl| unfold PMSP.OPDEL_SCR, SCR, FRAME; lia| |exact MB].
intros a I. destruct (N0 a I). }
assert (HST2 : PMH.hstat M2 true true be).
{ apply (PMHK.hstat_keep L LY LB0 (sp - 752) PMSP.OPDEL_SCR [] M M2 EKd); [|exact HST]. intros a I. destruct (N0 a I). }
pose proof (PMHK.hcore_facts L R0 M0 model0 sp ra LB0 R2 M2 model2 CORE2) as (_ & Rsp2 & _ & _ & WR2 & _).
pose proof CORE2 as (_ & Hcs2 & SRA2 & SS02 & _ & _ & _ & _ & _ & _ & _ & (Mh2 & Ml2 & Mm2)).
unfold PMH.fb, FRAME in SRA2, SS02. fold s0v in SS02.
cfeed PN (PMSHP.hnN_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 38%nat => ra | 39%nat => s0v | _ => 0 end)) ltac:(first [PMK.sc]).
PMK.pvz_hg ltac:(idtac; destruct PN as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG3 & FR3 & FRZ3 & MS3 & KS3 & A1n & A2n & A8n & A10n)); PMK.pvz_clrT.
assert (EM : M3 = M2) by (apply functional_extensionality; exact FR3). subst M3.
apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x341d0 R3 0x341e0 M2 K Mh2 Ml2 MS3).
apply (KONT fx3 R3 M2 model2). unfold H9.
split; [exists R2; exact CORE2|]. split; [exact A1n|]. split; [exact A2n|]. split; [rewrite A8n; exact ES0|]. split; [exact A10n|].
split. { intros k Hk. rewrite <- (Hcs2 k Hk). apply KS3. revert k Hk. apply PMH.CSK_in. vm_compute. reflexivity. }
split; [exact HST2|]. split; [exact EMONO|]. split; [exact HH2| exact CK].
Qed.
Lemma not_foot_outside : ltac2:(TCodec.tc2 tcn__PmSHarness9 "?'7&6&M&Q7v:%211r1%5221%711&K&Q2r2%3221p051pRL>1").
Proof. intros a.
intros N r Hin Hr. apply N. unfold WF in Hin. apply in_map_iff in Hin. destruct Hin as (iv & <- & Hiv).
exists iv. split; [exact Hiv|]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia.
Qed.
Lemma stage9 : ltac2:(TCodec.tc2 tcn__PmSHarness9 "S:'2'R0y8%211%411'5'7vQK&Q<&1r1%2281%411%83761&Q4vQ;v:v8%43321'Q8&?y5yR0%F11%4231'4%11Gp041'<&H'O'0'=%Q111!pT421&Q1vFvBvQIvQOvQMv;vQAvQEr7r6r5r4r3r2%?AQ3Q2>=<;:Q<987654321(3%11E%411'Q5'N&Q7%11Q:&Q6rC%5<32>CBE1HG=<QC&I&>%11?%35Q@G?A1&J%12LC'Q9&Q:&L%11QH&Q3r9%2651MQ1LKr<%847521p0:1p0=1p0B1pS2QC1pSBQE1pQ4QG1pQ<QK1pS>M1pS8R21r;r:+V`]Dr8%B6E432A1%G4FD1Q;p071p0Q71p0Q;1pDQL1pRNR11pSNR31pS0R51pS@R71pQ2R91pQ:R=1pS6RC1p0RE1p0RK1pSJS51").
Proof using All. intros payload.
intros EN OPD fx R M model cr s be K H8 K0 KONT.
apply (s_gone OPD fx R M model cr s be K H8 K0).
clear fx R M model H8. intros fx R M model ((Rm & CORE) & A1 & A2 & A8 & A10 & KSR & HST & EMONO & HH & CK).
destruct CORE as (_ & _ & _ & _ & STK & DFR & SPT & EK & LBhi & BASE & MB & (Mh & Ml & Mm)).
destruct Hra as (Hra1 & Hra2).
unfold PMSP.cfg.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx R M 0x341e0 (ltac:(oW' 0x341e0%Z)) ra (ltac:(oF' 0x341e0%Z)) ltac:(reflexivity) (ltac:(oD' 0x341e0%Z)) A1 Hra1 Hra2)|].
apply (KONT fx (PMST.ST true true be) R M model cr); [|exact HH|exact MB].
pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PMF.pot_call_le L n HK HB Hn) as (PC1 & PC2).
constructor.
- rewrite <- L5K.rl10 in A10. exact A10.
- apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
destruct Hk as [<-|Hk]; [rewrite A2, Hsp0; reflexivity|].
destruct Hk as [<-|Hk]; [apply KSR; unfold CSK; cbn; auto|].
destruct Hk as [<-|Hk]; [apply KSR; unfold CSK; cbn; auto|].
destruct Hk as [<-|Hk]; [exact A8|].
apply KSR. unfold CSK. cbn. tauto.
- cbn [ll_credit PMTS.TopLay]. rewrite <- EN. unfold PMSP.credit_keep, PMSP.cr0, PMH.P0 in CK. unfold LibIface.credit_le, LibIface.credit_sub, PMTS.TOPK, PMTS.TOPB. cbn [fst snd] in *.
unfold PMF.credit_le in *. cbn [fst snd] in *. lia.
- cbn [ll_heap ll_stack PMTS.TopLay]. intros a Ha CA NF NE. apply EK. split; [exact Ha|]. split; [exact CA|]. split; [exact NE|]. apply not_foot_outside. exact NF.
- cbn [ll_heap ll_stack PMTS.TopLay]. intros a Ha. unfold PMH.fb, FRAME, SCR in *. destruct STK as (_ & _ & _ & _ & DS).
destruct (Z_lt_ge_dec a (sp - 752)) as [X|X].
+ replace a with (sp - 752 - (65536 - 752) + (a - (sp - 65536))) by lia. apply DS. lia.
+ replace a with (sp - 752 + (a - (sp - 752))) by lia. apply DFR. lia.
- destruct HST as (H1 & H2 & H3). split; [exact BASE|]. split; [exact H1|]. split; [exact H2| exact H3].
Qed.
End Stage.
End PMH9.
