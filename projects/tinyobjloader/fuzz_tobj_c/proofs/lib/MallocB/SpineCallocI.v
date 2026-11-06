(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "sv"; "SPUle"; "sobj"; "valuation"; "rw"; "SAlu"; "SVar"; "FcsrFrm0"; "SPBranch"; "SPUlt"; "mkSS"; "rm"; "agree_below"; "rl"; "swf"; "SPAlign"; "SPNot"; "sprop_below"; "@Corelib.Init.Datatypes"; "cons"; "app"; "nil"; "list"; "bool"; "nat"; "prod"; "pair"; "true"; "None"; "false"; "option"; "Some"; "@Corelib.Init.Logic"; "eq"; "not"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI.CSPINE"; "PRODe"; "Jc"; "FACTSe"; "F_hi_e"; "F_lo_e"; "nwc"; "rho_ce"; "sa_c"; "F_arge"; "F_s1e"; "MHe"; "P0e"; "rup8e"; "sb_c"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "ae_calloc"; "malloc_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "KcA"; "Pre_callocI"; "ulink"; "ustop"; "J_alloc_preT"; "calloc_size"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "vSB"; "RT_m1"; "vRIS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "lt"; "sub"; "mul"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "rhoM_of"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@Stdlib.ZArith.ZArith_dec"; "Z_lt_dec"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.
Local Notation U := bv_unsigned.

Section CSPINE.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition Jc (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S41VAInv;VW;Vst;VA;VKc;S42A6").

Definition nwc (rho : valuation) : word := eval rho calloc_size.
Definition rho_ce (A : AA) (rho : valuation) : valuation := ltac2:(tb__ "0|1|
S34S5eVA;S34Vrho;PcM0S2aVrho;A1A3A2G0S6Vrho;G0A2A3").

Lemma rw_set : ltac2:(tb__ "0|1|
S5S33S23Q40A1M0S33S21G0S6S34R4R3R2A3R1A2S18G0L_;S66R1R3A2R2S6R4R1A2X18x2A3Fi;Fv;Fn;Fr;"). Proof. reflexivity. Qed.
Lemma rl_set : ltac2:(tb__ "0|0|
S5S33S23Q40A1S33S21S17S23Q8A1A1SfS34R4R3R2A3R1A2SfR4R1A2A3Fl;Fv;Fn;Fr;"). Proof. reflexivity. Qed.
Lemma rm_set : ltac2:(tb__ "0|1|
S5S33S23Q40A1M0S21G0S1fS23Q8A1A1F_;SdS34R3R2R1A3A1SdR3A1A3Fv;Fn;Fr;"). Proof. reflexivity. Qed.
Lemma rho_ce_agree : ltac2:(tb__ "0|0|
S45S5SeS49R1S2bR2R1A2A3Frho;FA;").
Proof.
  intros A rho. unfold rho_ce. set (r0 := rho_set_rw rho 12%positive (nwc rho)).
  pose proof (rhoM_agree A r0) as HM. revert HM. generalize (rhoM_of A r0). intros rM (Hw & Hl & Hm).
  split; [|split].
  - intros i Hi. rewrite rw_set. destruct (Pos.eqb i 12) eqn:E; [apply Pos.eqb_eq in E; subst i; reflexivity|].
    rewrite <- (Hw i Hi). unfold r0. rewrite rw_set, E. reflexivity.
  - intros l. rewrite rl_set, <- (Hl l). reflexivity.
  - intros a. rewrite rm_set, <- (Hm a). reflexivity.
Qed.

Lemma JMc_agree : ltac2:(tb__ "0|0|
S17S3fA1S40S45S3dS5S5S17S23Q40A1A1S17S59A1S58S5dR9R8A2SeS49R6R5A3S26RbRaR9R8R7R5R4R3A8S26RcRbRaR9R7R6R5R4A8F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho rho' tp tr md HUS Hag (HA & HK & Htp & HU & HB & HN & Htop). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (E12 : eval rho' calloc_size = eval rho calloc_size).
  { rewrite !calloc_size_val. rewrite <- (Hw 12%positive) by (unfold NF; lia). rewrite <- (Hw 13%positive) by (unfold NF; lia). reflexivity. }
  split; [unfold AInv, AInvA in *; rewrite Erm; exact HA|]. split; [exact HK|].
  split; [unfold tp_ok in *; rewrite <- (Hw 24%positive) by (unfold NF; lia); exact Htp|].
  split; [exact (HUS rho rho' Hag HU)|].
  rewrite E12. split; [exact HB |]. split; [exact HN|].
  unfold top_high in *. rewrite <- (Hw 10%positive) by (unfold NF; lia). rewrite <- (Hw V_DEPTH) by (unfold NF, V_DEPTH; lia). exact Htop.
Qed.

Definition PRODe : sv := SMd M_MUL (SVar 13) (SVar 12).
Definition MHe : sv := SMd M_MULHU (SVar 13) (SVar 12).
Definition F_s1e : list sprop := ltac2:(tb__ "0|0|
S14S0S11P9bZ10A2S14S0S3S1S5cA1S4fA2S14S0S3S4fS1S55S55Z7fffff800000S5bA2Z1000A2A1A2S14S0SaS47S51S7S46S4fS1S5bA1A3A3S14S0S3S1Z1A1S25A2S14S0SbS25S1S53Z2Z27A2A1A2S14S0S12SaS47S7S46S8PaA1S1N858A1A3S1Z0A1A3A1S16S0A1A3A3A3A3A3A3A3").
Definition F_arge : list sprop := ltac2:(tb__ "0|1|
S14S0S3S1Z1A1M0S8PcA1A2S14S0S3G0S8PdA1A2S14S0SaS47S2fS1Z0A1A3S14S0S3G0S25A2S14S0SbS25S1S53Z2Z27A2A1A2S16S0A1A3A3A3A3A3").
Definition rup8e : sv := ltac2:(tb__ "0|0|
S7S48S7S46S25S1Z7A1A3S1Zfffffffffffffff8A1A3").
Definition F_hi_e : list sprop := ltac2:(tb__ "0|0|
S14S0S3S1Zfc01A1S25A2S16S0A1A3").
Definition F_lo_e : list sprop := ltac2:(tb__ "0|0|
S14S0SbS25S1Zfc01A1A2S14S0S3S31S1Zfc00A1A2S16S0A1A3A3").
Definition FACTSe (W : list ulink) (st : ustop) : list sprop := ltac2:(tb__ "0|0|
S15S0S15S0S15S0S15S0S3bVW;Vst;A2S39S38A1A3S4eA3S2eA3S2dA3").
Definition sa_c (W : list ulink) (st : ustop) : sstate := ltac2:(tb__ "0|1|
ScS37S35A1S4cS4bS14S1aS19S2A2M0S1bS19S2U4S1S44A1A4S16G0A1A3A2S4aS9S1dS2A1S14S4S3aS15S4S3cVW;A1S36A3A3S15S0S3bVW;Vst;A2S39S38A1A3S49S1eA9").
Definition sb_c (W : list ulink) (st : ustop) : sstate := ltac2:(tb__ "0|1|
ScS37S35A1S4cS4bS14S1aS19S2A2M0S1bS19S2U4S1S44A1A4S16G0A1A3A2S4aS9S1dS2A1S15S4S14S4S3aS15S4S3cVW;A1S36A3A3S50A3S15S0S3bVW;Vst;A2S39S38A1A3S4dS1eA9").
Definition P0e (W : list ulink) (st : ustop) (fx : list sprop) : axst := ltac2:(tb__ "0|1|
S43ScS37S35A1S4cS4bS14S1aS19S2A2M0S1bS19S2U4S1S44A1A4S16G0A1A3A2S4aS9S1dS2A1S15S4S14S4S3aS15S4S3cVW;A1S36A3A3S50A3S15S0S27VW;Vst;A2Vfx;A3S4dS1eA9S16S1aS2S2A2A1A2").

Hypothesis law_die : ltac2:(tb__ "0|0|
S45S5S17S23Q40A1A1S58VAInv;R4R3R2R1A4S63S65S52SdR4A1A2S64Z17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Local Ltac civ_try2F HR n :=
  eapply (civ_nth2 _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Local Ltac civ_any2F HR := first [ civ_try2F HR 43%nat | civ_try2F HR 44%nat | civ_try2F HR 45%nat | civ_try2F HR 46%nat | civ_try2F HR 47%nat | civ_try2F HR 48%nat | civ_try2F HR 49%nat | civ_try2F HR 50%nat | civ_try2F HR 51%nat | civ_try2F HR 52%nat | civ_try2F HR 53%nat | civ_try2F HR 54%nat | civ_try2F HR 0%nat | civ_try2F HR 1%nat | civ_try2F HR 2%nat | civ_try2F HR 3%nat | civ_try2F HR 4%nat | civ_try2F HR 5%nat | civ_try2F HR 6%nat | civ_try2F HR 7%nat | civ_try2F HR 8%nat | civ_try2F HR 9%nat | civ_try2F HR 10%nat | civ_try2F HR 11%nat | civ_try2F HR 12%nat | civ_try2F HR 13%nat | civ_try2F HR 14%nat | civ_try2F HR 15%nat | civ_try2F HR 16%nat | civ_try2F HR 17%nat | civ_try2F HR 18%nat | civ_try2F HR 19%nat | civ_try2F HR 20%nat | civ_try2F HR 21%nat | civ_try2F HR 22%nat | civ_try2F HR 23%nat | civ_try2F HR 24%nat | civ_try2F HR 25%nat | civ_try2F HR 26%nat | civ_try2F HR 27%nat | civ_try2F HR 28%nat | civ_try2F HR 29%nat | civ_try2F HR 30%nat | civ_try2F HR 31%nat | civ_try2F HR 32%nat | civ_try2F HR 33%nat | civ_try2F HR 34%nat | civ_try2F HR 35%nat | civ_try2F HR 36%nat | civ_try2F HR 37%nat | civ_try2F HR 38%nat | civ_try2F HR 39%nat | civ_try2F HR 40%nat | civ_try2F HR 41%nat | civ_try2F HR 42%nat ].

Local Ltac lia_only v := repeat match goal with H : context [v] |- _ => revert H end; clear - v; intros; lia.
Local Ltac wr_cell2F HR n off tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell;
  [ lazymatch goal with |- ?x + _ <= ?x + _ < _ => idtac end; lia_only off | lia | tacW | lia ].
Local Ltac wr_any2F HR off tacW := first [ wr_cell2F HR 43%nat off tacW | wr_cell2F HR 44%nat off tacW | wr_cell2F HR 45%nat off tacW | wr_cell2F HR 46%nat off tacW | wr_cell2F HR 47%nat off tacW | wr_cell2F HR 48%nat off tacW | wr_cell2F HR 49%nat off tacW | wr_cell2F HR 50%nat off tacW | wr_cell2F HR 51%nat off tacW | wr_cell2F HR 52%nat off tacW | wr_cell2F HR 53%nat off tacW | wr_cell2F HR 54%nat off tacW ].

Lemma c_instantiate_e : ltac2:(tb__ "0|a|
S17S3fA1S40S45S3dS5S17S23Q40M0A1A1S60S5dR7R6A2S21S18S10S2cR8R7A2A1S1cA3S21S1fS1aS17S1aS2S2A2M1A1M2S17S0A1M3A2M4A1S61S62S3eS35R9R8A3A1S2cR9R8A2A2S20G4S1bG2G3S14G1S1bS2S2S8P18A1S1S44A1A4S16G1A1A3S16S0A1A4A2A3S21S18S10S32RaR9A2A1S1cA3S21S18S5fS0S13S4dA1M5S15S0S27RbRaA2S28A3A3S1cA3S21S18S5fS0G5S15S0S27RcRbA2S29A3A3S1cA3S54S56S24G0S6R9PcA2A2S24G0S6R9PdA2A2A2S53Z2Z40A2A2S5aS52S26ReRdRcRbA4S3eS35ReRdA3RaR9R8A6S5aS52S26RfReRdRcA4S30RfReS57S54S24G0S2aRbA1A2M6Zfc01M7A2M8S22G8A1M9A2G3L_;S67G6G7A2G8S29L_;G9S28L_;X57x2A3S2bRdRbA2RaR9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w HUS Wa Da Wb Fbh Fbl HNOV H.
  set (rho1 := rho_ce A rho).
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by reflexivity.
  assert (E10 : rw rho1 10%positive = rw rho 10%positive) by reflexivity.
  assert (E12 : rw rho1 12%positive = rw rho 12%positive) by reflexivity.
  assert (Erm : rm rho1 = rm rho) by reflexivity.
  assert (E151 : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by reflexivity.
  assert (E152 : rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by reflexivity.
  assert (E153 : rw rho1 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))) by reflexivity.
  assert (E154 : rw rho1 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))) by reflexivity.
  assert (E155 : rw rho1 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by reflexivity.
  assert (E156 : rw rho1 156%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize)) by reflexivity.
  pose proof (urange (rw rho 12%positive)) as U12. pose proof (urange (rw rho 13%positive)) as U13.
  assert (TOPlo : topG (aa_geom A) <= fst (obj_range rho1 stack_win)) by (unfold stack_win; rewrite own_lo; exact Htop).

  assert (H1 : SPA segs (Jc W st A Kc) (Pre_callocI AE_A W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|apply rho_ce_agree]; cbv; discriminate | apply JMc_agree; [exact HUS | apply rho_ce_agree]]. }
  clear H HsmA.

  assert (H2 : SPA segs (Jc W st A Kc) (mkAX (sa_c W st) [] base_sv) rho1 tp w).
  { change (mkAX (sa_c W st) [] base_sv) with (ax_setS (Pre_callocI AE_A W st) (sa_c W st)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H1].
    constructor; [|constructor]. cbn [fst snd eval]. rewrite E24. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H1.

  destruct HRest as (Hsep & _ & _ & _ & _ & _ & _ & HTH & HMI). unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG0 | lia]).

  destruct HMI as [HMIc _]. pose proof (Forall_inv (Forall_inv_tail HMIc)) as HPP.
  assert (HPP' : cell_ok (view segs (rm rho)) (mkACell (0 + 0xeb90d) 1 1)).
  { intros j Hj. specialize (HPP j Hj). cbn [c_addr c_w c_val] in HPP, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HPP; [exact HPP | apply fs_footb_img; [exact HG0 | lia]]. }

  pose proof (law_die A rho tp _ HA) as HDIE.
  assert (HDIE' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x17fbdc) 4 0)) by (rewrite Z.add_0_l; exact HDIE).

  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HMIc))) as HCSD.
  assert (HCSD' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x17fcd8) 4 0)).
  { intros j Hj. specialize (HCSD j Hj). cbn [c_addr c_w c_val] in HCSD, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HCSD; [exact HCSD | apply fs_footb_img; [exact HG0 | lia]]. }
  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_c]; apply in_or_app; right; cbn; tauto).
  destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W']; [constructor|].
    assert (HC : Forall (holds rho1) (chain_pre (l :: W'))).
    { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_c]. apply in_or_app. left.
      destruct st; [apply chain_pre_in; exact Hp | exact Hp]. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; clear TI CI G15 G16 G17 G18 G19 G20 G21; lia. }

  assert (H3 : SPA segs (Jc W st A Kc) (mkAX (sb_c W st) [] base_sv) rho1 tp w).
  { change (mkAX (sb_c W st) [] base_sv) with
      (ax_setS (mkAX (sa_c W st) [] base_sv) (let S := ax_S (mkAX (sa_c W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj N_m1) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      clear G15 G16 G17 G18 G19 G20 G21 TI CI.
      unfold N_m1, N_rest, N_fn, N_m5. cbn [tl app]. unfold vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: rewrite ?Erm.
      all: match goal with
           | |- cells_in_view _ _ 0 [(0xeb90d, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0xeb90d 1 1 (SLit 1) HPP' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ 0 [(0x17fbdc, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0x17fbdc 4 0 (SLit 0) HDIE' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ 0 [(0x17fcd8, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0x17fcd8 4 0 (SLit 0) HCSD' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ (ag_thread _) [(3168, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil]; intros j Hj; replace j with 0%nat by lia;
               rewrite nth0_enc1_zero; cbn [Z.of_nat]; rewrite Z.add_0_r; rewrite <- view_in by lia; exact HTH
           | |- cells_in_view _ _ _ _ => unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E153, ?E154, ?E155, ?E156; civ_any2F HR
           | _ => idtac end.
      all: try match goal with
           | |- forall off, 3168 <= off < 3169 -> _ =>
               intros off Hoff; replace off with 3168 by lia; eapply wok_rd_off_image2;
               [lia | (pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia) |]; rewrite <- view_in by lia; exact HTH
           | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
           | |- forall off, _ -> wok_of _ _ _ = true /\ _ =>
               intros off Hoff;
               first [ wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia)
                     | destruct (Z_lt_dec off 8); [|destruct (Z_lt_dec off 16)]; wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia) ]
           end.
      all: fail "m_instantiate: carve obligation left".
    -
      unfold N_m1, N_rest, N_fn, N_m5. cbn [tl app map carve_obj ss_objs ax_S sa_c]. unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      unfold A_globals. unfold O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      repeat (apply Forall_cons;
        [ apply Forall_cons;
          [ unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]);
            destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ])
          | apply Forall_app; split;
            [ eapply Forall_impl; [|exact LNK]; intros [ob olo ohi ocs od] (B & L & Hh); cbn [ob_base ob_lo ob_hi] in B, L, Hh; subst olo ohi;
              unfold ranges_disjoint; rewrite !obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; cbn [eval] in B; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ])
            | repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint;
              rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]) ] ]
        | ]).
      apply Forall_nil.
    -
      unfold N_m1, N_rest, N_fn, N_m5. cbn [tl app map carve_obj pairwise_disjoint]. unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]). }
  clear H2.

  set (nv := U (nwc rho)) in *.
  assert (ENW : nwc rho = mul_div M_MUL (rw rho 12%positive) (rw rho 13%positive)) by reflexivity.
  assert (HNv : 1 <= nv < 2 ^ 39) by (unfold nv, nwc; exact HN).
  assert (E13 : rw rho1 13%positive = rw rho 13%positive) by reflexivity.
  assert (EP : eval rho1 PRODe = nwc rho).
  { unfold PRODe. cbn [eval]. rewrite E12, E13, ENW. apply mul_word_comm. }
  assert (EMH : U (eval rho1 MHe) = 0).
  { unfold MHe. cbn [eval]. rewrite E12, E13. apply mulhu_zero_iff. lia. }
  destruct (mul_pos_factors (rw rho 12%positive) (rw rho 13%positive)) as [C1 S1]; [rewrite <- ENW; fold nv; lia|].
  change (P0e W st (if Z_lt_dec nv 64513 then F_lo_e else F_hi_e)) with
    (ax_with_facts (mkAX (sb_c W st) [] base_sv) (FACTSe W st ++ (if Z_lt_dec nv 64513 then F_lo_e else F_hi_e))).
  eapply SPA_refacts; [exact H3 | destruct (Z_lt_dec _ _); [exact Fbl | exact Fbh] |].
  intros Hold. unfold FACTSe. apply Forall_app. split; [apply Forall_app; split; [apply Forall_app; split; [apply Forall_app; split; [exact Hold|]|]|]|].
  - unfold F_geom_fn, vT, vCTX, vTOP, vBOT. clear TI CI G15 G16 G17 G18 G19 G20 G21.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E151, ?E152, ?E153, ?E154; rewrite ?u64_lit by lia; try lia.
  - unfold F_s1e, vSB, vRIS. unfold HIGH_SHADOW_END. rewrite kSpaceSize_val. clear TI CI G15 G16 G17 G18 G19 G20 G21.
    cbn [fst snd] in SW1, SW2. pose proof (urange (rw rho 10%positive)) as U10.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?EP; fold nv; cbn [eval]; rewrite ?E155, ?E156, ?E10; rewrite ?kSpaceSize_val; rewrite ?u64_lit by lia; try lia.
    +
      cbn [branch_taken]. unfold bv_eqb. rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. apply Z.eqb_refl.
    +
      intros E. cbn [branch_taken] in E. unfold bv_eqb in E. rewrite add_val in E. rewrite (u64_lit 0) in E by lia.
      replace (bv_unsigned (Z_to_bv 64 (-2136))) with (2 ^ 64 - 2136) in E by reflexivity.
      rewrite E10 in SW2. set (sp := bv_unsigned (rw rho 10%positive)) in *.
      replace (sp + (2 ^ 64 - 2136)) with ((sp - 2136) + 1 * 2 ^ 64) in E by lia.
      rewrite Z.mod_add in E by lia. rewrite Z.mod_small in E by lia. apply Z.eqb_eq in E. lia.
  - unfold F_arge. repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?EP; fold nv.
    + cbn [eval]. rewrite E12, u64_lit by lia. lia.
    + cbn [eval]. rewrite E13, u64_lit by lia. lia.
    + cbn [branch_taken]. unfold bv_eqb. rewrite EMH. cbn [eval]. rewrite u64_lit by lia. reflexivity.
    + cbn [eval]. rewrite u64_lit by lia. lia.
    + cbn [eval]. rewrite u64_lit by lia. lia.
  - destruct (Z_lt_dec nv 64513) as [Hlt|Hge]; unfold F_lo_e, F_hi_e, rup8e.
    + repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; [rewrite EP; fold nv; cbn [eval]; rewrite u64_lit by lia; lia|].
      cbn [eval]. change (mul_div M_MUL (rw rho1 13%positive) (rw rho1 12%positive)) with (eval rho1 PRODe). rewrite EP.
      rewrite and_val, add_val, !u64_lit by lia. fold nv. replace (bv_unsigned (Z_to_bv 64 18446744073709551608)) with 18446744073709551608 by reflexivity.
      rewrite Z.mod_small by lia. apply rup8_le. lia.
    + repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite EP; fold nv; cbn [eval]; rewrite u64_lit by lia. lia.
Qed.
End CSPINE.
