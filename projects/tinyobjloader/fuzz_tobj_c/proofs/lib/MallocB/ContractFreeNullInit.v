(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "valuation"; "SLit"; "swf"; "SVar"; "rw"; "FcsrFrm0"; "mkSS"; "sprop_below"; "agree_below"; "cell"; "enc_bytes"; "eval"; "rm"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "bool"; "list"; "nil"; "nat"; "true"; "app"; "false"; "Some"; "option"; "None"; "fst"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "L_free_null"; "Pre_free_nullI"; "J_free_null_preT"; "KcA"; "JL_free_null"; "Kc_ok"; "UStopLeOrPc"; "Wcan"; "free_depth"; "pre_facts"; "unwind_factsS"; "A_globals"; "stack_win"; "unwind_objs"; "V_FREE_A1"; "ae_free"; "base_sv"; "ulink"; "ustop"; "ae_ret_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_internal_inited"; "ag_ctx"; "ag_thread"; "ag_stack_bottom"; "ag_stack_top"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "cut_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit"; "RT_rest"; "E_fni"; "O_iaw"; "O_iaw_done"; "fni_cutpcs"; "O_inst"; "P0_fni"; "fni_cuts"; "fni_vcuts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull"; "stR"; "s_fn"; "sa_fn"; "rho1_of"; "stK"; "img_zone2_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit"; "N_rest"; "N_fni0"; "N_fni1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit.FNI"; "sb_fni"; "sc_fni"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM"; "rt_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue"; "coverb"; "img_zone_okb"; "spec_range"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma nth_enc2_zero' : ltac2:(tb__ "0|5|
S16S83R1U2M0A2S1fS40Q8M1A1M2S78G2R2SdG0S41Q40Z0M3A2A2S41G1G3A2M4A4G4A3F_;Fj;").
Proof. intros j Hj. do 2 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Definition K_iaw0 : carve_spec := ltac2:(tb__ "0|6|
S10S12S12S0S38A2M0S38A2S14S12S12S38S16A2M1S0A2M2A1S10G0S38S10S0S38S4Z0A1M3Z17db48M4A4Z17db4cA4S11G2S10G1S0S10S38S16G4U1M5A4G3A4S11G2S10G1S0S10S38S16Z17db49G5A4G3A4S11G2S10G1S0S10S38S16Z17db4aG5A4G3A4S11G2S10G1S0S10S38S16Z17db4bG5A4G3A4S15G2A1A3A3A3A3A4").
Definition K_iaw_done : carve_spec := ltac2:(tb__ "0|6|
S10S12S12S0S38A2M0S38A2S14S12S12S38S16A2M1S0A2M2A1S10G0S38S10S0S38S4Z0A1M3Z17db48M4A4Z17db4cA4S11G2S10G1S0S10S38S16Z17db49U1M5A4G3A4S11G2S10G1S0S10S38S16G4G5A4S4Z1A1A4S11G2S10G1S0S10S38S16Z17db4aU2A4G3A4S15G2A1A3A3A3A4").
Definition N_rest : list carve_spec := tl (tl N_fn).
Definition N_fni0 : list carve_spec := K_iaw0 :: N_rest.
Definition N_fni1 : list carve_spec := K_iaw_done :: N_rest.
Lemma N_rest_ok : ltac2:(tb__ "0|0|
S1fS14S1A1S76S52S1S53S69A4S5aA3").
Proof. reflexivity. Qed.
Lemma N_fni0_ok : ltac2:(tb__ "0|1|
S1fS14S1A1S76S52S1S53S6aA4S11S1S5cZ0M0G0A2S5aA3A3").
Proof. reflexivity. Qed.
Lemma N_fni1_ok : ltac2:(tb__ "0|0|
S1fS14S1A1S76S52S1S53S6bA4S11S1S5dS5aA3A3").
Proof. reflexivity. Qed.
Lemma N_rest_coverb : ltac2:(tb__ "0|0|
S1fS13S72S52S87S69A3S17A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_fni1_small : Forall spec_small N_fni1.
Proof.
  unfold N_fni1, N_rest, N_fn, K_iaw_done, spec_small. cbn [tl].
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma N_rest_small : Forall spec_small N_rest.
Proof. exact (Forall_inv_tail N_fni1_small). Qed.
Lemma N_rest_img_zone : ltac2:(tb__ "0|0|
S1fS13S72S52S68S69A3S17A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section FNI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S38S82VCST;R1A2S20S21S20S55S6dR2A2S56R2S6eA2A2A1S21S20S55Z17db48R2A2S56R2Z17db4cA2A2A1A2F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S26VAInv;VW;Vst;VA;VKc;A5").

Definition sb_fni (W : list ulink) : sstate := ltac2:(tb__ "0|2|
S9S33S23A1S4dS4eS11S12S16S0A2M0S10S16S0U4S4S54A1A4S11G0S10S16S0UaS4Z0M1A1A4S11G0S10S16S0UbS6S32A1A4S15G0A1A3A3A3A2S4cS8S1cS0A1S18S1S11S1S30S18S1S31VW;A1S2fA3A3S11S1S5cG1G1A2S5aA3A3S18S2S2eVW;S22A2S2dS2cA1A3S70S19A9").
Definition sc_fni (W : list ulink) : sstate := ltac2:(tb__ "0|2|
S9S33S23A1S4dS4eS11S12S16S0A2M0S10S16S0U4S4S54A1A4S11G0S10S16S0UaS4Z0M1A1A4S11G0S10S16S0UbS6S32A1A4S15G0A1A3A3A3A2S4cS8S1cS0A1S18S1S18S1S11S1S30S18S1S31VW;A1S2fA3A3S11S1S5cG1G1A2S5aA3A3S11S1S5fS15ScA1A1S15S1A1A3A3S18S2S2eVW;S22A2S2dS2cA1A3S70S19A9").

Local Ltac civ_try2F HR n :=
  eapply (civ_nth2 _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Local Ltac civ_any2F HR := first [ civ_try2F HR 43%nat | civ_try2F HR 44%nat | civ_try2F HR 45%nat | civ_try2F HR 46%nat | civ_try2F HR 47%nat | civ_try2F HR 48%nat | civ_try2F HR 49%nat | civ_try2F HR 50%nat | civ_try2F HR 51%nat | civ_try2F HR 52%nat | civ_try2F HR 53%nat | civ_try2F HR 54%nat | civ_try2F HR 0%nat | civ_try2F HR 1%nat | civ_try2F HR 2%nat | civ_try2F HR 3%nat | civ_try2F HR 4%nat | civ_try2F HR 5%nat | civ_try2F HR 6%nat | civ_try2F HR 7%nat | civ_try2F HR 8%nat | civ_try2F HR 9%nat | civ_try2F HR 10%nat | civ_try2F HR 11%nat | civ_try2F HR 12%nat | civ_try2F HR 13%nat | civ_try2F HR 14%nat | civ_try2F HR 15%nat | civ_try2F HR 16%nat | civ_try2F HR 17%nat | civ_try2F HR 18%nat | civ_try2F HR 19%nat | civ_try2F HR 20%nat | civ_try2F HR 21%nat | civ_try2F HR 22%nat | civ_try2F HR 23%nat | civ_try2F HR 24%nat | civ_try2F HR 25%nat | civ_try2F HR 26%nat | civ_try2F HR 27%nat | civ_try2F HR 28%nat | civ_try2F HR 29%nat | civ_try2F HR 30%nat | civ_try2F HR 31%nat | civ_try2F HR 32%nat | civ_try2F HR 33%nat | civ_try2F HR 34%nat | civ_try2F HR 35%nat | civ_try2F HR 36%nat | civ_try2F HR 37%nat | civ_try2F HR 38%nat | civ_try2F HR 39%nat | civ_try2F HR 40%nat | civ_try2F HR 41%nat | civ_try2F HR 42%nat ].

Local Ltac lia_only v := repeat match goal with H : context [v] |- _ => revert H end; clear - v; intros; lia.
Local Ltac wr_cell2F HR n off tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell;
  [ lazymatch goal with |- ?x + _ <= ?x + _ < _ => idtac end; lia_only off | lia | tacW | lia ].
Local Ltac wr_any2F HR off tacW := first [ wr_cell2F HR 43%nat off tacW | wr_cell2F HR 44%nat off tacW | wr_cell2F HR 45%nat off tacW | wr_cell2F HR 46%nat off tacW | wr_cell2F HR 47%nat off tacW | wr_cell2F HR 48%nat off tacW | wr_cell2F HR 49%nat off tacW | wr_cell2F HR 50%nat off tacW | wr_cell2F HR 51%nat off tacW | wr_cell2F HR 52%nat off tacW | wr_cell2F HR 53%nat off tacW | wr_cell2F HR 54%nat off tacW ].

Lemma fni_instantiate : ltac2:(tb__ "0|4|
S14S35A1S43S27S3S14S40Q40A1A1S57S1fS13S45R5A1S19A3S1fS13S5S65R7A1A1S17A3S1fS1bS12S14S12S0S0A2M0A1M1S14S2A1M2A2M3A1S74S3bS25S23R8S22A3A1S65R8A1A2S1aG3S10G1G2S11G0S10S0S0S6P18A1S4S54A1A4S15G0A1A3S15S2A1A4A2A3S1fS13S5S7fR9A1A1S17A3S1fS13S5S80RaA1A1S17A3S1fS13S72S2SaS70A1S18S2S18S2S2eRbS22A2S2dS2cA1A3S71A3A3S17A3S50Vsegs;VJ;RcS22RbRaA4S25S23RcS22A3R9R8R7A6S50Vsegs;VJ;RdS22RcRbA4S60RdS22A2S66RcRaA2R9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;FW;").
Proof.
  intros W A Kc rho tp w Hii Wa Da Wb Wc Fb H.
  set (rho1 := rho1_of A rho).
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HU & HK & Htp & Htop).
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by reflexivity.
  assert (E10 : rw rho1 10%positive = rw rho 10%positive) by reflexivity.
  assert (Erm : rm rho1 = rm rho) by reflexivity.
  assert (E151 : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by reflexivity.
  assert (E152 : rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by reflexivity.
  assert (E153 : rw rho1 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))) by reflexivity.
  assert (E154 : rw rho1 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))) by reflexivity.
  assert (TOPlo : topG (aa_geom A) <= fst (obj_range rho1 stack_win)) by (unfold stack_win; rewrite own_lo; exact Htop).

  assert (H1 : SPA segs (J W UStopLe A Kc) (Pre_free_nullI AE_A W UStopLe) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|apply rho1_agree]; cbv; discriminate | apply J_agree; apply rho1_agree]. }
  clear H HsmA.

  assert (H2 : SPA segs (J W UStopLe A Kc) (mkAX (sa_fn W) [] base_sv) rho1 tp w).
  { change (mkAX (sa_fn W) [] base_sv) with (ax_setS (Pre_free_nullI AE_A W UStopLe) (sa_fn W)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H1].
    constructor; [|constructor]. cbn [fst snd eval]. rewrite E24. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H1.

  destruct HRest as (Hsep & _ & _ & _ & _ & _ & HIA & HTH & HMI).
  unfold ia_inv in HIA. rewrite Hii in HIA. destruct HIA as (IA9 & IAa & IAb & IA8 & IAF).
  unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  assert (MV : forall z, z < 0x643000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
  { intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG0 | exact Hz]. }
  rewrite MV in IA9, IAa, IAb, IA8 by lia.
  assert (IAF' : forall z, IA_BEG <= z < IA_END -> view segs (rm rho) z = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite <- MV by (unfold IA_BEG, IA_END in Hz; lia). exact (IAF z Hz). }
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG0 | lia]).
  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_fn]; apply in_or_app; right; cbn; tauto).
  destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { assert (HC : Forall (holds rho1) (chain_pre W)).
    { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_fn]. apply in_or_app. left. apply chain_pre_in. exact Hp. }
    unfold unwind_objs. destruct W as [|l W']; [constructor|].
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; clear TI CI G15 G16 G17 G18 G19 G20 G21; lia. }

  assert (H3 : SPA segs (J W UStopLe A Kc) (mkAX (sb_fni W) [] base_sv) rho1 tp w).
  { change (mkAX (sb_fni W) [] base_sv) with
      (ax_setS (mkAX (sa_fn W) [] base_sv) (let S := ax_S (mkAX (sa_fn W) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj N_fni0) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      clear G15 G16 G17 G18 G19 G20 G21 TI CI.
      unfold N_fni0, N_rest, N_fn, K_iaw0. cbn [tl]. unfold vT, vCTX, vTOP, vBOT.
      repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: rewrite ?Erm.
      all: match goal with
           | |- cells_in_view _ _ 0 [(0x17db48, _, _); _; _; _] =>
               unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj; replace j with 0%nat by lia;
               cbn [Z.of_nat]; rewrite ?Z.add_0_r, ?Z.add_0_l; rewrite <- view_in by lia; rewrite nth0_enc1_zero;
               first [exact IA8 | exact IA9 | exact IAa | exact IAb]
           | |- cells_in_view _ _ (ag_thread _) [(3168, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil]; intros j Hj; replace j with 0%nat by lia;
               rewrite nth0_enc1_zero; cbn [Z.of_nat]; rewrite Z.add_0_r; rewrite <- view_in by lia; exact HTH
           | |- cells_in_view _ _ _ _ => unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; civ_any2F HR
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
      all: fail "fni_instantiate: carve obligation left".
    -
      unfold N_fni0, N_rest, N_fn, K_iaw0. cbn [tl map carve_obj ss_objs ax_S sa_fn]. unfold carved, vT, vCTX, vTOP, vBOT.
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
      unfold N_fni0, N_rest, N_fn, K_iaw0. cbn [tl map carve_obj pairwise_disjoint]. unfold carved, vT, vCTX, vTOP, vBOT.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]). }
  clear H2.

  assert (H4 : SPA segs (J W UStopLe A Kc) (mkAX (sc_fni W) [] base_sv) rho1 tp w).
  { destruct w as [tr [ms md]].
    change (mkAX (sc_fni W) [] base_sv) with
      (ax_setS (mkAX (sb_fni W) [] base_sv) (let S := ax_S (mkAX (sb_fni W) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj (SLit 0) (SLit IA_LO) (SLit IA_HI) [] DZero]) (ss_facts S) NW2 (ss_lenient S))).
    apply (SPA_carve_zero_rd segs (J W UStopLe A Kc) rho1 (mkAX (sb_fni W) [] base_sv) tp tr ms md (SLit 0) IA_LO IA_HI NW2 H3 Wc);
      cbn [ax_S ss_next sb_fni ax_X ss_objs eval]; rewrite ?u64_lit by lia; unfold IA_LO, IA_HI; try lia.
    -
      apply Forall_app. split.
      + apply Forall_cons; [unfold ranges_disjoint; destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; clear TI CI G15 G16 G17 G18 G19 G20 G21; lia|].
        apply Forall_app. split.
        * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
          unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. clear TI CI G15 G16 G17 G18 G19 G20 G21. lia.
        * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
          repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
      + unfold RT_rest, O_iaw, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs.
        unfold carved, vT, vCTX, vTOP, vBOT.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval];
          rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]).
    -
      intros a Ha. split; [apply wok_of_imageA; lia|]. rewrite Erm. rewrite <- view_in by lia. apply IAF'. unfold IA_BEG, IA_END. lia.
    - intros rr y j [].
  }
  clear H3.

  change (P0_fni W UStopLe) with (ax_with_facts (mkAX (sc_fni W) [] base_sv) ((unwind_factsS W UStopLe ++ pre_facts free_depth) ++ F_geom_fn)).
  eapply SPA_refacts; [exact H4 | exact Fb |].
  intros Hold. apply Forall_app. split; [exact Hold|]. unfold F_geom_fn, vT, vCTX, vTOP, vBOT. clear TI CI G15 G16 G17 G18 G19 G20 G21.
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E151, ?E152, ?E153, ?E154; rewrite ?u64_lit by lia; try lia.
Qed.

Lemma fni_civ : ltac2:(tb__ "0|5|
S43S3S14S40Q40M0A1M1A1S84VAInv;R4R3R2R1A4S1fG1S7R4P97A2S41G0S47S44R5A1A1A2A3S1fG1S7R5P98A2S41G0S46S44R6A1A1A2A3S1fG1S7R6P99A2S41G0S49S44R7A1A1A2A3S1fG1S7R7P9aA2S41G0S48S44R8A1A1A2A3S77S52S52S12S12S12S0S38A2M2S38A2M3S14S12S12S38S16A2S0A2A1M4A2OLk;R1G3G4G3OLp;R2G2S38G2OLp0;R2S0S38S85RfS86Vsegs;SfRfA1A2S42G0SeRfR2A2A2R5A4Llo;Lbase;X12x1Lhi;Lp0;X12x1Lcs;Lp;X12x1Lk;S69A3F_;F_;F_;F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA E151 E152 E153 E154.
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  destruct HRest as (Hsep & _ & _ & _ & _ & _ & _ & HTH & HMI). unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG | lia]).
  unfold N_rest, N_fn. cbn [tl]. unfold vT, vCTX, vTOP, vBOT.
  repeat apply Forall_cons; try apply Forall_nil; lazy beta iota zeta; cbn [eval]; rewrite ?E151, ?E152, ?u64_lit by lia.
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E153, ?E154.
  all: first [ intros j Hj; replace j with 0%nat by lia; cbn [Z.of_nat]; rewrite ?Z.add_0_r, ?Z.add_0_l; rewrite <- view_in by lia;
               rewrite nth0_enc1_zero'; exact HTH
             | civ_any2F HR ].
Qed.

Lemma N_rest_img_zone1 : ltac2:(tb__ "0|0|
S1fS13S72S52S88S69A3S17A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma N_rest_zone : ltac2:(tb__ "0|3|
S43S3S52S38S6fS44R4A1A1S1fS40Q40M0A1M1S7R4P97A2S41G0S47S44R5A1A1A2A3S1fG1S7R5P98A2S41G0S46S44R6A1A1A2A3S73S52R5S69A3S20S55S1dS38S38S89R7R6A2M2A3R5A2S56R5S1eS38S38G2A3A2A2S81S44R9A1R6A2F_;F_;F_;F_;F_;Fa;Fk;Frho;FA;").
Proof.
  intros A rho k a HG E151 E152 Hk Ha.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (proj1 (forallb_forall _ _) N_rest_img_zone1 k Hk) as IZ.
  unfold N_rest, N_fn in Hk. cbn [tl In] in Hk. unfold vT, vCTX, vTOP, vBOT in Hk. unfold rt_zone.
  repeat (destruct Hk as [E|Hk];
    [subst k; cbn [spec_range fst snd eval] in Ha; rewrite ?E151, ?E152, ?u64_lit in Ha by lia;
     first [ left; split; [unfold IMG_HI; lia|]; unfold img_zone_okb in IZ;
             eapply (forall_rangeZ_ok (fun a0 => cells_footb (rtc_cells_img RTC_A G0) a0)); [exact IZ | lia]
           | right; lia ]
    |]).
  destruct Hk.
Qed.

Lemma rt_zone_not_ia : ltac2:(tb__ "0|0|
S4aS38S6fR2A1S81R3R2A2S20S21S20S55S6dR3A2S56R3S6eA2A2A1S21S20S55Z17db48R3A2S56R3Z17db4cA2A2A1A2F_;F_;Fa;FG;").
Proof.

  intros G a HG R. pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & DI). unfold IMG_LO, IMG_HI in TI, CI, DI.
  unfold rt_zone, IMG_HI in R. unfold IA_BEG, IA_END.
  destruct R as [[_ R]|[R|[R|[R|R]]]]; [| clear CI DI; lia | clear TI DI; lia | clear TI CI; lia | clear TI CI DI; lia].
  unfold cells_footb in R. apply existsb_exists in R as (c & Hc & Hinb). unfold in_cellb in Hinb.
  apply andb_prop in Hinb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
  destruct (rtc_cells_img_lt _ _ Hc) as [X Y]. unfold IA_BEG, IA_END in X. lia.
Qed.

Definition stJ (W : list ulink) : sstate := ltac2:(tb__ "0|1|
S9S37S23A1S4dS4fS75A1S11S12S16S0A2M0S10S16S0U4S4S54A1A4S15G0A1A3A2S4cS8S1cS0A1S18S1S11S1S30S18S1S31VW;A1S2fA3A3S11S1S5dS5aA3A3S18S2S18S2S2eVW;S22A2S2dS2cA1A3S71A3S70S19A9").

Lemma fni_reabstract : ltac2:(tb__ "0|6|
S14S35A1S43S27S3S14S40Q40A1A1S57S3S1fS13S45R6A1S19A3S1fS13S5S63R8A1A1S17A3S1fS1bS12S14S12S0S0A2M0A1M1S14S2A1M2A2M3A1S74S67R9A1S63R9A1A2S1aG3S10G1G2S11G0S10S0S0S4S54A1S6P18A1A4S15G0A1M4A3S15S2A1A4A2A3S1fS13S3cS3dS63RaA1G4S34A3S24S23RaS22A3S64RaA1A3S17A3S1fS13S79S64RbA1S4bA2S17A3S50Vsegs;S7eS3SbS75S66RcRaA2R1A3Lr;VJ;RcS22RbRaA4A2S5bRcS22A2R6R8R7A6S3fVsegs;S4bRaR9S11S12S3aS3eA2M5S10S3aS3eS24S23RdS22A3S28VAInv;VCST;VXGL;RcRbA5A4S15G5A1A3R8A6F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;FW;").
Proof.
  intros W A Kc rho tp w rhoE Hii WR DKR Hent Hid H.
  destruct w as [tr [ms md]]. destruct H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct HJ as (HA & HU & HK & Htp & Htop).
  destruct Hag as (Hagw & Hagl & Hagm).
  assert (Erm : rm rhoE = rm rho).
  { apply functional_extensionality. intros a. rewrite <- Hagm. reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E153 : rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))). { rewrite <- (Hagw 153%positive) by (unfold GW; lia). reflexivity. }
  assert (E154 : rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))). { rewrite <- (Hagw 154%positive) by (unfold GW; lia). reflexivity. }
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof (proj1 HRest) as Hsep.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as TG.

  assert (Ha : SPA segs (fun _ _ t m => Kc t m) (E_fni W UStopLe) rhoE tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rhoE (E_fni W UStopLe) ((stack_win :: unwind_objs W ++ A_globals) ++ (O_iaw_done :: RT_rest)) [O_inst inst_cells] tp tr ms md eq_refl Ha (fun k => k)) as Hb1.
  cbn zeta in Hb1. set (rho2 := rho_absorb rhoE [O_inst inst_cells] (vms md tp ms)) in *.
  change (ax_setS (E_fni W UStopLe) (set_objs (ax_S (E_fni W UStopLe)) ((stack_win :: unwind_objs W ++ A_globals) ++ (O_iaw_done :: RT_rest)))) with (mkAX (stJ W) [] base_sv) in Hb1.
  pose proof (proj1 (proj1 Ha)) as HsmE. unfold virt in HsmE. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in HsmE.

  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rho2 (mkAX (stJ W) [] base_sv) (stack_win :: unwind_objs W ++ A_globals) (O_iaw_done :: RT_rest) tp tr ms md eq_refl Hb1 (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rho2 (O_iaw_done :: RT_rest) (vms md tp ms)) in *.
  change (ax_setS (mkAX (stJ W) [] base_sv) (set_objs (ax_S (mkAX (stJ W) [] base_sv)) (stack_win :: unwind_objs W ++ A_globals))) with (mkAX (stK W) [] base_sv) in Hb.
  pose proof (proj1 (proj1 Hb1)) as Hsm2. unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm2.
  assert (EV2 : forall e, eval rho2 e = eval rhoE e) by (intros e; unfold rho2; apply eval_absorb).
  assert (E151' : rw rho2 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by (unfold rho2; cbn [rho_absorb rw]; exact E151).
  assert (E152' : rw rho2 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by (unfold rho2; cbn [rho_absorb rw]; exact E152).

  pose proof (fni_civ A rhoE tp md HA E151 E152 E153 E154) as CIV.
  assert (RNG1 : forall z o, In o (O_iaw_done :: RT_rest) -> fst (obj_range rho2 o) <= z < snd (obj_range rho2 o) ->
                 (0x17db48 <= z < 0x17db4c) \/ exists k, In k N_rest /\ fst (spec_range rhoE k) <= z < snd (spec_range rhoE k)).
  { intros z o Hin Hr. rewrite <- N_fni1_ok in Hin. apply in_map_iff in Hin as (k & <- & Hk).
    pose proof (proj1 (Forall_forall _ _) N_fni1_small k Hk) as Sk.
    destruct Hk as [<-|Hk].
    - left. cbn [carve_obj K_iaw_done] in Hr. unfold carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd] in Hr. rewrite EV2 in Hr. cbn [eval] in Hr. rewrite u64_lit in Hr by lia. lia.
    - right. exists k. split; [exact Hk|]. destruct k as [[[base lo] hi] cs]. cbn [carve_obj] in Hr.
      destruct Sk as (S1 & S2 & S3 & _). unfold carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd ob_base spec_range] in Hr |- *.
      rewrite EV2 in Hr. exact Hr. }
  assert (VEQ : forall z, ~ ia_zone z -> view segs (rm rho3) z = view segs (rm rhoE) z).
  { intros z Hz. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by lia; reflexivity.
    rewrite !view_in by lia. destruct (in_ranges_dec rho2 (O_iaw_done :: RT_rest) (Z_to_bv 64 z)) as [Hri|Hrn].
    - destruct Hri as (o & Hin & Hr). rewrite u64_lit in Hr by lia.
      destruct (RNG1 z o Hin Hr) as [Zi|(k & Hk & Hzk)]; [exfalso; apply Hz; unfold ia_zone; lia|].
      unfold rho3. eapply (absorb_specs_view rho2 (stJ W) tr (vms md tp ms) (vmd md) (stack_win :: unwind_objs W ++ A_globals) (O_iaw_done :: RT_rest) N_rest (rd_of segs (rm rhoE)) Hsm2 eq_refl); [| exact Hk |].
      + intros k' Hk'. split; [rewrite <- N_fni1_ok; apply in_map; right; exact Hk'|]. split; [exact (proj1 (Forall_forall _ _) N_rest_small k' Hk')|].
        split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_rest_coverb k' Hk')|].
        pose proof (proj1 (Forall_forall _ _) CIV k' Hk') as C'. destruct k' as [[[base lo] hi] cs]. cbn [spec_range fst snd].
        cbn zeta in C'. rewrite EV2. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by lia.
        unfold cells_in_view in C' |- *. apply Forall_forall. intros [[o1 n1] e1] Hin' j Hj. rewrite EV2. exact (proj1 (Forall_forall _ _) C' _ Hin' j Hj).
      + destruct k as [[[base lo] hi] cs]. cbn [spec_range fst snd] in Hzk |- *. rewrite EV2. exact Hzk.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hrn.
      destruct (in_ranges_dec rhoE [O_inst inst_cells] (Z_to_bv 64 z)) as [Hri2|Hrn2].
      + exfalso. destruct Hri2 as (o & [<-|[]] & Hr). unfold O_inst in Hr. rewrite obj_range_mk in Hr by (unfold IA_LO, IA_HI; lia).
        cbn [fst snd eval] in Hr. rewrite !u64_lit in Hr by lia. apply Hz. unfold ia_zone, IA_BEG, IA_END. unfold IA_LO, IA_HI in Hr. lia.
      + unfold rho2. rewrite rm_absorb_out by exact Hrn2. reflexivity. }

  assert (Hrom2 : rom_ok segs (vms md tp ms)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm2))))).
  assert (IAZ : forall z, IA_MAP1 <= z < IA_MAP1 + IA_MAP1_SZ -> view segs (rm rho3) z = Some (Z_to_bv 8 0)).
  { intros z Hz. unfold IA_MAP1, IA_MAP1_SZ in Hz. rewrite view_in by lia.
    assert (Hrn : ~ in_ranges rho2 (O_iaw_done :: RT_rest) (Z_to_bv 64 z)).
    { intros (o & Hin & Hr). rewrite u64_lit in Hr by lia. destruct (RNG1 z o Hin Hr) as [Zi|(k & Hk & Hzk)]; [lia|].
      destruct (rt_zone_not_ia _ z HG (N_rest_zone A rhoE k z HG E151 E152 Hk Hzk)) as [X _]. unfold IA_BEG, IA_END in X. lia. }
    pose proof (absorb_zero_dflt segs rhoE (ax_S (E_fni W UStopLe)) tr (vms md tp ms) (vmd md) _ [O_inst inst_cells] (SLit 0) IA_LO IA_HI inst_cells
                  HsmE eq_refl ltac:(left; reflexivity) ltac:(unfold IA_LO; lia) ltac:(unfold IA_LO, IA_HI; lia) ltac:(unfold IA_HI; lia)) as ZD.
    cbn zeta in ZD. cbn [eval] in ZD. rewrite u64_lit in ZD by lia. fold rho2 in ZD.
    unfold rho3, rd_of. rewrite rm_absorb_out by exact Hrn.
    change (rd_of segs (rm rho2) (Z_to_bv 64 z) = Some (Z_to_bv 8 0)). rewrite <- (Z.add_0_l z).
    apply ZD; [unfold IA_LO, IA_HI; lia|].
    unfold inst_cells. intros Hcov. unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hc & Hic).
    destruct Hc as [<-|[<-|[]]]; unfold in_cell in Hic; cbn [c_off c_width] in Hic; rewrite soff_lit_small in Hic by lia; lia. }
  assert (IAW : view segs (rm rho3) 0x17db49 = Some (Z_to_bv 8 0) /\ view segs (rm rho3) 0x17db4a = Some (Z_to_bv 8 0)
                /\ view segs (rm rho3) 0x17db4b = Some (Z_to_bv 8 0) /\ view segs (rm rho3) 0x17db48 = Some (Z_to_bv 8 1)).
  { destruct (absorb_carved_cells segs rho2 (stJ W) tr (vms md tp ms) (vmd md) (stack_win :: unwind_objs W ++ A_globals) (O_iaw_done :: RT_rest)
                (SLit 0) 0x17db48 0x17db4c [(0x17db49, 1%nat, SLit 0); (0x17db48, 1%nat, SLit 1); (0x17db4a, 2%nat, SLit 0)]
                Hsm2 eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as [C _].
    fold rho3 in C. unfold cells_in_view in C. rewrite EV2 in C. cbn [eval] in C. rewrite u64_lit in C by lia.
    pose proof (Forall_inv C) as C9. pose proof (Forall_inv (Forall_inv_tail C)) as C8. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail C))) as Ca.
    cbn zeta in C9, C8, Ca.
    rewrite !view_in by lia.
    split; [specialize (C9 0%nat ltac:(lia)); replace (0 + 0x17db49 + Z.of_nat 0) with 0x17db49 in C9 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in C9; rewrite nth0_enc1_zero' in C9; exact C9|].
    split; [pose proof (Ca 0%nat ltac:(lia)) as Ca0; replace (0 + 0x17db4a + Z.of_nat 0) with 0x17db4a in Ca0 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in Ca0; rewrite (nth_enc2_zero' 0%nat ltac:(lia)) in Ca0; exact Ca0|].
    split; [pose proof (Ca 1%nat ltac:(lia)) as Ca1; replace (0 + 0x17db4a + Z.of_nat 1) with 0x17db4b in Ca1 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in Ca1; rewrite (nth_enc2_zero' 1%nat ltac:(lia)) in Ca1; exact Ca1|].
    specialize (C8 0%nat ltac:(lia)). replace (0 + 0x17db48 + Z.of_nat 0) with 0x17db48 in C8 by lia. change (eval rho3 (SLit 1)) with (Z_to_bv 64 1) in C8. rewrite nth0_enc1_one' in C8. exact C8. }
  destruct IAW as (V9 & Va & Vb & V8).

  assert (HA3 : AInv (set_inited A) rho3 tp md).
  { apply (AInvA_ia_update segs A rhoE rho3 tp md HA VEQ). unfold ia_inv. cbn [aa_internal_inited set_inited].
    split; [exact V9|]. split; [exact Va|]. split; [exact Vb|]. split; [exact V8|]. intros z Hz. exact (IAZ z Hz). }

  assert (Hc : SPA segs (fun _ _ t m => Kc t m) (mkAX (stR W) [] base_sv) rho3 tp (tr, mkCfg ms md)).
  { change (mkAX (stR W) [] base_sv) with (ax_setS (mkAX (stK W) [] base_sv) (stR W)).
    eapply SPA_restate; [exact WR | exact DKR | reflexivity | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3, rho2. cbn [rho_absorb rw]. rewrite Htp. destruct (geom_old _ HG) as (_ & _ & _ & G4' & _). rewrite G4'. reflexivity. }

  remember (s_fn W) as s eqn:Hs. clear Hs.
  pose proof (smatchA_entails segs _ _ _ rho3 tp _ Hent (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 s) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ Hid Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 s).

  exists (L_free_null AE_A W UStopLe), (JL_free_null AInv CST XGL A Kc), rho4, tp.
  split; [left; reflexivity|]. split; [|split; [exact Hsm4|]].
  { split; [intros k Hk; rewrite Hlow by exact Hk; rewrite (proj1 (rho1_agree A rho) k Hk); apply Hagw; unfold GW, NF in *; lia|].
    intros l. unfold rho4, rho3, rho2. cbn [rl rho_sub rho_absorb]. rewrite <- Hagl. reflexivity. }
  cbn [w_tr w_cfg cfg_model fst snd]. unfold JL_free_null. exists (set_inited A).
  assert (HA' : AInv (set_inited A) rho4 tp md).
  { unfold AInv, AInvA, Inv.AInvA in HA3 |- *. rewrite Erm4. exact HA3. }
  split; [exact HA'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|exact HK].

  rewrite Erm4, <- Erm.
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ rt_zone2 (aa_geom A) a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ba Hz. unfold rho3. rewrite rm_absorb_out.
    - unfold rho2. apply rm_absorb_out. intros (o & [<-|[]] & Hr). apply Hz. unfold O_inst in Hr. rewrite obj_range_mk in Hr by (unfold IA_LO, IA_HI; lia).
      cbn [fst snd eval] in Hr. rewrite !u64_lit in Hr by lia. unfold rt_zone2, IA_BEG, IA_END. unfold IA_LO, IA_HI in Hr. right. left. lia.
    - intros (o & Hin & Hr). rewrite u64_lit in Hr by lia. apply Hz. destruct (RNG1 a o Hin Hr) as [Zi|(k & Hk & Hzk)]; [unfold rt_zone2; right; right; exact Zi|].
      left. exact (N_rest_zone A rhoE k a HG E151 E152 Hk Hzk). }
  split.
  - intros a Ba Hcl. apply RMO; [exact Ba|].
    destruct Hcl as [[C1 _]|[C1 _]]; [exact (client_not_rt2 CST HCST HCST2 A a _ HG HF Hsep C1)|].
    pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    exact (shadow_not_rt2 A a HG B).
  - intros x j Hx Hj Hdef.
    assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
      - destruct (HXGL x GX). unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. lia. }
    unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
    destruct (word_byte_range (Sh x) j ltac:(lia) Hj) as (W1 & W2 & W3).
    unfold word_byte. rewrite RMO; [exact Hdef | lia |].
    apply (shadow_not_rt2 A _ HG). lia.
Qed.

Section PerN.
Variable n : nat.
Let W : list ulink := Wcan n.
Hypothesis Wa : ltac2:(tb__ "0|0|
S1fS13S5S65VW;A1A1S17A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S1fS1bS12S14S12S0S0A2M0A1M1S14S2A1M2A2M3A1S74S3bS25S23VW;S22A3A1S65VW;A1A2S1aG3S10G1G2S11G0S10S0S0S6P18A1S4S54A1A4S15G0A1A3S15S2A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S1fS13S5S7fVW;A1A1S17A3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S1fS13S5S80VW;A1A1S17A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S1fS13S72S2SaS70A1S18S2S18S2S2eVW;S22A2S2dS2cA1A3S71A3A3S17A3").
Hypothesis WR : ltac2:(tb__ "0|0|
S1fS13S5S63VW;A1A1S17A3").
Hypothesis DKR : ltac2:(tb__ "0|4|
S1fS1bS12S14S12S0S0A2M0A1M1S14S2A1M2A2M3A1S74S67VW;A1S63VW;A1A2S1aG3S10G1G2S11G0S10S0S0S4S54A1S6P18A1A4S15G0A1A3S15S2A1A4A2A3").
Hypothesis Ent : ltac2:(tb__ "0|0|
S1fS13S3cS3dS63VW;A1S15S12S0S0A2A1S34A3S24S23VW;S22A3S64VW;A1A3S17A3").
Hypothesis Id : ltac2:(tb__ "0|0|
S1fS13S79S64VW;A1S4bA2S17A3").
Hypothesis Cert : ltac2:(tb__ "0|0|
S1fS13S7bS39Ubb8S5eS75S61Vn;S22A2S11S3aS5bVW;S22A2S15S3aA1A3A6S17A3").
Hypothesis ECert : ltac2:(tb__ "0|1|
S1fS13S7cS39Ubb8S5eS75S62Vn;S22A2S11S7aS7dS5bVW;S22A2Z0M0S4G0A1A3S15S7aA1A3A6S17A3").

Theorem free_null_uninited : ltac2:(tb__ "0|1|
S57OF_;S43S27S3S14S40Q40A1A1S1fS13S45R4A1S19A3S29R4A1S51Vsegs;R7VJ;VW;S22R6R5A4A3S59Vsegs;R8S50Vsegs;VJ;VW;S22R7R6A4S25S23VW;S22A3R5R4A5S3fVsegs;S4bR5R4S11S12S3aS3eA2M0S10S3aS3eS24S23VW;S22A3S28VAInv;VCST;VXGL;R7R6A5A4S15G0A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Hii HKc Hokf.
  eapply triple_conseq; [intros w Hw; exact (fni_instantiate W A Kc rho tp w Hii Wa Da Wb Wc Fb Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW (P0_fni W UStopLe) (rho1_of A rho) tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 3000%nat fni_cutpcs GW (fni_cuts n UStopLe) [E_fni W UStopLe] (withGA (fun r => agree_below GW (rho1_of A rho) r) (J W UStopLe A Kc)) ok
           (LQPA segs NF rho tp [(L_free_null AE_A W UStopLe, JL_free_null AInv CST XGL A Kc)]) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply J_stableA; exact HKc].
  - exact Cert.
  - intros E rhoE [<-|[]].
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. right. exact (fni_reabstract W A Kc rho tp w rhoE Hii WR DKR Ent Id Hw).
  - left. reflexivity.
Qed.

Theorem free_null_uninited_ex : ltac2:(tb__ "0|1|
S43S27S3S14S40Q40A1A1S1fS13S45R4A1S19A3S29R4A1S58Vsegs;S50Vsegs;VJ;VW;S22R6R5A4S25S23VW;S22A3R4R3A5S3fVsegs;S4bR4R3S11S12S3aS3eA2M0S10S3aS3eS24S23VW;S22A3S28VAInv;VCST;VXGL;R6R5A5A4S15G0A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Hii HKc.
  eapply etriple_conseq; [intros w Hw; exact (fni_instantiate W A Kc rho tp w Hii Wa Da Wb Wc Fb Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW (P0_fni W UStopLe) (rho1_of A rho) tp w Hw) | intros w Hw; exact Hw |].
  change (P0_fni W UStopLe) with (vna_state (mkVNA (P0_fni W UStopLe) 5 (SLit 0))).
  apply (cfg_complete_autoA segs 3000%nat fni_cutpcs GW (fni_vcuts n UStopLe) [mkVNA (E_fni W UStopLe) 0 (SLit 0)]
           (withGA (fun r => agree_below GW (rho1_of A rho) r) (J W UStopLe A Kc))
           (LQPA segs NF rho tp [(L_free_null AE_A W UStopLe, JL_free_null AInv CST XGL A Kc)]) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply J_stableA; exact HKc].
  - intros m Hm. cbn [fni_vcuts In] in Hm.
    repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm.
  - exact ECert.
  - intros E rhoE [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl].
    intros w Hw. right. exact (fni_reabstract W A Kc rho tp w rhoE Hii WR DKR Ent Id Hw).
  - left. reflexivity.
Qed.
End PerN.
End FNI.

Section Inst.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S38S82VCST;R1A2S20S21S20S55S6dR2A2S56R2S6eA2A2A1S21S20S55Z17db48R2A2S56R2Z17db4cA2A2A1A2F_;Fa;").
Ltac fni_close :=
  match goal with
  | |- _ = true => vm_compute; reflexivity
  | |- state_diff _ _ = _ => vm_compute; reflexivity
  | _ => assumption
  end.

Theorem free_null_contract_0_uninited : ltac2:(tb__ "0|3|
S57OF_;S43S27S3S14S40Q40A1A1S1fS13S45R4A1S19A3S29R4A1S51S39R7S26S6cS39A1M0S2bU0A1M1S22R6R5A5A3S59S39R8S50S39S26G0G1S22R7R6A5S25S23G1S22A3R5R4A5S3fS39S4bR5R4S11S12S3aS3eA2M2S10S3aS3eS24S23G1S22A3S28G0VCST;VXGL;R7R6A5A4S15G2A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Hii HKc Hokf.
  Time (apply (free_null_uninited CST XGL HCST HXGL HCST2 0%nat); fni_close).
Qed.

Theorem free_null_contract_0_uninited_ex : ltac2:(tb__ "0|3|
S43S27S3S14S40Q40A1A1S1fS13S45R4A1S19A3S29R4A1S58S39S50S39S26S6cS39A1M0S2bU0A1M1S22R6R5A5S25S23G1S22A3R4R3A5S3fS39S4bR4R3S11S12S3aS3eA2M2S10S3aS3eS24S23G1S22A3S28G0VCST;VXGL;R6R5A5A4S15G2A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Hii HKc.
  Time (apply (free_null_uninited_ex CST XGL HCST HXGL HCST2 0%nat); fni_close).
Qed.

Theorem free_null_contract_0_uninited_orpc : ltac2:(tb__ "0|3|
S57OF_;S43S27S3S14S40Q40A1A1S1fS13S45R4A1S19A3S29R4A1S51S39R7S26S6cS39A1M0S2bU0A1M1S2aR6R5A5A3S59S39R8S50S39S26G0G1S2aR7R6A5S25S23G1S2aA3R5R4A5S3fS39S4bR5R4S11S12S3aS3eA2M2S10S3aS3eS24S23G1S2aA3S28G0VCST;VXGL;R7R6A5A4S15G2A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof. exact free_null_contract_0_uninited. Qed.
Theorem free_null_contract_0_uninited_orpc_ex : ltac2:(tb__ "0|3|
S43S27S3S14S40Q40A1A1S1fS13S45R4A1S19A3S29R4A1S58S39S50S39S26S6cS39A1M0S2bU0A1M1S2aR6R5A5S25S23G1S2aA3R4R3A5S3fS39S4bR4R3S11S12S3aS3eA2M2S10S3aS3eS24S23G1S2aA3S28G0VCST;VXGL;R6R5A5A4S15G2A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;").
Proof. exact free_null_contract_0_uninited_ex. Qed.

Theorem free_null_contract_0 : ltac2:(tb__ "0|3|
S36S57OF_;S43S27S3S14S40Q40A1A1S29R3A1S51S39R6S26S6cS39A1M0S2bU0A1M1R7R5R4A5A3S59S39R7S50S39S26G0G1R8R6R5A5S25S23G1R8A3R4R3A5S3fS39S4bR4R3S11S12S3aS3eA2M2S10S3aS3eS24S23G1R8A3S28G0VCST;VXGL;R6R5A5A4S15G2A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;Fst;").
Proof.
  intros st ok A Kc rho tp HKc Hokf. destruct (aa_internal_inited A) eqn:Hii.
  - destruct st; [exact (free_null_contract_0_inited CST XGL HCST HXGL HCST2 ok A Kc rho tp Hii HKc Hokf)
                 | exact (free_null_contract_0_inited_orpc CST XGL HCST HXGL HCST2 ok A Kc rho tp Hii HKc Hokf)].
  - destruct st; [exact (free_null_contract_0_uninited ok A Kc rho tp Hii HKc Hokf)
                 | exact (free_null_contract_0_uninited_orpc ok A Kc rho tp Hii HKc Hokf)].
Qed.
Theorem free_null_contract_0_ex : ltac2:(tb__ "0|3|
S36S43S27S3S14S40Q40A1A1S29R3A1S58S39S50S39S26S6cS39A1M0S2bU0A1M1R6R5R4A5S25S23G1R6A3R3R2A5S3fS39S4bR3R2S11S12S3aS3eA2M2S10S3aS3eS24S23G1R6A3S28G0VCST;VXGL;R5R4A5A4S15G2A1A3A5A3F_;Ftp;Frho;FKc;FA;Fst;").
Proof.
  intros st A Kc rho tp HKc. destruct (aa_internal_inited A) eqn:Hii.
  - destruct st; [exact (free_null_contract_0_inited_ex CST XGL HCST HXGL HCST2 A Kc rho tp Hii HKc)
                 | exact (free_null_contract_0_inited_orpc_ex CST XGL HCST HXGL HCST2 A Kc rho tp Hii HKc)].
  - destruct st; [exact (free_null_contract_0_uninited_ex A Kc rho tp Hii HKc)
                 | exact (free_null_contract_0_uninited_orpc_ex A Kc rho tp Hii HKc)].
Qed.
End Inst.
