(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "app"; "list"; "prod"; "nil"; "bool"; "true"; "length"; "None"; "false"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "sobj"; "valuation"; "agree_below"; "FcsrFrm0"; "SVar"; "mkSS"; "rw"; "swf"; "rm"; "sprop_below"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "AE_A"; "unwind_factsS"; "KcA"; "malloc_depth"; "pre_facts"; "A_globals"; "Pre_mallocI"; "ae_malloc"; "stack_win"; "unwind_objs"; "J_alloc_preT"; "Kc_ok"; "UStopLe"; "UStopLeOrPc"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cs_cache"; "aa_cls"; "aa_geom"; "aa_ptr_committed"; "aa_sec"; "ag_ctx"; "ag_pab"; "ag_spacebeg"; "ag_stack_bottom"; "ag_stack_top"; "ag_thread"; "ageom"; "class_state"; "cs_empty"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI.SPINE"; "stopJ_stable"; "cls_of"; "cst_of"; "rhoM_of"; "sa_m"; "secneeded"; "chk_of"; "cnt_of"; "needed8"; "sb_m"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "pre_regs"; "setregs"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "land"; "le"; "lt"; "of_nat"; "div"; "leb"; "max"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "F_geom_fn"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "F_hi"; "F_lo"; "F_s1"; "RT_m1"; "P0_s1"; "vRIS"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "round_up"; "rz"; "Size"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "N_m1"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "nthZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "coverb"; "zseq"; "@Stdlib.ZArith.ZArith_dec"; "Z_lt_dec"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma rup8_table : ltac2:(tb__ "0|1|
S20S7S53SeSeS5aS55R1Zfffffffffffffff8A2Zfc00M0A2Lx;S82Z8S5dG0A1A2A3S8A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rup8_le : ltac2:(tb__ "0|0|
SeS21S56Z1R1A2S57R1Zfc01A2A2S56S55S54R2Z7A2Zfffffffffffffff8A2Zfc00A2F_;Fn;").
Proof.
  intros n Hn.
  pose proof (proj1 (forallb_forall _ _) rup8_table (n + 7) ltac:(apply (proj2 (in_zseq _ _ _)); rewrite Z2Nat.id by lia; lia)) as H.
  cbn beta in H. apply Z.leb_le in H. exact H.
Qed.

Definition N_m5 : list carve_spec := ltac2:(tb__ "0|1a|
S1S5S5S5S10SeA2M0SeA2M1S4S5S5SeS2A2M2S10A2M3A1M4A2M5S0G1G4S0G0SeS0S10SeS12Z0A1M6Zeddb8M7A4Zeddc4A4S1G3S0G2S10S0SeS2G7U8M8A4S6cA4S1G3S0G2S10S0SeS2Zeddc0U4M9A4S12ZffffffffA1A4S6G3A1MaA3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Zeddc8MbA4Zeddd1A4S1G3S0G2S10S0SeS2GbG8A4S6bA4S1G3S0G2S10S0SeS2Zeddd0U1McA4G6A4GaA3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Zeebb8MdA4Zeebc4A4S1G3S0G2S10S0SeS2GdG8A4S12S5cZ2Z28A2A1A4S1G3S0G2S10S0SeS2Zeebc0U2MeA4S12Z10A1A4S1G3S0G2S10S0SeS2Zeebc2GeA4S12Z800A1A4GaA3A3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Z173662MfA4Z173663A4S1G3S0G2S10S0SeS2GfGcA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z182fb8M10A4Z182fc0A4S1G3S0G2S10S0SeS2G10G8A4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z18302cM11A4Z18302dA4S1G3S0G2S10S0SeS2G11GcA4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Ze9af0M12A4Ze9af8A4S1G3S0G2S10S0SeS2G12G8A4S12Zde378A1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Zeec4dM13A4Zeec4eA4S1G3S0G2S10S0SeS2G13GcA4S12Z1A1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z182ec0M14A4Z182ed0A4S1G3S0G2S10S0SeS2G14G8A4G6A4S1G3S0G2S10S0SeS2Z182ec8G8A4G6A4GaA3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Z6245c8M15A4Z6245ccA4S1G3S0G2S10S0SeS2G15G9A4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z182fa0M16A4Z182fa8A4S1G3S0G2S10S0SeS2G16G8A4S12ZffffffffffffffffA1A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Zeec24M17A4Zeec30A4S1G3S0G2S10S0SeS2G17G9A4S12Z1000A1A4S1G3S0G2S10S0SeS2Zeec28G9A4G6A4S1G3S0G2S10S0SeS2Zeec2cG9A4S12ZbeA1A4GaA3A3A3A4S1G5S0G1G4S0G0SeS0S10SeG6Z183018M18A4Z18301cA4S1G3S0G2S10S0SeS2G18G9A4G6A4GaA3A4S1G5S0G1G4S0G0SeS0S10SeG6Z182f1cM19A4Z182f20A4S1G3S0G2S10S0SeS2G19G9A4G6A4GaA3A4S6G5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition N_m1 : list carve_spec := N_rest ++ N_m5.
Lemma N_m1_ok : ltac2:(tb__ "0|0|
S20S4S13A1S77S72S13S73S75A4S69A3").
Proof. reflexivity. Qed.
Lemma N_m1_coverb : ltac2:(tb__ "0|0|
S20S7S53S72S81S75A3S8A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_m1_small : Forall spec_small N_m1.
Proof.
  unfold N_m1, N_rest, N_fn, N_m5, spec_small. cbn [tl app].
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.

Section SPINE.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S2fVAInv;VW;Vst;VA;VKc;S17PcA1A6").

Hypothesis law_die : ltac2:(tb__ "0|0|
S34S14S4S1eQ40A1A1S60VAInv;R4R3R2R1A4S7eS80Vsegs;S1bR4A1A2S7fZ182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Definition needed8 (n : Z) : Z := ltac2:(tb__ "0|1|
S54S6eS5bVn;Z8M0A2G0A2S6fVn;A1A2").
Definition cls_of (n : Z) : Z := ClassID (needed8 n).
Definition cst_of (A : AA) (n : Z) : class_state := ltac2:(tb__ "0|0|
S7dS41S36VA;A1S45Vn;A1S42A4").
Definition cnt_of (A : AA) (n : Z) : Z := ltac2:(tb__ "0|0|
S58S9SeS35S46VA;Vn;A2A1A2A1").
Definition chk_of (A : AA) (n : Z) : Z := ltac2:(tb__ "0|1|
S78SeS76S9SeS35S46VA;Vn;A2A1M0A2U1A2G0Z0A4").

Definition secneeded (n : Z) : Z := round_up n 8 + 4096.
Definition secmapsize (n : Z) : Z := ltac2:(tb__ "0|0|
S54S6eS49Vn;A1S6dA2S6dA2").
Definition rhoM_of (A : AA) (rho : valuation) : valuation := ltac2:(tb__ "0|5|
S37VA;A1S40S1fQ40M0S19Vrho;PcA2A2SeS74Vrho;S1S5SfS1eG0A1M1A2M2S0SfG1P97S1dG0S3fR2A1A2A4S1G2S0SfG1P98S1dG0S3aR2A1A2A4S1G2S0SfG1P99S1dG0S3eR2A1A2A4S1G2S0SfG1P9aS1dG0S3dR2A1A2A4S1G2S0SfG1P9bS1dG0S3cR2A1M3A2A4S1G2S0SfG1P9cS1dG0S54G3S71A2A2A4S1G2S0SfG1P94S1dG0S70S45R1A1M4A1A2A4S1G2S0SfG1P95S1dG0S4bVA;R1A2A2A4S1G2S0SfG1P96S1dG0S6fR1A1A2A4S1G2S0SfG1P9dS1dG0S4cR1A1A2A4S1G2S0SfG1P9eS1dG0G4A2A4S1G2S0SfG1P9fS1dG0S4aVA;R1A2A2A4S1G2S0SfG1P8dS1dG0S49R1A1A2A4S1G2S0SfG1P8eS1dG0S4eR1A1A2A4S1G2S0SfG1P91S1dG0S3bR2A1A2A4S1G2S0SfG1P92S1dG0S59S38VA;A1Z8A2A2A4S1G2S0SfG1P93S1dG0S58S9S43S39VA;A1A2A1A2A4S6G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2Tn;TG;").

Lemma rhoM_agree : ltac2:(tb__ "0|0|
S34S14S15S4fR1S47R2R1A2A3Frho;FA;").
Proof.
  intros. apply agree_below_rho_sets. intros j v Hin. cbn in Hin. unfold NF.
  repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; cbv; discriminate|]). destruct Hin.
Qed.

Definition stopJ_stable (W : list ulink) (st : ustop) : Prop := ltac2:(tb__ "0|1|
S14S14S15S4fR2R1A3S33VW;Vst;R3A3M0G0F_;F_;Frho';Frho;").
Lemma stopJ_stable_nil : ltac2:(tb__ "0|0|
S24S44S6S23A1R1A2Fst;").
Proof. intros st rho rho' _ H. exact H. Qed.
Lemma stopJ_stable_le : ltac2:(tb__ "0|0|
S4S23A1S44R1S31A2FW;").
Proof. intros W rho rho' _ H. unfold unwind_stopJ in *. destruct W; exact I. Qed.

Lemma JM_agree : ltac2:(tb__ "0|0|
S4S23A1S24S34S27S14S14S4S1eQ40A1A1S4S61A1S60S44R9R8A2S15S4fR6R5A3VJ;RbRaR9R8R7R5R4R3A8VJ;RcRbRaR9R7R6R5R4A8F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho rho' tp tr md HUS Hag (HA & HK & Htp & HU & HB & HN & Htop). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (E12 : eval rho' (SVar 12) = eval rho (SVar 12)) by (cbn; symmetry; apply Hw; unfold NF; lia).
  split; [unfold AInv, AInvA in *; rewrite Erm; exact HA|]. split; [exact HK|].
  split; [unfold tp_ok in *; rewrite <- (Hw 24%positive) by (unfold NF; lia); exact Htp|].
  split; [exact (HUS rho rho' Hag HU)|].
  rewrite E12. split; [exact HB |]. split; [exact HN|].
  unfold top_high in *. rewrite <- (Hw 10%positive) by (unfold NF; lia). rewrite <- (Hw V_DEPTH) by (unfold NF, V_DEPTH; lia). exact Htop.
Qed.

Lemma JM_stableA : ltac2:(tb__ "0|0|
S4S23A1S24S34S27S44R4R3A2S30R2A1S63Vsegs;S7cVJ;R6R5R4R3A4A3F_;F_;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc HUS HKc rho rho' tp tr md md' Hag Hme HJ.
  pose proof (JM_agree W st A Kc rho rho' tp tr md HUS ltac:(eapply agree_below_le; [|exact Hag]; cbv; discriminate) HJ) as (HA & HK & Htp & HU & HB & HN & Htop).
  split; [apply (AInvA_mat segs A rho' tp md md'); [exact HA | exact Hme]|].
  split; [destruct Hme as ((mat' & ->) & _); rewrite with_vm_backing_with_vm; apply HKc; exact HK|].
  split; [exact Htp|]. split; [exact HU|]. split; [|split; [exact HN | exact Htop]].
  destruct Hme as ((mat' & ->) & _). exact HB.
Qed.

Definition sa_m (W : list ulink) (st : ustop) : sstate := ltac2:(tb__ "0|1|
S18S2cS25A1S52S51S1S5S2S10A2M0S0S2S10U4S12S5eA1A4S6G0A1A3A2S50S16SaS10A1S1S13S2dS3S13S2eVW;A1S2aA3A3S3S11S26VW;Vst;A2S29S28A1A3S4fSbA9").
Definition sb_m (W : list ulink) (st : ustop) : sstate := ltac2:(tb__ "0|1|
S18S2cS25A1S52S51S1S5S2S10A2M0S0S2S10U4S12S5eA1A4S6G0A1A3A2S50S16SaS10A1S3S13S1S13S2dS3S13S2eVW;A1S2aA3A3S69A3S3S11S26VW;Vst;A2S29S28A1A3S65SbA9").

Local Ltac civ_try2F HR n :=
  eapply (civ_nth2 _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Local Ltac civ_any2F HR := first [ civ_try2F HR 43%nat | civ_try2F HR 44%nat | civ_try2F HR 45%nat | civ_try2F HR 46%nat | civ_try2F HR 47%nat | civ_try2F HR 48%nat | civ_try2F HR 49%nat | civ_try2F HR 50%nat | civ_try2F HR 51%nat | civ_try2F HR 52%nat | civ_try2F HR 53%nat | civ_try2F HR 54%nat | civ_try2F HR 0%nat | civ_try2F HR 1%nat | civ_try2F HR 2%nat | civ_try2F HR 3%nat | civ_try2F HR 4%nat | civ_try2F HR 5%nat | civ_try2F HR 6%nat | civ_try2F HR 7%nat | civ_try2F HR 8%nat | civ_try2F HR 9%nat | civ_try2F HR 10%nat | civ_try2F HR 11%nat | civ_try2F HR 12%nat | civ_try2F HR 13%nat | civ_try2F HR 14%nat | civ_try2F HR 15%nat | civ_try2F HR 16%nat | civ_try2F HR 17%nat | civ_try2F HR 18%nat | civ_try2F HR 19%nat | civ_try2F HR 20%nat | civ_try2F HR 21%nat | civ_try2F HR 22%nat | civ_try2F HR 23%nat | civ_try2F HR 24%nat | civ_try2F HR 25%nat | civ_try2F HR 26%nat | civ_try2F HR 27%nat | civ_try2F HR 28%nat | civ_try2F HR 29%nat | civ_try2F HR 30%nat | civ_try2F HR 31%nat | civ_try2F HR 32%nat | civ_try2F HR 33%nat | civ_try2F HR 34%nat | civ_try2F HR 35%nat | civ_try2F HR 36%nat | civ_try2F HR 37%nat | civ_try2F HR 38%nat | civ_try2F HR 39%nat | civ_try2F HR 40%nat | civ_try2F HR 41%nat | civ_try2F HR 42%nat ].

Local Ltac lia_only v := repeat match goal with H : context [v] |- _ => revert H end; clear - v; intros; lia.
Local Ltac wr_cell2F HR n off tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell;
  [ lazymatch goal with |- ?x + _ <= ?x + _ < _ => idtac end; lia_only off | lia | tacW | lia ].
Local Ltac wr_any2F HR off tacW := first [ wr_cell2F HR 43%nat off tacW | wr_cell2F HR 44%nat off tacW | wr_cell2F HR 45%nat off tacW | wr_cell2F HR 46%nat off tacW | wr_cell2F HR 47%nat off tacW | wr_cell2F HR 48%nat off tacW | wr_cell2F HR 49%nat off tacW | wr_cell2F HR 50%nat off tacW | wr_cell2F HR 51%nat off tacW | wr_cell2F HR 52%nat off tacW | wr_cell2F HR 53%nat off tacW | wr_cell2F HR 54%nat off tacW ].

Lemma m_instantiate : ltac2:(tb__ "0|c|
S4S23A1M0S24S34S27S14S4S1eQ40M1A1A1S79S20S24R6S32A3S20G0R8S6S23A1A3F_;S44R8R7A2S20S7S1aS48R9R8A2A1S8A3S20SdS5S4S5S10S10A2M2A1M3S4S11A1M4A2M5A1S7aS7bS2bS25RaR9A3A1S48RaR9A2A2ScG5S0G3G4S1G2S0S10S10S17P18A1S12S5eA1A4S6G2A1A3S6S11A1A4A2A3S20S7S1aS4dRbRaA2A1S8A3S20S7S53S11S1cS65A1M6S3S11S3S11S3S11S3S11S26RcRbA2S29S28A1M7A3S64A3S68A3S66A3A3S8A3S20S7S53S11G6S3S11S3S11S3S11S3S11S26RdRcA2G7A3S64A3S68A3S67A3A3S8A3S62Vsegs;VJ;ReRdRcRbA4S2bS25ReRdA3RaR9R8A6S62Vsegs;VJ;RfReRdRcA4S6aRfReS5fS57S1fG1S19RbPcA2A2M8Zfc01M9A2MaS22GaA1MbA2G4L_;S83G8G9A2GaS67L_;GbS66L_;X5fx2A3S47RdRbA2RaR9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w HW HUS Wa Da Wb Fbh Fbl H.
  set (rho1 := rhoM_of A rho).
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
  cbn [eval] in HN. pose proof (urange (rw rho 12%positive)) as U12.
  assert (TOPlo : topG (aa_geom A) <= fst (obj_range rho1 stack_win)) by (unfold stack_win; rewrite own_lo; exact Htop).

  assert (H1 : SPA segs (J W st A Kc) (Pre_mallocI AE_A W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|apply rhoM_agree]; cbv; discriminate | apply JM_agree; [exact HUS | apply rhoM_agree]]. }
  clear H HsmA.

  assert (H2 : SPA segs (J W st A Kc) (mkAX (sa_m W st) [] base_sv) rho1 tp w).
  { change (mkAX (sa_m W st) [] base_sv) with (ax_setS (Pre_mallocI AE_A W st) (sa_m W st)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H1].
    constructor; [|constructor]. cbn [fst snd eval]. rewrite E24. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H1.

  destruct HRest as (Hsep & _ & _ & _ & _ & _ & _ & HTH & HMI). unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG0 | lia]).

  destruct HMI as [HMIc _]. pose proof (Forall_inv (Forall_inv_tail HMIc)) as HPP.
  assert (HPP' : cell_ok (view segs (rm rho)) (mkACell (0 + 0xeec4d) 1 1)).
  { intros j Hj. specialize (HPP j Hj). cbn [c_addr c_w c_val] in HPP, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HPP; [exact HPP | apply fs_footb_img; [exact HG0 | lia]]. }

  pose proof (law_die A rho tp _ HA) as HDIE.
  assert (HDIE' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x182f1c) 4 0)) by (rewrite Z.add_0_l; exact HDIE).

  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HMIc))) as HCSD.
  assert (HCSD' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x183018) 4 0)).
  { intros j Hj. specialize (HCSD j Hj). cbn [c_addr c_w c_val] in HCSD, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HCSD; [exact HCSD | apply fs_footb_img; [exact HG0 | lia]]. }
  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_m]; apply in_or_app; right; cbn; tauto).
  destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W']; [constructor|].
    destruct st; [|discriminate (HW eq_refl)].
    assert (HC : Forall (holds rho1) (chain_pre (l :: W'))).
    { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_m]. apply in_or_app. left. apply chain_pre_in. exact Hp. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; clear TI CI G15 G16 G17 G18 G19 G20 G21; lia. }

  assert (H3 : SPA segs (J W st A Kc) (mkAX (sb_m W st) [] base_sv) rho1 tp w).
  { change (mkAX (sb_m W st) [] base_sv) with
      (ax_setS (mkAX (sa_m W st) [] base_sv) (let S := ax_S (mkAX (sa_m W st) [] base_sv) in
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
           | |- cells_in_view _ _ 0 [(0xeec4d, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0xeec4d 1 1 (SLit 1) HPP' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ 0 [(0x182f1c, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0x182f1c 4 0 (SLit 0) HDIE' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ 0 [(0x183018, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0x183018 4 0 (SLit 0) HCSD' eq_refl ltac:(lia) ltac:(lia))
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
      unfold N_m1, N_rest, N_fn, N_m5. cbn [tl app map carve_obj ss_objs ax_S sa_m]. unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
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

  change (P0_s1 W st (if Z_lt_dec (bv_unsigned (rw rho 12%positive)) 64513 then F_lo else F_hi)) with
    (ax_with_facts (mkAX (sb_m W st) [] base_sv)
       ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ (if Z_lt_dec (bv_unsigned (rw rho 12%positive)) 64513 then F_lo else F_hi))).
  eapply SPA_refacts; [exact H3 | destruct (Z_lt_dec _ _); [exact Fbl | exact Fbh] |].
  intros Hold. apply Forall_app. split; [apply Forall_app; split; [apply Forall_app; split; [exact Hold|]|]|].
  - unfold F_geom_fn, vT, vCTX, vTOP, vBOT. clear TI CI G15 G16 G17 G18 G19 G20 G21.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E151, ?E152, ?E153, ?E154; rewrite ?u64_lit by lia; try lia.
  - unfold F_s1, vSB, vRIS. unfold HIGH_SHADOW_END. rewrite kSpaceSize_val. clear TI CI G15 G16 G17 G18 G19 G20 G21.
    cbn [fst snd] in SW1, SW2. pose proof (urange (rw rho 10%positive)) as U10.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E155, ?E156, ?E12, ?E10; rewrite ?kSpaceSize_val; rewrite ?u64_lit by lia; try lia.
    +
      cbn [branch_taken]. unfold bv_eqb. rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. apply Z.eqb_refl.
    +
      intros E. cbn [branch_taken] in E. unfold bv_eqb in E. rewrite add_val in E. rewrite (u64_lit 0) in E by lia.
      replace (bv_unsigned (Z_to_bv 64 (-2128))) with (2 ^ 64 - 2128) in E by reflexivity.
      rewrite E10 in SW2. set (sp := bv_unsigned (rw rho 10%positive)) in *.
      replace (sp + (2 ^ 64 - 2128)) with ((sp - 2128) + 1 * 2 ^ 64) in E by lia.
      rewrite Z.mod_add in E by lia. rewrite Z.mod_small in E by lia. apply Z.eqb_eq in E. lia.
  - destruct (Z_lt_dec (bv_unsigned (rw rho 12%positive)) 64513) as [Hlt|Hge]; unfold F_lo, F_hi, rup8.
    + repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E12; rewrite ?u64_lit by lia; [lia|].
      rewrite and_val, add_val, !u64_lit by lia. replace (bv_unsigned (Z_to_bv 64 18446744073709551608)) with 18446744073709551608 by reflexivity.
      rewrite Z.mod_small by lia. apply rup8_le. lia.
    + repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E12; rewrite ?u64_lit by lia. lia.
Qed.
End SPINE.
