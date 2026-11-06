(* reac-pw/fuzz_segconf, image A: the 21 walks of groups G4 and G5 (the G4 / G5 walks) composed with each other, at the walks'
   own abstract listing instance (`Context {PI : PAImg seg_listing}`, the image-A owner's ruling: entries BASE + AF_<F>, call
   targets pa_sigma SS_<x>) and allocator record B. Each callee contract a G4 / G5 walk takes is discharged here by
   that callee's walk; what is left are Section hypotheses of exactly the walks' own texts:
   - the record and listing facts (PALib, PALibF, model_laws, seg_sig_prog, seg_val_objs, seg_val_relro, errno_rom,
     ro_below_ofl, dc_sspP), which lib/A/Prog/SegProgClosed.v discharges at image A's instance SegImg.PB_seg and the
     core's record SegB (SegRecRest seg_palib / seg_palibf / seg_model_laws / seg_sig_prog_PB / seg_val_objs_PB /
     seg_val_relro_PB, the core AD2l's errno_rom lemma, SegRecRo.ROB, SegRecCells.seg_ssp);
   - the runtime rows (the interceptor layer's interface rows and the kit's intrinsic / side-stack laws), each at the listing's
     call target.
   The walks (lib/A/Prog/<F>.v) are the G4 / G5 walks' 21 counted shas, from their integration head
   a15759b59213, merged into this close; FINAL
   6f783602b5e3 is an ancestor of each (INSTANTIATE.md section E). This file states no contract: each lemma's
   statement is the contract of lib/A/Prog/<F>_c.v at contracts FINAL 6f783602b5e3, at SegInstA's terms.
   proves no function (kind: merge; the composition of G4 / G5's walk theorems). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable SegSyms SegList SegPa SegPaLib PaLibF SegObj SegGlob SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
check_segments_c check_declared_c check_knock_refused_c reac_segconf_role_file_c reac_segconf_role_c
reac_segconf_init_c check_model_c check_refusals_c check_ignore_c check_role_c check_address_c check_absent_c
name_ok_c check_provenance_c reac_segconf_ignore_file_c reac_segconf_ignored_c reac_segconf_model_c
reac_declared_vlan_add_c reac_declared_vlan_split_c reac_segconf_declared_c reac_segconf_find_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require reac_segconf_declared_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require
check_segments check_declared check_knock_refused reac_segconf_role_file reac_segconf_role reac_segconf_init
check_model check_refusals check_ignore check_role check_address check_absent name_ok check_provenance
reac_segconf_ignore_file reac_segconf_ignored reac_segconf_model reac_declared_vlan_add reac_declared_vlan_split
reac_segconf_declared reac_segconf_find.
Import ListNotations.
Local Open Scope Z_scope.

Create HintDb g45.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
Section e.
Variable B : asyms.

(* ---- the record and listing facts (the walks' own texts) ---------------------------------------------- *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis HVO : seg_val_objs (PI := PI).
Hypothesis VRELRO : seg_val_relro (PI := PI).
Hypothesis ERRNO : errno_rom SEGS B.
Context {RO : ro_below_ofl SEGS RLO_A RHI_A}.
Hypothesis SSP : reac_segconf_declared_d.dc_sspP B gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---- the runtime rows, at the listing's call targets (the walks' own texts) --------------------------- *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState,
  @RtString.astrncmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncmp).
Hypothesis ASTRSTR : forall fx0 : YK11.FPState,
  @RtSeg.astrstr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strstr) SegInstA.gotwA SegInstA.guardA.
Hypothesis AISALNUM : forall fx0 : YK11.FPState, @RtSeg.aisalnum_realizes fx0 rc SEGS B (SIG SS_isalnum).
Hypothesis ASTRNCPY : forall fx0 : YK11.FPState,
  @RtSeg.astrncpy_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncpy).
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strrchr).
Hypothesis ASTRTOL0 : forall fx0 : YK11.FPState,
  @RtSeg.astrtol0_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strtol) gotwA guardA.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis ASM1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.

#[local] Hint Resolve YG0q.AR_laws_ok : g45.

(* ---- G5: reac_segconf_find, the query every other query calls ------------------------------------------ *)
Lemma cl_reac_segconf_find : forall fx0 : YK11.FPState,
  reac_segconf_find_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_find) STK_reac_segconf_find RLO_A RHI_A.
Proof. intros fx0. eapply reac_segconf_find.reac_segconf_find_walk; eauto with g45. Qed.
#[local] Hint Resolve cl_reac_segconf_find : g45.

(* ---- G5: the reader's init, the queries over find, and the ten checkers ------------------------------- *)
Lemma cl_reac_segconf_init : forall fx0 : YK11.FPState,
  reac_segconf_init_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_init) STK_reac_segconf_init.
Proof. intros fx0. eapply reac_segconf_init.reac_segconf_init_walk; eauto with g45. Qed.
Lemma cl_reac_segconf_role_file : forall fx0 : YK11.FPState,
  reac_segconf_role_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role_file) STK_reac_segconf_role_file
    RLO_A RHI_A.
Proof. intros fx0. eapply reac_segconf_role_file.reac_segconf_role_file_walk; eauto with g45. Qed.
Lemma cl_reac_segconf_role : forall fx0 : YK11.FPState,
  reac_segconf_role_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role) STK_reac_segconf_role RLO_A RHI_A.
Proof. intros fx0. eapply reac_segconf_role.reac_segconf_role_walk; eauto with g45. Qed.
Lemma cl_reac_segconf_ignore_file : forall fx0 : YK11.FPState,
  reac_segconf_ignore_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignore_file)
    STK_reac_segconf_ignore_file RLO_A RHI_A.
Proof. intros fx0. eapply reac_segconf_ignore_file.reac_segconf_ignore_file_walk; eauto with g45. Qed.
Lemma cl_reac_segconf_ignored : forall fx0 : YK11.FPState,
  reac_segconf_ignored_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignored) STK_reac_segconf_ignored
    RLO_A RHI_A.
Proof. intros fx0. eapply reac_segconf_ignored.reac_segconf_ignored_walk; eauto with g45. Qed.
Lemma cl_reac_segconf_model : forall fx0 : YK11.FPState,
  reac_segconf_model_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_model) STK_reac_segconf_model RLO_A RHI_A.
Proof. intros fx0. eapply reac_segconf_model.reac_segconf_model_walk; eauto with g45. Qed.
#[local] Hint Resolve cl_reac_segconf_role cl_reac_segconf_ignored cl_reac_segconf_model : g45.
Lemma cl_check_absent : forall fx0 : YK11.FPState,
  check_absent_contract (fx := fx0) SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
Proof. intros fx0. eapply check_absent.check_absent_walk; eauto with g45. Qed.
Lemma cl_check_segments : forall fx0 : YK11.FPState,
  check_segments_contract (fx := fx0) SEGS B (BASE + AF_check_segments) STK_check_segments RLO_A RHI_A.
Proof. intros fx0. eapply check_segments.check_segments_walk; eauto with g45. Qed.
Lemma cl_check_role : forall fx0 : YK11.FPState,
  check_role_contract (fx := fx0) SEGS B (BASE + AF_check_role) STK_check_role.
Proof. intros fx0. eapply check_role.check_role_walk; eauto with g45. Qed.
Lemma cl_check_model : forall fx0 : YK11.FPState,
  check_model_contract (fx := fx0) SEGS B (BASE + AF_check_model) STK_check_model RLO_A RHI_A.
Proof. intros fx0. eapply check_model.check_model_walk; eauto with g45. Qed.
Lemma cl_check_ignore : forall fx0 : YK11.FPState,
  check_ignore_contract (fx := fx0) SEGS B (BASE + AF_check_ignore) STK_check_ignore.
Proof. intros fx0. eapply check_ignore.check_ignore_walk; eauto with g45. Qed.
Lemma cl_check_provenance : forall fx0 : YK11.FPState,
  check_provenance_contract (fx := fx0) SEGS B (BASE + AF_check_provenance) STK_check_provenance RLO_A RHI_A.
Proof. intros fx0. eapply check_provenance.check_provenance_walk; eauto with g45. Qed.
Lemma cl_check_refusals : forall fx0 : YK11.FPState,
  check_refusals_contract (fx := fx0) SEGS B (BASE + AF_check_refusals) STK_check_refusals.
Proof. intros fx0. eapply check_refusals.check_refusals_walk; eauto with g45. Qed.
Lemma cl_check_address : forall fx0 : YK11.FPState,
  check_address_contract (fx := fx0) SEGS B (BASE + AF_check_address) STK_check_address RLO_A RHI_A.
Proof. intros fx0. eapply check_address.check_address_walk; eauto with g45. Qed.
Lemma cl_check_knock_refused : forall fx0 : YK11.FPState,
  check_knock_refused_contract (fx := fx0) SEGS B (BASE + AF_check_knock_refused) STK_check_knock_refused
    RLO_A RHI_A seg_litA_fz gotwA guardA.
Proof. intros fx0. eapply check_knock_refused.check_knock_refused_walk; eauto with g45. Qed.
Lemma cl_check_declared : forall fx0 : YK11.FPState,
  check_declared_contract (fx := fx0) SEGS B (BASE + AF_check_declared) STK_check_declared RLO_A RHI_A.
Proof. intros fx0. eapply check_declared.check_declared_walk; eauto with g45. Qed.

(* ---- G4: the declared-VLAN family ---------------------------------------------------------------------- *)
Lemma cl_name_ok : forall fx0 : YK11.FPState,
  name_ok_contract (fx := fx0) SEGS B (BASE + AF_name_ok) STK_name_ok RLO_A RHI_A.
Proof. intros fx0. eapply name_ok.name_ok_walk; eauto with g45. Qed.
#[local] Hint Resolve cl_name_ok : g45.
Lemma cl_reac_declared_vlan_split : forall fx0 : YK11.FPState,
  reac_declared_vlan_split_contract (fx := fx0) SEGS B (BASE + AF_reac_declared_vlan_split)
    STK_reac_declared_vlan_split RLO_A RHI_A gotwA guardA.
Proof. intros fx0. eapply reac_declared_vlan_split.reac_declared_vlan_split_walk; eauto with g45. Qed.
Lemma cl_reac_declared_vlan_add : forall fx0 : YK11.FPState,
  reac_declared_vlan_add_contract (fx := fx0) SEGS B (BASE + AF_reac_declared_vlan_add) STK_reac_declared_vlan_add
    RLO_A RHI_A.
Proof. intros fx0. eapply reac_declared_vlan_add.reac_declared_vlan_add_walk; eauto with g45. Qed.
#[local] Hint Resolve cl_reac_declared_vlan_split cl_reac_declared_vlan_add : g45.
Lemma cl_reac_segconf_declared : forall fx0 : YK11.FPState,
  reac_segconf_declared_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_declared) STK_reac_segconf_declared
    RLO_A RHI_A gotwA guardA.
Proof. intros fx0. eapply reac_segconf_declared.reac_segconf_declared_walk; eauto with g45. Qed.

End e.
End f.
End d.
