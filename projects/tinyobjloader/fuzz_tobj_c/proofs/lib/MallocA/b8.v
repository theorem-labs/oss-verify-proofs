(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CRefillJ.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RefillJ.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.

(* [comment removed for export] *)
Module CRefillJP.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "or"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "piece"; "ph_set"; "ph_get"; "ph_quiet"; "pord"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "phase"; "zoneR"; "mlink"; "rlink"; "ph_f"; "mkPh"; "ph_cnt"; "ph_fill"; "ph_pop"; "ph_ri"; "ph_u"; "F0"; "U0"; "shpage"; "@Corelib.Init.Datatypes"; "nat"; "list"; "None"; "app"; "bool"; "false"; "option"; "length"; "prod"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "alloc_top"; "m_vm_lazy"; "maps_subtract"; "vm_limit"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP.JP"; "pbase"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CRefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive piece : Set := PU | PF.

Definition ph_get (p : piece) (ph : phase) : nat := ltac2:(tb__ "0|0|
S6S1aLp;Vp;S16Vph;A1S10Vph;A1X6x2").
Definition ph_set (p : piece) (n : nat) (ph : phase) : phase := ltac2:(tb__ "0|4|
S6ScLp;Vp;S11Vn;S10Vph;A1S13Vph;A1M0S14Vph;A1M1S12Vph;A1M2S15Vph;A1M3A6S11S16Vph;A1Vn;G0G1G2G3A6X6x2").

Definition pord (p : piece) (ph : phase) : Prop := ltac2:(tb__ "0|0|
S6OLp;Vp;S0S1aS10Vph;A1U0A3S5X6x2").
Definition ph_quiet (ph : phase) : Prop := ltac2:(tb__ "0|1|
S1S0SbS13Vph;A1Z0M0A3S1S0SbS14Vph;A1G0A3S1S0S1eS12Vph;A1S1fA3S0S1eS15Vph;A1S1fA3A2A2A2").

Lemma ph_get_set : ltac2:(tb__ "0|0|
S6S1aScS0S1aS8R3S7R3R2R1A3A2R2A3Fph;Fn;Fp;").
Proof. intros [|] n ph; reflexivity. Qed.
Lemma ph_set_set : ltac2:(tb__ "0|0|
S6S1aS1aScS0ScS7R4R2S7R4R3R1A3A3S7R4R2R1A3A3Fph;Fn';Fn;Fp;").
Proof. intros [|] n n' ph; reflexivity. Qed.
Lemma ph_quiet_set : ltac2:(tb__ "0|0|
S6S1aScS9R1A1S9S7R4R3R2A3A1F_;Fph;Fn;Fp;").
Proof. intros [|] n ph H; exact H. Qed.
Lemma pord_set : ltac2:(tb__ "0|0|
S6S1aScSaR3R1A2SaR4S7R4R3R2A3A2F_;Fph;Fn;Fp;").
Proof. intros [|] n ph H; exact H. Qed.

Section JP.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model).
Definition pbase (p : piece) : Z := ltac2:(tb__ "0|0|
S6SbLp;Vp;S18VA;Vrb;A2S17VA;Vrb;A2X6x2").

Lemma mlink_commit : ltac2:(tb__ "0|9|
S6ScS1bS32Q40A1M0A1S24S24SeVA;Vrb;Vtp0;Vmd0;R4R3R2A7S0S1aS8R6R5A2U0A3SaR7R6A2S0S1bS22G0G0A2A1M1S29S23R4A1A1S29S23R5A1M2A1A3S0G1S2bG2A1S2bS23R6A1M3A1A3S0SbS28G3A1S28S23R7A1M4A1A3S0SbS25G4A1S25S23R8A1M5A1A3S0G1S2aG5A1S27S2aS23R9A1A1S31RcA1M6S2dG6Z40000M7A2A3A3S0G1S26R9A1S27S26RaA1S31RdA1M8S2dG8G7A2A3A3S2eS33RaRcA2S2dS33RbRcA2G7A2A2SeVA;Vrb;Vtp0;Vmd0;S7RfU1ReA3RdRbA7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md md' HM Hg Ho EM ER EL ET EN ELz HP.
  unfold mlink in HM |- *. cbn zeta in HM |- *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  rewrite EM, ER, EL, ET, EN, ELz, M5, M6.
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  destruct p; cbn [ph_get pord pbase ph_set ph_u ph_f] in *.
  - rewrite Hg, Ho in *. unfold subU, subF, committed, revealedp, kUserMapSize in *. cbn [Nat.leb] in *.
    split; [reflexivity|]. split; [reflexivity|]. exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. lia.
  - rewrite Hg in *. unfold subF, committed, revealedp, kFreeArrayMapSize in *. cbn [Nat.leb] in *.
    split; [reflexivity|]. split; [reflexivity|]. exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. lia.
Qed.

Lemma mlink_reveal : ltac2:(tb__ "0|2|
S6ScS1bS32Q40A1M0A1M1S24G1SeVA;Vrb;Vtp0;Vmd0;R4R3R2A7S0S1aS8R6R5A2U1A3G0S34G0R1R4A3S1S2S34G0R2R7A3A1S19S31R9A1R2A2A2F_;Fq;S2eS30S21G0R4A2A1Z8A2S2eS33R6S1dG0R5R7A3A2S2dS33R6R7A2Z8000A2A2SeVA;Vrb;Vtp0;Vmd0;S7RaU2R9A3S1dG0R6R8A3R7A7F_;F_;F_;F_;F_;Ftpn;Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md tpn HM Hg Hq Hn HP.
  unfold mlink in HM |- *. cbn zeta in HM |- *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  destruct p; cbn [ph_get pbase ph_set ph_u ph_f] in *; rewrite Hg in *; unfold committed, revealedp in *; cbn [Nat.leb] in *.
  - split; [exact M5|]. split; [exact M6|]. exists (tpn ++ tp1). split; [rewrite M7, app_assoc; reflexivity|].
    split.
    { intros q Hin. apply in_app_or in Hin as [Hin|Hin].
      - destruct (Hq q Hin) as [N S]. split; [intros X; apply N; rewrite M7; apply in_or_app; right; exact X | left; split; [reflexivity | exact S]].
      - destruct (M8 q Hin) as [N [[X _]|X]]; [discriminate X|]. split; [exact N | right; exact X]. }
    split; [rewrite length_app, Nat2Z.inj_add; lia|].
    lia.
  - split; [exact M5|]. split; [exact M6|]. exists (tpn ++ tp1). split; [rewrite M7, app_assoc; reflexivity|].
    split.
    { intros q Hin. apply in_app_or in Hin as [Hin|Hin].
      - destruct (Hq q Hin) as [N S]. split; [intros X; apply N; rewrite M7; apply in_or_app; right; exact X | right; split; [reflexivity | exact S]].
      - destruct (M8 q Hin) as [N [X|[X _]]]; [|discriminate X]. split; [exact N | left; exact X]. }
    split; [rewrite length_app, Nat2Z.inj_add; lia|].
    lia.
Qed.

Lemma mlink_release : ltac2:(tb__ "0|0|
S6ScS1bS32Q40A1A1S24SeVA;Vrb;Vtp0;Vmd0;R3R2R1A7S0S1aS8R5R4A2U2A3SeVA;Vrb;Vtp0;Vmd0;S7R6U3R5A3R4R3A7F_;F_;Fmd;Ftp;Fph;Fp;").
Proof.
  intros p ph tp md HM Hg. unfold mlink in HM |- *. cbn zeta in HM |- *.
  destruct p; cbn [ph_get ph_set ph_u ph_f] in *; rewrite Hg in HM; exact HM.
Qed.

Lemma zone_commit : ltac2:(tb__ "0|0|
S6ScSbS0S1aS8R3R2A2U0A3S3SdVA;Vrb;S7R4U1R3A3R2A4SdVA;Vrb;R3R2A4A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp; cbn [Nat.leb]; tauto.
Qed.
Lemma zone_reveal : ltac2:(tb__ "0|1|
S6ScSbS0S1aS8R3R2A2U1A3S3SdVA;Vrb;S7R4U2R3A3R2A4S4SdVA;Vrb;R3R2A4S1S2eS35S31R4A1A1M0R2A2S2fR2S2dG0Z8000A2A2A2A2A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get pbase ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp; cbn [Nat.leb]; split; intros H; repeat (destruct H as [H|H]); try (destruct H as [X H]; try discriminate X); tauto.
Qed.
Lemma zone_release : ltac2:(tb__ "0|1|
S6ScSbS0S1aS8R3R2A2U2A3S3SdVA;Vrb;S7R4U3R3A3R2A4S4SdVA;Vrb;R3R2A4S1S2eS31R4A1M0R2A2S2fR2S2dG0Z40000A2A2A2A2A2F_;Fz;Fph;Fp;").
Proof.
  intros p ph z Hg. unfold zoneR. destruct p; cbn [ph_get pbase ph_set ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in *; rewrite Hg;
    unfold revealedp, releasedp, kUserMapSize, kFreeArrayMapSize; cbn [Nat.leb]; split; intros H; repeat (destruct H as [H|H]); try (destruct H as [X H]; try discriminate X); tauto.
Qed.

Lemma rlink_grow_quiet : ltac2:(tb__ "0|5|
ScScSbOF_;S2cS2cS2cS9R6A1M0G0SbS3SdVA;Vrb;R8R1A4S4SdVA;Vrb;R9R1A4R7R1A1A2A2Fz;SbS4R8R1A1M1S2G1A1A2Fz;SfVA;Vrb;RaR7R6A5SbS2RaR1A1A1S0S20S32Q8A1M2A1M3R8R2A1R9R2A1M4A3F_;Fz;SbRbR1A1S2S0G3G4S1cG2A1A3A1F_;Fz;SfVA;Vrb;RcRaR8A5F_;F_;F_;F_;F_;F_;F_;Fm';Fm;Fm0;FN;Fph';Fph;").
Proof.
  intros ph ph' N m0 m m' (Q1 & Q2 & Q3 & Q4) (Q1' & Q2' & Q3' & Q4') HZ ND (L1 & L2 & _) HO HI.
  unfold rlink. rewrite Q1', Q2', Q3', Q4'.
  split; [intros z Hz; rewrite HO by (intros X; apply Hz; apply HZ; right; exact X); apply L1; intros X; apply Hz; apply HZ; left; exact X|].
  split.
  { intros z Hz. apply HZ in Hz. destruct (ND z) as [Y|Y]; [exact (HI z Y)|]. rewrite (HO z Y). destruct Hz as [Hz|Hz]; [exact (L2 z Hz) | contradiction]. }
  split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
Qed.

Lemma rlink_quiet_intro : ltac2:(tb__ "0|3|
ScScS2cS2cS2cS9R4A1SbSdVA;Vrb;R7R1A4SdVA;Vrb;R7R2A4F_;Fz;SfVA;Vrb;R7R5R4A5SbS2SdVA;Vrb;R8R1A4A1S0S20S32Q8A1M0A1M1R6R2A1R7R2A1M2A3F_;Fz;SbSdVA;Vrb;R9R1A4S2S0G1G2S1cG0A1A3A1F_;Fz;SfVA;Vrb;R9R8R6A5F_;F_;F_;F_;F_;Fm';Fm;Fm0;Fph';Fph;").
Proof.
  intros ph ph' m0 m m' (Q1' & Q2' & Q3' & Q4') HZ (L1 & _) HO HI.
  unfold rlink. rewrite Q1', Q2', Q3', Q4'.
  split; [intros z Hz; rewrite (HO z Hz); apply L1; intros X; exact (Hz (HZ z X))|].
  split; [exact HI|].
  split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
Qed.
End JP.
End CRefillJP.

(* [comment removed for export] *)
Module SpineMallocR1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "app"; "list"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "rw"; "valuation"; "holds"; "ss_facts"; "ss_objs"; "SLit"; "agree_below"; "obj_range"; "ranges_disjoint"; "smatch"; "sprop_below"; "ss_next"; "sstate"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "ag_spacebeg"; "ag_thread"; "aa_cache_inited"; "aa_geom"; "ag_ctx"; "ageom"; "class_state"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1"; "r0_of"; "ghostl"; "NR0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "ulink"; "unwind_objs"; "F_sp_high"; "KcA"; "UStopLeOrPc"; "V_DEPTH"; "chain_pre"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "ustop"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "F_gen"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "F_r0"; "F_r1"; "GR"; "O_pcm"; "O_ri"; "cR0"; "cR0a"; "vAU"; "vMC"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kSpaceSize"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "geom_ok"; "sep_geom3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "FAb"; "JR"; "entryR"; "gh_chx"; "gh_new"; "gh_nf"; "ghosts"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cnt_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1.ZONE"; "armint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ZONE.
Let segs : list Segment := segsA.
Variable W : list ulink.

Definition armint (G : ageom) (lo hi : Z) : Prop := ltac2:(tb__ "0|2|
S1eS1dS23S24S2aVG;A1M0Z120A2Vlo;A2S23Vhi;S24G0Zc60A2A2A2S1eS1dS23S29VG;A1M1Vlo;A2S23Vhi;S24S24G1S62A2Z1000A2A2A2S1dS23S61Vlo;A2S23Vhi;S60A2A2A2A2").

Lemma base_zone : ltac2:(tb__ "0|3|
S2eSdS18S2S5S4cA1S4bA2S5S9A1S1aS1aS68R7A1S69R8A1S15Vsegs;R8R7R6A4S9S38S9R1R7A3S38S9R2S10RaA1A3F_;Fo;S1cS5S2S2SaSaA2SaA2M0A1S25S9G0S34R7A4S25S9G0S34S4S9S1S9S3dS4S9S40VW;A1S3eA3A3S3cA3A4A3SeRbS41A2S26SbSeRcA1S45VW;A1A3S23S33ReA1S24S21Q40M1ScRdPaA2A2S22G1ScRdS44A2A2A2A2S1cS20G1A1M2ScReP97A2S1fG1S2aRfA1A2A3S1cG2ScRfP98A2S1fG1S2dR10A1A2A3S76R11RcRbA3S26S9S9S14S13R12R1A2S0S1aS1aReRdA4A2Lo';ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fobjs;Fw;FS;FrhoE;FG;").
Proof.
  intros G rhoE S w objs lo hi HG0 HS3 Hsm Hsub HSK Hhigh HCH Htop E151 E152 HI.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21 G1 G2 G3 G4 G10 G11.
  pose proof (geom_bands _ HG0) as (_ & TB & CB & _ & TI & CI & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB, CB, TI, CI.
  destruct HS3 as (PS1 & PS2 & _). rewrite kSpaceSize_val in PS1, PS2.
  pose proof (topG_range G) as TG.
  unfold armint, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HI. rewrite kSpaceSize_val in HI.
  destruct objs as [|osw orest]; [cbn [map] in HSK; exfalso; clear -HSK; discriminate HSK|].
  cbn [map] in HSK.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HSK).
  assert (SKrest : map skel orest = map skel ((unwind_objs W ++ A_globals) ++ RT_m1)) by exact (f_equal (@tl _) HSK).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm (Hsub osw (or_introl eq_refl)) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).
  assert (LNK : Forall (fun o => topG G + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG G)); [exact HCH | clear -SW0 SW2 SW3; lia | clear -TG; lia]. }
  constructor.
  - clear -SW0 G14 HI G6 TG. unfold ranges_disjoint. cbn [fst snd]. lia.
  - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (lo, hi)) orest _ SKrest).
    apply Forall_app. split.
    + apply Forall_app. split.
      * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by (clear -B TG; lia). cbn [fst snd]. clear -B G14 HI G6 TG. lia.
      * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia;
          clear -HI G5 G13 TI; lia.
    + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
             O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
      unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval];
        rewrite ?E151, ?E152, ?u64_lit by (first [ clear -G5 G6 TG; lia | clear -G8 G9 TG; lia | lia ]);
        (first [ clear -HI G5 G13 TI; lia | clear -HI G5 G6 TB TI PS1 G13 TG; lia | clear -HI G8 G9 CB CI PS2 G13 G24 TG G5 G6 G19; lia ]).
Qed.
End ZONE.

Definition NR0 : list carve_spec := ltac2:(tb__ "0|b|
S1S2S2S2SaS1aA2M0S1aA2M1S5S2S2S1aS3A2M2SaA2M3A1M4A2M5S0G1G4S0G0S1aS0SaS1aS52Z4M6A4Z8A4S1G3S0G2SaS0S1aS3G6U4A4S5bA4S6G3A1M7A3A4S1G5S0G1G4S0G0S1aS0SaS1aS5fZ0M8A4Z80A4S1G3S0G2SaS0S1aS3G8U8M9A4S11G8A1MaA4S1G3S0G2SaS0S1aS3Z10G9A4S5eA4S1G3S0G2SaS0S1aS3Z18G9A4S5cA4S1G3S0G2SaS0S1aS3Z20G9A4S5aA4S1G3S0G2SaS0S1aS3Z28G9A4GaA4S1G3S0G2SaS0S1aS3Z30G9A4S5dA4S1G3S0G2SaS0S1aS3Z38G9A4GaA4S1G3S0G2SaS0S1aS3Z44U1A4GaA4G7A3A3A3A3A3A3A3A3A4S6G5A1A3A3").
Lemma NR0_objs : ltac2:(tb__ "0|0|
S1cS5S9A1S25S66S9S65S37A4S1S9S56S1S9S57S6S9A1A3A3A3"). Proof. reflexivity. Qed.

Definition ghostl (A : AA) (rb : valuation) : list (positive * word) := ltac2:(tb__ "0|3|
S21Q40M0ScVrb;PcA2A2S1aS73R1A1S1aS75VA;R2A2S2fS29S2cVA;A1A1S1aS1S2S1bS20G0A1M1A2M2S0S1bG1PdcS1fG0S63R3A1A2A4S1G2S0S1bG1PddS1fG0S6fVA;Vrb;A2A2A4S1G2S0S1bG1PdeS1fG0S31R2A1A2A4S1G2S0S1bG1PdfS1fG0S30R2A1A2A4S1G2S0S1bG1Pe0S1fG0S32R2A1A2A4S1G2S0S1bG1Pe1S1fG0S64R1R3A2A2A4S1G2S0S1bG1Pe2S1fG0S6aVA;Vrb;A2A2A4S1G2S0S1bG1Pe3S1fG0S72R3A1A2A4S1G2S0S1bG1Pe4S1fG0S6eVA;Vrb;A2A2A4S1G2S0S1bG1Pe5S1fG0S6dVA;Vrb;A2A2A4S6G2A1A3A3A3A3A3A3A3A3A3A3TSB;Tcs;Tc;Tnv;").
Definition r0_of (A : AA) (rb : valuation) : valuation := ltac2:(tb__ "0|0|
S67Vrb;S36VA;Vrb;A2A2").

Lemma ghostl_ge : ltac2:(tb__ "0|1|
S28SdS1bS20Q40A1M0S38S2S1bG0A2S0S1bG0R2R1A4S36R4R3A2A3S78PdcR3A2F_;Fv;Fj;Frb;FA;").
Proof. intros A rb j v H. unfold ghostl in H. cbn [In] in H. repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H. Qed.
Lemma r0_agree : ltac2:(tb__ "0|0|
S28SdS12PdcR1S35R2R1A2A3Frb;FA;").
Proof. intros A rb. apply agree_below_rho_sets. apply ghostl_ge. Qed.
Lemma r0_ghosts : ltac2:(tb__ "0|0|
S28SdS70R2R1S35R2R1A2A3Frb;FA;").
Proof.
  intros A rb. unfold ghosts, r0_of.
  assert (ND : List.NoDup (map fst (ghostl A rb))).
  { unfold ghostl. cbn [map fst]. repeat (constructor; [cbn [In]; intros H; repeat (destruct H as [H|H]; [discriminate H|]); exact H|]). constructor. }
  repeat split; apply (rw_rho_sets_in rb (ghostl A rb) _ _ ND); unfold ghostl; cbn [In]; tauto.
Qed.

Section ENTRY.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.

Variable E3 : axst.
Hypothesis SK3 : ltac2:(tb__ "0|1|
S1cS5S2S2SaSaA2SaA2M0A1S25S9G0S34S10S27VE3;A1A1A4S25S9G0S34S4S9S4S9S1S9S3dS4S9S40VW;A1S3eA3A3S3cA3S1S9S50S1S9S51S6S9A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S3aSbS4SbS4SbS48VW;Vst;A2S47S46A1A3S4fA3SfS27VE3;A1A1A3").
Hypothesis NX3 : ltac2:(tb__ "0|0|
S1cS7S79S17S27VE3;A1A1PdcA2S8A3").
Hypothesis WR0a : ltac2:(tb__ "0|0|
S1cS7S19S27S59VE3;A1A1A1S8A3").
Hypothesis FB0 : ltac2:(tb__ "0|0|
S1cS7S39SbS16S55A1S4SbSfS27VE3;A1A1S4SbS53S54A3A3A3S8A3").

Lemma refill_entry : ltac2:(tb__ "0|2|
S28S42SdSdS5S20Q40M0A1A1S4eS1cS49Vst;S43A3S1cS5S3fA1VW;S6S3fA1A3F_;S1cS7S2bR7A1S8A3S1cS1aS74R8S21G0ScR6PcA2A2A2Z0A3S3bVsegs;S77VW;Vst;R9R8R7A5VE3;R6R5R4A6S1dS6cRaR7R6S4aS4dR5A1A1M1VW;Vst;R8A7S3bVsegs;S6bRaR9R7R6G1S71A6S58VE3;A1S35RaR7A2R6R5A6A2F_;F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w HW Hini Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. pose proof Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite <- E12 in Hcnt. set (nv := bv_unsigned (rw rhoE 12%positive)) in *.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). cbn. rewrite <- E12. reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p ((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (XF3 p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; tauto)) as F. cbn [holds eval] in F.
    rewrite u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  split.
  { unfold entryR. split; [exact Hag|]. split; [exact HA|]. split; [exact Htp|]. split; [exact HU|]. split; [exact HB|]. split; [lia|]. split; [exact Htop|]. split; [exact Hcnt|].
    exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA))). }
  idtac "entry:1".

  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). pose proof HG as HG0.
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  pose proof (proj1 HI3) as HS3.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.
  pose proof (topG_range (aa_geom A)) as TG.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (T := ag_thread G) in *. set (SB := ag_spacebeg G) in *.
  assert (MT : forall z, T <= z < T + 0x1000 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  assert (MS : forall z, SB <= z < SB + kSpaceSize + 4096 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. fold G SB in P4.
  destruct P4 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  idtac "entry:2".
  set (r0 := r0_of A rhoE).
  pose proof (r0_agree A rhoE) as AG0. pose proof (r0_ghosts A rhoE) as GH0. fold r0 in AG0, GH0.
  assert (Erm0 : rm r0 = rm rhoE) by (unfold r0, r0_of; apply rm_rho_sets).

  assert (Ha : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) E3 r0 tp w).
  { split.
    - eapply smatchA_agree; [|exact HsmA]. eapply agree_below_le; [|exact AG0]. apply Pos.leb_le. exact NX3.
    - unfold JR. split; [|split; [exact GH0|split; [exact HK|split; [|split]]]].
      + destruct AG0 as (Aw & Al & _). split; [exact Aw | exact Al].
      + unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
        repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia].
      + rewrite Erm0. unfold rlink, zoneR, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
        split; [intros; reflexivity|]. split.
        { intros z [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; exfalso; lia. }
        split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
      + intros a _. rewrite Erm0. reflexivity. }
  idtac "entry:3".

  destruct AG0 as (A0w & A0l & A0m).
  assert (R151 : rw r0 151%positive = Z_to_bv 64 T) by (rewrite <- (A0w 151%positive) by (clear; lia); exact E151).
  assert (R152 : rw r0 152%positive = Z_to_bv 64 (ag_ctx G)) by (rewrite <- (A0w 152%positive) by (clear; lia); exact E152).
  assert (R158 : rw r0 158%positive = Z_to_bv 64 c) by (rewrite <- (A0w 158%positive) by (clear; lia); exact E158).
  assert (R10 : rw r0 10%positive = rw rhoE 10%positive) by (rewrite <- (A0w 10%positive) by (clear; lia); reflexivity).
  assert (R15 : rw r0 V_DEPTH = rw rhoE V_DEPTH) by (rewrite <- (A0w V_DEPTH) by (unfold V_DEPTH; clear; lia); reflexivity).
  destruct GH0 as (Q220 & Q221 & Q222 & Q223 & Q224 & Q225 & Q226 & Q227 & Q228 & Q229).
  unfold gh_nf, FAb, cst_of in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold nv in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227. fold c in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold cs in Q221, Q222, Q223, Q224. fold G in Q225, Q226. fold SB in Q225, Q226.
  assert (EB : bv_unsigned (eval r0 pc_base) = T + 208 + 80 * c).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite R151, R158. rewrite add_val, add_val, mul_val, !u64_lit by (clear -C1 G5 G6 TG; lia).
    rewrite (Z.mod_small (c * 80)) by (clear -C1; lia). rewrite (Z.mod_small (T + 208)) by (clear -G5 G6 TG; lia). rewrite Z.mod_small by (clear -C1 G5 G6 TG; lia). clear; lia. }
  pose proof kSpaceSize_val as KSV.
  assert (RIr : SB + kSpaceSize <= region_info SB c /\ region_info SB c + 128 <= SB + kSpaceSize + 4096).
  { unfold region_info, kRegionInfoStride. clear -C1. lia. }
  assert (ERI : bv_unsigned (eval r0 vRI) = region_info SB c).
  { unfold vRI. cbn [eval]. rewrite Q225. apply u64_lit. rewrite kSpaceSize_val in *. clear -RIr G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }
  pose proof (proj1 Ha) as HsmA0. pose proof (proj1 HsmA0) as Hsm0. unfold virt in Hsm0. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm0.
  pose proof (smatch_facts_hold _ _ _ _ Hsm0) as HFa0.
  assert (HFX0 : forall p, In p ((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_gen) -> holds r0 p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa0 p (XF3 p Hp)). }

  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact SK3)) as (ob & ox & EO & SKb & SKx).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNc : obj_range r0 oc = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { rewrite (obj_range_skel r0 oc O_pcc0 SKc). unfold O_pcc0. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r0 os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r0 os O_st SKs). unfold O_st, vT. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite R151, u64_lit by (clear -G5 G6 TG; lia). reflexivity. }
  assert (BZ : forall lo hi, armint G lo hi -> Forall (fun o' => ranges_disjoint (obj_range r0 o') (lo, hi)) ob).
  { intros lo hi HI. apply (base_zone W G r0 (ax_S E3) _ ob lo hi HG0 HS3 Hsm0); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | | exact R151 | exact R152 | exact HI].
    - apply HFX0. apply in_or_app; left. apply in_or_app; right. cbn; tauto.
    - apply Forall_forall. intros p Hp. apply HFX0. apply in_or_app; left. apply in_or_app; left.
      destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp.
    - rewrite R10, R15. exact Htop. }
  idtac "entry:4".

  assert (PRT : forall z, T <= z < T + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G5 G6 TG; lia).
    eapply wok_rd_off_image2; [| |exact Hb]; [clear -Hz G5 G6 TG; lia | clear -Hz TI; lia]. }
  assert (PRS : forall z, SB <= z < SB + kSpaceSize + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite kSpaceSize_val in Hz. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    eapply wok_rd_off_image; [|exact Hb]. clear -Hz G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }

  assert (CVT : forall a k v (e : sv), T <= a -> a + Z.of_nat k <= T + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MT in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G5 G6 TG; lia). rewrite Erm0, Ee. exact Hc. }
  assert (CVS : forall a k v (e : sv), SB <= a -> a + Z.of_nat k <= SB + kSpaceSize + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MS in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite kSpaceSize_val in Ha2.
    rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G13 G14 TG; unfold HIGH_SHADOW_END in *; lia). rewrite Erm0, Ee. exact Hc. }
  idtac "entry:5".
  assert (Hb : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) (cR0a E3) r0 tp w).
  { apply (SPA_carve_list segs _ r0 E3 tp w NR0 GR Ha WR0a).
    - apply Pos.leb_le in NX3. clear -NX3. unfold GR. lia.
    - unfold NR0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + rewrite EB. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 G5 TG; lia|]. split; [clear -C1 G5 G6 TG; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRT; [clear -Hoff C1; lia|]. destruct (PE (T + 208 + 80 * c + off) ltac:(unfold T, G, c; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MT by (clear -Hoff C1; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        apply Forall_cons; [|apply Forall_nil]. intros j Hj.
        exact (CVT (T + 208 + 80 * c + 4) 4%nat (max_count c) vMC ltac:(clear -C1; lia) ltac:(clear -C1; lia) Q220 D2 j Hj).
      + rewrite ERI. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
        split; [clear -RIr G13; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [clear -RIr G13 G14 TG; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRS; [clear -Hoff RIr KSV; lia|]. destruct (PRI (region_info SB c + off) ltac:(unfold kRegionInfoStride; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MS by (clear -Hoff RIr KSV; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted in *.
        repeat apply Forall_cons; try apply Forall_nil; intros j Hj.
        * exact (CVS (region_info SB c + 0) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R1 j Hj).
        * exact (CVS (region_info SB c + 16) 8%nat _ vNF ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q221 R2 j Hj).
        * exact (CVS (region_info SB c + 24) 8%nat _ vMFA ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q222 R3 j Hj).
        * exact (CVS (region_info SB c + 32) 8%nat _ vAU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q223 R4 j Hj).
        * exact (CVS (region_info SB c + 40) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R5 j Hj).
        * exact (CVS (region_info SB c + 48) 8%nat _ vMU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q224 R6 j Hj).
        * exact (CVS (region_info SB c + 56) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R7 j Hj).
        * exact (CVS (region_info SB c + 68) 1%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R8 j Hj).
    - idtac "entry:6". cbn [map carve_obj NR0].
      assert (RNm : obj_range r0 (carved pc_base 4 8 [(4, 4%nat, vMC)]) = (T + 208 + 80 * c + 4, T + 208 + 80 * c + 8)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite EB. reflexivity. }
      assert (RNr : obj_range r0 (carved vRI 0 128 [(0, 8%nat, SLit 0); (16, 8%nat, vNF); (24, 8%nat, vMFA); (32, 8%nat, vAU); (40, 8%nat, SLit 0); (48, 8%nat, vMU); (56, 8%nat, SLit 0); (68, 1%nat, SLit 0)])
                    = (region_info SB c + 0, region_info SB c + 128)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite ERI. reflexivity. }
      destruct HS3 as (PS1 & _). fold T SB in PS1.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite EO; apply Forall_app; split.
      + rewrite RNm. apply BZ. left. fold T. clear -C1. lia.
      + rewrite RNm. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1; lia.
      + rewrite RNr. apply BZ. right; left. fold SB. clear -RIr KSV. lia.
      + rewrite RNr. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1 RIr KSV PS1; lia.
    - cbn [map carve_obj NR0 pairwise_disjoint]. split; [|split; [constructor | exact I]].
      apply Forall_cons; [|apply Forall_nil]. unfold carved. rewrite !obj_range_mk by (clear; lia). rewrite EB, ERI.
      destruct HS3 as (PS1 & _). fold T SB in PS1. unfold ranges_disjoint; cbn [fst snd]. clear -C1 RIr KSV PS1. lia. }
  idtac "entry:7".

  unfold cR0. apply (SPA_refacts segs _ r0 (cR0a E3) _ tp w Hb FB0).
  intros HF0. apply Forall_app. split; [exact HF0|].
  assert (E155 : rw r0 155%positive = Z_to_bv 64 SB) by (rewrite <- (A0w 155%positive) by (clear; lia); rewrite <- (Hagw 155%positive) by (unfold GW; clear; lia); reflexivity).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0.
  assert (DSB : exists q, SB = q * 2 ^ 16) by (apply Z.mod_divide in G12; [destruct G12 as [q Hq]; exists q; exact Hq | clear; lia]).
  destruct DSB as [q Hq].
  unfold F_r0, F_r1, vMC, vK, vNF, vAU, vMU. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval].
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -K1 K2. lia.
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -C4. lia.
  - split; [clear; lia|]. rewrite Q225, u64_lit by (clear -RIr KSV G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    unfold region_info, kRegionInfoStride. rewrite KSV, Hq. replace (q * 2 ^ 16 + 2 ^ 37 + c * 128) with ((q * 512 + 2 ^ 30 + c) * 2 ^ 7) by (clear; lia). apply Z_mod_mult.
  - split; [clear; lia|]. rewrite Q226.
    unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize.
    rewrite u64_lit by (clear -C1 G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia).
    rewrite Hq. replace (q * 2 ^ 16 + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) with ((q * 16 + c * 2 ^ 20 + (2 ^ 20 - 2 ^ 17)) * 2 ^ 12) by (clear; lia). apply Z_mod_mult.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q221, !u64_lit by (clear -N6 NF0; lia). clear -N6. lia.
  - rewrite Q223, Q224, !u64_lit by (clear -N2 N3; lia). clear -N2. lia.
  - split; [clear; lia|]. rewrite Q224, u64_lit by (clear -N2 N3; lia). exact N1.
  - split; [clear; lia|]. rewrite E155, u64_lit by (clear -G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia). exact G12.
Qed.
End ENTRY.
End SpineMallocR1.

(* [comment removed for export] *)
Module SegQ3D_skel.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "iff"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "list"; "app"; "true"; "nil"; "pair"; "prod"; "length"; "nat"; "S"; "false"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "qb_items"; "qb_addr"; "aa_geom"; "mkQB"; "qb_size"; "ag_spacebeg"; "ageom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "valuation"; "SLit"; "rw"; "SVar"; "ss_objs"; "ss_facts"; "rm"; "swf"; "sprop_below"; "ss_next"; "eval"; "SPUle"; "SAlu"; "SPAlign"; "holds"; "obj_range"; "ranges_disjoint"; "DUnknown"; "cell"; "mkObj"; "SPBranch"; "SPNot"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_base"; "ax_setS"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "pow"; "mul"; "sub"; "modulo"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "O_sb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "HVX"; "with_obj"; "benv"; "fixed_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "vXF"; "vXK"; "vXL"; "vXS"; "O_mtx00"; "STK"; "SWD"; "cb_cells"; "ZQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "dropl"; "addo"; "HVB"; "DH0a"; "DIc0"; "O_b24"; "addf"; "HVI"; "HVS"; "DBI0"; "MDH"; "FI1"; "FIc"; "DBI1"; "DBT1"; "DH0b"; "DHnb"; "DIc1"; "DTc1"; "MDBI"; "MDBT"; "MDIc"; "MDTc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "bview"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRD"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "DBx"; "DHn"; "DTc"; "DH"; "vBN"; "vS7"; "DIc"; "DI"; "DTs"; "vBS"; "DH0"; "vB"; "O_b"; "O_it"; "F_czB"; "F_nzB"; "s9'"; "vBC"; "vS9"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states"; "O_itg"; "F_b"; "F_b24"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "O_gmax"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "entsM"; "@Stdlib.Lists.List"; "forallb"; "In"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_END"; "kQuarantineBatchCount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "notin_vars"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event";
"@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "BC_NE"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep"; "last_addr"; "hd_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma OBD_fixed : ltac2:(tb__ "0|2|
S13S22S7S34A1M0G0S91R4R3A2S8eS20S30R4A1S90S97A1A3S8eS1fS51R5S1eS19R6A1A1A2S8S1fS8S1fS57R4S35S25PaA1S23Na8A1S23Z0A1R3S33A5A2S5S1fS56S5S1fS96SaS1fA1M1A3A3A3S8S1fS8fS5S1fS4dG1A3A3A3A3F_;F_;Fswc;Fcb;Frho;FA;").
Proof.
  intros A rho cb swc HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  destruct (stk_ranges rho _ _ cb swc eq_refl eq_refl ltac:(lia) HD) as (R1 & R2 & R3 & R4).
  unfold STK. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; unfold fixed_ok.
  - right. rewrite R1. cbn [fst]. lia.
  - right. rewrite R2. cbn [fst]. lia.
  - right. rewrite R3. cbn [fst]. lia.
  - right. rewrite R4. cbn [fst]. lia.
  - left. unfold O_mtx00, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold QG. lia.
  - left. unfold O_gmax, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold QG. lia.
  - left. unfold O_got. rewrite obj_range_mk by (unfold GOT_LO, GOT_HI; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold GOT_HI. lia.
  - left. unfold O_rtc. rewrite obj_range_mk by (unfold RTC_LO, RTC_HI; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold RTC_HI. lia.
  - left. unfold O_sb, carved. rewrite obj_range_mk by lia. cbn [snd eval]. rewrite u64_lit by lia. lia.
Qed.

Definition O_b24 (vb vn vs vc : positive) : sobj := ltac2:(tb__ "0|4|
SafS25Vvb;A1Z0M0Z18S5ScScS39SeA2M1S21A2M2SbG1S21SbS39SeG0U8M3A4S25Vvn;A1A4S5G2SbG1S21SbS39SeZ8G3A4S25Vvs;A1A4S5G2SbG1S21SbS39SeZ10G3A4S25Vvc;A1A4SaG2A1A3A3A3A4").
Lemma carve_b24 : ltac2:(tb__ "0|6|
S41S3bS22S7S4aQ40M0A1M1A1S5bS38S38S38S38S39S39S39S39S40S3fRdRcRbRaR9A6S0S7ScS21S21A2M2A1S3eRdA1SaG2A1A3S0S6S29S4fS3aReA1S61RaR9R8R7A4A2A1S9A3S0G1S24ReRbA2S4bG0R7A2M3A3S0G1S24RfRbA2G3A3S0G1S24R10RbA2G3A3S0G1S24R11RbA2G3A3S43Z646000RbA2S43S42RcZ18M4A2S46Z2Z3eA2A2S75S74S3fS28R14A1A2S76RdU8M5RcA3A2S75S74S3fS28R15A1A2S76S42ReZ8A2G5RcA3A2S75S74S3fS28R16A1A2S76S42RfZ10A2G5RcA3A2S8eS1fS1fS32S31R18R1A2SbS39S39R11S42R11G4A2A4A2Lo';S26S3aR18A1A1A3S40S3fR1aS3dR19S4fS3aR19A1S61R15R14R13R12A4A2A2R18R17R16A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fcnt;Fsz;Fnxt;Fa;Fvc;Fvs;Fvn;Fvb;Fw;Ftp;Frho;FS;FJ;").
Proof.
  intros J S rho tp w vb vn vs vc a nxt sz cnt H HX Hswf Eb En Es Ec Ha1 Ha2 Cn Cs Cc HD.
  pose proof (SPA_carve_list segsA J rho S tp w [(SVar vb, 0, 24, [(0, 8%nat, SVar vn); (8, 8%nat, SVar vs); (16, 8%nat, SVar vc)])] (ss_next (ax_S S)) H) as X.
  cbn zeta in X. cbn [map carve_obj] in X. apply X; clear X.
  - exact Hswf.
  - apply Pos.le_refl.
  - apply Forall_cons; [|apply Forall_nil]. cbn [eval]. rewrite Eb, u64_lit by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    split; [|split].
    + intros off Hoff. destruct (Z_lt_dec off 8); [|destruct (Z_lt_dec off 16)].
      * eapply (cell_wok_rd _ _ _ _ _ Cn); cbn [Z.of_nat]; lia.
      * eapply (cell_wok_rd _ _ _ _ _ Cs); cbn [Z.of_nat]; lia.
      * eapply (cell_wok_rd _ _ _ _ _ Cc); cbn [Z.of_nat]; lia.
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      * eapply (civ_cell rho (rm rho) a 0); [rewrite Z.add_0_r; exact Cn | cbn [eval]; exact En | lia | lia].
      * eapply (civ_cell rho (rm rho) a 8); [exact Cs | cbn [eval]; exact Es | lia | lia].
      * eapply (civ_cell rho (rm rho) a 16); [exact Cc | cbn [eval]; exact Ec | lia | lia].
    + intros rr y j Hin. rewrite HX in Hin. destruct Hin.
  - apply Forall_cons; [|apply Forall_nil]. unfold O_b24, carved in *.
    assert (ER : forall cs, obj_range rho (mkObj (SVar vb) (SLit 0) (SLit 24) cs DUnknown) = (a, a + 24)).
    { intros cs. rewrite obj_range_mk by lia. cbn [eval]. rewrite Eb, u64_lit by lia. f_equal; lia. }
    rewrite ER. exact HD.
  - cbn [pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Lemma carve_slot : ltac2:(tb__ "0|5|
S41S3bS22S7S4aQ40M0A1M1A1S5bS21S39S39S40S3fR8R7R6R5R4A6S0S7ScS21S21A2M2A1S3eR8A1SaG2A1A3S0S6S29S4fS3aR9A1S93R5A1A2A1S9A3S0G1S2cR9R6A2S4bG0R5A2M3A3S0G1S24RaPc6A2G3A3S43S42Z646000Z80M4A2R7A2S43R8S46Z2Z3eA2A2S75S74S3fS28RdA1A2S76S48R9G4A2U8R8A3A2S8eS1fS1fS32S31RfR1A2SbS39S39S48RbG4A2S48RbZ78A2A4A2Lo';S26S3aRfA1A1A3S40S3fR11S3dR10S4fS3aR10A1S93RcA1A2A2RfReRdA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fm;FB;Fe;Fw;Ftp;Frho;FS;FJ;").
Proof.
  intros J S rho tp w e B m H HX Hswf Ee Em HB1 HB2 Cm HD.
  pose proof (SPA_carve_list segsA J rho S tp w [(e, -128, -120, [(-128, 8%nat, SVar 198)])] (ss_next (ax_S S)) H) as X.
  cbn zeta in X. cbn [map carve_obj] in X. apply X; clear X.
  - exact Hswf.
  - apply Pos.le_refl.
  - apply Forall_cons; [|apply Forall_nil]. rewrite Ee, u64_lit by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    split; [|split].
    + intros off Hoff. replace (B + off) with (B - 128 + (off + 128)) by lia. eapply (cell_wok_rd _ _ _ _ _ Cm); cbn [Z.of_nat]; lia.
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      eapply (civ_cell rho (rm rho) B (-128)); [replace (B + -128) with (B - 128) by lia; exact Cm | cbn [eval]; exact Em | lia | lia].
    + intros rr y j Hin. rewrite HX in Hin. destruct Hin.
  - apply Forall_cons; [|apply Forall_nil]. unfold O_itg, carved in *.
    assert (ER : forall cs, obj_range rho (mkObj e (SLit (-128)) (SLit (-120)) cs DUnknown) = (B - 128, B - 120)).
    { intros cs. rewrite obj_range_mk by lia. rewrite Ee, u64_lit by lia. f_equal; lia. }
    rewrite ER. exact HD.
  - cbn [pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Lemma carve_sb : ltac2:(tb__ "0|3|
S41S3bS22S7S4aQ40M0A1M1A1S5bS1dS40S3fR6R5R4R3R2A6S0S7ScS21S21A2M2A1S3eR6A1SaG2A1A3S0S6S29S4fS3aR7A1S4dA2A1S9A3S78S74S3fS28R7A1A2R4A2S0G1S24R8P9bA2S4bG0S1cR5A1A2A3S8eS1fS1fS32S31RaR1A2SbS39S39Zeddb8Zeddc0A4A2Lo';S26S3aRaA1A1A3S40S3fRcS3dRbS4fS3aRbA1S4dA2A2RaR9R8A6F_;F_;F_;F_;F_;F_;FG;Fw;Ftp;Frho;FS;FJ;").
Proof.
  intros J S rho tp w G H HX Hswf HRTC E155 HD.
  pose proof (SPA_carve_list segsA J rho S tp w [(SLit 0, 0xeddb8, 0xeddc0, [(0xeddb8, 8%nat, vSB)])] (ss_next (ax_S S)) H) as X.
  cbn zeta in X. cbn [map carve_obj] in X. apply X; clear X.
  - exact Hswf.
  - apply Pos.le_refl.
  - apply Forall_cons; [|apply Forall_nil]. cbn [eval]. rewrite u64_lit by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    split; [|split].
    + intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia].
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      assert (HSB : cell_ok (view segsA (rm rho)) (mkACell 0xeddb8 8 (ag_spacebeg G))) by (unfold rtc_inv, rtc_cells in HRTC; exact (cells_ok_nth _ _ 3 _ HRTC eq_refl)).
      eapply (civ_cell rho (rm rho) 0 0xeddb8); [exact HSB | unfold vSB; cbn [eval]; exact E155 | lia | lia].
    + intros rr y j Hin. rewrite HX in Hin. destruct Hin.
  - apply Forall_cons; [|apply Forall_nil]. unfold O_sb, carved in *.
    assert (ER : forall cs, obj_range rho (mkObj (SLit 0) (SLit 0xeddb8) (SLit 0xeddc0) cs DUnknown) = (0xeddb8, 0xeddc0)).
    { intros cs. rewrite obj_range_mk by lia. cbn [eval]. rewrite u64_lit by lia. reflexivity. }
    rewrite ER. exact HD.
  - cbn [pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Definition dropl (X : axst) : axst := ltac2:(tb__ "0|1|
S3dVX;SadS3aVX;A1M0S9bS1fS26G0A1A2A2A2").
Definition addo (X : axst) (o : sobj) : axst := ltac2:(tb__ "0|0|
S3dVX;S4fS3aVX;A1Vo;A2A2").
Definition addf (X : axst) (F : list sprop) : axst := ltac2:(tb__ "0|0|
SaeVX;S8S20S27S3aVX;A1A1VF;A3A2").

Definition DH0a : axst := addo DH0 O_sb.
Definition DH0b : axst := ltac2:(tb__ "0|0|
S62S5dS5fS61Pb9Pa0Pa1Pa2A4A2S94A2").
Definition DHnb : axst := ltac2:(tb__ "0|0|
S62S5dS7cS61Pb9Pa0Pa1Pa2A4A2S94A2").
Definition MDH : vmap := ltac2:(tb__ "0|0|
SaaS5S38Pa0S5S38Pa1S5S38Pa2S5S38Pb8S5S38Pb9S5S38PbaS5S38PbbS5S38Pd0SaS38A1A3A3A3A3A3A3A3A3A1").
Lemma DH0b_ent : ltac2:(tb__ "0|0|
S0S6S98S6bS7eS66A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DHnb_ent : ltac2:(tb__ "0|0|
S0S6S98S6cS7eS66A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DH0_vars : ltac2:(tb__ "0|1|
S1S0S6S9cSa0S5S38Pa0S5S38Pa1S5S38Pa2SaS38A1A3A3A3A1M0S3aS5fA1A2S9A3S0S6S9dG0S3cS5fA1A2S9A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma DHn_vars : ltac2:(tb__ "0|1|
S1S0S6S9cSa0S5S38Pa0S5S38Pa1S5S38Pa2SaS38A1A3A3A3A1M0S3aS7cA1A2S9A3S0S6S9dG0S3cS7cA1A2S9A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma DH_swfs : ltac2:(tb__ "0|1|
S1S0S6S29S4fS3aS85A1S4dA2A1S9A3S1S0S6S29S4fS3aS5fA1S61Pb9Pa0Pa1Pa2A4M0A2A1S9A3S0S6S29S4fS3aS7cA1G0A2A1S9A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma DH_below : ltac2:(tb__ "0|1|
S1S0S6S99S20S2aS2bS3aS5fA1A1A1S8S20S27S3aS5dS5fS61Pb9Pa0Pa1Pa2A4M0A2A1A1S94A3A3S9A3S0S6S99S20S2aS2bS3aS7cA1A1A1S8S20S27S3aS5dS7cG0A2A1A1S94A3A3S9A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition FI1 : list sprop := ltac2:(tb__ "0|1|
S5S20S2dS23S42S9eZ98M0A2A1S4cS52S23G0A1A2A2S5S20S2fPb9Z4A2SaS20A1A3A3").
Definition DBI0 (nz : bool) : axst := dropl (DBx nz false).
Definition DBI1 (nz : bool) : axst := ltac2:(tb__ "0|0|
S62S5dS65Vnz;A1S93S4cS52S23Z98A1A2A1A2S67A2").
Definition MDBI (nz : bool) : vmap := ltac2:(tb__ "0|3|
S5ScS38S21A2M0SbS38S21Pa2M1S25G1A1A4S5G0SbS38S21Pa3S4cS52S23Z98A1A2A4S5G0SbS38S21Pa4S23Z10A1A4S5G0SbS38S21Pa5S25Pc6A1A4S5G0SbS38S21Pa6S52A4S5G0SbS38S21Pb8S4cS53S23N1A1A2A4S5G0SbS38S21Pb9S7fA4S5G0SbS38S21PbaS6S21Lnz;Vnz;S54S23Z0A1X6x2A4S5G0SbS38S21PbbS2eSa5S55S84A3A4S5G0SbS38S21Pd0M2S25G2A1A4SaG0A1A3A3A3A3A3A3A3A3A3A3").
Lemma DBI1_ent : ltac2:(tb__ "0|0|
S6S0S6S98S69R1A1S82S6fR1A1A3S9A3Fnz;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DBx_objs : ltac2:(tb__ "0|1|
S6S6S0S7S1fA1S26S3aS7bR2R1A2M0A1A1S8S1fS26S3aS5cG0A1A1A1S5S1fS87S7fA1SaS1fA1A3A3A3Fcz;Fnz;"). Proof. intros [|] [|]; reflexivity. Qed.
Lemma DBI0_vars : ltac2:(tb__ "0|2|
S6S1S0S6S9cSa0S5S38Pc6SaS38A1A3A1M0S3aS65R1A1M1A1A2S9A3S0S6S9dG0S3cG1A1A2S9A3A2Fnz;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma DBI_swf : ltac2:(tb__ "0|0|
S6S0S6S29S4fS3aS65R1A1A1S93S4cS52S23Z98A1A2A1A2A1S9A3Fnz;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DBI_below : ltac2:(tb__ "0|1|
S6S0S6S99S20S2aS2bS3aS65R1A1M0A1A1A1S8S20S27S3aS5dG0S93S4cS52S23Z98A1A2A1A2A1A1S67A3A3S9A3Fnz;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition DBT1 (nz : bool) : axst := ltac2:(tb__ "0|0|
S62S5cS7bVnz;S9A2A1S95S52A1A2").
Definition MDBT (nz : bool) : vmap := ltac2:(tb__ "0|2|
S5ScS38S21A2M0SbS38S21Pa6S52A4S5G0SbS38S21Pb8S4cS53S23N1A1A2A4S5G0SbS38S21Pb9S7fA4S5G0SbS38S21PbaS6S21Lnz;Vnz;S54S23Z0A1X6x2A4S5G0SbS38S21PbbS2eSa5S55S84A3A4S5G0SbS38S21Pd0M1S25G1A1A4SaG0A1A3A3A3A3A3A3").
Lemma DBT1_ent : ltac2:(tb__ "0|0|
S6S0S6S98S6aR1A1S83S70R1A1A3S9A3Fnz;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DBT_below : ltac2:(tb__ "0|1|
S6S0S6S99S20S2aS2bS3aS5cS7bR1S9A2A1A1M0A1A1S8S20S27G0A1S95S52A1A3A3S9A3Fnz;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition FIc : list sprop := ltac2:(tb__ "0|0|
S5S20S2dS23S42S9eZ98A2A1S4cS80S23Z8A1A2A2SaS20A1A3").
Definition DIc0 : axst := dropl DIc.
Definition DIc1 : axst := ltac2:(tb__ "0|0|
S62S5dS60S93S4cS80S23Z8A1A2A1A2S68A2").
Definition MDIc : vmap := ltac2:(tb__ "0|8|
S5ScS38S21A2M0SbS38S21Pa2M1S25G1A1A4S5G0SbS38S21Pa3S4cS80S23Z8A1A2A4S5G0SbS38S21Pa4S4cS8dS23Z1A1A2A4S5G0SbS38S21Pa5S25Pc6A1A4S5G0SbS38S21Pa6M2S25G2A1A4S5G0SbS38S21Pb8M3S25G3A1A4S5G0SbS38S21Pb9M4S25G4A1A4S5G0SbS38S21PbaM5S25G5A1A4S5G0SbS38S21PbbM6S25G6A1A4S5G0SbS38S21Pd0M7S25G7A1A4SaG0A1A3A3A3A3A3A3A3A3A3A3").
Lemma DIc1_ent : ltac2:(tb__ "0|0|
S0S6S98S6dS82S71A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DIc_objs : ltac2:(tb__ "0|2|
S1S0S7S1fA1M0S26S3aS81A1A1S8S1fS26S3aS60A1A1S5S1fS88SaS1fA1A3M1A3A3S0G0S26S3aS7dA1A1S8S1fS26S3aS5cS7dA1A1A1G1A3A3A2"). Proof. split; reflexivity. Qed.
Lemma DIc0_vars : ltac2:(tb__ "0|1|
S1S0S6S9cSa0S5S38Pc6SaS38A1A3A1M0S3aS60A1A2S9A3S0S6S9dG0S3cS60A1A2S9A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma DIc_swf : ltac2:(tb__ "0|0|
S0S6S29S4fS3aS60A1S93S4cS80S23Z8A1A2A1A2A1S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DIc_below : ltac2:(tb__ "0|0|
S0S6S99S20S2aS2bS3aS60A1A1A1S8S20S27S3aS5dS60S93S4cS80S23Z8A1A2A1A2A1A1S68A3A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition DTc1 : axst := ltac2:(tb__ "0|0|
S62S5cS7dA1S95S86A1A2").
Definition MDTc : vmap := ltac2:(tb__ "0|0|
SaaS5S38Pa6S5S38Pb8S5S38Pb9S5S38PbaS5S38PbbS5S38Pd0SaS38A1A3A3A3A3A3A3A1").
Lemma DTc1_ent : ltac2:(tb__ "0|0|
S0S6S98S6eS83S72A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DTc_below : ltac2:(tb__ "0|1|
S0S6S99S20S2aS2bS3aS5cS7dA1A1M0A1A1S8S20S27G0A1S95S86A1A3A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition HVB (rho : valuation) (b : qbatch) (tmp' : list qbatch) : Prop := ltac2:(tb__ "0|2|
S1S0S4aQ40M0A1M1S24Vrho;Pa0A2S4bG0SacVtmp';A1A2A3S1S0G1S24Vrho;Pa1A2S4bG0S1bVb;A1A2A3S0G1S24Vrho;Pa2A2S4bG0S44SdScS39S39A2S17Vb;A1A2A1A2A3A2A2").

Definition HVI (rho : valuation) (a n0 : Z) (nd : nat) (it : Z * Z) : Prop := ltac2:(tb__ "0|4|
S1S0S4aQ40M0A1M1S24Vrho;Pa2A2S4bG0Vn0;A2A3S1S0G1S24Vrho;Pa3A2S4bG0S42S42Va;Z98A2S47Z8S44Vnd;A1M2A2A2A2A3S1S0G1S24Vrho;Pa4A2S4bG0S42Z10M3G2A2A2A3S1S0G1S24Vrho;Pa5A2S4bG0S48S11S39S39Vit;A3G3A2A2A3S0G1S24Vrho;Pa6A2S4bG0Va;A2A3A2A2A2A2").

Definition HVS (rho : valuation) (a : Z) (nd : nat) (it : Z * Z) : Prop := ltac2:(tb__ "0|0|
S75S74S3fS28Vrho;A1A2S76S42S42Va;Z18A2S47Z8S44Vnd;A1A2A2U8S48S11S39S39Vit;A3Z10A2A3A2").

Lemma OBD_clear_sb : ltac2:(tb__ "0|2|
S13S22S7S34A1M0G0S91R4R3A2S8eS20S30R4A1S90S97A1A3S8eS1fS1fS32S31R6R1A2SbS39S39Zeddb8Zeddc0A4A2Lo';S8S1fS8S1fS57R4S35S25PaA1S23Na8A1S23Z0A1R3S33A5A2S5S1fS56S5S1fS96SaS1fA1M1A3A3A3S8S1fS8fG1A3A3A3F_;F_;Fswc;Fcb;Frho;FA;").
Proof.
  intros A rho cb swc HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  destruct (stk_ranges rho _ _ cb swc eq_refl eq_refl ltac:(lia) HD) as (R1 & R2 & R3 & R4).
  unfold STK. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint.
  - rewrite R1. cbn [fst snd]. lia.
  - rewrite R2. cbn [fst snd]. lia.
  - rewrite R3. cbn [fst snd]. lia.
  - rewrite R4. cbn [fst snd]. lia.
  - unfold O_mtx00, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold QG. lia.
  - unfold O_gmax, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold QG. lia.
  - unfold O_got. rewrite obj_range_mk by (unfold GOT_LO, GOT_HI; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold GOT_LO, GOT_HI. lia.
  - unfold O_rtc. rewrite obj_range_mk by (unfold RTC_LO, RTC_HI; lia). cbn [fst snd eval]. rewrite u64_lit by lia. unfold RTC_LO, RTC_HI. lia.
Qed.
Lemma DH0_objs : ltac2:(tb__ "0|1|
S0S7S1fA1S26S3aS85A1A1S8S1fS8S1fS57S59S58S53S52S54S55A4A2S5S1fS56S5S1fS96SaS1fA1M0A3A3A3S8S1fS8fG0A3A3A3"). Proof. reflexivity. Qed.
Lemma DH0a_objs : ltac2:(tb__ "0|1|
S0S7S1fA1S26S3aS5fA1A1S8S1fS8S1fS57S59S58S53S52S54S55A4A2S5S1fS56S5S1fS96SaS1fA1M0A3A3A3S8S1fS8fS5S1fS4dG0A3A3A3A3"). Proof. reflexivity. Qed.
Lemma DHn_objs : ltac2:(tb__ "0|1|
S0S7S1fA1S26S3aS7cA1A1S8S1fS8S1fS57S59S58S53S52S54S55A4A2S5S1fS56S5S1fS96SaS1fA1M0A3A3A3S8S1fS8fS5S1fS4dG0A3A3A3A3"). Proof. reflexivity. Qed.
Lemma D_pre_facts : ltac2:(tb__ "0|2|
S3bS7S20A1M0S0G0S27S3aR2A1A1S8S20S90S97A1M1R1A3A3S22S8eS20S30R1A1S27S3aR4A1A1A3S8eS20S30R2A1G1A3F_;Fr;F_;FF;FS;").
Proof. intros S F E r H. rewrite E in H. apply Forall_app in H as [H _]. exact H. Qed.

Section DSkel.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Lemma dh_core : ltac2:(tb__ "0|a|
S3bS7S20A1M0S13S12S7S12A1M1G1S22S7S4aQ40A1A1S5bS0S6S9cSa0S5S38Pa0M2S5S38Pa1M3S5S38Pa2M4SaS38A1A3A3A3A1M5S3aR9A1A2S9A3S0S6S9dG5S3cRaA1A2S9A3S0S7ScS21S21A2M6A1S3eRbA1SaG6A1A3S0S6S29S4fS3aRcA1S61Pb9G2G3G4A4M7A2A1S9A3S0S6S99S20S2aS2bS3aRdA1A1A1S8S20S27S3aS5dRdG7A2A1A1S94A3A3S9A3S0S6S98S62S5dReG7A2S94A2S7eS66A3S9A3S0S7S1fA1S26S3aRfA1A1S8S1fS8S1fS57S59S58S53S52S54S55A4A2S5S1fS56S5S1fS96SaS1fA1M8A3A3A3S8S1fS8fS5S1fS4dG8A3A3A3A3S0G0S27S3aR10A1A1S8S20S90S97A1RfA3A3S0G1S16RfA1SaS12A1A3S0S6S14R10A1S9A3S0G1S15R11A1S8S12S5S12R10RfA3ReA3A3S40S3fS79VK;VA0;Vrho0;R12S5S12R11R10A3RfA6R14ReRdRcA6S4eRfS5S12R12R11A3A2S2S22S22S1S40S3fS79VK;VA0;Vrho0;R15S5S12R14R13A3M9R12A6S7eR1R10RfA6S1S4eR1G9A2S5eR1R14R13A3A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fb;FA;FF0;FS0;").
Proof.
  intros S0 F0 A b tmp' rest rho tp w HV1 HV2 HX Hswf HBEL HENT HOBJ HFACT HTH HCI HGL H (E184 & E185 & E186 & E187 & E208).
  rewrite hd_addr_cons in E185.
  destruct w as [tr [ms md]]. destruct (proj2 H) as (HK & (HBM & HLT & HLR & HTHD & HGH) & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HBM, HLT, HLR, HTHD, HGH, HFRM.
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  assert (INB : In b (aa_q_global A)) by (rewrite HGL; left; reflexivity).
  destruct (batch_addr_facts A HTH rho b BE INB) as (BA1 & BA2 & BA3 & BA4 & BA5).
  pose proof (Forall_inv HBM) as (CSZ & CCNT & _). cbn [app] in HBM.
  assert (CNX : cell_ok (view segsA (rm rho)) (mkACell (qb_addr b) 8 (hd_addr tmp'))) by (cbn [qlinks] in HLT; destruct HLT as [X _]; destruct tmp'; exact X).
  set (rho1 := rho_sets rho [(160%positive, Z_to_bv 64 (hd_addr tmp')); (161%positive, Z_to_bv 64 (qb_size b)); (162%positive, Z_to_bv 64 (Z.of_nat (length (qb_items b))))]).
  pose proof (JRD_stable K HL A0 rho0 A (b :: tmp') rest) as HST.
  assert (H1 : SPA segsA (JRD K A0 rho0 A (b :: tmp') rest) S0 rho1 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE S0 rho tp _ _ HX HST); [| exact HV1 | exact HV2 | exact H].
    intros v Hv. cbn in Hv. destruct Hv as [<-|[<-|[<-|[]]]]; unfold NPRE, Pos.le; cbn; discriminate. }
  assert (OTH : forall i, i <> 160%positive -> i <> 161%positive -> i <> 162%positive -> rw rho1 i = rw rho i).
  { intros i N1 N2 N3. unfold rho1. apply rho_sets_other. cbn. intros [X|[X|[X|[]]]]; congruence. }
  assert (ERM : rm rho1 = rm rho) by (unfold rho1; apply rm_rho_sets).
  pose proof (D_pre_facts S0 F0 HFACT rho1 (SPA_facts_hold segsA _ rho1 S0 tp _ H1)) as HF1.
  assert (HTOP1 : top_high A rho1) by (pose proof (be_top _ _ BE) as X; unfold top_high in *; rewrite !OTH by (unfold V_DEPTH; discriminate); exact X).
  assert (H2 : SPA segsA (JRD K A0 rho0 A (b :: tmp') rest) (addo S0 (O_b24 185 160 161 162)) rho1 tp (tr, mkCfg ms md)).
  { apply (carve_b24 _ S0 rho1 tp _ 185 160 161 162 (qb_addr b) (hd_addr tmp') (qb_size b) (Z.of_nat (length (qb_items b))) H1 HX Hswf); try reflexivity; try lia.
    - rewrite OTH by discriminate. exact E185.
    - rewrite ERM. exact CNX.
    - rewrite ERM. exact CSZ.
    - rewrite ERM. exact CCNT.
    - rewrite HOBJ. pose proof (OBD_fixed A rho1 cb_cells (ob_cells (SWD vXK vXF vXL vXS)) HTOP1 HF1) as FX.
      eapply Forall_impl; [|exact FX]. intros o Ho. apply (fixed_clear rho1 (topG (aa_geom A)) o _ _ Ho); lia. }
  assert (H3 : SPA segsA (JRD K A0 rho0 A (b :: tmp') rest) (addf (addo S0 (O_b24 185 160 161 162)) F_b) rho1 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H2 | exact HBEL |]. intros HF. apply Forall_app. split; [exact HF|]. unfold F_b. repeat apply Forall_cons; try apply Forall_nil.
    - unfold vXF. cbn [holds eval]. rewrite OTH by discriminate. rewrite E185, !u64_lit by (unfold HIGH_SHADOW_END in *; lia). exact BA4.
    - cbn [holds]. split; [lia|]. rewrite OTH by discriminate. rewrite E185, u64_lit by lia.
      clear -BA5. pose proof (Z.div_mod (qb_addr b) 8192 ltac:(lia)) as D. rewrite BA5, Z.add_0_r in D. rewrite D. replace (8192 * (qb_addr b / 8192)) with (512 * (qb_addr b / 8192) * 2 ^ 4) by lia. apply Z.mod_mul. lia. }
  destruct (entM_SPA _ _ DH MDH rho1 tp _ HENT HST H3) as (H4 & AG4 & V4 & RM4).
  eexists. split; [exact H4|].
  assert (VV : forall v, In v [160; 161; 162; 184; 185; 186; 187; 208]%positive -> rw (rho_sub rho1 (infer_sub NPRE (ax_S (addf (addo S0 (O_b24 185 160 161 162)) F_b)) (ax_S DH))) v = rw rho1 v).
  { intros v Hv. rewrite (V4 v (SVar v)); [reflexivity|]. unfold MDH, idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. }
  split.
  - unfold HVX. rewrite !VV by (cbn; tauto). rewrite !OTH by discriminate. rewrite hd_addr_cons. tauto.
  - unfold HVB. rewrite !VV by (cbn; tauto). split; [reflexivity | split; reflexivity].
Qed.

Lemma dhn_glue : ltac2:(tb__ "0|2|
S13S12S7S12A1M0G0S22S7S4aQ40A1A1S5bS0G0S16R7A1SaS12A1A3S0S6S14R8A1S9A3S0G0S15R9A1S8S12S5S12R8R7A3R6A3A3S40S3fS79VK;VA0;Vrho0;RaS5S12R9R8A3R7A6S7cR6R5R4A6S4eR7S5S12RaR9A3A2S2S22S22S1S40S3fS79VK;VA0;Vrho0;RdS5S12RcRbA3M1RaA6S7eR1R8R7A6S1S4eR1G1A2S5eR1RcRbA3A2A2Lrho2;A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fb;FA;").
Proof.
  intros A b tmp' rest rho tp w HTH HCI HGL H HV.
  exact (dh_core DHn [SPBranch BC_NE vXK (SLit 0)] A b tmp' rest rho tp w (proj1 DHn_vars) (proj2 DHn_vars) eq_refl (proj2 (proj2 DH_swfs)) (proj2 DH_below) DHnb_ent DHn_objs eq_refl HTH HCI HGL H HV).
Qed.

Lemma dh0_glue : ltac2:(tb__ "0|2|
S13S12S7S12A1M0G0S22S7S4aQ40A1A1S5bS0G0S16R7A1SaS12A1A3S0S6S14R8A1S9A3S0G0S15R9A1S8S12S5S12R8R7A3R6A3A3S40S3fS79VK;VA0;Vrho0;RaS5S12R9R8A3R7A6S85R6R5R4A6S4eR7S5S12RaR9A3A2S2S22S22S1S40S3fS79VK;VA0;Vrho0;RdS5S12RcRbA3M1RaA6S7eR1R8R7A6S1S4eR1G1A2S5eR1RcRbA3A2A2Lrho2;A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fb;FA;").
Proof.
  intros A b tmp' rest rho tp w HTH HCI HGL H HV. destruct w as [tr [ms md]].
  pose proof (proj1 (proj2 H)) as HK. cbn [w_tr w_cfg cfg_model fst snd] in HK.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  destruct HRIG as (_ & _ & E155 & _).
  pose proof (D_pre_facts DH0 [SPNot (SPBranch BC_EQ vXK (SLit 0))] eq_refl rho (SPA_facts_hold segsA _ rho DH0 tp _ H)) as HF0.
  assert (Ha : SPA segsA (JRD K A0 rho0 A (b :: tmp') rest) DH0a rho tp (tr, mkCfg ms md)).
  { apply (carve_sb _ DH0 rho tp _ (aa_geom A) H eq_refl (proj1 DH_swfs) HRTC E155). rewrite DH0_objs.
    exact (OBD_clear_sb A rho cb_cells (ob_cells (SWD vXK vXF vXL vXS)) HKTOP HF0). }
  exact (dh_core DH0a [SPNot (SPBranch BC_EQ vXK (SLit 0))] A b tmp' rest rho tp _ (proj1 DH0_vars) (proj2 DH0_vars) eq_refl (proj1 (proj2 DH_swfs)) (proj1 DH_below) DH0b_ent DH0a_objs eq_refl HTH HCI HGL Ha HV).
Qed.

Lemma DBI0_objs : ltac2:(tb__ "0|1|
S6S6S0S7S1fA1S26S3aS5cS7bR2R1A2A1A1A1S8S1fS8S1fS57S59S58S4cS53S23N1A1A2S7fS6S21Lnz;R2S54S5aX6x2S2eSa5S55S84A3A4A2S5S1fS56S5S1fS96SaS1fA1M0A3A3A3S8S1fS8fS5S1fS4dG0A3A3A3A3Fcz;Fnz;").
Proof. intros [|] [|]; reflexivity. Qed.
Lemma DBx_facts : ltac2:(tb__ "0|1|
S6S6S0S7S20A1S27S3aS7bR2R1A2A1A1S8S20S90S97A1S8S20S5S20S2dS23S9eA1S52A2S5S20S2fPb9Z4A2SaS20A1M0A3A3S5S20S89R1A1S5S20S8aR2A1G0A3A3A3A3A3Fcz;Fnz;").
Proof. intros nz cz. unfold DBx, mkD, mkR, F_D. cbn [ax_S mkA ss_facts]. rewrite <- app_assoc. reflexivity. Qed.
Lemma last_addr_cons : ltac2:(tb__ "0|1|
S12S7S12A1M0S3S0G0R1SaS12A1A3A1S0S39SabS5S12R3R2A3A1SabR2A1A3F_;Fl;Fb;").
Proof. intros b [|c l] H; [congruence | reflexivity]. Qed.

Lemma dbx_flags : ltac2:(tb__ "0|6|
S41S6S6S22S7S4aQ40A1A1S5bS12S7S12A1M0S40S3fR8S7bR7R6A2R5R4R3A6S5eR6R3R2A3S12G0S0G0R5S5S12R2R1A3A3S1S45Z0S18R3A1M1A2S45G1S46Z2M2Z3eA2A2A2F_;Ft;Ft0;S45S44SdScS39S39A2M3S17R5A1A2A1S46G2Z3cA2A2S1S0G0R5SaS12A1A3M4S0S6RcS10A3F_;S1S3G4A1S0S6RcS9A3F_;S1S0S7G3A1S17R6A1SaG3A1A3M5S0S6RbS9A3F_;S3G5A1S0S6RbS10A3F_;A2A2A2F_;F_;F_;F_;Ftmp';Fb;Fw;Ftp;Frho;Fcz;Fnz;FJ;").
Proof.
  intros J nz cz rho tp w b tmp' H (E160 & E161 & E162) HT0 HLEN.
  pose proof (SPA_facts_hold segsA _ rho (DBx nz cz) tp w H) as HFa. rewrite DBx_facts in HFa.
  apply Forall_app in HFa as [_ HFa]. apply Forall_app in HFa as [_ HFa].
  pose proof (Forall_inv HFa) as FCZ. pose proof (Forall_inv (Forall_inv_tail HFa)) as FNZ.
  assert (NZ : nz = true <-> hd_addr tmp' <> 0).
  { destruct nz; unfold F_nzB, vBN in FNZ; cbn [holds branch_taken eval] in FNZ; rewrite E160 in FNZ; unfold bv_eqb in FNZ.
    - apply negb_true_iff in FNZ. apply Z.eqb_neq in FNZ. destruct tmp' as [|t0 t]; [exfalso; apply FNZ; reflexivity|].
      split; [intros _|reflexivity]. rewrite hd_addr_cons. pose proof (HT0 t0 t eq_refl). lia.
    - split; [discriminate|]. intros NE. exfalso. apply FNZ. apply negb_true_iff. apply Z.eqb_neq. destruct tmp' as [|t0 t]; [cbn in NE; lia|].
      rewrite hd_addr_cons in *. pose proof (HT0 t0 t eq_refl). rewrite !u64_lit by lia. lia. }
  assert (CZ : cz = true <-> Z.of_nat (length (qb_items b)) = 0).
  { destruct cz; unfold F_czB, vBC in FCZ; cbn [holds branch_taken eval] in FCZ; rewrite E162 in FCZ; unfold bv_eqb in FCZ.
    - apply Z.eqb_eq in FCZ. rewrite !u64_lit in FCZ by lia. split; [intros _; exact FCZ | reflexivity].
    - split; [discriminate|]. intros E0. exfalso. apply FCZ. apply Z.eqb_eq. rewrite !u64_lit by lia. exact E0. }
  split; [intros ->; destruct nz; [exfalso; apply (proj1 NZ eq_refl); reflexivity | reflexivity]|].
  split; [intros NE; apply NZ; destruct tmp' as [|t0 t]; [congruence|]; rewrite hd_addr_cons; pose proof (HT0 t0 t eq_refl); lia|].
  split; [intros E; apply CZ; rewrite E; reflexivity|].
  intros NE. destruct cz; [|reflexivity]. exfalso. pose proof (proj1 CZ eq_refl) as X. destruct (qb_items b); [congruence | cbn in X; lia].
Qed.

Lemma db_unobj : ltac2:(tb__ "0|5|
S6S6S13S12S7S12A1M0G0S22S7S4aQ40M1A1M2A1S7Sa4A1M3Sa7Sa3S0G0S16R9A1SaS12A1A3S0S6S14RaA1S9A3S39S73RcR1A2S73VA0;R2A2F_;Fz;S0G0S15RcA1S8S12S5S12RbRaA3R9A3A3S40S3fS79VK;VA0;Vrho0;RdS5S12RcRbA3RaA6S7bRfReA2R9R8SbG3Sa1R7Sa2R6R5A2A4A6S0G2S24RaPb9A2S4bG1S18RdA1A2A3S5eRbReRdA3Sa8RcS5S1fS87S7fA1SaS1fA1A3Sa9R8RbR9A3A3S22S1S40S3fS7aVK;VA0;Vrho0;R11S18R10A1S44SdScS39S39A2S17R10A1M4A2A1U0G4RfReAaS5cS7bR13R12A2A1R1RcSbG3Sa1RbSa2RaR9A2A4A6S0S77S74S3fS28R1A1A2S74S3fS28RdA1A2A3A2Trho3;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Frest;Ftmp';Fb;FA;Fcz;Fnz;").
Proof.
  intros nz cz A b tmp' rest rho tp tr ms md HTH HCI HQW HGL H E185 (E160 & E161 & E162) rho3.
  destruct (proj2 H) as (HK & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HRM, HFRM. pose proof HRM as (HBM & HLT & HLR & HTHD & HGH).
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  assert (INB : In b (aa_q_global A)) by (rewrite HGL; left; reflexivity).
  destruct (batch_addr_facts A HTH rho b BE INB) as (BA1 & BA2 & BA3 & BA4 & BA5). unfold HIGH_SHADOW_END in BA4.
  cbn [app] in HBM. pose proof (Forall_inv HBM) as HBMb. pose proof HBMb as (CSZ & CCNT & _).
  assert (CNX : cell_ok (view segsA (rm rho)) (mkACell (qb_addr b) 8 (hd_addr tmp'))) by (cbn [qlinks] in HLT; destruct HLT as [X _]; destruct tmp'; exact X).
  set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ [O_b vBN] vXF 0 24 _ Hsm (DBx_objs nz cz) ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                ltac:(unfold vXF; cbn [eval]; rewrite E185, u64_lit by lia; lia) ltac:(unfold vXF; cbn [eval]; rewrite E185, u64_lit by lia; lia)) as [AV PR].
  fold rho3 v3 in AV, PR. unfold vXF in AV, PR. cbn [eval] in AV, PR. rewrite E185, u64_lit in AV, PR by lia.
  assert (C0 : cell_ok v3 (mkACell (qb_addr b) 8 (hd_addr tmp'))) by (replace (qb_addr b) with (qb_addr b + 0) at 1 by lia; exact (av_cell v3 (qb_addr b) 0 8 _ _ rho (fun j => AV _ _ _ j (or_introl eq_refl)) E160)).
  assert (C1 : cell_ok v3 (mkACell (qb_addr b + 8) 8 (qb_size b))) by exact (av_cell v3 (qb_addr b) 8 8 _ _ rho (fun j => AV _ _ _ j (or_intror (or_introl eq_refl))) E161).
  assert (C2 : cell_ok v3 (mkACell (qb_addr b + 16) 8 (Z.of_nat (length (qb_items b))))) by exact (av_cell v3 (qb_addr b) 16 8 _ _ rho (fun j => AV _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) E162).
  clear AV.
  set (P := fun z : Z => qb_addr b <= z < qb_addr b + 24).
  assert (INRG : forall x, in_ranges rho [O_b vBN] x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[]]. unfold O_b, carved, vXF in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd eval] in Hz. rewrite E185, u64_lit in Hz by lia. lia. }
  destruct (absorb_out rho [O_b vBN] (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (EV : v3 = v).
  { apply functional_extensionality. intros z. destruct (Z_lt_dec z (qb_addr b)) as [|]; [apply FR; unfold P; lia|]. destruct (Z_lt_dec z (qb_addr b + 24)) as [|]; [|apply FR; unfold P; lia].
    destruct (Z_lt_dec z (qb_addr b + 8)) as [|]; [apply (cell_ok_same v v3 _ CNX C0); cbn [c_addr c_w]; lia|].
    destruct (Z_lt_dec z (qb_addr b + 16)) as [|]; [apply (cell_ok_same v v3 _ CSZ C1); cbn [c_addr c_w]; lia | apply (cell_ok_same v v3 _ CCNT C2); cbn [c_addr c_w]; lia]. }
  destruct (K_FRM_absorb K HL A0 rho0 A HQW rho rho3 tp tr md P ltac:(intros z; unfold P; lia) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. left. apply (batch_in_QW A HTH rho b z BE INB). unfold P in Hz. lia. }
  { intros z Hz. fold v3. destruct (PR z ltac:(unfold P in Hz; lia)) as [x Hx]. rewrite Hx. discriminate. }
  split; [|exact EV].
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (DBx nz cz) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (DBx nz cz) _ [O_b vBN] tp tr ms md (DBx_objs nz cz) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  split; [exact (proj1 HU)|]. split; [exact HK3|]. fold v3. rewrite EV. split; [|split; [|exact HF3]].
  - apply CURB_of_batch_mem; [exact HBMb|]. pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 A HTH) in HBP.
    exact (proj1 (proj2 (proj1 (Forall_forall _ _) HBP b INB))).
  - split; [exact (Forall_inv_tail HBM)|]. split; [cbn [qlinks] in HLT; exact (proj2 HLT)|]. split; [exact HLR|]. split; [exact HTHD | exact HGH].
Qed.

Lemma jrd_pure : ltac2:(tb__ "0|5|
S13S12S7S12A1M0G0S22S7S4aQ40A1A1S7Sa4A1Sa3S0G0S16R8A1SaS12A1A3S0S6S14R9A1S9A3S0G0S15RaA1S8S12S5S12R9R8A3R7A3A3S79VK;VA0;Vrho0;RbS5S12RaR9A3R8R7R6R5R4AaS1S50RcR8A2S1S43Z2000M1S1bRbA1A2S1S43Z0M2S92RaA1M3A2S1S43S47G1S44SdS12RaA2A1A2G3A2S1S43S44SdScS39S39A2S17RbA1A2A1S9fA2S12G0S0G0RcS5S12R2R1A3A3S1S45G2S18R3A1M4A2S45G4S46Z2Z3eA2A2A2F_;Ft;Ft0;A2A2A2A2A2F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Frest;Ftmp';Fb;FA;").
Proof.
  intros A b tmp' rest rho tp tr md HTH HCI HGL (HK & (HBM & _) & _).
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE. split; [exact BE|].
  pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 A HTH), HGL in HBP.
  cbn [app] in HBP, HBM. pose proof (Forall_inv HBP) as PB. pose proof (Forall_inv HBM) as MB.
  apply Forall_inv_tail in HBP. apply Forall_inv_tail in HBM. apply Forall_app in HBP as [P1 _]. apply Forall_app in HBM as [M1 _].
  pose proof (qsize_ge A _ [b] ltac:(constructor; [exact PB | constructor]) ltac:(constructor; [exact MB | constructor])) as Q1.
  pose proof (qsize_ge A _ tmp' P1 M1) as Q2. unfold kQuarantineBatchSize in *. cbn [qsize fold_right length Z.of_nat] in Q1.
  split; [cbn in Q1; lia|]. split; [lia|]. split; [lia|]. split; [exact (proj1 (proj2 PB))|].
  intros t0 t E. assert (INT : In t0 (aa_q_global A)) by (rewrite HGL, E; right; apply in_or_app; left; left; reflexivity).
  destruct (batch_addr_facts A HTH rho t0 BE INT) as (B1 & B2 & B3 & _). lia.
Qed.

Lemma dbi_glue : ltac2:(tb__ "0|8|
S6S13S12ScS39S39A2M0S7G0A1M1S7S12A1M2G2S22S7S4aQ40A1A1S5bS0G2S16R9A1SaS12A1A3S0S6S14RaA1S9A3S39S73RcR1A2S73VA0;R2A2F_;Fz;S0G2S15RcA1S8S12S5S12RbR8A3R7A3A3S0G1S17RcA1S5G0RbRaA3A3S45S92S5S12RdRaA3A1S46Z2Z3eA2M3A2S40S3fS79VK;VA0;Vrho0;RfS5S12ReRbA3RaA6S7bR10S10A2R9R8R7A6S4eRaS5S12RfRcA3A2S5eRbR10RdA3S2S22S22S1S40S3fS7aVK;VA0;Vrho0;R13S18R12A1M4S44SdG0S17R12A1M5A2A1M6U0M7G5RfReAaS82R1RcRbA6S1S4eR1RfA2S1S63R1G4G6G7R11A5S1S64R1G4G7R11A4S45S92RfA1G3A2A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fits;Fit0;Fb;FA;Fnz;").
Proof.
  intros nz A b it0 its tmp' rest rho tp w HTH HCI HQW HGL HIT HSZ H HVx HVb. destruct w as [tr [ms md]].
  pose proof HVx as (E184 & E185 & E186 & E187 & E208). rewrite hd_addr_cons in E185. pose proof HVb as (E160 & E161 & E162).
  destruct (jrd_pure A b tmp' rest rho tp tr md HTH HCI HGL (proj2 H)) as (BE & QB & QT0 & QTL & HCNT & HT0).
  destruct (dbx_flags _ nz false rho tp _ b tmp' H HVb HT0 ltac:(unfold kQuarantineBatchCount in HCNT; lia)) as (FL1 & FL2 & _ & _).
  assert (INB : In b (aa_q_global A)) by (rewrite HGL; left; reflexivity).
  destruct (batch_addr_facts A HTH rho b BE INB) as (BA1 & BA2 & BA3 & BA4 & BA5). unfold HIGH_SHADOW_END in BA4.
  destruct (db_unobj nz false A b tmp' rest rho tp tr ms md HTH HCI HQW HGL H E185 HVb) as [H3 EV].
  set (rho3 := rho_absorb rho [O_b vBN] (vms md tp ms)) in *.
  set (JI := JRI K A0 rho0 A (qb_addr b) (Z.of_nat (length (qb_items b))) 0 (qb_items b) tmp' rest) in *.
  pose proof (JRI_stable K HL A0 rho0 A (qb_addr b) (Z.of_nat (length (qb_items b))) 0 (qb_items b) tmp' rest) as HST. fold JI in HST.
  destruct (proj2 H3) as (_ & HCB & _). cbn [w_tr w_cfg cfg_model fst snd] in HCB.
  set (rho4 := rho_sets rho3 [(198%positive, Z_to_bv 64 (fst it0 - 16))]).
  assert (H4 : SPA segsA JI (DBI0 nz) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE (DBI0 nz) rho3 tp _ _ eq_refl HST); [| exact (proj1 (DBI0_vars nz)) | exact (proj2 (DBI0_vars nz)) | exact H3].
    intros v Hv. cbn in Hv. destruct Hv as [<-|[]]. unfold NPRE, Pos.le; cbn; discriminate. }
  assert (OTH : forall i, i <> 198%positive -> rw rho4 i = rw rho i).
  { intros i N1. unfold rho4. rewrite rho_sets_other; [reflexivity|]. cbn. intros [X|[]]; congruence. }
  assert (ERM : rm rho4 = rm rho3) by (unfold rho4; apply rm_rho_sets).
  pose proof (D_pre_facts (DBI0 nz) _ (DBx_facts nz false) rho4 (SPA_facts_hold segsA _ rho4 (DBI0 nz) tp _ H4)) as HF4.
  assert (HTOP4 : top_high A rho4) by (pose proof (be_top _ _ BE) as X; unfold top_high in *; rewrite !OTH by (unfold V_DEPTH; discriminate); exact X).
  assert (Ee : eval rho4 (add vXF (SLit 152)) = Z_to_bv 64 (qb_addr b + 152)).
  { apply (eval_add_lit A); try lia. unfold vXF. cbn [eval]. rewrite OTH by discriminate. exact E185. }
  assert (Cm : cell_ok (view segsA (rm rho3)) (mkACell (qb_addr b + 24 + 8 * Z.of_nat 0) 8 (fst it0 - 16))).
  { destruct HCB as (_ & _ & _ & _ & HSL). destruct (HSL 0%nat it0 ltac:(rewrite HIT; reflexivity)) as [C _]. cbn [Z.of_nat] in C. exact C. }
  assert (H5 : SPA segsA JI (addo (DBI0 nz) (O_itg (add vXF (SLit 152)))) rho4 tp (tr, mkCfg ms md)).
  { apply (carve_slot _ (DBI0 nz) rho4 tp _ (add vXF (SLit 152)) (qb_addr b + 152) (fst it0 - 16) H4 eq_refl (DBI_swf nz) Ee); try reflexivity; try lia.
    - rewrite ERM. replace (qb_addr b + 152 - 128) with (qb_addr b + 24 + 8 * Z.of_nat 0) by (cbn [Z.of_nat]; lia). exact Cm.
    - unfold DBI0. rewrite (DBI0_objs nz false).
      pose proof (OBD_fixed A rho4 cb_cells (ob_cells (SWD (add vXK (SLit (-1))) vBN (if nz then vXL else ZQ) (SAlu ALU_SUB vXS vBS))) HTOP4 HF4) as FX.
      eapply Forall_impl; [|exact FX]. intros o Ho. apply (fixed_clear rho4 (topG (aa_geom A)) o _ _ Ho); lia. }
  assert (H6 : SPA segsA JI (DBI1 nz) rho4 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H5 | exact (DBI_below nz) |]. intros HF. apply Forall_app. split; [exact HF|]. unfold FI1. repeat apply Forall_cons; try apply Forall_nil.
    - cbn [holds]. rewrite Ee. change (eval rho4 (SLit (HIGH_SHADOW_END + 152))) with (Z_to_bv 64 (HIGH_SHADOW_END + 152)). rewrite !u64_lit by (unfold HIGH_SHADOW_END; lia). unfold HIGH_SHADOW_END. lia.
    - cbn [holds]. split; [lia|]. rewrite OTH by discriminate. rewrite E185, u64_lit by lia.
      clear -BA5. pose proof (Z.div_mod (qb_addr b) 8192 ltac:(lia)) as D. rewrite BA5, Z.add_0_r in D. rewrite D. replace (8192 * (qb_addr b / 8192)) with (512 * (qb_addr b / 8192) * 2 ^ 4) by lia. apply Z.mod_mul. lia. }
  destruct (entM_SPA _ _ DI (MDBI nz) rho4 tp _ (DBI1_ent nz) HST H6) as (H7 & AG7 & V7 & RM7).
  eexists. split; [exact H7|].
  assert (LEN : Z.of_nat (length (b :: tmp')) = Z.of_nat (length tmp') + 1) by (cbn [length]; lia).
  split.
  - unfold HVX. rewrite (V7 184%positive (add vXK (SLit (-1)))), (V7 185%positive vBN), (V7 186%positive (if nz then vXL else SLit 0)),
      (V7 187%positive (SAlu ALU_SUB vXS vBS)), (V7 208%positive (SVar 208)) by (unfold MDBI; cbn; tauto).
    split; [|split; [|split; [|split]]].
    + replace (Z.of_nat (length tmp')) with (Z.of_nat (length (b :: tmp')) + -1) by lia. apply (eval_add_lit A); try lia.
      * unfold vXK. cbn [eval]. rewrite OTH by discriminate. exact E184.
      * rewrite qsize_cons in HSZ. lia.
      * rewrite qsize_cons in HSZ. lia.
    + unfold vBN. cbn [eval]. rewrite OTH by discriminate. exact E160.
    + destruct nz.
      * unfold vXL. cbn [eval]. rewrite OTH by discriminate. rewrite E186. rewrite last_addr_cons; [reflexivity|]. intros E. discriminate (FL1 E).
      * assert (ET : tmp' = []) by (destruct tmp' as [|t0 t]; [reflexivity|]; discriminate (FL2 ltac:(discriminate))). rewrite ET. reflexivity.
    + replace (qsize tmp') with (qsize (b :: tmp') - qb_size b) by (rewrite qsize_cons; lia). apply (eval_sub_z A).
      * unfold vXS. cbn [eval]. rewrite OTH by discriminate. exact E187.
      * unfold vBS. cbn [eval]. rewrite OTH by discriminate. exact E161.
      * rewrite qsize_cons. lia.
      * lia.
    + cbn [eval]. rewrite OTH by discriminate. exact E208.
  - split; [|split; [unfold HVS; rewrite RM7, ERM; exact Cm | rewrite qsize_cons in HSZ; lia]].
    unfold HVI. rewrite (V7 162%positive (SVar 162)), (V7 163%positive (add vXF (SLit 152))), (V7 164%positive (SLit 16)), (V7 165%positive (SVar 198)), (V7 166%positive vXF) by (unfold MDBI; cbn; tauto).
    split; [cbn [eval]; rewrite OTH by discriminate; exact E162|]. split; [rewrite Ee; f_equal; lia|]. split; [reflexivity|].
    split; [cbn [eval]; unfold rho4; reflexivity|]. unfold vXF. cbn [eval]. rewrite OTH by discriminate. exact E185.
Qed.

Lemma hvx_pop : ltac2:(tb__ "0|7|
S6S13S12S7S12A1M0S22S22S4eR2S5S12R4R3A3A2S5eR3R5R4A3S43Z2000M1S1bR6A1A2S43Z0M2S92R6A1A2S43S47G1S44SdS12R7A2A1A2S92R7A1A2S45S92S5S12R9R8A3A1S46Z2Z3eA2A2S0G0R9SaS12A1M3A3S0S6RdS10A3F_;S3S0G0RaG3A3A1S0S6ReS9A3F_;S0S1dS19RdA1M4G4A3S0S4aQ40A1M5S24RaPb8A2S2cRbS4cS53S23N1A1A2A2A3S0G5S24RbPb9A2S2cRcS7fA2A3S0G5S24RcPbaA2S2cRdS6S21Lnz;R11S54S23G2A1X6x2A2A3S0G5S24RdPbbA2S2cReS2eSa5S55S84A3A2A3S0G5S24RePd0M6A2S2cRfS25G6A1A2A3S4eRfR11A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho2;Frho;Ftmp';Fb;FA;Fnz;").
Proof.
  intros nz A b tmp' rho rho2 (E184 & E185 & E186 & E187 & E208) (E160 & E161 & E162) QB QT0 QTL HSZ FL1 FL2 _ V184 V185 V186 V187 V208.
  assert (LEN : Z.of_nat (length (b :: tmp')) = Z.of_nat (length tmp') + 1) by (cbn [length]; lia). rewrite qsize_cons in HSZ.
  unfold HVX. rewrite V184, V185, V186, V187, V208. split; [|split; [|split; [|split]]].
  - replace (Z.of_nat (length tmp')) with (Z.of_nat (length (b :: tmp')) + -1) by lia. apply (eval_add_lit A); try lia. unfold vXK. cbn [eval]. exact E184.
  - unfold vBN. cbn [eval]. exact E160.
  - destruct nz.
    + unfold vXL. cbn [eval]. rewrite E186. rewrite last_addr_cons; [reflexivity|]. intros E. discriminate (FL1 E).
    + assert (ET : tmp' = []) by (destruct tmp' as [|t0 t]; [reflexivity|]; discriminate (FL2 ltac:(discriminate))). rewrite ET. reflexivity.
  - replace (qsize tmp') with (qsize (b :: tmp') - qb_size b) by (rewrite qsize_cons; lia). apply (eval_sub_z A).
    + unfold vXS. cbn [eval]. exact E187.
    + unfold vBS. cbn [eval]. exact E161.
    + rewrite qsize_cons. lia.
    + rewrite qsize_cons. lia.
  - cbn [eval]. exact E208.
Qed.

Lemma batch_sb_facts : ltac2:(tb__ "0|6|
S13S12S22S7S4aQ40M0A1M1A1S7Sa4A1Sa3S0S7S12A1S16R6A1SaS12A1A3S0S6S14R7A1S9A3VK;R8R6R5R4R3A5S9aS12R8S15R9A1A3S1S0G1S24R8P9bA2S4bG0S1cS19RaA1A1M2A2A3S1S43Z0G2A2S1S45S42G2S46Z2M3Z25A2A2S46G3Z3eA2A2S1S43S42G2S47Z18S46G3Z20A2M4A2A2S18R9A1M5A2S43S42G5Z2000A2S42G2S47Z19G4A2A2A2A2A2A2A2F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fb;FA;").
Proof.
  intros A b rho tp tr md HTH HCI HK INB. pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG _ _ _ _ _ _ _ _ _ _ _]. destruct HRIG as (_ & _ & E155 & _).
  destruct BE as [HG' _ HQP HAU _ _ _]. rewrite <- (qall_A1 A HTH) in INB.
  destruct (batch_slot A HQP HAU HG' b INB) as (y & E & Y0 & Yal & Y1 & B5 & B6 & B7 & _).
  pose proof (SB_facts A HG') as (S1 & S2 & S3). rewrite kSpaceSize_val in S3. unfold HIGH_SHADOW_END in S2.
  split; [exact E155|]. split; [lia|]. split; [lia|]. split; [lia | exact B6].
Qed.

Lemma dbt_glue : ltac2:(tb__ "0|7|
S6S13S12S7S12A1M0G0S22S7S4aQ40M1A1M2A1S5bS0G0S16R7A1SaS12A1A3S0S6S14R8A1S9A3S39S73RaR1A2S73VA0;R2A2F_;Fz;S0G0S15RaA1S8S12S5S12R9R8A3R7A3A3S45S92S5S12RaR9A3A1S46Z2Z3eA2M3A2S40S3fS79VK;VA0;Vrho0;RcS5S12RbRaA3R9A6S7bRdS9A2R8R7R6A6S4eR9S5S12RcRbA3A2S5eRaRdRcA3S2S22S22S1S40S3fS7aVK;VA0;Vrho0;R10S18RfA1M4S44SdScS39S39A2M5S17RfA1M6A2A1U0G6ReRdAaS83R1RbRaA6S1S4eR1ReA2S1S0G2S24R1Pa6A2S4bG1G4A2A3S1S0S7G5A1G6SaG5A1A3S45S92ReA1G3A2A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fb;FA;Fnz;").
Proof.
  intros nz A b tmp' rest rho tp w HTH HCI HQW HGL HSZ H HVx HVb. destruct w as [tr [ms md]].
  pose proof HVx as (E184 & E185 & E186 & E187 & E208). rewrite hd_addr_cons in E185.
  destruct (jrd_pure A b tmp' rest rho tp tr md HTH HCI HGL (proj2 H)) as (BE & QB & QT0 & QTL & HCNT & HT0).
  destruct (dbx_flags _ nz true rho tp _ b tmp' H HVb HT0 ltac:(unfold kQuarantineBatchCount in HCNT; lia)) as (FL1 & FL2 & _ & FL4).
  assert (INB : In b (aa_q_global A)) by (rewrite HGL; left; reflexivity).
  destruct (batch_sb_facts A b rho tp tr md HTH HCI (proj1 (proj2 H)) INB) as (E155 & SB0 & SB1 & SB2 & SB3).
  destruct (db_unobj nz true A b tmp' rest rho tp tr ms md HTH HCI HQW HGL H E185 HVb) as [H3 EV].
  set (rho3 := rho_absorb rho [O_b vBN] (vms md tp ms)) in *.
  set (JI := JRI K A0 rho0 A (qb_addr b) (Z.of_nat (length (qb_items b))) 0 (qb_items b) tmp' rest) in *.
  pose proof (JRI_stable K HL A0 rho0 A (qb_addr b) (Z.of_nat (length (qb_items b))) 0 (qb_items b) tmp' rest) as HST. fold JI in HST.
  assert (H6 : SPA segsA JI (DBT1 nz) rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H3 | exact (DBT_below nz) |]. intros HF. apply Forall_app. split; [exact HF|]. unfold F_b24. repeat apply Forall_cons; try apply Forall_nil.
    - unfold vSB, vXF. cbn [holds eval]. change (rw rho3) with (rw rho). rewrite E155, E185, !u64_lit by lia. lia.
    - cbn [holds]. rewrite (eval_add_lit A rho3 vSB (ag_spacebeg (aa_geom A)) (2 ^ 37)) by (try lia; unfold vSB; cbn [eval]; exact E155).
      unfold vXF. cbn [eval]. change (rw rho3) with (rw rho). rewrite E185, !u64_lit by lia. lia. }
  destruct (entM_SPA _ _ DTs (MDBT nz) rho3 tp _ (DBT1_ent nz) HST H6) as (H7 & AG7 & V7 & RM7).
  eexists. split; [exact H7|]. split; [|split].
  - apply (hvx_pop nz A b tmp' rho3 _ HVx HVb QB QT0 QTL HSZ FL1 FL2 eq_refl); apply V7; unfold MDBT; cbn; tauto.
  - rewrite (V7 166%positive vXF) by (unfold MDBT; cbn; tauto). unfold vXF. cbn [eval]. exact E185.
  - split; [|rewrite qsize_cons in HSZ; lia]. destruct (qb_items b) as [|i0 il]; [reflexivity|]. discriminate (FL4 ltac:(discriminate)).
Qed.

Lemma DIc0_objs : ltac2:(tb__ "0|3|
S1S0S7S1fA1M0S26S3aS5cS81A1A1A1S8S1fS8S1fS57S59S58S53S52S54S55A4A2S5S1fS56S5S1fS96SaS1fA1M1A3A3A3S8S1fS8fS5S1fS4dG1A3A3A3M2A3S0G0S26S3aS5cS7dA1A1A1G2A3A2").
Proof. split; reflexivity. Qed.
Lemma DIc_facts : ltac2:(tb__ "0|5|
S1S0S7S20A1M0S27S3aS81A1A1S8S20S90S97A1M1S8S20S5S20S2dS23S9eA1S86A2S5S20S2fPa6Z4A2S5S20S2dS23S42S9eZ98A2A1S80A2S5S20S2fPa3Z3A2SaS20A1M2A3A3A3A3M3S5S20S36Sa6S8bS4cS8cS23Z10A1A2A3M4G2A3A3A3A3S0G0S27S3aS7dA1A1S8S20G1S8S20G3S5S20S37G4A1G2A3A3A3A3A2").
Proof. split; unfold DIc, DTc, mkD, mkR, F_DI; cbn [ax_S mkA ss_facts]; rewrite <- app_assoc; reflexivity. Qed.

Lemma ri_flags : ltac2:(tb__ "0|3|
S41S6S22S7S4aQ40M0A1M1A1S5bS39SeS40S3fR7S6S3bLc;R6S81S7dX6x2R5R4R3A6S0G1S24R6Pa2A2S4bG0R3A2A3S0G1S24R7Pa4A2S4bG0S42Z10S44R3A1A2A2A3S1S43Z0R5A2S45R5S46Z2Z3cA2M2A2A2S45S44R5A1G2A2S4S0S6RbS9A3S3S0S39S44SfR6A1A1R7A3A1A2F_;F_;F_;F_;F_;Fnd;Fn0;Fw;Ftp;Frho;Fc;FJ;").
Proof.
  intros J c rho tp w n0 nd H E162 E164 Hn0 Hnd.
  assert (E1 : eval rho s9' = Z_to_bv 64 (16 + Z.of_nat nd + 1)) by (apply (eval_add_lit A0); try lia; unfold vS9; cbn [eval]; exact E164).
  assert (E2 : eval rho (add vBC (SLit 16)) = Z_to_bv 64 (n0 + 16)) by (apply (eval_add_lit A0); try lia; unfold vBC; cbn [eval]; exact E162).
  pose proof (SPA_facts_hold segsA _ rho _ tp w H) as HFa. destruct c.
  - rewrite (proj1 DIc_facts) in HFa. apply Forall_app in HFa as [_ HFa]. apply Forall_app in HFa as [_ HFa]. pose proof (Forall_inv HFa) as F.
    cbn [holds branch_taken] in F. rewrite E1, E2 in F. unfold bv_eqb in F. apply negb_true_iff in F. apply Z.eqb_neq in F. rewrite !u64_lit in F by lia.
    split; [intros _; lia | reflexivity].
  - rewrite (proj2 DIc_facts) in HFa. apply Forall_app in HFa as [_ HFa]. apply Forall_app in HFa as [_ HFa]. pose proof (Forall_inv HFa) as F.
    cbn [holds branch_taken] in F. rewrite E1, E2 in F. unfold bv_eqb in F. split; [discriminate|]. intros NE. exfalso. apply F. apply negb_true_iff. apply Z.eqb_neq.
    rewrite !u64_lit by lia. lia.
Qed.

Lemma it_unobj : ltac2:(tb__ "0|7|
S3bS13S39S39S39SeS7ScS39S39A2M0A1S7S12A1M1G1G0S22S7S4aQ40A1A1S7Sa4A1M2Sa7Sa3S0S7S1fA1S26S3aRfA1A1S8S1fS26S3aS5cRfA1A1A1S5S1fS88SaS1fA1A3M3A3A3S0G1S16RfA1SaS12A1A3S0S6S14R10A1S9A3S39S73R12R1A2S73VA0;R2A2F_;Fz;S0G1S15R12A1S5S12S1aR11RdR10A3S8S12RcRbA3A3A3S40S3fS7aVK;VA0;Vrho0;R13R12R10SfRfA1ReRdRcAaR14RaR9SbG2Sa1R8Sa2R7R6A2A4A6S63RbR13R11R10RcA5S64RcR14R11RdA4Sa8RdG3Sa9R9RcRaA3A3S22S1S40S3fS7aVK;VA0;Vrho0;R17R16R14SfR13A1M4R12R11R10AaS5cR18A1R1RdSbG2Sa1RcSa2RbRaA2A4A6S1S0S77S74S3fS28R1A1A2S74S3fS28ReA1A2A3S1S43Z646000R16A2S1S43S42R16Z2000M5A2M6S1eS19R17A1A1A2S1S43G6S46Z2Z3eA2A2S1S0S39S49R16G5A2Z0A3S1S0S39R14S42S44G4A1S44SdG0R12A2A1A2A3S43R14S9fA2A2A2A2A2A2A2A2Trho3;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fit;Frest;Ftmp';Fits;Fnd;Fn0;Fs;Fa;FA;FSt;").
Proof.
  intros St A a s n0 nd its tmp' rest it rho tp tr ms md HOBJ HTH HCI HQW HGL H (E162 & E163 & E164 & E165 & E166) HS rho3.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  assert (INB : In (mkQB a its s) (aa_q_global A)) by (rewrite HGL; left; reflexivity).
  destruct (batch_addr_facts A HTH rho _ BE INB) as (BA1 & BA2 & BA3 & BA4 & BA5). cbn [qb_addr] in BA1, BA2, BA3, BA4, BA5. unfold HIGH_SHADOW_END in BA4.
  pose proof HCB as (_ & HN0 & HN1 & _). unfold kQuarantineBatchCount in HN1.
  set (B := a + 152 + 8 * Z.of_nat nd) in *.
  set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  assert (EB : bv_unsigned (eval rho vS7) = B) by (unfold vS7; cbn [eval]; rewrite E163, u64_lit by (unfold B; lia); reflexivity).
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ [O_it] vS7 (-128) (-120) [(-128, 8%nat, vIT)] Hsm HOBJ ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                ltac:(rewrite EB; unfold B; lia) ltac:(rewrite EB; unfold B; lia)) as [AV PR].
  fold rho3 v3 in AV, PR. rewrite EB in AV, PR.
  assert (C0 : cell_ok v3 (mkACell (B + -128) 8 (fst it - 16))) by exact (av_cell v3 B (-128) 8 _ _ rho (fun j => AV _ _ _ j (or_introl eq_refl)) E165).
  clear AV. unfold HVS in HS. fold v in HS. replace (a + 24 + 8 * Z.of_nat nd) with (B + -128) in HS by (unfold B; lia).
  set (P := fun z : Z => B - 128 <= z < B - 120).
  assert (INRG : forall x, in_ranges rho [O_it] x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[]]. unfold O_it in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. rewrite EB in Hz. lia. }
  destruct (absorb_out rho [O_it] (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (EV : v3 = v).
  { apply functional_extensionality. intros z. destruct (Z_lt_dec z (B - 128)) as [|]; [apply FR; unfold P; lia|]. destruct (Z_lt_dec z (B - 120)) as [|]; [|apply FR; unfold P; lia].
    apply (cell_ok_same v v3 _ HS C0); cbn [c_addr c_w]; lia. }
  destruct (K_FRM_absorb K HL A0 rho0 A HQW rho rho3 tp tr md P ltac:(intros z; unfold P; lia) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. left. apply (batch_in_QW A HTH rho _ z BE INB). cbn [qb_addr]. unfold P, B in Hz. lia. }
  { intros z Hz. fold v3. destruct (PR z ltac:(unfold P in Hz; lia)) as [x Hx]. rewrite Hx. discriminate. }
  split; [|split; [exact EV | repeat split; try assumption; lia]].
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ St rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho St _ [O_it] tp tr ms md HOBJ HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  split; [exact (proj1 HU)|]. split; [exact HK3|]. fold v3. rewrite EV. split; [exact HCB|]. split; [exact HRM | exact HF3].
Qed.

Lemma dic_glue : ltac2:(tb__ "0|3|
S13S39S39S39SeScS39S39A2M0G0S7G0A1S7S12A1M1G1S22S7S4aQ40A1A1S5bS0G1S16RdA1SaS12A1A3S0S6S14ReA1S9A3S39S73R10R1A2S73VA0;R2A2F_;Fz;S0G1S15R10A1S5S12S1aRfS5G0RaR9A3ReA3S8S12R8R7A3A3A3S40S3fS7aVK;VA0;Vrho0;R11R10ReSfRdA1S5G0RbRaA3R9R8AaS81R7R6R5A6S4eR8RaA2S63R9R12R10RfReA5S64RaR13R10RfA4S2S22S22S1S40S3fS7aVK;VA0;Vrho0;R16R15R13SfR12A1M2S5G0R10RfA3ReRdAaS82R1RbRaA6S1S4eR1ReA2S1S63R1R15R13G2R10A5S64R1R15G2R10A4A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fits';Fit1;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it it1 its' tmp' rest rho tp w HTH HCI HQW HGL H HVx HVi HVs. destruct w as [tr [ms md]].
  pose proof HVx as (E184 & E185 & E186 & E187 & E208). pose proof HVi as (E162 & E163 & E164 & E165 & E166).
  destruct (it_unobj DIc A a s n0 nd (it1 :: its') tmp' rest it rho tp tr ms md (proj1 DIc_objs) HTH HCI HQW HGL H HVi HVs) as (H3 & EV & BA1 & BA2 & BA3 & BA5 & HN0 & HN1).
  set (rho3 := rho_absorb rho [O_it] (vms md tp ms)) in *. unfold kQuarantineBatchCount in HN1. cbn [length] in HN0. pose proof (topG_range (aa_geom A)) as TG.
  set (JI := JRI K A0 rho0 A a n0 (S nd) (it1 :: its') tmp' rest) in *.
  pose proof (JRI_stable K HL A0 rho0 A a n0 (S nd) (it1 :: its') tmp' rest) as HST. fold JI in HST.
  destruct (proj2 H3) as (HK3 & HCB & _). cbn [w_tr w_cfg cfg_model fst snd] in HK3, HCB.
  pose proof (benv_of_K K HL A HCI rho3 tp tr md HK3) as BE.
  set (rho4 := rho_sets rho3 [(198%positive, Z_to_bv 64 (fst it1 - 16))]).
  assert (H4 : SPA segsA JI DIc0 rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE DIc0 rho3 tp _ _ eq_refl HST); [| exact (proj1 DIc0_vars) | exact (proj2 DIc0_vars) | exact H3].
    intros v Hv. cbn in Hv. destruct Hv as [<-|[]]. unfold NPRE, Pos.le; cbn; discriminate. }
  assert (OTH : forall i, i <> 198%positive -> rw rho4 i = rw rho i).
  { intros i N1. unfold rho4. rewrite rho_sets_other; [reflexivity|]. cbn. intros [X|[]]; congruence. }
  assert (ERM : rm rho4 = rm rho3) by (unfold rho4; apply rm_rho_sets).
  pose proof (D_pre_facts DIc0 _ (proj1 DIc_facts) rho4 (SPA_facts_hold segsA _ rho4 DIc0 tp _ H4)) as HF4.
  assert (HTOP4 : top_high A rho4) by (pose proof (be_top _ _ BE) as X; unfold top_high in *; rewrite !OTH by (unfold V_DEPTH; discriminate); exact X).
  assert (Ee : eval rho4 (add vS7 (SLit 8)) = Z_to_bv 64 (a + 152 + 8 * Z.of_nat (S nd))).
  { replace (a + 152 + 8 * Z.of_nat (S nd)) with (a + 152 + 8 * Z.of_nat nd + 8) by lia. apply (eval_add_lit A); try lia. unfold vS7. cbn [eval]. rewrite OTH by discriminate. exact E163. }
  assert (Cm : cell_ok (view segsA (rm rho3)) (mkACell (a + 24 + 8 * Z.of_nat (S nd)) 8 (fst it1 - 16))).
  { destruct HCB as (_ & _ & _ & _ & HSL). destruct (HSL 0%nat it1 eq_refl) as [C _]. cbn [Z.of_nat] in C. rewrite Z.add_0_r in C. exact C. }
  assert (H5 : SPA segsA JI (addo DIc0 (O_itg (add vS7 (SLit 8)))) rho4 tp (tr, mkCfg ms md)).
  { apply (carve_slot _ DIc0 rho4 tp _ (add vS7 (SLit 8)) (a + 152 + 8 * Z.of_nat (S nd)) (fst it1 - 16) H4 eq_refl DIc_swf Ee); try reflexivity; try lia.
    - rewrite ERM. replace (a + 152 + 8 * Z.of_nat (S nd) - 128) with (a + 24 + 8 * Z.of_nat (S nd)) by lia. exact Cm.
    - unfold DIc0. rewrite (proj1 DIc0_objs).
      pose proof (OBD_fixed A rho4 cb_cells (ob_cells (SWD vXK vXF vXL vXS)) HTOP4 HF4) as FX.
      eapply Forall_impl; [|exact FX]. intros o Ho. apply (fixed_clear rho4 (topG (aa_geom A)) o _ _ Ho); lia. }
  assert (H6 : SPA segsA JI DIc1 rho4 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H5 | exact DIc_below |]. intros HF. apply Forall_app. split; [exact HF|]. unfold FIc. repeat apply Forall_cons; try apply Forall_nil.
    cbn [holds]. rewrite Ee. change (eval rho4 (SLit (HIGH_SHADOW_END + 152))) with (Z_to_bv 64 (HIGH_SHADOW_END + 152)). rewrite !u64_lit by (unfold HIGH_SHADOW_END; lia).
    pose proof (batch_addr_facts A HTH rho3 _ BE ltac:(rewrite HGL; left; reflexivity)) as (_ & _ & _ & X & _). cbn [qb_addr] in X. unfold HIGH_SHADOW_END in *. lia. }
  destruct (entM_SPA _ _ DI MDIc rho4 tp _ DIc1_ent HST H6) as (H7 & AG7 & V7 & RM7).
  eexists. split; [exact H7|]. split; [|split].
  - unfold HVX. rewrite (V7 184%positive (SVar 184)), (V7 185%positive (SVar 185)), (V7 186%positive (SVar 186)), (V7 187%positive (SVar 187)), (V7 208%positive (SVar 208)) by (unfold MDIc; cbn; tauto).
    cbn [eval]. rewrite !OTH by discriminate. tauto.
  - unfold HVI. rewrite (V7 162%positive (SVar 162)), (V7 163%positive (add vS7 (SLit 8))), (V7 164%positive (add vS9 (SLit 1))), (V7 165%positive (SVar 198)), (V7 166%positive (SVar 166)) by (unfold MDIc; cbn; tauto).
    split; [cbn [eval]; rewrite OTH by discriminate; exact E162|]. split; [exact Ee|].
    split; [replace (16 + Z.of_nat (S nd)) with (16 + Z.of_nat nd + 1) by lia; apply (eval_add_lit A); try lia; unfold vS9; cbn [eval]; rewrite OTH by discriminate; exact E164|].
    split; [cbn [eval]; unfold rho4; reflexivity|]. cbn [eval]. rewrite OTH by discriminate. exact E166.
  - unfold HVS. rewrite RM7, ERM. exact Cm.
Qed.

Lemma dtc_glue : ltac2:(tb__ "0|5|
S13S39S39S39SeScS39S39A2M0S7S12A1M1G1S22S7S4aQ40M2A1M3A1S5bS0G1S16RbA1SaS12A1A3S0S6S14RcA1S9A3S39S73ReR1A2S73VA0;R2A2F_;Fz;S0G1S15ReA1S5S12S1aRdSaG0A1M4RcA3S8S12R8R7A3A3A3S40S3fS7aVK;VA0;Vrho0;RfReRcSfRbA1G4R9R8AaS7dR7R6R5A6S4eR8RaA2S63R9R10ReRdRcA5S64RaR11ReRdA4S2S22S22S1S40S3fS7aVK;VA0;Vrho0;R14R13R11SfR10A1G4ReRdAaS83R1RbRaA6S1S4eR1ReA2S0G3S24R1Pa6A2S4bG2R13A2A3A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it tmp' rest rho tp w HTH HCI HQW HGL H HVx HVi HVs. destruct w as [tr [ms md]].
  pose proof HVx as (E184 & E185 & E186 & E187 & E208). pose proof HVi as (E162 & E163 & E164 & E165 & E166).
  destruct (it_unobj DTc A a s n0 nd [] tmp' rest it rho tp tr ms md (proj2 DIc_objs) HTH HCI HQW HGL H HVi HVs) as (H3 & EV & BA1 & BA2 & BA3 & BA5 & HN0 & HN1).
  set (rho3 := rho_absorb rho [O_it] (vms md tp ms)) in *.
  set (JI := JRI K A0 rho0 A a n0 (S nd) [] tmp' rest) in *.
  pose proof (JRI_stable K HL A0 rho0 A a n0 (S nd) [] tmp' rest) as HST. fold JI in HST.
  destruct (batch_sb_facts A (mkQB a [] s) rho3 tp tr md HTH HCI (proj1 (proj2 H3)) ltac:(rewrite HGL; left; reflexivity)) as (E155 & SB0 & SB1 & SB2 & SB3). cbn [qb_addr] in SB2, SB3.
  assert (H6 : SPA segsA JI DTc1 rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact H3 | exact DTc_below |]. intros HF. apply Forall_app. split; [exact HF|]. unfold F_b24. repeat apply Forall_cons; try apply Forall_nil.
    - unfold vSB, vB. cbn [holds eval]. change (rw rho3) with (rw rho) in *. rewrite E155, E166, !u64_lit by lia. lia.
    - cbn [holds]. rewrite (eval_add_lit A rho3 vSB (ag_spacebeg (aa_geom A)) (2 ^ 37)) by (try lia; unfold vSB; cbn [eval]; exact E155).
      unfold vB. cbn [eval]. change (rw rho3) with (rw rho) in *. rewrite E166, !u64_lit by lia. lia. }
  destruct (entM_SPA _ _ DTs MDTc rho3 tp _ DTc1_ent HST H6) as (H7 & AG7 & V7 & RM7).
  assert (VV : forall v, In v [166; 184; 185; 186; 187; 208]%positive -> rw (rho_sub rho3 (infer_sub NPRE (ax_S DTc1) (ax_S DTs))) v = rw rho v).
  { intros v Hv. rewrite (V7 v (SVar v)); [reflexivity|]. unfold MDTc, idm. apply in_map_iff. exists v. split; [reflexivity | exact Hv]. }
  eexists. split; [exact H7|]. split.
  - unfold HVX. rewrite !VV by (cbn; tauto). tauto.
  - rewrite VV by (cbn; tauto). exact E166.
Qed.

End DSkel.
End SegQ3D_skel.

(* [comment removed for export] *)
Module CertCallocSV.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SAlu"; "SVar"; "sobj"; "sprop"; "mkObj"; "mkCell"; "cell"; "DUnknown"; "sv"; "SPBranch"; "DZero"; "SPNot"; "SPUle"; "sstate"; "ss_objs"; "mkSS"; "sprop_eqb"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "prod"; "app"; "true"; "pair"; "bool"; "list"; "option"; "length"; "negb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "ALU_SUB"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "kAllocBegMagic"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV.NX2"; "RUE"; "L3b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "sym_runA"; "ax_S"; "ax_setS"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "M48"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "rstS"; "BR"; "Bw"; "O_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV.NX3"; "a2e8"; "END8"; "B4"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_MS"; "V_NCH"; "V_PAB"; "O_errno"; "O_oom"; "O_san"; "V_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV"; "CPC"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_3"; "O_3b"; "O_4z"; "O_Mhi"; "O_Mlo"; "O_Pf9"; "O_fill"; "O_pxF"; "O_secgF"; "O_seciF"; "O_secmF"; "O_secsF"; "O_stF"; "PGST"; "a2e8"; "fx8"; "perm7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV.NX"; "L3"; "B3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV.NX4"; "UE9"; "BP9"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV.NX5"; "UBs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "kPtrArrayReserve"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Lists.List"; "existsb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymObj SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SecLog2 CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SecLog2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section NX.
Variable nx : positive.

Definition F_A : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS1S26S2Vnx;A1S2S42A1A3S2P9bA1A2S1bS4A1A3").
Definition F_B : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS1S26S2P9bA1S0S2fS30Z2Z25A2Z1000A2A1A3S2Vnx;A1A2S1bS4A1A3").

Definition B3 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S1S26S2Vnx;A1S0Z1000A1A3S0Z3A1A3S0Z7fff8000A1A3").
Definition a2e6 : sv := ltac2:(tb__ "0|2|
S1S29S1S26S1S27S1S26S2Vnx;A1M0S0Z17f8A1A3S0Z3A1M1A3S0Z1A1A3S1S27S1S26G0S0Z1000A1A3G1A3A3").
Definition L3 : sv := SLit 256.
Definition O_3 : sobj := ltac2:(tb__ "0|0|
S5S62S0Z0A1S61S1bS7A1S8A5").
Definition ru6 : list (nat * sv) := ltac2:(tb__ "0|1|
S1aS1dS1cS9A2M0S20S1cS9UcS61A4S1bG0A1A3").
End NX.

Definition rmF (f : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S34VE;A1SeS35VE;S10S17R1A1S18R1A1S14R1A1S13R1A1S19R1A1SfR1A1S6fS4S22S4A1S71S4A1S4S6dS25S6eS4S11R1A1Vf;A3A1M0A1Lp;S4S70G0A1Lx;S12R1A1A6S16R1A1S15R1A1A9A2TS;").
Definition runT6 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S33S3dUfa0S1aS2eS38S1bS2eA1A3VT;S1fA5").

Section NX2.
Variable nx : positive.
Definition RUE : sv := ltac2:(tb__ "0|0|
S1S28S1S26S1S26S1S26S2Vnx;A1S0Z1800A1A3S2PcA1A3S0Z7A1A3S0Zfffffffffffffff8A1A3").
Definition F_g7 : list sprop := ltac2:(tb__ "0|0|
S1aS4ScSaS2aS0Z7fffffffffffA1S31A3A1S1bS4A1A3").
Definition a0e7 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S31S0Z3A1A3S0Z7fff8000A1A3").
Definition a2e7 : sv := ltac2:(tb__ "0|1|
S1S29S1S26S1S27S1S26S1S26S31S1S26S1S29S1S26S2Vnx;A1S0Z1000A1A3S31A3S1S28S1S26S2S48A1S0ZfffA1A3S0Zfffffffffffff000A1A3A3A3S0N8A1A3S0Z3A1M0A3S0Z1A1A3S1S27S31G0A3A3").
Definition L3b : sv := SAlu ALU_ADD L2 (SLit 256).
Definition O_3n : sobj := ltac2:(tb__ "0|0|
S5S3aVnx;A1S0Z0A1S0Z100A1S1bS7A1S8A5").
Definition ru7 : list (nat * sv) := ltac2:(tb__ "0|1|
S1aS1dS1cS9A2M0S20S1cS9UaS3aVnx;A1A4S1aG0S20S1cS9UcS32A4S1bG0A1A3A3").
End NX2.
Definition U7p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S39VE;S1bS1dS1cS9A2A1S4cVnx;A1A3").

Definition perm7 (n : nat) : list nat := ltac2:(tb__ "0|1|
S1eS1cS1aS1cU0S1aS1cS41Vn;U1M0A2S1aS1cG0S1bS1cA1A3A3A3S65U2S41Vn;U3A2A2A3").
Definition sel7 (E : axst) : axst := ltac2:(tb__ "0|2|
S35VE;S68S34VE;A1M0S66SfG0A1M1S60S24S3G1A2A1A2A2A2").

Section NX3.
Variable nx : positive.
Definition END8 : sv := ltac2:(tb__ "0|0|
S1S26S1S26S1S26S2Vnx;A1S0Z1800A1A3S1S28S2PcA1S0S37A1A3A3S0N8A1A3").
Definition a2e8 : sv := ltac2:(tb__ "0|1|
S1S29S1S26S1S27S3fS0Z3A1M0A3S0Z1A1A3S1S27S1S26S2Vnx;A1S0Z1800A1A3G0A3A3").
Definition B4 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S1S26S2Vnx;A1S0Z1800A1A3S0Z3A1A3S0Z7fff8000A1A3").

Definition F_g8 : list sprop := ltac2:(tb__ "0|0|
S1aS4SaS2aS3eS0ZffffffffffffffffA1A3S1aS4ScSaS2aS0Z7fffffffffffA1S3fA3A1S1aS4ScSaS2bS1S28S2PcA1S0S37A1A3S0Z0A1A3A1S1bS4A1A3A3A3").

Definition fx8 : list sprop := ltac2:(tb__ "0|0|
S1aS4SdS3eS0Z4000000000000000A1A2S1bS4A1A3").
Definition O_3b : sobj := ltac2:(tb__ "0|0|
S5S3aVnx;A1S0Z0A1S4fS1bS7A1S8A5").
Definition O_4 : sobj := ltac2:(tb__ "0|0|
S5S40S0Z0A1S3eS1bS7A1S8A5").
End NX3.
Definition U8p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S39VE;S1bS1dS1cS9A2A1S4dVnx;A1A3").
Definition CT8p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S39VE;S1bS1dS1cS9A2A1S5fVnx;A1A3").

Section NX4.
Variable nx : positive.
Definition UE9 : sv := ltac2:(tb__ "0|0|
S1S26S1S26S2Vnx;A1S0Z1800A1A3S1S28S2PcA1S0S37A1A3A3").
Definition F_g9 : list sprop := ltac2:(tb__ "0|0|
S1aS4ScSaS2aS0Z7fffffffffffA1S63A3A1S1bS4A1A3").
Definition BP9 : sv := ltac2:(tb__ "0|0|
S1S26S1S27S63S0Z3A1A3S0Z7fff8000A1A3").
Definition O_4z : sobj := ltac2:(tb__ "0|0|
S5S4aVnx;A1S0Z0A1S5eVnx;A1S1bS7A1SbA5").
Definition O_P9 : sobj := ltac2:(tb__ "0|0|
S5S64S0Z0A1S0Z1A1S1bS7A1S8A5").
Definition F_par : sprop := ltac2:(tb__ "0|1|
SaS2bS2PcA1M0S1S28G0S0S37A1A3A3").
End NX4.
Definition U9p (nx : positive) (E : axst) : axst := ltac2:(tb__ "0|0|
S39VE;S1bS1dS1cS9A2A1S4eVnx;A1A3").
Definition PGST : Z := 0x3c728.
Definition CPC : Z := 0x3c8c0.
Definition runT9 (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S33S3dUfa0S1aS2eS49S1aS2eS5dS1bS2eA1A3A3VT;S1fA5").
Definition runT9q (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S33S3dUfa0S1aS2eS49S1bS2eA1A3VT;S1fA5").
Definition osplit (A : axst) (i : nat) (mid : sv) : axst := ltac2:(tb__ "0|0|
S23SeA1S36Lx;S67S34VA;A1Vi;Vmid;A3SeS35VA;R1A2LS';VA;X23x2").
Fixpoint find_map (nx : positive) (l : list sobj) (i : nat) : nat :=
  match l with [] => i | o :: t => if sv_eqb (ob_base o) (SVar nx) then i else find_map nx t (S i) end.
Definition runTF (T : axst) : option (list leafA) := ltac2:(tb__ "0|0|
S33S3dUfa0S1bS2eA1VT;S1fA5").

Section NX5.
Variable nx : positive.
Definition UBs : sv := ltac2:(tb__ "0|0|
S1S26S2Vnx;A1S0Z1800A1A3").
Definition O_fill : sobj := ltac2:(tb__ "0|0|
S5S2Vnx;A1S0Z1800A1S0Z2800A1S1bS7A1SbA5").
Definition O_Mlo (mc : list cell) : sobj := ltac2:(tb__ "0|0|
S5S2Vnx;A1S0Z0A1S0Z1800A1Vmc;SbA5").
Definition O_Mhi : sobj := ltac2:(tb__ "0|0|
S5S2Vnx;A1S0Z2800A1S2S42A1S1bS7A1SbA5").
Definition O_UBs : sobj := ltac2:(tb__ "0|0|
S5S69S0Z0A1S2PcA1S1bS7A1SbA5").
Definition mc_map : cell := ltac2:(tb__ "0|0|
S6S0Z0A1Z8S2Vnx;A1A3").
Definition mc_ms : cell := mkCell (SLit 8) 8 msx.
Definition mc_ns : cell := mkCell (SLit 16) 8 (SVar V_NS).
Definition mc_idx : cell := ltac2:(tb__ "0|0|
S6S0Z18A1Z8S2S43A1A3").
Definition mc_magic : cell := ltac2:(tb__ "0|0|
S6S0Z1000A1Z8S0S2dA1A3").
Definition mc_cptr : cell := ltac2:(tb__ "0|0|
S6S0Z1008A1Z8S1S26S2Vnx;A1S0Z17f0A1A3A3").
Definition mc_state : cell := mkCell (SLit 6128) 1 (SLit 2).
Definition mc_type (t : Z) : cell := mkCell (SLit 6129) 1 (SLit t).
Definition mc_sizehi : cell := ltac2:(tb__ "0|0|
S6S0Z17f2A1Z2S1S27S2PcA1S0Z20A1A3A3").
Definition mc_size : cell := mkCell (SLit 6132) 4 (SVar 12).
Definition O_Pf9 : sobj := ltac2:(tb__ "0|2|
S5S4bVnx;A1S0Z0A1M0S0Z1M1A1S1aS7S6G0G1S1S28S2PcA1S0Z7A1A3A3S1bS7A1A3S8A5").
Definition xc_map : cell := ltac2:(tb__ "0|0|
S6S0Z0A1Z8S2Vnx;A1A3").
End NX5.
Definition O_seciF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0S2cA1S0S2fS2cZ40A2A1Vc;S8A5").
Definition O_secsF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0S2fS2cZ40A2A1S0Zee040A1Vc;S8A5").
Definition O_secmF : sobj := ltac2:(tb__ "0|2|
S5S0Z0A1M0S0Zee040A1M1S0Zee044A1S1aS7S6G1Z1G0A3S1aS7S6S0Zee041A1Z3G0A3S1bS7A1A3A3S8A5").
Definition O_secgF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S0Z0A1S0Zee048A1S0Zee070A1Vc;S8A5").
Definition O_stF (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S6aS0Zad0A1S0Zc60A1Vc;S8A5").
Definition O_pxF (blk : Z) (d : odefault) (c : list cell) : sobj := ltac2:(tb__ "0|0|
S5S3bS0Z0A1S0Vblk;A1Vc;Vd;A5").
Definition ic_pg : cell := ltac2:(tb__ "0|0|
S6S0S2cA1Z8S0S6bA1A3").
Definition ic_c1 : cell := ltac2:(tb__ "0|1|
S6S0S2fS2cZ8M0A2A1G0S2S44A1A3").
Definition ic_c2 : cell := ltac2:(tb__ "0|0|
S6S0S2fS2cZ10A2A1Z8S2S44A1A3").
Definition ic_rs : cell := ltac2:(tb__ "0|0|
S6S0S2fS2cZ18A2A1Z8S0S6cA1A3").
Definition ic_nres (e : sv) : cell := ltac2:(tb__ "0|0|
S6S0S2fS2cZ30A2A1Z8Ve;A3").
Definition ic_nch : cell := ltac2:(tb__ "0|0|
S6S0S2fS2cZ38A2A1Z8S1S26S2S43A1S0Z1A1A3A3").
Definition RSF (nx : positive) (c1 c2 c4 c5 mc xc : list cell) (blk : Z) (dpx : odefault) (partial : bool) : list sobj := ltac2:(tb__ "0|1|
S1eS3S1aS3S56Vnx;A1S1aS3S52Vnx;A1S1aS3S51Vnx;A1S1aS3S50Vnx;A1S1aS3S3cVnx;A1S1bS3A1M0A3A3A3A3A3S1eS3S1aS3S59Vc1;A1S1aS3S5bVc2;A1S1aS3S5aS1aS3S58Vc4;A1S1aS3S47S1aS3S46S1aS3S45S1aS3S5cVc5;A1G0A3A3A3A3A3A3A3A3S1eS3S1aS3S54Vnx;Vmc;A2S1aS3S53Vnx;A1S1aS3S57Vblk;Vdpx;Vxc;A3G0A3A3A3S21S22S3A1Lpartial;Vpartial;S1aS3S55Vnx;A1G0A3G0X21x2A3A3A3").
End CertCallocSV.

