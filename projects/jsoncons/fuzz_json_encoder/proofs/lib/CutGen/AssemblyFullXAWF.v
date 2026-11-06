(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull LibIface IcptIfaceA L5Defs L5Core L5LazyA FPSteps
  Pm4PlanKit Pm4L5DefsA PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecsXA PmEncSpecsA PmEncSpecs2A PmFloatXSpecsA PmFloatXTuA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import Pm4CutKit CutHeapA CutL5A CutRtCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopKitXA TopSpecsXA HnKitXA XKitXA PmTopSpecsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibIfaceAW PmLibSpecsW PmRef PmRefXA PmLibSpecsXAW PmTopSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopAW Require Import TopSpecsAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require OpNewXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require OpDelXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require OpDelNullXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require GuardXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ErrHandlerXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SyscatXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require LocaleXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require LocaleDtorXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AtexitHandlerXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrPushBackXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrAppendXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrReserveXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrInitXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrAppendRangeXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AnnotateXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AnnotateNullXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require VecReserveXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require VecPushSlowXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require VecPushXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require VecDtorXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PopStateXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ParentXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm4StrtodOk.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require DecstrXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ParserDtorXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require DecU64XA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ValidateXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ConvertXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SetEcXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AtcXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require TceXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require XsgetnXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require DetectXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ReadChunkXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require IssCtorXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ReaderCtorXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ResetXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PcdXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require RCheckDoneXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SkipSpaceXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SkipWsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AfterValueXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require BeginMemberXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SourceDtorXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncPushBackXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncAppendXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncLiteralsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncToCodepointXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncNewLineFXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncBeginScalarFXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncEscapeXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncWriteBignumXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncWriteStringXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm4StrtodG.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require DecstrGXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FloatXA Require SnprintfCpsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require DumpBufXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require PrettifyXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require DtoaFalseXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require DtoaTrueXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require FromIntU64XA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require FromIntI64XA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require WriteDoubleClosedXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncNewLine2FXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require AnnotateCtxXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PushFastNXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PushSlowXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PushFastRXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitNullFXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitBoolFXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitU64FXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitI64FXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitStrFXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitKeyFXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXA Require VisitDoubleClosedXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitBeginFXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitEndFXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require WidenXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require EncCtorXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require EncDtorXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HnKitXA2 HnGlueXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopAW Require XsgetnXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopAW Require DetectXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopAW Require ReadChunkXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmParseAsmXAW Require ParseAsmXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopAW Require ReadXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HarnessAsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HarnessAlXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HarnessBsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HarnessBlXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require LibTopXAW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ASMFXAWF.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.
Abbreviation IC := PMLA.C_xasan.
Abbreviation EC := PMESA.EC_xasan.
Abbreviation VIS := XKA.VIS.
Abbreviation VISD := XKA.VISD.
Section A.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL : icpt_layout.
(* [comment removed for export] *)
Variable CL : Z.
Variable onmax : Z.
Definition enc_invA := PMESA.enc_invA L IC EC.
Definition benc := PMESA.benc L CL.
Definition eroomA := PMESA.eroomA CL.
(* [comment removed for export] *)
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis FOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a.
Hypothesis FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis FOOTXC : forall a, PMLA.in_footx IC a -> ~ hl_rt_static L a.
Hypothesis TPV : hl_tp L = 6938576.
Hypothesis ISH : rt_img_shadow L IL HI.
Hypothesis ANN : aannotate_spec L ar SCFG HI 540712 4096.
Hypothesis FN : HeapIfaceANull.afree_null_spec L ar SCFG HI.
(* [comment removed for export] *)
Hypothesis POI_VTT : Forall (fun r : Z * Z => 1420200 + 16 <= fst r \/ snd r <= 1420200) (icl_poison IL).
Hypothesis POI_VBO : Forall (fun r : Z * Z => 1420120 + 8 <= fst r \/ snd r <= 1420120) (icl_poison IL).
Hypothesis POI_ISS : Forall (fun r : Z * Z => 1435760 + 8 <= fst r \/ snd r <= 1435760) (icl_poison IL).      (* [comment removed for export] *)
(* [comment removed for export] *)
Variable PAT : Z.
Hypothesis PATR : 65536 <= PAT /\ PAT + 8 <= 1449984.
Hypothesis SF5 : PmHeapIfaceA.astack_free_spec L ar SCFG HI 419988 PAT 5.
Hypothesis SETSH00 : aset_shadow_spec L ar SCFG HI 540080 0 256.
Hypothesis SETSHF8 : aset_shadow_spec L ar SCFG HI 540368 248 256.
Hypothesis POI_HN : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) [1435840; 1435864; 1435760]) (icl_poison IL).
(* [comment removed for export] *)
Hypothesis SETSHF5 : aset_shadow_spec L ar SCFG HI 540344 245 256.
Hypothesis POI_EC5 : Forall (fun r : Z * Z => Forall (fun an : Z * Z => fst an + snd an <= fst r \/ snd r <= fst an) EncCtorXA.ISHRG5) (icl_poison IL).   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis RTG : rt_globals IL HI.
Hypothesis GLIN : Forall (fun g : Z * Z => In g (icl_globals IL)) EncCtorXA.ECGLOBS.
(* [comment removed for export] *)
Hypothesis FOOTXC2 : forall a, PMLA.in_footx IC a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis CLOKX : EncKitA.EKA.clok CL onmax.
Hypothesis CL40 : CL <= 2 ^ 40.                             (* [comment removed for export] *)
Hypothesis ACC_NULL : PMESA.img_aacc HI 154272 4.           (* [comment removed for export] *)
Hypothesis ACC_TRUE : PMESA.img_aacc HI 165024 4.           (* [comment removed for export] *)
Hypothesis ACC_FALSE : PMESA.img_aacc HI 165056 5.          (* [comment removed for export] *)
Hypothesis ACC_COLON : PMESA.img_aacc HI 150292 2.          (* [comment removed for export] *)
Hypothesis ACC_COMMA : PMESA.img_aacc HI 150300 2.          (* [comment removed for export] *)
Hypothesis ACC_OBRACE : PMESA.img_aacc HI 150312 1.         (* [comment removed for export] *)
Hypothesis ACC_CBRACE : PMESA.img_aacc HI 150313 1.         (* [comment removed for export] *)
Hypothesis ACC_OBRACKET : PMESA.img_aacc HI 150318 1.       (* [comment removed for export] *)
Hypothesis ACC_CBRACKET : PMESA.img_aacc HI 150319 1.       (* [comment removed for export] *)
Hypothesis POI_TC : Forall (fun r : Z * Z => 151376 + 288 <= fst r \/ snd r <= 151376) (icl_poison IL).     (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis SM0 : hl_stack_malloc L 0 = 0x65e70.
Hypothesis SM1 : hl_stack_malloc L 1 = 0x65fe4.
Hypothesis SM2 : hl_stack_malloc L 2 = 0x66174.
Hypothesis SM3 : hl_stack_malloc L 3 = 0x66310.
Hypothesis SM4 : hl_stack_malloc L 4 = 0x664bc.
Hypothesis MEMSET_LIBC : CRC.amemset_spec_at L ar HI 0x80234.
Hypothesis MEMCPY_LIBC : amemcpy_spec_at L ar SCFG HI 0x8023c false.
Hypothesis MEMMOVE_LIBC : amemcpy_spec_at L ar SCFG HI 0x80238 false.
Hypothesis MEMCMP_TU : amemcmp_spec_at L ar SCFG HI 0x6b930 8192.
Hypothesis POI_MS : Forall (fun r : Z * Z => 0x69cf28 <= fst r \/ snd r <= 0x69ce38) (icl_poison IL).
Hypothesis POI_RO : Forall (fun r : Z * Z => 0x306a8 <= fst r \/ snd r <= 0x30678) (icl_poison IL).
(* [comment removed for export] *)
Definition VTSLOTS : list Z := [1420344; 1420352; 1420360; 1420368; 1420376; 1420384; 1420400; 1420408; 1420416; 1420424; 1420432; 1420440;
                               1421176; 1421336; 1421344; 1421360; 1421632; 1421640; 1421648; 1421656; 1421672; 1421688; 1421696; 1421704; 1421712; 1421720; 1421728;
                               1435608; 1435760; 1435840; 1435864].
Hypothesis POI_VT : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) VTSLOTS) (icl_poison IL).
Hypothesis POI_IOS32 : Forall (fun r : Z * Z => 1435880 <= fst r \/ snd r <= 1435848) (icl_poison IL).
Hypothesis POI_BOM : Forall (fun r : Z * Z => 165614 <= fst r \/ snd r <= 165598) (icl_poison IL).
Hypothesis POI_DTAB : Forall (fun r : Z * Z => 165728 + 256 <= fst r \/ snd r <= 165728) (icl_poison IL).   (* [comment removed for export] *)
(* [comment removed for export] *)
Variable ILX : icpt_layout_x.
Hypothesis ICok : pm_aicpt_ok L ar IL ILX SCFG HI (aannotate_spec L ar SCFG HI (iclx_annotate ILX) 4096).
Hypothesis CXA_PC : iclx_cxa_atexit ILX = 440824.
Hypothesis CXA_SCR : 0 <= iclx_scr_cxa ILX <= 512.
Hypothesis CXA_TAB : iclx_atexit_tab ILX = PMLA.ATEXIT_TAB IC.
Hypothesis CXA_AT : iclx_atcxa ILX = PMLA.ATCXA_HANDLER IC.
Hypothesis CXA_NL : iclx_need_locks ILX = PMLA.NEED_LOCKS IC.
(* [comment removed for export] *)
Lemma FPMH : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Proof. rewrite (L5A.aly_segs L C LAY). exact FPM. Qed.
(* [comment removed for export] *)
Lemma POIV : forall a, existsb (Z.eqb a) VTSLOTS = true -> Forall (fun r : Z * Z => a + 8 <= fst r \/ snd r <= a) (icl_poison IL).
Proof.
  intros a Ha. apply existsb_exists in Ha as (b & Hb & E). apply Z.eqb_eq in E. subst b.
  eapply Forall_impl; [|exact POI_VT]. cbv beta. intros r Hr. exact (proj1 (Forall_forall _ _) Hr a Hb).
Qed.
Lemma POIL : forall l, forallb (fun a => existsb (Z.eqb a) VTSLOTS) l = true -> Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) l) (icl_poison IL).
Proof.
  intros l Hl. rewrite forallb_forall in Hl. eapply Forall_impl; [|exact POI_VT]. cbv beta. intros r Hr. apply Forall_forall. intros a Ha.
  pose proof (Hl a Ha) as Hx. apply existsb_exists in Hx as (b & Hb & E). apply Z.eqb_eq in E. subst b. exact (proj1 (Forall_forall _ _) Hr a Hb).
Qed.
Lemma POI_TC264 : Forall (fun r : Z * Z => 151376 + 264 <= fst r \/ snd r <= 151376) (icl_poison IL).
Proof. eapply Forall_impl; [|exact POI_TC]. cbv beta. intros r Hr. lia. Qed.
Create HintDb asmrows discriminated.
(* [comment removed for export] *)
Hypothesis FLA : DecIfaceA.PDCA.float_layoutA L DecIfaceA.PDCA.xasan.                                                        (* [comment removed for export] *)
Hypothesis GLT : In (G3PureXA.PT_BASE, 8 * 687) (icl_globals IL).                                         (* [comment removed for export] *)
Hypothesis GLE : In (G3PureXA.PE_BASE, 4 * 687) (icl_globals IL).
Hypothesis RSD : rt_shadow_defined HI.                                                                     (* [comment removed for export] *)
Hypothesis SNCELLS : incl SnprintfCpsXA.SNA_CELLS (asc_cells C).                                           (* [comment removed for export] *)
Hypothesis ILG_FMT : In (SnprintfCpsXA.FMT_ADDR, 6) (icl_globals IL).                                      (* [comment removed for export] *)
Hypothesis POI_SNP : Forall (fun r : Z * Z => 147584 <= fst r \/ snd r <= 81856) (icl_poison IL).        (* [comment removed for export] *)
Lemma F_LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Proof. rewrite (L5A.aly_img_lo L C LAY), (L5A.aly_img_hi L C LAY). unfold BIGSHADOW_LO. lia. Qed.
Lemma F_LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Proof. intros a Ha. rewrite (L5A.aly_img_lo L C LAY), (L5A.aly_img_hi L C LAY). exact (L5A.aly_ro_img L C LAY a Ha). Qed.
Lemma F_LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Proof. rewrite (L5A.aly_segs L C LAY), (L5A.aly_img_hi L C LAY). exact L5A.segs_below. Qed.
Lemma F_LYN : wx_segs_nowrap (hl_segs L).
Proof. rewrite (L5A.aly_segs L C LAY). exact L5A.wx_nowrap. Qed.
Lemma F_LS : hl_segs L = Pm4PlanKit.RSEGS. Proof. exact (L5A.aly_segs L C LAY). Qed.
Lemma F_ILO : hl_img_lo L = 65536. Proof. exact (L5A.aly_img_lo L C LAY). Qed.
Lemma F_IHI : hl_img_hi L = 7077888. Proof. exact (L5A.aly_img_hi L C LAY). Qed.
#[local] Hint Resolve F_LYI F_LYR F_LYB F_LYN F_LS F_ILO F_IHI : asmrows.

Ltac plug := first [ eassumption | solve [eauto 1 with asmrows nocore] | exact FPM | exact FPMH | exact F_LYR | exact F_LYI | exact F_LYB | exact F_LYN | exact F_LS | exact F_ILO | exact F_IHI | reflexivity | (split; reflexivity) | exact XKA.lits_inside_xasan | exact POI_TC264
                   | (apply POIV; vm_compute; reflexivity) | (apply POIL; vm_compute; reflexivity)
                   | (pose proof (L5A.aly_cost L C LAY); lia) | match goal with |- ?G => idtac "OPENPREMISE" G; fail end ].

(* [comment removed for export] *)
Definition CLW : Z := CL.            (* [comment removed for export] *)
Hypothesis CLOK : TPSXAW.clokP CLW.
Variable PHI : list byte -> Prop.
Hypothesis PHIW : TPSXAW.phiwP PHI.
(* [comment removed for export] *)
Hypothesis ERRNO_NS : forall a, 6938412 <= a < 6938412 + 4 -> ~ hl_rt_static L a.
Lemma ROOMW : PMXAW.roomwP eroomA CLW. Proof. exact (fun _ _ H => H). Qed.

(* [comment removed for export] *)
Hypothesis LOCFIRST : PMSA.locale_ctor_first_specA L ar HI IC 1212420.   (* [comment removed for export] *)
Hypothesis OPNEWX : PMESA.opnew_x_specA L ar HI onmax 1414360.   (* [comment removed for export] *)
Hypothesis MEMCPY_X : PMESA.amemcpy_x_spec_at L ar HI onmax 524860 false.   (* [comment removed for export] *)
Hypothesis MEMMOVE_X : PMESA.amemcpy_x_spec_at L ar HI onmax 524856 false.   (* [comment removed for export] *)
(* [comment removed for export] *)
Record open_contracts : Prop := OC {

}.
Hypothesis OPEN : open_contracts.

(* [comment removed for export] *)
Lemma OPNEW : PMSA.opnew_specA L ar HI 1414360.
Proof. eapply OpNewXA.opnew_ok; plug. Qed.
#[local] Hint Resolve OPNEW : asmrows.
(* [comment removed for export] *)
Lemma OPDEL : PMSA.opdel_specA L ar HI 1031544.
Proof. eapply OpDelXA.opdel_ok; plug. Qed.
#[local] Hint Resolve OPDEL : asmrows.
(* [comment removed for export] *)
Lemma OPDELS : PMSA.opdel_specA L ar HI 1031548.
Proof. eapply OpDelXA.opdel_sized_ok; plug. Qed.
#[local] Hint Resolve OPDELS : asmrows.
(* [comment removed for export] *)
Lemma OPDELNULL : PMSA.opdel_null_specA L ar HI 1031544.
Proof. eapply OpDelNullXA.opdel_null_ok; plug. Qed.
#[local] Hint Resolve OPDELNULL : asmrows.
(* [comment removed for export] *)
Lemma GUARD_ACQ : PMSA.guard_acquire_specA L ar HI 914508.
Proof. eapply GuardXA.guard_acquire_ok; plug. Qed.
#[local] Hint Resolve GUARD_ACQ : asmrows.
(* [comment removed for export] *)
Lemma GUARD_REL : PMSA.guard_release_specA L ar HI 914588.
Proof. eapply GuardXA.guard_release_ok; plug. Qed.
#[local] Hint Resolve GUARD_REL : asmrows.
(* [comment removed for export] *)
Lemma ERRH : PMSA.errh_specA L ar HI 836392.
Proof. eapply ErrHandlerXA.errh_ok; plug. Qed.
#[local] Hint Resolve ERRH : asmrows.
(* [comment removed for export] *)
Lemma SYSCAT : PMSA.system_category_specA L ar HI IC 1058428.
Proof. eapply SyscatXA.system_category_ok; plug. Qed.
#[local] Hint Resolve SYSCAT : asmrows.
(* [comment removed for export] *)
Lemma LOCLATER : PMSA.locale_ctor_later_specA L ar HI IC 1212420.
Proof. eapply LocaleXA.locale_ctor_later_ok; plug. Qed.
#[local] Hint Resolve LOCLATER : asmrows.
(* [comment removed for export] *)
Lemma LOCDTOR : PMSA.locale_dtor_specA L ar HI IC 1212636.
Proof. eapply LocaleDtorXA.locale_dtor_ok; plug. Qed.
#[local] Hint Resolve LOCDTOR : asmrows.
(* [comment removed for export] *)
Lemma ATEXIT_HANDLER : forall ILX : icpt_layout_x, PMSA.atexit_handler_specA L ar HI IC ILX.
Proof. eapply AtexitHandlerXA.atexit_handler_ok; plug. Qed.
#[local] Hint Resolve ATEXIT_HANDLER : asmrows.
(* [comment removed for export] *)
Lemma STRPUSHBACK : PMSA.str_push_back_specA L ar HI 1041292.
Proof. eapply StrPushBackXA.str_push_back_ok; plug. Qed.
#[local] Hint Resolve STRPUSHBACK : asmrows.
(* [comment removed for export] *)
Lemma STRAPPEND : PMSA.str_append_specA L ar HI 1040708.
Proof. eapply StrAppendXA.str_append_ok; plug. Qed.
#[local] Hint Resolve STRAPPEND : asmrows.
(* [comment removed for export] *)
Lemma STRRSV : PMSA.str_reserve_specA L ar HI 1040164.
Proof. eapply StrReserveXA.str_reserve_ok; plug. Qed.
#[local] Hint Resolve STRRSV : asmrows.
(* [comment removed for export] *)
Lemma STRINIT : PMSA.strinit_specA L ar HI 724956.
Proof. eapply StrInitXA.strinit_ok; plug. Qed.
#[local] Hint Resolve STRINIT : asmrows.
(* [comment removed for export] *)
Lemma STRAPPENDRANGE : PMSA.str_append_range_specA L ar HI 911564.
Proof. eapply StrAppendRangeXA.str_append_range_ok; plug. Qed.
#[local] Hint Resolve STRAPPENDRANGE : asmrows.
(* [comment removed for export] *)
Lemma ANN_INC : PMSA.annotate_increase_spec L ar HI 842060.
Proof. eapply AnnotateXA.annotate_increase_ok; plug. Qed.
#[local] Hint Resolve ANN_INC : asmrows.
(* [comment removed for export] *)
Lemma ANN_SHR : PMSA.annotate_shrink_spec L ar HI 730684.
Proof. eapply AnnotateXA.annotate_shrink_ok; plug. Qed.
#[local] Hint Resolve ANN_SHR : asmrows.
(* [comment removed for export] *)
Lemma ANN_NEW : PMSA.annotate_new_spec L ar HI 841184.
Proof. eapply AnnotateXA.annotate_new_ok; plug. Qed.
#[local] Hint Resolve ANN_NEW : asmrows.
(* [comment removed for export] *)
Lemma ANN_DEL : PMSA.annotate_delete_spec L ar HI 730524.
Proof. eapply AnnotateXA.annotate_delete_ok; plug. Qed.
#[local] Hint Resolve ANN_DEL : asmrows.
(* [comment removed for export] *)
Lemma ANN_DELNULL : PMSA.annotate_delete_null_spec L ar HI 730524.
Proof. eapply AnnotateNullXA.annotate_delete_null_ok; plug. Qed.
#[local] Hint Resolve ANN_DELNULL : asmrows.
(* [comment removed for export] *)
Lemma VRSV : PMSA.vec_reserve_specA L ar HI 840148.
Proof. eapply VecReserveXA.vec_reserve_ok; plug. Qed.
#[local] Hint Resolve VRSV : asmrows.
(* [comment removed for export] *)
Lemma VPUSHSLOW : PMSA.vec_push_slow_spec L ar HI 841580.
Proof. eapply VecPushSlowXA.vec_push_slow_ok; plug. Qed.
#[local] Hint Resolve VPUSHSLOW : asmrows.
(* [comment removed for export] *)
Lemma VPUSH : PMSA.vec_push_specA L ar HI 841320.
Proof. eapply VecPushXA.vec_push_ok; plug. Qed.
#[local] Hint Resolve VPUSH : asmrows.
(* [comment removed for export] *)
Lemma VDTOR : PMSA.vec_dtor_specA L ar HI 730236.
Proof. eapply VecDtorXA.vec_dtor_ok; plug. Qed.
#[local] Hint Resolve VDTOR : asmrows.
(* [comment removed for export] *)
Lemma POPSTATE : PMSA.pop_state_specA L ar HI 878496.
Proof. eapply PopStateXA.pop_state_ok; plug. Qed.
#[local] Hint Resolve POPSTATE : asmrows.
(* [comment removed for export] *)
Lemma PARENT : PMSA.parent_specA L ar HI 899700.
Proof. eapply ParentXA.parent_ok; plug. Qed.
#[local] Hint Resolve PARENT : asmrows.
(* [comment removed for export] *)
Lemma STRTOD : PMSA.strtod_specA L ar HI IC 1383752.
Proof. eapply Pm4StrtodOk.STOA.strtod_okA; plug. Qed.
#[local] Hint Resolve STRTOD : asmrows.
(* [comment removed for export] *)
Lemma DECSTR : PMSA.decstr_to_double_specA L ar HI IC 824664.
Proof. eapply DecstrXA.decstr_ok; plug. Qed.
#[local] Hint Resolve DECSTR : asmrows.
(* [comment removed for export] *)
Lemma PDTOR : PMSA.parser_dtor_specA L ar HI IC 729216.
Proof. eapply ParserDtorXA.parser_dtor_ok; plug. Qed.
#[local] Hint Resolve PDTOR : asmrows.
(* [comment removed for export] *)
Lemma DECU64 : PMSA.dec_u64_specA L ar HI IC 904392.
Proof. eapply DecU64XA.dec_u64_ok; plug. Qed.
#[local] Hint Resolve DECU64 : asmrows.
(* [comment removed for export] *)
Lemma VALIDATE : PMSA.validate_specA L ar HI IC 909212.
Proof. eapply ValidateXA.validate_ok; plug. Qed.
#[local] Hint Resolve VALIDATE : asmrows.
(* [comment removed for export] *)
Lemma CONVERT : PMSA.convert_specA L ar HI 908744.
Proof. eapply ConvertXA.convert_ok; plug. Qed.
#[local] Hint Resolve CONVERT : asmrows.
(* [comment removed for export] *)
Lemma SETEC : PMSA.set_ec_specA L ar HI IC 827600.
Proof. eapply SetEcXA.set_ec_ok; plug. Qed.
#[local] Hint Resolve SETEC : asmrows.
(* [comment removed for export] *)
Lemma ATC : PMSA.append_to_codepoint_specA L ar HI IC 908076.
Proof. eapply AtcXA.atc_ok; plug. Qed.
#[local] Hint Resolve ATC : asmrows.
(* [comment removed for export] *)
Lemma TCE : PMSA.translate_conv_errc_specA L ar HI IC 910144.
Proof. eapply TceXA.tce_ok; plug. Qed.
#[local] Hint Resolve TCE : asmrows.
(* [comment removed for export] *)
Lemma XSGETN : TPSA.xsgetn_specA L ar HI IC 1063324.
Proof. eapply XsgetnXA.xsgetn_ok; plug. Qed.
#[local] Hint Resolve XSGETN : asmrows.
(* [comment removed for export] *)
Lemma DETECT : TPSA.detect_json_specA L ar HI IC 846264.
Proof. eapply DetectXA.detect_json_ok; plug. Qed.
#[local] Hint Resolve DETECT : asmrows.
(* [comment removed for export] *)
Lemma READCHUNK : TPSA.read_chunk_specA L ar HI IC 844856.
Proof. eapply ReadChunkXA.read_chunk_ok; plug. Qed.
#[local] Hint Resolve READCHUNK : asmrows.
(* [comment removed for export] *)
Lemma ISS : PMSA.iss_ctor_specA L ar HI IC 725300.
Proof. eapply IssCtorXA.iss_ctor_ok; plug. Qed.
#[local] Hint Resolve ISS : asmrows.
(* [comment removed for export] *)
Lemma ISSX : HNK.iss_ctor_specX L ar HI IC 725300.
Proof. eapply IssCtorXA.iss_ctor_okX; plug. Qed.
#[local] Hint Resolve ISSX : asmrows.
(* [comment removed for export] *)
Lemma RCTOR : PMSA.reader_ctor_specA L ar HI IC 727172.
Proof. eapply ReaderCtorXA.reader_ctor_ok; plug. Qed.
#[local] Hint Resolve RCTOR : asmrows.
(* [comment removed for export] *)
Lemma RESET : TPSA.reset_specA L ar HI IC 844500.
Proof. eapply ResetXA.reset_ok; plug. Qed.
#[local] Hint Resolve RESET : asmrows.
(* [comment removed for export] *)
Lemma PCD : PMSA.parser_check_done_specA L ar HI IC 913528.
Proof. eapply PcdXA.parser_check_done_ok; plug. Qed.
#[local] Hint Resolve PCD : asmrows.
(* [comment removed for export] *)
Lemma RCDONE : TPSA.rcheck_done_specA L ar HI IC 843556.
Proof. eapply RCheckDoneXA.rcheck_done_ok; plug. Qed.
#[local] Hint Resolve RCDONE : asmrows.
(* [comment removed for export] *)
Lemma SKIPSPACE : PMSA.skip_space_specA L ar HI IC 879392.
Proof. eapply SkipSpaceXA.skip_space_ok; plug. Qed.
#[local] Hint Resolve SKIPSPACE : asmrows.
(* [comment removed for export] *)
Lemma SKIPWS : PMSA.skip_whitespace_specA L ar HI IC 845264.
Proof. eapply SkipWsXA.skip_whitespace_ok; plug. Qed.
#[local] Hint Resolve SKIPWS : asmrows.
(* [comment removed for export] *)
Lemma AFTERVALUE : PMSA.after_value_specA L ar HI IC 903708.
Proof. eapply AfterValueXA.after_value_ok; plug. Qed.
#[local] Hint Resolve AFTERVALUE : asmrows.
(* [comment removed for export] *)
Lemma BEGINMEMBER : PMSA.begin_member_specA L ar HI IC 899016.
Proof. eapply BeginMemberXA.begin_member_ok; plug. Qed.
#[local] Hint Resolve BEGINMEMBER : asmrows.
(* [comment removed for export] *)
Lemma SDTOR : PMSA.source_dtor_specA L ar HI IC 730848.
Proof. eapply SourceDtorXA.source_dtor_ok; plug. Qed.
#[local] Hint Resolve SDTOR : asmrows.
(* [comment removed for export] *)
Lemma STRPUSHBACKX : PMESA.str_push_back_x_specA L ar HI CL 1041292.
Proof. pose proof (L5A.aly_cost L C LAY) as (K0 & LIN0 & OVH0). exact (EncPushBackXA.EPBA.str_push_back_x_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) K0 LIN0 OVH0 CL onmax CLOKX OPNEWX OPDEL MEMMOVE_X). Qed.
#[local] Hint Resolve STRPUSHBACKX : asmrows.
(* [comment removed for export] *)
Lemma STRAPPENDX : PMESA.str_append_x_specA L ar HI IC CL 1040708.
Proof. pose proof (L5A.aly_cost L C LAY) as (K0 & LIN0 & OVH0). exact (EncAppendXA.EAPA.str_append_x_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) K0 LIN0 OVH0 CL onmax CLOKX OPNEWX OPDEL MEMMOVE_X MEMCPY_X). Qed.
#[local] Hint Resolve STRAPPENDX : asmrows.
(* [comment removed for export] *)
Lemma NULL_LIT : PMESA.null_literal_specA L ar HI IC 770528.
Proof. exact (EncLiteralsXA.ELTNA.null_literal_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) GUARD_ACQ GUARD_REL). Qed.
#[local] Hint Resolve NULL_LIT : asmrows.
(* [comment removed for export] *)
Lemma TRUE_LIT : PMESA.true_literal_specA L ar HI IC 832876.
Proof. exact (EncLiteralsXA.ELTTA.true_literal_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) GUARD_ACQ GUARD_REL). Qed.
#[local] Hint Resolve TRUE_LIT : asmrows.
(* [comment removed for export] *)
Lemma FALSE_LIT : PMESA.false_literal_specA L ar HI IC 832992.
Proof. exact (EncLiteralsXA.ELTFA.false_literal_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) GUARD_ACQ GUARD_REL). Qed.
#[local] Hint Resolve FALSE_LIT : asmrows.
(* [comment removed for export] *)
Lemma TOCP : PMESA.to_codepoint_specA L ar HI IC 809452.
Proof. exact (EncToCodepointXA.to_codepoint_ok L ar C HI IL HIok LAY ISH POI_TC ltac:(first [exact FPM | exact FPMH])). Qed.
#[local] Hint Resolve TOCP : asmrows.
(* [comment removed for export] *)
Lemma NEWLINE : PMESA.new_line_specA L ar HI IC EC CL 763924.
Proof. exact (EncNewLineFXA.ENLFA.new_line_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL STRAPPENDX STRPUSHBACKX). Qed.
#[local] Hint Resolve NEWLINE : asmrows.
(* [comment removed for export] *)
Lemma BEGINSCALAR : PMESA.begin_scalar_specA L ar HI IC EC CL 765616.
Proof. exact (EncBeginScalarFXA.EBFA.begin_scalar_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ACC_COMMA CL STRAPPENDX NEWLINE). Qed.
#[local] Hint Resolve BEGINSCALAR : asmrows.
(* [comment removed for export] *)
Lemma ESCAPE : PMESA.escape_string_specA L ar HI IC CL 777944.
Proof. exact (EncEscapeXA.EESX.escape_string_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL CL40 STRPUSHBACKX TOCP). Qed.
#[local] Hint Resolve ESCAPE : asmrows.
(* [comment removed for export] *)
Lemma WRITEBIGNUM : PMESA.write_bignum_specA L ar HI IC EC CL 774832.
Proof. exact (EncWriteBignumXA.write_bignum_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL STRAPPENDX SETSHF5). Qed.
#[local] Hint Resolve WRITEBIGNUM : asmrows.
(* [comment removed for export] *)
Lemma WRITESTRING : PMESA.write_string_specA L ar HI IC EC CL 769828.
Proof. exact (EncWriteStringXA.write_string_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL STRPUSHBACKX STRAPPENDX ESCAPE WRITEBIGNUM). Qed.
#[local] Hint Resolve WRITESTRING : asmrows.
(* [comment removed for export] *)
Lemma STRTODG : PMFXA.strtod_g_specA L ar HI IC 1383752.
Proof. eapply Pm4StrtodG.STGA.strtod_g_okA; plug. Qed.
#[local] Hint Resolve STRTODG : asmrows.
(* [comment removed for export] *)
Lemma DECSTRG : PMFXA.decstr_to_double_g_specA L ar HI IC 824664.
Proof. eapply DecstrGXA.decstr_g_ok; plug. Qed.
#[local] Hint Resolve DECSTRG : asmrows.
(* [comment removed for export] *)
Lemma SNPRINTFG : PMFXA.snprintf_g_specA L ar HI IC PMFXA.PC_SNPRINTF_xasan 154496.
Proof. eapply SnprintfCpsXA.snprintf_g_okA; plug. Qed.
#[local] Hint Resolve SNPRINTFG : asmrows.
(* [comment removed for export] *)
Lemma DUMPBUF : PMFXTA.dump_buffer_x_specA L ar HI IC CL 815348.
Proof. eapply DumpBufXA.dump_buffer_x_ok; plug. Qed.
#[local] Hint Resolve DUMPBUF : asmrows.
(* [comment removed for export] *)
Lemma PRETTIFY : PMFXTA.prettify_x_specA L ar HI IC CL 819012.
Proof. eapply PrettifyXA.prettify_x_ok; plug. Qed.
#[local] Hint Resolve PRETTIFY : asmrows.
(* [comment removed for export] *)
Lemma DTOAF : PMFXTA.dtoa_false_x_specA L ar HI IC CL 826584.
Proof. eapply DtoaFalseXA.dtoa_false_x_ok; plug. Qed.
#[local] Hint Resolve DTOAF : asmrows.
(* [comment removed for export] *)
Lemma DTOAT : PMFXTA.dtoa_true_x_specA L ar HI IC CL 825600.
Proof. eapply DtoaTrueXA.dtoa_true_x_ok; plug. Qed.
#[local] Hint Resolve DTOAT : asmrows.
(* [comment removed for export] *)
Lemma FROMU : PMESA.from_integer_x_specA L ar HI IC CL 766156.
Proof. eapply FromIntU64XA.from_integer_u64_x_ok; plug. Qed.
#[local] Hint Resolve FROMU : asmrows.
(* [comment removed for export] *)
Lemma FROMI : PMESA.from_integer_x_specA L ar HI IC CL 767788.
Proof. eapply FromIntI64XA.from_integer_i64_x_ok; plug. Qed.
#[local] Hint Resolve FROMI : asmrows.
(* [comment removed for export] *)
Lemma WDOUBLE : PMESA.write_double_x_specA L ar HI IC PMFXA.WD_SCR_XA CL 772144.
Proof. eapply WriteDoubleClosedXA.WDCA.write_double_closed; plug. Qed.
#[local] Hint Resolve WDOUBLE : asmrows.
(* [comment removed for export] *)
Lemma NEWLINE2 : PMESA.new_line2_specA L ar HI IC CL 763924.
Proof. exact (EncNewLine2FXA.ENL2FA.new_line2_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL STRAPPENDX STRPUSHBACKX). Qed.
#[local] Hint Resolve NEWLINE2 : asmrows.
(* [comment removed for export] *)
Lemma ANNCTX : PMES2A.annotate_shrink_ctx_specA L ar HI 763296.
Proof. exact (AnnotateCtxXA.annotate_shrink_ctx_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ANN). Qed.
#[local] Hint Resolve ANNCTX : asmrows.
(* [comment removed for export] *)
Lemma PUSHFAST_A : PMES2A.push_fast_specA L ar HI 829116.
Proof. exact (PushFastNXA.push_fast_nested_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ANN). Qed.
#[local] Hint Resolve PUSHFAST_A : asmrows.
(* [comment removed for export] *)
Lemma PUSHSLOW_A : PMES2A.push_slow_specA L ar HI onmax 829116.
Proof. exact (PushSlowXA.push_slow_nested_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) onmax OPNEWX ANN OPDEL). Qed.
#[local] Hint Resolve PUSHSLOW_A : asmrows.
(* [comment removed for export] *)
Lemma PUSHFAST_B : PMES2A.push_fast_specA L ar HI 827820.
Proof. exact (PushFastRXA.push_fast_root_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ANN). Qed.
#[local] Hint Resolve PUSHFAST_B : asmrows.
(* [comment removed for export] *)
Lemma PUSHSLOW_B : PMES2A.push_slow_specA L ar HI onmax 827820.
Proof. exact (PushSlowXA.push_slow_root_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) onmax OPNEWX ANN OPDEL). Qed.
#[local] Hint Resolve PUSHSLOW_B : asmrows.
(* [comment removed for export] *)
Lemma VNULL_E : PMESA.visit_null_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 751316.
Proof. exact (EncVisitNullFXA.EVNFA.visit_null_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ACC_NULL FOOTXC2 CL BEGINSCALAR NULL_LIT STRAPPENDX). Qed.
#[local] Hint Resolve VNULL_E : asmrows.
(* [comment removed for export] *)
Lemma VBOOL_E : PMESA.visit_bool_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 751920.
Proof. exact (EncVisitBoolFXA.EVBFA.visit_bool_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ACC_TRUE ACC_FALSE FOOTXC2 CL BEGINSCALAR TRUE_LIT FALSE_LIT STRAPPENDX). Qed.
#[local] Hint Resolve VBOOL_E : asmrows.
(* [comment removed for export] *)
Lemma VU64_E : PMESA.visit_uint64_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 738876.
Proof. exact (EncVisitU64FXA.EVUFA.visit_uint64_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) FOOTXC2 CL BEGINSCALAR FROMU). Qed.
#[local] Hint Resolve VU64_E : asmrows.
(* [comment removed for export] *)
Lemma VI64_E : PMESA.visit_int64_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 739428.
Proof. exact (EncVisitI64FXA.EVIFA.visit_int64_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) FOOTXC2 CL BEGINSCALAR FROMI). Qed.
#[local] Hint Resolve VI64_E : asmrows.
(* [comment removed for export] *)
Lemma VSTR_E : PMESA.visit_string_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 752584.
Proof. exact (EncVisitStrFXA.EVSFA.visit_string_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) FOOTXC2 CL BEGINSCALAR WRITESTRING). Qed.
#[local] Hint Resolve VSTR_E : asmrows.
(* [comment removed for export] *)
Lemma VKEY_E : PMESA.visit_key_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 749552.
Proof. exact (EncVisitKeyFXA.EVKFA.visit_key_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL ACC_COMMA ACC_COLON FOOTXC2 NEWLINE2 STRAPPENDX STRPUSHBACKX ESCAPE). Qed.
#[local] Hint Resolve VKEY_E : asmrows.
(* [comment removed for export] *)
Lemma VDBL_E : PMESA.visit_double_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 739980.
Proof. eapply VisitDoubleClosedXA.VDCA.visit_double_closed; plug. Qed.
#[local] Hint Resolve VDBL_E : asmrows.
(* [comment removed for export] *)
Lemma VBOBJ_E : PMESA.visit_begin_object_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 744592.
Proof. exact (EncVisitBeginFXA.EVBGA.visit_begin_object_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL onmax IL ACC_OBRACE ACC_COMMA ISH POI_VBO FOOTXC2 NEWLINE2 STRAPPENDX CLOKX PUSHFAST_A PUSHSLOW_A PUSHFAST_B PUSHSLOW_B). Qed.
#[local] Hint Resolve VBOBJ_E : asmrows.
(* [comment removed for export] *)
Lemma VBARR_E : PMESA.visit_begin_array_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 747704.
Proof. exact (EncVisitBeginFXA.EVBGA.visit_begin_array_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL onmax IL ACC_OBRACKET ACC_COMMA ISH POI_VBO FOOTXC2 NEWLINE2 STRAPPENDX CLOKX PUSHFAST_A PUSHSLOW_A PUSHFAST_B PUSHSLOW_B). Qed.
#[local] Hint Resolve VBARR_E : asmrows.
(* [comment removed for export] *)
Lemma VEOBJ_E : PMESA.visit_end_object_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 746348.
Proof. exact (EncVisitEndFXA.EVEFA.visit_end_object_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL ACC_CBRACE FOOTXC2 NEWLINE2 ANNCTX STRAPPENDX). Qed.
#[local] Hint Resolve VEOBJ_E : asmrows.
(* [comment removed for export] *)
Lemma VEARR_E : PMESA.visit_end_array_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 737520.
Proof. exact (EncVisitEndFXA.EVEFA.visit_end_array_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL ACC_CBRACKET FOOTXC2 NEWLINE2 ANNCTX STRAPPENDX). Qed.
#[local] Hint Resolve VEARR_E : asmrows.
(* [comment removed for export] *)
Lemma VNULL : PMXA.visit_null_specXA L ar HI IC enc_invA VIS VISD benc eroomA 751316.
Proof. exact (WidenXA.WDXA.visit_null_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VNULL_E). Qed.
#[local] Hint Resolve VNULL : asmrows.
(* [comment removed for export] *)
Lemma VBOOL : PMXA.visit_bool_specXA L ar HI IC enc_invA VIS VISD benc eroomA 751920.
Proof. exact (WidenXA.WDXA.visit_bool_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VBOOL_E). Qed.
#[local] Hint Resolve VBOOL : asmrows.
(* [comment removed for export] *)
Lemma VU64 : PMXA.visit_uint64_specXA L ar HI IC enc_invA VIS VISD benc eroomA 738876.
Proof. exact (WidenXA.WDXA.visit_uint64_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VU64_E). Qed.
#[local] Hint Resolve VU64 : asmrows.
(* [comment removed for export] *)
Lemma VI64 : PMXA.visit_int64_specXA L ar HI IC enc_invA VIS VISD benc eroomA 739428.
Proof. exact (WidenXA.WDXA.visit_int64_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VI64_E). Qed.
#[local] Hint Resolve VI64 : asmrows.
(* [comment removed for export] *)
Lemma VSTR : PMXA.visit_string_specXA L ar HI IC enc_invA VIS VISD benc eroomA 752584.
Proof. exact (WidenXA.WDXA.visit_string_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VSTR_E). Qed.
#[local] Hint Resolve VSTR : asmrows.
(* [comment removed for export] *)
Lemma VKEY : PMXA.visit_key_specXA L ar HI IC enc_invA VIS VISD benc eroomA 749552.
Proof. exact (WidenXA.WDXA.visit_key_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VKEY_E). Qed.
#[local] Hint Resolve VKEY : asmrows.
(* [comment removed for export] *)
Lemma VDBL : PMXA.visit_double_specXA L ar HI IC enc_invA VIS VISD benc eroomA 739980.
Proof. exact (WidenXA.WDXA.visit_double_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VDBL_E). Qed.
#[local] Hint Resolve VDBL : asmrows.
(* [comment removed for export] *)
Lemma VBOBJ : PMXA.visit_begin_object_specXA L ar HI IC enc_invA VIS VISD benc eroomA 744592.
Proof. exact (WidenXA.WDXA.visit_begin_object_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VBOBJ_E). Qed.
#[local] Hint Resolve VBOBJ : asmrows.
(* [comment removed for export] *)
Lemma VBARR : PMXA.visit_begin_array_specXA L ar HI IC enc_invA VIS VISD benc eroomA 747704.
Proof. exact (WidenXA.WDXA.visit_begin_array_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VBARR_E). Qed.
#[local] Hint Resolve VBARR : asmrows.
(* [comment removed for export] *)
Lemma VEOBJ : PMXA.visit_end_object_specXA L ar HI IC enc_invA VIS VISD benc eroomA 746348.
Proof. exact (WidenXA.WDXA.visit_end_object_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VEOBJ_E). Qed.
#[local] Hint Resolve VEOBJ : asmrows.
(* [comment removed for export] *)
Lemma VEARR : PMXA.visit_end_array_specXA L ar HI IC enc_invA VIS VISD benc eroomA 737520.
Proof. exact (WidenXA.WDXA.visit_end_array_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXA.WDXA.wdle_12800 WidenXA.WDXA.wd8_12800 _ VEARR_E). Qed.
#[local] Hint Resolve VEARR : asmrows.
(* [comment removed for export] *)
Lemma ENC_AGREE : PMXA.enc_agreeP enc_invA.
Proof. exact (EncKitA.EKA.enc_agree_ok L IC EC). Qed.
#[local] Hint Resolve ENC_AGREE : asmrows.
(* [comment removed for export] *)
Lemma ENC_CTOR : TPSXA.enc_ctor_specXA L ar HI IC enc_invA 725968.
Proof. exact (EncCtorXA.enc_ctor_ok L ar C HI IL EC HIok LAY ltac:(first [exact FPM | exact FPMH]) SETSHF5 ISH POI_EC5 RTG GLIN eq_refl). Qed.
#[local] Hint Resolve ENC_CTOR : asmrows.
(* [comment removed for export] *)
Lemma ENC_DTOR : TPSXA.enc_dtor_specXA L ar HI IC enc_invA 728724.
Proof. exact (EncDtorXA.enc_dtor_ok L ar C HI IL EC HIok LAY ltac:(first [exact FPM | exact FPMH]) ANN OPDEL ISH POI_VTT POI_VBO). Qed.
#[local] Hint Resolve ENC_DTOR : asmrows.
(* [comment removed for export] *)
Lemma ENC_AGREE_NS : HnKitXA2.HK2.enc_agree_nsP enc_invA.
Proof. exact (HnGlueXA.HGX.enc_agree_ns_ok L IC EC). Qed.
#[local] Hint Resolve ENC_AGREE_NS : asmrows.
(* [comment removed for export] *)
Lemma ENC_VIS : forall (M : PMSA.mem) V S2 g, enc_invA M V S2 g -> PMSA.vis_at L IC M V.
Proof. exact (HnGlueXA.HGX.enc_vis_ok L IC EC). Qed.
#[local] Hint Resolve ENC_VIS : asmrows.
(* [comment removed for export] *)
Lemma BENC0 : PMXA.bencP benc.
Proof. pose proof (L5A.aly_cost L C LAY) as (_ & LIN0 & OVH0). exact (EncKitA.EKA.benc_nonneg L CL LIN0 OVH0). Qed.
#[local] Hint Resolve BENC0 : asmrows.
(* [comment removed for export] *)
Lemma XSGETNW : TPSAW.xsgetn_specAW L ar HI IC 1063324.
Proof. eapply XsgetnXAW.xsgetn_okw; plug. Qed.
#[local] Hint Resolve XSGETNW : asmrows.
(* [comment removed for export] *)
Lemma DETECTW : TPSAW.detect_json_specAW L ar HI IC 846264.
Proof. eapply DetectXAW.detect_json_okw; plug. Qed.
#[local] Hint Resolve DETECTW : asmrows.
(* [comment removed for export] *)
Lemma RCHUNKW : TPSAW.read_chunk_specAW L ar HI IC 844856.
Proof. eapply ReadChunkXAW.read_chunk_okw; plug. Qed.
#[local] Hint Resolve RCHUNKW : asmrows.
(* [comment removed for export] *)
Lemma PSOMEXW : PMXAW.parse_some_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW 847680.
Proof. exact (ParseAsmXAW.parse_some_okw_lib L ar C HI IL CLW enc_invA benc eroomA HIok LAY FPM FOOTC FOOTXC ISH TPV POI_VT POI_DTAB POI_TC SM0 SM1 SM4 SETSHF5 ERRNO_NS ERRH SETEC STRPUSHBACK STRAPPEND STRAPPENDRANGE VPUSH POPSTATE PARENT DECSTR DECU64 TCE ENC_AGREE BENC0 ROOMW VNULL VBOOL VU64 VI64 VSTR VKEY VDBL VBOBJ VBARR VEOBJ VEARR). Qed.
#[local] Hint Resolve PSOMEXW : asmrows.
(* [comment removed for export] *)
Lemma READXAW : TPSXAW.read_specXAW L ar HI IC enc_invA VIS VISD benc CLW 728576.
Proof. exact (ReadXAW.read_xaw_ok L ar C HI IL HIok LAY FPM FOOTXC enc_invA benc ENC_AGREE XKA.lits_inside_xasan TPV ISH POI_ISS RESET CLW RCHUNKW PSOMEXW SKIPWS SETEC RCDONE). Qed.
#[local] Hint Resolve READXAW : asmrows.
(* [comment removed for export] *)
Lemma HASW : TPSXAW.harness_chainXAW L ar HI IC benc 722256 0 false.
Proof. exact (HarnessAsXAW.harness_as_okw L ar C HI IL HIok LAY FPM FOOTC FOOTC2 FOOTXC enc_invA benc ENC_AGREE_NS BENC0 XKA.lits_inside_xasan ENC_VIS PAT PATR SF5 SETSH00 SETSHF8 STRINIT ISSX RCTOR SYSCAT CLW CLOK READXAW ENC_CTOR ENC_DTOR PDTOR SDTOR LOCDTOR OPDEL FN TPV ISH POI_HN). Qed.
#[local] Hint Resolve HASW : asmrows.
(* [comment removed for export] *)
Lemma HALW : TPSXAW.harness_chainXAW L ar HI IC benc 722256 0 true.
Proof. exact (HarnessAlXAW.harness_al_okw L ar C HI IL HIok LAY FPM FOOTC FOOTC2 FOOTXC enc_invA benc ENC_AGREE_NS BENC0 XKA.lits_inside_xasan ENC_VIS PAT PATR SF5 SETSH00 SETSHF8 STRINIT ISSX RCTOR SYSCAT CLW CLOK READXAW ENC_CTOR ENC_DTOR PDTOR SDTOR LOCDTOR OPDEL FN TPV ISH POI_HN). Qed.
#[local] Hint Resolve HALW : asmrows.
(* [comment removed for export] *)
Lemma HBSW : TPSXAW.harness_chainXAW L ar HI IC benc 722256 16 false.
Proof. exact (HarnessBsXAW.harness_bs_okw L ar C HI IL HIok LAY FPM FOOTC FOOTC2 FOOTXC enc_invA benc ENC_AGREE_NS BENC0 XKA.lits_inside_xasan ENC_VIS PAT PATR SF5 SETSH00 SETSHF8 STRINIT ISSX RCTOR SYSCAT CLW CLOK READXAW ENC_CTOR ENC_DTOR PDTOR SDTOR LOCDTOR OPDEL FN TPV ISH POI_HN). Qed.
#[local] Hint Resolve HBSW : asmrows.
(* [comment removed for export] *)
Lemma HBLW : TPSXAW.harness_chainXAW L ar HI IC benc 722256 16 true.
Proof. exact (HarnessBlXAW.harness_bl_okw L ar C HI IL HIok LAY FPM FOOTC FOOTC2 FOOTXC enc_invA benc ENC_AGREE_NS BENC0 XKA.lits_inside_xasan ENC_VIS PAT PATR SF5 SETSH00 SETSHF8 STRINIT ISSX RCTOR SYSCAT CLW CLOK READXAW ENC_CTOR ENC_DTOR PDTOR SDTOR LOCDTOR OPDEL FN TPV ISH POI_HN). Qed.
#[local] Hint Resolve HBLW : asmrows.
(* [comment removed for export] *)
Lemma LIBTOPXAW : forall Lay, TPSXA.pm_layout_okxA L IC VIS benc Lay -> lla_stack Lay = TPSXA.HARN_SCRXA -> lla_entry Lay = 722256 -> lla_empty Lay = TPSXA.EMPTY_X -> PmLibIfaceAW.lib_call_okAW Lay ar SCFG HI (TPSXA.pm_staticsxA L IC) PHI.
Proof. exact (LibTopXAW.LTXAW.lib_call_okw L ar C HI VIS benc HIok TPV PHI PHIW HASW HALW HBSW HBLW). Qed.
#[local] Hint Resolve LIBTOPXAW : asmrows.

Theorem lib_ok_xaw_full : forall Lay, lla_stack Lay = TPSXA.HARN_SCRXA -> lla_entry Lay = 722256 -> lla_empty Lay = TPSXA.EMPTY_X -> TPSXAW.lib_specxAW L ar HI IC VIS benc PHI Lay.
Proof. intros Lay H1 H2 H3 LOK. exact (LIBTOPXAW Lay LOK H1 H2 H3). Qed.
End A.
End ASMFXAWF.
