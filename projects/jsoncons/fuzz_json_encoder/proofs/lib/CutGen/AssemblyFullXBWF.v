(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull LibIface IcptIfaceA L5Defs L5Core L5LazyA FPSteps
  Pm5PlanKit Pm5L5DefsA PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecsXA PmEncSpecsA PmEncSpecs2A PmFloatXSpecsA PmFloatXTuA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import Pm5CutKit CutHeapA CutL5A CutRtCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopKitA TopSpecsXB HnKitXB XKitXA PmTopSpecsXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import HnKitXB2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PmLibSpecsBLocal.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibIfaceAW PmLibSpecsW PmRef PmRefXA PmLibSpecsXAW PmTopSpecsXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require Import TopSpecsBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require OpNewXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require OpDelXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require OpDelNullXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require GuardXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ErrHandlerXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SyscatXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require LocaleXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require LocaleDtorXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AtexitHandlerXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrPushBackXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrAppendXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrReserveXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrInitXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require StrAppendRangeXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AnnotateXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AnnotateNullXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require VecReserveXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require VecPushSlowXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require VecPushXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require VecDtorXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PopStateXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ParentXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm5StrtodOk.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require DecstrXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ParserDtorXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require DecU64XB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ValidateXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ConvertXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SetEcXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AtcXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require TceXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require XsgetnXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require DetectXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ReadChunkXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require IssCtorXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ReaderCtorXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require ResetXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PcdXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require RCheckDoneXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SkipSpaceXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SkipWsXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require AfterValueXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require BeginMemberXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require SourceDtorXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncPushBackXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncAppendXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncLiteralsXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncToCodepointXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncNewLineFXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncBeginScalarFXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncEscapeXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncWriteBignumXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncWriteStringXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm5StrtodG.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require DecstrGXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FloatXB Require SnprintfCpsXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require DumpBufXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require PrettifyXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require DtoaFalseXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require DtoaTrueXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require FromIntU64XB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require FromIntI64XB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require WriteDoubleClosedXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncNewLine2FXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require AnnotateCtxXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PushFastRXB PushFastNXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PushSlowXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PushFastRXB PushFastNXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitNullFXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitBoolFXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitU64FXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitI64FXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitStrFXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitKeyFXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatXB Require VisitDoubleClosedXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitBeginFXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncVisitEndFXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require WidenXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require EncKitXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require EncCtorXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require EncDtorXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HnKitXB2 HnGlueXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require XsgetnXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require DetectXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require ReadChunkXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require ParseAsmXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require ReadXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HarnessAsXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HarnessAlXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HarnessBsXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require HarnessBlXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require LibTopXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require ReadXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require PcdXB16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module ASMFXBWF.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.
Abbreviation IC := PMLA.C_xboth.
Abbreviation EC := PMESA.EC_xboth.
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
Hypothesis TPV : hl_tp L = 6953104.
Hypothesis ISH : rt_img_shadow L IL HI.
Hypothesis ANN : aannotate_spec L ar SCFG HI 542968 4096.
Hypothesis FN : HeapIfaceANull.afree_null_spec L ar SCFG HI.
(* [comment removed for export] *)
Hypothesis POI_VTT : Forall (fun r : Z * Z => 1435080 + 16 <= fst r \/ snd r <= 1435080) (icl_poison IL).
Hypothesis POI_VBO : Forall (fun r : Z * Z => 1435000 + 8 <= fst r \/ snd r <= 1435000) (icl_poison IL).
Hypothesis POI_ISS : Forall (fun r : Z * Z => 1450352 + 8 <= fst r \/ snd r <= 1450352) (icl_poison IL).      (* [comment removed for export] *)
(* [comment removed for export] *)
Variable PAT : Z.
Hypothesis PATR : 65536 <= PAT /\ PAT + 8 <= 1466368.
Hypothesis SF5 : PmHeapIfaceA.astack_free_spec L ar SCFG HI 422244 PAT 5.
Hypothesis SETSH00 : aset_shadow_spec L ar SCFG HI 542336 0 256.
Hypothesis SETSHF8 : aset_shadow_spec L ar SCFG HI 542624 248 256.
Hypothesis POI_HN : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) [1450432; 1450456; 1450352]) (icl_poison IL).
(* [comment removed for export] *)
Hypothesis SETSHF5 : aset_shadow_spec L ar SCFG HI 542600 245 256.
Hypothesis POI_EC5 : Forall (fun r : Z * Z => Forall (fun an : Z * Z => fst an + snd an <= fst r \/ snd r <= fst an) EncCtorXB.ISHRG5) (icl_poison IL).   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis RTG : rt_globals IL HI.
Hypothesis GLIN : Forall (fun g : Z * Z => In g (icl_globals IL)) EncCtorXB.ECGLOBS.
(* [comment removed for export] *)
Hypothesis FOOTXC2 : forall a, PMLA.in_footx IC a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis CLOKX : EncKitXB.EKA.clok CL onmax.
Hypothesis CL40 : CL <= 2 ^ 40.                             (* [comment removed for export] *)
Hypothesis ACC_NULL : PMESA.img_aacc HI 154688 4.           (* [comment removed for export] *)
Hypothesis ACC_TRUE : PMESA.img_aacc HI 165440 4.           (* [comment removed for export] *)
Hypothesis ACC_FALSE : PMESA.img_aacc HI 165472 5.          (* [comment removed for export] *)
Hypothesis ACC_COLON : PMESA.img_aacc HI 150388 2.          (* [comment removed for export] *)
Hypothesis ACC_COMMA : PMESA.img_aacc HI 150396 2.          (* [comment removed for export] *)
Hypothesis ACC_OBRACE : PMESA.img_aacc HI 150408 1.         (* [comment removed for export] *)
Hypothesis ACC_CBRACE : PMESA.img_aacc HI 150409 1.         (* [comment removed for export] *)
Hypothesis ACC_OBRACKET : PMESA.img_aacc HI 150414 1.       (* [comment removed for export] *)
Hypothesis ACC_CBRACKET : PMESA.img_aacc HI 150415 1.       (* [comment removed for export] *)
Hypothesis POI_TC : Forall (fun r : Z * Z => 151792 + 288 <= fst r \/ snd r <= 151792) (icl_poison IL).     (* [comment removed for export] *)
Hypothesis POI_CV : Forall (fun r : Z * Z => 166496 + 8 <= fst r \/ snd r <= 166496) (icl_poison IL).     (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis SM0 : hl_stack_malloc L 0 = 0x66740.
Hypothesis SM1 : hl_stack_malloc L 1 = 0x668b4.
Hypothesis SM2 : hl_stack_malloc L 2 = 0x66a44.
Hypothesis SM3 : hl_stack_malloc L 3 = 0x66be0.
Hypothesis SM4 : hl_stack_malloc L 4 = 0x66d8c.
Hypothesis MEMSET_LIBC : CRC.amemset_spec_at L ar HI 0x80b04.
Hypothesis MEMCPY_LIBC : amemcpy_spec_at L ar SCFG HI 0x80b0c false.
Hypothesis MEMMOVE_LIBC : amemcpy_spec_at L ar SCFG HI 0x80b08 false.
Hypothesis MEMCMP_TU : amemcmp_spec_at L ar SCFG HI 0x6c200 8192.
Hypothesis POI_MS : Forall (fun r : Z * Z => 0x6a07e8 <= fst r \/ snd r <= 0x6a06f8) (icl_poison IL).
Hypothesis POI_RO : Forall (fun r : Z * Z => 0x30868 <= fst r \/ snd r <= 0x30838) (icl_poison IL).
(* [comment removed for export] *)
Definition VTSLOTS : list Z := [1435224; 1435232; 1435240; 1435248; 1435256; 1435264; 1435280; 1435288; 1435296; 1435304; 1435312; 1435320;
                               1436056; 1436216; 1436224; 1436240; 1436512; 1436520; 1436528; 1436536; 1436552; 1436568; 1436576; 1436584; 1436592; 1436600; 1436608;
                               1450200; 1450352; 1450432; 1450456].
Hypothesis POI_VT : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) VTSLOTS) (icl_poison IL).
Hypothesis POI_IOS32 : Forall (fun r : Z * Z => 1450472 <= fst r \/ snd r <= 1450440) (icl_poison IL).
Hypothesis POI_BOM : Forall (fun r : Z * Z => 166030 <= fst r \/ snd r <= 166014) (icl_poison IL).       (* [comment removed for export] *)
Hypothesis POI_DTAB : Forall (fun r : Z * Z => 166144 + 256 <= fst r \/ snd r <= 166144) (icl_poison IL).   (* [comment removed for export] *)
(* [comment removed for export] *)
Variable ILX : icpt_layout_x.
Hypothesis ICok : pm_aicpt_ok L ar IL ILX SCFG HI (aannotate_spec L ar SCFG HI (iclx_annotate ILX) 4096).
Hypothesis CXA_PC : iclx_cxa_atexit ILX = 443080.
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
Lemma POI_TC264 : Forall (fun r : Z * Z => 151792 + 264 <= fst r \/ snd r <= 151792) (icl_poison IL).
Proof. eapply Forall_impl; [|exact POI_TC]. cbv beta. intros r Hr. lia. Qed.
Create HintDb asmrows discriminated.
(* [comment removed for export] *)
Hypothesis FLA : DecIfaceA.PDCA.float_layoutA L DecIfaceA.PDCA.xboth.                                                        (* [comment removed for export] *)
Hypothesis GLT : In (G3PureXB.PT_BASE, 8 * 687) (icl_globals IL).                                         (* [comment removed for export] *)
Hypothesis GLE : In (G3PureXB.PE_BASE, 4 * 687) (icl_globals IL).
Hypothesis RSD : rt_shadow_defined HI.                                                                     (* [comment removed for export] *)
Hypothesis SNCELLS : incl SnprintfCpsXB.SNA_CELLS (asc_cells C).                                           (* [comment removed for export] *)
Hypothesis ILG_FMT : In (SnprintfCpsXB.FMT_ADDR, 6) (icl_globals IL).                                      (* [comment removed for export] *)
Hypothesis POI_SNP : Forall (fun r : Z * Z => 147584 <= fst r \/ snd r <= 77760) (icl_poison IL).        (* [comment removed for export] *)
Lemma F_LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Proof. rewrite (L5A.aly_img_lo L C LAY), (L5A.aly_img_hi L C LAY). unfold BIGSHADOW_LO. lia. Qed.
Lemma F_LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Proof. intros a Ha. rewrite (L5A.aly_img_lo L C LAY), (L5A.aly_img_hi L C LAY). exact (L5A.aly_ro_img L C LAY a Ha). Qed.
Lemma F_LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Proof. rewrite (L5A.aly_segs L C LAY), (L5A.aly_img_hi L C LAY). exact L5A.segs_below. Qed.
Lemma F_LYN : wx_segs_nowrap (hl_segs L).
Proof. rewrite (L5A.aly_segs L C LAY). exact L5A.wx_nowrap. Qed.
Lemma F_LS : hl_segs L = Pm5PlanKit.RSEGS. Proof. exact (L5A.aly_segs L C LAY). Qed.
Lemma F_ILO : hl_img_lo L = 65536. Proof. exact (L5A.aly_img_lo L C LAY). Qed.
Lemma F_IHI : hl_img_hi L = 7094272. Proof. exact (L5A.aly_img_hi L C LAY). Qed.
#[local] Hint Resolve F_LYI F_LYR F_LYB F_LYN F_LS F_ILO F_IHI : asmrows.

Ltac plug := first [ eassumption | solve [eauto 1 with asmrows nocore] | exact FPM | exact FPMH | exact F_LYR | exact F_LYI | exact F_LYB | exact F_LYN | exact F_LS | exact F_ILO | exact F_IHI | reflexivity | (split; reflexivity) | exact XKA.lits_inside_xboth | exact POI_TC264
                   | (apply POIV; vm_compute; reflexivity) | (apply POIL; vm_compute; reflexivity)
                   | (pose proof (L5A.aly_cost L C LAY); lia) | match goal with |- ?G => idtac "OPENPREMISE" G; fail end ].

(* [comment removed for export] *)
Definition CLW : Z := CL.            (* [comment removed for export] *)
Hypothesis CLOK : TPSXAW.clokP CLW.
Variable PHI : list byte -> Prop.
Hypothesis PHIW : TPSXAW.phiwP PHI.
(* [comment removed for export] *)
Hypothesis ERRNO_NS : forall a, 6952940 <= a < 6952940 + 4 -> ~ hl_rt_static L a.
Lemma ROOMW : PMXAW.roomwP eroomA CLW. Proof. exact (fun _ _ H => H). Qed.

(* [comment removed for export] *)
Hypothesis LOCFIRST : PMSA.locale_ctor_first_specA L ar HI IC 1227132.   (* [comment removed for export] *)
Hypothesis OPNEWX : PMESA.opnew_x_specA L ar HI onmax 1429232.   (* [comment removed for export] *)
Hypothesis MEMCPY_X : PMESA.amemcpy_x_spec_at L ar HI onmax 527116 false.   (* [comment removed for export] *)
Hypothesis MEMMOVE_X : PMESA.amemcpy_x_spec_at L ar HI onmax 527112 false.   (* [comment removed for export] *)
(* [comment removed for export] *)
Record open_contracts : Prop := OC {

}.
Hypothesis OPEN : open_contracts.

(* [comment removed for export] *)
Lemma OPNEW : PMSA.opnew_specA L ar HI 1429232.
Proof. eapply OpNewXB.opnew_ok; plug. Qed.
#[local] Hint Resolve OPNEW : asmrows.
(* [comment removed for export] *)
Lemma OPDEL : PMSA.opdel_specA L ar HI 1046256.
Proof. eapply OpDelXB.opdel_ok; plug. Qed.
#[local] Hint Resolve OPDEL : asmrows.
(* [comment removed for export] *)
Lemma OPDELS : PMSA.opdel_specA L ar HI 1046260.
Proof. eapply OpDelXB.opdel_sized_ok; plug. Qed.
#[local] Hint Resolve OPDELS : asmrows.
(* [comment removed for export] *)
Lemma OPDELNULL : PMSA.opdel_null_specA L ar HI 1046256.
Proof. eapply OpDelNullXB.opdel_null_ok; plug. Qed.
#[local] Hint Resolve OPDELNULL : asmrows.
(* [comment removed for export] *)
Lemma GUARD_ACQ : PMSA.guard_acquire_specA L ar HI 929220.
Proof. eapply GuardXB.guard_acquire_ok; plug. Qed.
#[local] Hint Resolve GUARD_ACQ : asmrows.
(* [comment removed for export] *)
Lemma GUARD_REL : PMSA.guard_release_specA L ar HI 929300.
Proof. eapply GuardXB.guard_release_ok; plug. Qed.
#[local] Hint Resolve GUARD_REL : asmrows.
(* [comment removed for export] *)
Lemma ERRH : PMSA.errh_specA L ar HI 852452.
Proof. eapply ErrHandlerXB.errh_ok; plug. Qed.
#[local] Hint Resolve ERRH : asmrows.
(* [comment removed for export] *)
Lemma SYSCAT : PMSA.system_category_specA L ar HI IC 1073140.
Proof. eapply SyscatXB.system_category_ok; plug. Qed.
#[local] Hint Resolve SYSCAT : asmrows.
(* [comment removed for export] *)
Lemma LOCLATER : PMSA.locale_ctor_later_specA L ar HI IC 1227132.
Proof. eapply LocaleXB.locale_ctor_later_ok; plug. Qed.
#[local] Hint Resolve LOCLATER : asmrows.
(* [comment removed for export] *)
Lemma LOCDTOR : PMSA.locale_dtor_specA L ar HI IC 1227348.
Proof. eapply LocaleDtorXB.locale_dtor_ok; plug. Qed.
#[local] Hint Resolve LOCDTOR : asmrows.
(* [comment removed for export] *)
Lemma ATEXIT_HANDLER : forall ILX : icpt_layout_x, PMSA.atexit_handler_specA L ar HI IC ILX.
Proof. eapply AtexitHandlerXB.atexit_handler_ok; plug. Qed.
#[local] Hint Resolve ATEXIT_HANDLER : asmrows.
(* [comment removed for export] *)
Lemma STRPUSHBACK : PMSA.str_push_back_specA L ar HI 1056004.
Proof. eapply StrPushBackXB.str_push_back_ok; plug. Qed.
#[local] Hint Resolve STRPUSHBACK : asmrows.
(* [comment removed for export] *)
Lemma STRAPPEND : PMSA.str_append_specA L ar HI 1055420.
Proof. eapply StrAppendXB.str_append_ok; plug. Qed.
#[local] Hint Resolve STRAPPEND : asmrows.
(* [comment removed for export] *)
Lemma STRRSV : PMSA.str_reserve_specA L ar HI 1054876.
Proof. eapply StrReserveXB.str_reserve_ok; plug. Qed.
#[local] Hint Resolve STRRSV : asmrows.
(* [comment removed for export] *)
Lemma STRINIT : PMSA.strinit_specA L ar HI 727212.
Proof. eapply StrInitXB.strinit_ok; plug. Qed.
#[local] Hint Resolve STRINIT : asmrows.
(* [comment removed for export] *)
Lemma STRAPPENDRANGE : PMSA.str_append_range_specA L ar HI 926224.
Proof. eapply StrAppendRangeXB.str_append_range_ok; plug. Qed.
#[local] Hint Resolve STRAPPENDRANGE : asmrows.
(* [comment removed for export] *)
Lemma ANN_INC : PmLibSpecsBLocal.PMSB.annotate_increase_spec L ar HI 859068.
Proof. eapply AnnotateXB.annotate_increase_ok; plug. Qed.
#[local] Hint Resolve ANN_INC : asmrows.
(* [comment removed for export] *)
Lemma ANN_SHR : PmLibSpecsBLocal.PMSB.annotate_shrink_spec L ar HI 733160.
Proof. eapply AnnotateXB.annotate_shrink_ok; plug. Qed.
#[local] Hint Resolve ANN_SHR : asmrows.
(* [comment removed for export] *)
Lemma ANN_NEW : PMSA.annotate_new_spec L ar HI 857884.
Proof. eapply AnnotateXB.annotate_new_ok; plug. Qed.
#[local] Hint Resolve ANN_NEW : asmrows.
(* [comment removed for export] *)
Lemma ANN_DEL : PMSA.annotate_delete_spec L ar HI 732972.
Proof. eapply AnnotateXB.annotate_delete_ok; plug. Qed.
#[local] Hint Resolve ANN_DEL : asmrows.
(* [comment removed for export] *)
Lemma ANN_DELNULL : PMSA.annotate_delete_null_spec L ar HI 732972.
Proof. eapply AnnotateNullXB.annotate_delete_null_ok; plug. Qed.
#[local] Hint Resolve ANN_DELNULL : asmrows.
(* [comment removed for export] *)
Lemma VRSV : PMSA.vec_reserve_specA L ar HI 856176.
Proof. eapply VecReserveXB.vec_reserve_ok; plug. Qed.
#[local] Hint Resolve VRSV : asmrows.
(* [comment removed for export] *)
Lemma VPUSHSLOW : PMSA.vec_push_slow_spec L ar HI 858448.
Proof. eapply VecPushSlowXB.vec_push_slow_ok; plug. Qed.
#[local] Hint Resolve VPUSHSLOW : asmrows.
(* [comment removed for export] *)
Lemma VPUSH : PMSA.vec_push_specA L ar HI 858048.
Proof. eapply VecPushXB.vec_push_ok; plug. Qed.
#[local] Hint Resolve VPUSH : asmrows.
(* [comment removed for export] *)
Lemma VDTOR : PMSA.vec_dtor_specA L ar HI 732544.
Proof. eapply VecDtorXB.vec_dtor_ok; plug. Qed.
#[local] Hint Resolve VDTOR : asmrows.
(* [comment removed for export] *)
Lemma POPSTATE : PmLibSpecsBLocal.PMSB.pop_state_specA L ar HI 893820.
Proof. eapply PopStateXB.pop_state_ok; plug. Qed.
#[local] Hint Resolve POPSTATE : asmrows.
(* [comment removed for export] *)
Lemma PARENT : PMSA.parent_specA L ar HI 914208.
Proof. eapply ParentXB.parent_ok; plug. Qed.
#[local] Hint Resolve PARENT : asmrows.
(* [comment removed for export] *)
Lemma STRTOD : PMSA.strtod_specA L ar HI IC 1398624.
Proof. eapply Pm5StrtodOk.STOA.strtod_okA; plug. Qed.
#[local] Hint Resolve STRTOD : asmrows.
(* [comment removed for export] *)
Lemma DECSTR : PMSA.decstr_to_double_specA L ar HI IC 839740.
Proof. eapply DecstrXB.decstr_ok; plug. Qed.
#[local] Hint Resolve DECSTR : asmrows.
(* [comment removed for export] *)
Lemma PDTOR : PMSA.parser_dtor_specA L ar HI IC 731512.
Proof. eapply ParserDtorXB.parser_dtor_ok; plug. Qed.
#[local] Hint Resolve PDTOR : asmrows.
(* [comment removed for export] *)
Lemma DECU64 : PMSA.dec_u64_specA L ar HI IC 918912.
Proof. eapply DecU64XB.dec_u64_ok; plug. Qed.
#[local] Hint Resolve DECU64 : asmrows.
(* [comment removed for export] *)
Lemma VALIDATE : PMSA.validate_specA L ar HI IC 924200.
Proof. eapply ValidateXB.validate_ok; plug. Qed.
#[local] Hint Resolve VALIDATE : asmrows.
(* [comment removed for export] *)
Lemma CONVERT : PmLibSpecsBLocal.PMSB.convert_specA L ar HI IC 923544.
Proof. eapply ConvertXB.convert_ok; plug. Qed.
#[local] Hint Resolve CONVERT : asmrows.
(* [comment removed for export] *)
Lemma SETEC : PMSA.set_ec_specA L ar HI IC 842884.
Proof. eapply SetEcXB.set_ec_ok; plug. Qed.
#[local] Hint Resolve SETEC : asmrows.
(* [comment removed for export] *)
Lemma ATC : PMSA.append_to_codepoint_specA L ar HI IC 922968.
Proof. eapply AtcXB.atc_ok; plug. Qed.
#[local] Hint Resolve ATC : asmrows.
(* [comment removed for export] *)
Lemma TCE : PMSA.translate_conv_errc_specA L ar HI IC 925292.
Proof. eapply TceXB.tce_ok; plug. Qed.
#[local] Hint Resolve TCE : asmrows.
(* [comment removed for export] *)
Lemma XSGETN : TPSA.xsgetn_specA L ar HI IC 1078036.
Proof. eapply XsgetnXB.xsgetn_ok; plug. Qed.
#[local] Hint Resolve XSGETN : asmrows.
(* [comment removed for export] *)
Lemma DETECT : TPSA.detect_json_specA L ar HI IC 863032.
Proof. eapply DetectXB.detect_json_ok; plug. Qed.
#[local] Hint Resolve DETECT : asmrows.
(* [comment removed for export] *)
Lemma READCHUNK : TPSA.read_chunk_specA L ar HI IC 861456.
Proof. eapply ReadChunkXB.read_chunk_ok; plug. Qed.
#[local] Hint Resolve READCHUNK : asmrows.
(* [comment removed for export] *)
Lemma ISS : PMSA.iss_ctor_specA L ar HI IC 727572.
Proof. eapply IssCtorXB.iss_ctor_ok; plug. Qed.
#[local] Hint Resolve ISS : asmrows.
(* [comment removed for export] *)
Lemma ISSX : HNK.iss_ctor_specX L ar HI IC 727572.
Proof. eapply IssCtorXB.iss_ctor_okX; plug. Qed.
#[local] Hint Resolve ISSX : asmrows.
(* [comment removed for export] *)
Lemma RCTOR : PMSA.reader_ctor_specA L ar HI IC 729448.
Proof. eapply ReaderCtorXB.reader_ctor_ok; plug. Qed.
#[local] Hint Resolve RCTOR : asmrows.
(* [comment removed for export] *)
Lemma RESET : TPSA.reset_specA L ar HI IC 861128.
Proof. eapply ResetXB.reset_ok; plug. Qed.
#[local] Hint Resolve RESET : asmrows.
(* [comment removed for export] *)
Lemma PCD : PMSA.parser_check_done_specA L ar HI IC 928308.
Proof. eapply PcdXB.parser_check_done_ok; plug. Qed.
#[local] Hint Resolve PCD : asmrows.
(* [comment removed for export] *)
Lemma PCD16 : PmLibSpecsBLocal.PMSB.parser_check_done_specB16 L ar HI IC 928308.
Proof. eapply PcdXB16.parser_check_done16_ok; plug. Qed.
#[local] Hint Resolve PCD16 : asmrows.
(* [comment removed for export] *)
Lemma RCDONE : TPSA.rcheck_done_specA L ar HI IC 860404.
Proof. eapply RCheckDoneXB.rcheck_done_ok; plug. Qed.
#[local] Hint Resolve RCDONE : asmrows.
(* [comment removed for export] *)
Lemma SKIPSPACE : PMSA.skip_space_specA L ar HI IC 894716.
Proof. eapply SkipSpaceXB.skip_space_ok; plug. Qed.
#[local] Hint Resolve SKIPSPACE : asmrows.
(* [comment removed for export] *)
Lemma SKIPWS : PMSA.skip_whitespace_specA L ar HI IC 861724.
Proof. eapply SkipWsXB.skip_whitespace_ok; plug. Qed.
#[local] Hint Resolve SKIPWS : asmrows.
(* [comment removed for export] *)
Lemma AFTERVALUE : PMSA.after_value_specA L ar HI IC 918320.
Proof. eapply AfterValueXB.after_value_ok; plug. Qed.
#[local] Hint Resolve AFTERVALUE : asmrows.
(* [comment removed for export] *)
Lemma BEGINMEMBER : PMSA.begin_member_specA L ar HI IC 913616.
Proof. eapply BeginMemberXB.begin_member_ok; plug. Qed.
#[local] Hint Resolve BEGINMEMBER : asmrows.
(* [comment removed for export] *)
Lemma SDTOR : PMSA.source_dtor_specA L ar HI IC 733456.
Proof. eapply SourceDtorXB.source_dtor_ok; plug. Qed.
#[local] Hint Resolve SDTOR : asmrows.
(* [comment removed for export] *)
Lemma STRPUSHBACKX : PMESA.str_push_back_x_specA L ar HI CL 1056004.
Proof. pose proof (L5A.aly_cost L C LAY) as (K0 & LIN0 & OVH0). exact (EncPushBackXB.EPBA.str_push_back_x_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) K0 LIN0 OVH0 CL onmax CLOKX OPNEWX OPDEL MEMMOVE_X). Qed.
#[local] Hint Resolve STRPUSHBACKX : asmrows.
(* [comment removed for export] *)
Lemma STRAPPENDX : PMESA.str_append_x_specA L ar HI IC CL 1055420.
Proof. pose proof (L5A.aly_cost L C LAY) as (K0 & LIN0 & OVH0). exact (EncAppendXB.EAPA.str_append_x_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) K0 LIN0 OVH0 CL onmax CLOKX OPNEWX OPDEL MEMMOVE_X MEMCPY_X). Qed.
#[local] Hint Resolve STRAPPENDX : asmrows.
(* [comment removed for export] *)
Lemma NULL_LIT : PMESA.null_literal_specA L ar HI IC 778032.
Proof. exact (EncLiteralsXB.ELTNA.null_literal_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) GUARD_ACQ GUARD_REL). Qed.
#[local] Hint Resolve NULL_LIT : asmrows.
(* [comment removed for export] *)
Lemma TRUE_LIT : PMESA.true_literal_specA L ar HI IC 848468.
Proof. exact (EncLiteralsXB.ELTTA.true_literal_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) GUARD_ACQ GUARD_REL). Qed.
#[local] Hint Resolve TRUE_LIT : asmrows.
(* [comment removed for export] *)
Lemma FALSE_LIT : PMESA.false_literal_specA L ar HI IC 848584.
Proof. exact (EncLiteralsXB.ELTFA.false_literal_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) GUARD_ACQ GUARD_REL). Qed.
#[local] Hint Resolve FALSE_LIT : asmrows.
(* [comment removed for export] *)
Lemma TOCP : PMESA.to_codepoint_specA L ar HI IC 822120.
Proof. exact (EncToCodepointXB.to_codepoint_ok L ar C HI IL HIok LAY ISH POI_TC ltac:(first [exact FPM | exact FPMH])). Qed.
#[local] Hint Resolve TOCP : asmrows.
(* [comment removed for export] *)
Lemma NEWLINE : PMESA.new_line_specA L ar HI IC EC CL 770716.
Proof. exact (EncNewLineFXB.ENLFA.new_line_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL STRAPPENDX STRPUSHBACKX). Qed.
#[local] Hint Resolve NEWLINE : asmrows.
(* [comment removed for export] *)
Lemma BEGINSCALAR : PMESA.begin_scalar_specA L ar HI IC EC CL 772528.
Proof. exact (EncBeginScalarFXB.EBFA.begin_scalar_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ACC_COMMA CL STRAPPENDX NEWLINE). Qed.
#[local] Hint Resolve BEGINSCALAR : asmrows.
(* [comment removed for export] *)
Lemma ESCAPE : PMESA.escape_string_specA L ar HI IC CL 785716.
Proof. exact (EncEscapeXB.EESX.escape_string_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL CL40 STRPUSHBACKX TOCP). Qed.
#[local] Hint Resolve ESCAPE : asmrows.
(* [comment removed for export] *)
Lemma WRITEBIGNUM : PMESA.write_bignum_specA L ar HI IC EC CL 782480.
Proof. exact (EncWriteBignumXB.write_bignum_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL STRAPPENDX SETSHF5). Qed.
#[local] Hint Resolve WRITEBIGNUM : asmrows.
(* [comment removed for export] *)
Lemma WRITESTRING : PMESA.write_string_specA L ar HI IC EC CL 777096.
Proof. exact (EncWriteStringXB.write_string_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL STRPUSHBACKX STRAPPENDX ESCAPE WRITEBIGNUM). Qed.
#[local] Hint Resolve WRITESTRING : asmrows.
(* [comment removed for export] *)
Lemma STRTODG : PMFXA.strtod_g_specA L ar HI IC 1398624.
Proof. eapply Pm5StrtodG.STGA.strtod_g_okA; plug. Qed.
#[local] Hint Resolve STRTODG : asmrows.
(* [comment removed for export] *)
Lemma DECSTRG : PMFXA.decstr_to_double_g_specA L ar HI IC 839740.
Proof. eapply DecstrGXB.decstr_g_ok; plug. Qed.
#[local] Hint Resolve DECSTRG : asmrows.
(* [comment removed for export] *)
Lemma SNPRINTFG : PMFXA.snprintf_g_specA L ar HI IC 442940 154912.
Proof. eapply SnprintfCpsXB.snprintf_g_okA; plug. Qed.
#[local] Hint Resolve SNPRINTFG : asmrows.
(* [comment removed for export] *)
Lemma DUMPBUF : PMFXTA.dump_buffer_x_specA L ar HI IC CL 828952.
Proof. eapply DumpBufXB.dump_buffer_x_ok; plug. Qed.
#[local] Hint Resolve DUMPBUF : asmrows.
(* [comment removed for export] *)
Lemma PRETTIFY : PMFXTA.prettify_x_specA L ar HI IC CL 833108.
Proof. eapply PrettifyXB.prettify_x_ok; plug. Qed.
#[local] Hint Resolve PRETTIFY : asmrows.
(* [comment removed for export] *)
Lemma DTOAF : PMFXTA.dtoa_false_x_specA L ar HI IC CL 841828.
Proof. eapply DtoaFalseXB.dtoa_false_x_ok; plug. Qed.
#[local] Hint Resolve DTOAF : asmrows.
(* [comment removed for export] *)
Lemma DTOAT : PMFXTA.dtoa_true_x_specA L ar HI IC CL 840792.
Proof. eapply DtoaTrueXB.dtoa_true_x_ok; plug. Qed.
#[local] Hint Resolve DTOAT : asmrows.
(* [comment removed for export] *)
Lemma FROMU : PMESA.from_integer_x_specA L ar HI IC CL 773284.
Proof. eapply FromIntU64XB.from_integer_u64_x_ok; plug. Qed.
#[local] Hint Resolve FROMU : asmrows.
(* [comment removed for export] *)
Lemma FROMI : PMESA.from_integer_x_specA L ar HI IC CL 774952.
Proof. eapply FromIntI64XB.from_integer_i64_x_ok; plug. Qed.
#[local] Hint Resolve FROMI : asmrows.
(* [comment removed for export] *)
Lemma WDOUBLE : PMESA.write_double_x_specA L ar HI IC PMFXA.WD_SCR_XA CL 779704.
Proof. eapply WriteDoubleClosedXB.WDCA.write_double_closed; plug. Qed.
#[local] Hint Resolve WDOUBLE : asmrows.
(* [comment removed for export] *)
Lemma NEWLINE2 : PMESA.new_line2_specA L ar HI IC CL 770716.
Proof. exact (EncNewLine2FXB.ENL2FA.new_line2_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL STRAPPENDX STRPUSHBACKX). Qed.
#[local] Hint Resolve NEWLINE2 : asmrows.
(* [comment removed for export] *)
Lemma ANNCTX : PMES2A.annotate_shrink_ctx_specA L ar HI 769920.
Proof. exact (AnnotateCtxXB.annotate_shrink_ctx_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ANN). Qed.
#[local] Hint Resolve ANNCTX : asmrows.
(* [comment removed for export] *)
Lemma PUSHFAST_A : PMES2A.push_fast_specXB L ar HI 846068.
Proof. exact (PushFastRXB.push_fast_root_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ANN). Qed.
#[local] Hint Resolve PUSHFAST_A : asmrows.
(* [comment removed for export] *)
Lemma PUSHSLOW_A : PMES2A.push_slow_specXB L ar HI onmax 846316.
Proof. exact (PushSlowXB.push_slow_root_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) onmax OPNEWX ANN OPDEL). Qed.
#[local] Hint Resolve PUSHSLOW_A : asmrows.
(* [comment removed for export] *)
Lemma PUSHFAST_B : PMES2A.push_fast_specXB L ar HI 843104.
Proof. exact (PushFastNXB.push_fast_nested_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ANN). Qed.
#[local] Hint Resolve PUSHFAST_B : asmrows.
(* [comment removed for export] *)
Lemma PUSHSLOW_B : PMES2A.push_slow_specXB L ar HI onmax 843352.
Proof. exact (PushSlowXB.push_slow_nested_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) onmax OPNEWX ANN OPDEL). Qed.
#[local] Hint Resolve PUSHSLOW_B : asmrows.
(* [comment removed for export] *)
Lemma VNULL_E : PMESA.visit_null_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 756100.
Proof. exact (EncVisitNullFXB.EVNFA.visit_null_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ACC_NULL FOOTXC2 CL BEGINSCALAR NULL_LIT STRAPPENDX). Qed.
#[local] Hint Resolve VNULL_E : asmrows.
(* [comment removed for export] *)
Lemma VBOOL_E : PMESA.visit_bool_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 756716.
Proof. exact (EncVisitBoolFXB.EVBFA.visit_bool_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) ACC_TRUE ACC_FALSE FOOTXC2 CL BEGINSCALAR TRUE_LIT FALSE_LIT STRAPPENDX). Qed.
#[local] Hint Resolve VBOOL_E : asmrows.
(* [comment removed for export] *)
Lemma VU64_E : PMESA.visit_uint64_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 741900.
Proof. exact (EncVisitU64FXB.EVUFA.visit_uint64_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) FOOTXC2 CL BEGINSCALAR FROMU). Qed.
#[local] Hint Resolve VU64_E : asmrows.
(* [comment removed for export] *)
Lemma VI64_E : PMESA.visit_int64_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 742460.
Proof. exact (EncVisitI64FXB.EVIFA.visit_int64_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) FOOTXC2 CL BEGINSCALAR FROMI). Qed.
#[local] Hint Resolve VI64_E : asmrows.
(* [comment removed for export] *)
Lemma VSTR_E : PMESA.visit_string_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 757412.
Proof. exact (EncVisitStrFXB.EVSFA.visit_string_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) FOOTXC2 CL BEGINSCALAR WRITESTRING). Qed.
#[local] Hint Resolve VSTR_E : asmrows.
(* [comment removed for export] *)
Lemma VKEY_E : PMESA.visit_key_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 754188.
Proof. exact (EncVisitKeyFXB.EVKFA.visit_key_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL ACC_COMMA ACC_COLON FOOTXC2 NEWLINE2 STRAPPENDX STRPUSHBACKX ESCAPE). Qed.
#[local] Hint Resolve VKEY_E : asmrows.
(* [comment removed for export] *)
Lemma VDBL_E : PMESA.visit_double_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 743020.
Proof. eapply VisitDoubleClosedXB.VDCA.visit_double_closed; plug. Qed.
#[local] Hint Resolve VDBL_E : asmrows.
(* [comment removed for export] *)
Lemma VBOBJ_E : PMESA.visit_begin_object_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 747548.
Proof. exact (EncVisitBeginFXB.EVBGA.visit_begin_object_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL onmax IL ACC_OBRACE ACC_COMMA ISH POI_VBO FOOTXC2 NEWLINE2 STRAPPENDX CLOKX PUSHFAST_A PUSHSLOW_A PUSHFAST_B PUSHSLOW_B). Qed.
#[local] Hint Resolve VBOBJ_E : asmrows.
(* [comment removed for export] *)
Lemma VBARR_E : PMESA.visit_begin_array_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 751264.
Proof. exact (EncVisitBeginFXB.EVBGA.visit_begin_array_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL onmax IL ACC_OBRACKET ACC_COMMA ISH POI_VBO FOOTXC2 NEWLINE2 STRAPPENDX CLOKX PUSHFAST_A PUSHSLOW_A PUSHFAST_B PUSHSLOW_B). Qed.
#[local] Hint Resolve VBARR_E : asmrows.
(* [comment removed for export] *)
Lemma VEOBJ_E : PMESA.visit_end_object_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 749780.
Proof. exact (EncVisitEndFXB.EVEFA.visit_end_object_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL ACC_CBRACE FOOTXC2 NEWLINE2 ANNCTX STRAPPENDX). Qed.
#[local] Hint Resolve VEOBJ_E : asmrows.
(* [comment removed for export] *)
Lemma VEARR_E : PMESA.visit_end_array_specA L ar HI IC EC PMFXA.WD_SCR_XA CL 740416.
Proof. exact (EncVisitEndFXB.EVEFA.visit_end_array_ok L ar C HI HIok LAY ltac:(first [exact FPM | exact FPMH]) CL ACC_CBRACKET FOOTXC2 NEWLINE2 ANNCTX STRAPPENDX). Qed.
#[local] Hint Resolve VEARR_E : asmrows.
(* [comment removed for export] *)
Lemma VNULL : PMXA.visit_null_specXA L ar HI IC enc_invA VIS VISD benc eroomA 756100.
Proof. exact (WidenXB.WDXA.visit_null_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VNULL_E). Qed.
#[local] Hint Resolve VNULL : asmrows.
(* [comment removed for export] *)
Lemma VBOOL : PMXA.visit_bool_specXA L ar HI IC enc_invA VIS VISD benc eroomA 756716.
Proof. exact (WidenXB.WDXA.visit_bool_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VBOOL_E). Qed.
#[local] Hint Resolve VBOOL : asmrows.
(* [comment removed for export] *)
Lemma VU64 : PMXA.visit_uint64_specXA L ar HI IC enc_invA VIS VISD benc eroomA 741900.
Proof. exact (WidenXB.WDXA.visit_uint64_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VU64_E). Qed.
#[local] Hint Resolve VU64 : asmrows.
(* [comment removed for export] *)
Lemma VI64 : PMXA.visit_int64_specXA L ar HI IC enc_invA VIS VISD benc eroomA 742460.
Proof. exact (WidenXB.WDXA.visit_int64_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VI64_E). Qed.
#[local] Hint Resolve VI64 : asmrows.
(* [comment removed for export] *)
Lemma VSTR : PMXA.visit_string_specXA L ar HI IC enc_invA VIS VISD benc eroomA 757412.
Proof. exact (WidenXB.WDXA.visit_string_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VSTR_E). Qed.
#[local] Hint Resolve VSTR : asmrows.
(* [comment removed for export] *)
Lemma VKEY : PMXA.visit_key_specXA L ar HI IC enc_invA VIS VISD benc eroomA 754188.
Proof. exact (WidenXB.WDXA.visit_key_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VKEY_E). Qed.
#[local] Hint Resolve VKEY : asmrows.
(* [comment removed for export] *)
Lemma VDBL : PMXA.visit_double_specXA L ar HI IC enc_invA VIS VISD benc eroomA 743020.
Proof. exact (WidenXB.WDXA.visit_double_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VDBL_E). Qed.
#[local] Hint Resolve VDBL : asmrows.
(* [comment removed for export] *)
Lemma VBOBJ : PMXA.visit_begin_object_specXA L ar HI IC enc_invA VIS VISD benc eroomA 747548.
Proof. exact (WidenXB.WDXA.visit_begin_object_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VBOBJ_E). Qed.
#[local] Hint Resolve VBOBJ : asmrows.
(* [comment removed for export] *)
Lemma VBARR : PMXA.visit_begin_array_specXA L ar HI IC enc_invA VIS VISD benc eroomA 751264.
Proof. exact (WidenXB.WDXA.visit_begin_array_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VBARR_E). Qed.
#[local] Hint Resolve VBARR : asmrows.
(* [comment removed for export] *)
Lemma VEOBJ : PMXA.visit_end_object_specXA L ar HI IC enc_invA VIS VISD benc eroomA 749780.
Proof. exact (WidenXB.WDXA.visit_end_object_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VEOBJ_E). Qed.
#[local] Hint Resolve VEOBJ : asmrows.
(* [comment removed for export] *)
Lemma VEARR : PMXA.visit_end_array_specXA L ar HI IC enc_invA VIS VISD benc eroomA 740416.
Proof. exact (WidenXB.WDXA.visit_end_array_bridge L ar HI IC EC PMFXA.WD_SCR_XA CL WidenXB.WDXA.wdle_12800 WidenXB.WDXA.wd8_12800 _ VEARR_E). Qed.
#[local] Hint Resolve VEARR : asmrows.
(* [comment removed for export] *)
Lemma ENC_AGREE : PMXA.enc_agreeP enc_invA.
Proof. exact (EncKitXB.EKA.enc_agree_ok L IC EC). Qed.
#[local] Hint Resolve ENC_AGREE : asmrows.
(* [comment removed for export] *)
Lemma ENC_CTOR : TPSXA.enc_ctor_specXA L ar HI IC enc_invA 728244.
Proof. exact (EncCtorXB.enc_ctor_ok L ar C HI IL EC HIok LAY ltac:(first [exact FPM | exact FPMH]) SETSHF5 ISH POI_EC5 RTG GLIN eq_refl). Qed.
#[local] Hint Resolve ENC_CTOR : asmrows.
(* [comment removed for export] *)
Lemma ENC_DTOR : TPSXA.enc_dtor_specXA L ar HI IC enc_invA 731020.
Proof. exact (EncDtorXB.enc_dtor_ok L ar C HI IL EC HIok LAY ltac:(first [exact FPM | exact FPMH]) ANN OPDEL ISH POI_VTT POI_VBO). Qed.
#[local] Hint Resolve ENC_DTOR : asmrows.
(* [comment removed for export] *)
Lemma ENC_AGREE_NS : HnKitXB2.HK2.enc_agree_nsP enc_invA.
Proof. exact (HnGlueXB.HGX.enc_agree_ns_ok L IC EC). Qed.
#[local] Hint Resolve ENC_AGREE_NS : asmrows.
(* [comment removed for export] *)
Lemma ENC_VIS : forall (M : PMSA.mem) V S2 g, enc_invA M V S2 g -> PMSA.vis_at L IC M V.
Proof. exact (HnGlueXB.HGX.enc_vis_ok L IC EC). Qed.
#[local] Hint Resolve ENC_VIS : asmrows.
(* [comment removed for export] *)
Lemma BENC0 : PMXA.bencP benc.
Proof. pose proof (L5A.aly_cost L C LAY) as (_ & LIN0 & OVH0). exact (EncKitXB.EKA.benc_nonneg L CL LIN0 OVH0). Qed.
#[local] Hint Resolve BENC0 : asmrows.
(* [comment removed for export] *)
Lemma XSGETNW : TPSAW.xsgetn_specAW L ar HI IC 1078036.
Proof. eapply XsgetnXBW.xsgetn_okw; plug. Qed.
#[local] Hint Resolve XSGETNW : asmrows.
(* [comment removed for export] *)
Lemma DETECTW : TPSAW.detect_json_specAW L ar HI IC 863032.
Proof. eapply DetectXBW.detect_json_okw; plug. Qed.
#[local] Hint Resolve DETECTW : asmrows.
(* [comment removed for export] *)
Lemma RCHUNKW : TPSAW.read_chunk_specAW L ar HI IC 861456.
Proof. eapply ReadChunkXBW.read_chunk_okw; plug. Qed.
#[local] Hint Resolve RCHUNKW : asmrows.
(* [comment removed for export] *)
Lemma PSOMEXW : PMXAW.parse_some_specXAW L ar HI IC enc_invA VIS VISD benc (PMRXA.the_rmA L) CLW 864580.
Proof. exact (ParseAsmXBW.parse_some_okw_lib L ar C HI IL CLW enc_invA benc eroomA HIok LAY FPM FOOTC FOOTXC ISH TPV POI_VT POI_DTAB POI_TC POI_CV SM0 SM1 SM4 SETSHF5 ERRNO_NS ERRH SETEC STRPUSHBACK STRAPPEND STRAPPENDRANGE VPUSH POPSTATE PARENT DECSTR DECU64 TCE ENC_AGREE BENC0 ROOMW VNULL VBOOL VU64 VI64 VSTR VKEY VDBL VBOBJ VBARR VEOBJ VEARR). Qed.
#[local] Hint Resolve PSOMEXW : asmrows.
(* [comment removed for export] *)
Lemma READXAW : TPSXAW.read_specXAW L ar HI IC enc_invA VIS VISD benc CLW 730872.
Proof. exact (ReadXBW.read_xbw_ok L ar C HI IL HIok LAY FPM FOOTXC enc_invA benc ENC_AGREE XKA.lits_inside_xboth TPV ISH POI_ISS RESET CLW RCHUNKW PSOMEXW SKIPWS SETEC RCDONE). Qed.
#[local] Hint Resolve READXAW : asmrows.
(* [comment removed for export] *)
Lemma HASW : TPSXAW.harness_chainXAW L ar HI IC benc 724512 0 false.
Proof. exact (HarnessAsXBW.harness_as_okw L ar C HI IL HIok LAY FPM FOOTC FOOTC2 FOOTXC enc_invA benc ENC_AGREE_NS BENC0 XKA.lits_inside_xboth ENC_VIS PAT PATR SF5 SETSH00 SETSHF8 STRINIT ISSX RCTOR SYSCAT CLW CLOK READXAW ENC_CTOR ENC_DTOR PDTOR SDTOR LOCDTOR OPDEL FN TPV ISH POI_HN). Qed.
#[local] Hint Resolve HASW : asmrows.
(* [comment removed for export] *)
Lemma HALW : TPSXAW.harness_chainXAW L ar HI IC benc 724512 0 true.
Proof. exact (HarnessAlXBW.harness_al_okw L ar C HI IL HIok LAY FPM FOOTC FOOTC2 FOOTXC enc_invA benc ENC_AGREE_NS BENC0 XKA.lits_inside_xboth ENC_VIS PAT PATR SF5 SETSH00 SETSHF8 STRINIT ISSX RCTOR SYSCAT CLW CLOK READXAW ENC_CTOR ENC_DTOR PDTOR SDTOR LOCDTOR OPDEL FN TPV ISH POI_HN). Qed.
#[local] Hint Resolve HALW : asmrows.
(* [comment removed for export] *)
Lemma HBSW : TPSXAW.harness_chainXAW L ar HI IC benc 724512 16 false.
Proof. exact (HarnessBsXBW.harness_bs_okw L ar C HI IL HIok LAY FPM FOOTC FOOTC2 FOOTXC enc_invA benc ENC_AGREE_NS BENC0 XKA.lits_inside_xboth ENC_VIS PAT PATR SF5 SETSH00 SETSHF8 STRINIT ISSX RCTOR SYSCAT CLW CLOK READXAW ENC_CTOR ENC_DTOR PDTOR SDTOR LOCDTOR OPDEL FN TPV ISH POI_HN). Qed.
#[local] Hint Resolve HBSW : asmrows.
(* [comment removed for export] *)
Lemma HBLW : TPSXAW.harness_chainXAW L ar HI IC benc 724512 16 true.
Proof. exact (HarnessBlXBW.harness_bl_okw L ar C HI IL HIok LAY FPM FOOTC FOOTC2 FOOTXC enc_invA benc ENC_AGREE_NS BENC0 XKA.lits_inside_xboth ENC_VIS PAT PATR SF5 SETSH00 SETSHF8 STRINIT ISSX RCTOR SYSCAT CLW CLOK READXAW ENC_CTOR ENC_DTOR PDTOR SDTOR LOCDTOR OPDEL FN TPV ISH POI_HN). Qed.
#[local] Hint Resolve HBLW : asmrows.
(* [comment removed for export] *)
Lemma LIBTOPXAW : forall Lay, TPSXA.pm_layout_okxA L IC VIS benc Lay -> lla_stack Lay = TPSXA.HARN_SCRXA -> lla_entry Lay = 724512 -> lla_empty Lay = TPSXA.EMPTY_X -> PmLibIfaceAW.lib_call_okAW Lay ar SCFG HI (TPSXA.pm_staticsxA L IC) PHI.
Proof. exact (LibTopXBW.LTXAW.lib_call_okw L ar C HI VIS benc HIok TPV PHI PHIW HASW HALW HBSW HBLW). Qed.
#[local] Hint Resolve LIBTOPXAW : asmrows.

Theorem lib_ok_xaw_full : forall Lay, lla_stack Lay = TPSXA.HARN_SCRXA -> lla_entry Lay = 724512 -> lla_empty Lay = TPSXA.EMPTY_X -> TPSXAW.lib_specxAW L ar HI IC VIS benc PHI Lay.
Proof. intros Lay H1 H2 H3 LOK. exact (LIBTOPXAW Lay LOK H1 H2 H3). Qed.
End A.
End ASMFXBWF.
