(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 4505 of its 4800 lines of code are new or changed and 4758 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s15.v, with its module paths and module names changed; 188 of its 244 lines of code are new or changed and 4744 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the walk of the test harness's
   entry function LLVMFuzzerTestOneInput (0x84d34, 4,488 bytes, 1,122 instructions) composed from its segment lemmas
   into LLVMFuzzerTestOneInput_contract at image A's instance (the entry BASE + AF_LLVMFuzzerTestOneInput, the window
   STK_LLVMFuzzerTestOneInput and SegInstA's pure parameters, exactly as lt_adapter in LLVMFuzzerTestOneInput_s02.v
   states it). This is the theorem the image-A owner's close consumes.

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput.v:40-109 (origin/ossv/recipes 501c0d516c69):
   each segment lemma at every FP state (lt_close closes each of its premises from this Section), the chain by
   LLVMFuzzerTestOneInput_s02.v's lt_assemble (the two loops by downward induction inside it), and the entry
   statement adapted to the contract by lt_adapter.

   Section hypotheses: the union of the segment lemmas' own Section hypotheses, each stated once and word for word
   as the segment proofs state it (the callee contracts and runtime rows at every FP state, the kit laws, the listing
   classes, the image facts); the walk's hypothesis list lists each one with the
   segments that use it and how the close discharges it. Every segment of the walk (S00 .. S21 and the ret) is a
   lemma here: no segment statement is a hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob
  SegPaLib PaLibF SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtShadow RtSegCalloc RtSeg RtPFSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_init_c check_refusals_c
  check_address_c check_knock_refused_c reac_segconf_declared_c check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import check_segments_c reac_segconf_role_c
  check_role_c reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c reac_segconf_role_file_c
  reac_segconf_ignore_file_c check_provenance_c reac_segconf_parse_c m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_find_c check_absent_c m_file_c
  reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02 LLVMFuzzerTestOneInput_s10k
  LLVMFuzzerTestOneInput_s14k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require LLVMFuzzerTestOneInput_s10
  LLVMFuzzerTestOneInput_s12 LLVMFuzzerTestOneInput_s13 LLVMFuzzerTestOneInput_s14 LLVMFuzzerTestOneInput_s15
  LLVMFuzzerTestOneInput_s16 LLVMFuzzerTestOneInput_s17 LLVMFuzzerTestOneInput_s18 LLVMFuzzerTestOneInput_s19
  LLVMFuzzerTestOneInput_s20 LLVMFuzzerTestOneInput_s21 LLVMFuzzerTestOneInput_s22 LLVMFuzzerTestOneInput_s23
  LLVMFuzzerTestOneInput_s24 LLVMFuzzerTestOneInput_s25.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the segment proofs by file group (_sNN): 10 S00, 12 S01 S02, 13 S03, 14 S04, 15 S05, 16 S06, 17 S07 S08, 18 S09, 19 S10,
   20 S11 S12, 21 S13, 22 S14, 23 S15, 24 S16 .. S20, 25 S21 and the ret *)
Module L10 := LLVMFuzzerTestOneInput_s10.
Module L12 := LLVMFuzzerTestOneInput_s12.
Module L13 := LLVMFuzzerTestOneInput_s13.
Module L14 := LLVMFuzzerTestOneInput_s14.
Module L15 := LLVMFuzzerTestOneInput_s15.
Module L16 := LLVMFuzzerTestOneInput_s16.
Module L17 := LLVMFuzzerTestOneInput_s17.
Module L18 := LLVMFuzzerTestOneInput_s18.
Module L19 := LLVMFuzzerTestOneInput_s19.
Module L20 := LLVMFuzzerTestOneInput_s20.
Module L21 := LLVMFuzzerTestOneInput_s21.
Module L22 := LLVMFuzzerTestOneInput_s22.
Module L23 := LLVMFuzzerTestOneInput_s23.
Module L24 := LLVMFuzzerTestOneInput_s24.
Module L25 := LLVMFuzzerTestOneInput_s25.

(* a segment lemma's premise: a hypothesis of this Section (an image number such as cstk is fixed by the
   hypothesis that names it), or a callee or runtime contract at the segment's FP state (this Section gives
   each at every FP state) *)
Ltac lt_close := solve [ eassumption | match goal with H : forall fx0 : YK11.FPState, _ |- _ => exact (H _) end ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the segment lemmas' Section hypotheses, each once, in the segment proofs' words (the segments that take each:
   the walk's hypothesis list) ---- *)
(* the listing's record of the runtime cells and wrappers *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the two image facts lt_img needs at a later reader (LLVMFuzzerTestOneInput_s10k.v, re-cut: RELRO in the image and
   the guard's ROM bytes), the allocator record's symbols (the stack-protector cells at an AR state come from it,
   SegRecCells.seg_ssp's route), and memchr's constant window: read-only image bytes no one owns, not errno
   (LLVMFuzzerTestOneInput_s14k.v; the same text as the m_file group's owner's m_file_memchr.memchr_rom_fact) *)
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis MCR : s14_memchr_rom SEGS B.
(* longl, the program's one writable static (ltoi_PG): a static of B in the image, not read-only; the words m_file and
   parse_file read from m_key.words and the box table point below longl (_s15's text) *)
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
(* the program's writable statics are B's *)
Hypothesis PRW : prog_rw SEGS B.
(* the listing's objects and the call targets of the program functions *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* the allocator model's laws, the meter's laws and the meter across set_fs *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
(* the side stack for frames: frame_alloc_3's contract, its release law and the flag law *)
Hypothesis SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* the runtime entries: malloc, free, memchr, strrchr, the checked memcpy and memset, strcmp, strlen, calloc at its
   stack window cstk, snprintf at its image numbers snp_lo snp_hi snp_cr (interface row 4's family; the five facts
   below are _s15's text, which _s20 takes verbatim), meta_fill_f5 *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  MemchrDef.amemchr_realizesM (fx := fx0) SEGS B memchr_loA memchr_hiA (SIG SS___interceptor_trampoline_memchr).
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strrchr).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OCpy (pa_sigma SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Variable cstk : Z.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (pa_sigma SS___interceptor_trampoline_calloc) cstk.
Variables (snp_lo snp_hi : Z) (snp_cr : list (Z * Z)).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr (SIG SS___interceptor_trampoline_snprintf)
    gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis SHF5 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (pa_sigma SS___asan_set_shadow_f5) 0xf5.
(* the program callees' contracts, at the listing's entry and window of each *)
Hypothesis HINIT : forall fx0 : YK11.FPState,
  @reac_segconf_init_contract fx0 rc SK SEGS B (BASE + AF_reac_segconf_init) STK_reac_segconf_init.
Hypothesis HCR : forall fx0 : YK11.FPState,
  check_refusals_contract (fx := fx0) SEGS B (BASE + AF_check_refusals) STK_check_refusals.
Hypothesis HCA : forall fx0 : YK11.FPState,
  check_address_contract (fx := fx0) SEGS B (BASE + AF_check_address) STK_check_address RLO_A RHI_A.
Hypothesis HCK : forall fx0 : YK11.FPState,
  check_knock_refused_contract (fx := fx0) SEGS B (BASE + AF_check_knock_refused) STK_check_knock_refused
    RLO_A RHI_A seg_litA_fz gotwA guardA.
Hypothesis HDECL : forall fx0 : YK11.FPState, reac_segconf_declared_contract (fx := fx0) SEGS B
  (BASE + AF_reac_segconf_declared) STK_reac_segconf_declared RLO_A RHI_A gotwA guardA.
Hypothesis HCHKD : forall fx0 : YK11.FPState, check_declared_contract (fx := fx0) SEGS B
  (BASE + AF_check_declared) STK_check_declared RLO_A RHI_A.
Hypothesis HCSEG : forall fx0 : YK11.FPState,
  check_segments_contract (fx := fx0) SEGS B (BASE + AF_check_segments) STK_check_segments RLO_A RHI_A.
Hypothesis HROLE : forall fx0 : YK11.FPState,
  reac_segconf_role_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role) STK_reac_segconf_role RLO_A RHI_A.
Hypothesis HCROLE : forall fx0 : YK11.FPState,
  check_role_contract (fx := fx0) SEGS B (BASE + AF_check_role) STK_check_role.
Hypothesis HMODEL : forall fx0 : YK11.FPState,
  reac_segconf_model_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_model) STK_reac_segconf_model RLO_A RHI_A.
Hypothesis HCMODEL : forall fx0 : YK11.FPState,
  check_model_contract (fx := fx0) SEGS B (BASE + AF_check_model) STK_check_model RLO_A RHI_A.
Hypothesis HIGNORED : forall fx0 : YK11.FPState,
  reac_segconf_ignored_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignored) STK_reac_segconf_ignored RLO_A RHI_A.
Hypothesis HCIGNORE : forall fx0 : YK11.FPState,
  check_ignore_contract (fx := fx0) SEGS B (BASE + AF_check_ignore) STK_check_ignore.
Hypothesis HROLEFILE : forall fx0 : YK11.FPState,
  reac_segconf_role_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role_file) STK_reac_segconf_role_file
    RLO_A RHI_A.
Hypothesis HIGNFILE : forall fx0 : YK11.FPState,
  reac_segconf_ignore_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignore_file) STK_reac_segconf_ignore_file
    RLO_A RHI_A.
Hypothesis HCPROV : forall fx0 : YK11.FPState,
  check_provenance_contract (fx := fx0) SEGS B (BASE + AF_check_provenance) STK_check_provenance RLO_A RHI_A.
Hypothesis HPARSE : forall fx0 : YK11.FPState, reac_segconf_parse_contract (fx := fx0) SEGS B
  (BASE + AF_reac_segconf_parse) STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc SK SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc SK SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
Hypothesis MREF : forall fx0 : YK11.FPState,
  @m_refuse_contract fx0 rc SK SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz gotwA guardA.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  @m_file_c.m_file_contract fx0 rc SK SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.

Theorem pb_LLVMFuzzerTestOneInput :
  LLVMFuzzerTestOneInput_contract SEGS B MT (BASE + AF_LLVMFuzzerTestOneInput) STK_LLVMFuzzerTestOneInput emptyA
    RLO_A RHI_A longlA mod40A catA wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc.
Proof.
(* each segment at every FP state, from its lemma at that state *)
assert (H00 : forall fx1 : YK11.FPState, lt_seg_S00_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L10.lt_seg_S00 fx1); lt_close).
assert (H01 : forall fx1 : YK11.FPState, lt_seg_S01_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L12.lt_seg_S01 fx1); lt_close).
assert (H02 : forall fx1 : YK11.FPState, lt_seg_S02_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L12.lt_seg_S02 fx1); lt_close).
assert (H03 : forall fx1 : YK11.FPState, lt_seg_S03_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L13.lt_seg_S03 fx1); lt_close).
assert (H04 : forall fx1 : YK11.FPState, lt_seg_S04_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L14.lt_seg_S04 fx1); lt_close).
assert (H05 : forall fx1 : YK11.FPState, lt_seg_S05_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L15.lt_seg_S05 fx1); lt_close).
(* _s16 and _s17 take the FP state last (their Sections put fx after the hypotheses): eapply finds it from the goal *)
assert (H06 : forall fx1 : YK11.FPState, lt_seg_S06_stmt (fx := fx1) B MT)
  by (intros fx1; eapply L16.lt_seg_S06; lt_close).
assert (H07 : forall fx1 : YK11.FPState, lt_seg_S07_stmt (fx := fx1) B MT)
  by (intros fx1; eapply L17.lt_seg_S07; lt_close).
assert (H08 : forall fx1 : YK11.FPState, lt_seg_S08_stmt (fx := fx1) B MT)
  by (intros fx1; eapply L17.lt_seg_S08; lt_close).
assert (H09 : forall fx1 : YK11.FPState, lt_seg_S09_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L18.lt_seg_S09 fx1); lt_close).
assert (H10 : forall fx1 : YK11.FPState, lt_seg_S10_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L19.lt_seg_S10 fx1); lt_close).
(* _s20 states its lemmas at every FP state (no fx in its Section): eapply finds the image numbers by the
   hypotheses that name them *)
assert (H11 : forall fx1 : YK11.FPState, lt_seg_S11_stmt (fx := fx1) B MT)
  by (intros fx1; eapply L20.lt_seg_S11; lt_close).
assert (H12 : forall fx1 : YK11.FPState, lt_seg_S12_stmt (fx := fx1) B MT)
  by (intros fx1; eapply L20.lt_seg_S12; lt_close).
assert (H13 : forall fx1 : YK11.FPState, lt_seg_S13_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L21.lt_seg_S13 fx1); lt_close).
assert (H14 : forall fx1 : YK11.FPState, lt_seg_S14_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L22.lt_seg_S14 fx1); lt_close).
assert (H15 : forall fx1 : YK11.FPState, lt_seg_S15_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L23.lt_seg_S15 fx1); lt_close).
assert (H16 : forall fx1 : YK11.FPState, lt_seg_S16_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L24.lt_seg_S16 fx1); lt_close).
assert (H17 : forall fx1 : YK11.FPState, lt_seg_S17_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L24.lt_seg_S17 fx1); lt_close).
assert (H18 : forall fx1 : YK11.FPState, lt_seg_S18_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L24.lt_seg_S18 fx1); lt_close).
assert (H19 : forall fx1 : YK11.FPState, lt_seg_S19_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L24.lt_seg_S19 fx1); lt_close).
assert (H20 : forall fx1 : YK11.FPState, lt_seg_S20_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L24.lt_seg_S20 fx1); lt_close).
assert (H21 : forall fx1 : YK11.FPState, lt_seg_S21_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L25.lt_seg_S21 fx1); lt_close).
assert (HR : forall fx1 : YK11.FPState, lt_seg_RET_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L25.lt_seg_RET fx1); lt_close).
exact (lt_adapter B MT (lt_assemble B MT H00 H01 H02 H03 H04 H05 H06 H07 H08 H09 H10 H11 H12 H13 H14
  H15 H16 H17 H18 H19 H20 H21 HR)).
Qed.

End e.
End f.
End d.
About L10.lt_seg_S00.
About L12.lt_seg_S01.
About L12.lt_seg_S02.
About L13.lt_seg_S03.
About L14.lt_seg_S04.
About L15.lt_seg_S05.
About L16.lt_seg_S06.
About L17.lt_seg_S07.
About L17.lt_seg_S08.
About L18.lt_seg_S09.
About L19.lt_seg_S10.
About L20.lt_seg_S11.
About L20.lt_seg_S12.
About L21.lt_seg_S13.
About L22.lt_seg_S14.
About L23.lt_seg_S15.
About L24.lt_seg_S16.
About L24.lt_seg_S17.
About L24.lt_seg_S18.
About L24.lt_seg_S19.
About L24.lt_seg_S20.
About L25.lt_seg_S21.
About L25.lt_seg_RET.
Print Assumptions pb_LLVMFuzzerTestOneInput.
About pb_LLVMFuzzerTestOneInput.
