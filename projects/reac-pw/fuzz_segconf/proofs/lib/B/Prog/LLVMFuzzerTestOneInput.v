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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s15.v, with its module paths and module names changed; 177 of its 228 lines of code are new or changed and 4749 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk of the test
   harness's entry function LLVMFuzzerTestOneInput (0x84dc0, 4,992 bytes, 1,248 instructions) composed from its segment
   lemmas into LLVMFuzzerTestOneInput_contract at image B's instance (the entry BASE + AF_LLVMFuzzerTestOneInput, the
   window STK_LLVMFuzzerTestOneInput and SegInstB's pure parameters, exactly as lt_adapter in
   LLVMFuzzerTestOneInput_s02.v states it). This is the theorem the image-B owner's close consumes.

   THE FORM: the image-B twin of the image-A G1 walk owner's lib/A/Prog/LLVMFuzzerTestOneInput.v (image A's composition commit
   d7cd63ea3138), with the same theorem name and the same hypothesis names wherever image B has the same hypothesis;
   its form is plugin-hostd/fuzz_command's lib/B/Prog/LLVMFuzzerTestOneInput.v (origin/ossv/recipes 3abc3740de97):
   each segment lemma at every FP state (lt_close closes each of its premises from this Section), the chain by
   LLVMFuzzerTestOneInput_s02.v's lt_assemble (the two loops by downward induction inside it), and the entry
   statement adapted to the contract by lt_adapter.

   Section hypotheses: the union of the 22 segment lemmas' and the ret's own Section hypotheses, each stated once and
   in the segment files' words (the callee contracts and runtime rows at every FP state, the kit laws, the listing
   record, image B's image facts and symbol record); where a segment file names a fact differently from the image-A
   twin, the image-A name is kept (HB for the HSY of the S00, S01 / S02, S04 and S11 / S12 walks and the HBS of the
   S05 and S07 / S08 walks; HINIT, HDECL, HCHKD, HIGNORED, HCIGNORE, HROLEFILE, HIGNFILE, MREF for the names of the
   S03, S16 .. S20, S09 and S06 walks). Two segment premises are not hypotheses here: the S09 walk's
   `LAWS : AR_laws SEGS B` is the kit's theorem YG0q.AR_laws_ok, and the S03 walk's callee contract at the call target
   `pa_sigma SS_reac_segconf_init` follows from HINIT (at the listing entry BASE + AF_reac_segconf_init) by SIGP's
   equation. The walk's hypothesis note WALK-HYPOTHESES.md lists each hypothesis with the segments that
   use it, its image-A twin and how the close discharges it. `Proof using All` keeps every one of them in the
   theorem's type, so the close's argument list is the Section's. Every segment is a lemma: no segment statement is
   a hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YF0m YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob
  SegPaLib PaLibF SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtShadow RtSegCalloc RtSeg RtPFSeg RtString
  MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_segconf_init_c check_refusals_c
  check_address_c check_knock_refused_c reac_segconf_declared_c check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import check_segments_c reac_segconf_role_c
  check_role_c reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c reac_segconf_role_file_c
  reac_segconf_ignore_file_c check_provenance_c m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse_c m_find_c check_absent_c
  m_file_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require LLVMFuzzerTestOneInput_s10
  LLVMFuzzerTestOneInput_s12 LLVMFuzzerTestOneInput_s13 LLVMFuzzerTestOneInput_s14 LLVMFuzzerTestOneInput_s15
  LLVMFuzzerTestOneInput_s16 LLVMFuzzerTestOneInput_s17 LLVMFuzzerTestOneInput_s18 LLVMFuzzerTestOneInput_s19
  LLVMFuzzerTestOneInput_s20 LLVMFuzzerTestOneInput_s21 LLVMFuzzerTestOneInput_s22 LLVMFuzzerTestOneInput_s23
  LLVMFuzzerTestOneInput_s24 LLVMFuzzerTestOneInput_s25.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the segment walks and their files: S00 (_s10.v), S01 and S02 (_s12.v), S03 (_s13.v), S04 (_s14.v), S05 (_s15.v),
   S06 (_s16.v), S07 and S08 (_s17.v), S09 (_s18.v), S10 (_s19.v), S11 and S12 (_s20.v), S13 (_s21.v), S14 (_s22.v),
   S15 (_s23.v), S16 .. S20 (_s24.v), S21 and the ret (_s25.v); each alias below is its file's number *)
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
   hypothesis that names it), a fact the proof states first (LAWS, HINIT'), or a callee or runtime contract at the
   segment's FP state (this Section gives each at every FP state) *)
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

(* ---- the segment lemmas' Section hypotheses, each once, in the segment files' words ---- *)
(* the listing's record of the runtime cells and wrappers (S00, S01, S02, S04, S05, S07, S08, S11, S12, S14, S15,
   S16 .. S20) *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* image B's facts about the image and its segments (lib/B/Prog/SegRecBase.v; S00, S01, S02, S04, S05, S07, S08,
   S11, S12, S16 .. S20) and image B's symbol record (lib/B/YF0m.v; the same segments: the S00, S01 / S02, S04 and
   S11 / S12 walks name it HSY, the S05 and S07 / S08 walks HBS, the S16 .. S20 walk HB) *)
Hypothesis IMGF : SegRecBase.seg_img_facts SEGS B.
Hypothesis HB : YF0m.SegBSyms B.
(* the listing's objects (S01, S05, S11, S12, S13) and the call targets of the program functions (S03 by HINIT', S05
   .. S12, S16 .. S20) *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* the program's writable static longl (S05): writable, a static of the record, in the image, not read-only, and every
   pointer word of words[] and of the catalogue rows 64 KiB below it (the S05 walk's text, image A's S05 walk's
   names) *)
Hypothesis PRW : prog_rw SEGS B.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
(* the allocator model's laws, the meter's laws and the meter across set_fs *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
(* the side stack for frames: frame_alloc_3's contract (S00), its release law and the flag law (S21) *)
Hypothesis SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* the runtime entries: malloc (S01, S04), free (S05, S07, S16 .. S19), memchr (S04), strrchr (S14), the checked
   memcpy (S05, S13, S14, S15) and memset (S05, S13), strlen (S11), strcmp (S15), calloc at its stack window cstk (S02,
   S11, S12), snprintf at its image numbers snp_lo snp_hi snp_cr (S05, S11; interface row 4, with the five facts on
   them the S05 walk states and the S11 / S12 walk takes four of), meta_fill_f5 (S21) *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B memchr_loA memchr_hiA (SIG SS___interceptor_trampoline_memchr).
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strrchr).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
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
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_f5) 0xf5.
(* the program callees' contracts, at the listing's entry and window of each (S03; S05; S06; S07; S09; S10; S11; S16) *)
Hypothesis HINIT : forall fx0 : YK11.FPState,
  @reac_segconf_init_contract fx0 rc SK SEGS B (BASE + AF_reac_segconf_init) STK_reac_segconf_init.
Hypothesis HCR : forall fx0 : YK11.FPState, @check_refusals_contract fx0 rc SK SEGS B (BASE + AF_check_refusals)
  STK_check_refusals.
Hypothesis HCA : forall fx0 : YK11.FPState,
  @check_address_contract fx0 rc SK SEGS B (BASE + AF_check_address) STK_check_address RLO_A RHI_A.
Hypothesis HCK : forall fx0 : YK11.FPState,
  @check_knock_refused_contract fx0 rc SK SEGS B (BASE + AF_check_knock_refused) STK_check_knock_refused
    RLO_A RHI_A seg_litA_fz gotwA guardA.
Hypothesis HDECL : forall fx0 : YK11.FPState,
  @reac_segconf_declared_c.reac_segconf_declared_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_declared) STK_reac_segconf_declared RLO_A RHI_A gotwA guardA.
Hypothesis HCHKD : forall fx0 : YK11.FPState,
  @check_declared_c.check_declared_contract fx0 rc SK SEGS B
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
  reac_segconf_ignore_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignore_file)
    STK_reac_segconf_ignore_file RLO_A RHI_A.
Hypothesis HCPROV : forall fx0 : YK11.FPState,
  check_provenance_contract (fx := fx0) SEGS B (BASE + AF_check_provenance) STK_check_provenance RLO_A RHI_A.
Hypothesis HPARSE : forall fx0 : YK11.FPState, @reac_segconf_parse_c.reac_segconf_parse_contract fx0 rc SK SEGS B
  (BASE + AF_reac_segconf_parse) STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  m_file_c.m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract (fx := fx0) SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc SK SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc SK SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
Hypothesis MREF : forall fx0 : YK11.FPState,
  m_refuse_contract (fx := fx0) SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz gotwA guardA.

Theorem pb_LLVMFuzzerTestOneInput :
  LLVMFuzzerTestOneInput_contract SEGS B MT (BASE + AF_LLVMFuzzerTestOneInput) STK_LLVMFuzzerTestOneInput emptyA
    RLO_A RHI_A longlA mod40A catA wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc.
Proof using All.
(* the S09 walk's premise LAWS is the kit's theorem; the S03 walk takes reac_segconf_init's contract at its call
   target, which is HINIT's listing entry by SIGP (the call target of every program function is BASE + seg_af s) *)
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
assert (HINIT' : forall fx0 : YK11.FPState,
  @reac_segconf_init_contract fx0 rc SK SEGS B (SIG SS_reac_segconf_init) STK_reac_segconf_init).
{ intros fx0.
  rewrite (SIGP SS_reac_segconf_init ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_reac_segconf_init) with AF_reac_segconf_init by (vm_compute; reflexivity).
  exact (HINIT fx0). }
(* each closed segment at every FP state, from its lemma at that state *)
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
assert (H06 : forall fx1 : YK11.FPState, lt_seg_S06_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L16.lt_seg_S06 fx1); lt_close).
(* the S07 / S08 walk takes the FP state last (its Sections put fx after the hypotheses): eapply finds it from the
   goal *)
assert (H07 : forall fx1 : YK11.FPState, lt_seg_S07_stmt (fx := fx1) B MT)
  by (intros fx1; eapply L17.lt_seg_S07; lt_close).
assert (H08 : forall fx1 : YK11.FPState, lt_seg_S08_stmt (fx := fx1) B MT)
  by (intros fx1; eapply L17.lt_seg_S08; lt_close).
assert (H09 : forall fx1 : YK11.FPState, lt_seg_S09_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L18.lt_seg_S09 fx1); lt_close).
assert (H10 : forall fx1 : YK11.FPState, lt_seg_S10_stmt (fx := fx1) B MT)
  by (intros fx1; eapply (@L19.lt_seg_S10 fx1); lt_close).
(* the S11 / S12 walk states its lemmas at every FP state (no fx in its Section): eapply finds the image numbers by
   the hypotheses that name them *)
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
