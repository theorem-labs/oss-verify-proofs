(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: THE PLUG of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput.
   rule 24: no function proved (kind: merge).  This file proves no segment and no callee: it applies the top
   composition `llvmf_compose` (lib/A/P_LLVMFuzzerTestOneInput_Top.v:94) at scene's own instance and discharges six
   of its seven segment premises with the proved segment theorems, each at the statement's Section h. *)

(*     scene_llvmf_plug : scene_llvmf_stmt B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY

   under the hypotheses of lib/A/P_LLVMFuzzerTestOneInput.v's Section h (copied below in its text; a hypothesis the
   proof does not use drops out when the section closes) and ONE more: HS0, the composition's S0 premise, in the
   form lib/A/P_LLVMFuzzerTestOneInput_Top.v:167 states it.

   INSTANCE.  segs := scene_segs (= PI_scene's pa_segs), meter := scene_mt (= ameter_triv), walk := scene_walk_asan
   (Top.v:161, i.e. scene_walk (Top.v:82-87) at SCENE_SINK_OWNED and the six entry constants, sw_xm = sw_xn = 0,
   sw_rlo / sw_rhi = PI_scene's pa_relro_lo / pa_relro_hi), geometry := scene_geom_asan, shape :=
   SceneAsanBase.scene_shape (the statement's, P_LLVMFuzzerTestOneInput.v:152, :307).  The sink head is the
   statement's own constant P_LLVMFuzzerTestOneInput.scene_sink_head (:150-151, type written fully qualified there),
   passed BY NAME to every lemma that takes one (gate 6h); its local instance below only mirrors the statement's
   own `#[local] Instance` (:150), so that the copied hypotheses elaborate as they do there.

   THE SEGMENT THEOREMS (each Qed; Print Assumptions = kernel primitives + functional_extensionality_dep):
     S1  P_LLVMFuzzerTestOneInput_S1.scene_seg_S1  :1032  a working branch 7b2b57c5429
     S2  P_LLVMFuzzerTestOneInput_S2.seg_S2        :225   a working branch 6e3cac2c3e1 (+ S2AluLemmas.v, a28950bc27b)
     S3  P_LLVMFuzzerTestOneInput_S3.scene_seg_S3  :1921  a working branch 4cf034be9d6
     S4  P_LLVMFuzzerTestOneInput_S4.scene_S4      :1936  a working branch 2172fd006fc
     S5  P_LLVMFuzzerTestOneInput_S5.scene_seg_S5  :135   a working branch 3a1b22cbd21 (+ _S5_kit.v, J_StackSzPf.v)
     S6  P_LLVMFuzzerTestOneInput_S6.llvmf_S6      :134   a working branch 28719c5598c
   S3 is ONE whole_transfer turn, `seg_S3_turn_stmt`, which is exactly the composition's HS3 (Top.v:173,
   seg.v:592-595); the 343-turn induction is inside S4 (`s4_loop`), whose statement takes the turn as its second
   premise (seg.v:601-603), and llvmf_compose feeds HS3 there (Top.v:125).  No bridge lemma is needed.

   HOW EACH SEGMENT PREMISE IS DISCHARGED (statement = lib/A/P_LLVMFuzzerTestOneInput.v at 0b6bed94801, whose Section
   h c0ad992d3c8 changes only by writing (SK := scene_sink_head) in BSS / SSB / SSM, as this file already does, at
   the same lines; segment lines are the segment file's).  Only the premises a segment theorem keeps after its
   section closes are listed (its `About`); every one is the statement's hypothesis itself, accepted up to
   conversion, except HWKev (derived by lia) and HWRLO / HWRHI (eq_refl).
     RO      (S1 :74, S2 :97, S3 :186, S5 :105)  statement RO :175, the same proposition at SK := scene_sink_head.
     TL, ML  (S1 :76/:78, S4 :464-465, S5 :106/:108, S6 :105-106)   statement TL :223, ML :225 verbatim.
     AMALLOC (S1 :80, S4 :466, S5 :109), AFREE (S4 :467, S6 :107), AMEMSET (S2 :101, S5 :110),
     AMEMCPY (S3 :214, S5 :111), ABCMP (S4 :468, S5 :112), ASH00 / ASHF8 (S5 :113-114), SSB / SSM (S5 :115-116),
     BSS (S2 :102, S3 :215), TCHECKX (S2 :103, S3 :216)
                                                  statement :271-276, :283-284, :289-293 verbatim; SK by name.
     ASF8    (S6 :108, class 8)                   statement ASF8 :282 at LLVMF_CID; LLVMF_CID := 8 (:119).
     AIL     (S6 :109, at sw_sink WK)             statement AIL :232 at SCENE_SINK_OWNED = sw_sink of the walk.
     HEV     (S1 :128, S3 :196, S4 :471, S5 :119, S6 :110: 6 <= sw_ev WK)
                                                  statement HEV :189; LLVMF_EV := 6, sw_ev of the walk = EV_LIB.
     HWKev   (S2 :126: 1 <= sw_ev WK)             DERIVED: from statement HEV by lia (6 <= EV_LIB).
     HLIVE   (S1 :129, S3 :197, S4 :472, S5 :120: 2 * 65535 <= sw_live WK)
                                                  statement HLIVE :190; LLVMF_NMAX := 65535.
     HSTK    (S1 :127, S2 :123, S3 :194, S4 :473, S5 :121, S6 :111: 240 + ASTACK <= sw_stk WK)
                                                  statement HSTK :191; LLVMF_SPDROP := 240.
     HSTK_CS (S3 :195)                            statement HSTK_CS :192; LLVMF_SPDROP := 240.
     HWRLO / HWRHI (S1 :309-310, S2 :121-122, S3 :200-201, S4 :478-480, S5 :122-123)
                                                  NOT in the statement: eq_refl, scene_walk's sw_rlo / sw_rhi.
     HTRACE  (S1 :130-133, S4 :483-486, S5 :124-127, S6 :112-115; at sw_ra WK and literal offsets)
                                                  statement HTRACE :300-301 at RA_LLVMF and RT_*_ra (:159-164):
                                                  RT_malloc1_ra := BASE + AF_LLVMFuzzerTestOneInput + 0x328 etc.;
                                                  S4 writes BASE + 0x328 (AF_LLVMFuzzerTestOneInput = 0).
     HOWN_PLGOT (S1 :317-318)                     statement HRO_PLGOT :217-218, the same text.
     HZS_PL  (S1 :342, s1_PL / s1_PLN)            statement HZS_PL :263; s1_PL := 0x20e80, s1_PLN := 8904 (S1 :241-242).
     HB_Z_TT / HB_C_TT (S2 :108-111 literals; S3 :207-208 over its own copies :79-83)
                                                  statement HB_Z_TT :265, HB_C_TT :266; A_TAIL_TRAILER := 0x20e20,
                                                  TAIL_TRAILER_N := 12, TT_SHCELLS (:258-260) has the same body.
     HRO_TT  (S2 :115-116, S3 :211-212)           statement HRO_TT :204-205 verbatim.
   Declared in a segment section but not used by its proof, so not passed: TLF / FFL (S1 :77/:79, S3 :190-191),
   TL / ML (S2 :98/:100, S3 :187/:189).  No premise of a proved segment is missing from the statement.  Section h
   hypotheses no proved segment uses, which therefore drop out of scene_llvmf_plug's type: HA_LLVMF, HRA_LLVMF,
   HA_EMPTY, HRO_PL, TLF, FFL, HB_C_PL, stack_malloc_8_sz.

   FILE ORDER.  lib/A/P_LLVMFuzzerTestOneInput.v pulls in lib/SceneAsanBase.v, and lib/A/G_Sink.v (Required by the
   statement and by S6) pulls in lib/Reusable/SinkGuard.v and through it lib/U/Reusable modules; after either, the
   short names YI16.sink_head / YI16.sk_ofl_head (and lib_shape, LIBK, LL: Top.v:46-50) can resolve to the lib/U
   twins.  This file is Required after all of them and writes none of those names: the sink head is the
   statement's own constant, by its full name, and the shape's leaf equation is closed by reflexivity without
   being written.

   BUILD RECIPE (scene's base does not build standalone): clone at the statement of record f6ab6e97937;
   `git checkout 7687b78416d3 -- proofs/libreac/fuzz_scene && git checkout f6ab6e97937 -- proofs/libreac/fuzz_scene`;
   then by path the segment files above and lib/A/P_LLVMFuzzerTestOneInput_Top.v (a working branch f4279258d43). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require SceneAsanBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx J_StackSz.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_reac_ctrl_build_scene_step P_reac_ctrl_scene_build P_reac_ctrl_scene_set_mac.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step P_check_step_cut.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import G_Sink.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_seg P_LLVMFuzzerTestOneInput.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require
P_LLVMFuzzerTestOneInput_S1 P_LLVMFuzzerTestOneInput_S2 P_LLVMFuzzerTestOneInput_S3 P_LLVMFuzzerTestOneInput_S4
P_LLVMFuzzerTestOneInput_S5 P_LLVMFuzzerTestOneInput_S6 P_LLVMFuzzerTestOneInput_Top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the statement's own sink head (P_LLVMFuzzerTestOneInput.v:150-151), by its full name *)
#[local] Notation SKS := OSSVerify.Proofs.libreac.fuzz_scene.lib.A.P_LLVMFuzzerTestOneInput.scene_sink_head.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance OSSVerify.Proofs.libreac.fuzz_scene.lib.A.P_LLVMFuzzerTestOneInput.scene_sink_head.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ scene_listing PI_scene).
#[local] Notation RHI := (@pa_relro_hi _ scene_listing PI_scene).

(* ---- lib/A/P_LLVMFuzzerTestOneInput.v's Section h (:166-301), in its own text and order; BSS, SSB and SSM take
   the sink head by name, as c0ad992d3c8 writes them. ---- *)
Section h.
Variable B : asyms.
Variables A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z.
Context {RO : ro_below_ofl (SK := SKS) SEGS RLO RHI}.
Hypothesis HA_LLVMF : A_LLVMF = BASE + AF_LLVMFuzzerTestOneInput.
Hypothesis HRA_LLVMF : RA_LLVMF = 0x82774.
Hypothesis HA_EMPTY : A_EMPTY = 0x5d5e60.
Hypothesis HEV : LLVMF_EV <= EV_LIB.
Hypothesis HLIVE : 2 * LLVMF_NMAX <= LIVE_LIB.
Hypothesis HSTK : LLVMF_SPDROP + ASTACK <= LLVMF_STK.
Hypothesis HSTK_CS : LLVMF_SPDROP + TCHECK_STEP_STK <= LLVMF_STK.
Hypothesis HRO_TT : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x20e20 + i < as_errno B + 4).
Hypothesis HRO_PL : forall i, 0 <= i < LLVMF_SCENE_BYTES ->
  ~ Exists (in_zr (A_reac_scene_placeholder + i)) (as_owned_static B) /\
  ~ (as_errno B <= A_reac_scene_placeholder + i < as_errno B + 4).
Hypothesis HRO_PLGOT : forall i, 0 <= i < 8 ->
  ~ Exists (in_zr (VAL (A_OBJ 4) + i)) (as_owned_static B) /\ ~ (as_errno B <= VAL (A_OBJ 4) + i < as_errno B + 4).
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI_scene) B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AIL : sink_img_laws SEGS B SCENE_SINK_OWNED.
Hypothesis HZS_PL : in_zs B A_reac_scene_placeholder LLVMF_SCENE_BYTES.
Hypothesis HB_C_PL : forall ly, Forall (fun c => In c (as_const B ly)) PL_SHCELLS.
Hypothesis HB_Z_TT : in_zs B (A_TAIL_TRAILER - 0x20) (0x20 + (TAIL_TRAILER_N - TAIL_TRAILER_N mod 8)).
Hypothesis HB_C_TT : forall ly, Forall (fun c => In c (as_const B ly)) TT_SHCELLS.
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Hypothesis stack_malloc_8_sz : astack_malloc_sz_realizes SEGS B PC_STACK_MALLOC_8 CID8.
Hypothesis ASF8 : StackFreeDef.astack_free_realizes SEGS B (SIGMA SS___asan_stack_free_8) LLVMF_CID.
Hypothesis ASH00 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
Hypothesis BSS : treac_ctrl_build_scene_step_spec (SK := SKS) (PI := PI_scene) B.
Hypothesis SSB : treac_ctrl_scene_build_spec (SK := SKS) (PI := PI_scene) B.
Hypothesis SSM : treac_ctrl_scene_set_mac_spec (SK := SKS) (PI := PI_scene) B.
Hypothesis TCHECKX : tcheck_step_specX SKS B.
Hypothesis HTRACE : rt_trace_in_stmt SEGS RA_LLVMF (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
RT_malloc1_ra RT_malloc2_ra RT_malloc3_ra RT_free1_ra RT_free2_ra RT_free3_ra (as_universe B).

(* ---- the composition's instance (P_LLVMFuzzerTestOneInput_Top.v:79-87, :161-162) ---- *)
#[local] Notation WKA := (P_LLVMFuzzerTestOneInput_Top.scene_walk_asan A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY).
#[local] Notation SSEGS := P_LLVMFuzzerTestOneInput_Top.scene_segs.
#[local] Notation SMT := P_LLVMFuzzerTestOneInput_Top.scene_mt.

(* ---- the one segment this file leaves open: S0 (a Theorem Labs lane), in the composition's form (Top.v:167); P_LLVMFuzzerTestOneInput_Closed.v closes it with P_LLVMFuzzerTestOneInput_S0.v's scene_seg_S0 ---- *)
Hypothesis HS0 : seg_S0_stmt (SK := SKS) SSEGS B SMT WKA scene_geom_asan.

Theorem scene_llvmf_plug : scene_llvmf_stmt B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY.
Proof.
(* S2's HWKev is the one segment premise that is not a statement hypothesis up to conversion. *)
assert (HWKev : 1 <= sw_ev WKA)
  by (pose proof HEV as Hev; unfold LLVMF_EV in Hev; change (sw_ev WKA) with EV_LIB; lia).
assert (HS1 : seg_S1_stmt (SK := SKS) SSEGS B SMT WKA scene_geom_asan)
  by exact (@P_LLVMFuzzerTestOneInput_S1.scene_seg_S1 fx rc SKS RO B TL ML AMALLOC WKA
              HSTK HEV HLIVE HTRACE eq_refl eq_refl HRO_PLGOT HZS_PL).
assert (HS2 : seg_S2_stmt (SK := SKS) SSEGS B SMT WKA scene_geom_asan)
  by exact (@P_LLVMFuzzerTestOneInput_S2.seg_S2 fx rc SKS B RO AMEMSET BSS TCHECKX HB_Z_TT HB_C_TT HRO_TT WKA
              eq_refl eq_refl HSTK HWKev).
assert (HS3 : seg_S3_turn_stmt (SK := SKS) SSEGS B SMT WKA scene_geom_asan)
  by exact (@P_LLVMFuzzerTestOneInput_S3.scene_seg_S3 fx rc SKS B WKA RO HSTK HSTK_CS HEV HLIVE
              eq_refl eq_refl HB_Z_TT HB_C_TT HRO_TT AMEMCPY BSS TCHECKX).
assert (HS4 : seg_S4_stmt (SK := SKS) SSEGS B SMT WKA scene_geom_asan)
  by exact (@P_LLVMFuzzerTestOneInput_S4.scene_S4 fx rc SKS B WKA TL ML AMALLOC AFREE ABCMP
              HEV HLIVE HSTK eq_refl eq_refl HTRACE).
assert (HS5 : seg_S5_stmt (SK := SKS) SSEGS B SMT WKA scene_geom_asan)
  by exact (@P_LLVMFuzzerTestOneInput_S5.scene_seg_S5 fx rc SKS B RO ML TL AMALLOC AMEMSET AMEMCPY ABCMP
              ASH00 ASHF8 SSB SSM WKA HEV HLIVE HSTK eq_refl eq_refl HTRACE).
assert (HS6 : seg_S6_stmt (SK := SKS) SSEGS B SMT WKA scene_geom_asan)
  by exact (@P_LLVMFuzzerTestOneInput_S6.llvmf_S6 fx rc SKS B WKA ML TL AFREE ASF8 AIL HEV HSTK HTRACE).
unfold scene_llvmf_stmt.
refine (P_LLVMFuzzerTestOneInput_Top.llvmf_compose (LS := SceneAsanBase.scene_shape) (SK := SKS)
  SSEGS B SMT WKA scene_geom_asan _ HS0 HS1 HS2 HS3 HS4 HS5 HS6).
(* the shape's leaf equation: scene's harness does no I/O, LIBK pl fs K = K (LL 0 fs []) by construction
   (Top.v:41-44, :185-188) *)
intros pl fs K. reflexivity.
Qed.
End h.
End d.
