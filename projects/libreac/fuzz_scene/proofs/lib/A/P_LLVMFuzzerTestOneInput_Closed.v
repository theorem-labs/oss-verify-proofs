(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: THE CLOSING of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput.
   rule 24: no function proved (kind: merge).  This file proves no segment and no callee. *)

(* This file proves  scene_llvmf_closed : scene_llvmf_stmt B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY

   under ONLY lib/A/P_LLVMFuzzerTestOneInput.v's Section h (statement of record a working branch
   f6ab6e97937; copied below in its text).  Four Section h hypotheses are used by no segment proof and drop out
   when the section closes: HRA_LLVMF, HRO_PL, HB_C_PL and FFL.  The proof applies
   P_LLVMFuzzerTestOneInput_Plug.scene_llvmf_plug (S1 .. S6 plugged into the composition, open on HS0 alone; this
   branch) and discharges HS0 with P_LLVMFuzzerTestOneInput_S0.scene_seg_S0 (a working branch
   67f0c71b18d), at the statement's own sink head P_LLVMFuzzerTestOneInput.scene_sink_head, passed by name
   (gate 6h).

   S0's premises (P_LLVMFuzzerTestOneInput_S0.v Section e; FFL, :186, is declared there but unused by the proof, so
   scene_seg_S0 does not take it) and how each is discharged:
     TL, TLF, ML, stack_malloc_8_sz, ASHF8   the Section h hypotheses of the same name, same text.
     HWRLO / HWRHI   sw_rlo / sw_rhi of scene_walk_asan are pa_relro_lo / pa_relro_hi: eq_refl.
     HWENT  sw_entry WK = BASE + AF_LLVMFuzzerTestOneInput: HA_LLVMF (sw_entry of the walk is A_LLVMF).
     HWEMP  4096 <= sw_empty WK <= 140737479966720: HA_EMPTY (A_EMPTY = 0x5d5e60) and lia.
     HWSTK  240 + ASTACK <= sw_stk WK: HSTK (LLVMF_SPDROP := 240).

   FILE ORDER as P_LLVMFuzzerTestOneInput_Plug.v: every Require first; no short name of YI16 / lib_shape / LIBK /
   LL is written after them.

   BUILD RECIPE: the Plug's (P_LLVMFuzzerTestOneInput_Plug.v header), with the statement files at f6ab6e97937
   (`git checkout f6ab6e97937 -- proofs/libreac/fuzz_scene` after the 7687b78416d3 overlay) and
   lib/A/P_LLVMFuzzerTestOneInput_S0.v from 67f0c71b18d by path.  S0 alone compiles in about 2.3 h. *)
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
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require P_LLVMFuzzerTestOneInput_S0 P_LLVMFuzzerTestOneInput_Plug.
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

(* ---- lib/A/P_LLVMFuzzerTestOneInput.v's Section h (:166-301 at f6ab6e97937), in its own text and order; BSS,
   SSB and SSM take the sink head by name, as the statement writes them. ---- *)
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

Theorem scene_llvmf_closed : scene_llvmf_stmt B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY.
Proof.
(* S0's two walk premises that are not a Section h hypothesis up to conversion *)
assert (HWENT : sw_entry WKA = BASE + AF_LLVMFuzzerTestOneInput) by exact HA_LLVMF.
assert (HWEMP : 4096 <= sw_empty WKA <= 140737479966720)
  by (change (sw_empty WKA) with A_EMPTY; rewrite HA_EMPTY; lia).
assert (HS0 : seg_S0_stmt (SK := SKS) SSEGS B SMT WKA scene_geom_asan).
{ eapply (@P_LLVMFuzzerTestOneInput_S0.scene_seg_S0 fx rc SKS B).
  all: first [ assumption | reflexivity ]. }
exact (@P_LLVMFuzzerTestOneInput_Plug.scene_llvmf_plug fx rc B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY
  RO HEV HLIVE HSTK HSTK_CS HRO_TT HRO_PLGOT TL ML AIL HZS_PL HB_Z_TT HB_C_TT
  AMALLOC AFREE AMEMSET AMEMCPY ABCMP ASF8 ASH00 ASHF8 BSS SSB SSM TCHECKX HTRACE HS0).
Qed.
End h.
End d.
