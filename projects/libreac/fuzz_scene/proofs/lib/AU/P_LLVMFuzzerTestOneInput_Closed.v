(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the CLOSED walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput in the ASAN-UBSAN
   build (lib/AU).  Rule 24: this file proves no function.  It is a composition of proved lemmas only. *)

(* This file's theorem is  scene_llvmf_closed : scene_llvmf_stmt B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY

   proved in a Section h that repeats every Variable, Context and Hypothesis line of the Section h of the statement
   of record (lib/AU/P_LLVMFuzzerTestOneInput.v, a working branch c0ad992d3c8) word for word, as that
   file's header asks ("the walk `scene_llvmf : scene_llvmf_stmt`, proved in Section h under its hypotheses").  So,
   outside the Section, the theorem's only premises are hypotheses of the statement's own Section h: the 29 that the
   seven segments use.  The other five (HRA_LLVMF, HA_EMPTY, HRO_PL, FFL, HB_C_PL) no segment lemma takes, so Rocq
   does not make them premises when the Section closes.

   THE PROOF.  lib/AU/P_LLVMFuzzerTestOneInput_Top.v (a working branch 96638cf4b1c) proves
   `scene_llvmf` from seven Section hypotheses HS0 .. HS6, the segment statements of
   lib/AU/P_LLVMFuzzerTestOneInput_seg.v at Top's sink head `top_sink_head` and Top's walk `scene_walk_asan_ubsan`.
   Each `au_plug_Sx` below discharges HSx with the proved segment lemma, applied to Section h hypotheses, to
   `eq_refl` for the ruled pair HWRLO / HWRHI (the walk's sw_rlo / sw_rhi fields are the listing's, Top.v:96), and,
   for S2's HWKev only, to the bridge `s2_hwkev_of_hev`.  The segments' own sink heads and walks are the same
   record values as Top's (0x5f7190; the same eleven walk fields), so the kernel converts between them.

     S0 a working branch   8b9208d286e  P_LLVMFuzzerTestOneInput_S0.llvmf_S0
     S1 a working branch   0daa1a51ade  P_LLVMFuzzerTestOneInput_S1.llvmf_S1
     S2 a working branch   729b9b9d254  P_LLVMFuzzerTestOneInput_S2.seg_S2
     S3 a working branch   67cd72b99e4  P_LLVMFuzzerTestOneInput_S3.scene_seg_S3_turn_au
     S4 a working branch   3dfbc0d1cf5  P_LLVMFuzzerTestOneInput_S4.scene_seg_S4_au
     S5 a working branch   2691a72bbce  P_LLVMFuzzerTestOneInput_S5.seg_S5_au
     S6 a working branch   8af5cd1029c  P_LLVMFuzzerTestOneInput_S6.llvmf_S6

   SINK HEADS (gate 6h).  No sink head is found by instance search here.  The statement's head
   `scene_sink_head` (statement :165) is named in every Section h row that takes one (RO, BSS, SSB, SSM, TCHECKX),
   as the statement names it; Top's `top_sink_head` (Top.v:156) is passed by name to every segment statement and
   to every segment lemma whose head is a parameter (S0, S1, S2, S4, S6).  S3 and S5 fix the head themselves
   (S3.v:142, S5.v:35), at the same record value.

   FILE ORDER.  The statement's own Require header comes first, line for line with its comments left out
   (statement :81-133), so every short name of the Section h text below resolves as it does in the statement file.
   The segment files are Required without Import and named qualified, so no short name of theirs (S3's and S5's
   `scene_sink_head`) reaches the Section h text. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require SceneAsanBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx J_StackSz.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_reac_ctrl_build_scene_step P_reac_ctrl_scene_build P_reac_ctrl_scene_set_mac.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step P_check_step_cut.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Sink.
(* the segment statements, the statement of record and the top composition, in Top.v's own order *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_seg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_Top.
(* the seven proved segment lemmas: Required, never Imported (FILE ORDER above) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require
P_LLVMFuzzerTestOneInput_S0 P_LLVMFuzzerTestOneInput_S1 P_LLVMFuzzerTestOneInput_S2 P_LLVMFuzzerTestOneInput_S3
P_LLVMFuzzerTestOneInput_S4 P_LLVMFuzzerTestOneInput_S5 P_LLVMFuzzerTestOneInput_S6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the one bridge.  S2 states its event budget in a lane-local form, `HWKev : 1 <= sw_ev WK`
   (S2.v:318: the one allocator event M1 counted at C2), which is weaker than the statement's HEV
   (`LLVMF_EV <= EV_LIB`, LLVMF_EV = 6, statement :143, :203).  With sw_ev of Top's walk = EV_LIB (Top.v:93), this
   lemma turns HEV into HWKev.  It is closed: no Section variable is in its goal. ---- *)
Lemma s2_hwkev_of_hev : forall ev : Z, LLVMF_EV <= ev -> 1 <= ev.
Proof. intros ev H. unfold LLVMF_EV in H. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the statement's own Section d notations (statement :167-172), word for word *)
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ scene_listing PI_scene).
#[local] Notation RHI := (@pa_relro_hi _ scene_listing PI_scene).

(* ==== the statement's Section h (statement :180-306 at c0ad992d3c8): every Variable, Context and Hypothesis line
   word for word, its comments left out.  Its two Definitions TT_SHCELLS / PL_SHCELLS and the walk statement
   scene_llvmf_stmt are the statement's own constants and are not restated. ==== *)
Section h.
Variable B : asyms.
Variables A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z.
Context {RO : ro_below_ofl (SK := scene_sink_head) SEGS RLO RHI}.

Hypothesis HA_LLVMF : A_LLVMF = BASE + AF_LLVMFuzzerTestOneInput.
Hypothesis HRA_LLVMF : RA_LLVMF = 0x827a0.
Hypothesis HA_EMPTY : A_EMPTY = 0x5d6160.
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

Hypothesis BSS : treac_ctrl_build_scene_step_spec (SK := scene_sink_head) (PI := PI_scene) B.
Hypothesis SSB : treac_ctrl_scene_build_spec (SK := scene_sink_head) (PI := PI_scene) B.
Hypothesis SSM : treac_ctrl_scene_set_mac_spec (SK := scene_sink_head) (PI := PI_scene) B.
Hypothesis TCHECKX : tcheck_step_specX scene_sink_head B.

Hypothesis HTRACE : rt_trace_in_stmt SEGS RA_LLVMF (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
RT_malloc1_ra RT_malloc2_ra RT_malloc3_ra RT_free1_ra RT_free2_ra RT_free3_ra (as_universe B).
(* ==== end of the statement's Section h ==== *)

(* Top's walk at this Section's entry constants (Top.v:170-171). *)
#[local] Notation WKAU := (scene_walk_asan_ubsan A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY).

(* ---- HS0 .. HS6 of Top.v:176-188, each the segment lemma applied.  The type of each is Top's hypothesis text. ---- *)
(* S0: SM8 (S0.v:302) is stack_malloc_8_sz by conversion (SIGMA SS___asan_stack_malloc_8 = PC_STACK_MALLOC_8 =
   0x3f438, CID8 = 8); HENTRY is HA_LLVMF (sw_entry = A_LLVMF). *)
Lemma au_plug_S0 : seg_S0_stmt (SK := top_sink_head) scene_segs B scene_mt WKAU scene_geom_asan_ubsan.
Proof.
exact (@P_LLVMFuzzerTestOneInput_S0.llvmf_S0 fx rc top_sink_head B WKAU
  ML TL TLF stack_malloc_8_sz ASHF8 HSTK HA_LLVMF eq_refl eq_refl).
Qed.

(* S1: HTRACE's six return addresses are RT_*_ra unfolded; HZS_PL is the statement's with
   A_reac_scene_placeholder = 0x20e80, LLVMF_SCENE_BYTES = 8904 unfolded. *)
Lemma au_plug_S1 : seg_S1_stmt (SK := top_sink_head) scene_segs B scene_mt WKAU scene_geom_asan_ubsan.
Proof.
exact (@P_LLVMFuzzerTestOneInput_S1.llvmf_S1 fx rc top_sink_head RO B TL ML AMALLOC WKAU
  HSTK HEV HLIVE HTRACE eq_refl eq_refl HRO_PLGOT HZS_PL).
Qed.

(* S2: HWKev from HEV through s2_hwkev_of_hev; HB_Z_TT / HB_C_TT are the statement's with A_TAIL_TRAILER,
   TAIL_TRAILER_N and TT_SHCELLS unfolded. *)
Lemma au_plug_S2 : seg_S2_stmt (SK := top_sink_head) scene_segs B scene_mt WKAU scene_geom_asan_ubsan.
Proof.
exact (@P_LLVMFuzzerTestOneInput_S2.seg_S2 fx rc top_sink_head B RO AMEMSET BSS TCHECKX
  HB_Z_TT HB_C_TT HRO_TT WKAU eq_refl eq_refl HSTK (s2_hwkev_of_hev EV_LIB HEV)).
Qed.

(* S3: its head is its own scene_sink_head (S3.v:142), the same record as top_sink_head. *)
Lemma au_plug_S3 : seg_S3_turn_stmt (SK := top_sink_head) scene_segs B scene_mt WKAU scene_geom_asan_ubsan.
Proof.
exact (@P_LLVMFuzzerTestOneInput_S3.scene_seg_S3_turn_au fx rc B WKAU
  eq_refl eq_refl HEV HB_Z_TT HB_C_TT HRO_TT RO HSTK HSTK_CS AMEMCPY BSS TCHECKX).
Qed.

Lemma au_plug_S4 : seg_S4_stmt (SK := top_sink_head) scene_segs B scene_mt WKAU scene_geom_asan_ubsan.
Proof.
exact (@P_LLVMFuzzerTestOneInput_S4.scene_seg_S4_au fx rc top_sink_head B WKAU
  RO ML TL AMALLOC AFREE ABCMP HTRACE HSTK HEV HLIVE eq_refl eq_refl).
Qed.

(* S5: its walk s5_walk (S5.v:66-70) is Top's walk at the same six constants, field for field, and its head is
   the statement's scene_sink_head (S5.v:35). *)
Lemma au_plug_S5 : seg_S5_stmt (SK := top_sink_head) scene_segs B scene_mt WKAU scene_geom_asan_ubsan.
Proof.
exact (@P_LLVMFuzzerTestOneInput_S5.seg_S5_au fx rc B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY
  RO HEV HLIVE HSTK TL ML AMALLOC AMEMSET AMEMCPY ABCMP ASH00 ASHF8 SSB SSM HTRACE).
Qed.

(* S6: AIL's range list is sw_sink of the walk = SCENE_SINK_OWNED (Top.v:171); ASF8's class is LLVMF_CID = 8. *)
Lemma au_plug_S6 : seg_S6_stmt (SK := top_sink_head) scene_segs B scene_mt WKAU scene_geom_asan_ubsan.
Proof.
exact (@P_LLVMFuzzerTestOneInput_S6.llvmf_S6 fx rc top_sink_head B WKAU
  ML TL AFREE ASF8 AIL HEV HSTK HTRACE).
Qed.

(* ---- the walk of record: Top's scene_llvmf (Top.v:190) at the seven discharged segments. ---- *)
Theorem scene_llvmf_closed : @scene_llvmf_stmt fx rc B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY.
Proof.
exact (@P_LLVMFuzzerTestOneInput_Top.scene_llvmf fx rc B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY
  au_plug_S0 au_plug_S1 au_plug_S2 au_plug_S3 au_plug_S4 au_plug_S5 au_plug_S6).
Qed.
End h.
End d.
