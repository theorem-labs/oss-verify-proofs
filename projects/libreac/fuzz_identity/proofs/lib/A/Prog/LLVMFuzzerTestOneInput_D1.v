(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v; 58 of its 118 lines of code are new or changed and 1020 lines of the source are left out. *)
(* Segment D1 of LLVMFuzzerTestOneInput's ASan walk: one record, 0x80b20..0x80d04.
   seg_D1 of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v: from the loop head inv_rec to inv_D1_end.
   The cut into ten phases, their shared predicates and the phases' statements are LLVMFuzzerTestOneInput_D1cut.v.
   The phases are proved in their own files: Ph1 _D1p1.v, Ph2 + Ph3 _D1p23.v, Ph4 + Ph8 _D1p48.v (the two
   reac_identity_ingest calls), Ph5 + Ph6 _D1p56.v, Ph7 + Ph9 _D1p79.v, Ph10 _D1p10.v. This file composes them.
   Every abort branch is decided by the plain model or a malloc result; every __asan_report branch is refuted by a
   shadow fact; no path ends at, or reaches, a report call. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g YK0w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv reac_identity_ingest.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_D1cut
  LLVMFuzzerTestOneInput_D1p1 LLVMFuzzerTestOneInput_D1p10 LLVMFuzzerTestOneInput_D1p48 LLVMFuzzerTestOneInput_D1p79
  LLVMFuzzerTestOneInput_D1p56 LLVMFuzzerTestOneInput_D1p23 LLVMFuzzerTestOneInput_D1p3.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the shadow arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* What this segment takes, each with the name and type the contract's Section gives it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
(* The allocator call traces (LLVMFuzzerTestOneInput.v, the contract's text). *)
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
(* the program callee (lib/A/Prog/reac_identity_ingest.v) *)
Hypothesis HING : treac_identity_ingest_spec B.
(* the cut file's predicates and facts, with this Section's parameters *)
#[local] Notation CTX := (D1ctx B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation RUNS := (D1S B MT LLVMF_STK).


(* ---- the segment from its phases ----------------------------------------------------------------------------- *)
#[local] Notation STMT X := (X B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS) (only parsing).
Lemma d1_compose :
  STMT d1_ph2_stmt -> STMT d1_ph3_stmt -> STMT d1_ph4_stmt -> STMT d1_ph5_stmt ->
  STMT d1_ph6_stmt -> STMT d1_ph7_stmt -> STMT d1_ph8_stmt -> STMT d1_ph9_stmt ->
  STMT seg_D1.
Proof.
intros H2 H3 H4 H5 H6 H7 H8 H9.
unfold seg_D1. intros g pos mf i W2 c2 HI.
unfold inv_rec, acut in HI.
destruct HI as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & MLE & MOK & HEC & Hi & R20 & R21 & R24 & HRL).
assert (HC : CTX g pos mf i ly2 S2 W2 regs2 mem2 md2)
  by exact (conj HJ (conj Hfr (conj Hk (conj MLE (conj MOK (conj HEC (conj Hi (conj R20 (conj R21 (conj R24 HRL)))))))))).
eapply SRr_bind; [eapply d1_ph1; eassumption|].
intros W3 c3 _ (pl & S1).
eapply SRr_bind; [exact (H2 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3 HC S1)|]. intros W4 c4 _ S2'.
eapply SRr_bind; [exact (H3 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W4 c4 HC S2')|]. intros W5 c5 _ S3.
eapply SRr_bind; [exact (H4 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W5 c5 HC S3)|]. intros W6 c6 _ S4.
eapply SRr_bind; [exact (H5 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W6 c6 HC S4)|]. intros W7 c7 _ (gb & S5).
eapply SRr_bind; [exact (H6 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W7 c7 HC S5)|]. intros W8 c8 _ S6.
eapply SRr_bind; [exact (H7 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W8 c8 HC S6)|]. intros W9 c9 _ S7.
eapply SRr_bind; [exact (H8 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W9 c9 HC S7)|]. intros W10 c10 _ S8.
eapply SRr_bind; [exact (H9 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W10 c10 HC S8)|]. intros W11 c11 _ S9.
eapply SRr_mono; [eapply d1_ph10; eassumption|].
intros W' c' _ HQ. exists pl. exact HQ.
Qed.

(* The ten phases, each proved in its own file: Ph1 _D1p1.v, Ph2 _D1p23.v, Ph3 _D1p3.v, Ph4 and Ph8 _D1p48.v,
   Ph5 and Ph6 _D1p56.v, Ph7 and Ph9 _D1p79.v, Ph10 _D1p10.v. *)
Theorem seg_D1_holds : STMT seg_D1.
Proof.
apply d1_compose.
- eapply d1_ph2; eassumption.
- eapply d1_ph3; eassumption.
- eapply d1_ph4; eassumption.
- eapply d1_ph5; eassumption.
- eapply d1_ph6; eassumption.
- eapply d1_ph7; eassumption.
- eapply d1_ph8; eassumption.
- eapply d1_ph9; eassumption.
Qed.

End c.
End b.
End a.
