(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan+UBSan
   build: the module paths are this unit's lib.B, the image is the position-abstract one (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput of identb_listing), the library shape and every constant of the unit's
   relocated core are parameters of the Section, and the measured needs of this build's entry (events, live
   bytes, stack) are stated beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput.v; 99 of its 169 lines of code are new or changed and 157 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), +0x1388 .. +0x1988
   (0x81afc .. 0x820fc, 384 slots): seg_J of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v, chained from its pieces.
   The cuts and one `Prop` per piece are in lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v, the six copy loops in
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_loops_stmt.v; each piece and each loop is proved in its own file.

   The run: the width decision (j_wdec, +0x1388 .. +0x13ec); the unpoisoning of exp_nm / exp_dp and, with bad
   widths, the jump to +0x1988 (j_width); the stem (j_stem); w4 by put_dec (j_w4); the stem copy (j_stemcpy);
   the tail compare, the dash and the digits (j_w4tail, j_w4cpy); exp_dp := exp_nm (j_dpcpy); the three
   literals and the two widths of the display (j_lit1 .. j_lit3); the NUL, the memchr of the first dash and the
   capacity tests (j_fits). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
(* the pieces, each proved in its own file against the statement the prefix fixes *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
LLVMFuzzerTestOneInput_seg_J_wdec LLVMFuzzerTestOneInput_seg_J_width LLVMFuzzerTestOneInput_seg_J_stem
LLVMFuzzerTestOneInput_seg_J_w4
LLVMFuzzerTestOneInput_seg_J_stemglue
LLVMFuzzerTestOneInput_seg_J_w4tail
LLVMFuzzerTestOneInput_seg_J_dpglue LLVMFuzzerTestOneInput_seg_J_lit1glue LLVMFuzzerTestOneInput_seg_J_lit2glue
LLVMFuzzerTestOneInput_seg_J_lit3glue
LLVMFuzzerTestOneInput_seg_J_fits.
(* the copy loops, proved against lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_loops_stmt.v *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
LLVMFuzzerTestOneInput_seg_J_dpcpy LLVMFuzzerTestOneInput_seg_J_lit1 LLVMFuzzerTestOneInput_seg_J_lit2
LLVMFuzzerTestOneInput_seg_J_lit3 LLVMFuzzerTestOneInput_seg_J_stemcpy LLVMFuzzerTestOneInput_seg_J_w4cpy.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this segment's address arithmetic (shadow_addr, the
   frame's 64-byte alignment) needs it, so this file turns it back on, as lib/A/Prog/LLVMFuzzerTestOneInput_D6.v
   does. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v, in the same order; the hypotheses are the contract's own text. *)
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
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis G_SW : In (VAL (A_OBJ 7), 24) G.
Hypothesis G_PAREN : In (VAL (A_OBJ 9), 3) G.
Hypothesis G_IN : In (VAL (A_OBJ 10), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 11), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IB___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis HPD : put_dec.tput_dec_spec B.

(* seg_J: the eleven pieces and the six copy loops, chained. *)
Theorem seg_J_holds :
seg_J_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS.
Proof.
unfold seg_J_stmt. intros g pos mf nm tk dp W2 c2 HI.
eapply SRr_bind; [exact (LLVMFuzzerTestOneInput_seg_J_wdec.j_wdec B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS LAWS HSTK g pos mf nm tk dp W2 c2 HI)|].
intros W3 c3 _ H0.
eapply SRr_bind; [exact (LLVMFuzzerTestOneInput_seg_J_width.j_width B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS g pos mf nm tk dp W3 c3 H0)|].
intros W4 c4 _ [[Hwok H1] | [_ HJ]]; [| apply SRr_ret; exact HJ].
eapply SRr_bind;
[exact (LLVMFuzzerTestOneInput_seg_J_stem.j_stem B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK G HRO HIMG
  LAWS TL GM IV G_SW G_REAC g pos mf nm tk dp W4 c4 H1 Hwok)|].
intros W5 c5 _ (st & H2).
eapply SRr_bind; [exact (LLVMFuzzerTestOneInput_seg_J_w4.j_w4 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS
  LAWS HSTK HEV HPD PSIG MTL HMT0 g pos mf nm tk dp st W5 c5 H2 Hwok)|].
intros W6 c6 _ H3.
eapply SRr_bind;
[exact (LLVMFuzzerTestOneInput_seg_J_stemglue.j_stemcpy_glue B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS LAWS
  (LLVMFuzzerTestOneInput_seg_J_stemcpy.j_stemcpy B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
   asink_syms_T KS asink_none ameta_inv arodata_okS)
  g pos mf nm tk dp st W6 c6 H3 Hwok)|].
intros W7 c7 _ H4.
eapply SRr_bind;
[exact (LLVMFuzzerTestOneInput_seg_J_w4tail.j_w4tail B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS LAWS ABCMP HSTK
  (LLVMFuzzerTestOneInput_seg_J_w4cpy.j_w4cpy B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
   asink_syms_T KS asink_none ameta_inv arodata_okS)
  g pos mf nm tk dp W7 c7 H4 Hwok)|].
intros W8 c8 _ H5.
eapply SRr_bind;
[exact (LLVMFuzzerTestOneInput_seg_J_dpglue.j_dpcpy_glue B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS LAWS
  (LLVMFuzzerTestOneInput_seg_J_dpcpy.j_dpcpy B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
   asink_syms_T KS asink_none ameta_inv arodata_okS)
  g pos mf nm tk dp W8 c8 H5 Hwok)|].
intros W9 c9 _ H6.
eapply SRr_bind;
[exact (LLVMFuzzerTestOneInput_seg_J_lit1glue.j_lit1_glue B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS G HRO HIMG AJ_NIL_IO
  LAWS HSTK HEV HPD PSIG MTL HMT0 GM G_PAREN
  (LLVMFuzzerTestOneInput_seg_J_lit1.j_lit1 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
   asink_syms_T KS asink_none ameta_inv arodata_okS)
  g pos mf nm tk dp W9 c9 H6 Hwok)|].
intros W10 c10 _ H7.
eapply SRr_bind;
[exact (LLVMFuzzerTestOneInput_seg_J_lit2glue.j_lit2_glue B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS G HRO HIMG
  LAWS HSTK HEV HPD PSIG MTL HMT0 GM G_IN
  (LLVMFuzzerTestOneInput_seg_J_lit2.j_lit2 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
   asink_syms_T KS asink_none ameta_inv arodata_okS)
  g pos mf nm tk dp W10 c10 H7 Hwok)|].
intros W11 c11 _ H8.
eapply SRr_bind;
[exact (LLVMFuzzerTestOneInput_seg_J_lit3glue.j_lit3_glue B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS G HRO HIMG
  LAWS GM G_OUT
  (LLVMFuzzerTestOneInput_seg_J_lit3.j_lit3 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
   asink_syms_T KS asink_none ameta_inv arodata_okS)
  g pos mf nm tk dp W11 c11 H8 Hwok)|].
intros W12 c12 _ H9.
exact (LLVMFuzzerTestOneInput_seg_J_fits.j_fits B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HRO
  LAWS AMEMCHR HSTK g pos mf nm tk dp W12 c12 H9 Hwok).
Qed.

(* seg_J of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v, with the contract's own hypotheses. *)
Theorem seg_J : seg_J_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof. exact seg_J_holds. Qed.
Check (seg_J : seg_J_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
Print Assumptions seg_J.

End c.
End b.
End a.
