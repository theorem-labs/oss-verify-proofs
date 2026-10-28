(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x YI5s YI5v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACj9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7 ACj3 AChd ACj8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACif AChf AChg AChh AChi AChk AChl AChm AChn ACho AChx AChp AChs ACht AChu AChw AChv AChj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis ASM2 : astack_malloc_realizes SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMEMCMP : amemcmp_realizes SEGS B (SIGMA AS_memcmp).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA AS_memcmp_2).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable wfn : Z.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AFREEN4 : afree_null04_rule SEGS B MT.
Hypothesis HTR : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0x2448) \/ (pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0x1fd4) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0x2124)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Variable CTXR : list (list Z).
Hypothesis TRAWADDX : trawadd_specX SEGS KS B MT XN (SIGMA AS_cgif_raw_addframe) CTXR wfn pa_relro_lo pa_relro_hi.
Hypothesis HXM : forall N M, 1 <= M <= N -> N <= 100000000 -> mo_malloc MT M + xm_rawadd XN M + mo_free MT <= xm_flush XN N.
Hypothesis HXN : forall N M, 1 <= M <= N -> N <= 100000000 -> mo_malloc MT M + xn_rawadd XN M + mo_free MT <= xn_flush XN N.
Hypothesis HXMN : forall M, 1 <= M <= 100000000 -> 0 <= xn_rawadd XN M <= xm_rawadd XN M.
Hypothesis HCTXR : forall l, In l CTX -> In ((BASE + 0x243c) :: l) CTXR.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Theorem pb_flushFrameX : tflush_specX SEGS KS B MT XN (BASE + AF_asan3_flushFrame) CTX wfn pa_relro_lo pa_relro_hi.
Proof.
assert (RX : fl_fromX1 KS MT XN B CTX wfn ss_X (INV_XX KS MT XN B)) by (eapply fl_XX; eassumption).
assert (RR5 : fl_fromX1 KS MT XN B CTX wfn ss_R5 (INV_R5X KS MT XN B)) by (eapply fl_R5X; eassumption).
assert (RR4 : fl_fromX0 KS MT XN B CTX wfn ss_R4 (INV_R4X MT B)) by (eapply fl_R4X; eassumption).
assert (RR3 : fl_fromX0 KS MT XN B CTX wfn ss_R3 (INV_R3X MT B)) by (eapply fl_R3X; eassumption).
assert (RR2 : fl_fromX0 KS MT XN B CTX wfn ss_R2 (INV_R2X MT B)) by (eapply fl_R2X; eassumption).
assert (RR : fl_fromX0 KS MT XN B CTX wfn ss_R (INV_RX MT B)) by (eapply fl_R1X; eassumption).
pose proof (pb_cmpPixel B LAWS TL AMEMCMP) as TCMP.
assert (FT3 : fl_fromX0 KS MT XN B CTX wfn ss_T3 (INV_T3X MT B)) by (eapply fl_T3X; eassumption).
assert (RT1x : fl_fromX0 KS MT XN B CTX wfn ss_T1x (INV_T1xX MT B)) by (eapply fl_T2X; eassumption).
assert (FT0 : fl_fromX0 KS MT XN B CTX wfn ss_T0 (INV_T0X MT B)) by (eapply fl_T1X; eassumption).
assert (FD1 : fl_fromX0 KS MT XN B CTX wfn ss_D1 (INV_D1X MT B)) by (eapply fl_D1X; eassumption).
assert (FD : fl_fromX0 KS MT XN B CTX wfn ss_DIMS (INV_DIMSX MT B)) by (eapply fl_DX; eassumption).
assert (FDi : fl_fromX0 KS MT XN B CTX wfn ss_DIMSi (INV_DIMSiX MT B)) by (eapply fl_DiX; eassumption).
assert (FS : fl_fromX0 KS MT XN B CTX wfn ss_S (INV_SX MT B)) by (eapply fl_SX; eassumption).
assert (FFv : fl_fromX0 KS MT XN B CTX wfn ss_Fv (INV_FvX MT B)) by (eapply fl_FvX; eassumption).
assert (FDIFF : fl_fromX0 KS MT XN B CTX wfn ss_DIFF (INV_DIFFX MT B)) by (eapply fl_WX; eassumption).
assert (RB3 : fl_fromX0 KS MT XN B CTX wfn ss_B3 (INV_B3X MT B)) by (eapply fl_CX; eassumption).
assert (RB2 : fl_fromX0 KS MT XN B CTX wfn ss_B2 (INV_B2X MT B)) by (eapply fl_B2X; eassumption).
assert (RB : fl_fromX0 KS MT XN B CTX wfn ss_B (INV_0X MT B 0)) by (eapply fl_B1X; eassumption).
eapply pb_flushFrameX_A; eassumption.
Qed.
End d.
End b.
End a.
