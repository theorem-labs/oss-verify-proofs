(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k YI16 YI1h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCfx YCex YCev YCf6 YCf2 YCf7 YCet YCf3 YCf5 YCey YCgx YCec YCed YCee YCef YCeh YCei YCej YCek YCel YCes YCf0 YCem YCen YCe5 YCf8 YCf9 YCeo YCf4 YCfb YCep YCer YCeq YCeg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis ASM1 : astack_malloc_realizes trbsegs B 1.
Hypothesis ASM2 : astack_malloc_realizes trbsegs B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Hypothesis AMEMCMP : amemcmp_realizes trbsegs B A_memcmp_icpt.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_icpt.
Theorem trb_flushFrame : tflush_spec B.
Proof.
assert (RX : fl_from B ss_X (INV_X B)) by (apply fl_X; assumption).
assert (RR5 : fl_from B ss_R5 (INV_R5 B)) by (eapply fl_R5; eassumption).
pose proof (trb_cgif_raw_addframe B TL LAWS ML AMALLOC AMEMSET AMEMCPY AFREE ASM1 SMP ASF FFL) as TRAWADD.
assert (RR4 : fl_from B ss_R4 (INV_R4 B)) by (eapply fl_R4; eassumption).
assert (RR3 : fl_from B ss_R3 (INV_R3 B)) by (eapply fl_R3; eassumption).
assert (RR2 : fl_from B ss_R2 (INV_R2 B)) by (eapply fl_R2; eassumption).
assert (RR : fl_from B ss_R (INV_R B)) by (eapply fl_R1; eassumption).
pose proof (trb_cmpPixel B TL LAWS AMEMCMP) as TCMP.
assert (FT3 : fl_from B ss_T3 (INV_T3 B)) by (eapply fl_T3; eassumption).
assert (RT1x : fl_from B ss_T1x (INV_T0 B)) by (eapply fl_T2; eassumption).
assert (FT0 : fl_from B ss_T0 (INV_T0 B)) by (eapply fl_T1; eassumption).
assert (FD : fl_from B ss_DIMS (INV_DIMS B)) by (eapply fl_D; eassumption).
assert (FS : fl_from B ss_S (INV_DIFF B)) by (eapply fl_S; eassumption).
assert (FFv : fl_from B ss_Fv (INV_DIFF B)) by (eapply fl_Fv; eassumption).
assert (FDIFF : fl_from B ss_DIFF (INV_DIFF B)) by (eapply fl_W; eassumption).
assert (RB3 : fl_from B ss_B3 (INV_B3 B)) by (eapply fl_C; eassumption).
assert (RB2 : fl_from B ss_B2 (INV_B2 B)) by (eapply fl_B2; eassumption).
assert (RB : fl_from B ss_B (INV_0 B 0)) by (eapply fl_B1; eassumption).
eapply trb_flushFrame_A; eassumption.
Qed.
End b.
End a.
