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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCas YCav YCaw YCbh YCax YCay YCaz YCb0 YCb1 YCb2 YCb3 YCb4 YCb5 YCb6 YCb7.
Definition rga_X38b_mem : smem :=
{| r_base := Some 305%nat; r_lo := 0; r_hi := 48; r_wlo := 0; r_whi := 48;
r_chunks := [{| c_off := 32; YQ0b.c_val := CVal 8 (SOff 523 0) |}; {| c_off := 24; YQ0b.c_val := CVal 8 (SOff 522 0) |};
{| c_off := 16; YQ0b.c_val := CVal 8 (SOff 521 0) |}; {| c_off := 8; YQ0b.c_val := CVal 8 (SOff 520 0) |};
{| c_off := 0; YQ0b.c_val := CVal 8 (SOff 519 0) |}] |} :: rga_XB_mem.
Definition ss_X38b : sstate := Eval vm_compute in
mkSS 0x83ae8
[SLit 0; SOff 500 0; SOff 2 (-512); SOff 3 0; SOff 4 0; SOff 501 0; SOff 502 0; SOff 503 0; SOff 2 0; SOff 2 (-512);
SOff 504 0; SOff 505 0; SOff 506 0; SOff 507 0; SOff 508 0; SOff 509 0; SOff 510 0; SOff 511 0;
SOff 54 0; SOff 67 0; SOff 305 0; SOff 512 0; SOff 513 0; SOff 514 0; SOff 10 60; SOff 44 0; SOff 67 532; SOff 54 0;
SOff 515 0; SOff 516 0; SOff 517 0; SOff 518 0]
rga_X38b_mem None (mkFacts ((305%nat, HPTR 4) :: rga_XB_atoms) [] rga_X_alias).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition INV_X38b (B : asyms) : rga_inv_t :=
fun cx E k ly3 S3 W3 ms3 md3 => exists blk fim tb fq hh uu pp xx nf nh nu np nx : Z,
rga_kb cx S3 k (k + 8 <= EV_RGBADD) (RGA_G) (RGA_T) 51 /\ (c_fmt cx = 3 \/ c_fmt cx = 4) /\
Permutation (ablocks B ly3 S3)
(ablocks B (c_ly cx) (c_S cx) ++ [(blk, c_fmt cx * c_N cx); (fim, c_N cx)] ++
(tb, 48) :: optb fq nf ++ optb hh nh ++ optb uu nu ++ optb pp np ++ optb xx nx) /\
rga_newblk B cx E 152 blk (c_fmt cx * c_N cx) /\ rga_newblk B cx E 184 fim (c_N cx) /\ rga_newblk B cx E 305 tb 48 /\
rga_optblk B cx E 519 fq nf /\ rga_optblk B cx E 520 hh nh /\ rga_optblk B cx E 521 uu nu /\
rga_optblk B cx E 522 pp np /\ rga_optblk B cx E 523 xx nx.
End a.
