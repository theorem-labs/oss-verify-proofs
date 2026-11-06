(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCpj YCpm YCq8.
Definition rga_deads_XB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 23; 25; 26; 28; 29; 30; 31]%bv.
Definition rga_XB_mem : smem :=
[ YQ0b.mkRegion (Some 67%nat) 644 648 0 0 [];
YQ0b.mkRegion (Some 54%nat) 5152 5168 5152 5168 [YQ0b.mkChunk 5160 (CVal 8 (SOff 184 0))];
YQ0b.mkRegion (Some 54%nat) 0 32 0 32 [];
YQ0b.mkRegion (Some 54%nat) 5184 8192 5184 8192 [YQ0b.mkChunk 8184 (CVal 8 (SOff 66 0))];
YQ0b.mkRegion (Some 2%nat) (-576) 0 (-576) 0
(YQ0b.mkChunk (-448) (CVal 8 (SOff 54 5152)) :: YQ0b.mkChunk (-368) (CVal 8 (SOff 152 0)) :: YQ0b.mkChunk (-272) (CVal 8 (SOff 10 60)) ::
YQ0b.mkChunk (-280) (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 60) (SLit 3)) (SOff 44 0))) :: rga_saved_chunks);
{| r_base := Some 10%nat; r_lo := 0; r_hi := 64; r_wlo := 48; r_whi := 64; r_chunks := [{| c_off := 0; YQ0b.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YQ0b.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; YQ0b.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; YQ0b.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 32; YQ0b.c_val := CVal 4 (SOff 36 0) |}; {| c_off := 36; YQ0b.c_val := CVal 4 (SOff 37 0) |}; {| c_off := 40; YQ0b.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 42; YQ0b.c_val := CVal 2 (SOff 39 0) |}; {| c_off := 44; YQ0b.c_val := CVal 2 (SOff 40 0) |}; {| c_off := 48; YQ0b.c_val := CVal 8 (SOff 41 0) |}; {| c_off := 56; YQ0b.c_val := CVal 4 (SOff 42 0) |}; {| c_off := 60; YQ0b.c_val := CVal 4 (SOff 43 0) |}] |} ].
Definition rga_XB_atoms : list (nat * afact) := [(184%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (152%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (67%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (66%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (54%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (44%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (45%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (46%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (47%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})].
Definition ss_XB : sstate := Eval vm_compute in
mkSS 0x843fc
[SLit 0; SOff 700 0; SOff 2 (-576); SOff 3 0; SOff 4 0; SOff 701 0; SOff 702 0; SOff 703 0; SOff 2 0; SOff 2 (-576);
SOff 704 0; SOff 705 0; SOff 706 0; SOff 707 0; SOff 708 0; SOff 709 0; SOff 710 0; SOff 711 0;
SOff 712 0; SOff 67 0; SOff 54 0; SOff 67 532; SOff 713 0; SOff 714 0; SOff 54 0; SOff 715 0; SOff 716 0; SOff 44 0;
SOff 717 0; SOff 718 0; SOff 719 0; SOff 720 0]
rga_XB_mem None (mkFacts rga_XB_atoms [] rga_X_alias).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition INV_XB (B : asyms) : rga_inv_t :=
fun cx E k ly3 S3 W3 ms3 md3 => exists blk fim : Z,
rga_kb cx S3 k (k + 2 <= EV_RGBADD) (RGA_G) (RGA_T) 57 /\ (c_fmt cx = 3 \/ c_fmt cx = 4) /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(blk, c_fmt cx * c_N cx); (fim, c_N cx)]) /\
rga_newblk B cx E 152 blk (c_fmt cx * c_N cx) /\ rga_newblk B cx E 184 fim (c_N cx).
End a.
