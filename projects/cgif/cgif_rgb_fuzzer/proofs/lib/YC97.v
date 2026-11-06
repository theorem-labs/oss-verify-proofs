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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCas YCav YCaw YCbh YCax YCay YCbi YC1c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i.
Definition ss_FINb : sstate :=
(mkSS 340224 [SLit 0; SLit 541844; SOff 2 (-512); SOff 3 0; SOff 4 0; SOff 1022 0; SOff 1023 0; SOff 1024 0; SOff 2 0; SOff 2 (-512); SOff 41 0; SLit 0; SOff 1027 0; SOff 1028 0; SOff 1029 0; SOff 1030 0; SOff 1031 0; SOff 1032 0; SOff 54 0; SOff 67 0; SOff 10 48; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 48) (SLit 3)) (SOff 44 0); SOff 1025 0; SOff 1014 0; SOff 10 0; SOff 44 0; SOff 67 532; SOff 54 0; SOff 1033 0; SOff 1034 0; SOff 1035 0; SOff 1036 0] [
{| r_base := Some 54%nat; r_lo := 5168; r_hi := 5184; r_wlo := 5168; r_whi := 5184; r_chunks := [{| c_off := 5180; YQ0b.c_val := CVal 1 (SOff 1012 0) |}; {| c_off := 5168; YQ0b.c_val := CVal 4 (SAlu ALU_OR (SExt true 32 (SOff 300 0)) (SOff 1020 0)) |}; {| c_off := 5178; YQ0b.c_val := CVal 2 (SOff 1012 0) |}; {| c_off := 5176; YQ0b.c_val := CVal 2 (SExt true 16 (SOff 49 0)) |}; {| c_off := 5172; YQ0b.c_val := CVal 4 (SLit 0) |}] |};
{| r_base := Some 67%nat; r_lo := 644; r_hi := 648; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 647; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 646; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 645; YQ0b.c_val := CVal 1 (SLit 0) |}; {| c_off := 644; YQ0b.c_val := CVal 1 (SLit 0) |}] |};
{| r_base := Some 54%nat; r_lo := 5152; r_hi := 5168; r_wlo := 5152; r_whi := 5168; r_chunks := [{| c_off := 5160; YQ0b.c_val := CVal 8 (SOff 184 0) |}; {| c_off := 5152; YQ0b.c_val := CVal 8 (SOff 54 4256) |}] |};
{| r_base := Some 54%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |};
{| r_base := Some 67%nat; r_lo := 532; r_hi := 628; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 532; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 540; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 548; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 556; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 564; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 572; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 580; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 588; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 596; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 604; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 612; YQ0b.c_val := CVal 8 (SLit 0) |}; {| c_off := 620; YQ0b.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 54%nat; r_lo := 5184; r_hi := 8192; r_wlo := 5184; r_whi := 8192; r_chunks := [{| c_off := 8184; YQ0b.c_val := CVal 8 (SOff 66 0) |}] |};
{| r_base := Some 2%nat; r_lo := -512; r_hi := 0; r_wlo := -512; r_whi := 0; r_chunks := [{| c_off := -480; YQ0b.c_val := CVal 8 (SOff 10 60) |}; {| c_off := -408; YQ0b.c_val := CVal 8 (SOff 10 56) |}; {| c_off := -400; YQ0b.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 48) (SLit 3)) (SOff 44 0)) |}; {| c_off := -392; YQ0b.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 56) (SLit 3)) (SOff 44 0)) |}; {| c_off := -376; YQ0b.c_val := CVal 8 (SOff 10 48) |}; {| c_off := -368; YQ0b.c_val := CVal 8 (SOff 11 8) |}; {| c_off := -344; YQ0b.c_val := CVal 8 (SOff 1019 0) |}; {| c_off := -328; YQ0b.c_val := CVal 8 (SOff 152 0) |}; {| c_off := -312; YQ0b.c_val := CVal 8 (SOff 54 5152) |}; {| c_off := -224; YQ0b.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 60) (SLit 3)) (SOff 44 0)) |}; {| c_off := -168; YQ0b.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 8) (SLit 3)) (SOff 44 0)) |}; {| c_off := -104; YQ0b.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YQ0b.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YQ0b.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YQ0b.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YQ0b.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YQ0b.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YQ0b.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YQ0b.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YQ0b.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YQ0b.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YQ0b.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YQ0b.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YQ0b.c_val := CVal 8 (SOff 1 0) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 64; r_wlo := 48; r_whi := 64; r_chunks := [{| c_off := 0; YQ0b.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YQ0b.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 16; YQ0b.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 24; YQ0b.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 32; YQ0b.c_val := CVal 4 (SOff 36 0) |}; {| c_off := 36; YQ0b.c_val := CVal 4 (SOff 37 0) |}; {| c_off := 40; YQ0b.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 42; YQ0b.c_val := CVal 2 (SOff 39 0) |}; {| c_off := 44; YQ0b.c_val := CVal 2 (SOff 40 0) |}; {| c_off := 48; YQ0b.c_val := CVal 8 (SOff 41 0) |}; {| c_off := 56; YQ0b.c_val := CVal 4 (SOff 42 0) |}; {| c_off := 60; YQ0b.c_val := CVal 4 (SOff 43 0) |}] |};
{| r_base := Some 11%nat; r_lo := 0; r_hi := 24; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YQ0b.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 8; YQ0b.c_val := CVal 4 (SOff 46 0) |}; {| c_off := 12; YQ0b.c_val := CVal 4 (SOff 47 0) |}; {| c_off := 16; YQ0b.c_val := CVal 4 (SOff 48 0) |}; {| c_off := 20; YQ0b.c_val := CVal 2 (SOff 49 0) |}] |}] None {| f_atoms := [(1012%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (184%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (152%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (67%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (66%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (54%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (44%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (45%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (46%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (47%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})]; f_conds := []; f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 54 0) (SLit 3)) (SOff 44 0), SOff 67 0)] |}).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition INV_FINb (B : asyms) : rga_inv_t :=
fun cx E k ly3 S3 W3 ms3 md3 => exists (blk fim : Z) (s' : cgif_st),
rga_kb cx S3 k (k + 2 <= EV_RGBADD) (RGA_G) (RGA_T) 53 /\ (c_fmt cx = 3 \/ c_fmt cx = 4) /\
tcgif_at (mrestrict (w_H W3) (ms_mem ms3)) (c_g cx) s' /\ cgif_wf s' (c_N cx) /\
cg_W s' = c_Wd cx /\ cg_H s' = c_Hd cx /\ cg_attr s' = cg_attr (c_s cx) /\ cg_raw s' = cg_raw (c_s cx) /\
Permutation (ablocks B ly3 S3)
((c_r cx, RGB_SIZE) :: (cgif_blocks (c_g cx) s' (c_N cx) ++ (fim, c_N cx) :: optb (c_bef cx) (c_beffmt cx * c_N cx) ++
timg_block (c_img cx) (c_fmt cx) (c_N cx) ++ c_rest cx ++ [(blk, c_fmt cx * c_N cx)])) /\
rga_newblkF B cx E 152 blk (c_fmt cx * c_N cx) /\ rga_newblkF B cx E 184 fim (c_N cx) /\
(forall b, In b (cgif_blocks (c_g cx) s' (c_N cx)) ->
aftok (rgc_FP cx) (ablocks B (c_ly cx) (c_S cx)) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TRGBADD_STK (spZ (c_regs cx)) (rgc_FP cx) (ablocks B (c_ly cx) (c_S cx)) blc lyq [] (fst b + i)).
End a.
