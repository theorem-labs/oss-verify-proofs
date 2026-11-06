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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCas.
Definition rga_deads_X : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 28; 29; 30; 31]%bv.
Definition rga_saved_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk (-104) (CVal 8 (SOff 27 0)); YQ0b.mkChunk (-96) (CVal 8 (SOff 26 0)); YQ0b.mkChunk (-88) (CVal 8 (SOff 25 0));
YQ0b.mkChunk (-80) (CVal 8 (SOff 24 0)); YQ0b.mkChunk (-72) (CVal 8 (SOff 23 0)); YQ0b.mkChunk (-64) (CVal 8 (SOff 22 0));
YQ0b.mkChunk (-56) (CVal 8 (SOff 21 0)); YQ0b.mkChunk (-48) (CVal 8 (SOff 20 0)); YQ0b.mkChunk (-40) (CVal 8 (SOff 19 0));
YQ0b.mkChunk (-32) (CVal 8 (SOff 18 0)); YQ0b.mkChunk (-24) (CVal 8 (SOff 9 0)); YQ0b.mkChunk (-16) (CVal 8 (SOff 8 0));
YQ0b.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition rga_X_mem : smem :=
[ YQ0b.mkRegion (Some 67%nat) 644 648 0 0 [];
YQ0b.mkRegion (Some 54%nat) 0 32 0 32 [];
YQ0b.mkRegion (Some 54%nat) 5184 8192 5184 8192 [YQ0b.mkChunk 8184 (CVal 8 (SOff 66 0))];
YQ0b.mkRegion (Some 2%nat) (-512) 0 (-512) 0 rga_saved_chunks ].
Definition rga_X_atoms : list (nat * afact) :=
[ (67%nat, mkAF 2147451392 17594333495296 2); (66%nat, HPTR 0); (54%nat, HPTR 5); (2%nat, mkAF (2^46) (2^47) 5); (44%nat, mkAF SB SB 0) ].
Definition rga_X_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 54 0) (SLit 3)) (SOff 44 0), SOff 67 0)].
Definition ss_EPI : sstate := Eval vm_compute in
mkSS 0x83b18
[SLit 0; SOff 900 0; SOff 2 (-512); SOff 3 0; SOff 4 0; SOff 901 0; SOff 902 0; SOff 903 0; SOff 2 0; SOff 2 (-512);
SOff 904 0; SOff 905 0; SOff 906 0; SOff 907 0; SOff 908 0; SOff 909 0; SOff 910 0; SOff 911 0;
SOff 54 0; SOff 67 0; SOff 912 0; SOff 913 0; SOff 914 0; SOff 915 0; SOff 916 0; SOff 44 0; SOff 67 532; SOff 54 0;
SOff 917 0; SOff 918 0; SOff 919 0; SOff 920 0]
rga_X_mem None (mkFacts rga_X_atoms [] rga_X_alias).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition INV_X (B : asyms) : rga_inv_t :=
fun cx E k ly3 S3 W3 ms3 md3 =>
rga_kb cx S3 k (k <= EV_RGBADD) (RGA_G) (RGA_T) 57 /\
exists (s' : cgif_st) (bef' beffmt' cur' : Z),
obj_at trasegs (mrestrict (w_H W3) (ms_mem ms3)) (c_r cx) LAY_Rgb
[c_g cx; c_wfn cx; c_ctx cx; c_path cx; c_attr cx; c_gen cx; c_loops cx; c_Wd cx; c_Hd cx; bef'; beffmt'; cur'] /\
tcgif_at (mrestrict (w_H W3) (ms_mem ms3)) (c_g cx) s' /\ cgif_wf s' (c_N cx) /\
cg_W s' = c_Wd cx /\ cg_H s' = c_Hd cx /\ cg_attr s' = cg_attr (c_s cx) /\ cg_raw s' = cg_raw (c_s cx) /\
(bef' = 0 \/ beffmt' = 3 \/ beffmt' = 4) /\
Permutation (ablocks B ly3 S3) (trgb_own (c_r cx) (c_g cx) s' (c_N cx) bef' beffmt' ++ timg_block (c_img cx) (c_fmt cx) (c_N cx) ++ c_rest cx) /\
(forall b, In b (trgb_own (c_r cx) (c_g cx) s' (c_N cx) bef' beffmt') ->
aftok (rgc_FP cx) (ablocks B (c_ly cx) (c_S cx)) b /\
forall blc lyq i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TRGBADD_STK (spZ (c_regs cx)) (rgc_FP cx) (ablocks B (c_ly cx) (c_S cx)) blc lyq [] (fst b + i)).
End a.
