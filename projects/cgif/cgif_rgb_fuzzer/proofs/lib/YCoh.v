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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4.
Definition rga_deads_XD : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 25; 26; 28; 29; 30; 31]%bv.
Definition rga_XD_mem : smem :=
[ YQ0b.mkRegion (Some 305%nat) 0 48 0 48 [YQ0b.mkChunk 32 (CVal 8 (SOff 619 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 618 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 617 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 616 0)); YQ0b.mkChunk 0 (CVal 8 (SOff 615 0))];
YQ0b.mkRegion (Some 67%nat) 644 648 0 0 [];
YQ0b.mkRegion (Some 54%nat) 5152 5168 5152 5168 [YQ0b.mkChunk 5160 (CVal 8 (SOff 184 0)); YQ0b.mkChunk 5152 (CVal 8 (SOff 54 4256))];
YQ0b.mkRegion (Some 54%nat) 0 32 0 32 [];
YQ0b.mkRegion (Some 54%nat) 5184 8192 5184 8192 [YQ0b.mkChunk 8184 (CVal 8 (SOff 66 0))];
YQ0b.mkRegion (Some 2%nat) (-576) 0 (-576) 0 [YQ0b.mkChunk (-272) (CVal 8 (SOff 10 60)); YQ0b.mkChunk (-368) (CVal 8 (SOff 152 0)); YQ0b.mkChunk (-448) (CVal 8 (SOff 54 5152)); YQ0b.mkChunk (-280) (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 60) (SLit 3)) (SOff 44 0))); YQ0b.mkChunk (-192) (CVal 8 (SOff 626 0)); YQ0b.mkChunk (-352) (CVal 8 (SOff 67 532)); YQ0b.mkChunk (-536) (CVal 8 (SOff 54 0)); YQ0b.mkChunk (-360) (CVal 8 (SOff 305 0)); YQ0b.mkChunk (-104) (CVal 8 (SOff 27 0)); YQ0b.mkChunk (-96) (CVal 8 (SOff 26 0)); YQ0b.mkChunk (-88) (CVal 8 (SOff 25 0)); YQ0b.mkChunk (-80) (CVal 8 (SOff 24 0)); YQ0b.mkChunk (-72) (CVal 8 (SOff 23 0)); YQ0b.mkChunk (-64) (CVal 8 (SOff 22 0)); YQ0b.mkChunk (-56) (CVal 8 (SOff 21 0)); YQ0b.mkChunk (-48) (CVal 8 (SOff 20 0)); YQ0b.mkChunk (-40) (CVal 8 (SOff 19 0)); YQ0b.mkChunk (-32) (CVal 8 (SOff 18 0)); YQ0b.mkChunk (-24) (CVal 8 (SOff 9 0)); YQ0b.mkChunk (-16) (CVal 8 (SOff 8 0)); YQ0b.mkChunk (-8) (CVal 8 (SOff 1 0))];
YQ0b.mkRegion (Some 10%nat) 0 64 48 64 [YQ0b.mkChunk 0 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 34 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 32 (CVal 4 (SOff 36 0)); YQ0b.mkChunk 36 (CVal 4 (SOff 37 0)); YQ0b.mkChunk 40 (CVal 2 (SOff 38 0)); YQ0b.mkChunk 42 (CVal 2 (SOff 39 0)); YQ0b.mkChunk 44 (CVal 2 (SOff 40 0)); YQ0b.mkChunk 48 (CVal 8 (SOff 41 0)); YQ0b.mkChunk 56 (CVal 4 (SOff 42 0)); YQ0b.mkChunk 60 (CVal 4 (SOff 43 0))] ].
Definition rga_XD_atoms : list (nat * afact) := [(305%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (626%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (184%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (152%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (67%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (66%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (54%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (44%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (45%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (46%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (47%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})].
Definition ss_XD : sstate := Eval vm_compute in
mkSS 0x848fc
[SLit 0; SOff 2600 0; SOff 2 (-576); SOff 3 0; SOff 4 0; SOff 2601 0; SOff 2602 0; SOff 2603 0; SOff 2 0; SOff 2 (-576); SOff 2604 0; SOff 2605 0; SOff 2606 0; SOff 2607 0; SOff 2608 0; SOff 2609 0; SOff 2610 0; SOff 2611 0; SOff 305 0; SOff 67 0; SOff 54 0; SOff 2612 0; SOff 2613 0; SOff 2614 0; SOff 54 0; SOff 2615 0; SOff 2616 0; SOff 44 0; SOff 2617 0; SOff 2618 0; SOff 2619 0; SOff 2620 0]
rga_XD_mem None (mkFacts rga_XD_atoms [] rga_X_alias).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition INV_XD (B : asyms) : rga_inv_t :=
fun cx E k ly3 S3 W3 ms3 md3 => exists (blk fim tb fq hh uu pp xx Tsz dn nd : Z),
rga_kb cx S3 k (k + 1 + EV_FREECHT + 2 <= EV_RGBADD) (RGA_G) (RGA_T) 0 /\ (c_fmt cx = 3 \/ c_fmt cx = 4) /\ 0 <= Tsz /\ 0 <= nd /\
Permutation (ablocks B ly3 S3)
(ablocks B (c_ly cx) (c_S cx) ++ [(blk, c_fmt cx * c_N cx); (fim, c_N cx)] ++ ((tb, CHT_SIZE) :: cht_blocks fq hh uu pp xx Tsz) ++ [(dn, nd)]) /\
rga_newblk B cx E 152 blk (c_fmt cx * c_N cx) /\ rga_newblk B cx E 184 fim (c_N cx) /\ rga_newblk B cx E 305 tb CHT_SIZE /\
ew E 615 = Z_to_bv 64 fq /\ ew E 616 = Z_to_bv 64 hh /\ ew E 617 = Z_to_bv 64 uu /\ ew E 618 = Z_to_bv 64 pp /\ ew E 619 = Z_to_bv 64 xx /\
rga_newblk B cx E 626 dn nd.
End a.
