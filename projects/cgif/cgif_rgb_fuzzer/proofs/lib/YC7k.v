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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCas YCbh YC7j.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rga_obj_r_of_region_any : forall E m r lo hi wlo whi cs (vals : list Z) ecur,
region_ok trasegs E m (YQ0b.mkRegion (Some 10%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 10) = r ->
length vals = 11%nat ->
(forall j v, nth_error vals j = Some v -> ew E (32 + j) = Z_to_bv 64 v /\
0 <= v < 2 ^ (8 * Z.of_N (snd (nth j LAY_Rgb (0, 8%N)))) /\
In (YQ0b.mkChunk (fst (nth j LAY_Rgb (0, 8%N))) (CVal (snd (nth j LAY_Rgb (0, 8%N))) (SOff (32 + j) 0))) cs) ->
In (YQ0b.mkChunk 60 (CVal 4 ecur)) cs ->
obj_at trasegs m r LAY_Rgb (vals ++ [bv_unsigned (sv_denot E ecur) mod 2 ^ 32]).
Proof.
intros E m r lo hi wlo whi cs vals ecur HR Hr Hlen Hv Hc60.
assert (FLD : forall j v, nth_error vals j = Some v -> field_ok trasegs m r (nth j LAY_Rgb (0, 8%N)) v).
{ intros j v Hj. destruct (Hv j v Hj) as (He & Hrg & Hin). split; [|exact Hrg].
assert (Hw : Z.of_N (snd (nth j LAY_Rgb (0, 8%N))) <= 8).
{ assert (Hjl : (j < 11)%nat) by (rewrite <- Hlen; apply nth_error_Some; congruence).
do 11 (destruct j as [|j]; [cbn; lia|]). lia. }
apply (field_of_region E m 10 r cs lo hi wlo whi _ _ (SOff (32 + j) 0) v HR Hr Hin); [|exact Hrg | exact Hw].
cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
do 11 (destruct vals as [|? vals]; [discriminate Hlen|]). destruct vals; [|discriminate Hlen].
cbn [app obj_at LAY_Rgb].
repeat (split; [first [ exact (FLD 0%nat _ eq_refl) | exact (FLD 1%nat _ eq_refl) | exact (FLD 2%nat _ eq_refl) | exact (FLD 3%nat _ eq_refl)
| exact (FLD 4%nat _ eq_refl) | exact (FLD 5%nat _ eq_refl) | exact (FLD 6%nat _ eq_refl) | exact (FLD 7%nat _ eq_refl)
| exact (FLD 8%nat _ eq_refl) | exact (FLD 9%nat _ eq_refl) | exact (FLD 10%nat _ eq_refl) ]|]).
split; [|exact I]. split.
- exact (rg_field_of_region_any E m 10 r cs lo hi wlo whi 60 4%N ecur HR Hr Hc60 ltac:(cbn; lia)).
- cbn [snd Z.of_N]. change (2 ^ (8 * 4)) with (2 ^ 32). apply Z.mod_pos_bound. lia.
Qed.
End a.
