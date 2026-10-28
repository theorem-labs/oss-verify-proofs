(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition A_rd : Z := 0x2e8c.
Definition rd_written (cx : lzw_acx) (lp : Z) (a : Z) : Prop :=
(z_sp cx - 336 - 4096 <= a < z_sp cx - 304) \/ (z_ctx cx + 60 <= a < z_ctx cx + 68) \/ (z_ld cx + 2 * lp <= a < z_ld cx + 2 * lp + 2) \/
(z_ti cx <= a < z_ti cx + z_tisz cx) \/ (z_lm cx <= a < z_lm cx + 8192) \/ (z_lc cx <= a < z_lc cx + 4096) \/ (z_li cx <= a < z_li cx + 8192).
Definition rd_untouched (cx : lzw_acx) (lp : Z) (a : Z) : Prop := ~ rd_written cx lp a.
Definition in_rng (lo hi a : Z) : Prop := lo <= a < hi.
Definition rctx_chunks (k60 : bool) : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0));
YP09.mkChunk 48 (CVal 8 (SOff 38 0)); YP09.mkChunk 56 (CVal 4 (SOff 39 0))] ++
(if k60 then [YP09.mkChunk 60 (CVal 4 (SOff 41 0))] else []).
Definition rctx_region (k60 : bool) : YP09.region := YP09.mkRegion (Some 8%nat) 0 72 60 68 (rctx_chunks k60).
Definition agen_ptrs (m : word -> option byte) (cx : lzw_acx) : Prop :=
let g := z_ctx cx in
val_mem SEGS m g 8 (z_ti cx) /\ val_mem SEGS m (g + 8) 8 (z_lm cx) /\
val_mem SEGS m (g + 16) 8 (z_lc cx) /\ val_mem SEGS m (g + 24) 8 (z_li cx) /\
val_mem SEGS m (g + 32) 8 (z_tm cx) /\ val_mem SEGS m (g + 40) 8 (z_ld cx) /\
val_mem SEGS m (g + 48) 8 (z_img cx) /\ val_mem SEGS m (g + 56) 4 (z_nP cx).
Lemma agen_ptrs_of_at : forall m cx lp dp mp, agen_at m cx lp dp mp -> agen_ptrs m cx.
Proof. intros m cx lp dp mp (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _). unfold agen_ptrs. repeat split; assumption. Qed.
Lemma agen_at_of_ptrs : forall m m' cx lp' dp' mp',
agen_ptrs m cx ->
(forall a, z_ctx cx <= a < z_ctx cx + 60 -> mbyte SEGS m' a = mbyte SEGS m a) ->
val_mem SEGS m' (z_ctx cx + 60) 4 lp' -> val_mem SEGS m' (z_ctx cx + 64) 2 dp' -> val_mem SEGS m' (z_ctx cx + 66) 2 mp' ->
agen_at m' cx lp' dp' mp'.
Proof.
intros m m' cx lp' dp' mp' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hfr Vlp Vdp Vmp.
unfold agen_at. repeat split; try assumption;
intros k Hk; (rewrite Hfr; [| cbn in Hk; lia]); first [apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8]; exact Hk.
Qed.
Lemma arr16_zeros_aview : forall H (mem : word -> option byte) base n,
(forall a, base <= a < base + 2 * Z.of_nat n -> mbyte SEGS (mrestrict H mem) a = Some (Z_to_bv 8 0)) ->
arr16 SEGS (mrestrict H mem) base (repeat 0 n).
Proof. intros H mem base n Hz. apply arr16_zeros. exact Hz. Qed.
Lemma mbyte_zero_of_aview : forall H (m : word -> option byte) a,
aview SEGS H m a = Some 0 -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
intros H m a Hz. destruct (aview_byte SEGS H m a 0 Hz) as (b & Hb & Hv & _). rewrite Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])). lia.
Qed.
End e.
End d.
