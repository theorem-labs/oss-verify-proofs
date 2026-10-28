(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatCARSpec_b BatDepotA_b BatDepot_b BatAllocate3_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition art_malloc_fp (S t spb ris qs c km ab rz n rs l2 blk : Z) (x : Z) : Prop :=
  (S - 4096 <= x < S) \/ art_alloc3_fp (S - 2144) t spb ris qs c km ab rz n rs l2 blk x.

(* [comment removed for export] *)
Definition art_malloc_fp_lin (S t spb qs c km w qz qr n l2 blk : Z) (x : Z) : Prop :=
  let rb := spb + c * 2 ^ 32 in let shb := 2147450880 + 8192 * qs + c * 2 ^ 29 in
  (S - 4096 <= x < S)
  \/ (t + 208 + 80 * c <= x < t + 208 + 80 * c + 80) \/ (exists c', 1 <= c' <= 31 /\ t + 208 + 80 * c' + 4 <= x < t + 208 + 80 * c' + 16)
  \/ (t + 2784 <= x < t + 2824) \/ (t + 2872 <= x < t + 2888) \/ (t + 2912 + 8 * c <= x < t + 2920 + 8 * c)
  \/ (spb + 2 ^ 37 + 128 * c <= x < spb + 2 ^ 37 + 128 * c + 128)
  \/ (rb + 262144 * km <= x < rb + 262144 * km + 262144) \/ (rb + 3758096384 <= x < rb + 4294967296)
  \/ (rb + 16 * w <= x < rb + 16 * w + 16 * qz + n)
  \/ (shb + 32768 * km <= x < shb + 32768 * km + 32768) \/ (shb + 469762048 <= x < shb + 536870912)
  \/ (shb + 2 * w + 2 * qz <= x < shb + 2 * w + 2 * qz + qr)
  \/ (0x211b08 <= x < 0x661b28) \/ (l2 <= x < l2 + 2 ^ 20) \/ (blk <= x < blk + 2 ^ 23).

Lemma art_malloc_fp_cases : forall S t spb ris qs c km ab rz n rs l2 blk w qz qr x,
  spb = 65536 * qs -> ris = spb + 2 ^ 37 -> ab = spb + c * 2 ^ 32 + w * 16 -> rz = 16 * qz -> rs = 8 * qr ->
  art_malloc_fp S t spb ris qs c km ab rz n rs l2 blk x -> art_malloc_fp_lin S t spb qs c km w qz qr n l2 blk x.
Proof.
  intros S t spb ris qs c km ab rz n rs l2 blk w qz qr x Espb Eris Eab Erz Ers F.
  assert (Hub8 : (ab + rz) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz).
  { rewrite Eab, Espb, Erz. replace (65536 * qs + c * 2 ^ 32 + w * 16 + 16 * qz) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
  assert (Hqr8 : rs / 8 = qr). { rewrite Ers, Z.mul_comm. apply Z.div_mul. lia. }
  unfold art_malloc_fp, art_alloc3_fp in F. rewrite Hub8, Hqr8 in F. unfold art_ca_fp, art_refill_fp, art_pc_hdr_foot, dprivD in F.
  unfold art_malloc_fp_lin. cbv zeta.
  destruct F as [F|[F|[[F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|F]]|[F|[F|[F|[F|[F|[F|F]]]]]]]]].
  1-4: left; lia.
  1: right; left; lia.
  1: { destruct F as (c' & Hc' & F). right; right; left. exists c'. split; [exact Hc'|lia]. }
  1: do 3 right; left; lia.
  1: do 6 right; left; lia.
  1: do 7 right; left; lia.
  1: do 8 right; left; lia.
  1: do 10 right; left; lia.
  1: do 11 right; left; lia.
  1: do 4 right; left; lia.
  1: do 3 right; left; lia.
  1: do 9 right; left; lia.
  1: do 12 right; left; lia.
  1: do 3 right; left; lia.
  1: do 5 right; left; lia.
  1: do 13 right; left; lia.
  1: do 14 right; left; lia.
  1: do 15 right; lia.
Qed.

(* [comment removed for export] *)
Definition art_malloc_coarse (HI t spb qs l2 blk : Z) (x : Z) : Prop :=
  HI <= x \/ (t + 208 <= x < t + 3160) \/ (spb + 2 ^ 32 <= x < spb + 2 ^ 37 + 4096)
  \/ (2147450880 + 8192 * qs + 2 ^ 29 <= x < 2147450880 + 8192 * qs + 2 ^ 34)
  \/ (0x211b08 <= x < 0x661b28) \/ (l2 <= x < l2 + 2 ^ 20) \/ (blk <= x < blk + 2 ^ 23).

Lemma art_mfp_coarse : forall S HI t spb qs c km w qz qr n l2 blk x,
  1 <= c <= 30 -> 0 <= km -> 262144 * km <= 3758096384 -> 0 <= w -> 1 <= qz -> 0 <= n -> 0 <= qr ->
  16 * w + 16 * qz + n <= 3758096384 -> 2 * w + 2 * qz + qr <= 469762048 -> HI + 4096 <= S - 4096 ->
  art_malloc_fp_lin S t spb qs c km w qz qr n l2 blk x -> art_malloc_coarse HI t spb qs l2 blk x.
Proof.
  intros S HI t spb qs c km w qz qr n l2 blk x Hc Hkm Hkm' Hw Hqz Hn Hqr Hch Hsh HS F.
  unfold art_malloc_fp_lin in F. cbv zeta in F. unfold art_malloc_coarse.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]].
  - left; lia.
  - right; left; lia.
  - destruct F as (c' & Hc' & F). right; left; lia.
  - right; left; lia.
  - right; left; lia.
  - right; left; lia.
  - do 2 right; left; lia.
  - do 2 right; left; lia.
  - do 2 right; left; lia.
  - do 2 right; left; lia.
  - do 3 right; left; lia.
  - do 3 right; left; lia.
  - do 3 right; left; lia.
  - do 4 right; left; lia.
  - do 5 right; left; lia.
  - do 6 right; lia.
Qed.

(* [comment removed for export] *)
Lemma art_mfp_out_class : forall S HI t spb qs c km w qz qr n l2 blk c0 x,
  1 <= c <= 30 -> 1 <= c0 <= 30 -> c0 <> c -> 0 <= km -> 262144 * km <= 3758096384 -> 0 <= w -> 1 <= qz -> 0 <= n -> 0 <= qr ->
  16 * w + 16 * qz + n <= 3758096384 -> 2 * w + 2 * qz + qr <= 469762048 -> HI + 4096 <= S - 4096 ->
  0x10007fff8000 <= HI -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> spb + 2 ^ 37 + 4096 <= HI -> HI <= 2 ^ 47 ->
  apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
  apart l2 (2 ^ 20) spb (2 ^ 37 + 4096) -> apart l2 (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
  apart blk (2 ^ 23) spb (2 ^ 37 + 4096) -> apart blk (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
  (spb + c0 * 2 ^ 32 <= x < spb + c0 * 2 ^ 32 + 2 ^ 32
   \/ 2147450880 + 8192 * qs + c0 * 2 ^ 29 <= x < 2147450880 + 8192 * qs + c0 * 2 ^ 29 + 2 ^ 29
   \/ spb + 2 ^ 37 + 128 * c0 <= x < spb + 2 ^ 37 + 128 * c0 + 128) ->
  ~ art_malloc_fp_lin S t spb qs c km w qz qr n l2 blk x.
Proof.
  intros S HI t spb qs c km w qz qr n l2 blk c0 x Hc Hc0 Ne Hkm Hkm' Hw Hqz Hn Hqr Hch Hsh HS G1 Espb G4 G6 G2 At_k At_s Al_k Al_s Ab_k Ab_s Hx F.
  unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.

(* [comment removed for export] *)
Lemma art_mfp_out_chunk : forall S HI t spb qs c km w qz qr n l2 blk sz w0 x,
  1 <= c <= 30 -> 0 <= km -> 262144 * km <= 3758096384 -> 0 <= w -> 16 * w + sz <= 3758096384 -> 1 <= qz -> 0 <= n -> n <= 8 * qr -> 16 * qz + 8 * qr <= sz -> sz <= 65536 ->
  0 <= w0 -> 16 * w0 + sz <= 262144 * km -> (16 * w0 + sz <= 16 * w \/ 16 * w + sz <= 16 * w0) -> HI + 4096 <= S - 4096 ->
  0x10007fff8000 <= HI -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> spb + 2 ^ 37 + 4096 <= HI -> HI <= 2 ^ 47 ->
  apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
  apart l2 (2 ^ 20) spb (2 ^ 37 + 4096) -> apart l2 (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
  apart blk (2 ^ 23) spb (2 ^ 37 + 4096) -> apart blk (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
  (spb + c * 2 ^ 32 + 16 * w0 <= x < spb + c * 2 ^ 32 + 16 * w0 + sz
   \/ 8 * (x - (2147450880 + 8192 * qs + c * 2 ^ 29)) + 8 <= 16 * w0 + sz /\ 2147450880 + 8192 * qs + c * 2 ^ 29 + 2 * w0 <= x) ->
  ~ art_malloc_fp_lin S t spb qs c km w qz qr n l2 blk x.
Proof.
  intros S HI t spb qs c km w qz qr n l2 blk sz w0 x Hc Hkm Hkm' Hw Hwu Hqz Hn Hnr Hfit Hsz Hw0 Hold Hap HS G1 Espb G4 G6 G2 At_k At_s Al_k Al_s Ab_k Ab_s Hx F.
  unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.

(* [comment removed for export] *)
Lemma art_mfp_out_cache : forall S HI t spb qs c km w qz qr n l2 blk c0 x,
  1 <= c <= 30 -> 1 <= c0 <= 31 -> c0 <> c -> 0 <= w -> 1 <= qz -> 0 <= n -> 0 <= qr -> 0 <= km -> 262144 * km <= 3758096384 ->
  16 * w + 16 * qz + n <= 3758096384 -> 2 * w + 2 * qz + qr <= 469762048 -> HI + 4096 <= S - 4096 -> spb + 2 ^ 37 + 4096 <= HI -> HI <= 2 ^ 47 ->
  0x10007fff8000 <= HI -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> t + 4096 <= HI ->
  apart t 4096 spb (2 ^ 37 + 4096) -> apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> apart t 4096 0x10000 (0x696000 - 0x10000) ->
  apart l2 (2 ^ 20) t 4096 -> apart blk (2 ^ 23) t 4096 ->
  (t + 208 + 80 * c0 <= x < t + 208 + 80 * c0 + 4 \/ t + 208 + 80 * c0 + 16 <= x < t + 208 + 80 * c0 + 80) ->
  ~ art_malloc_fp_lin S t spb qs c km w qz qr n l2 blk x.
Proof.
  intros S HI t spb qs c km w qz qr n l2 blk c0 x Hc Hc0 Ne Hw Hqz Hn Hqr Hkm Hkm' Hch Hsh HS G6 G2 G1 Espb G4 G8 At_k At_s At_i Al_t Ab_t Hx F.
  unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.

(* [comment removed for export] *)
Lemma art_mfp_out_shc : forall S HI t spb qs c km w qz qr n l2 blk y,
  1 <= c <= 30 -> 0 <= km -> 262144 * km <= 3758096384 -> 0 <= w -> 1 <= qz -> 0 <= n -> 0 <= qr -> HI + 4096 <= S - 4096 ->
  0x10007fff8000 <= HI -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> spb + 2 ^ 37 + 4096 <= HI -> HI <= 2 ^ 47 ->
  apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> apart l2 (2 ^ 20) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) -> apart blk (2 ^ 23) 0x7fff7000 (0x10007fff8000 - 0x7fff7000) ->
  0 <= y -> y < 32768 * km -> (y < 2 * w + 2 * qz \/ 2 * w + 2 * qz + qr <= y) ->
  ~ art_malloc_fp_lin S t spb qs c km w qz qr n l2 blk (2147450880 + 8192 * qs + c * 2 ^ 29 + y).
Proof.
  intros S HI t spb qs c km w qz qr n l2 blk y Hc Hkm Hkm' Hw Hqz Hn Hqr HS G1 Espb G4 G6 G2 At_s Al_s Ab_s Hy Hy' Hyu F.
  unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.

(* [comment removed for export] *)
Lemma art_mfp_out_stack : forall S HI t spb qs c km w qz qr n l2 blk a,
  1 <= c <= 30 -> 0 <= km -> 262144 * km <= 3758096384 -> 0 <= w -> 1 <= qz -> 0 <= n -> 0 <= qr ->
  16 * w + 16 * qz + n <= 3758096384 -> 2 * w + 2 * qz + qr <= 469762048 ->
  0x10007fff8000 <= HI -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> spb + 2 ^ 37 + 4096 <= HI -> HI <= 2 ^ 47 -> t + 4096 <= HI ->
  l2 + 2 ^ 20 <= HI -> blk + 2 ^ 23 <= HI ->
  HI <= a -> ~ (S - 4096 <= a < S) -> ~ art_malloc_fp_lin S t spb qs c km w qz qr n l2 blk a.
Proof.
  intros S HI t spb qs c km w qz qr n l2 blk a Hc Hkm Hkm' Hw Hqz Hn Hqr Hch Hsh G1 Espb G4 G6 G2 G8 Dl2 Dblk Ha Ns F.
  unfold art_malloc_fp_lin in F. cbv zeta in F.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.

(* [comment removed for export] *)
Lemma art_mfp_out_image : forall S HI t spb qs c km w qz qr n l2 blk a,
  1 <= c <= 30 -> 0 <= km -> 0 <= w -> 1 <= qz -> 0 <= n -> 0 <= qr -> HI + 4096 <= S - 4096 ->
  0x10007fff8000 <= HI -> spb = 65536 * qs -> 0x10007fff8000 <= spb -> apart t 4096 0x10000 (0x696000 - 0x10000) -> 0x696000 <= l2 -> 0x696000 <= blk ->
  0x10000 <= a < 0x696000 -> ~ (0x211b08 <= a < 0x661b28) -> ~ art_malloc_fp_lin S t spb qs c km w qz qr n l2 blk a.
Proof.
  intros S HI t spb qs c km w qz qr n l2 blk a Hc Hkm Hw Hqz Hn Hqr HS G1 Espb G4 At_i Dl Db Ha Nd F.
  unfold art_malloc_fp_lin in F. cbv zeta in F. unfold apart in *.
  destruct F as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]; try (destruct F as (c' & Hc' & F)); lia.
Qed.
