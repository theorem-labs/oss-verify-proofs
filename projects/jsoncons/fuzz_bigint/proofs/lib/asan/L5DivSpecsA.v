(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA LibIface
     AsanAcct L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5CoreB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5DSA.
Import L5A. Import L5CA. Import L5CSA. Import L5CB.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition OPMOD : Z := 0x91df8.          (* [comment removed for export] *)
Definition DIVIDE : Z := 0x920ec.
Definition OPDIV : Z := 0x93f48.          (* [comment removed for export] *)
Definition UNNORM : Z := 0x93830.
Definition NORMALIZE : Z := 0x932a0.
Definition ZERO_THROW : Z := 0x92de0.     (* [comment removed for export] *)
Definition ASSERT_THROW : Z := 0x902d0.   (* [comment removed for export] *)
Definition OM1RET : Z := 0x8e080.         (* [comment removed for export] *)
Definition DIV_RET_O : Z := 0x91f30.      (* [comment removed for export] *)
Definition DIV_RET_N : Z := 0x94080.      (* [comment removed for export] *)
Definition DIVEQ_RET : Z := 0x93870.      (* [comment removed for export] *)
Definition UNNORM_RET : Z := 0x92a54.     (* [comment removed for export] *)
Definition RESIZE_RET_G : Z := 0x92758.   (* [comment removed for export] *)
Definition RESERVE_RET : Z := 0x8f940.    (* [comment removed for export] *)
Definition RETIRE_MAGIC : Z := 0x45e0360e.
Definition FRAME_MAGIC : Z := 0x41b58ab3.
Definition MWORD : Z := 2 ^ 64 - 1.

Definition U (R : bvmap 5 word) (k : Z) : Z := bv_unsigned (getr R (Z_to_bv 5 k)).

(* [comment removed for export] *)
Record fr_live (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FFb : list fframe) (M : word -> option byte) (k F fl rs : Z) : Prop := FRL {
  frl_cell : cell_is RSEGS M (F + ff_bytes k - 8) 8 fl;
  frl_fs : ar_fs ar <= fl < ar_fs ar + FS_BYTES;
  frl_nc : ~ aclient L ar LB ((F, k, rs) :: FFb) 0 0 fl;
  frl_apart : F + ff_bytes k <= fl \/ fl + 1 <= F;
  frl_head : L5.u64_at RSEGS M F FRAME_MAGIC
}.

(* [comment removed for export] *)
Definition sh_run (M : word -> option byte) (F off n v : Z) : Prop := forall j, 0 <= j < n -> byte_at M (S F + off + j) v.

(* [comment removed for export] *)
Definition zero_throw_regs (R0 R : bvmap 5 word) (S F1 F3 xo fden : Z) : Prop :=
     getr R 2%bv = Z_to_bv 64 (S - 448) /\ getr R 3%bv = getr R0 3%bv /\ getr R 4%bv = getr R0 4%bv
  /\ getr R 10%bv = Z_to_bv 64 16
  /\ getr R 8%bv = Z_to_bv 64 (S - 96) /\ getr R 9%bv = Z_to_bv 64 (S - 448)
  /\ getr R 18%bv = Z_to_bv 64 (F3 / 8 + SB) /\ getr R 19%bv = Z_to_bv 64 (F1 + 32) /\ getr R 20%bv = Z_to_bv 64 0
  /\ getr R 21%bv = Z_to_bv 64 fden /\ getr R 22%bv = Z_to_bv 64 1 /\ getr R 23%bv = Z_to_bv 64 (F3 + 32)
  /\ getr R 24%bv = Z_to_bv 64 xo /\ getr R 25%bv = getr R0 25%bv /\ getr R 26%bv = Z_to_bv 64 (F3 + 48) /\ getr R 27%bv = Z_to_bv 64 F3.

(* [comment removed for export] *)
Definition opmod_frame (R0 : bvmap 5 word) (M : word -> option byte) (S F1 : Z) : Prop :=
     L5.u64_at RSEGS M (S - 8) (U R0 1) /\ L5.u64_at RSEGS M (S - 16) (U R0 8) /\ L5.u64_at RSEGS M (S - 24) (U R0 9)
  /\ L5.u64_at RSEGS M (S - 32) (U R0 18) /\ L5.u64_at RSEGS M (S - 40) (U R0 19) /\ L5.u64_at RSEGS M (S - 48) (U R0 20)
  /\ L5.u64_at RSEGS M (S - 56) (U R0 21) /\ L5.u64_at RSEGS M (S - 64) (U R0 22) /\ L5.u64_at RSEGS M (S - 72) (U R0 23)
  /\ L5.u64_at RSEGS M (S - 80) (U R0 24) /\ L5.u64_at RSEGS M (S - 88) F1.

(* [comment removed for export] *)
Definition divO_saves (R0 : bvmap 5 word) (M : word -> option byte) (S F1 xo bo : Z) : Prop :=
     L5.u64_at RSEGS M (S - 104) DIV_RET_O /\ L5.u64_at RSEGS M (S - 112) S /\ L5.u64_at RSEGS M (S - 120) (S - 96)
  /\ L5.u64_at RSEGS M (S - 128) F1 /\ L5.u64_at RSEGS M (S - 136) xo /\ L5.u64_at RSEGS M (S - 144) bo
  /\ L5.u64_at RSEGS M (S - 152) (F1 + 32) /\ L5.u64_at RSEGS M (S - 160) (F1 / 8 + SB) /\ L5.u64_at RSEGS M (S - 168) F1
  /\ L5.u64_at RSEGS M (S - 176) RETIRE_MAGIC
  /\ L5.u64_at RSEGS M (S - 184) (U R0 25) /\ L5.u64_at RSEGS M (S - 192) (U R0 26) /\ L5.u64_at RSEGS M (S - 200) (U R0 27).

Definition zero_throw_atA (L : asan_layout) (ar : asan_run) (SCR : Z) (LB : list (Z * Z)) (FF : list fframe)
           (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
           (S xo bo F1 fl1 F3 fl3 : Z) : Prop :=
  exists fden v16 v24,
     zero_throw_regs R0 R S F1 F3 xo fden
  /\ opmod_frame R0 M S F1 /\ divO_saves R0 M S F1 xo bo
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S - 392) F3 /\ L5.u64_at RSEGS M (S - 376) F3 /\ L5.u64_at RSEGS M (S - 288) F3
  /\ L5.u64_at RSEGS M (S - 360) (F3 + 32) /\ L5.u64_at RSEGS M (S - 352) xo
  /\ L5.u64_at RSEGS M (S - 336) (F3 / 8 + SB) /\ L5.u64_at RSEGS M (S - 296) SB
  (* [comment removed for export] *)
  /\ L5.big_at RSEGS M (F1 + 32) (L5.BO 0 0 (L5.BInl 0 0))
  /\ L5.big_at RSEGS M (F3 + 32) (L5.BO fden 0 (L5.BInl v16 v24))
  (* [comment removed for export] *)
  /\ sh_run M F1 0 4 0xf1 /\ sh_run M F1 4 4 0 /\ sh_run M F1 8 4 0xf3 /\ sh_run M F1 12 4 0
  /\ sh_run M F3 0 4 0xf1 /\ sh_run M F3 4 4 0
  /\ sh_run M F3 8 4 0xf2 /\ sh_run M F3 12 4 0xf8 /\ sh_run M F3 16 4 0xf2 /\ sh_run M F3 20 4 0xf8 /\ sh_run M F3 24 4 0xf2 /\ sh_run M F3 28 4 0xf8
  /\ sh_run M F3 32 4 0xf2 /\ sh_run M F3 36 4 0xf8 /\ sh_run M F3 40 4 0xf2 /\ sh_run M F3 44 4 0xf8 /\ sh_run M F3 48 4 0xf3 /\ sh_run M F3 52 12 0
  (* [comment removed for export] *)
  /\ fr_live L ar LB ((F1, 1, S - 64) :: FF) M 3 F3 fl3 (S - 416)
  /\ fr_live L ar LB FF M 1 F1 fl1 (S - 64)
  (* [comment removed for export] *)
  /\ ahpres L ar LB FF S SCR [] M0 M.

(* [comment removed for export] *)
Definition ff_e2 (FF : list fframe) (S F1 F3 : Z) : list fframe := (F3, 3, S - 416) :: (F1, 1, S - 64) :: FF.

(* [comment removed for export] *)
Definition ff_e3 (FF : list fframe) (S F1a F3a F1b F3b F1c F1d : Z) : list fframe :=
  (F1d, 1, S - 1184) :: (F1c, 1, S - 1056) :: (F3b, 3, S - 928) :: (F1b, 1, S - 576) :: (F3a, 3, S - 416) :: (F1a, 1, S - 64) :: FF.
(* [comment removed for export] *)
Definition assert_throw_regs (R0 R : bvmap 5 word) (S xo F1c F1d : Z) : Prop :=
     getr R 2%bv = Z_to_bv 64 (S - 1216) /\ getr R 3%bv = getr R0 3%bv /\ getr R 4%bv = getr R0 4%bv
  /\ getr R 10%bv = Z_to_bv 64 16
  /\ getr R 8%bv = Z_to_bv 64 (S - 1088) /\ getr R 9%bv = Z_to_bv 64 (S - 1216)
  /\ getr R 18%bv = Z_to_bv 64 F1d /\ getr R 19%bv = Z_to_bv 64 xo /\ getr R 20%bv = Z_to_bv 64 (F1d + 32)
  /\ getr R 21%bv = Z_to_bv 64 (xo + 8) /\ getr R 22%bv = Z_to_bv 64 (F1c / 8 + SB) /\ getr R 23%bv = Z_to_bv 64 (F1d / 8 + SB)
  /\ getr R 24%bv = Z_to_bv 64 F1d /\ getr R 25%bv = Z_to_bv 64 SB /\ getr R 26%bv = Z_to_bv 64 ((xo + 8) / 8 + SB) /\ getr R 27%bv = Z_to_bv 64 0.
(* [comment removed for export] *)
End SCFG_1.
End L5DSA.
