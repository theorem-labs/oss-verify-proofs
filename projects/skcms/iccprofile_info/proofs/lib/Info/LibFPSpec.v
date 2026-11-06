(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record wp3_abi : Type := WP3 {
  w3_evalc     : Z;   (* [comment removed for export] *)
  w3_fitlin    : Z;   (* [comment removed for export] *)
  w3_fitlin_fr : Z;   (* [comment removed for export] *)
  w3_canon     : Z;   (* [comment removed for export] *)
  w3_canon_d   : Z;   (* [comment removed for export] *)
  w3_memset    : Z;   (* [comment removed for export] *)
  w3_ro_lo     : Z;   (* [comment removed for export] *)
  w3_ro_hi     : Z
}.

Definition wp3_src1 : wp3_abi :=
  WP3 0x136d8 0x15b14 112 0x15ca8 160 0x1dfe4 0x103ec 0x1048c.
Definition wp3_infoub : wp3_abi :=
  WP3 0x138a4 0x163f0 128 0x165ac 176 0x1eae0 0x103ec 0x10490.

Section Specs.
Variable segs : list Segment.
Variable W : wp3_abi.

#[local] Abbreviation cell := (cell segs).
#[local] Abbreviation cell32 := (cell32 segs).
#[local] Abbreviation cell64 := (cell64 segs).
#[local] Abbreviation writable := (writable segs).
#[local] Abbreviation curve_ok := (curve_ok segs).

(* [comment removed for export] *)
Definition table_curve (mem : word -> option byte) (data : word) (len : Z)
    (c : Z) (n : Z) (t8 t16 : word) : Prop :=
  cell32 mem c n /\ cell64 mem (c + 8) t8 /\ cell64 mem (c + 16) t16 /\
  2 <= n <= 2 ^ 24 /\
  (bv_unsigned t8 <> 0 -> inDATA data len (bv_unsigned t8) n) /\
  (bv_unsigned t16 <> 0 -> inDATA data len (bv_unsigned t16) (2 * n)) /\
  (bv_unsigned t8 <> 0 \/ bv_unsigned t16 <> 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eval_curve_pre (data : word) (len : Z) (bs : list byte)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  exists (c t8 t16 : word) (n : Z),
    getr regs 10 = c /\ (bv_unsigned c mod 8 = 0) /\ (bv_unsigned c + 24 <= 2 ^ 64) /\
    table_curve mem data len (bv_unsigned c) n t8 t16 /\
    data_ok mem data len bs /\ rodata_clear mem (w3_ro_lo W) (w3_ro_hi W).

Definition eval_curve_post
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  mem' = mem.

Definition eval_curve_contract : Prop :=
  forall data len bs, fn_contract segs (w3_evalc W) (eval_curve_pre data len bs) eval_curve_post.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fitlin_pre (data : word) (len : Z) (bs : list byte)
    (sp C : word) (n : Z) (t8 t16 : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let s := bv_unsigned sp in
  let c := bv_unsigned C in
  let fr := w3_fitlin_fr W in
  getr regs 2 = sp /\ getr regs 10 = C /\ getr regs 11 = Z_to_bv 64 n /\
  getr regs 12 = Z_to_bv 64 (s + 12) /\ getr regs 13 = Z_to_bv 64 (s + 8) /\
  getr regs 14 = Z_to_bv 64 (s + 4) /\
  (s mod 16 = 0) /\ writable mem (s - fr) (fr + 16) /\
  (exists w, cell mem (s + 12) 4 w) /\
  (c mod 8 = 0) /\ (c + 32 <= 2 ^ 64) /\
  table_curve mem data len c n t8 t16 /\
  data_ok mem data len bs /\ rodata_clear mem (w3_ro_lo W) (w3_ro_hi W) /\
  (* [comment removed for export] *)
  (s + 16 <= c \/ c + 32 <= s - fr) /\
  (bv_unsigned data + len <= s - fr \/ s + 16 <= bv_unsigned data).

Definition fitlin_post (data : word) (len : Z) (bs : list byte)
    (sp C : word) (n : Z) (t8 t16 : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let s := bv_unsigned sp in
  let fr := w3_fitlin_fr W in
  frame_mod mem mem' [(Z_to_bv 64 (s - fr), fr + 16)] /\
  (exists w, cell mem' (s + 12) 4 w) /\ (exists w, cell mem' (s + 4) 4 w) /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ 1 <= r <= n.

Definition fit_linear_contract : Prop :=
  forall data len bs sp C n t8 t16,
    fn_contract segs (w3_fitlin W)
      (fitlin_pre data len bs sp C n t8 t16)
      (fitlin_post data len bs sp C n t8 t16).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition canon_pre (data : word) (len : Z) (bs : list byte) (sp C : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let s := bv_unsigned sp in
  let c := bv_unsigned C in
  let d := w3_canon_d W in
  getr regs 2 = sp /\ getr regs 10 = C /\
  (s mod 16 = 0) /\ writable mem (s - d) d /\
  (c mod 8 = 0) /\ writable mem c 32 /\ (c + 32 < 2 ^ 64) /\
  curve_ok mem data len c /\
  data_ok mem data len bs /\ rodata_clear mem (w3_ro_lo W) (w3_ro_hi W) /\
  (s <= c \/ c + 32 <= s - d) /\
  (bv_unsigned data + len <= c \/ c + 32 <= bv_unsigned data) /\
  (bv_unsigned data + len <= s - d \/ s <= bv_unsigned data).

Definition canon_post (data : word) (len : Z) (bs : list byte) (sp C : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - w3_canon_d W), w3_canon_d W); (C, 32)] /\
  curve_ok mem' data len (bv_unsigned C).

Definition canonicalize_contract : Prop :=
  forall data len bs sp C,
    fn_contract segs (w3_canon W) (canon_pre data len bs sp C) (canon_post data len bs sp C).

End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
