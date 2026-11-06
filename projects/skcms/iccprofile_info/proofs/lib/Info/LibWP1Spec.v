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

Record wp1_abi : Type := WP1 {
  w1_rte       : Z;   (* [comment removed for export] *)
  w1_memset    : Z;   (* [comment removed for export] *)
  w1_rcurve    : Z;   (* [comment removed for export] *)
  w1_rcurve_d  : Z;   (* [comment removed for export] *)
  w1_classify  : Z;   (* [comment removed for export] *)
  w1_gettag    : Z;   (* [comment removed for export] *)
  w1_tagxyz    : Z;   (* [comment removed for export] *)
  w1_xyzd50    : Z;   (* [comment removed for export] *)
  w1_xyzd50_d  : Z;   (* [comment removed for export] *)
  w1_ro_lo     : Z;   (* [comment removed for export] *)
  w1_ro_hi     : Z
}.

Definition wp1_src1 : wp1_abi :=
  WP1 0x130cc 0x1dfe4 0x1424c 64 0x13274 0x137b4 0x138e8 0x1485c 32 0x103ec 0x1048c.
Definition wp1_infoub : wp1_abi :=
  WP1 0x131b8 0x1eae0 0x1463c 32 0x133b8 0x13a68 0x13bd8 0x14d04 48 0x103ec 0x10490.

Section Specs.
Variable segs : list Segment.
Variable W : wp1_abi.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memset_pre (n al : Z) (d : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 10 = d /\ getr regs 11 = Z_to_bv 64 0 /\ getr regs 12 = Z_to_bv 64 n /\
  (bv_unsigned d mod al = 0) /\ writable segs mem (bv_unsigned d) n /\
  (bv_unsigned d + n <= 2 ^ 64).

Definition memset_post (n : Z) (d : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(d, n)] /\
  (forall i, 0 <= i < n -> mem' (Z_to_bv 64 (bv_unsigned d + i)) = Some (Z_to_bv 8 0)) /\
  getr regs' 10 = d.

Definition memset976_contract : Prop :=
  forall d, fn_contract segs (w1_memset W) (memset_pre 976 8 d) (memset_post 976 d).
Definition memset20_contract : Prop :=
  forall d, fn_contract segs (w1_memset W) (memset_pre 20 4 d) (memset_post 20 d).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rcurve_pre (data : word) (len : Z) (bs : list byte)
    (sp buf C cs : word) (size : Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  let d := w1_rcurve_d W in
  getr regs 2 = sp /\ getr regs 10 = buf /\ getr regs 11 = Z_to_bv 64 size /\
  getr regs 12 = C /\ getr regs 13 = cs /\
  data_ok mem data len bs /\ 0 <= size < 2 ^ 32 /\ inDATA data len (bv_unsigned buf) size /\
  writable segs mem c 32 /\ (c mod 8 = 0) /\
  (bv_unsigned sp mod 16 = 0) /\ writable segs mem (bv_unsigned sp - d) d /\
  rodata_clear mem (w1_ro_lo W) (w1_ro_hi W) /\
  (* [comment removed for export] *)
  (bv_unsigned data + len <= c \/ c + 32 <= bv_unsigned data) /\
  (bv_unsigned sp <= c \/ c + 32 <= bv_unsigned sp - d) /\
  (bv_unsigned data + len <= bv_unsigned sp - d \/ bv_unsigned sp <= bv_unsigned data) /\
  (* [comment removed for export] *)
  (bv_unsigned cs = 0 \/
   (writable segs mem (bv_unsigned cs) 4 /\ (bv_unsigned cs mod 4 = 0) /\
    (bv_unsigned data + len <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned data) /\
    (c + 32 <= bv_unsigned cs \/ bv_unsigned cs + 4 <= c) /\
    (bv_unsigned sp <= bv_unsigned cs \/ bv_unsigned cs + 4 <= bv_unsigned sp - d))).

Definition rcurve_post (data : word) (len : Z) (bs : list byte)
    (sp buf C cs : word) (size : Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  let d := w1_rcurve_d W in
  frame_mod mem mem'
    ((Z_to_bv 64 (bv_unsigned sp - d), d) :: (C, 32)
      :: (if Z.eq_dec (bv_unsigned cs) 0 then [] else [(cs, 4)])) /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
    (r = 1 -> curve_ok segs mem' data len c) /\
    (curve_ok segs mem data len c -> curve_ok segs mem' data len c) /\
    (bv_unsigned cs <> 0 -> r = 1 -> exists v, cell32 segs mem' (bv_unsigned cs) v).

Definition read_curve_contract : Prop :=
  forall data len bs sp buf C cs size,
    fn_contract segs (w1_rcurve W)
      (rcurve_pre data len bs sp buf C cs size)
      (rcurve_post data len bs sp buf C cs size).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rte_pre (data : word) (len : Z) (bs : list byte) (c : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 10 = c /\ data_ok mem data len bs /\ curve_ok segs mem data len (bv_unsigned c) /\ (bv_unsigned c mod 8 = 0) /\ (bv_unsigned c + 32 <= 2 ^ 64).

Definition rte_post (data : word) (len : Z) (bs : list byte) (c : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  mem' = mem.

Definition rte_contract (entry : Z) : Prop :=
  forall data len bs c,
    fn_contract segs entry (rte_pre data len bs c) (rte_post data len bs c).

(* [comment removed for export] *)

End Specs.
