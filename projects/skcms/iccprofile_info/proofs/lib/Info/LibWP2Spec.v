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

Record wp2_abi : Type := WP2 {
  w_mftc_a2b   : Z;   (* [comment removed for export] *)
  w_mftc_b2a   : Z;   (* [comment removed for export] *)
  w_init_a2b   : Z;   (* [comment removed for export] *)
  w_init_b2a   : Z;   (* [comment removed for export] *)
  w_init_fr    : Z;   (* [comment removed for export] *)
  w_rcurves    : Z;   (* [comment removed for export] *)
  w_rcurves_d  : Z;   (* [comment removed for export] *)
  w_a2b        : Z;   (* [comment removed for export] *)
  w_b2a        : Z;   (* [comment removed for export] *)
  w_ab_d       : Z;   (* [comment removed for export] *)
  w_ro_lo      : Z;   (* [comment removed for export] *)
  w_ro_hi      : Z
}.

(* [comment removed for export] *)
Definition wp2_src1 : wp2_abi :=
  WP2 0x15d58 0x15ffc 0x15dc8 0x16070 16 0x15f1c 144 0x148ec 0x151f8 336 0x103ec 0x1048c.
Definition wp2_infoub : wp2_abi :=
  WP2 0x1667c 0x16a34 0x16704 0x16aac 32 0x16914 128 0x14e04 0x15898 352 0x103ec 0x10490.

Section Specs.
Variable segs : list Segment.
Variable W : wp2_abi.

#[local] Notation cell32 := (cell32 segs).
#[local] Notation cell64 := (cell64 segs).
#[local] Notation cell8 := (cell8 segs).
#[local] Notation writable := (writable segs).
#[local] Notation curve_ok := (curve_ok segs).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mftc_a2b_pre (data : word) (len : Z) (bs : list byte) (mft A : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 10 = mft /\ getr regs 11 = A /\
  data_ok mem data len bs /\ inDATA data len (bv_unsigned mft) 48 /\
  writable mem (bv_unsigned A) 400 /\ (bv_unsigned A mod 8 = 0) /\
  (bv_unsigned data + len <= bv_unsigned A \/ bv_unsigned A + 400 <= bv_unsigned data).

Definition mftc_a2b_post (data : word) (len : Z) (bs : list byte) (mft A : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  frame_mod mem mem' [(Z_to_bv 64 (a + 144), 8); (Z_to_bv 64 (a + 296), 8)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 ->
     exists ic g,
       1 <= ic <= 4 /\ 2 <= g <= 255 /\
       cell32 mem' (a + 144) ic /\ cell32 mem' (a + 296) 0 /\ cell32 mem' (a + 300) 3 /\
       (forall i, 0 <= i < ic -> cell8 mem' (a + 148 + i) g)).

Definition read_mft_common_a2b_contract : Prop :=
  forall data len bs mft A,
    fn_contract segs (w_mftc_a2b W) (mftc_a2b_pre data len bs mft A) (mftc_a2b_post data len bs mft A).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mftc_b2a_pre (data : word) (len : Z) (bs : list byte) (mft B : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  getr regs 10 = mft /\ getr regs 11 = B /\
  data_ok mem data len bs /\ inDATA data len (bv_unsigned mft) 48 /\
  writable mem (bv_unsigned B) 400 /\ (bv_unsigned B mod 8 = 0) /\
  (bv_unsigned data + len <= bv_unsigned B \/ bv_unsigned B + 400 <= bv_unsigned data).

Definition mftc_b2a_post (data : word) (len : Z) (bs : list byte) (mft B : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  frame_mod mem mem' [(Z_to_bv 64 (b + 96), 8); (Z_to_bv 64 (b + 392), 8)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 ->
     exists oc g,
       3 <= oc <= 4 /\ 2 <= g <= 255 /\
       cell32 mem' (b + 96) 3 /\ cell32 mem' (b + 100) 0 /\ cell32 mem' (b + 396) oc /\
       (forall i, 0 <= i < 3 -> cell8 mem' (b + 392 + i) g)).

Definition read_mft_common_b2a_contract : Prop :=
  forall data len bs mft B,
    fn_contract segs (w_mftc_b2a W) (mftc_b2a_pre data len bs mft B) (mftc_b2a_post data len bs mft B).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition itab_a2b_pre (data : word) (len : Z) (bs : list byte)
    (sp tb A : word) (maxlen bw ite ote ic : Z) (gps : list Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  getr regs 2 = sp /\ getr regs 10 = tb /\ getr regs 11 = Z_to_bv 64 maxlen /\
  getr regs 12 = Z_to_bv 64 bw /\ getr regs 13 = Z_to_bv 64 ite /\ getr regs 14 = Z_to_bv 64 ote /\
  getr regs 15 = A /\
  data_ok mem data len bs /\ 0 <= maxlen /\ inDATA data len (bv_unsigned tb) maxlen /\
  (bw = 1 \/ bw = 2) /\ 2 <= ite <= 4096 /\ 2 <= ote <= 4096 /\
  1 <= ic <= 4 /\ Z.of_nat (length gps) = ic /\ Forall (fun g => 2 <= g <= 255) gps /\
  cell32 mem (a + 144) ic /\ cell32 mem (a + 300) 3 /\
  (forall i, 0 <= i < ic -> cell8 mem (a + 148 + i) (nth (Z.to_nat i) gps 0)) /\
  writable mem (a + 0) 400 /\ (a mod 8 = 0) /\ 0 < a /\
  writable mem (bv_unsigned sp - w_init_fr W) (w_init_fr W) /\
  (* [comment removed for export] *)
  (bv_unsigned sp <= a \/ a + 400 <= bv_unsigned sp - w_init_fr W) /\
  (bv_unsigned data + len <= a \/ a + 400 <= bv_unsigned data) /\
  (bv_unsigned data + len <= bv_unsigned sp - w_init_fr W \/ bv_unsigned sp <= bv_unsigned data).

Definition itab_a2b_post (data : word) (len : Z) (bs : list byte)
    (sp tb A : word) (maxlen bw ite ote ic : Z) (gps : list Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  let stk := (Z_to_bv 64 (bv_unsigned sp - w_init_fr W), w_init_fr W) in
  exists r, getr regs' 10 = Z_to_bv 64 r /\
  ((r = 0 /\ frame_mod mem mem' [stk])
   \/ (r = 1 /\
       frame_mod mem mem' [stk; (Z_to_bv 64 a, 32 * ic); (Z_to_bv 64 (a + 128), 16); (Z_to_bv 64 (a + 304), 96)] /\
       (forall i, 0 <= i < ic -> curve_ok mem' data len (a + 32 * i)) /\
       (forall i, 0 <= i < 3 -> curve_ok mem' data len (a + 304 + 32 * i)) /\
       exists g8 g16 : word,
         cell64 mem' (a + 128) g8 /\ cell64 mem' (a + 136) g16 /\
         (bw = 1 -> bv_unsigned g16 = 0 /\ inDATA data len (bv_unsigned g8) (3 * zprod gps)) /\
         (bw = 2 -> bv_unsigned g8 = 0 /\ inDATA data len (bv_unsigned g16) (2 * (3 * zprod gps))))).

Definition init_tables_a2b_contract : Prop :=
  forall data len bs sp tb A maxlen bw ite ote ic gps,
    fn_contract segs (w_init_a2b W)
      (itab_a2b_pre data len bs sp tb A maxlen bw ite ote ic gps)
      (itab_a2b_post data len bs sp tb A maxlen bw ite ote ic gps).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition itab_b2a_pre (data : word) (len : Z) (bs : list byte)
    (sp tb B : word) (maxlen bw ite ote oc : Z) (gps : list Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  getr regs 2 = sp /\ getr regs 10 = tb /\ getr regs 11 = Z_to_bv 64 maxlen /\
  getr regs 12 = Z_to_bv 64 bw /\ getr regs 13 = Z_to_bv 64 ite /\ getr regs 14 = Z_to_bv 64 ote /\
  getr regs 15 = B /\
  data_ok mem data len bs /\ 0 <= maxlen /\ inDATA data len (bv_unsigned tb) maxlen /\
  (bw = 1 \/ bw = 2) /\ 2 <= ite <= 4096 /\ 2 <= ote <= 4096 /\
  3 <= oc <= 4 /\ Z.of_nat (length gps) = 3 /\ Forall (fun g => 2 <= g <= 255) gps /\
  cell32 mem (b + 96) 3 /\ cell32 mem (b + 396) oc /\
  (forall i, 0 <= i < 3 -> cell8 mem (b + 392 + i) (nth (Z.to_nat i) gps 0)) /\
  writable mem (b + 0) 400 /\ (b mod 8 = 0) /\ 0 < b /\
  writable mem (bv_unsigned sp - w_init_fr W) (w_init_fr W) /\
  (bv_unsigned sp <= b \/ b + 400 <= bv_unsigned sp - w_init_fr W) /\
  (bv_unsigned data + len <= b \/ b + 400 <= bv_unsigned data) /\
  (bv_unsigned data + len <= bv_unsigned sp - w_init_fr W \/ bv_unsigned sp <= bv_unsigned data).

Definition itab_b2a_post (data : word) (len : Z) (bs : list byte)
    (sp tb B : word) (maxlen bw ite ote oc : Z) (gps : list Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  let stk := (Z_to_bv 64 (bv_unsigned sp - w_init_fr W), w_init_fr W) in
  exists r, getr regs' 10 = Z_to_bv 64 r /\
  ((r = 0 /\ frame_mod mem mem' [stk])
   \/ (r = 1 /\
       frame_mod mem mem' [stk; (Z_to_bv 64 b, 96); (Z_to_bv 64 (b + 248), 32 * oc); (Z_to_bv 64 (b + 376), 16)] /\
       (forall i, 0 <= i < 3 -> curve_ok mem' data len (b + 32 * i)) /\
       (forall i, 0 <= i < oc -> curve_ok mem' data len (b + 248 + 32 * i)) /\
       exists g8 g16 : word,
         cell64 mem' (b + 376) g8 /\ cell64 mem' (b + 384) g16 /\
         (bw = 1 -> bv_unsigned g16 = 0 /\ inDATA data len (bv_unsigned g8) (oc * zprod gps)) /\
         (bw = 2 -> bv_unsigned g8 = 0 /\ inDATA data len (bv_unsigned g16) (2 * (oc * zprod gps))))).

Definition init_tables_b2a_contract : Prop :=
  forall data len bs sp tb B maxlen bw ite ote oc gps,
    fn_contract segs (w_init_b2a W)
      (itab_b2a_pre data len bs sp tb B maxlen bw ite ote oc gps)
      (itab_b2a_post data len bs sp tb B maxlen bw ite ote oc gps).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rcurves_pre (data : word) (len : Z) (bs : list byte)
    (sp buf C : word) (size : Z) (offw : word) (k : Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  getr regs 2 = sp /\ getr regs 10 = buf /\ getr regs 11 = Z_to_bv 64 size /\
  getr regs 12 = offw /\ getr regs 13 = Z_to_bv 64 k /\ getr regs 14 = C /\
  data_ok mem data len bs /\ 0 <= size < 2 ^ 32 /\
  inDATA data len (bv_unsigned buf) size /\
  0 <= k <= 4 /\ (0 < k -> writable mem c (32 * k)) /\ (c mod 8 = 0) /\ (0 < k -> c + 32 * k <= 2 ^ 64) /\
  (bv_unsigned sp mod 16 = 0) /\
  writable mem (bv_unsigned sp - w_rcurves_d W) (w_rcurves_d W) /\
  rodata_clear mem (w_ro_lo W) (w_ro_hi W) /\
  (bv_unsigned sp <= c \/ c + 32 * k <= bv_unsigned sp - w_rcurves_d W) /\
  (bv_unsigned data + len <= c \/ c + 32 * k <= bv_unsigned data) /\
  (bv_unsigned data + len <= bv_unsigned sp - w_rcurves_d W \/ bv_unsigned sp <= bv_unsigned data).

Definition rcurves_post (data : word) (len : Z) (bs : list byte)
    (sp buf C : word) (size : Z) (offw : word) (k : Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - w_rcurves_d W), w_rcurves_d W); (Z_to_bv 64 c, 32 * k)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 -> forall i, 0 <= i < k -> curve_ok mem' data len (c + 32 * i)).

Definition read_curves_contract : Prop :=
  forall data len bs sp buf C size offw k,
    fn_contract segs (w_rcurves W)
      (rcurves_pre data len bs sp buf C size offw k)
      (rcurves_post data len bs sp buf C size offw k).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a2b_curve_offsets : list Z := [0; 32; 64; 96; 152; 184; 216; 304; 336; 368].

Definition a2b_grid_ok (mem : word -> option byte) (data : word) (len : Z) (a : Z) : Prop :=
  exists (ic oc : Z) (gps : list Z) (g8 g16 : word),
    cell32 mem (a + 144) ic /\ cell32 mem (a + 300) oc /\
    0 <= ic <= 4 /\ Z.of_nat (length gps) = ic /\ Forall (fun g => 2 <= g <= 255) gps /\
    (forall i, 0 <= i < ic -> cell8 mem (a + 148 + i) (nth (Z.to_nat i) gps 0)) /\
    cell64 mem (a + 128) g8 /\ cell64 mem (a + 136) g16 /\
    oc = 3 /\
    (ic <> 0 ->
       (bv_unsigned g8 <> 0 -> inDATA data len (bv_unsigned g8) (oc * zprod gps)) /\
       (bv_unsigned g16 <> 0 -> inDATA data len (bv_unsigned g16) (2 * (oc * zprod gps)))).

Definition a2b_pre (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let a := bv_unsigned A in let t := bv_unsigned T in
  getr regs 2 = sp /\ getr regs 10 = T /\ getr regs 11 = A /\ getr regs 12 = Z_to_bv 64 pcs /\
  getr regs 13 = Z_to_bv 64 (bv_unsigned data + len) /\ (pcs = 0 \/ pcs = 1) /\
  data_ok mem data len bs /\
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok segs mem data len t /\
  (t mod 8 = 0) /\ t + 24 <= 2 ^ 64 /\
  writable mem a 400 /\ (a mod 8 = 0) /\ 0 < a /\ a + 400 < 2 ^ 64 /\
  Forall (fun off => curve_ok mem data len (a + off)) a2b_curve_offsets /\
  (exists g8 g16, cell64 mem (a + 128) g8 /\ cell64 mem (a + 136) g16) /\
  (bv_unsigned sp mod 16 = 0) /\
  writable mem (bv_unsigned sp - w_ab_d W) (w_ab_d W) /\
  rodata_clear mem (w_ro_lo W) (w_ro_hi W) /\
  (* [comment removed for export] *)
  (bv_unsigned sp <= t \/ t + 24 <= bv_unsigned sp - w_ab_d W) /\
  (bv_unsigned sp <= a \/ a + 400 <= bv_unsigned sp - w_ab_d W) /\
  (t + 24 <= a \/ a + 400 <= t) /\
  (bv_unsigned data + len <= a \/ a + 400 <= bv_unsigned data) /\
  (bv_unsigned data + len <= t \/ t + 24 <= bv_unsigned data) /\
  (bv_unsigned data + len <= bv_unsigned sp - w_ab_d W \/ bv_unsigned sp <= bv_unsigned data).

Definition a2b_post (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - w_ab_d W), w_ab_d W); (Z_to_bv 64 a, 400)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 ->
     Forall (fun off => curve_ok mem' data len (a + off)) a2b_curve_offsets /\
     a2b_grid_ok mem' data len a).

Definition read_a2b_contract : Prop :=
  forall data len bs sp T A pcs,
    fn_contract segs (w_a2b W) (a2b_pre data len bs sp T A pcs) (a2b_post data len bs sp T A pcs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b2a_curve_offsets : list Z := [0; 32; 64; 104; 136; 168; 248; 280; 312; 344].

Definition b2a_pre (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let b := bv_unsigned B in let t := bv_unsigned T in
  getr regs 2 = sp /\ getr regs 10 = T /\ getr regs 11 = B /\ getr regs 12 = Z_to_bv 64 pcs /\
  getr regs 13 = Z_to_bv 64 (bv_unsigned data + len) /\ (pcs = 0 \/ pcs = 1) /\
  data_ok mem data len bs /\
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok segs mem data len t /\
  (t mod 8 = 0) /\ t + 24 <= 2 ^ 64 /\
  writable mem b 400 /\ (b mod 8 = 0) /\ 0 < b /\ b + 400 < 2 ^ 64 /\
  Forall (fun off => curve_ok mem data len (b + off)) b2a_curve_offsets /\
  (bv_unsigned sp mod 16 = 0) /\
  writable mem (bv_unsigned sp - w_ab_d W) (w_ab_d W) /\
  rodata_clear mem (w_ro_lo W) (w_ro_hi W) /\
  (bv_unsigned sp <= t \/ t + 24 <= bv_unsigned sp - w_ab_d W) /\
  (bv_unsigned sp <= b \/ b + 400 <= bv_unsigned sp - w_ab_d W) /\
  (t + 24 <= b \/ b + 400 <= t) /\
  (bv_unsigned data + len <= b \/ b + 400 <= bv_unsigned data) /\
  (bv_unsigned data + len <= t \/ t + 24 <= bv_unsigned data) /\
  (bv_unsigned data + len <= bv_unsigned sp - w_ab_d W \/ bv_unsigned sp <= bv_unsigned data).

Definition b2a_post (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - w_ab_d W), w_ab_d W); (Z_to_bv 64 b, 400)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 -> Forall (fun off => curve_ok mem' data len (b + off)) b2a_curve_offsets).

Definition read_b2a_contract : Prop :=
  forall data len bs sp T B pcs,
    fn_contract segs (w_b2a W) (b2a_pre data len bs sp T B pcs) (b2a_post data len bs sp T B pcs).

End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
