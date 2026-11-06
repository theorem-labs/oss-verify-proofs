(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP FpBound FpReal.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk Bi_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record hpp : Type := mk_hpp {
  hp_S1 : Z;                      (* [comment removed for export] *)
  hp_DS : Z; hp_DT : Z; hp_N : Z; (* [comment removed for export] *)
  hp_SP : Z; hp_RR : Z;           (* [comment removed for export] *)
  hp_w : Z; hp_h : Z;             (* [comment removed for export] *)
  hp_wpl : Z; hp_ht : Z;          (* [comment removed for export] *)
  hp_c : Z }.                     (* [comment removed for export] *)

Definition hp_ok (p : hpp) : Prop :=
  0 < hp_w p <= 20000 /\ 0 < hp_h p <= 20000 /\ hp_w p + 22 <= 4 * hp_wpl p /\ hp_h p + 22 <= hp_ht p /\ 0 < hp_wpl p
  /\ hp_N p = 4 * (hp_wpl p * hp_ht p) /\ hp_wpl p * hp_ht p <= 2^26 /\ 0 <= hp_c p <= 255
  /\ 0 < hp_DS p /\ hp_DS p mod 4 = 0 /\ hp_DS p + hp_N p <= 2^47 /\ (hp_DS p + hp_N p <= 0x7fff7000 \/ 0x10007fff8000 <= hp_DS p)
  /\ 0 < hp_DT p /\ hp_DT p mod 4 = 0 /\ hp_DT p + hp_N p <= 2^47 /\ (hp_DT p + hp_N p <= 0x7fff7000 \/ 0x10007fff8000 <= hp_DT p)
  /\ 0 < hp_SP p /\ hp_SP p mod 16 = 0 /\ hp_SP p + 44 <= 2^47 /\ (hp_SP p + 44 <= 0x7fff7000 \/ 0x10007fff8000 <= hp_SP p)
  /\ 0 < hp_RR p /\ hp_RR p mod 16 = 0 /\ hp_RR p + 1024 <= 2^47 /\ (hp_RR p + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= hp_RR p)
  /\ 0x10007fff8000 <= hp_S1 p /\ hp_S1 p mod 16 = 0 /\ hp_S1 p + 192 <= 2^47
  /\ (hp_S1 p + 192 <= hp_DT p \/ hp_DT p + hp_N p <= hp_S1 p).

(* [comment removed for export] *)
Definition hp_kcells (p : hpp) (ks rs : Z -> Z) (m : mem) : Prop :=
  (forall q, 0 <= q < 11 -> rw_cells asegs m (hp_SP p + 4 * q) [C4 (Z_to_bv 64 (ks q))] /\ FB fmt_single 1 (ks q)) /\ acc asegs m (hp_SP p) 44
  /\ (forall q, 0 <= q < 256 -> rw_cells asegs m (hp_RR p + 4 * q) [C4 (Z_to_bv 64 (rs q))] /\ FB fmt_single 1 (rs q)) /\ acc asegs m (hp_RR p) 1024.

(* [comment removed for export] *)
Definition hp_ro (p : hpp) (ks rs : Z -> Z) (m : mem) : Prop :=
  rw_cells asegs m (hp_S1 p + 112) [C8 (Z_to_bv 64 (hp_wpl p))] /\ rw_cells asegs m (hp_S1 p + 128) [C8 (Z_to_bv 64 (hp_DS p))]
  /\ rw_cells asegs m (hp_S1 p + 136) [C8 (Z_to_bv 64 (hp_h p))] /\ rw_cells asegs m (hp_S1 p + 144) [C8 (Z_to_bv 64 (hp_DT p))]
  /\ rw_cells asegs m (hp_S1 p + 152) [C8 (Z_to_bv 64 0x10768)] /\ rw_cells asegs m (hp_S1 p + 160) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (hp_S1 p + 168) [C8 (Z_to_bv 64 (hp_w p))] /\ rw_cells asegs m (hp_S1 p + 176) [C8 (Z_to_bv 64 18446744073709551606)]
  /\ rw_cells asegs m (hp_S1 p + 184) [C8 (Z_to_bv 64 1)]
  /\ wr_at asegs m (hp_DS p) (hp_N p) /\ acc asegs m (hp_DS p) (hp_N p) /\ hp_kcells p ks rs m.

(* [comment removed for export] *)
Definition hp_fregs (F : bvmap 5 word) : Prop :=
  reg_get F (Z_to_bv 5 8) = Z_to_bv 64 p_lo_d /\ reg_get F (Z_to_bv 5 9) = Z_to_bv 64 p_hi_d /\ reg_get F (Z_to_bv 5 18) = nan_box (Z_to_bv 32 p_zero).

(* [comment removed for export] *)
Definition bc_hp_exit (p : hpp) (sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (hp_S1 p)) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0xcfa14) fc' None m' (seg_rom asegs)
    /\ fs_agree F F' /\ frm0 fc' /\ munch [(hp_DT p, hp_DT p + hp_N p)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Definition bc_hpass_stmt : Prop :=
  forall (p : hpp) (ks rs : Z -> Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  hp_ok p -> frm0 fc -> hp_fregs F ->
  (forall m', munch [(hp_DT p, hp_DT p + hp_N p)] m m' -> wmono asegs m m' -> hp_ro p ks rs m') ->
  wr_at asegs m (hp_DT p) (hp_N p) -> acc asegs m (hp_DT p) (hp_N p) -> mem_inv asegs m ->
  evt asegs (bc_hp_exit p sp gp tp s0 (Z_to_bv 64 (hp_RR p)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (hp_wpl p)) (Z_to_bv 64 3) (Z_to_bv 64 1)
               (Z_to_bv 64 (18446744073709551615 - hp_RR p)) (Z_to_bv 64 1) (Z_to_bv 64 10) (Z_to_bv 64 (hp_c p)) (Z_to_bv 64 (hp_SP p)) F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (hp_S1 p)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (hp_RR p)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (hp_wpl p)) (Z_to_bv 64 3) (Z_to_bv 64 1)
             (Z_to_bv 64 (18446744073709551615 - hp_RR p)) (Z_to_bv 64 1) (Z_to_bv 64 10) (Z_to_bv 64 (hp_c p)) (Z_to_bv 64 (hp_SP p))
             t3 (Z_to_bv 64 11) t5 t6)
        F (Z_to_bv 64 0xcf770) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition vp_ok (p : hpp) (DD ND wpld : Z) : Prop :=
  0 < wpld /\ hp_w p <= 4 * wpld /\ ND = 4 * (wpld * hp_h p) /\ wpld * hp_h p <= 2^26
  /\ 0 < DD /\ DD mod 4 = 0 /\ DD + ND <= 2^47 /\ (DD + ND <= 0x7fff7000 \/ 0x10007fff8000 <= DD)
  /\ (hp_S1 p + 192 <= DD \/ DD + ND <= hp_S1 p).

Definition vp_ro (p : hpp) (ks rs : Z -> Z) (DD : Z) (m : mem) : Prop :=
  rw_cells asegs m (hp_S1 p + 80) [C8 (Z_to_bv 64 11)] /\ rw_cells asegs m (hp_S1 p + 120) [C8 (Z_to_bv 64 DD)]
  /\ rw_cells asegs m (hp_S1 p + 136) [C8 (Z_to_bv 64 (hp_h p))] /\ rw_cells asegs m (hp_S1 p + 144) [C8 (Z_to_bv 64 (hp_DT p))]
  /\ rw_cells asegs m (hp_S1 p + 152) [C8 (Z_to_bv 64 0x10768)] /\ rw_cells asegs m (hp_S1 p + 160) [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (hp_S1 p + 168) [C8 (Z_to_bv 64 (hp_w p))] /\ rw_cells asegs m (hp_S1 p + 176) [C8 (Z_to_bv 64 18446744073709551606)]
  /\ wr_at asegs m (hp_DT p) (hp_N p) /\ acc asegs m (hp_DT p) (hp_N p) /\ hp_kcells p ks rs m.

(* [comment removed for export] *)
Definition bc_vp_exit (p : hpp) (DD ND : Z) (sp gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 11) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (hp_S1 p)) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (Z_to_bv 64 0xcf6dc) fc' None m' (seg_rom asegs)
    /\ fs_agree F F' /\ frm0 fc' /\ munch [(DD, DD + ND)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

Definition bc_vpass_stmt : Prop :=
  forall (p : hpp) (ks rs : Z -> Z) (DD ND wpld : Z) (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  hp_ok p -> vp_ok p DD ND wpld -> frm0 fc -> hp_fregs F ->
  (forall m', munch [(DD, DD + ND)] m m' -> wmono asegs m m' -> vp_ro p ks rs DD m') ->
  wr_at asegs m DD ND -> acc asegs m DD ND -> mem_inv asegs m ->
  evt asegs (bc_vp_exit p DD ND sp gp tp s0 (Z_to_bv 64 (hp_RR p)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (hp_wpl p)) (Z_to_bv 64 3) (Z_to_bv 64 1)
               (Z_to_bv 64 (18446744073709551615 - hp_RR p)) (Z_to_bv 64 1) (Z_to_bv 64 10) (Z_to_bv 64 (hp_c p)) (Z_to_bv 64 (hp_SP p)) F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (hp_S1 p)) (Z_to_bv 64 wpld) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (hp_RR p)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (hp_wpl p)) (Z_to_bv 64 3) (Z_to_bv 64 1)
             (Z_to_bv 64 (18446744073709551615 - hp_RR p)) (Z_to_bv 64 1) (Z_to_bv 64 10) (Z_to_bv 64 (hp_c p)) (Z_to_bv 64 (hp_SP p))
             t3 t4 t5 t6)
        F (Z_to_bv 64 0xcfa38) fc None m (seg_rom asegs)).
