(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SoftFloat.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import F_extenddftf2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.


Section CANSEC1. Context {rc : runConstT}.
Definition pop_arg_entry := 0xbde58%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_DBL := 25%Z.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at bsegs m VA (u64s slots).

(* [comment removed for export] *)
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
  if (ty =? T_PTR)%Z then slot
  else if (ty =? T_INT)%Z then sx32 slot
  else if (ty =? T_UINT)%Z then zx32 slot
  else Z_to_bv 64 (lo64 (f128_of_d (bv_unsigned slot))).
Definition pop_arg_hi (ty : Z) (slot y : word) : word :=
  if (ty =? T_DBL)%Z then Z_to_bv 64 (hi64 (f128_of_d (bv_unsigned slot))) else y.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells bsegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ rw_cells bsegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
    /\ va_area m' VA slots
    /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma va_read8 : forall m VA slots (i : Z) w a,
  bytes_at bsegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes bsegs m a 8 = Some (le8 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read bsegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma va_read4 : forall m VA slots (i : Z) w a,
  bytes_at bsegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes bsegs m a 4 = Some (le4 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read bsegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8. reflexivity.
Qed.

Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. lia. Qed.

End CANSEC1.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Section CANSEC2. Context {rc : runConstT}.
Lemma pop_arg_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells bsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells bsegs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk bsegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv bsegs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG (bv_unsigned sp - 16) 16 -> rng RNG (bv_unsigned a2) 8 -> rng RNG (bv_unsigned a0) 16 ->
  rng RNG VA (8 * Z.of_nat (length slots)) ->
  evtF bsegs RNG (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbde58) fc None m (seg_rom bsegs)).
Proof.
  intros until y. intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4 RIMG RFR RAP RARG RVA.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_DBL.
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    carve_frame 16%nat ST.
    zstep. zstep. zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep.
    zstep. call extenddftf2_spec. 1:{ exact MI. }
    rewrite freg_get_same by reflexivity.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
    { intros k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned 10) with 10%Z. lia. }
Qed.
End CANSEC2.
