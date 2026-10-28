(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit F_memset.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import MagicDiv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeMagic W_posix_to_tm W_gmtime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma zlit_fold : forall (e v : Z), (bv_unsigned (Z_to_bv 64 e) = v)%Z -> Z_to_bv 64 e = Z_to_bv 64 v.
Proof.
  intros e v H. apply bv_eq. rewrite H. symmetry. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 e)) as R.
  rewrite H in R. unfold bv_wrap. rewrite Z.mod_small; [reflexivity| exact R].
Qed.
Ltac zl_has_var c := match c with context [?x] => is_var x end.
Ltac zlits :=
  repeat match goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with
      | context [Z_to_bv 64 ?e] =>
          lazymatch e with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
          tryif zl_has_var e then fail else idtac;
          let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 e)) in
          replace (Z_to_bv 64 e) with (Z_to_bv 64 v) by (symmetry; apply zlit_fold; vm_compute; reflexivity)
      end
  end.
Local Tactic Notation "zrun" integer(n) := do n (zstep; try brc; zlits).

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tm2p_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (B : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + 8)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' B [C8 (Z_to_bv 64 0)].

Lemma OPENSSL_tm_to_posix_epoch_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A B : Z) (junk8 : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (0 < A)%Z -> (A + 56 <= lo \/ bv_unsigned sp <= A)%Z -> (A + 56 <= 2^64)%Z -> (A mod 8 = 0)%Z -> ro_cells ctusegs m A (tm_cells epoch_tm) ->
  (bv_unsigned sp <= B)%Z -> (B + 8 <= 2^64)%Z -> (B + 8 <= A \/ A + 56 <= B)%Z -> (B mod 8 = 0)%Z -> rw_cells ctusegs m B [CB 8%nat junk8] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 B ->
  evt ctusegs (tm2p_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m B)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_TM_TO_POSIX) fc None m (seg_rom ctusegs)).
Proof.
  intros until junk8. intros ST MI GLO LO HA HA2 HA3 ALA TM HB HB2 HAB ALB OUT -> ->. unfold GLOBALS_TOP in GLO. unfold OPENSSL_TM_TO_POSIX in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + 8)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPA : A + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by lia.
  assert (SEPB : B + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= B) by lia.
  unfold tm_cells, epoch_tm in TM. cbn [t_sec t_min t_hour t_mday t_mon t_year Z.sub] in TM.
  carve_frame 16%nat ST. do 4 zstep.
  zstep. let C := fresh "C" in if_cases C; [exfalso; zify_cond C; rewrite ?land64, ?Z.mod_small in C by (clear - HA HA3; lia); clear - C HA; lia | clear C].
  zstep. zstep. let C := fresh "C" in if_cases C; [exfalso; zify_cond C; change 7 with (Z.ones 3) in C; rewrite Z.land_ones in C by lia; change (2^3) with 8 in C; exact (C ALA) | clear C].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. setreg 14%Z (Z_to_bv 64 70) ltac:(symmetry; apply sx32_small; lia).
  zrun 4.
  zstep. setreg 13%Z (Z_to_bv 64 1) ltac:(symmetry; apply sx32_small; lia).
  zrun 1.
  zstep. setreg 17%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 2.
  (* [comment removed for export] *)
  zrun 8.
  (* [comment removed for export] *)
  zstep. setreg 14%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 3.
  zstep. setreg 16%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 1.
  zstep. setreg 10%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 5.
  (* [comment removed for export] *)
  zstep. let C := fresh "C" in if_cases C; [exfalso; zify_cond C; rewrite ?land64, ?Z.mod_small in C by (clear - HB HB2 SPR; lia); clear - C HB LO LO0; lia | clear C].
  zstep. zstep. let C := fresh "C" in if_cases C; [exfalso; zify_cond C; change 7 with (Z.ones 3) in C; rewrite Z.land_ones in C by lia; change (2^3) with 8 in C; exact (C ALB) | clear C].
  zrun 40. zrun 32.
  zstep. zstep.
  (* [comment removed for export] *)
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold tm2p_post.
  do 14 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

End WithCeiling.
