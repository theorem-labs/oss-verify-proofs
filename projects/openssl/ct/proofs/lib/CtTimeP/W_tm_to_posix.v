(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit F_memset.
From OSSVerify.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtPrnP Require Import MagicDiv.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeMagic W_posix_to_tm W_gmtime.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
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
             F (ret_pc ra) fc None m' (seg_rom ctpsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + 8)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m'
    /\ stk ctpsegs m' lo (bv_unsigned sp)
    /\ rw_cells ctpsegs m' B [C8 (Z_to_bv 64 0)].

Lemma OPENSSL_tm_to_posix_epoch_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A B : Z) (junk8 : list byte),
  stk ctpsegs m lo (bv_unsigned sp) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  (0 < A)%Z -> (A + 56 <= lo \/ bv_unsigned sp <= A)%Z -> (A + 56 <= 2^64)%Z -> ro_cells ctpsegs m A (tm_cells epoch_tm) ->
  (bv_unsigned sp <= B)%Z -> (B + 8 <= 2^64)%Z -> (B + 8 <= A \/ A + 56 <= B)%Z -> rw_cells ctpsegs m B [CB 8%nat junk8] ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 B ->
  evt ctpsegs (tm2p_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m B)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_TM_TO_POSIX) fc None m (seg_rom ctpsegs)).
Proof.
  intros until junk8. intros ST MI GLO LO HA HA2 HA3 TM HB HB2 HAB OUT -> ->. unfold GLOBALS_TOP in GLO. unfold OPENSSL_TM_TO_POSIX in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + 8)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPA : A + 56 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= A) by lia.
  assert (SEPB : B + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= B) by lia.
  unfold tm_cells, epoch_tm in TM. cbn [t_sec t_min t_hour t_mday t_mon t_year Z.sub] in TM.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. setreg 14%Z (Z_to_bv 64 70) ltac:(symmetry; apply sx32_small; lia).
  zrun 5.
  zstep. setreg 13%Z (Z_to_bv 64 1) ltac:(symmetry; apply sx32_small; lia).
  zrun 1.
  zstep. setreg 17%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 2.
  (* [comment removed for export] *)
  zrun 12.
  (* [comment removed for export] *)
  zstep. setreg 14%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 3.
  zstep. setreg 16%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 1.
  zstep. setreg 10%Z (Z_to_bv 64 0) ltac:(symmetry; apply sx32_small; lia).
  zrun 5.
  (* [comment removed for export] *)
  zrun 40. zrun 31.
  zstep. zstep.
  (* [comment removed for export] *)
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. unfold tm2p_post.
  do 14 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

End WithCeiling.
