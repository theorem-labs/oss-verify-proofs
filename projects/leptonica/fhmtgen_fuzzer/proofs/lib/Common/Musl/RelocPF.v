(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec StepTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition pf_bounds_ok (img_lo rw_lo img_hi dT dS dF1 dF2 : Z) : bool :=
  (img_lo <=? 0x102e7 + dS) && (0x102f1 + dS <=? rw_lo)
  && (img_lo <=? 0x114a8 + dT) && (0x117c0 + dT <=? rw_lo) && (rw_lo <=? 2 ^ 31)
  && (0x117c0 + dT <=? 0x17f6c + dF1) && (0x18d9c + dF1 <=? rw_lo)
  && (0x117c0 + dT <=? 0x18d9c + dF2) && (0x18ed0 + dF2 <=? rw_lo)
  && (img_hi mod 8 =? 0) && (2 ^ 16 <=? img_lo) && (img_hi <=? 2 ^ 31).

Definition pf_bounds_chk {RL : Reloc} : bool := pf_bounds_ok rl_img_lo rl_rw_lo rl_img_hi dA_114a8 dS_102e7 dF_17f6c dF_18d9c.

(* [comment removed for export] *)
Definition pf_prefix_ok (segs : list Segment) (a : Z) : bool :=
  match rdn segs (fun _ => None) (Z_to_bv 64 a) 1 with
  | Some (b :: nil) => bv_unsigned b =? 45
  | _ => false
  end.

Class RelocPF (RL : Reloc) := {
  rl_segs_lo_val : segs_lo rl_segs = rl_img_lo;
  rl_segs_hi_val : segs_hi rl_segs = rl_img_hi;
  rl_pf_bounds : pf_bounds_chk = true;
  rl_pf_prefix : pf_prefix_ok rl_segs (0x102e7 + dS_102e7) = true
}.

Section PF.
  Context {RL : Reloc} {RP : RelocPF RL}.

  Lemma rl_rom_range : forall (x : word) b, seg_rom rl_segs x = Some b -> rl_img_lo <= bv_unsigned x < rl_img_hi.
  Proof.
    intros x b H. pose proof (seg_rom_range rl_segs x b H) as R.
    rewrite rl_segs_lo_val, rl_segs_hi_val in R. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_pf_facts :
    rl_img_lo <= 0x102e7 + dS_102e7 /\ 0x102f1 + dS_102e7 <= rl_rw_lo
    /\ rl_img_lo <= 0x114a8 + dA_114a8 /\ 0x117c0 + dA_114a8 <= rl_rw_lo /\ rl_rw_lo <= 2 ^ 31
    /\ 0x117c0 + dA_114a8 <= 0x17f6c + dF_17f6c /\ 0x18d9c + dF_17f6c <= rl_rw_lo
    /\ 0x117c0 + dA_114a8 <= 0x18d9c + dF_18d9c /\ 0x18ed0 + dF_18d9c <= rl_rw_lo.
  Proof.
    pose proof rl_pf_bounds as H. unfold pf_bounds_chk, pf_bounds_ok in H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
    repeat (apply andb_prop in H; destruct H as [H ?]).
    repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X end.
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_img_hi_mod8 : rl_img_hi mod 8 = 0.
  Proof.
    pose proof rl_pf_bounds as H. unfold pf_bounds_chk, pf_bounds_ok in H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply Z.eqb_eq in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_img_lo_ge : 2 ^ 16 <= rl_img_lo.
  Proof.
    pose proof rl_pf_bounds as H. unfold pf_bounds_chk, pf_bounds_ok in H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply Z.leb_le in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_img_hi_le : rl_img_hi <= 2 ^ 31.
  Proof.
    pose proof rl_pf_bounds as H. unfold pf_bounds_chk, pf_bounds_ok in H.
    apply andb_prop in H as [_ H]. apply Z.leb_le in H. exact H.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_pf_prefix0 : rdn rl_segs (fun _ => None) (rl dS_102e7 0x102e7) 1 = Some [Z_to_bv 8 45].
  Proof.
    pose proof rl_pf_prefix as H. unfold pf_prefix_ok in H. unfold rl.
    destruct (rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x102e7 + dS_102e7)) 1) as [[|b [|? ?]]|]; try discriminate H.
    apply Z.eqb_eq in H. do 2 f_equal. apply bv_eq. rewrite H. reflexivity.
  Qed.
End PF.
