(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Export BWorld.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Class Ceiling := {
  clg_bw :: BWorld;
  alloc_ceiling : Z;
  alloc_ceiling_lo : 0x7fff7f800000 <= alloc_ceiling;
  alloc_ceiling_hi : alloc_ceiling <= 0x7fffff800000;
  alloc_ceiling_al : alloc_ceiling mod 16 = 0
}.

(* [comment removed for export] *)
Lemma sp_window_lo_val : sp_window_lo = 0x7fff80000000.
Proof. reflexivity. Qed.
Lemma sp_window_hi_val : sp_window_hi = 0x800000000000.
Proof. reflexivity. Qed.
Lemma stack_max_size_val' : stack_max_size = 0x800000.
Proof. reflexivity. Qed.

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Lemma alloc_ceiling_val : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. split; [apply alloc_ceiling_lo | apply alloc_ceiling_hi]. Qed.

(* [comment removed for export] *)

Lemma alloc_ceiling_mod16 : alloc_ceiling mod 16 = 0.
Proof. apply alloc_ceiling_al. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ceil_ok (md : Model) : Prop := alloc_top (m_vmmaps md) = alloc_ceiling.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ceil_ok_same_vmmaps : forall md md', m_vmmaps md' = m_vmmaps md -> ceil_ok md -> ceil_ok md'.
Proof. intros md md' E H. unfold ceil_ok in *. rewrite E. exact H. Qed.

(* [comment removed for export] *)

Lemma alloc_top_mkVmMapsFull : forall r m na sb b l mb isp,
  alloc_top (mkVmMapsFull r m na sb b l mb isp) = bv_unsigned isp - stack_max_size.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL.

(* [comment removed for export] *)

Lemma ceiling_of_sp_lo : forall sp, valid_sp sp -> 0x7fff7f800000 <= bv_unsigned sp - stack_max_size.
Proof. intros sp (Hlo & Hhi & Hal). rewrite sp_window_lo_val in Hlo. rewrite stack_max_size_val'. lia. Qed.
Lemma ceiling_of_sp_hi : forall sp, valid_sp sp -> bv_unsigned sp - stack_max_size <= 0x7fffff800000.
Proof. intros sp (Hlo & Hhi & Hal). rewrite sp_window_hi_val in Hhi. rewrite stack_max_size_val'. lia. Qed.
Lemma ceiling_of_sp_al : forall sp, valid_sp sp -> (bv_unsigned sp - stack_max_size) mod 16 = 0.
Proof. intros sp (Hlo & Hhi & Hal). rewrite stack_max_size_val'. rewrite <- Zminus_mod_idemp_l, Hal. reflexivity. Qed.

Definition ceiling_of_sp {BW : BWorld} (sp : word) (V : valid_sp sp) : Ceiling :=
  {| clg_bw := BW;
     alloc_ceiling := bv_unsigned sp - stack_max_size;
     alloc_ceiling_lo := ceiling_of_sp_lo sp V;
     alloc_ceiling_hi := ceiling_of_sp_hi sp V;
     alloc_ceiling_al := ceiling_of_sp_al sp V |}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
