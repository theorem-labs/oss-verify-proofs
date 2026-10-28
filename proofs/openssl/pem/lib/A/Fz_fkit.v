(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface Fz_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma land_m32_pad : forall x pad, 0 <= x < 2^64 -> x mod 32 = pad -> Z.land x 18446744073709551584 = x - pad.
Proof.
  intros x pad Hx <-. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5) with 32. pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

Lemma shr3_div : forall x, 0 <= x -> x ≫ 3 = x / 8.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma div8_facts : forall x, 8 * (x / 8) <= x < 8 * (x / 8) + 8.
Proof. intros x. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). change (bv_modulus 8) with (2^8).
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.

Ltac lfix :=
  first [ lazymatch goal with
          | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
          end
        | fix_lit_store ].

Lemma rw_cells_blur : forall (m : mem) A cs1 cs2, rw_cells asegs m A (cs1 ++ cs2) ->
  rw_cells asegs m A (CB (cells_size cs1) (cells_bytes cs1) :: cs2).
Proof.
  intros m A cs1 cs2 [[WF BY] WR]. apply cells_wf_app in WF as [WF1 WF2].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply cells_bytes_length; exact WF1| exact WF2].
  - cbn [cells_bytes cbytes]. rewrite cells_bytes_app in BY. exact BY.
  - cbn [cells_size csize]. rewrite cells_size_app in WR. exact WR.
Qed.
