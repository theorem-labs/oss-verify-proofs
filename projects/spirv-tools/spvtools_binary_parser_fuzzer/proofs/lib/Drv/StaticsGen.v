(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk MemSplit LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u_small64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia. Qed.

Section Gen.
  Variable SEGS : list Segment.
  Variable L : Layout.
  Variable DC : list run.

  Hypothesis DC_rw : forall a, in_runs DC a -> in_ranges (ly_rw L) a.

  Hypothesis H_rw : forall a, zwin (ly_new_handler L) (ly_new_handler L + 8) a -> in_ranges (ly_rw L) a.
  Hypothesis H_range : 0 <= ly_new_handler L /\ ly_new_handler L + 8 <= 2 ^ 64.
  Hypothesis relro_range : forall a, in_ranges (ly_relro L) a -> 0 <= a < 2 ^ 64.

  Definition st_region (a : Z) : Prop :=
    in_runs DC a \/ zwin (ly_new_handler L) (ly_new_handler L + 8) a.

  Definition handler_bytes : list byte := word_to_le_bytes 8 (Z_to_bv 64 (ly_oom_spin L)).

  Definition st_inv (s : bool) (M : mem) : Prop :=
    pins DC M
    /\ (forall a, in_ranges (ly_relro L) a -> M (Z_to_bv 64 a) = None)
    /\ rdn SEGS M (Z_to_bv 64 (ly_new_handler L)) 8 = Some handler_bytes.

  Lemma st_frame : forall s M M', st_inv s M ->
    same_on (fun a => st_region a \/ in_ranges (ly_relro L) a) M M' -> st_inv s M'.
  Proof.
    intros s M M' (HP & HR & HH) HS. split; [|split].
    - eapply pins_same; [exact HP|]. intros a Ha. apply HS. left. left. exact Ha.
    - intros a Ha. pose proof (relro_range a Ha). rewrite <- (HR a Ha). apply HS. rewrite u_small64 by lia. right. exact Ha.
    - rewrite <- HH. apply rdn_ext; [rewrite u_small64 by lia; lia|].
      intros x Hx. rewrite u_small64 in Hx by lia. apply HS. left. right. exact Hx.
  Qed.

  Definition drv_statics : StaticsIface SEGS L.
  Proof.
    refine (@STATICS_IFACE SEGS L bool (fun s s' => s = true -> s' = true) st_inv st_region
              _ _ _ st_frame _ (fun _ => True) _ _).
    -   intros s H; exact H.
    -   intros a b c H1 H2 H; exact (H2 (H1 H)).
    -   intros a [Ha|Ha]; [apply DC_rw; exact Ha | apply H_rw; exact Ha].
    -   intros s M a (_ & HR & _) Ha. apply HR. exact Ha.
    -   intros s s' _ _. exact I.
    -   intros s M (_ & _ & HH) _. exact HH.
  Defined.

End Gen.

