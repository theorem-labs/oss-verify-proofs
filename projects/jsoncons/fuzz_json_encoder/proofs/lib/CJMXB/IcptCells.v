(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm5RegionPoisoned Pm5AsanMemcpy Pm5AsanMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMXB Require Import ShZero.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint high_all (W : list ivl) : Prop :=
  match W with
  | [] => True
  | (a, b) :: W' => (b <= a \/ (0x10007fff8000 <= a /\ b <= 0x7fffffffff00)) /\ high_all W'
  end.

Lemma high_in_app_all : forall W, high_all W -> in_app_all W.
Proof.
  induction W as [|[a b] W IH]; cbn; [tauto|]. intros [[H|[H1 H2]] HW]; split; [left; exact H| |right; right; unfold app; lia|]; apply IH, HW.
Qed.

Lemma outside_high : forall W y, high_all W -> 0 <= y < 0x10007fff8000 -> outside W y.
Proof.
  induction W as [|[a b] W IH]; intros y HW Hy; cbn [outside high_all] in *; [exact I|].
  destruct HW as [[Hba|[A1 A2]] HW']; (split; [lia|]); apply IH; assumption.
Qed.

Section T.
Variable segs : list Segment.

Lemma rdn_munch_low : forall m m' W (a : word) k bs, high_all W -> munch W m m' ->
  (bv_unsigned a + Z.of_nat k <= 0x10007fff8000)%Z ->
  rdn segs m a k = Some bs -> rdn segs m' a k = Some bs.
Proof.
  intros m m' W a k bs HW MU Ha H. rewrite <- H. apply rdn_ext; [lia|].
  intros x Hx. apply MU. apply outside_high; [exact HW|]. pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in *. lia.
Qed.
End T.

Lemma rt_layout_globs_munch : forall m m' W, high_all W -> munch W m m' -> Pm5RegionPoisoned.rt_layout_globs m -> Pm5RegionPoisoned.rt_layout_globs m'.
Proof.
  intros m m' W HW MU (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). unfold Pm5RegionPoisoned.rt_layout_globs.
  repeat split; (eapply rdn_munch_low; [exact HW | exact MU | | eassumption ]); vm_compute; congruence.
Qed.

Lemma mc_icpt_globs_munch : forall m m' W, high_all W -> munch W m m' -> Pm5AsanMemcpy.mc_icpt_globs m -> Pm5AsanMemcpy.mc_icpt_globs m'.
Proof.
  intros m m' W HW MU (H1 & H2 & H3). unfold Pm5AsanMemcpy.mc_icpt_globs.
  repeat split; (eapply rdn_munch_low; [exact HW | exact MU | | eassumption ]); vm_compute; congruence.
Qed.

Lemma ms_icpt_globs_munch : forall m m' W, high_all W -> munch W m m' -> Pm5AsanMemset.ms_icpt_globs m -> Pm5AsanMemset.ms_icpt_globs m'.
Proof.
  intros m m' W HW MU (H1 & H2 & H3). unfold Pm5AsanMemset.ms_icpt_globs.
  repeat split; (eapply rdn_munch_low; [exact HW | exact MU | | eassumption ]); vm_compute; congruence.
Qed.

Definition ai_byte (m : word -> option byte) : Prop := rdn AsanUbsan.M.loaded_segments m (0x16e498 : word) 1%nat = Some [Z_to_bv 8 1].
Definition fx_got (m : word -> option byte) : Prop :=
  rdn AsanUbsan.M.loaded_segments m (0x166390 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14901c)).

Lemma ai_byte_munch : forall m m' W, high_all W -> munch W m m' -> ai_byte m -> ai_byte m'.
Proof. intros m m' W HW MU H. unfold ai_byte in *. eapply rdn_munch_low; [exact HW | exact MU | | exact H]. vm_compute; congruence. Qed.
Lemma fx_got_munch : forall m m' W, high_all W -> munch W m m' -> fx_got m -> fx_got m'.
Proof. intros m m' W HW MU H. unfold fx_got in *. eapply rdn_munch_low; [exact HW | exact MU | | exact H]. vm_compute; congruence. Qed.

Definition aenv (m : word -> option byte) : Prop :=
  Pm5RegionPoisoned.rt_layout_globs m /\ Pm5AsanMemcpy.mc_icpt_globs m /\ Pm5AsanMemset.ms_icpt_globs m /\ ai_byte m /\ fx_got m.

Lemma aenv_rt : forall m, aenv m -> Pm5RegionPoisoned.rt_layout_globs m.  Proof. intros m H; apply H. Qed.
Lemma aenv_mc : forall m, aenv m -> Pm5AsanMemcpy.mc_icpt_globs m.  Proof. intros m H; apply H. Qed.
Lemma aenv_ms : forall m, aenv m -> Pm5AsanMemset.ms_icpt_globs m.  Proof. intros m H; apply H. Qed.
Lemma aenv_ai : forall m, aenv m -> ai_byte m.  Proof. intros m H; apply H. Qed.
Lemma aenv_fx : forall m, aenv m -> fx_got m.  Proof. intros m H; apply H. Qed.

Lemma aenv_munch : forall m m' W, high_all W -> munch W m m' -> aenv m -> aenv m'.
Proof.
  intros m m' W HW MU (H1 & H2 & H3 & H4 & H5). split; [|split; [|split; [|split]]].
  - exact (rt_layout_globs_munch m m' W HW MU H1).
  - exact (mc_icpt_globs_munch m m' W HW MU H2).
  - exact (ms_icpt_globs_munch m m' W HW MU H3).
  - exact (ai_byte_munch m m' W HW MU H4).
  - exact (fx_got_munch m m' W HW MU H5).
Qed.
