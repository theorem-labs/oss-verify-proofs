(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec StoreOk Frame ShapeAlg Spec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Export U1Exit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1SpecConsts S1Spec U1ExitKn.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Lemma cell_agree : forall M M' a n v,
  a + Z.of_nat n < 2 ^ 64 -> 0 <= a ->
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  cell M a n v -> cell M' a n v.
Proof.
  intros M M' a n v Hnw Ha Hag Hc. unfold cell in *. rewrite <- Hc.
  apply rdn_ext; [rewrite u64_lit by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia.
  replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range x); lia); reflexivity).
  apply Hag. lia.
Qed.

Lemma rdn_agree : forall M M' (a : Z) (n : nat) bs,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M' (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M M' a n bs Ha Hn Hag H. rewrite <- H. apply rdn_ext; [rewrite u64_lit by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia.
  replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range x); lia); reflexivity).
  apply Hag. lia.
Qed.

Lemma img_clear_agree : forall M M' lo hi,
  (forall i, lo <= i < hi -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> img_clear M lo hi -> img_clear M' lo hi.
Proof. intros M M' lo hi Hag H i Hi. rewrite Hag by lia. apply H. lia. Qed.

Record main_frame (sp0 : Z) (M : word -> option byte) : Prop := {
  mf_ra : cell M (sp0 - 56) 8 0xd1808;
  mf_s0 : cell M (sp0 - 64) 8 (sp0 + 8);
  mf_s1 : cell M (sp0 - 72) 8 2;
  mf_s2 : cell M (sp0 - 80) 8 0x6583c;
  mf_s3 : cell M (sp0 - 88) 8 (sp0 + 32);
  mf_s4 : cell M (sp0 - 96) 8 0;
  mf_s5 : cell M (sp0 - 104) 8 0;
  mf_s6 : cell M (sp0 - 112) 8 0;
  mf_s7 : cell M (sp0 - 120) 8 0
}.

Theorem main_frame_frame : forall sp0 M M',
  120 <= sp0 -> sp0 + 40 < 2 ^ 64 ->
  (forall i, sp0 - 120 <= i < sp0 - 48 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  main_frame sp0 M -> main_frame sp0 M'.
Proof.
  intros sp0 M M' Hlo Hhi Hag [H1 H2 H3 H4 H5 H6 H7 H8 H9].
  constructor; (eapply cell_agree; [ | | | eassumption]; [cbn; lia | lia | intros; apply Hag; cbn in *; lia]).
Qed.

Definition stack_writableZ (M : word -> option byte) (sp0 : Z) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= 8388608 ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 8388608 + d)) m = true.

Lemma stack_writableZ_grows : forall M M' sp0, mem_grows M M' -> stack_writableZ M sp0 -> stack_writableZ M' sp0.
Proof. intros M M' sp0 Hg H d m Hd Hm. eapply store_ok_mono; [exact Hg | apply H; assumption]. Qed.

Definition mng_static (a : Z) : Prop :=
     (0x122820 <= a < 0x122bc8)
  \/ (0x1226d8 <= a < 0x1226e0)
  \/ (a = 0x1226ab)
  \/ (0x122688 <= a < 0x122690)
  \/ (0x12340c <= a < 0x123414).

Definition hdr_b0 (content : list byte) : Z := bv_unsigned (nth 0 content (Z_to_bv 8 0)).
Definition hdr_b1 (content : list byte) : Z := bv_unsigned (nth 1 content (Z_to_bv 8 0)).
Definition hdr_cfg (content : list byte) : Z := hdr_b0 content + 256 * hdr_b1 content.
Definition hdr_cfglen (content : list byte) : Z := hdr_cfg content mod 32768.
Definition hdr_paylen (content : list byte) : Z := Z.of_nat (length content) - 6 - hdr_cfglen content.

Definition t_target (content : list byte) (fs : Fs.Fs) : TSet :=
  let b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0)) in
  let cfg := hdr_cfg content in
  let config_len := Z.to_nat (cfg mod 32768) in
  let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
  t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs).

Lemma t_body_target : forall content fs,
  (Z.of_nat (length content) < MAX_INPUT) ->
  (6 + Z.to_nat (hdr_cfg content mod 32768) <= length content)%nat ->
  t_body content fs = t_target content fs.
Proof.
  intros content fs Hmax Hlen. unfold t_body, t_target, hdr_cfg, hdr_b0, hdr_b1 in *.
  destruct (MAX_INPUT <=? Z.of_nat (length content)) eqn:E1; [apply Z.leb_le in E1; lia|].
  destruct (length content <? 6)%nat eqn:E2; [apply Nat.ltb_lt in E2; lia|].
  destruct (length content <? 6 + Z.to_nat ((bv_unsigned (nth 0 content (Z_to_bv 8 0)) +
             256 * bv_unsigned (nth 1 content (Z_to_bv 8 0))) mod 32768))%nat eqn:E3;
    [apply Nat.ltb_lt in E3; lia|].
  reflexivity.
Qed.

Definition drv_cells : list (Z * nat * Z) := (exit_cxx_cells ++ [(0x1023e8, 8%nat, 0x1226e0)])%Z.
Definition drv_cells_ok (M : word -> option byte) : Prop :=
  Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
    rdn RSEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)) end) drv_cells.

Lemma drv_cells_range : Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
    0xf0200 <= a /\ a + Z.of_nat w <= 0x1226e0 end) drv_cells.
Proof.
  assert (HA : forallb (fun c : Z * nat * Z => let '(a, w, v) := c in ((0xf0200 <=? a) && (a + Z.of_nat w <=? 0x1226e0))%bool) drv_cells = true)
    by (vm_compute; reflexivity).
  apply Forall_forall. intros [[a w] v] Hin. pose proof (proj1 (forallb_forall _ _) HA _ Hin) as HB.
  cbv beta iota in HB |- *. apply andb_prop in HB as [H0 H1]. apply Z.leb_le in H0, H1. lia.
Qed.

Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.
