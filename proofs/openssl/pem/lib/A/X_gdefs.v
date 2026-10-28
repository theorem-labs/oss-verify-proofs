(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout D_agree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GT_LO : Z := 0x5aaa60.        (* [comment removed for export] *)
Definition GT_HI : Z := 0x669460.        (* [comment removed for export] *)
Definition GT_N : Z := 12200.            (* [comment removed for export] *)
Definition GT_Nn : nat := 12200.
Definition XSEGLO : Z := 0x10000.        (* [comment removed for export] *)
Definition XSEGTOP : Z := 0xbc6000.
(* [comment removed for export] *)
Notation SHW_LO := 0x7fffa000%Z (only parsing).     (* [comment removed for export] *)
Notation SHW_HI := 0x80170c00%Z (only parsing).     (* [comment removed for export] *)
Notation ODR_LO := 0xb9faa0%Z (only parsing).       (* [comment removed for export] *)
Notation ODR_HI := 0xba356d%Z (only parsing).
Definition ODR_NONE : Z := 0xffffffffffffffff.

Lemma GT_span : GT_LO + 64 * GT_N = GT_HI. Proof. reflexivity. Qed.
Lemma SHW_LO_eq : SHW_LO = shad XSEGLO. Proof. reflexivity. Qed.
Lemma SHW_HI_eq : SHW_HI = shad XSEGTOP. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gd_okb (beg srz odr : Z) : bool :=
  (XSEGLO <=? beg) && (beg mod 8 =? 0) && (8 <=? srz) && (srz mod 8 =? 0)
  && (beg + srz <=? XSEGTOP) && (srz / 8 <? 0x10000)
  && ((odr =? ODR_NONE) || ((ODR_LO <=? odr) && (odr <? ODR_HI))).

Lemma gd_okb_spec : forall beg srz odr, gd_okb beg srz odr = true ->
  XSEGLO <= beg /\ beg mod 8 = 0 /\ 8 <= srz /\ srz mod 8 = 0 /\ beg + srz <= XSEGTOP /\ srz / 8 < 0x10000
  /\ (SHW_LO <= SHB + beg / 8 /\ SHB + beg / 8 + srz / 8 <= SHW_HI)
  /\ (odr = ODR_NONE \/ ODR_LO <= odr < ODR_HI).
Proof.
  intros beg srz odr H. unfold gd_okb in H.
  repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                       | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
                       | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split.
  - unfold SHB, XSEGLO, XSEGTOP in *. Z.div_mod_to_equations. lia.
  - match goal with HO : _ || _ = true |- _ =>
      apply orb_true_iff in HO; destruct HO as [HO1|HO2];
      [ left; apply Z.eqb_eq; exact HO1
      | right; apply andb_prop in HO2; destruct HO2 as [HO3 HO4]; apply Z.leb_le in HO3; apply Z.ltb_lt in HO4; lia ] end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gd_at (m : mem) (A beg srz odr : Z) : Prop :=
  ro_cells asegs m A [C8 (Z_to_bv 64 beg)]
  /\ ro_cells asegs m (A + 16) [C8 (Z_to_bv 64 srz)]
  /\ ro_cells asegs m (A + 56) [C8 (Z_to_bv 64 odr)].

Definition gtab_at (m : mem) : Prop :=
  forall i, 0 <= i < GT_N ->
    exists beg srz odr, gd_at m (GT_LO + 64 * i) beg srz odr /\ gd_okb beg srz odr = true.

Lemma gd_at_agree : forall m m' A beg srz odr, gd_at m A beg srz odr ->
  agree_on (fun x => A <= x < A + 64) m m' -> gd_at m' A beg srz odr.
Proof.
  intros m m' A beg srz odr (H0 & H2 & H7) AG. split; [| split].
  - apply (ro_cells_agree asegs m m' _ _ H0). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia.
  - apply (ro_cells_agree asegs m m' _ _ H7). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia.
Qed.

Lemma gtab_at_agree : forall m m', gtab_at m -> agree_on (fun x => GT_LO <= x < GT_HI) m m' -> gtab_at m'.
Proof.
  intros m m' H AG i Hi. destruct (H i Hi) as (beg & srz & odr & HA & HOK). exists beg, srz, odr. split; [|exact HOK].
  apply (gd_at_agree m m' _ _ _ _ HA). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold GT_LO, GT_HI, GT_N in *. lia.
Qed.

(* [comment removed for export] *)
Lemma gtab_at_munch : forall W m m', gtab_at m -> munch W m m' -> (forall x, GT_LO <= x < GT_HI -> outside W x) -> gtab_at m'.
Proof. intros W m m' H MU HW. apply (gtab_at_agree m m' H). exact (agree_of_munch _ _ _ _ MU HW). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition img_u64 (A : Z) : option (Z * list byte) :=
  match image_bytes asegs A 8 with
  | Some bs => Some (bv_unsigned (le_bytes_to_word bs), bs)
  | None => None
  end.

Fixpoint bytes_eqb (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb (bv_unsigned x) (bv_unsigned y) && bytes_eqb a' b'
  | _, _ => false
  end.

Lemma bytes_eqb_eq : forall a b, bytes_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. apply bv_eq in H1. subst y. f_equal. exact (IH b H2).
Qed.

(* [comment removed for export] *)
Definition gd_img_okb (i : nat) : bool :=
  let A := GT_LO + 64 * Z.of_nat i in
  match img_u64 A, img_u64 (A + 16), img_u64 (A + 56) with
  | Some (beg, b0), Some (srz, b2), Some (odr, b7) =>
      gd_okb beg srz odr
      && bytes_eqb (le8 (Z_to_bv 64 beg)) b0 && bytes_eqb (le8 (Z_to_bv 64 srz)) b2 && bytes_eqb (le8 (Z_to_bv 64 odr)) b7
  | _, _, _ => false
  end.

(* [comment removed for export] *)
Lemma gtab_img_ok : forallb gd_img_okb (seq 0 GT_Nn) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma image_bytes_nth : forall n A bs, image_bytes asegs A n = Some bs ->
  forall k, (k < n)%nat -> seg_rom asegs (wa (A + Z.of_nat k)) = nth_error bs k.
Proof.
  induction n as [|n IH]; intros A bs H k Hk; [lia|]. cbn [image_bytes] in H.
  destruct (seg_rom asegs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (image_bytes asegs (A + 1) n) as [bs'|] eqn:E'; [|discriminate]. injection H as <-.
  destruct k as [|k].
  - cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E' k ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma img_cell : forall (m : mem) A v bs, 0 <= A -> A + 8 <= 2^64 ->
  img_u64 A = Some (v, bs) -> bytes_eqb (le8 (Z_to_bv 64 v)) bs = true ->
  (forall x, A <= x < A + 8 -> mrd asegs m (wa x) = seg_rom asegs (wa x)) ->
  ro_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v bs HA0 HA1 HI HB HM. unfold img_u64 in HI.
  destruct (image_bytes asegs A 8) as [bs0|] eqn:E; [|discriminate]. injection HI as <- <-.
  apply bytes_eqb_eq in HB.
  pose proof (image_bytes_length asegs 8 A bs0 E) as HL.
  split.
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. change (le8 (Z_to_bv 64 (bv_unsigned (le_bytes_to_word bs0)))) with (le8 (Z_to_bv 64 (bv_unsigned (le_bytes_to_word bs0)))).
    rewrite HB. split; [exact HA0|]. split; [rewrite HL; cbn; lia|].
    intros k Hk. rewrite HL in Hk. rewrite (HM (A + Z.of_nat k) ltac:(lia)).
    exact (image_bytes_nth 8 A bs0 E k Hk).
Qed.

Theorem gtab_at_of_image : forall m : mem,
  (forall x, GT_LO <= x < GT_HI -> mrd asegs m (wa x) = seg_rom asegs (wa x)) -> gtab_at m.
Proof.
  intros m HM i Hi.
  pose proof gtab_img_ok as HT. rewrite forallb_forall in HT.
  specialize (HT (Z.to_nat i)).
  assert (HN : Z.of_nat GT_Nn = GT_N) by (vm_compute; reflexivity).
  assert (Hin : In (Z.to_nat i) (seq 0 GT_Nn)).
  { apply in_seq. split; [lia|]. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. rewrite Nat.add_0_l, HN. lia. }
  specialize (HT Hin). unfold gd_img_okb in HT. rewrite Z2Nat.id in HT by lia. unfold GT_N in Hi.
  destruct (img_u64 (GT_LO + 64 * i)) as [[beg b0]|] eqn:E0; [|discriminate].
  destruct (img_u64 (GT_LO + 64 * i + 16)) as [[srz b2]|] eqn:E2; [|discriminate].
  destruct (img_u64 (GT_LO + 64 * i + 56)) as [[odr b7]|] eqn:E7; [|discriminate].
  apply andb_prop in HT. destruct HT as [HT H7]. apply andb_prop in HT. destruct HT as [HT H2].
  apply andb_prop in HT. destruct HT as [HOK H0].
  exists beg, srz, odr. split; [|exact HOK].
  assert (B : 0 <= GT_LO + 64 * i /\ GT_LO + 64 * i + 64 <= GT_HI /\ GT_HI <= 2 ^ 64) by (unfold GT_LO, GT_HI; lia).
  split; [| split].
  - apply (img_cell m (GT_LO + 64 * i) beg b0); [lia| lia| exact E0| exact H0|]. intros x Hx. apply HM. lia.
  - apply (img_cell m (GT_LO + 64 * i + 16) srz b2); [lia| lia| exact E2| exact H2|]. intros x Hx. apply HM. lia.
  - apply (img_cell m (GT_LO + 64 * i + 56) odr b7); [lia| lia| exact E7| exact H7|]. intros x Hx. apply HM. lia.
Qed.

(* [comment removed for export] *)
Corollary gtab_at_of_overlay_none : forall m : mem,
  (forall x, GT_LO <= x < GT_HI -> m (wa x) = None) -> gtab_at m.
Proof. intros m H. apply gtab_at_of_image. intros x Hx. unfold mrd. rewrite (H x Hx). reflexivity. Qed.
