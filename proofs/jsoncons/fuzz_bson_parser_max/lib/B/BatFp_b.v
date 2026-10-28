(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Fixpoint art_out (W : list (Z * Z)) (z : Z) : Prop :=
  match W with [] => True | p :: r => ~ (fst p <= z < fst p + snd p) /\ art_out r z end.
Fixpoint art_gap (W : list (Z * Z)) (a n : Z) : Prop :=
  match W with [] => True | p :: r => apart a n (fst p) (snd p) /\ art_gap r a n end.
Definition art_agree (W : list (Z * Z)) (M M' : word -> option byte) : Prop :=
  forall x : word, art_out W (U x) -> M' x = M x.

Lemma art_out_app : forall W1 W2 z, art_out (W1 ++ W2) z <-> art_out W1 z /\ art_out W2 z.
Proof. induction W1 as [|p r IH]; intros W2 z; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma art_gap_out : forall W a n z, art_gap W a n -> a <= z < a + n -> art_out W z.
Proof.
  induction W as [|p r IH]; intros a n z G Hz; cbn in *; [exact I|]. destruct G as [G1 G2]. split; [|eapply IH; eassumption].
  unfold apart in G1. lia.
Qed.

Lemma art_gap_sub : forall W a n a' n', art_gap W a n -> a <= a' -> a' + n' <= a + n -> art_gap W a' n'.
Proof.
  induction W as [|p r IH]; intros a n a' n' G H1 H2; cbn in *; [exact I|]. destruct G as [G1 G2]. split; [|eapply IH; eassumption].
  unfold apart in *. lia.
Qed.
Lemma art_gap_app : forall W1 W2 a n, art_gap (W1 ++ W2) a n <-> art_gap W1 a n /\ art_gap W2 a n.
Proof. induction W1 as [|p r IH]; intros W2 a n; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma art_agree_refl : forall W M, art_agree W M M.
Proof. intros W M x _. reflexivity. Qed.
Lemma art_agree_trans : forall W1 W2 M0 M1 M2, art_agree W1 M0 M1 -> art_agree W2 M1 M2 -> art_agree (W1 ++ W2) M0 M2.
Proof. intros W1 W2 M0 M1 M2 A1 A2 x Hx. apply art_out_app in Hx. destruct Hx as [H1 H2]. rewrite A2 by exact H2. apply A1. exact H1. Qed.
Lemma art_agree_sub : forall W W' M M', art_agree W M M' -> (forall z, 0 <= z < 2 ^ 64 -> art_out W' z -> art_out W z) -> art_agree W' M M'.
Proof. intros W W' M M' A S x Hx. apply A. apply S; [|exact Hx]. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R. lia. Qed.
(* [comment removed for export] *)
Lemma art_agree_pt : forall W M M' (x : word), art_agree W M M' -> art_out W (U x) -> M' x = M x.
Proof. intros W M M' x A H. apply A. exact H. Qed.

Lemma art_agree_Wn : forall n M a v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> art_agree [(a, Z.of_nat n)] M (Wn n M a v).
Proof. intros n M a v Ha Hn x Hx. cbn in Hx. destruct Hx as [Hx _]. apply Wn_outside; assumption. Qed.
Lemma art_agree_Wf : forall M a k b, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> art_agree [(a, Z.of_nat k)] M (Wf M a k b).
Proof. intros M a k b Ha Hk x Hx. cbn in Hx. destruct Hx as [Hx _]. apply Wf_outside; assumption. Qed.
Lemma art_agree_zfill : forall M r len, art_agree [(r, len)] M (art_zfill M r len).
Proof. intros M r len x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_zfill_out. exact Hx. Qed.
Lemma art_agree_unmap : forall M r len, art_agree [(r, len)] M (art_unmap M r len).
Proof. intros M r len x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_unmap_out. exact Hx. Qed.
Lemma art_agree_reveal : forall M lo hi, art_agree [(lo, hi - lo)] M (art_reveal M lo hi).
Proof. intros M lo hi x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_reveal_out. lia. Qed.

(* [comment removed for export] *)
Lemma art_cell_tr : forall W M M' a (n : nat) v,
  art_agree W M M' -> art_gap W a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> cellA M a n v -> cellA M' a n v.
Proof.
  intros W M M' a n v A G Ha Hn C. apply (art_cell_agree _ M M'); [|exact Ha|exact Hn|exact C].
  intros x Hx. apply A. eapply art_gap_out; eassumption.
Qed.
Lemma art_byte_tr : forall W (M M' : word -> option byte) (x : word) b, art_agree W M M' -> art_out W (U x) -> M x = Some b -> M' x = Some b.
Proof. intros W M M' x b A O H. rewrite (A x O). exact H. Qed.

(* [comment removed for export] *)
Lemma art_cell1_of_byte : forall (M : word -> option byte) a v, 0 <= v < 256 -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v) -> cellA M a 1 v.
Proof. intros M a v Hv H. unfold cell. cbn [rdn]. rewrite H. rewrite art_bytes1 by lia. reflexivity. Qed.
Lemma cell_Wf_in : forall M a k b i, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> 0 <= i < Z.of_nat k -> 0 <= b < 256 -> cellA (Wf M a k b) (a + i) 1 b.
Proof. intros M a k b i Ha Hk Hi Hb. apply art_cell1_of_byte; [exact Hb|]. apply Wf_inside; assumption. Qed.

(* [comment removed for export] *)
Lemma art_zb_mod64 : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma art_cell_norm : forall M a (n : nat) v, cellA M a n v -> cellA M a n (v mod 2 ^ 64).
Proof. intros M a n v C. unfold cell in *. rewrite art_zb_mod64. exact C. Qed.
Lemma art_cell_mod_add : forall M a (n : nat) x y, cellA M a n (x mod 2 ^ 64 + y) -> cellA M a n (x + y).
Proof.
  intros M a n x y C. unfold cell in *. replace (Z_to_bv 64 (x + y)) with (Z_to_bv 64 (x mod 2 ^ 64 + y)); [exact C|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma art_mod64_range : forall v, 0 <= v mod 2 ^ 64 < 2 ^ 64.
Proof. intros v. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zagree :=
  lazymatch goal with
  | |- art_agree _ ?M ?M => apply (art_agree_refl [])
  | |- art_agree _ ?M (Wn ?n ?M1 ?a ?v) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_Wn; [lia | cbn; lia] ]
  | |- art_agree _ ?M (Wf ?M1 ?a ?k ?b) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_Wf; [lia | rewrite ?Z2Nat.id by lia; lia] ]
  | |- art_agree _ ?M (art_zfill ?M1 ?r ?len) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_zfill ]
  | |- art_agree _ ?M (art_unmap ?M1 ?r ?len) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_unmap ]
  | |- art_agree _ ?M (art_reveal ?M1 ?lo ?hi) => eapply (art_agree_trans _ _ M M1 _); [ zagree | apply art_agree_reveal ]
  end.
Ltac zgrows :=
  lazymatch goal with
  | |- mem_grows ?M ?M => apply mem_grows_refl
  | |- mem_grows ?M (Wn _ ?M1 _ _) => apply (mem_grows_trans M M1 _); [ zgrows | apply Wn_grows ]
  | |- mem_grows ?M (Wf ?M1 _ _ _) => apply (mem_grows_trans M M1 _); [ zgrows | apply Wf_grows ]
  | |- mem_grows ?M (art_zfill ?M1 _ _) => apply (mem_grows_trans M M1 _); [ zgrows | apply art_zfill_grows ]
  | |- mem_grows ?M (art_reveal ?M1 _ _) => apply (mem_grows_trans M M1 _); [ zgrows | apply art_reveal_grows ]
  end.
(* [comment removed for export] *)
Ltac zsub := let z := fresh "z" in let Hz := fresh "Hz" in let H := fresh "H" in
  intros z Hz H; cbn [art_out app fst snd] in H |- *; repeat split; lia.
(* [comment removed for export] *)
Ltac zgap := cbn [art_gap fst snd app]; repeat split; first [ exact I | zapart | unfold apart; cbn; lia ].
(* [comment removed for export] *)
Ltac ztr :=
  lazymatch goal with
  | |- cell _ ?M ?a ?n ?v =>
      first [ match goal with H : cell _ M a n v |- _ => exact H end
            | match goal with H : cell _ M ?a' n v |- _ => replace a with a' by lia; exact H end
            | match goal with A : art_agree ?W ?M0 M |- _ => apply (art_cell_tr W M0 M a n v A); [ zgap | lia | cbn; lia | ztr ] end ]
  end.

(* [comment removed for export] *)
Lemma art_cell_tr1 : forall W M M' a (n : nat) v,
  art_agree W M M' -> (art_gap W a (Z.of_nat n) /\ 0 <= a /\ a + Z.of_nat n < 2 ^ 64) -> cellA M a n v -> cellA M' a n v.
Proof. intros W M M' a n v A (G & Ha & Hn) C. eapply art_cell_tr; eassumption. Qed.
Ltac zapart_t :=
  lazymatch goal with |- apart _ _ _ _ => idtac | _ => fail end;
  first [ assumption
        | apply apart_sym; assumption
        | unfold apart at 1; lia
        | match goal with H : apart _ _ _ _ |- _ => unfold apart at 1; unfold apart in H; destruct H; lia end ].
Ltac zarith_t := cbn [art_gap fst snd app]; repeat split; first [ exact I | zapart_t | lia | cbn; lia ].
Ltac zgap_c clr := clr; zarith_t.
Ltac zsub_c clr := let z := fresh "z" in let Hz := fresh "Hz" in let H := fresh "H" in
  intros z; clr; intros Hz H; cbn [art_out app fst snd] in H |- *; repeat split; lia.
Ltac ztr_c clr :=
  lazymatch goal with
  | |- cell _ ?M ?a ?n ?v =>
      first [ match goal with H : cell _ M a n v |- _ => exact H end
            | match goal with A : art_agree ?W ?M0 M |- _ => apply (art_cell_tr1 W M0 M a n v A); [ clr; zarith_t | ztr_c clr ] end ]
  end.
(* [comment removed for export] *)
Ltac inl := cbn [In]; repeat first [left; reflexivity | right].

(* [comment removed for export] *)
Lemma art_layout_fp : forall W M M', art_agree W M M' -> (forall z, 0x10000 <= z < 0x211b08 -> art_out W z) -> art_layout M -> art_layout M'.
Proof. intros W M M' A O L. apply (art_layout_agree3 M M'); [|exact L]. intros x Hx. apply A. apply O. exact Hx. Qed.

Lemma art_tsd_fp : forall W M M' tp key tsd ctx t, art_agree W M M' ->
  (forall z, 0x10000 <= z < 0x696000 -> art_out W z) -> (forall z, ctx + 152 <= z < ctx + 160 -> art_out W z) ->
  0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 ->
  art_tsd M tp key tsd ctx t -> art_tsd M' tp key tsd ctx t.
Proof.
  intros W M M' tp key tsd ctx t A OI OC Htp Htp' Htsd Htsd' T.
  destruct T as (C1 & C2 & C3 & C4 & C5 & R). unfold art_tsd.
  assert (TI : forall a (n : nat) v, 0x10000 <= a -> a + Z.of_nat n <= 0x696000 -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn C. apply (art_cell_agree _ M M'); [|lia|lia|exact C]. intros x Hx. apply A. apply OI. lia. }
  assert (Rk : 0 <= key < 128) by (destruct R as (_ & _ & R3 & _); exact R3).
  split; [apply TI; [lia|cbn; lia|exact C1]|]. split; [apply TI; [lia|cbn; lia|exact C2]|].
  split; [apply TI; [lia|cbn; lia|exact C3]|]. split; [apply TI; [lia|cbn; lia|exact C4]|].
  split; [|exact R].
  apply (art_cell_agree _ M M'); [|lia|cbn; lia|exact C5]. intros x Hx. apply A. apply OC. cbn in Hx. lia.
Qed.
