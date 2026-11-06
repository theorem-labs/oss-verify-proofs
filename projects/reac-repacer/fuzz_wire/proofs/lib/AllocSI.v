From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO0j YO0m.
Import ListNotations.
Local Open Scope Z_scope.

Definition frameless (am : ameta) : Prop :=
  forall i, 0 <= i <= am_last am -> ss_fr (nth_slot am i) = None.

Definition unreserved (R : option (sptr * Z)) (g : sptr) : Prop := forall i, R <> Some (g, i).

Definition owned_maps (X : list sptr) (s : astate) : Prop :=
  forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
  exists g am, usedX X s g am /\ 0 < am_maplen am /\ prid (am_mem am) = k.

Definition empty_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) : Prop :=
  forall g am, usedX X s g am -> frameless am -> unreserved R g ->
  0 < am_maplen am /\ 0 <= am_sc am < 48.

Definition empty_unique (X : list sptr) (R : option (sptr * Z)) (s : astate) : Prop :=
  forall g1 a1 g2 a2, usedX X s g1 a1 -> usedX X s g2 a2 -> frameless a1 -> frameless a2 ->
  unreserved R g1 -> unreserved R g2 -> am_sc a1 = am_sc a2 -> g1 = g2.

Definition children_ok (X : list sptr) (s : astate) : Prop :=
  forall g am i fr, usedX X s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  fr_kind fr = FGroup ->
  exists c ac, usedX X s c ac /\ am_maplen ac = 0 /\ am_mem ac = slot_start am i /\ am_sc ac < am_sc am.

Definition hand_keys (s : astate) : Prop := hand s = Z.of_nat (length (st_metas s)).

Definition SIX (X : list sptr) (R : option (sptr * Z)) (s : astate) : Prop :=
  owned_maps X s /\ empty_ok X R s /\ empty_unique X R s /\ children_ok X s /\ hand_keys s.

Definition SI (s : astate) : Prop := SIX [] None s.

Definition nblocks (s : astate) : Z := Z.of_nat (length (user_blocks s)).

Definition nused (s : astate) : Z := Z.of_nat (length (used_metas s)).

Lemma SI_init : SI init_state.
Proof.
  assert (NU : forall X g am, ~ usedX X init_state g am).
  { intros X g am H. unfold usedX, MTX, MT in H. destruct (memb g X); cbn in H; discriminate. }
  unfold SI, SIX. split; [|split; [|split; [|split]]].
  - intros k rg Hk. unfold region_of in Hk. cbn in Hk. destruct k; discriminate.
  - intros g am H. exfalso. exact (NU _ _ _ H).
  - intros g1 a1 g2 a2 H. exfalso. exact (NU _ _ _ H).
  - intros g am i fr H. exfalso. exact (NU _ _ _ H).
  - unfold hand_keys, hand, nareas. cbn. reflexivity.
Qed.
