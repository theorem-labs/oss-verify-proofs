(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.

Module Foott1g.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.

Definition rg_wf (r : region) : Prop :=
  0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.

(* [comment removed for export] *)
Definition covers (r : region) (a : word) (n : nat) : Prop :=
  rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.

Definition rg_disj (r1 r2 : region) : Prop :=
  rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_rg (sp : word) (below above : Z) : region :=
  Rg (bv_unsigned sp - below) (bv_unsigned sp + above).

(* [comment removed for export] *)
Definition seg_rg (lo hi : Z) : region := Rg lo hi.

(* [comment removed for export] *)
Definition heap_rg (base : word) (cur : Z) : region :=
  Rg (bv_unsigned base) (bv_unsigned base + cur).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition layout_wf (rs : list region) : Prop :=
  Forall rg_wf rs /\
  forall i j, (i < j)%nat -> (j < length rs)%nat ->
              rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).
End Foott1g.


Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition no_higher_fit (maps : list (word * word)) (aZ nZ baseZ : Z)
    : Prop :=
  forall g : Z,
    (g mod page_size = 0)%Z ->
    (aZ + nZ <= g)%Z ->
    (g + nZ <= baseZ)%Z ->
    region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false.

(* [comment removed for export] *)
Definition fit_candidates (maps : list (word * word)) (aZ nZ : Z)
    : list Z :=
  (aZ + nZ)%Z
    :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                      + bv_unsigned (snd p))%Z)
           maps.

Definition higher_fit_b (maps : list (word * word)) (aZ nZ baseZ : Z)
    : bool :=
  existsb (fun g => (g mod page_size =? 0)%Z
                    && (aZ + nZ <=? g)%Z && (g + nZ <=? baseZ)%Z
                    && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ))
          (fit_candidates maps aZ nZ).

Lemma page_round_up_Z_aligned : forall z,
  (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition search_candidates (maps : list (word * word)) (loZ : Z)
    : list Z :=
  loZ :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                        + bv_unsigned (snd p))%Z)
             maps.

(* [comment removed for export] *)
Definition place_fits (maps : list (word * word)) (loZ hiZ nZ : Z) (g : Z)
    : bool :=
  (g mod page_size =? 0)%Z && (loZ <=? g)%Z && (g + nZ <=? hiZ)%Z
  && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ).

Definition place (maps : list (word * word)) (loZ hiZ nZ : Z)
    : option Z :=
  find (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition place_in_model (h : VmMaps) (nZ : Z) : option Z :=
  place (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Example place_accepts_a_negative_length :
  place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = Some 4096%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition witness_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 8192)].

(* [comment removed for export] *)
Definition demo_top : Z := alloc_top (mkVmMaps [] [] 0 0 0).

(* [comment removed for export] *)
Example place_skips_the_occupied_floor :
  place witness_ledger page_size demo_top 4096 = Some 12288%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Example place_complete_premises_are_satisfiable :
  (0 <= page_size)%Z /\ (0 < 4096)%Z
  /\ (page_size mod page_size = 0)%Z /\ (4096 mod page_size = 0)%Z
  /\ (demo_top < two_pow_64)%Z
  /\ (12288 mod page_size = 0)%Z /\ (page_size <= 12288)%Z
  /\ (12288 + 4096 <= demo_top)%Z
  /\ region_free witness_ledger (Z_to_bv 64 12288) (Z_to_bv 64 4096) = true.
Proof.
  unfold page_size, demo_top, two_pow_64. rewrite alloc_top_mkVmMaps.
  repeat split; try (vm_compute; reflexivity); try lia.
Qed.

(* [comment removed for export] *)
Definition full_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))].

Example place_finds_nothing_when_full :
  place full_ledger page_size demo_top 4096 = None.
Proof. vm_compute. reflexivity. Qed.
