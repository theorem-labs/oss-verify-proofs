(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Definition no_higher_fit (maps : list (word * word)) (aZ nZ baseZ : Z)
: Prop :=
forall g : Z,
(g mod page_size = 0)%Z ->
(aZ + nZ <= g)%Z ->
(g + nZ <= baseZ)%Z ->
region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false.
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








Definition search_candidates (maps : list (word * word)) (loZ : Z)
: list Z :=
loZ :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
+ bv_unsigned (snd p))%Z)
maps.
Definition place_fits (maps : list (word * word)) (loZ hiZ nZ : Z) (g : Z)
: bool :=
(g mod page_size =? 0)%Z && (loZ <=? g)%Z && (g + nZ <=? hiZ)%Z
&& region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ).
Definition place (maps : list (word * word)) (loZ hiZ nZ : Z)
: option Z :=
find (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).




Definition place_in_model (h : VmMaps) (nZ : Z) : option Z :=
place (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ.

Example place_accepts_a_negative_length :
place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = Some 4096%Z.
Proof. vm_compute. reflexivity. Qed.

Definition witness_ledger : list (word * word) :=
[(Z_to_bv 64 4096, Z_to_bv 64 8192)].
Definition demo_top : Z := alloc_top (mkVmMaps [] [] 0 0 0).
Example place_skips_the_occupied_floor :
place witness_ledger page_size demo_top 4096 = Some 12288%Z.
Proof. vm_compute. reflexivity. Qed.
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
Definition full_ledger : list (word * word) :=
[(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))].
Example place_finds_nothing_when_full :
place full_ledger page_size demo_top 4096 = None.
Proof. vm_compute. reflexivity. Qed.
