(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface LibIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10DrvLibL_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PmLay (L : heap_layout) (credit : Z -> credit) (foot : list (Z * Z)) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x396ec;
  ll_gp := 0x10800;
  ll_empty := 0xd4dd0;
  ll_initc := [(0xd6738, 0xd6800); (0xf6a70, 0xf6a78); (0xf6a98, 0xf6aa0); (0xf6ac8, 0xf6af8); (0xf6a93, 0xf6a94); (0xf6b68, 0xf6b6c)];
  ll_init_img := [(0x10000, 0xc4d70); (0xd4dc1, 0xd4dc4); (0xd4dc5, 0xd6730); (0xf6808, 0xf6828);
                  (0xf6848, 0xf6850); (0xf6854, 0xf6858); (0xf6860, 0xf6868); (0xf6870, 0xf6968); (0xf6970, 0xf6a68);
                  (0xf6a93, 0xf6a94); (0xf6b68, 0xf6b6c)];
  ll_td_self := 0xd6738; ll_td_tid := 0xd6758; ll_td_locale := 0xd67d0; ll_locale := 0xf6ac8; ll_td_canary := 0xd67f0;
  ll_guard := 0xf6a70; ll_auxvp := 0xf6a98;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0xc4c58;
  ll_stack := 65536;
  ll_credit := credit;
  ll_foot := foot;
  ll_init_cells := [(0xf6850, 4%nat, 1); (0xf6858, 8%nat, 0xf6860); (0xf6868, 8%nat, 0xa710c); (0xf6968, 8%nat, 0x39674)]     |}.

Definition foot_in_envelope (foot : list (Z * Z)) : Prop :=
  forall iv, In iv foot -> (0xd4de0 <= fst iv /\ snd iv <= 0xd5f78) \/ (0xd6728 <= fst iv /\ snd iv <= 0xd6730) \/ (0xf6848 <= fst iv /\ snd iv <= 0xf6a68).

Lemma drv_lib_layout_PmLay : forall L credit foot,
  foot_in_envelope foot ->
  (forall n, 0 <= n -> 0 <= fst (credit n) /\ 0 <= snd (credit n)) ->
  drv_lib_layout (PmLay L credit foot) L.
Proof.
  intros L credit foot HF HC. constructor; try reflexivity; try (cbn; lia).
  - exact HF.
  - intros iv [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn; lia.
  - exact HC.
Qed.
