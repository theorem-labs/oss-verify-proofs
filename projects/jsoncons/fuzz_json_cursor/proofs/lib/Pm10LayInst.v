(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface LibIface Pm10DrvLibL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PmLay (L : heap_layout) (credit : Z -> credit) (foot : list (Z * Z)) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x393fc;
  ll_gp := 0x10800;
  ll_empty := 0xd2f80;
  ll_initc := [(0xd48e8, 0xd49b0); (0xf4c20, 0xf4c28); (0xf4c48, 0xf4c50); (0xf4c78, 0xf4ca8); (0xf4c43, 0xf4c44); (0xf4d18, 0xf4d1c)];
  ll_init_img := [(0x10000, 0xc2f20); (0xd2f71, 0xd2f74); (0xd2f75, 0xd48e0); (0xf49b8, 0xf49d8);
                  (0xf49f8, 0xf4a00); (0xf4a04, 0xf4a08); (0xf4a10, 0xf4a18); (0xf4a20, 0xf4b18); (0xf4b20, 0xf4c18);
                  (0xf4c43, 0xf4c44); (0xf4d18, 0xf4d1c)];
  ll_td_self := 0xd48e8; ll_td_tid := 0xd4908; ll_td_locale := 0xd4980; ll_locale := 0xf4c78; ll_td_canary := 0xd49a0;
  ll_guard := 0xf4c20; ll_auxvp := 0xf4c48;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0xc2e08;
  ll_stack := 65536;
  ll_credit := credit;
  ll_foot := foot;
  ll_init_cells := [(0xf4a00, 4%nat, 1); (0xf4a08, 8%nat, 0xf4a10); (0xf4a18, 8%nat, 0xa5358); (0xf4b18, 8%nat, 0x39384)]     |}.

Definition foot_in_envelope (foot : list (Z * Z)) : Prop :=
  forall iv, In iv foot -> (0xd2f90 <= fst iv /\ snd iv <= 0xd4128) \/ (0xd48d8 <= fst iv /\ snd iv <= 0xd48e0) \/ (0xf49f8 <= fst iv /\ snd iv <= 0xf4c18).

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
