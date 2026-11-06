(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface LibIface Pm6DrvLibL.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PmLay (L : heap_layout) (credit : Z -> credit) (foot : list (Z * Z)) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x39d90;                    (* [comment removed for export] *)
  ll_gp := 0x10800;
  ll_empty := 0xd7bb0;                    (* [comment removed for export] *)
  ll_initc := [(0xd9558, 0xd9620); (0xf9890, 0xf9898); (0xf98b8, 0xf98c0); (0xf98e8, 0xf9918); (0xf98b3, 0xf98b4); (0xf9988, 0xf998c)];   (* [comment removed for export] *)
  ll_init_img := [(0x10000, 0xc7b48); (0xd7ba1, 0xd7ba4); (0xd7ba5, 0xd9550); (0xf9628, 0xf9648);
                  (0xf9668, 0xf9670); (0xf9674, 0xf9678); (0xf9680, 0xf9688); (0xf9690, 0xf9788); (0xf9790, 0xf9888);
                  (0xf98b3, 0xf98b4); (0xf9988, 0xf998c)];   (* [comment removed for export] *)
  ll_td_self := 0xd9558; ll_td_tid := 0xd9578; ll_td_locale := 0xd95f0; ll_locale := 0xf98e8; ll_td_canary := 0xd9610;
  ll_guard := 0xf9890; ll_auxvp := 0xf98b8;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0xc7a38;                    (* [comment removed for export] *)
  ll_stack := 65536;
  ll_credit := credit;
  ll_foot := foot;
  ll_init_cells := [(0xf9670, 4%nat, 1); (0xf9678, 8%nat, 0xf9680); (0xf9688, 8%nat, 0xa9f74); (0xf9788, 8%nat, 0x39d18)]   (* [comment removed for export] *) |}.

(* [comment removed for export] *)
Definition foot_in_envelope (foot : list (Z * Z)) : Prop :=
  forall iv, In iv foot -> (0xd7bc0 <= fst iv /\ snd iv <= 0xd8d98) \/ (0xd9548 <= fst iv /\ snd iv <= 0xd9550) \/ (0xf9668 <= fst iv /\ snd iv <= 0xf9888).

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
