(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface LibIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6DrvLibL_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PmLay (L : heap_layout) (credit : Z -> credit) (foot : list (Z * Z)) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x3a610;                    (* [comment removed for export] *)
  ll_gp := 0x10800;
  ll_empty := 0xdb5a0;                    (* [comment removed for export] *)
  ll_initc := [(0xdcf48, 0xdd010); (0xfd280, 0xfd288); (0xfd2a8, 0xfd2b0); (0xfd2d8, 0xfd308); (0xfd2a3, 0xfd2a4); (0xfd378, 0xfd37c)];   (* [comment removed for export] *)
  ll_init_img := [(0x10000, 0xcb538); (0xdb591, 0xdb594); (0xdb595, 0xdcf40); (0xfd018, 0xfd038);
                  (0xfd058, 0xfd060); (0xfd064, 0xfd068); (0xfd070, 0xfd078); (0xfd080, 0xfd178); (0xfd180, 0xfd278);
                  (0xfd2a3, 0xfd2a4); (0xfd378, 0xfd37c)];   (* [comment removed for export] *)
  ll_td_self := 0xdcf48; ll_td_tid := 0xdcf68; ll_td_locale := 0xdcfe0; ll_locale := 0xfd2d8; ll_td_canary := 0xdd000;
  ll_guard := 0xfd280; ll_auxvp := 0xfd2a8;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0xcb428;                    (* [comment removed for export] *)
  ll_stack := 65536;
  ll_credit := credit;
  ll_foot := foot;
  ll_init_cells := [(0xfd060, 4%nat, 1); (0xfd068, 8%nat, 0xfd070); (0xfd078, 8%nat, 0xad8c0); (0xfd178, 8%nat, 0x3a598)]   (* [comment removed for export] *) |}.

(* [comment removed for export] *)
Definition foot_in_envelope (foot : list (Z * Z)) : Prop :=
  forall iv, In iv foot -> (0xdb5b0 <= fst iv /\ snd iv <= 0xdc788) \/ (0xdcf38 <= fst iv /\ snd iv <= 0xdcf40) \/ (0xfd058 <= fst iv /\ snd iv <= 0xfd278).

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
