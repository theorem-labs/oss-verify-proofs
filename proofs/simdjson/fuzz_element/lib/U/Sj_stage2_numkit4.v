(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_numkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition pw (m : word -> option byte) (a : word) : word :=
  match ov_read_bytes usegs m a 8 with Some bs => le_bytes_to_word bs | None => Z_to_bv 64 0 end.

Lemma pow_tab_read_pw : forall (m : word -> option byte) k a, (0 <= k)%Z -> (k + 8 <= 10600)%Z -> a = wa (T_POW + k) ->
  ov_read_bytes usegs m a 8 = Some (le8 (pw m a)).
Proof.
  intros m k a Hk Hl Ha. destruct (pow_tab_read m k a Hk Hl Ha) as [w RD].
  unfold pw. rewrite RD. rewrite le_bytes_to_word_le8. reflexivity.
Qed.

Ltac p_lia := lia.
Ltac s2_load_pow :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 8] =>
      let Ea := addr_expr a in
      rewrite (pow_tab_read_pw m (Ea - 87720)%Z a ltac:(p_lia) ltac:(p_lia) ltac:(unfold wa, T_POW; apply wz_eq_mod; f_equal; p_lia))
  end;
  load_post.
