(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateOverlay RefDeflFast6 RefDeflSafeFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition fb_buf_okP (buf : option Z) (len : Z) : Prop :=
  match buf with Some off => 0 <= off /\ off + len <= 65536 | None => True end.

Lemma fb_buf_ok_core : forall s,
  0 <= ds_strstart s - ds_block_start s < 2 ^ 32 -> 0 <= ds_strstart s <= 2 * ds_w_size s -> ds_w_size s <= 32768 ->
  fb_buf_okP (fb_buf s) (fb_len s) /\ fb_len s = ds_strstart s - ds_block_start s
  /\ (0 <= ds_block_start s -> fb_buf s = Some (ds_block_start s)) /\ (ds_block_start s < 0 -> fb_buf s = None).
Proof.
  intros s Hd Hs Hw. unfold fb_buf_okP, fb_buf, fb_len.
  assert (E64 : wrap64 (ds_strstart s - ds_block_start s) = ds_strstart s - ds_block_start s) by (apply wrap64_id; lia).
  rewrite E64. destruct (Z.leb_spec 0 (ds_block_start s)) as [B|B].
  - assert (E32 : wrap32 (ds_block_start s) = ds_block_start s) by (apply wrap32_id; lia).
    rewrite E32. split; [split; lia|]. split; [reflexivity|]. split; [intros _; reflexivity | intros; lia].
  - split; [exact I|]. split; [reflexivity|]. split; [intros; lia | intros _; reflexivity].
Qed.

Lemma fb_buf_ok_entry : forall s last, fb_entry s last -> fb_buf_okP (fb_buf s) (fb_len s).
Proof.
  intros s last FE. apply (fb_buf_ok_core s); [exact (fe_diff _ _ FE) | exact (fe_str _ _ FE) | exact (proj2 (fe_ws _ _ FE))].
Qed.

Lemma fb_buf_ok_flush : forall s last, flush_ok s last -> ds_w_size s <= 32768 -> fb_buf_okP (fb_buf s) (fb_len s).
Proof.
  intros s last F Hw. unfold flush_ok in F. cbv zeta in F. destruct F as (_ & _ & Hd & _ & Hs & _).
  apply (fb_buf_ok_core s); assumption.
Qed.
