(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 128).

Definition CST (w pv hd : arr) (st : cstrm) : Prop :=
  arr_len w = 2 * ws /\ arr_len pv = ws /\ arr_len hd = hs /\ cs_input st = cs_input (ds_strm ds)
  /\ Z.of_nat (length (cs_out_rev st)) + cs_avail_out st = OLEN0 + AV0
  /\ 0 <= cs_avail_out st /\ OLEN0 <= Z.of_nat (length (cs_out_rev st)).



Lemma arr_blit_upd : forall (dst : arr) dofs (src : arr) sofs n,
  arr_blit dst dofs src sofs n = arr_upd dst dofs (arr_slice src sofs n).
Proof.
  intros dst dofs src sofs n. unfold arr_blit, arr_slice. generalize (Z.to_nat n) as k. clear n.
  intros k. revert dst dofs sofs. induction k as [|k IH]; intros dst dofs sofs; [reflexivity|].
  cbn [arr_blit_nat arr_slice_nat arr_upd]. apply IH.
Qed.

Inductive skind :=
  | KBlockStart | KStrstart | KInsert | KPending | KMatches | KHighWater
  | KPendingOut (off : Z)
  | KPb (i c' : Z)
  | KFrame.

End Walk.

Definition dtVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 6); (35%nat, 2 ^ 32)].
Lemma sx32_cases : forall a, 0 <= a < 2 ^ 32 ->
  (a < 2 ^ 31 /\ szwrap 32 a mod 2 ^ 64 = a) \/ (2 ^ 31 <= a /\ szwrap 32 a mod 2 ^ 64 = a + 2 ^ 64 - 2 ^ 32).
Proof.
  intros a Ha. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296 in *.
  change (2 ^ 31) with 2147483648. change (2 ^ 64) with 18446744073709551616.
  destruct (Z_lt_le_dec a 2147483648).
  - left. split; [lia|]. rewrite (Z.mod_small (a + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. replace ((a + 2147483648) mod 4294967296) with (a + 2147483648 - 4294967296) by (Z.to_euclidean_division_equations; lia).
    Z.to_euclidean_division_equations; lia.
Qed.
Lemma sx32_u64_ge : forall a q, 0 <= a < 2 ^ 32 -> 0 <= q < 2 ^ 31 -> q <= a -> q <= szwrap 32 a mod 2 ^ 64.
Proof. intros a q Ha Hp Hle. destruct (sx32_cases a Ha) as [[? E]|[? E]]; rewrite E; lia. Qed.
Lemma sx32_u64_nz : forall a, 0 < a < 2 ^ 32 -> szwrap 32 a mod 2 ^ 64 <> 0.
Proof. intros a Ha. destruct (sx32_cases a ltac:(lia)) as [[? E]|[? E]]; rewrite E; lia. Qed.
Lemma snez_sx32 : forall a, 0 <= a < 2 ^ 32 -> (if 0 <? szwrap 32 a mod 2 ^ 64 then 1 else 0) = (if 0 <? a then 1 else 0).
Proof.
  intros a Ha. destruct (sx32_cases a Ha) as [[? E]|[? E]]; rewrite E; [reflexivity|].
  destruct (Z.ltb_spec 0 (a + 2 ^ 64 - 2 ^ 32)); destruct (Z.ltb_spec 0 a); first [reflexivity | lia].
Qed.


Lemma left_spell : forall str bs, (str - bs mod 2 ^ 64) mod 2 ^ 32 = wrap32 (str - bs).
Proof.
  intros str bs. rewrite wrap32_mod.
  pose proof (Z_div_mod_eq_full bs (2 ^ 64)) as E.
  replace (str - bs mod 2 ^ 64) with ((str - bs) + (bs / 2 ^ 64 * 2 ^ 32) * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma szwrap32_modl : forall x y, szwrap 32 (x + y) = szwrap 32 (x mod 2 ^ 32 + y).
Proof. intros x y. rewrite <- (szwrap_mod 32 (x + y)) by lia. rewrite <- (szwrap_mod 32 (x mod 2 ^ 32 + y)) by lia. f_equal. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma szwrap32_mod1 : forall x, szwrap 32 x = szwrap 32 (x mod 2 ^ 32).
Proof. intros x. symmetry. apply szwrap_mod. lia. Qed.

Lemma sx32_small : forall a, 0 <= a < 2 ^ 31 -> szwrap 32 a mod 2 ^ 64 = a /\ szwrap 32 a = a.
Proof. intros a Ha. rewrite (szwrap_small 32) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma sx32_eq_small : forall x l, 0 <= l < 2 ^ 31 ->
  (szwrap 32 x mod 2 ^ 64 = l <-> wrap32 x = l).
Proof.
  intros x l Hl. rewrite wrap32_mod. rewrite (szwrap32_mod1 x).
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)) as Hr.
  destruct (sx32_cases (x mod 2 ^ 32) Hr) as [[H1 E]|[H1 E]]; rewrite E; lia.
Qed.

Lemma lnot_mod8 : forall len, Z.lnot len mod 2 ^ 8 = Z.lxor (len mod 2 ^ 8) (-1) mod 2 ^ 8.
Proof.
  intros len. rewrite Z.lxor_m1_r. unfold Z.lnot, Z.pred.
  pose proof (Z_div_mod_eq_full len (2 ^ 8)) as E.
  replace (- len + -1) with ((- (len mod 2 ^ 8) + -1) + (- (len / 2 ^ 8)) * 2 ^ 8) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma lnot_hi_mod8 : forall len,
  Z.shiftr (wrap32 (Z.lnot len)) 8 mod 2 ^ 8 = (Z.lxor len (-1) mod 2 ^ 32 / 2 ^ 8) mod 2 ^ 8.
Proof. intros len. rewrite Z.lxor_m1_r, wrap32_mod, Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma spb_twice : forall X a b, set_pending_buf (set_pending_buf X a) b = set_pending_buf X b.
Proof. intros. reflexivity. Qed.

Lemma sx32_u64_gt : forall a q, 0 <= a < 2 ^ 32 -> 0 <= q -> q < a -> q + 1 < 2 ^ 31 -> q < szwrap 32 a mod 2 ^ 64.
Proof. intros a q Ha Hq Hlt Hq2. pose proof (sx32_u64_ge a (q + 1) Ha ltac:(lia) ltac:(lia)). lia. Qed.
