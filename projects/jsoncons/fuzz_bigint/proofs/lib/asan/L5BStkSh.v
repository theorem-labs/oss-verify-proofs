(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface HeapIfaceA L5Defs L5DefsAB0 L5CoreAB0 L5ArithSpecsB0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5BSS.
Import L5ASB.

Lemma stksh_sub (ar : asan_run) (Mk Mk' : word -> option byte) lo lo' : stksh ar Mk lo -> lo <= lo' -> lo mod 8 = 0 -> lo' mod 8 = 0 -> ahl_ceil ar <= lo -> 0 <= lo ->
  ar_stack_top ar <= 2 ^ 47 -> ar_sptop ar <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> Mk' (Z_to_bv 64 a) = Mk (Z_to_bv 64 a)) -> stksh ar Mk' lo'.
Proof.
  intros SSH LE L8 L8' CE L0 TOP SPT AG j Hj. unfold byte_at. unfold stksh, shadow_zero, byte_at in SSH.
  set (mx := Z.max (ar_sptop ar) (ar_stack_top ar)) in *.
  assert (MX : mx <= 2 ^ 47) by (subst mx; apply Z.max_lub; assumption).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (Q : S lo' + j = S lo + ((lo' - lo) / 8 + j) /\ 0 <= (lo' - lo) / 8 + j < (mx - lo) / 8 /\ 0 <= S lo' + j < 2 ^ 64 /\ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) (S lo' + j)).
  { unfold in_shadow_of, S, SB. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415.
    clear - Hj LE L8 L8' CE L0 MX. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct Q as (Q1 & Q2 & Q3 & Q4). rewrite AG by assumption. rewrite Q1. apply SSH. exact Q2.
Qed.

(* [comment removed for export] *)
Lemma stksh_frame (ar : asan_run) (M M' : word -> option byte) lo lo' flo fhi : stksh ar M lo -> lo <= lo' -> lo mod 8 = 0 -> lo' mod 8 = 0 -> ahl_ceil ar <= lo -> 0 <= lo ->
  ar_stack_top ar <= 2 ^ 47 -> ar_sptop ar <= 2 ^ 47 -> 2 ^ 46 <= flo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (flo <= a < fhi) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> stksh ar M' lo'.
Proof.
  intros SSH LE L8 L8' CE L0 TOP SPT FL AG. apply (stksh_sub ar M M' lo lo' SSH LE L8 L8' CE L0 TOP SPT).
  intros a Ha SX. apply AG. exact Ha. unfold in_shadow_of, S, SB in SX. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) in SX by (clear; lia).
  change ((2 ^ 47 - 1) / 8) with 17592186044415 in SX. clear - SX FL. lia.
Qed.
(* [comment removed for export] *)
Lemma stksh_ek (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte) lo lo' :
  stksh ar M lo -> lo <= lo' -> lo mod 8 = 0 -> lo' mod 8 = 0 -> ahl_ceil ar <= lo -> 0 <= lo -> ar_stack_top ar <= 2 ^ 47 -> ar_sptop ar <= 2 ^ 47 ->
  (forall a, L5CA.akept L ar LB FF sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside W a) -> stksh ar M' lo'.
Proof.
  intros SSH LE L8 L8' CE L0 TOP SPT EK WOFF. apply (stksh_sub ar M M' lo lo' SSH LE L8 L8' CE L0 TOP SPT).
  intros a Ha SX. apply EK. split. exact Ha. split. right; right; right; right; left. exact SX. apply WOFF. exact SX.
Qed.
(* [comment removed for export] *)
Lemma shadow_outside1 (ar : asan_run) (o sz a : Z) : 0 <= ahl_ceil ar -> (0x7fff7000 + 17592186048512 <= o \/ o + sz <= 0x7fff7000) ->
  in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> L5.outside [(o, sz)] a.
Proof.
  intros CE OB SX rr Hr IR. destruct Hr as [<-|[]]. unfold L5.in_rng in IR. cbn [fst snd] in IR. unfold in_shadow_of, S, SB in SX.
  replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) in SX by (clear; lia). change ((2 ^ 47 - 1) / 8) with 17592186044415 in SX.
  assert (Q : 0 <= ahl_ceil ar / 8) by (apply Z.div_pos; [exact CE | clear; lia]). clear - SX IR OB Q. lia.
Qed.
End L5BSS.
