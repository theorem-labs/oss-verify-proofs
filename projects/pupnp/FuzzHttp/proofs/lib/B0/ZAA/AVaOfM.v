(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim PEnv APrimSpec2 APrimQ ASec ASecD AQuar AQuarM AQuarR AHeap ALedger ALinkPg ALinkVm ALink ALinkPrim ALinkSec ALinkFreeIn AHeap2 AHeapB AMallocP AVaOf.
Import ListNotations.
Open Scope Z_scope.

Lemma cache_alloc_mfa : forall P c, 1 <= c <= 31 -> length (pr_cls P) = 32%nat ->
  let P' := fst (cache_alloc P c) in let k := get_cls P c in
  p_mfa (get_cls P' c) = (if p_cnt k =? 0 then p_mfa (refill k c) else p_mfa k).
Proof.
  intros P c Hc LEN. cbv zeta. unfold cache_alloc. destruct (cache_alloc_cls (get_cls P c) c) as [kp v] eqn:EC. cbn [fst].
  assert (EM : p_mfa kp = (if p_cnt (get_cls P c) =? 0 then p_mfa (refill (get_cls P c) c) else p_mfa (get_cls P c))).
  { unfold cache_alloc_cls in EC. destruct (p_cnt (get_cls P c) =? 0); inversion EC; reflexivity. }
  destruct P as [cls ini ca cm]. cbn [pr_cls pr_calloc pr_cmapped] in *.
  rewrite get_cls_set_same by (first [exact LEN | lia]). exact EM.
Qed.

Definition D_calloc (P : prim) (c : Z) : Z := if p_cnt (get_cls P c) =? 0 then D_gfa (get_cls P c) c (max_count c / 2) else 0.

Lemma cache_alloc_sums : forall P c, 1 <= c <= 31 -> length (pr_cls P) = 32%nat ->
  sum_mu (fst (cache_alloc P c)) + sum_mfa (fst (cache_alloc P c)) = sum_mu P + sum_mfa P + D_calloc P c.
Proof.
  intros P c Hc LEN. destruct (cache_alloc_mu P c Hc LEN) as (EO & EMU & _). pose proof (cache_alloc_mfa P c Hc LEN) as EMF. cbv zeta in *.
  set (P' := fst (cache_alloc P c)) in *. set (k := get_cls P c) in *.
  rewrite (sum_mu_upd P P' c (p_mu (get_cls P' c) - p_mu k) Hc ltac:(intros c' Hc' NE; rewrite (EO c' Hc' NE); reflexivity) ltac:(fold k; lia)).
  rewrite (sum_mfa_upd P P' c (p_mfa (get_cls P' c) - p_mfa k) Hc ltac:(intros c' Hc' NE; rewrite (EO c' Hc' NE); reflexivity) ltac:(fold k; lia)).
  rewrite EMU, EMF. unfold D_calloc. fold k. destruct (p_cnt k =? 0); [| lia]. pose proof (refill_D_gfa k c). lia.
Qed.

Theorem malloc_prim_va_of : forall s s1' c, 1 <= c <= 31 -> length (pr_cls (bs_prim s)) = 32%nat ->
  bs_X s1' = (fst (cache_alloc (bs_prim s) c), bs_sec s) -> bs_nsec s1' = bs_nsec s + 0 ->
  va_of s1' = mkVA (va_prim (va_of s) + D_calloc (bs_prim s) c) (va_chunks (va_of s)) (va_nsec (va_of s)) (va_aux (va_of s)).
Proof.
  intros s s1' c Hc LEN EX EN. unfold bs_X in EX. pose proof (f_equal fst EX) as EP. pose proof (f_equal snd EX) as ES. cbn [fst snd] in EP, ES.
  unfold va_of. cbn [va_prim va_chunks va_nsec va_aux].
  pose proof (cache_alloc_sums (bs_prim s) c Hc LEN) as CS. rewrite EP, ES, EN. f_equal; lia.
Qed.

Theorem malloc_sec_va_of : forall s s1' a size, se_nres (bs_sec s) mod 16384 = 0 -> 0 <= se_nres (bs_sec s) ->
  bs_X s1' = (bs_prim s, sec_alloc (bs_sec s) a size) -> bs_nsec s1' = bs_nsec s + 1 ->
  let v' := va_sec_alloc (va_of s) (bs_sec s) a (sec_msize size) in
  va_prim v' = va_prim (va_of s1') /\ Permutation (va_chunks v') (va_chunks (va_of s1')) /\ va_nsec v' = va_nsec (va_of s1') /\ va_aux v' = va_aux (va_of s1').
Proof.
  intros s s1' a size M16 N0 EX EN. unfold bs_X in EX. pose proof (f_equal fst EX) as EP. pose proof (f_equal snd EX) as ES. cbn [fst snd] in EP, ES. cbv zeta.
  unfold va_sec_alloc, va_of. cbn [va_prim va_chunks va_nsec va_aux]. rewrite EP, ES, EN.
  split; [reflexivity|]. split.
  { unfold sec_alloc. cbn [se_chunks]. rewrite map_app. cbn [map]. unfold cpair at 3. cbn [sc_beg sc_msize]. apply Permutation_cons_append. }
  split; [reflexivity|].
  unfold aux_of, sec_alloc, parr_step_cost. cbn [se_nres]. change (131072 + 131072 / 8 + 2 * 4096) with 155648.
  destruct (se_n (bs_sec s) =? se_nres (bs_sec s)); [| lia].
  assert (E1 : (se_nres (bs_sec s) + 16384) / 16384 = se_nres (bs_sec s) / 16384 + 1) by (clear - M16 N0; Z.div_mod_to_equations; lia).
  rewrite E1. lia.
Qed.
