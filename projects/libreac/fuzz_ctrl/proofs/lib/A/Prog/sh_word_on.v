(* The shadow of the n bytes at p as a REGION (Z -> Prop), for fuzz_ctrl's route (C) (a Theorem Labs lane, 2026-10-29 09:20Z;
   wave lead a Theorem Labs lane): exactly rng_asan.v's sh_word_rng range [sh_al8_lo p, sh_al8_hi p n). It is the CONTIGUOUS
   span of aligned 8-byte shadow words, from the word that holds shadow_addr p through the word that holds
   shadow_addr (p + n - 1), every word in between included; empty when n = 0. That is the shadow the runtime's check
   may load for [p, p + n): the inline check reads the first and the last word, and for N >= 65 (and for a nonzero
   inline word) the __asan_region_is_poisoned arm reads the whole range. A `shadow_rw_on (sh_word_on p n) m` premise
   (ShadowRwOn.v) names those bytes and no others.
   ASSUMPTION: the definition is over Z and assumes p + n <= 2^64 (no wrap). It carries no guard of its own: each
   user's premises must give it, and every current user does (addressable, S + N <= APPMEM_END, N <= 2^40).
   Author a Theorem Labs lane. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan.
Open Scope Z_scope.

Definition sh_word_on (p n a : Z) : Prop :=
  n <> 0 /\ rng_asan.sh_al8_lo p <= a < rng_asan.sh_al8_hi p n.

(* The aligned shadow word of the FIRST or the LAST byte of the range lies in it. *)
Lemma sh_word_on_end : forall p n x j, 0 < n -> (x = p \/ x = p + n - 1) -> 0 <= j < 8 ->
  sh_word_on p n (8 * ((x / 8 + ASAN_K) / 8) + j).
Proof.
  intros p n x j Hn Hx Hj. unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr.
  split; [lia|]. destruct Hx as [->| ->]; Z.div_mod_to_equations; lia.
Qed.
