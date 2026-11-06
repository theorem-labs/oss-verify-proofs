(* reac-pw/fuzz_link, image A: `apresent` does not see the 64-bit wrap.

   Every callee step and every symbolic run gives presence growth BOUNDED, `forall a, 0 <= a < 2 ^ 64 ->
   apresent H m a -> apresent H m' a`, but `akept`'s presence clauses (link_amem.v) and `akept_run`
   (LinkWalk.v) ask for it UNBOUNDED. `apresent H m a` reads only `Z_to_bv 64 a`, which is
   `Z_to_bv 64 (a mod 2 ^ 64)`, so the bounded form gives the unbounded one. `apresent_grow` is that step.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0n.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Lemma Z_to_bv64_mod : forall e, Z_to_bv 64 (e mod 2 ^ 64) = Z_to_bv 64 e.
Proof.
intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64)%Z. apply Z.mod_mod. lia.
Qed.

Lemma apresent_mod64 : forall H (m : word -> option byte) a,
  apresent H m a <-> apresent H m (a mod 2 ^ 64).
Proof. intros H m a. unfold apresent. rewrite (Z_to_bv64_mod a). reflexivity. Qed.

Lemma apresent_grow : forall H (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> apresent H m a -> apresent H m' a) ->
  forall a, apresent H m a -> apresent H m' a.
Proof.
intros H m m' Hb a Ha.
apply (proj2 (apresent_mod64 H m' a)).
apply Hb; [pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)); lia |].
exact (proj1 (apresent_mod64 H m a) Ha).
Qed.
