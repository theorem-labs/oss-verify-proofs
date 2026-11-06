(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1c YK15 YK1b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Lemma t_emit_app : forall (a b : list event) (T : TSet),
t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)).
Proof.
intros a b T tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)].
+ apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
* left. exact Hp.
* right. exists b'. split; [reflexivity | left; exact Hp].
+ right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|].
right. exists tr'. auto.
- intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
+ left. apply is_prefix_app_r. exact Hp.
+ left. apply is_prefix_app_mono. exact Hp.
+ right. exists tr''. rewrite app_assoc. auto.
Qed.

Lemma t_alt2_congr : forall A A' B B' : TSet,
t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.









Lemma u64_lit : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.
Lemma v_add_lit : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2 ^ 64)%Z ->
v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b Ha Hb Hab. unfold v_add. rewrite !u64_lit by lia. reflexivity.
Qed.
Lemma v_sub_lit : forall a b, (0 <= b <= a)%Z -> (a < 2 ^ 64)%Z ->
v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
intros a b Hab Ha. unfold v_sub. rewrite !u64_lit by lia. reflexivity.
Qed.
Lemma v_addi_lit : forall a i, (0 <= a < 2 ^ 64)%Z ->
v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.


Lemma c_eq_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.
Lemma bv_signed_small : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap.
unfold bv_wrap, bv_half_modulus, bv_modulus.
replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.




Ltac show_goal_marker := match goal with |- ?g => idtac "=====GOAL=====" g end.
Lemma rdn_addr_eq : forall segs m (a b : word) n r,
a = b -> rdn segs m b n = r -> rdn segs m a n = r.
Proof. intros segs m a b n r -> H. exact H. Qed.
Ltac rdn_at b :=
apply (rdn_addr_eq _ _ _ b);
[ first [ f_equal; lia
| lazymatch goal with |- ?g => YK1a.check_closed_term g end;
apply bv_eq; vm_compute; reflexivity ]
| ].
Fixpoint zall (n : nat) (f : Z -> bool) (z : Z) : bool :=
match n with
| O => true
| S n' => if f z then zall n' f (z + 1)%Z else false
end.
Lemma zall_spec : forall n f z,
zall n f z = true -> forall x, (z <= x < z + Z.of_nat n)%Z -> f x = true.
Proof.
induction n as [|n IH]; intros f z H x Hx; [lia|].
cbn [zall] in H. destruct (f z) eqn:E; [|discriminate].
destruct (Z.eq_dec x z) as [->|Hne]; [exact E|].
apply (IH f (z + 1)%Z H). lia.
Qed.

Ltac rdn_at_hyp Hb :=
lazymatch type of Hb with
| rdn _ _ ?b _ = _ => rdn_at b; exact Hb
end.
