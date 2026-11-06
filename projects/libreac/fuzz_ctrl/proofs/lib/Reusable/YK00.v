(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK00.v (donor image sha256 7093581aab04), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1c YK15 YK1b.
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
Lemma t_emit_congr : forall (e : list event) (T T' : TSet),
t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
intros e T T' H tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
- intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
Qed.
Lemma t_alt2_congr : forall A A' B B' : TSet,
t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.
Lemma t_emit_nil_l : forall (T : TSet), T [] -> t_eq (t_emit [] T) T.
Proof. exact t_emit_nil_eq. Qed.
Lemma rz_eq : forall segs c (T T' : TSet),
t_eq T' T -> realizes segs c T' -> realizes segs c T.
Proof. intros segs c T T' Heq H. eapply rz_conseq; [exact H | exact Heq]. Qed.
Lemma t_emit_app3 : forall (a b c : list event) (T : TSet),
t_eq (t_emit a (t_emit b (t_emit c T))) (t_emit (a ++ b ++ c) T).
Proof.
intros a b c T. apply t_eq_sym.
eapply t_eq_trans; [apply t_emit_app|].
apply t_emit_congr. apply t_emit_app.
Qed.
Lemma map_app3 {A B} (f : A -> B) (a b c : list A) :
map f (a ++ b ++ c) = map f a ++ map f b ++ map f c.
Proof. rewrite !map_app. reflexivity. Qed.
Lemma len_word_of_nat : forall (bs : list byte),
len_word bs = Z_to_bv 64 (Z.of_nat (length bs)).
Proof. reflexivity. Qed.
Lemma read_bytes_map_of_store_ok : forall segs mem (a : word) (n : nat),
store_ok segs mem a n = true -> (Z.of_nat n < 2 ^ 64)%Z ->
exists w, read_bytes_map (wview segs mem) a (Z_to_bv 64 (Z.of_nat n)) = Some w.
Proof.
intros segs mem a n H Hn. rewrite read_bytes_map_eq. unfold word_to_nat.
rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
apply store_ok_read_aux. exact H.
Qed.
Lemma fd_insert_head_same : forall fds (fd : word) e e',
fd_insert ((fd, e) :: fds) fd e' = fd_insert fds fd e'.
Proof.
intros fds fd e e'. unfold fd_insert. cbn [List.filter fst].
rewrite bv_eqb_refl. cbn [negb]. reflexivity.
Qed.
Lemma filter_fd_id : forall (fds : list (word * FdEntry)) (fd : word),
fd_lookup fds fd = None ->
List.filter (fun p => negb (bv_eqb (fst p) fd)) fds = fds.
Proof.
induction fds as [|[k e] r IH]; intros fd H; [reflexivity|].
cbn [List.filter fst fd_lookup] in *.
destruct (bv_eqb k fd) eqn:E; [discriminate|]. cbn [negb].
rewrite (IH fd H). reflexivity.
Qed.
Lemma fd_insert_fresh_eq : forall fds (fd : word) e,
fd_lookup fds fd = None -> fd_insert fds fd e = (fd, e) :: fds.
Proof. intros fds fd e H. unfold fd_insert. rewrite (filter_fd_id fds fd H). reflexivity. Qed.
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
Lemma Z_to_bv_64_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof.
intro z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma c_ltu_lit : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_lit by lia. reflexivity. Qed.
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
Lemma bv_signed_neg : forall e, (0 < e <= 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 (- e)) = (- e)%Z.
Proof.
intros e He. rewrite Z_to_bv_signed. unfold bv_swrap.
unfold bv_wrap, bv_half_modulus, bv_modulus.
replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma c_lts_zero_nonneg : forall z, (0 <= z < 2 ^ 63)%Z ->
c_lts (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof.
intros z Hz. unfold c_lts, bv_lts. rewrite !bv_signed_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma c_lts_zero_errno : forall e, (0 < e <= 2 ^ 63)%Z ->
c_lts (Z_to_bv 64 (- e)) (Z_to_bv 64 0) = true.
Proof.
intros e He. unfold c_lts, bv_lts. rewrite bv_signed_neg by lia.
rewrite bv_signed_small by lia. apply Z.ltb_lt. lia.
Qed.
Lemma errno_ret_lit : forall e, errno_ret e = Z_to_bv 64 (- e).
Proof. reflexivity. Qed.
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
Lemma zallN_spec : forall (n : N) f,
zall (N.to_nat n) f 0%Z = true -> forall x, (0 <= x < Z.of_N n)%Z -> f x = true.
Proof. intros n f H x Hx. apply (zall_spec (N.to_nat n) f 0%Z H). rewrite N_nat_Z. lia. Qed.
Ltac rdn_at_hyp Hb :=
lazymatch type of Hb with
| rdn _ _ ?b _ = _ => rdn_at b; exact Hb
end.
