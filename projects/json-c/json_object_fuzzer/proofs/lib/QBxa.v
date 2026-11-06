(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QSjk QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QSjk QRjH QRjH.Mq3.
Import ListNotations.
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
| lazymatch goal with |- ?g => QEVk.Mq0.check_closed_term g end;
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
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import QsRG.Mq0 Qnhz.Mq0 QRjH.Mq3.
Import ListNotations.
Open Scope bv_scope.

Definition in_rng (a base : word) (len : Z) : Prop :=
(bv_unsigned base <= bv_unsigned a < bv_unsigned base + len)%Z.

Definition in_rngb (a base : word) (len : Z) : bool :=
(Z.leb (bv_unsigned base) (bv_unsigned a) && Z.ltb (bv_unsigned a) (bv_unsigned base + len))%bool.

Lemma in_rngb_spec : forall a base len, in_rngb a base len = true <-> in_rng a base len.
Proof.
intros. unfold in_rngb, in_rng. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Fixpoint outside (a : word) (rs : list (word * Z)) : Prop :=
match rs with
| [] => True
| (b, n) :: rs' => ~ in_rng a b n /\ outside a rs'
end.

Lemma outside_app : forall a rs1 rs2, outside a (rs1 ++ rs2) <-> outside a rs1 /\ outside a rs2.
Proof.
intros a rs1 rs2. induction rs1 as [|[b n] rs1 IH]; cbn; tauto.
Qed.

Definition frame_mod (mem mem' : word -> option byte) (rs : list (word * Z)) : Prop :=
(forall a, outside a rs -> mem' a = mem a) /\ mem_grows mem mem'.

Lemma frame_mod_refl : forall mem rs, frame_mod mem mem rs.
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma frame_mod_weaken : forall mem mem' rs rs',
(forall a, outside a rs' -> outside a rs) -> frame_mod mem mem' rs -> frame_mod mem mem' rs'.
Proof.
intros mem mem' rs rs' Hw [He Hg]. split; [|exact Hg]. intros a Ha. apply He, Hw, Ha.
Qed.

Lemma frame_mod_trans : forall m1 m2 m3 rs1 rs2,
frame_mod m1 m2 rs1 -> frame_mod m2 m3 rs2 -> frame_mod m1 m3 (rs1 ++ rs2).
Proof.
intros m1 m2 m3 rs1 rs2 [E1 G1] [E2 G2]. split.
- intros a Ha. apply outside_app in Ha as [H1 H2]. rewrite (E2 a H2). apply E1, H1.
- eapply mem_grows_trans; eassumption.
Qed.

Lemma frame_mod_trans_same : forall m1 m2 m3 rs,
frame_mod m1 m2 rs -> frame_mod m2 m3 rs -> frame_mod m1 m3 rs.
Proof.
intros m1 m2 m3 rs H1 H2. eapply frame_mod_weaken; [| exact (frame_mod_trans _ _ _ _ _ H1 H2)].
intros a Ha. apply outside_app. tauto.
Qed.

Lemma wbytes_outside : forall bs m (base a : word),
~ in_rng a base (Z.of_nat (length bs)) ->
(bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
wbytes m base bs a = m a.
Proof.
intros bs m base a Hn Hb. unfold in_rng in Hn.
destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned base)) as [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above. lia.
Qed.

Lemma frame_mod_wbytes : forall m base bs,
(bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
frame_mod m (wbytes m base bs) [(base, Z.of_nat (length bs))].
Proof.
intros m base bs Hb. split.
- intros a [Ha _]. apply wbytes_outside; assumption.
- apply wbytes_grows.
Qed.

Lemma frame_mod_store_ok : forall segs mem mem' rs a n,
frame_mod mem mem' rs -> store_ok segs mem a n = true -> store_ok segs mem' a n = true.
Proof. intros segs mem mem' rs a n [_ Hg] H. eapply store_ok_mono; eassumption. Qed.

Lemma frame_mod_byte : forall mem mem' rs a,
frame_mod mem mem' rs -> outside a rs -> mem' a = mem a.
Proof. intros mem mem' rs a [He _] Ha. apply He, Ha. Qed.

Lemma frame_mod_rdn : forall segs mem mem' rs n (a : word),
frame_mod mem mem' rs ->
(forall i, (0 <= i < Z.of_nat n)%Z -> outside (Z_to_bv 64 (bv_unsigned a + i)) rs) ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
rdn segs mem' a n = rdn segs mem a n.
Proof.
intros segs mem mem' rs n. induction n as [|n IH]; intros a Hf Ho Hb; [reflexivity|].
cbn [rdn]. pose proof (u64_range a).
assert (Ha : mem' a = mem a).
{ pose proof (Ho 0%Z ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
eapply frame_mod_byte; eassumption. }
rewrite Ha.
destruct n as [|n'].
- reflexivity.
- assert (Ha1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
rewrite (IH (a + 1) Hf).
+ reflexivity.
+ intros i Hi. rewrite Ha1. replace (bv_unsigned a + 1 + i)%Z with (bv_unsigned a + (1 + i))%Z by lia.
apply Ho. lia.
+ rewrite Ha1. lia.
Qed.
End Mq1.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEVk QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import QsRG.Mq0 Qnhz.Mq0 Qrxj QEVk.Mq0 QRjH.Mq3 QiVh.Mq0.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma wbytes_inside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
cbn [wbytes length] in *.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- assert (x = a) by (apply bv_eq; exact Heq). subst x.
rewrite Z.sub_diag. cbn [Z.to_nat nth].
destruct rest as [|b' rest'].
+ cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
+ cbn [length] in Hnw. rewrite wbytes_below.
* rewrite bv_eqb_refl. reflexivity.
* rewrite u_add1 by lia. cbn [length]. lia.
* rewrite u_add1 by lia. lia.
- assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
by (apply u_add1; lia).
rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.

Lemma wbytes_outside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
wbytes m a bs x = m x.
Proof.
intros bs m a x Hnw [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.

Lemma wbytes_select : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
P x = true) ->
wbytes (fun x => if P x then f x else g x) a bs
= (fun x => if P x then wbytes f a bs x else g x).
Proof.
intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
- rewrite !wbytes_outside by lia. reflexivity.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
+ rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
+ rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_select_r : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
P x = false) ->
wbytes (fun x => if P x then f x else g x) a bs
= (fun x => if P x then f x else wbytes g a bs x).
Proof.
intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
- rewrite !wbytes_outside by lia. reflexivity.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
+ rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
+ rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_shadow : forall m (a : word) bs1 bs2,
length bs1 = length bs2 ->
bv_unsigned a + Z.of_nat (length bs2) <= 2^64 ->
wbytes (wbytes m a bs1) a bs2 = wbytes m a bs2.
Proof.
intros m a bs1 bs2 Hlen Hnw. apply functional_extensionality. intro x.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
- rewrite !wbytes_outside by lia. reflexivity.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs2))) as [Hin|Hout].
+ rewrite !wbytes_inside by lia. reflexivity.
+ rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma rdn_const : forall segs m (a : word) n b,
bv_unsigned a + Z.of_nat n <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m x = Some b) ->
rdn segs m a n = Some (repeat b n).
Proof.
intros segs m a n; revert a; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
cbn [rdn repeat]. rewrite (Hall a) by lia.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
rewrite (IH (a + 1)%bv b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
reflexivity.
Qed.

Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.

Definition in_win (sp0 : word) (x : word) : Prop :=
win_lo sp0 <= bv_unsigned x < bv_unsigned sp0.

Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.

Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
forall x : word, in_win sp0 x -> J x <> None.

Lemma wfJ_const : forall sp0 b, wfJ sp0 (fun _ => Some b).
Proof. intros sp0 b x _. discriminate. Qed.

Lemma wfJ_wbytes : forall sp0 J a bs, wfJ sp0 J -> wfJ sp0 (wbytes J a bs).
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.

Definition agree_above (lo : Z) (J J' : word -> option byte) : Prop :=
forall x : word, lo <= bv_unsigned x -> J' x = J x.

Lemma agree_above_refl : forall lo J, agree_above lo J J.
Proof. intros lo J x _. reflexivity. Qed.

Lemma agree_above_trans : forall lo J1 J2 J3,
agree_above lo J1 J2 -> agree_above lo J2 J3 -> agree_above lo J1 J3.
Proof. intros lo J1 J2 J3 H12 H23 x Hx. rewrite (H23 x Hx). apply H12. exact Hx. Qed.

Lemma agree_above_mono : forall lo lo' J J',
lo <= lo' -> agree_above lo J J' -> agree_above lo' J J'.
Proof. intros lo lo' J J' Hle H x Hx. apply H. lia. Qed.

Lemma agree_above_wbytes : forall lo J a bs,
bv_unsigned a + Z.of_nat (length bs) <= lo ->
agree_above lo J (wbytes J a bs).
Proof.
intros lo J a bs Hle x Hx. apply wbytes_above. lia.
Qed.

Lemma rdn_agree_above : forall segs lo J J' (a : word) n,
agree_above lo J J' -> lo <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= 2^64 ->
rdn segs J' a n = rdn segs J a n.
Proof.
intros segs lo J J' a n H Hlo Hnw. apply rdn_ext; [exact Hnw|].
intros x Hx. apply H. lia.
Qed.

Section CMem.
Variable sp0 : word.
Variable mem0 : word -> option byte.

Let csel := cmem sp0 mem0.

#[using="Type"] Lemma stack_max_size_pos : 0 < stack_max_size.
Proof. rewrite stack_max_size_val. lia. Qed.

#[using="Type"] Lemma wbytes_cmem_win : forall J D (a : word) bs,
win_lo sp0 <= bv_unsigned a ->
bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned sp0 ->
wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 (wbytes J a bs) D.
Proof.
intros J D a bs Hlo Hhi. unfold cmem.
pose proof (u64_range sp0) as Hsp.
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
(fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
apply functional_extensionality. intro x.
destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
by (first [lia | intros y Hy; apply Z.leb_le; lia]).
reflexivity.
Qed.

#[using="Type"] Lemma wbytes_cmem_data : forall J D (a : word) bs,
bv_unsigned a + Z.of_nat (length bs) <= win_lo sp0 ->
wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 J (wbytes D a bs).
Proof.
intros J D a bs Hhi. unfold cmem.
pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
unfold win_lo in *.
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
(fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
apply functional_extensionality. intro x.
destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
reflexivity.
Qed.

#[using="Type"] Lemma rdn_cmem_above : forall segs J D (a : word) n,
bv_unsigned sp0 <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= 2^64 ->
rdn segs (cmem sp0 mem0 J D) a n = rdn segs mem0 a n.
Proof.
intros segs J D a n Hlo Hnw. apply rdn_ext; [exact Hnw|].
intros x Hx. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma rdn_cmem_win : forall segs J D (a : word) n,
win_lo sp0 <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
rdn segs (cmem sp0 mem0 J D) a n = rdn segs J a n.
Proof.
intros segs J D a n Hlo Hhi. pose proof (u64_range sp0).
apply rdn_ext; [lia|].
intros x Hx. unfold cmem.
rewrite (proj2 (Z.leb_gt _ _)) by lia.
rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma rdn_cmem_data : forall segs J D (a : word) n,
bv_unsigned a + Z.of_nat n <= win_lo sp0 ->
rdn segs (cmem sp0 mem0 J D) a n = rdn segs D a n.
Proof.
intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
unfold win_lo in *.
apply rdn_ext; [lia|].
intros x Hx. unfold cmem, win_lo.
rewrite (proj2 (Z.leb_gt _ _)) by lia.
rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma cmem_at_above : forall J D (x : word),
bv_unsigned sp0 <= bv_unsigned x -> cmem sp0 mem0 J D x = mem0 x.
Proof. intros. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

#[using="Type"] Lemma cmem_at_win : forall J D (x : word),
in_win sp0 x -> cmem sp0 mem0 J D x = J x.
Proof.
intros J D x [Hlo Hhi]. unfold cmem.
rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma cmem_at_data : forall J D (x : word),
bv_unsigned x < win_lo sp0 -> cmem sp0 mem0 J D x = D x.
Proof.
intros J D x Hx. pose proof stack_max_size_pos. unfold cmem, win_lo in *.
rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma store_ok_cmem_win : forall segs J D (a : word) n,
wfJ sp0 J ->
win_lo sp0 <= bv_unsigned a ->
bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
store_ok segs (cmem sp0 mem0 J D) a n = true.
Proof.
intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
apply store_ok_of_all; [lia|].
intros x Hx. unfold wview.
rewrite cmem_at_win by (unfold in_win; lia).
destruct (J x) as [b|] eqn:E; [discriminate|].
exfalso. apply (HJ x); [unfold in_win; lia | exact E].
Qed.

#[using="Type"] Lemma store_ok_cmem_data : forall segs J D (a : word) n,
wseg_ok segs a n = true ->
store_ok segs (cmem sp0 mem0 J D) a n = true.
Proof. intros. apply store_ok_wseg. assumption. Qed.

End CMem.

Lemma cmem_init : forall ph (sp0 : word) av ev uid hw (rdraw : EntryDraw),
wrap_mem ph sp0 av ev uid hw rdraw
= cmem sp0 (wrap_mem ph sp0 av ev uid hw rdraw) (fun _ => Some (Z_to_bv 8 0)) (fun _ => None).
Proof.
intros ph sp0 av ev uid hw rdraw. apply functional_extensionality. intro x.
unfold cmem.
destruct (bv_unsigned sp0 <=? bv_unsigned x) eqn:E1; [reflexivity|].
apply Z.leb_gt in E1.
unfold wrap_mem, win_lo.
assert (Hst : stack_to_mem sp0 (entry_stack_image ph sp0 av ev uid hw rdraw) x = None).
{ unfold stack_to_mem. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
rewrite Hst. rewrite (proj2 (Z.ltb_lt _ _) E1), andb_true_r. reflexivity.
Qed.
End Mq2.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq3.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition sub {A} (bs : list A) (j k : nat) : list A := firstn k (skipn j bs).

#[using="Type"] Lemma firstn_add : forall {A} (l : list A) a b,
firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
intros A l a. revert l. induction a as [|a IH]; intros l b.
- cbn. reflexivity.
- destruct l as [|x l]; cbn.
+ destruct b; reflexivity.
+ rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma firstn_sub_app : forall {A} (bs : list A) j k,
firstn j bs ++ sub bs j k = firstn (j + k) bs.
Proof. intros. unfold sub. rewrite firstn_add. reflexivity. Qed.

#[using="Type"] Lemma skipn_add : forall {A} (l : list A) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
destruct l as [|x l]; cbn; [destruct b; reflexivity|]. apply IH.
Qed.

#[using="Type"] Lemma sub_length : forall {A} (bs : list A) j k,
(j + k <= length bs)%nat -> length (sub bs j k) = k.
Proof.
intros A bs j k H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.

#[using="Type"] Lemma sub_split : forall {A} (bs : list A) j a b,
sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b.
Proof.
intros A bs j a b. unfold sub. rewrite firstn_add. f_equal.
rewrite <- skipn_add. f_equal; lia.
Qed.

#[using="Type"] Lemma sub_0_all : forall {A} (bs : list A), sub bs 0 (length bs) = bs.
Proof. intros. unfold sub. cbn. apply firstn_all. Qed.

#[using="Type"] Lemma length_firstn_id : forall {A} (bs : list A) k, k = length bs -> firstn k bs = bs.
Proof. intros A bs k ->. apply firstn_all. Qed.

#[using="Type"] Lemma sub_nth : forall (bs : list byte) j,
(j < length bs)%nat -> sub bs j 1 = [nth j bs (Z_to_bv 8 0)].
Proof.
intros bs j. revert bs. induction j as [|j IH]; intros bs H.
- destruct bs; cbn in *; [lia|reflexivity].
- destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.

#[using="Type"] Lemma at_succ : forall (a : word) d, (at_ a d + 1)%bv = at_ a (d + 1).
Proof.
intros a d. unfold at_. apply bv_eq.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned (1 : word)) with 1.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma word_succ_at : forall (a : word), (a + 1)%bv = at_ a 1.
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.

#[using="Type"] Lemma at_u : forall (a : word) d,
0 <= bv_unsigned a + d -> bv_unsigned a + d < 2^64 ->
bv_unsigned (at_ a d) = bv_unsigned a + d.
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.

#[using="Type"] Lemma at_nat : forall (a : word) (j : nat), (a + nat_to_word j)%bv = at_ a (Z.of_nat j).
Proof.
intros a j. unfold at_, nat_to_word. apply bv_eq.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

#[using="Type"] Lemma wbytes_app : forall bs1 bs2 m (a : word),
wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (at_ a (Z.of_nat (length bs1))) bs2.
Proof.
induction bs1 as [|b r IH]; intros bs2 m a.
- cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
- cbn [app wbytes length]. rewrite IH. f_equal.
rewrite word_succ_at, at_at. f_equal. lia.
Qed.

#[using="Type"] Lemma wbytes_extend : forall m (dst : word) bs j k,
wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
= wbytes m dst (firstn (j + k) bs) \/ (length bs < j)%nat.
Proof.
intros m dst bs j k.
destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma wbytes_extend' : forall m (dst : word) bs j k,
(j <= length bs)%nat ->
wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
= wbytes m dst (firstn (j + k) bs).
Proof.
intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.

#[using="Type"] Lemma rdn_skipn : forall segs mem n (a : word) bs j,
rdn segs mem a n = Some bs -> (j <= n)%nat ->
rdn segs mem (at_ a (Z.of_nat j)) (n - j) = Some (skipn j bs).
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs j H Hj.
- assert (j = 0)%nat by lia. subst j. cbn in H. injection H as <-.
rewrite at_0. reflexivity.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1)%bv n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct j as [|j].
+ rewrite at_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
+ cbn [skipn]. replace (S n - S j)%nat with (n - j)%nat by lia.
replace (at_ a (Z.of_nat (S j))) with (at_ (a + 1)%bv (Z.of_nat j))
by (rewrite word_succ_at, at_at; f_equal; lia).
apply IH; [exact Er|lia].
Qed.

#[using="Type"] Lemma rdn_sub : forall segs mem n (a : word) bs j k,
rdn segs mem a n = Some bs -> (j + k <= n)%nat ->
rdn segs mem (at_ a (Z.of_nat j)) k = Some (sub bs j k).
Proof.
intros segs mem n a bs j k H Hjk. unfold sub.
apply (rdn_firstn segs mem (n - j)); [|lia].
apply rdn_skipn; [exact H|lia].
Qed.
End FPGEN1.

Abbreviation lez := bytes_le_to_Z.
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

Definition LWv (l : list byte) : word := v_lw (Z_to_bv 64 (lez l)).

#[using="Type"] Lemma lez_bound_len : forall bs k, length bs = k -> 0 <= lez bs < 2 ^ (8 * Z.of_nat k).
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
#[using="Type"] Lemma lez4_range : forall l, length l = 4%nat -> 0 <= lez l < 2 ^ 32.
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
#[using="Type"] Lemma u_lez4 : forall l, length l = 4%nat -> bv_unsigned (Z_to_bv 64 (lez l)) = lez l.
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.

#[using="Type"] Lemma testbit_u_LWv : forall l i, length l = 4%nat -> 0 <= i < 32 ->
Z.testbit (bv_unsigned (LWv l)) i = Z.testbit (lez l) i.
Proof.
intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
rewrite bv_wrap_spec_low by lia.
rewrite bv_swrap_spec by lia.
case_bool_decide; [reflexivity|].
replace i with 31 by lia. reflexivity.
Qed.

#[using="Type"] Lemma u_vlw_mod32 : forall l, length l = 4%nat -> bv_unsigned (LWv l) mod 2 ^ 32 = lez l.
Proof.
intros l H. pose proof (lez4_range l H) as R.
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
- rewrite Z.mod_pow2_bits_low by lia. apply testbit_u_LWv; [exact H|lia].
- rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (Z_testbit_high 32); lia.
Qed.

#[using="Type"] Lemma lez_cons : forall b bs, lez (b :: bs) = Z.lor (bv_unsigned b) (Z.shiftl (lez bs) 8).
Proof. reflexivity. Qed.

#[using="Type"] Lemma testbit_lez_high : forall bs i, 8 * Z.of_nat (length bs) <= i -> Z.testbit (lez bs) i = false.
Proof.
intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
apply lez_bound_len. reflexivity.
Qed.

#[using="Type"] Lemma testbit_lez_skipn : forall q bs i, 0 <= i ->
Z.testbit (lez (skipn q bs)) i = Z.testbit (lez bs) (i + 8 * Z.of_nat q).
Proof.
induction q as [|q IH]; intros bs i Hi.
- cbn [skipn]. f_equal. lia.
- destruct bs as [|b bs].
+ cbn [skipn lez]. rewrite !Z.bits_0. reflexivity.
+ cbn [skipn]. rewrite IH by lia. rewrite lez_cons.
rewrite Z.lor_spec, Z.shiftl_spec by lia.
pose proof (u8_range b).
rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. cbn [orb]. f_equal. lia.
Qed.

#[using="Type"] Lemma testbit_lez_firstn : forall q bs i, 0 <= i ->
Z.testbit (lez (firstn q bs)) i = if i <? 8 * Z.of_nat q then Z.testbit (lez bs) i else false.
Proof.
induction q as [|q IH]; intros bs i Hi.
- cbn [firstn lez]. rewrite Z.bits_0. destruct (Z.ltb_spec i (8 * Z.of_nat 0)); [lia|reflexivity].
- destruct bs as [|b bs].
+ cbn [firstn lez]. rewrite !Z.bits_0. destruct (i <? _); reflexivity.
+ cbn [firstn]. rewrite !lez_cons, !Z.lor_spec, !Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 8) as [H8|H8].
* rewrite !(Z.testbit_neg_r _ (i - 8)) by lia.
destruct (Z.ltb_spec i (8 * Z.of_nat (S q))); [reflexivity|lia].
* rewrite IH by lia.
destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (S q))); try lia; try reflexivity.
pose proof (u8_range b). rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma testbit_lez_app : forall xs ys i, 0 <= i ->
Z.testbit (lez (xs ++ ys)) i =
if i <? 8 * Z.of_nat (length xs) then Z.testbit (lez xs) i else Z.testbit (lez ys) (i - 8 * Z.of_nat (length xs)).
Proof.
intros xs ys i Hi. rewrite bytes_le_app, Z.lor_spec, Z.shiftl_spec by lia.
destruct (Z.ltb_spec i (8 * Z.of_nat (length xs))).
- rewrite (Z.testbit_neg_r (lez ys)) by lia. apply orb_false_r.
- rewrite testbit_lez_high by lia. reflexivity.
Qed.

#[using="Type"] Lemma Z_to_le_bytes_lez : forall bs, Z_to_le_bytes (length bs) (lez bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes].
replace (Z.shiftr (lez (b :: bs)) 8) with (lez bs).
2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
pose proof (testbit_lez_skipn 1 (b :: bs) i Hi) as E. change (skipn 1 (b :: bs)) with bs in E.
rewrite E. reflexivity. }
rewrite IH. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned.
apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
destruct (Z.lt_ge_cases i 8).
- rewrite bv_wrap_spec_low by lia. rewrite lez_cons, Z.lor_spec, Z.shiftl_spec by lia.
rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
- rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

#[using="Type"] Lemma word_to_le_bytes_4_eq : forall (v : word) (l : list byte),
length l = 4%nat ->
(forall i, 0 <= i < 32 -> Z.testbit (bv_unsigned v) i = Z.testbit (lez l) i) ->
word_to_le_bytes 4 v = l.
Proof.
intros v l Hl Hb. unfold word_to_le_bytes.
rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 32).
- rewrite bv_wrap_spec_low by lia. apply Hb. lia.
- rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.

#[using="Type"] Lemma sw_bytes_LWv : forall l, length l = 4%nat -> word_to_le_bytes 4 (LWv l) = l.
Proof.
intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.

Definition LBv (b : byte) : word := Z_to_bv 64 (bv_unsigned b).

#[using="Type"] Lemma sb_byte_LBv : forall b : byte, Z_to_bv 8 (bv_unsigned (LBv b)) = b.
Proof.
intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

#[using="Type"] Lemma sb_byte_eq : forall (v : word) (b : byte),
(forall i, 0 <= i < 8 -> Z.testbit (bv_unsigned v) i = Z.testbit (bv_unsigned b) i) ->
Z_to_bv 8 (bv_unsigned v) = b.
Proof.
intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
destruct (Z.lt_ge_cases i 8).
- rewrite bv_wrap_spec_low by lia. apply Hb. lia.
- rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

#[using="Type"] Lemma testbit_nth_lez : forall l q i, 0 <= i < 8 -> (q < length l)%nat ->
Z.testbit (bv_unsigned (nth q l (Z_to_bv 8 0))) i = Z.testbit (lez l) (i + 8 * Z.of_nat q).
Proof.
intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
revert l Hq. induction q as [|q IH]; intros l Hq.
- destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
- destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.

#[using="Type"] Lemma sb_byte_srli_LWv : forall l q, length l = 4%nat -> (q <= 3)%nat ->
Z_to_bv 8 (bv_unsigned (v_srli (LWv l) (8 * Z.of_nat q))) = nth q l (Z_to_bv 8 0).
Proof.
intros l q H Hq. apply sb_byte_eq. intros i Hi.
unfold v_srli. rewrite Z_to_bv_unsigned, bv_wrap_spec_low, Z.shiftr_spec by lia.
rewrite testbit_u_LWv by (try exact H; lia).
rewrite testbit_nth_lez by (try rewrite H; lia). reflexivity.
Qed.

#[using="Type"] Lemma testbit_u_srliw_LWv : forall l s i, length l = 4%nat -> 1 <= s -> 0 <= i ->
Z.testbit (bv_unsigned (v_srliw (LWv l) s)) i = if i + s <? 32 then Z.testbit (lez l) (i + s) else false.
Proof.
intros l s i H Hs Hi. unfold v_srliw. rewrite Z_to_bv_unsigned.
assert (Sh : forall j, 0 <= j -> Z.testbit (Z.shiftr (bv_wrap 32 (bv_unsigned (LWv l))) s) j
= if j + s <? 32 then Z.testbit (lez l) (j + s) else false).
{ intros j Hj. rewrite Z.shiftr_spec by lia.
destruct (Z.ltb_spec (j + s) 32).
- rewrite bv_wrap_spec_low by lia. apply testbit_u_LWv; [exact H|lia].
- apply bv_wrap_spec_high. lia. }
destruct (Z.lt_ge_cases i 64).
- rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
case_bool_decide.
+ apply Sh. lia.
+ rewrite Sh by lia.
destruct (Z.ltb_spec (Z.of_N 32 - 1 + s) 32), (Z.ltb_spec (i + s) 32); try lia; reflexivity.
- rewrite bv_wrap_spec_high by lia. destruct (Z.ltb_spec (i + s) 32); [lia|reflexivity].
Qed.

#[using="Type"] Lemma testbit_u_slli_LWv : forall l s i, length l = 4%nat -> 0 <= s -> 0 <= i < 32 ->
Z.testbit (bv_unsigned (v_slli (LWv l) s)) i = if i <? s then false else Z.testbit (lez l) (i - s).
Proof.
intros l s i H Hs Hi. unfold v_slli. rewrite Z_to_bv_unsigned.
rewrite bv_wrap_spec_low by lia. rewrite Z.shiftl_spec by lia.
destruct (Z.ltb_spec i s).
- apply Z.testbit_neg_r. lia.
- apply testbit_u_LWv; [exact H|lia].
Qed.

#[using="Type"] Lemma testbit_u_vor : forall (x y : word) i, 0 <= i ->
Z.testbit (bv_unsigned (v_or x y)) i = Z.testbit (bv_unsigned x) i || Z.testbit (bv_unsigned y) i.
Proof.
intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
destruct (Z.lt_ge_cases i 64).
- rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
- rewrite bv_wrap_spec_high by lia.
pose proof (u64_range x). pose proof (u64_range y).
rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma sw_bytes_merge : forall l1 l2 (q : nat) (v : word),
length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
v = v_or (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) (v_srliw (LWv l1) (8 * Z.of_nat q)) ->
word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
intros l1 l2 q v H1 H2 Hq ->.
apply word_to_le_bytes_4_eq.
{ rewrite length_app, length_skipn, length_firstn, H1, H2. lia. }
intros i Hi.
rewrite testbit_u_vor by lia.
rewrite testbit_u_slli_LWv by (try exact H2; lia).
rewrite testbit_u_srliw_LWv by (try exact H1; lia).
rewrite testbit_lez_app by lia. rewrite length_skipn, H1.
rewrite testbit_lez_skipn by lia.
destruct (Z.ltb_spec i (32 - 8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (4 - q))),
(Z.ltb_spec (i + 8 * Z.of_nat q) 32); try lia.
- reflexivity.
- rewrite testbit_lez_firstn by lia.
destruct (Z.ltb_spec (i - 8 * Z.of_nat (4 - q)) (8 * Z.of_nat q)); [|lia].
rewrite orb_false_r. f_equal. lia.
Qed.

#[using="Type"] Lemma sw_bytes_merge' : forall l1 l2 (q : nat) (v : word),
length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
v = v_or (v_srliw (LWv l1) (8 * Z.of_nat q)) (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) ->
word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
intros l1 l2 q v H1 H2 Hq ->. apply (sw_bytes_merge l1 l2 q); try assumption.
unfold v_or. f_equal. apply Z.lor_comm.
Qed.

#[using="Type"] Lemma store_ok_at : forall segs m (dst : word) (N : nat) bsw j k,
bv_unsigned dst + Z.of_nat N <= 2 ^ 64 ->
store_ok segs m dst N = true ->
0 <= j -> j + Z.of_nat k <= Z.of_nat N ->
store_ok segs (wbytes m dst bsw) (at_ dst j) k = true.
Proof.
intros segs m dst N bsw j k Hnw Hok Hj Hk.
destruct k as [|k]; [reflexivity|].
pose proof (u64_range dst).
apply (store_ok_mono segs (S k) m); [apply wbytes_grows|].
apply (store_ok_sub segs m dst (at_ dst j) N (S k) Hnw Hok); rewrite at_u; lia.
Qed.

Definition callee_kept : list reg :=
[1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, In r callee_kept -> getr regs' r = getr regs r.

#[using="Type"] Lemma keeps_refl : forall regs, keeps regs regs.
Proof. intros regs r _. reflexivity. Qed.

#[using="Type"] Lemma keeps_trans : forall r1 r2 r3, keeps r1 r2 -> keeps r2 r3 -> keeps r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

#[using="Type"] Lemma keeps_upd : forall regs regs' (rd : reg) v,
keeps regs regs' -> ~ In rd callee_kept -> keeps regs (regupd regs' rd v).
Proof.
intros regs regs' rd v K Hn r Hr.
rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

#[using="Type"] Lemma keeps_getr : forall regs regs' (r : reg), keeps regs regs' -> In r callee_kept -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.

#[using="Type"] Lemma in_regs_dec : forall (r : reg) (l : list reg),
existsb (fun x => bv_eqb x r) l = true -> In r l.
Proof.
intros r l H. apply existsb_exists in H as (x & Hx & E).
unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst x. exact Hx.
Qed.
#[using="Type"] Lemma not_in_regs_dec : forall (r : reg) (l : list reg),
forallb (fun x => negb (bv_eqb x r)) l = true -> ~ In r l.
Proof.
intros r l H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as H'. cbn beta in H'.
rewrite bv_eqb_refl in H'. discriminate H'.
Qed.
End FPGEN2.

Ltac kept_reg := first [ apply in_regs_dec; reflexivity | cbv [callee_kept In]; intuition congruence ].
Section FPGEN3.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Example keeps_sp_example : forall regs regs', keeps regs regs' -> getr regs' 2 = getr regs 2.
Proof. intros regs regs' K. apply (keeps_getr _ _ 2 K). kept_reg. Qed.
End FPGEN3.

Ltac not_kept := first [ apply not_in_regs_dec; reflexivity | cbv; intuition discriminate ].

Ltac solve_keeps :=
repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Section FPGEN4.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma runs_trans : forall segs (s0 : machine_state)
(st1 : bvmap 5 word -> machine_state) (P1 : bvmap 5 word -> Prop)
(st2 : bvmap 5 word -> machine_state) (P2 : bvmap 5 word -> Prop),
(exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
(forall r1, P1 r1 -> exists r2, msteps segs (st1 r1) (st2 r2) /\ P2 r2) ->
exists r2, msteps segs s0 (st2 r2) /\ P2 r2.
Proof.
intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
destruct (K r1 H1) as (r2 & R2 & H2).
exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

Definition callee_saved : list reg :=
[1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps_cs (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, In r callee_saved -> getr regs' r = getr regs r.

#[using="Type"] Lemma keeps_cs_refl : forall regs, keeps_cs regs regs.
Proof. intros regs r _. reflexivity. Qed.

#[using="Type"] Lemma keeps_cs_trans : forall r1 r2 r3, keeps_cs r1 r2 -> keeps_cs r2 r3 -> keeps_cs r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

#[using="Type"] Lemma keeps_cs_upd : forall regs regs' (rd : reg) v,
keeps_cs regs regs' -> ~ In rd callee_saved -> keeps_cs regs (regupd regs' rd v).
Proof.
intros regs regs' rd v K Hn r Hr.
rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

#[using="Type"] Lemma keeps_cs_upd_same : forall regs regs' (rd : reg) v,
keeps_cs regs regs' -> getr regs rd = v -> rd <> 0%bv -> keeps_cs regs (regupd regs' rd v).
Proof.
intros regs regs' rd v K Hv Hnz r Hr.
destruct (decide (r = rd)) as [->|Hne].
- rewrite getr_same by exact Hnz. symmetry. exact Hv.
- rewrite getr_other by exact Hne. apply K, Hr.
Qed.

#[using="Type"] Lemma keeps_keeps_cs : forall regs regs', keeps regs regs' -> keeps_cs regs regs'.
Proof.
intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.

#[using="Type"] Lemma keeps_cs_getr : forall regs regs' (r : reg), keeps_cs regs regs' -> In r callee_saved -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.
End FPGEN4.

Ltac solve_keeps_cs :=
repeat (first [ apply keeps_cs_upd; [| not_kept]
| apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwNp Qpox QsV0 Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QwNp Qpox QsV0 QsRG Qn1e QRjH.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition halt_ev (m' : Model) (code : word) : event :=
match m_killed m' with
| Some sig => KillEv sig (m_fs m')
| None => ExitEv code (m_fs m')
end.

#[using="Type"] Lemma sstep_svc_inv : forall ms model x8 e st,
ms_svc_pending ms = Some x8 ->
sstep segs (mkCfg ms model) e st ->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
/\ ((exists model'', m_halted model' = None /\ e = evs
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
/\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
\/ (m_halted model' = None /\ e = []
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
/\ st = SError)
\/ (exists code, m_halted model' = Some code
/\ e = evs ++ [halt_ev model' code]
/\ st = SNext (mkCfg ms model'))))
\/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
intros ms model x8 e st Hsvc Hss.
inversion Hss; subst; try congruence.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split; [eassumption|].
left. eexists. repeat split; eauto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split; [eassumption|].
right. left. repeat split; auto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split; [eassumption|].
right. right. eexists. repeat split; eauto.
unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split; [eassumption|].
right. right.
match goal with Hk : m_killed ?mm = Some _ |- _ =>
destruct (m_halted mm) as [code|] eqn:Hhc;
[| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
end.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
right. repeat split; auto.
Qed.

#[using="Type"] Lemma sstep_cfg_svc_inv : forall ms model x8 e st,
ms_svc_pending ms = Some x8 ->
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms model) e st ->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
/\ ((exists model'', ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff
/\ m_halted model' = None /\ e = evs
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
/\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
\/ (~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff
/\ m_halted model' = None /\ e = []
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
/\ st = SError)
\/ (exists code, m_halted model' = Some code
/\ e = evs ++ [halt_ev model' code]
/\ st = SNext (mkCfg ms model'))))
\/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
intros ms model x8 e st Hsvc Hss.
inversion Hss; subst; try congruence.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split; [eassumption|].
left. eexists. repeat split; eauto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split; [eassumption|].
right. left. repeat split; auto.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split; [eassumption|].
right. right. eexists. repeat split; eauto.
unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split; [eassumption|].
right. right.
match goal with Hk : m_killed ?mm = Some _ |- _ =>
destruct (m_halted mm) as [code|] eqn:Hhc;
[| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
end.
-
match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
right. repeat split; auto.
Qed.

#[using="Type"] Lemma sstep_of_spec : forall ms model x8 eff m' evs,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hlazy.
apply (sstep_cfg_syscall segs (alloc_only_cfg false) ms model x8 eff m' m' evs Hh Hsvc Hc Hns Hh').
apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

#[using="Type"] Lemma not_spurious_sysno : forall i m eff,
~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
intros i m eff Hn (Hoff & _). unfold injected_family_off in Hoff.
destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|] eqn:E; [|discriminate Hoff].
destruct (ia_family a) eqn:F; cbn in Hoff; rewrite ?F in Hoff; try discriminate Hoff.
apply Hn. exact (alloc_family_dispatched _ a E F).
Qed.

#[using="Type"] Lemma det_not_spurious : forall i model eff0 m0 evs0,
(forall o, syscall_spec i model o <-> o = Ok eff0 m0 evs0) ->
~ spurious_refusal_cfg (alloc_only_cfg false) i model eff0.
Proof.
intros i model eff0 m0 evs0 Hchk (_ & Hr & (eff' & m' & evs' & Hs & Hr')).
apply Hchk in Hs. injection Hs as -> _ _. congruence.
Qed.

#[using="Type"] Lemma node_chk_ev : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
(forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
(forall i, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs i)) ->
node_ok segs (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns. split.
- intros i. apply (sstep_of_spec ms model x8); auto.
- intros e st Hss. apply sstep_cfg_sub in Hss.
destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
| (Hc & -> & ->)].
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
injection Hmat as <-. exists i. split; reflexivity.
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
+ exfalso. exact (Hnu Hc).
Qed.

#[using="Type"] Lemma node_chk : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) [])) ->
(forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
(~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
(forall i, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs i)) ->
node_ok segs (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns.
apply (node_chk_ev ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

#[using="Type"] Lemma node_family : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
(R : outcome SyscallEffect -> Prop),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
(forall i, R (Ok (effs i) (ms' i) (evs i))) ->
(forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
(forall i, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs i)) ->
node_ok segs (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hh' Hlazy Hns.
apply (node_chk_ev ms model x8 I effs ms' evs Hh Hsvc).
- intros i. apply HR. apply Hin.
- intros eff m' ev Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi).
apply Ok_inj in Hi as (-> & -> & ->). exists i. auto.
- intros Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
- exact Hh'.
- exact Hlazy.
- exact Hns.
Qed.

#[using="Type"] Lemma node_family_ns : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
node_ok segs (mkCfg ms model)
{i : I | ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs i)}
(fun i => evs (proj1_sig i))
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs (proj1_sig i)))) (ms' (proj1_sig i))).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hchk Hh' Hlazy. split.
- intros [i Hi]. cbn [proj1_sig]. apply (sstep_of_spec ms model x8); auto.
apply Hchk. exists i. reflexivity.
- intros e st Hss.
destruct (sstep_cfg_svc_inv ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(m'' & Hns & Hh2 & -> & Hmat & ->) | [(Hns & Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
| (Hc & -> & ->)].
+ apply Hchk in Hc as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->).
rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
injection Hmat as <-. exists (exist _ i Hns). split; reflexivity.
+ apply Hchk in Hc as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->).
rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
+ apply Hchk in Hc as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->). rewrite Hh' in Hh2. discriminate.
+ exfalso. apply Hchk in Hc as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
Qed.

#[using="Type"] Lemma node_det : forall ms model x8 eff0 m0 evs0,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0) ->
m_halted m0 = None ->
m_vm_lazy m0 = [] ->
node_ok segs (mkCfg ms model) unit (fun _ => evs0)
(fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hh0 Hlazy0.
apply (node_family ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
(fun o => o = Ok eff0 m0 evs0) Hh Hsvc Hchk).
- intros []. reflexivity.
- intros o ->. exists tt. reflexivity.
- intros []; exact Hh0.
- intros []; exact Hlazy0.
- intros []. exact (det_not_spurious _ _ _ _ _ Hchk).
Qed.

#[using="Type"] Lemma node_ret_only : forall ms model x8 r m' evs,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' evs) ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
node_ok segs (mkCfg ms model) unit (fun _ => evs)
(fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
rewrite <- (apply_effect_no_write ms r).
apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc Hchk Hh' Hlazy).
Qed.

#[using="Type"] Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o
<-> o = Ok (with_copyins reads (mkEffect r [] [])) m' evs) ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
node_ok segs (mkCfg ms model) unit (fun _ => evs)
(fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
rewrite <- (apply_effect_copyins_no_write ms r reads).
apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc Hchk Hh' Hlazy).
Qed.

#[using="Type"] Lemma rz_ret_only : forall ms model x8 r m' evs T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' evs) ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
intros ms model x8 r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply rz_emit1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_ret_only_copyins : forall ms model x8 reads r m' evs T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o
<-> o = Ok (with_copyins reads (mkEffect r [] [])) m' evs) ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
intros ms model x8 reads r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply rz_emit1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_ret_only_silent : forall ms model x8 r m' T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' []) ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
realizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply rz_silent1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o
<-> o = Ok (with_copyins reads (mkEffect r [] [])) m' []) ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
realizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_det : forall ms model x8 eff0 m0 T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 []) ->
m_halted m0 = None ->
m_vm_lazy m0 = [] ->
realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
realizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hh0 Hlazy0 Hc.
eapply rz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I (fun _ => []) nx ->
(forall i, realizes segs (nx i) (T i)) ->
realizes segs c (t_alt T).
Proof.
intros c I nx T i0 Hnode Hc.
apply (rz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
- apply (rz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
- intros tr. split.
+ intros [i Hi]. exists i.
exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
+ intros [i Hi]. exists i.
exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

#[using="Type"] Lemma rz_exit_chk : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
realizes segs (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros. eapply rz_exit; eassumption. Qed.

Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
(i : open_I model) : config :=
match i with
| inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
| inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
(mk (alloc_fd (m_fds model)))
end.

#[using="Type"] Lemma node_open : forall ms model x8 reads (mk : word -> Model),
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
~ In (bv_unsigned x8) alloc_mark_sysnos ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> open_out reads model mk o) ->
(forall fd, m_halted (mk fd) = None) ->
(forall fd, m_vm_lazy (mk fd) = []) ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
intros ms model x8 reads mk Hh Hlazy Hsvc Hna Hchk Hmk Hmklazy Hfree.
assert (Hns : forall i, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model i)
by (intros i; apply not_spurious_sysno; rewrite in_sysno_sys_input; exact Hna).
pose (effs := fun i : open_I model => match i with
| inl (exist _ e _) => with_copyins reads (mkEffect (errno_ret e) [] [])
| inr _ => with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] []) end).
pose (ms' := fun i : open_I model => match i with
| inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end).
assert (Enx : forall i, open_nx ms model mk i
= mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
{ intros [[e He] | []]; cbn [open_nx effs ms']; rewrite apply_effect_copyins_no_write; reflexivity. }
split.
- intros i. rewrite Enx.
apply (proj1 (node_family ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hchk
ltac:(intros [[e He] | []]; [left; exists e; auto | right; auto])
ltac:(intros o [(e & He & ->) | (Hlk & ->)];
[exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity)
ltac:(intros [[e He] | []]; [exact Hh | apply Hmk])
ltac:(intros [[e He] | []]; [exact Hlazy | apply Hmklazy]) (fun i => Hns _)) i).
- intros e st Hss.
destruct (proj2 (node_family ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hchk
ltac:(intros [[er Her] | []]; [left; exists er; auto | right; auto])
ltac:(intros o [(er & Her & ->) | (Hlk & ->)];
[exists (inl (exist _ er Her)) | exists (inr tt)]; reflexivity)
ltac:(intros [[er Her] | []]; [exact Hh | apply Hmk])
ltac:(intros [[er Her] | []]; [exact Hlazy | apply Hmklazy]) (fun i => Hns _)) e st Hss)
as (i & -> & ->).
exists i. rewrite Enx. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_open : forall ms model x8 reads (mk : word -> Model) A B,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 ->
~ In (bv_unsigned x8) alloc_mark_sysnos ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> open_out reads model mk o) ->
(forall fd, m_halted (mk fd) = None) ->
(forall fd, m_vm_lazy (mk fd) = []) ->
fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
(forall e, In e openat_errnos ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
(mk (alloc_fd (m_fds model)))) B ->
realizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
intros ms model x8 reads mk A B Hh Hlazy Hsvc Hna Hchk Hmk Hmklazy Hfree HA HB.
apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
(open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
- eapply node_open; eassumption.
- intros [e He]. cbn [open_nx]. apply HA. exact He.
- intros []. cbn [open_nx]. exact HB.
Qed.

End WithSegs.
End Mq4.
From Stdlib Require String Ascii.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State.
Import QRjH.
Import ListNotations.
Open Scope bv_scope.

Definition s2b (s : string) : list byte :=
map (fun a => Z_to_bv 8 (Z.of_nat (nat_of_ascii a))) (list_ascii_of_string s).

Definition W (ch : Z) (s : list byte) : list event := map (WriteEv (Z_to_bv 64 ch)) s.

Definition exit_code (z : Z) : word := Z_to_bv 64 z.

Definition t_die (msg : list byte) (fs : Fs.Fs) : TSet :=
t_emit (W 2 msg) (t_exit (exit_code 2) fs).

Definition msg_usage (argv0 : list byte) : list byte :=
s2b "usage: " ++ argv0 ++ s2b " INPUT" ++ [Z_to_bv 8 10].
Definition msg_cannot_open (path : list byte) : list byte :=
s2b "cli: cannot open " ++ path ++ [Z_to_bv 8 10].
Definition msg_read_error (path : list byte) : list byte :=
s2b "cli: read error on " ++ path ++ [Z_to_bv 8 10].
Definition msg_oom : list byte := s2b "cli: out of memory" ++ [Z_to_bv 8 10].
Definition msg_refused : list byte :=
s2b "cli: input >= 67108864 bytes, refused" ++ [Z_to_bv 8 10].
Definition msg_short : list byte :=
s2b "cli: input shorter than header" ++ [Z_to_bv 8 10].
Definition msg_overrun : list byte :=
s2b "cli: config_len overruns input" ++ [Z_to_bv 8 10].

Fixpoint zero_lines (calls : nat) : list byte :=
match calls with
| O => []
| S k => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zero_lines k
end.

Definition MAX_INPUT : Z := 67108864%Z.

Definition t_body (data : list byte) (fs : Fs.Fs) : TSet :=
let len := length data in
if (MAX_INPUT <=? Z.of_nat len)%Z then t_die msg_refused fs
else if (len <? 6)%nat then t_die msg_short fs
else
let b0 := bv_unsigned (nth 0 data (Z_to_bv 8 0)) in
let b1 := bv_unsigned (nth 1 data (Z_to_bv 8 0)) in
let b2 := bv_unsigned (nth 2 data (Z_to_bv 8 0)) in
let cfg := (b0 + 256 * b1)%Z in
let config_len := Z.to_nat (cfg mod 32768) in
let counting := (32768 <=? cfg)%Z in
if (len <? 6 + config_len)%nat then t_die msg_overrun fs
else
let payload_len := (len - 6 - config_len)%nat in
let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
let succ := t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs) in

match payload_len with
| O => succ
| _ => succ
end.

Definition t_opened (data : list byte) (fs : Fs.Fs) : TSet :=
t_body data fs.

Definition t_opened_dir (path : list byte) (fs : Fs.Fs) : TSet :=
t_die (msg_read_error path) fs.

Definition dot_path : list byte := [Z_to_bv 8 46].

Fixpoint list_byte_eqb (p q : list byte) : bool :=
match p, q with
| [], [] => true
| a :: p', b :: q' => bv_eqb a b && list_byte_eqb p' q'
| _, _ => false
end.

Definition spec (argv : list (list byte)) (fs0 : Fs.Fs) : TSet :=
match argv with
| [_; path] =>
if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0
else if list_byte_eqb path [] then t_die (msg_cannot_open path) fs0
else if list_byte_eqb path dot_path then
t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened_dir path fs0)
else match fs_lookup fs0 path with
| None => t_die (msg_cannot_open path) fs0
| Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)
end
| _ => t_die (msg_usage (hd [] argv)) fs0
end.
End Mq5.

Module Mq6.

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsRG.Mq0 Qnhz.Mq0 Qrxj QEVk.Mq0 QRjH.Mq0.

Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma rdn_skipn : forall segs mem n (a : word) bs off k,
rdn segs mem a n = Some bs -> (off + k <= n)%nat ->
rdn segs mem (a + nat_to_word off) k = Some (firstn k (skipn off bs)).
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs off k H Hk.
- assert (off = 0%nat) by lia. assert (k = 0%nat) by lia. subst.
rewrite word_add_0. cbn in H |- *. injection H as <-. reflexivity.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct off as [|off].
+ rewrite word_add_0. cbn [skipn].
eapply rdn_firstn; [|exact Hk].
cbn [rdn]. rewrite Eb, Er. reflexivity.
+ cbn [skipn].
replace (a + nat_to_word (S off)) with (a + 1 + nat_to_word off)
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply (IH (a+1) rest off k Er). lia.
Qed.

#[using="Type"] Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
cbn. apply app_nil_r.
Qed.

#[using="Type"] Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
intros A l1 l2 n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

#[using="Type"] Lemma skipn_repeat' : forall {A} (x : A) off n,
skipn off (repeat x n) = repeat x (n - off).
Proof.
intros A x off. induction off as [|off IH]; intros n.
- cbn. rewrite Nat.sub_0_r. reflexivity.
- destruct n as [|n]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. f_equal.
Qed.

#[using="Type"] Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat ->
firstn k (repeat x n) = repeat x k.
Proof.
intros A x k. induction k as [|k IH]; intros n H; [reflexivity|].
destruct n as [|n]; [lia|]. cbn [repeat firstn]. rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma repeat_firstn_skipn : forall {A} (x : A) n off k,
(off + k <= n)%nat -> firstn k (skipn off (repeat x n)) = repeat x k.
Proof.
intros A x n off k H.
rewrite skipn_repeat', firstn_repeat' by lia. reflexivity.
Qed.

Definition cat_envp_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
nth k (fst (string_addrs (cat_env_base sp av ev) ev)) (Z_to_bv 64 0).

Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
(8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.

Definition auxv_words (ph : PhdrInfo) (rnd uid hw : word) : list word :=
flat_map (fun e => [fst e; snd e]) (auxv_entries ph rnd uid hw).

#[using="Type"] Lemma build_auxv_words : forall entries,
build_auxv entries = flat_map word_le8 (flat_map (fun e => [fst e; snd e]) entries).
Proof.
induction entries as [|[t v] es IH]; [reflexivity|].
cbn [build_auxv flat_map fst snd app].
change (build_auxv es) with
(flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
rewrite IH, <- app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma auxv_bytes_words : forall ph rnd uid hw,
auxv_bytes ph rnd uid hw = flat_map word_le8 (auxv_words ph rnd uid hw).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

#[using="Type"] Lemma length_auxv_words : forall ph rnd uid hw, length (auxv_words ph rnd uid hw) = 20%nat.
Proof. reflexivity. Qed.

Section Layout.

Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.

Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

Let bsb := build_stack_bytes ph sp av ev uid hw rdraw.

Let stk := stack_to_mem sp (entry_stack_image ph sp av ev uid hw rdraw).

#[using="Hva Hve Hsp_hi"] Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
Proof. exact (bsb_nw ph sp av ev uid hw rdraw Hva Hve Hsp_hi). Qed.

#[using="Hva"] Lemma lay_len_av : (1 <= length av <= 1024)%nat.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

#[using="Hve"] Lemma lay_len_ev : (length ev <= 256)%nat.
Proof. destruct Hve as [H1 _]. lia. Qed.

#[using="Type"] Lemma bsb_decomp : exists strs_tail,
bsb = (word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
++ word_le8 (Z_to_bv 64 0)
++ flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))
++ word_le8 (Z_to_bv 64 0)
++ auxv_bytes ph (at_random_ptr sp av ev) uid hw
++ strs_tail.
Proof.
unfold bsb, build_stack_bytes, cat_env_base, cat_string_base, cat_struct_size.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma len_argc_argv :
length (word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av)))
= (8 + 8 * length av)%nat.
Proof.
rewrite length_app, length_n_to_le_8, length_flat_map_le8, length_string_addrs_fst. lia.
Qed.

#[using="Type"] Lemma len_envp_ptrs :
length (flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))) = (8 * length ev)%nat.
Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.

#[using="Hva Hve Hsp_hi bsb"] Lemma read_argv_null :
rdn segs stk (sp + nat_to_word (8 + 8 * length av)) 8%nat = Some (word_le8 (Z_to_bv 64 0)).
Proof.
destruct bsb_decomp as [tl E].
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
(length_n_to_le_8 _) lay_bsb_nw) as H.
rewrite len_argc_argv in H. exact H.
Qed.

#[using="Hva Hve Hsp_hi bsb"] Lemma read_envp_ptr_k : forall k, (k < length ev)%nat ->
rdn segs stk (sp + nat_to_word (envp_off av + 8 * k)) 8%nat
= Some (word_le8 (cat_envp_ptr sp av ev k)).
Proof.
intros k Hk.
destruct bsb_decomp as [tl E].
assert (Hk' : (k < length (fst (string_addrs (cat_env_base sp av ev) ev)))%nat)
by (rewrite length_string_addrs_fst; exact Hk).
rewrite (flat_map_le8_decomp _ k Hk') in E.
rewrite <- !app_assoc in E.
match type of E with
| bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 8%nat) as H
end.
rewrite <- !app_assoc in H.
specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
rewrite !length_app in H.
rewrite !length_flat_map_le8 in H.
rewrite length_string_addrs_fst in H.
rewrite firstn_length_le in H by (rewrite length_string_addrs_fst; lia).
rewrite !length_n_to_le_8 in H.
unfold envp_off, cat_envp_ptr.
replace (8 + 8 * (length av + 1) + 8 * k)%nat with (8 + (8 * length av + (8 + 8 * k)))%nat by lia.
exact H.
Qed.

#[using="Hva Hve Hsp_hi bsb"] Lemma read_envp_null :
rdn segs stk (sp + nat_to_word (envp_off av + 8 * length ev)) 8%nat
= Some (word_le8 (Z_to_bv 64 0)).
Proof.
destruct bsb_decomp as [tl E].
match type of E with
| bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?mid ++ ?rest =>
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3) mid rest 8%nat) as H
end.
rewrite <- !app_assoc in H.
specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
rewrite !length_app in H. rewrite len_envp_ptrs in H.
rewrite !length_n_to_le_8 in H.
rewrite length_flat_map_le8, length_string_addrs_fst in H.
unfold envp_off.
match type of H with
| rdn _ _ (sp + nat_to_word ?n) 8 = _ =>
replace (8 + 8 * (length av + 1) + 8 * length ev)%nat with n by lia
end.
exact H.
Qed.

#[using="Hva Hve Hsp_hi bsb"] Lemma read_auxv_all :
rdn segs stk (sp + nat_to_word (auxv_off av ev)) 160%nat
= Some (auxv_bytes ph (at_random_ptr sp av ev) uid hw).
Proof.
destruct bsb_decomp as [tl E].
match type of E with
| bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 160%nat) as H
end.
rewrite <- !app_assoc in H.
specialize (H E (length_auxv_bytes _ _ _ _) lay_bsb_nw).
rewrite !length_app in H. rewrite len_envp_ptrs in H.
rewrite !length_n_to_le_8 in H.
rewrite length_flat_map_le8, length_string_addrs_fst in H.
unfold auxv_off.
match type of H with
| rdn _ _ (sp + nat_to_word ?n) _ = _ =>
replace (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat with n by lia
end.
exact H.
Qed.

#[using="Hva Hve Hsp_hi bsb"] Lemma read_auxv_word : forall j, (j < 20)%nat ->
rdn segs stk (sp + nat_to_word (auxv_off av ev + 8 * j)) 8%nat
= Some (word_le8 (nth j (auxv_words ph (at_random_ptr sp av ev) uid hw) (Z_to_bv 64 0))).
Proof.
intros j Hj.
rewrite <- nat_to_word_add_merge.
rewrite (rdn_skipn segs stk 160 _ _ (8 * j) 8 read_auxv_all) by lia.
f_equal. rewrite auxv_bytes_words.
rewrite (flat_map_le8_decomp _ j) by (rewrite length_auxv_words; exact Hj).
rewrite skipn_app_exact
by (rewrite length_flat_map_le8, firstn_length_le by (rewrite length_auxv_words; lia); lia).
apply firstn_app_exact. apply length_n_to_le_8.
Qed.

#[using="Type"] Lemma bsb_random_split : exists pre,
bsb = pre ++ at_random_bytes (ed_random rdraw)
/\ at_random_ptr sp av ev = sp + nat_to_word (length pre)
/\ (Z.of_nat (length pre) mod 8 = 0)%Z.
Proof.
unfold bsb, build_stack_bytes, at_random_ptr.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota zeta.
match goal with
| |- exists pre, ?raw ++ repeat ?z ?pd ++ at_random_bytes (ed_random rdraw) = _ /\ _ /\ _ =>
exists (raw ++ repeat z pd)
end.
split; [rewrite <- !app_assoc; reflexivity|].
rewrite !length_app, !repeat_length, !length_flat_map_le8, !length_string_addrs_fst,
!length_n_to_le_8, length_auxv_bytes, !length_flatten_strings.
unfold auxv_size.
match goal with
| |- _ /\ (Z.of_nat (?L' + _) mod 8 = 0)%Z => set (L := L')
end.
replace (8 + (length av + 1) * 8 + (length ev + 1) * 8 + 160
+ total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat with L by lia.
assert (Hpd : (0 <= (8 - Z.of_nat L mod 8) mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
split; [reflexivity|].
rewrite Nat2Z.inj_add, Z2Nat.id by lia.
rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
replace (Z.of_nat L mod 8 + (8 - Z.of_nat L mod 8))%Z with 8%Z by lia.
reflexivity.
Qed.

#[using="Hva Hve Hsp_hi"] Lemma at_random_off : exists off : nat,
at_random_ptr sp av ev = sp + nat_to_word off
/\ (off + 16 = length bsb)%nat
/\ (Z.of_nat off mod 8 = 0)%Z
/\ forall j n, (j + n <= 16)%nat ->
rdn segs stk (at_random_ptr sp av ev + nat_to_word j) n
= Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
Proof.
destruct bsb_random_split as [pre [E [Hp Hmod]]].
pose proof (length_at_random_bytes (ed_random rdraw)) as HL.
exists (length pre). split; [exact Hp|]. split.
{ unfold bsb in E |- *. rewrite E, length_app, HL. reflexivity. }
split; [exact Hmod|].
intros j n Hjn. rewrite Hp, nat_to_word_add_merge.
rewrite <- (firstn_skipn j (at_random_bytes (ed_random rdraw))) in E.
rewrite app_assoc in E.
rewrite <- (firstn_skipn n (skipn j (at_random_bytes (ed_random rdraw)))) in E.
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
(firstn n (skipn j (at_random_bytes (ed_random rdraw))))
(skipn n (skipn j (at_random_bytes (ed_random rdraw)))) n E) as H.
assert (Hlen : length (pre ++ firstn j (at_random_bytes (ed_random rdraw))) = (length pre + j)%nat).
{ rewrite length_app, firstn_length_le by lia. reflexivity. }
rewrite Hlen in H.
apply H; [rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia] | exact lay_bsb_nw].
Qed.

#[using="Hva Hve"] Lemma lay_bsb_len : (Z.of_nat (length bsb) <= 2240000)%Z.
Proof. exact (bsb_bound ph sp av ev uid hw rdraw Hva Hve). Qed.

#[using="Type"] Lemma auxv_off_bound : (auxv_off av ev + 160 + 16 <= length bsb)%nat.
Proof.
unfold bsb, build_stack_bytes. cbv zeta.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
rewrite !length_app, length_at_random_bytes, !repeat_length, !length_flat_map_le8,
!length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
!length_flatten_strings.
unfold auxv_size, auxv_off. lia.
Qed.

#[using="Type"] Lemma cat_envp_ptr_eq : forall k, (k < length ev)%nat ->
cat_envp_ptr sp av ev k
= sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat av
+ total_arg_bytes_nat (firstn k ev)).
Proof.
intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
unfold cat_env_base, cat_string_base. rewrite !nat_to_word_add_merge.
rewrite Nat.add_assoc. reflexivity.
Qed.

#[using="Hve"] Lemma total_firstn_ev_bound : forall k,
(Z.of_nat (total_arg_bytes_nat (firstn k ev)) <= 131072)%Z.
Proof.
intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
pose proof (total_arg_bytes_firstn_le k ev). lia.
Qed.

#[using="Hva Hve"] Lemma struct_av_bound :
(Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av) <= 2107576)%Z.
Proof.
destruct Hva as [[Hl0 Hl] [Hta _]]. destruct Hve as [Hle _].
rewrite total_arg_bytes_Z in Hta. unfold cat_struct_size, auxv_size. lia.
Qed.

#[using="Hva Hve Hsp_lo Hsp_hi"] Lemma u_cat_envp_ptr : forall k, (k < length ev)%nat ->
bv_unsigned (cat_envp_ptr sp av ev k)
= (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av
+ total_arg_bytes_nat (firstn k ev)))%Z.
Proof.
intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
pose proof struct_av_bound. pose proof (total_firstn_ev_bound k).
unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
apply u_Z2bv; lia.
Qed.

#[using="Hva Hve Hsp_lo Hsp_hi"] Lemma cat_envp_ptr_nz : forall k, (k < length ev)%nat ->
bv_unsigned (cat_envp_ptr sp av ev k) <> 0%Z.
Proof.
intros k Hk. rewrite u_cat_envp_ptr by exact Hk. unfold sp_window_lo in Hsp_lo. lia.
Qed.

#[using="Hva Hve Hsp_lo Hsp_hi"] Lemma u_cat_argv_ptr : forall k, (k < length av)%nat ->
bv_unsigned (cat_argv_ptr sp av ev k)
= (bv_unsigned sp + Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat (firstn k av)))%Z.
Proof.
intros k Hk. rewrite cat_argv_ptr_offset by exact Hk. unfold cat_string_base.
rewrite nat_to_word_add_merge, word_add_nat.
pose proof struct_av_bound. pose proof (total_arg_bytes_firstn_le k av).
unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
apply u_Z2bv; lia.
Qed.

#[using="Hva"] Lemma argv_str_len : forall k, (k < length av)%nat ->
(Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof. intros k Hk. exact (valid_argv_str_len av k Hva Hk). Qed.

#[using="Type"] Lemma auxv_words_eq : forall rnd,
auxv_words ph rnd uid hw =
[AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr ph)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent ph));
AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num ph)); AT_HWCAP; hw; AT_PAGESZ; Z_to_bv 64 4096;
AT_UID; uid; AT_EUID; uid; AT_SECURE; Z_to_bv 64 0;
AT_RANDOM; rnd; AT_NULL; Z_to_bv 64 0].
Proof. reflexivity. Qed.

#[using="Hva Hve Hsp_lo Hsp_hi"] Lemma rnd_facts : forall (Hal : (bv_unsigned sp mod 16 = 0)%Z),
(bv_unsigned sp <= bv_unsigned (at_random_ptr sp av ev))%Z
/\ (bv_unsigned (at_random_ptr sp av ev) + 16 <= bv_unsigned sp + Z.of_nat (length bsb))%Z
/\ (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z
/\ (bv_unsigned (at_random_ptr sp av ev) mod 8 = 0)%Z
/\ (forall j n, (j + n <= 16)%nat ->
rdn segs stk (Z_to_bv 64 (bv_unsigned (at_random_ptr sp av ev) + Z.of_nat j)) n
= Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
Proof.
intros Hal.
destruct at_random_off as [off [Hp [Hlen [Hmod Hrd]]]].
pose proof lay_bsb_nw as Hnw. pose proof lay_bsb_len as Hbl.
unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
assert (Hu : bv_unsigned (at_random_ptr sp av ev) = (bv_unsigned sp + Z.of_nat off)%Z).
{ rewrite Hp, word_add_nat. apply u_Z2bv; lia. }
rewrite Hu. split; [lia|]. split; [lia|]. split; [lia|]. split.
- rewrite Z.add_mod by lia.
replace (bv_unsigned sp mod 8)%Z with 0%Z.
2:{ symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
rewrite Hmod. reflexivity.
- intros j n Hjn. rewrite <- Hu. rewrite <- word_add_nat. apply Hrd. exact Hjn.
Qed.

End Layout.
End FPGEN1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma bytes_le_to_Z_4 : forall v : word, (bv_unsigned v < 2^32)%Z ->
bytes_le_to_Z (word_to_le_bytes 4 v) = bv_unsigned v.
Proof.
intros v Hv. rewrite bytes_le_N.
change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : forall z, (0 <= z < 2147483648)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia.
apply (bv_swrap_small 32). change (bv_half_modulus 32) with 2147483648%Z. lia.
Qed.

Lemma v_lw_m1 : v_lw (Z_to_bv 64 4294967295) = Z_to_bv 64 (-1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma c_eq_Z : forall a b : Z, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z ->
c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_eq_refl : forall x : word, c_eq x x = true.
Proof. intros x. unfold c_eq. apply bv_eqb_refl. Qed.

Ltac zlen :=
repeat match goal with
| |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
end;
cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
Ltac zsimp := zlen; u_norm. Ltac mkr__zsimp_1 := zlen; u_norm.

Ltac sok_stack SOK :=
store_ok_peel;
eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.

Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia_fast := first [ solve [ clear_disj; lia ] | lia ].

Lemma rdn_wbytes_out_Z : forall segs bs m (zb za : Z) n,
(0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
zb + Z.of_nat (length bs) <= 2^64 /\
(za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
intros segs bs m zb za n (Ha & Han & Hb & Hbn & Hd).
apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
Ltac rdn_peel1 :=
first [ rewrite rdn_wbytes_out_Z by (zlen; lia_fast)
| rewrite rdn_wbytes_out by (zsimp; lia_fast) ].
Ltac rdn_by H := repeat rdn_peel1; exact H.

Ltac rdn_hyp :=
match goal with
| H : rdn _ _ ?a ?n = Some _ |- rdn _ _ ?a ?n = Some _ => exact H
end.
Ltac rdn_solve :=
lazymatch goal with
| |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
else (rdn_peel1; rdn_solve)
| |- _ => rdn_hyp
end.

Ltac zbv_target x i :=
lazymatch x with
| Z_to_bv 64 (?a - ?b)%Z => let d := eval cbv in (b - i)%Z in constr:(Z_to_bv 64 (a - d))
| Z_to_bv 64 (?a + ?b)%Z => let d := eval cbv in (b + i)%Z in constr:(Z_to_bv 64 (a + d))
| Z_to_bv 64 ?a =>
lazymatch i with
| Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (a - d))
| _ => constr:(Z_to_bv 64 (a + i))
end
| _ =>
lazymatch i with
| Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (bv_unsigned x - d))
| _ => constr:(Z_to_bv 64 (bv_unsigned x + i))
end
end.

Ltac addr_norm :=
match goal with
| |- context [v_addi ?x ?i] =>
let e := constr:(v_addi x i) in
tryif check_closed_term e then wlit_closed e
else first
[ rewrite (v_addi_0 x)
| let t := zbv_target x i in
replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
| _ => idtac
end.

Ltac sp_renorm :=
match goal with
| |- context [regupd _ 2 (v_addi ?x ?i)] =>
let e := constr:(v_addi x i) in
first
[ rewrite (v_addi_0 x)
| let t := zbv_target x i in
replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
end.

Ltac getr_hyps :=
repeat match goal with
| H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H
end.
Ltac addr_tac := getr_hyps; unfold v_addi; u_norm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia].
Ltac val_tac := first [reflexivity | assumption | symmetry; assumption].

Ltac stepST F D aa vv oktac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Store SZ8 _ _ _, _) =>
eapply step_sd_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
| decode_any _ = Some (Store SZ4 _ _ _, _) =>
eapply step_sw_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
| decode_any _ = Some (Store SZ1 _ _ _, _) =>
eapply Qn1e.Mq1.step_sb_at with (a := aa) (v := vv);
[ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
| reflexivity | oktac ]
end
| step_simpl ].

Ltac stepLD F D bsv vv rdtac vtac :=
chain_step;
[ reflexivity
| lazymatch type of D with
| decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
| decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
| decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
end;
[ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
| step_simpl ]; vnorm.

Ltac stepLD8 F D vv := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).

Ltac stepLBU F D bb rdtac :=
chain_step;
[ reflexivity
| eapply step_lbu with (b := bb);
[ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac ]
| step_simpl ]; vnorm.

Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with
| context [bv_unsigned (Z_to_bv 64 _)] => fail
| _ => rewrite (u_Z2bv z) by lia
end
end.

Ltac addi_renorm :=
match goal with
| |- context [regupd _ _ (v_addi (Z_to_bv 64 ?x) ?i)] =>
let t := zbv_target (Z_to_bv 64 x) i in
replace (v_addi (Z_to_bv 64 x) i) with t by (unfold v_addi; unorm; f_equal; lia)
end.

Lemma rdn_img : forall segs mem (a : Z) (n : nat) (lo hi : Z),
(forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
(lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (0 <= lo)%Z -> (hi < 2^64)%Z ->
rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
intros segs mem a n lo hi Himg Hlo Hhi H0 H64.
apply rdn_ext; [u_norm; lia|].
intros x Hx. revert Hx. u_norm. intros Hx.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Himg. lia.
Qed.

Ltac img_exists :=
lazymatch goal with |- exists bs, ?l = Some bs =>
let v := eval vm_compute in l in
lazymatch v with Some ?bs => exists bs; vm_compute; reflexivity end
end.

Ltac enum_nat k N tac :=
let rec go n := lazymatch n with
| O => lia
| S ?m => destruct k as [|k]; [tac | go m]
end in go N.

Ltac zaddr H :=
repeat match type of H with
| context [Z_to_bv 64 (?a + ?b)%Z] =>
let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
end.

Ltac zaddr_goal :=
repeat match goal with
| |- context [Z_to_bv 64 (?a + ?b)%Z] =>
let c := eval cbv in (a + b)%Z in
lazymatch c with
| Zpos _ => change (a + b)%Z with c
end
end.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq7.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpox. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.

Import ListNotations.
Open Scope bv_scope.

Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
error_free (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
bh_traces (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply realizes_obs_iff. assumption. Qed.
