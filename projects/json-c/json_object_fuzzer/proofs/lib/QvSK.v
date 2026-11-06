(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE Q85Z Qt8n QWtD QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import QWTC QgpE Q85Z.Mq1 Qt8n QWtD.

Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Inductive scell : Type := SCw (w : nat) (v : expr) | SCz (n : nat) | SCi (n : nat).

Section Cells.
Variable segs : list Segment.

Definition rom_byte (a : Z) : byte := match seg_rom segs (Z_to_bv 64 a) with Some b => b | None => Z_to_bv 8 0 end.
Fixpoint rom_bytes (a : Z) (n : nat) : list byte := match n with O => [] | S n' => rom_byte a :: rom_bytes (a + 1) n' end.
Fixpoint rom_ok (a : Z) (n : nat) : bool :=
match n with O => true | S n' => match seg_rom segs (Z_to_bv 64 a) with Some _ => rom_ok (a + 1) n' | None => false end end.

Definition sc_len (c : scell) : nat := match c with SCw w _ => w | SCz n => n | SCi n => n end.
Fixpoint scs_len (cs : list scell) : nat := match cs with [] => O | c :: r => (sc_len c + scs_len r)%nat end.

Fixpoint sc_bytes (E : env) (A : Z) (cs : list scell) : list byte :=
match cs with
| [] => []
| SCw w v :: r => word_to_le_bytes w (edenot E v) ++ sc_bytes E (A + Z.of_nat w) r
| SCz n :: r => repeat (Z_to_bv 8 0) n ++ sc_bytes E (A + Z.of_nat n) r
| SCi n :: r => rom_bytes A n ++ sc_bytes E (A + Z.of_nat n) r
end.

Definition has_word (kn : list kentry) (b : expr) (off : Z) (w : nat) (v : expr) : bool :=
existsb (fun K => match K with
| KWord (SA b' k) w' v' => expr_eqb b b' && Z.eqb k off && Nat.eqb w w' && expr_eqb v v'
| _ => false end) kn.
Definition zero_at (kn : list kentry) (b : expr) (off : Z) : bool :=
existsb (fun K => match K with
| KZero (SA b' k) (ELit n) => expr_eqb b b' && Z.leb k off && Z.ltb off (k + n) && Z.leb 0 n && Z.ltb n (2^64)
| _ => false end) kn.
Fixpoint zeros_ok (kn : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
match n with O => true | S n' => zero_at kn b off && zeros_ok kn b (off + 1) n' end.
Definition img_at (kn : list kentry) (a : Z) : bool :=
existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.ltb a hi | _ => false end) kn.
Fixpoint imgs_ok (kn : list kentry) (a : Z) (n : nat) : bool :=
match n with O => true | S n' => img_at kn a && imgs_ok kn (a + 1) n' end.

Definition is_lit0 (b : expr) : bool := match b with ELit 0 => true | _ => false end.

Fixpoint cells_check (kn : list kentry) (b : expr) (off : Z) (cs : list scell) : bool :=
match cs with
| [] => true
| SCw w v :: r => has_word kn b off w v && cells_check kn b (off + Z.of_nat w) r
| SCz n :: r => zeros_ok kn b off n && cells_check kn b (off + Z.of_nat n) r
| SCi n :: r => is_lit0 b && imgs_ok kn off n && rom_ok off n && cells_check kn b (off + Z.of_nat n) r
end.

Lemma mrd_some : forall (m : word -> option byte) a b, m a = Some b -> QZDE.mrd segs m a = Some b.
Proof. intros m a b H. unfold QZDE.mrd. rewrite H. reflexivity. Qed.
Lemma mrd_none : forall (m : word -> option byte) a, m a = None -> QZDE.mrd segs m a = seg_rom segs a.
Proof. intros m a H. unfold QZDE.mrd. rewrite H. reflexivity. Qed.

Lemma rdn_mrd_c : forall (m : word -> option byte) n (a : word) bs i,
rdn segs m a n = Some bs -> (i < n)%nat -> bv_unsigned a + Z.of_nat n <= 2^64 ->
QZDE.mrd segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)) = nth_error bs i.
Proof.
intros m n. induction n as [|n IH]; intros a bs i H Hi Hnw; [lia|].
cbn [rdn] in H.
destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Hb; [|discriminate].
destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hr; [|discriminate].
injection H as <-.
destruct i as [|i].
- rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [nth_error]. unfold QZDE.mrd.
change (QsjA.seg_rom segs a) with (seg_rom segs a). exact Hb.
- cbn [nth_error].
assert (Hu : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S i)) with (bv_unsigned (a + 1)%bv + Z.of_nat i) by lia.
apply (IH (a + 1)%bv rest i Hr ltac:(lia)). lia.
Qed.

Lemma bytes_at_intro : forall (m : word -> option byte) A bs,
0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
(forall i, (i < length bs)%nat -> QZDE.mrd segs m (Z_to_bv 64 (A + Z.of_nat i)) = nth_error bs i) ->
QZDE.bytes_at segs m A bs.
Proof. intros m A bs H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi. unfold QZDE.wa. apply H. exact Hi. Qed.

Lemma nth_error_repeat : forall {X} (x : X) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof. intros X x n. induction n as [|n IH]; intros i Hi; [lia|]. destruct i; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma rom_bytes_length : forall n a, length (rom_bytes a n) = n.
Proof. induction n as [|n IH]; intros a; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma rom_bytes_nth : forall n a i, (i < n)%nat -> rom_ok a n = true ->
seg_rom segs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error (rom_bytes a n) i.
Proof.
induction n as [|n IH]; intros a i Hi Hok; [lia|]. cbn [rom_ok] in Hok.
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Hb; [|discriminate].
destruct i as [|i].
- rewrite Z.add_0_r. cbn [rom_bytes nth_error]. unfold rom_byte. rewrite Hb. reflexivity.
- cbn [rom_bytes nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply IH; [lia | exact Hok].
Qed.

Lemma sc_bytes_length : forall E cs A, length (sc_bytes E A cs) = scs_len cs.
Proof.
intros E cs. induction cs as [|[w v|n|n] r IH]; intros A; [reflexivity| | |]; cbn [sc_bytes scs_len sc_len]; rewrite length_app, IH.
- rewrite length_N_to_le_bytes. reflexivity.
- rewrite repeat_length. reflexivity.
- rewrite rom_bytes_length. reflexivity.
Qed.

Section Sound.
Variables (E : env) (base : word -> option byte) (kn : list kentry).
Hypothesis KN : know_ok segs E base kn.

Lemma zero_at_sound : forall b off, zero_at kn b off = true ->
base (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) = Some (Z_to_bv 8 0).
Proof.
intros b off H. unfold zero_at in H. apply existsb_exists in H as (K & HIn & HK).
pose proof (proj1 (Forall_forall _ _) KN K HIn) as OK.
destruct K as [| a n | | | | | | | |]; try discriminate. destruct a as [b' k]. destruct n; try discriminate.
apply andb_prop in HK as [HK H5]. apply andb_prop in HK as [HK H4]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
cbn [kentry_ok] in OK. destruct OK as [_ OK]. unfold elenZ, estart in OK. cbn [edenot a_base a_off] in OK.
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small in OK by lia.
specialize (OK (off - k) ltac:(lia)). replace (bv_unsigned (edenot E b) + k + (off - k)) with (bv_unsigned (edenot E b) + off) in OK by lia. exact OK.
Qed.

Lemma img_at_sound : forall a, img_at kn a = true -> base (Z_to_bv 64 a) = None.
Proof.
intros a H. unfold img_at in H. apply existsb_exists in H as (K & HIn & HK).
pose proof (proj1 (Forall_forall _ _) KN K HIn) as OK.
destruct K; try discriminate. apply andb_prop in HK as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
cbn [kentry_ok] in OK. destruct OK as (_ & _ & OK). apply OK. lia.
Qed.

Lemma has_word_sound : forall b off w v, has_word kn b off w v = true ->
let A := bv_unsigned (edenot E b) + off in
0 <= A /\ A + Z.of_nat w <= 2^64 /\
forall i, (i < w)%nat -> QZDE.mrd segs base (Z_to_bv 64 (A + Z.of_nat i)) = nth_error (word_to_le_bytes w (edenot E v)) i.
Proof.
intros b off w v H A. unfold has_word in H. apply existsb_exists in H as (K & HIn & HK).
pose proof (proj1 (Forall_forall _ _) KN K HIn) as OK.
destruct K as [a w' v'| | | | | | | | |]; try discriminate. destruct a as [b' k].
apply andb_prop in HK as [HK H4]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.eqb_eq in H2. subst k. apply Nat.eqb_eq in H3. subst w'. apply expr_eqb_eq in H4. subst v'.
cbn [kentry_ok] in OK. destruct OK as (_ & FL & RD).
pose proof (flat_u E _ _ FL) as FU. unfold estart in FU. cbn [a_base a_off] in FU.
destruct FL as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4. fold A in F1, F2, F4, FU.
split; [exact F1|]. split; [exact F4|]. intros i Hi.
pose proof (rdn_mrd_c base w _ _ i RD Hi ltac:(rewrite FU; exact F4)) as R. rewrite FU in R. exact R.
Qed.

Lemma zeros_ok_sound : forall n b off, zeros_ok kn b off n = true ->
forall i, (i < n)%nat -> base (Z_to_bv 64 (bv_unsigned (edenot E b) + off + Z.of_nat i)) = Some (Z_to_bv 8 0).
Proof.
induction n as [|n IH]; intros b off H i Hi; [lia|]. cbn [zeros_ok] in H. apply andb_prop in H as [H1 H2].
destruct i as [|i]; [rewrite Z.add_0_r; apply zero_at_sound; exact H1|].
replace (bv_unsigned (edenot E b) + off + Z.of_nat (S i)) with (bv_unsigned (edenot E b) + (off + 1) + Z.of_nat i) by lia.
apply IH; [exact H2 | lia].
Qed.

Lemma imgs_ok_sound : forall n a, imgs_ok kn a n = true -> forall i, (i < n)%nat -> base (Z_to_bv 64 (a + Z.of_nat i)) = None.
Proof.
induction n as [|n IH]; intros a H i Hi; [lia|]. cbn [imgs_ok] in H. apply andb_prop in H as [H1 H2].
destruct i as [|i]; [rewrite Z.add_0_r; apply img_at_sound; exact H1|].
replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply IH; [exact H2 | lia].
Qed.

Lemma cells_check_nth : forall cs b off, cells_check kn b off cs = true ->
forall i, (i < scs_len cs)%nat ->
QZDE.mrd segs base (Z_to_bv 64 (bv_unsigned (edenot E b) + off + Z.of_nat i)) = nth_error (sc_bytes E (bv_unsigned (edenot E b) + off) cs) i.
Proof.
induction cs as [|c r IH]; intros b off H i Hi; [cbn in Hi; lia|].
destruct c as [w v|n|n]; cbn [cells_check] in H; cbn [scs_len sc_len] in Hi; cbn [sc_bytes].
- apply andb_prop in H as [H1 H2]. destruct (has_word_sound b off w v H1) as (_ & _ & HW).
destruct (Nat.ltb_spec i w) as [L|G].
+ rewrite nth_error_app1 by (rewrite length_N_to_le_bytes; exact L). apply HW. exact L.
+ rewrite nth_error_app2 by (rewrite length_N_to_le_bytes; lia).
rewrite length_N_to_le_bytes.
replace (bv_unsigned (edenot E b) + off + Z.of_nat i) with (bv_unsigned (edenot E b) + (off + Z.of_nat w) + Z.of_nat (i - w)) by lia.
replace (bv_unsigned (edenot E b) + off + Z.of_nat w) with (bv_unsigned (edenot E b) + (off + Z.of_nat w)) by lia.
apply IH; [exact H2 | lia].
- apply andb_prop in H as [H1 H2].
destruct (Nat.ltb_spec i n) as [L|G].
+ rewrite nth_error_app1 by (rewrite repeat_length; exact L). rewrite nth_error_repeat by exact L.
apply mrd_some. apply (zeros_ok_sound n b off H1 i L).
+ rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length.
replace (bv_unsigned (edenot E b) + off + Z.of_nat i) with (bv_unsigned (edenot E b) + (off + Z.of_nat n) + Z.of_nat (i - n)) by lia.
replace (bv_unsigned (edenot E b) + off + Z.of_nat n) with (bv_unsigned (edenot E b) + (off + Z.of_nat n)) by lia.
apply IH; [exact H2 | lia].
- apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
assert (B0 : bv_unsigned (edenot E b) = 0) by (destruct b as [z| | | | | | |]; try discriminate; destruct z; try discriminate; reflexivity).
destruct (Nat.ltb_spec i n) as [L|G].
+ rewrite nth_error_app1 by (rewrite rom_bytes_length; exact L). rewrite B0, Z.add_0_l.
rewrite (mrd_none base _ (imgs_ok_sound n off H2 i L)). apply rom_bytes_nth; assumption.
+ rewrite nth_error_app2 by (rewrite rom_bytes_length; lia). rewrite rom_bytes_length.
replace (bv_unsigned (edenot E b) + off + Z.of_nat i) with (bv_unsigned (edenot E b) + (off + Z.of_nat n) + Z.of_nat (i - n)) by lia.
replace (bv_unsigned (edenot E b) + off + Z.of_nat n) with (bv_unsigned (edenot E b) + (off + Z.of_nat n)) by lia.
apply IH; [exact H4 | lia].
Qed.

Theorem cells_check_sound : forall cs b off, cells_check kn b off cs = true ->
let A := bv_unsigned (edenot E b) + off in
0 <= A -> A + Z.of_nat (scs_len cs) <= 2^64 ->
QZDE.bytes_at segs base A (sc_bytes E A cs).
Proof.
intros cs b off H A H0 H1. apply bytes_at_intro; [exact H0 | rewrite sc_bytes_length; exact H1 |].
intros i Hi. rewrite sc_bytes_length in Hi. exact (cells_check_nth cs b off H i Hi).
Qed.

Definition wr_check (b : expr) (off : Z) (n : Z) : bool :=
existsb (fun K => match K with
| KWr (SA b' k) (ELit len) => expr_eqb b b' && Z.leb k off && Z.leb (off + n) (k + len) && Z.leb 0 len && Z.ltb len (2^64)
| _ => false end) kn.

Theorem wr_check_sound : forall b off n, wr_check b off n = true -> 0 <= n ->
QZDE.wr_at segs base (bv_unsigned (edenot E b) + off) n.
Proof.
intros b off n H Hn. unfold wr_check in H. apply existsb_exists in H as (K & HIn & HK).
pose proof (proj1 (Forall_forall _ _) KN K HIn) as OK.
destruct K as [| | | | | | a len | | |]; try discriminate. destruct a as [b' k]. destruct len; try discriminate.
apply andb_prop in HK as [HK H5]. apply andb_prop in HK as [HK H4]. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply expr_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
cbn [kentry_ok] in OK. destruct OK as [FL OK]. unfold elenZ, estart in OK, FL. unfold flat, estart, elenZ in FL. cbn [edenot a_base a_off] in OK, FL.
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small in OK, FL by lia. destruct FL as (F1 & F2 & F3 & F4).
split; [lia|]. split; [lia|]. intros i Hi. unfold QZDE.wa.
specialize (OK (off - k + i) 1%nat ltac:(lia) ltac:(lia)).
replace (bv_unsigned (edenot E b) + k + (off - k + i)) with (bv_unsigned (edenot E b) + off + i) in OK by lia.
cbn [store_ok] in OK. destruct (wview segs base (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i))); [discriminate | discriminate OK].
Qed.
End Sound.

Fixpoint img_w_b (a : Z) (n : nat) : bool :=
match n with O => true | S n' => match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => img_w_b (a + 1) n' | None => false end end.
Lemma img_w_b_sound : forall n a (m : word -> option byte), img_w_b a n = true -> 0 <= a -> a + Z.of_nat n <= 2^64 ->
QZDE.wr_at segs m a (Z.of_nat n).
Proof.
intros n a m H H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi. unfold QZDE.wa.
revert a H H0 H1 i Hi. induction n as [|n IH]; intros a H H0 H1 i Hi; [lia|].
cbn [img_w_b] in H. destruct (wview segs (fun _ => None) (Z_to_bv 64 a)) as [b|] eqn:W; [|discriminate].
destruct (Z.eq_dec i 0) as [->|NE].
- rewrite Z.add_0_r. unfold wview in *. destruct (m (Z_to_bv 64 a)); [discriminate|]. cbn beta in W. rewrite W. discriminate.
- replace (a + i) with (a + 1 + (i - 1)) by lia. apply IH; [exact H | lia | lia | lia].
Qed.
End Cells.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ki. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= Stdlib.omega.PreOmega.Z.to_euclidean_division_equations.

Section Bridge.
Variable segs : list Segment.

Lemma to_spin_A_to_C : forall ms mo, QHWH.to_spin segs ms mo -> Q1Ki.to_spin segs ms mo.
Proof.
intros ms mo H. induction H as [ms mo Hs Hst | ms mo ms' mo' Hs Hst _ IH].
- exact (Q1Ki.ts_spin segs ms mo Hs Hst).
- exact (Q1Ki.ts_step segs ms mo ms' mo' Hs Hst IH).
Qed.
Lemma to_spin_C_to_A : forall ms mo, Q1Ki.to_spin segs ms mo -> QHWH.to_spin segs ms mo.
Proof.
intros ms mo H. induction H as [ms mo Hs Hst | ms mo ms' mo' Hs Hst _ IH].
- exact (QHWH.ts_spin segs ms mo Hs Hst).
- exact (QHWH.ts_step segs ms mo ms' mo' Hs Hst IH).
Qed.

Lemma srz_A_to_C_mut :
(forall c T, Q1lV.srealizes segs c T -> Q6EJ.srealizes segs c T) /\
(forall V T c, Q1lV.slbody segs V T c -> Q6EJ.slbody segs V T c).
Proof.
apply (Q1lV.srealizes_slbody_mutind segs
(fun c T _ => Q6EJ.srealizes segs c T) (fun V T c _ => Q6EJ.slbody segs V T c)).
- intros c I evs nx T i0 Hn _ IH. exact (Q6EJ.srz_node segs c I evs nx T i0 Hn IH).
- intros c Hh. exact (Q6EJ.srz_halt segs c Hh).
- intros c Hs Hh. exact (Q6EJ.srz_spin segs c (to_spin_A_to_C _ _ Hs) Hh).
- intros c T T' _ IH Heq. exact (Q6EJ.srz_conseq segs c T T' IH Heq).
- intros V T c c_e HV _ IHb Hst _ IHe. exact (Q6EJ.srz_loop segs V T c c_e HV IHb Hst IHe).
- intros V T c _ IH. exact (Q6EJ.slb_exit segs V T c IH).
- intros V T c I nx k Hn _ IHk HV. exact (Q6EJ.slb_node segs V T c I nx k Hn IHk HV).
Qed.

Theorem srz_A_to_C : forall c T, Q1lV.srealizes segs c T -> Q6EJ.srealizes segs c T.
Proof. exact (proj1 srz_A_to_C_mut). Qed.

Lemma srz_C_to_A_mut :
(forall c T, Q6EJ.srealizes segs c T -> Q1lV.srealizes segs c T) /\
(forall V T c, Q6EJ.slbody segs V T c -> Q1lV.slbody segs V T c).
Proof.
apply (Q6EJ.srealizes_slbody_mutind segs
(fun c T _ => Q1lV.srealizes segs c T) (fun V T c _ => Q1lV.slbody segs V T c)).
- intros c I evs nx T i0 Hn _ IH. exact (Q1lV.srz_node segs c I evs nx T i0 Hn IH).
- intros c Hh. exact (Q1lV.srz_halt segs c Hh).
- intros c Hs Hh. exact (Q1lV.srz_spin segs c (to_spin_C_to_A _ _ Hs) Hh).
- intros c T T' _ IH Heq. exact (Q1lV.srz_conseq segs c T T' IH Heq).
- intros V T c c_e HV _ IHb Hst _ IHe. exact (Q1lV.srz_loop segs V T c c_e HV IHb Hst IHe).
- intros V T c _ IH. exact (Q1lV.slb_exit segs V T c IH).
- intros V T c I nx k Hn _ IHk HV. exact (Q1lV.slb_node segs V T c I nx k Hn IHk HV).
Qed.

Theorem srz_C_to_A : forall c T, Q6EJ.srealizes segs c T -> Q1lV.srealizes segs c T.
Proof. exact (proj1 srz_C_to_A_mut). Qed.
End Bridge.
