(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC QoNr Qs9x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import QCiC.Mq1. Import QoNr.
Import Qs9x.
Import ListNotations.
Open Scope Z_scope.

Lemma Zrange_forallb : forall (P : Z -> bool) (lo : Z) (n : nat),
forallb P (map (fun k => lo + Z.of_nat k) (seq 0 n)) = true ->
forall c, lo <= c < lo + Z.of_nat n -> P c = true.
Proof.
intros P lo n H c Hc. rewrite forallb_forall in H. apply H.
apply in_map_iff. exists (Z.to_nat (c - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Notation M64 := 18446744073709551615.

Lemma digit_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
Bool.eqb (Z.land (c + -48) M64 <=? 9) (is_digit c) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma digit_test : forall c, 0 <= c < 256 -> (Z.land (c + -48) M64 <= 9 <-> is_digit c = true).
Proof.
intros c Hc. pose proof (digit_testb c ltac:(cbn; lia)) as E.
destruct (Z.leb_spec0 (Z.land (c + -48) M64) 9); destruct (is_digit c); cbn in E; try discriminate.
all: split; intros; first [reflexivity | assumption | discriminate | lia].
Qed.
Lemma digit_range : forall c, is_digit c = true <-> 48 <= c <= 57.
Proof. intros c. unfold is_digit. rewrite andb_true_iff, !Z.leb_le. lia. Qed.

Lemma sp_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
Bool.eqb (Z.land (c + -32) M64 <? 32) ((32 <=? c) && (c <? 64)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma sp_test : forall c, 0 <= c < 256 -> (Z.land (c + -32) M64 < 32 <-> 32 <= c < 64).
Proof.
intros c Hc. pose proof (sp_testb c ltac:(cbn; lia)) as E.
destruct (Z.ltb_spec0 (Z.land (c + -32) M64) 32); destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in E; try discriminate; lia.
Qed.

Definition flagw (c : Z) : Z := Z.land (bv_swrap 32 (Z.shiftl 1 ((c + -32) mod 32))) M64.

Lemma flag_noneb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
Bool.eqb (Z.land (flagw c) 75913 =? 0) (match flag_bit c with None => true | Some _ => false end) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_none : forall c, 32 <= c < 64 -> (Z.land (flagw c) 75913 = 0 <-> flag_bit c = None).
Proof.
intros c Hc. pose proof (flag_noneb c ltac:(cbn; lia)) as E.
destruct (Z.eqb_spec (Z.land (flagw c) 75913) 0); destruct (flag_bit c); cbn in E; try discriminate.
all: split; intros; first [reflexivity | assumption | discriminate | congruence | lia].
Qed.
Lemma flag_someb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
match flag_bit c with None => true | Some b => (flagw c =? b) && (0 <=? b) && (b <? 131072) end = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_some : forall c b, 32 <= c < 64 -> flag_bit c = Some b -> flagw c = b /\ 0 <= b < 131072.
Proof.
intros c b Hc Hb. pose proof (flag_someb c ltac:(cbn; lia)) as E. rewrite Hb in E.
rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3]. apply Z.eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. lia.
Qed.
Lemma flag_bit_range : forall c, flag_bit c <> None -> 32 <= c < 64.
Proof.
intros c H. unfold flag_bit in H.
destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in H; try lia; exfalso; apply H; reflexivity.
Qed.

Lemma lor_bound17 : forall a b, 0 <= a < 131072 -> 0 <= b < 131072 -> 0 <= Z.lor a b < 131072.
Proof.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
change 131072 with (2^17) in *.
destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma parse_flags_cons_some : forall c s fl b, flag_bit c = Some b -> parse_flags (c :: s) fl = parse_flags s (Z.lor fl b).
Proof. intros c s fl b H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_cons_none : forall c s fl, flag_bit c = None -> parse_flags (c :: s) fl = (fl, c :: s).
Proof. intros c s fl H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_range : forall s fl, 0 <= fl < 131072 -> 0 <= fst (parse_flags s fl) < 131072.
Proof.
induction s as [|c s IH]; intros fl Hfl; cbn; [exact Hfl|].
destruct (flag_bit c) as [b|] eqn:E; [|exact Hfl].
apply IH. pose proof (flag_some c b (flag_bit_range c ltac:(congruence)) E) as [_ Hb]. apply lor_bound17; lia.
Qed.

Lemma getint_cons_digit : forall c s i, is_digit c = true ->
getint (c :: s) i = if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None else getint s (10 * i + (c - 48)).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_cons_nondigit : forall c s i, is_digit c = false -> getint (c :: s) i = Some (i, c :: s).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_some_range : forall s i w s', 0 <= i <= INT_MAX -> getint s i = Some (w, s') -> 0 <= w <= INT_MAX.
Proof.
induction s as [|c s IH]; intros i w s' Hi H; cbn [getint] in H.
- inversion H; subst. exact Hi.
- destruct (is_digit c) eqn:D.
+ destruct (214748364 <? i) eqn:E1; [discriminate|]. destruct (INT_MAX - 10 * i <? c - 48) eqn:E2; [discriminate|]. cbn in H.
apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. apply digit_range in D. unfold INT_MAX in *. eapply IH; [|exact H]. lia.
+ inversion H; subst. exact Hi.
Qed.

Lemma lxor_imax : forall x, 0 <= x <= 2147483647 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof.
intros x Hx. change 2147483647 with (Z.ones 31).
assert (E : Z.lxor x (Z.ones 31) = (Z.lnot x) mod 2^31).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 31).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; cbn in *; lia|lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^31)) with (2^31 - 1).
replace (Z.lnot x) with (-x - 1) by (unfold Z.lnot; lia).
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by (cbn in *; lia). lia.
Qed.

Lemma parse_dir_shape : forall s d rest, parse_dir s = Some (d, rest) ->
match s with c0 :: c0b :: _ => is_digit c0 && (c0b =? 36) = false | [c0] => is_digit c0 = false | [] => True end /\
let (fl, s1) := parse_flags s 0 in
d_fl d = fl /\
exists c1 s1b, s1 = c1 :: s1b /\ c1 <> 42 /\
exists s2, getint s1 0 = Some (d_w d, s2) /\
exists c2 s2b, s2 = c2 :: s2b /\
( (c2 <> 46 /\ d_p d = -1 /\ d_xp d = false /\ d_t d = c2 /\ rest = s2b /\ conv_type c2 = Some (d_ty d))
\/ (c2 = 46 /\ d_xp d = true /\ exists c3 s3b, s2b = c3 :: s3b /\ c3 <> 42 /\
exists s3, getint s2b 0 = Some (d_p d, s3) /\ s3 = d_t d :: rest /\ conv_type (d_t d) = Some (d_ty d)) ).
Proof.
intros s d rest H. unfold parse_dir in H.
split. { destruct s as [|c0 [|c0b s0]]; try exact I. { destruct (is_digit c0); [discriminate|reflexivity]. } destruct (is_digit c0 && (c0b =? 36)); [discriminate|reflexivity]. }
match type of H with (if ?pp then None else _) = _ => destruct pp; [discriminate|] end.
destruct (parse_flags s 0) as [fl s1].
destruct s1 as [|c1 s1b]; [discriminate|].
destruct (Z.eqb_spec c1 42) as [E42|N42]; [discriminate|].
destruct (getint (c1 :: s1b) 0) as [[w s2]|] eqn:G; [|discriminate].
destruct s2 as [|c2 s2b]; [discriminate|].
destruct (Z.eqb_spec c2 46) as [E46|N46].
- destruct s2b as [|c3 s3b]; [discriminate|]. destruct (Z.eqb_spec c3 42) as [E42'|N42']; [discriminate|].
destruct (getint (c3 :: s3b) 0) as [[p s3]|] eqn:G2; [|discriminate].
destruct s3 as [|t s4]; [discriminate|]. destruct (conv_type t) as [ty|] eqn:CT; [|discriminate].
injection H as <- <-. cbn. split; [reflexivity|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
exists (c2 :: c3 :: s3b). split; [first [reflexivity | exact G]|]. exists c2, (c3 :: s3b). split; [reflexivity|].
right. split; [exact E46|]. split; [reflexivity|]. exists c3, s3b. split; [reflexivity|]. split; [exact N42'|].
exists (t :: s4). split; [first [reflexivity | exact G2]|]. split; first [reflexivity | exact CT].
- destruct (conv_type c2) as [ty|] eqn:CT; [|discriminate]. injection H as <- <-. cbn.
split; [reflexivity|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
exists (c2 :: s2b). split; [first [reflexivity | exact G]|]. exists c2, s2b. split; [reflexivity|].
left. split; [exact N46|]. repeat split; first [reflexivity | exact CT].
Qed.

Lemma parse_flags_suffix : forall s acc fl s1, parse_flags s acc = (fl, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
induction s as [|c s IH]; intros acc fl s1 H; cbn in H.
- injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
- destruct (flag_bit c) as [b|].
+ destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
+ injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.
Lemma getint_suffix : forall s acc w s1, getint s acc = Some (w, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
induction s as [|c s IH]; intros acc w s1 H; cbn [getint] in H.
- injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
- destruct (is_digit c).
+ destruct (_ || _); [discriminate|]. destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
+ injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.

Definition STATES0 : list Z :=
[25; 0; 11; 0; 25; 25; 25; 0; 0; 0; 0; 5; 0; 0; 0; 0; 0; 0; 9; 0; 0; 0; 0; 11; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 10; 10; 25; 25; 25; 3; 10; 7; 0; 1; 27; 9; 11; 24; 0; 0; 9; 6; 11; 0; 0; 11; 0; 6].
Lemma conv_type_range : forall t ty, conv_type t = Some ty -> 65 <= t <= 122.
Proof.
intros t ty H. unfold conv_type in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [try (injection H as <-)|] end; try discriminate;
repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end; try lia.
Qed.
Lemma states0_conv : forall t ty, conv_type t = Some ty -> znth STATES0 (t - 65) = ty.
Proof.
intros t ty H. unfold conv_type in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [injection H as <-|] end; try discriminate;
repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E; subst; reflexivity | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end.
Qed.

Definition conv_target (t : Z) : Z :=
if t =? 115 then 0x23558
else if (t =? 100) || (t =? 105) then 0x23510
else if t =? 117 then 0x23648
else if (t =? 120) || (t =? 88) then 0x236c0
else 0x234c0.

Lemma conv_type_ty : forall t ty, conv_type t = Some ty -> ty = 9 \/ ty = 10 \/ ty = 11 \/ ty = 25.
Proof.
intros t ty H. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c; [injection H as <-; lia|] end. discriminate.
Qed.

Lemma land_M64_neg : forall x, - 2^64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2^64.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma nzmask_bits : forall n, 0 <= n < 0 + Z.of_nat 64 -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma nzmask_eq : forall fl, 0 <= fl < 131072 -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof.
intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases n 64).
- pose proof (nzmask_bits n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
- replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
Qed.
Lemma land_bound : forall a m, 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
Proof.
intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
pose proof (Z.sub_land_same_l a m) as E.
assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha).
lia.
Qed.
End Mq0.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTa Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.

Import QdTa Q0z1.
Open Scope Z_scope.

Module RL.
Import Ltac2.
Ltac2 ops () : constr list :=
[constr:(Z.add); constr:(Z.sub); constr:(Z.mul); constr:(Z.opp); constr:(Z.succ); constr:(Z.pred);
constr:(Z.le); constr:(Z.lt); constr:(Z.ge); constr:(Z.gt); constr:(@eq); constr:(and); constr:(or);
constr:(not); constr:(iff); constr:(Z.div); constr:(Z.modulo); constr:(Z.of_nat); constr:(Z.to_nat);
constr:(Z.min); constr:(Z.max); constr:(Z.pow);

constr:(Nat.add); constr:(Nat.sub); constr:(Nat.mul); constr:(Nat.div); constr:(Nat.modulo); constr:(Nat.pred);
constr:(Nat.min); constr:(Nat.max); constr:(N.add); constr:(N.sub); constr:(N.mul); constr:(N.of_nat); constr:(N.to_nat);
constr:(Z.of_N); constr:(Z.to_N); constr:(Z.abs); constr:(Z.quot); constr:(Z.rem)].
Ltac2 rec add_atom (c : constr) (acc : constr list) : constr list :=
if List.exist (Constr.equal c) acc then acc else c :: acc.

Ltac2 rec atoms (ops : constr list) (acc : constr list) (c : constr) : constr list :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f args =>
if List.exist (Constr.equal f) ops then Array.fold_left (atoms ops) acc args
else
match Constr.Unsafe.kind f with

| Constr.Unsafe.Constructor _ _ => Array.fold_left (atoms ops) acc args
| Constr.Unsafe.Ind _ _ => Array.fold_left (atoms ops) acc args
| _ => add_atom c acc
end
| Constr.Unsafe.Var _ => add_atom c acc
| Constr.Unsafe.Constant _ _ => add_atom c acc
| Constr.Unsafe.Prod b body => atoms ops (atoms ops acc (Constr.Binder.type b)) body
| Constr.Unsafe.Cast c _ _ => atoms ops acc c
| _ => acc
end.
Ltac2 rec meets (xs : constr list) (ys : constr list) : bool :=
match xs with
| [] => false
| x :: xs' => if List.exist (Constr.equal x) ys then true else meets xs' ys
end.

Ltac2 hop (ops : constr list) (g : constr list) : constr list :=
let sfh := constr:(sf_hide) in
List.fold_left (fun g h => let (id, body, ty) := h in
match body with
| Some _ => g
| None =>
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args =>
if Constr.equal f sfh then
let p := Array.get args 0 in
let ap := atoms ops [] p in
if meets ap g then
(ltac1:(h |- unfold sf_hide in h) (Ltac1.of_ident id);
List.fold_left (fun g a => add_atom a g) g ap)
else g
else g
| _ => g
end
end) g (Control.hyps ()).
Ltac2 unhide_rel () : unit :=
let ops := ops () in
let g := atoms ops [] (Control.goal ()) in
let g := hop ops g in
let _ := hop ops g in ().
Ltac sf_unhide_rel_atoms := ltac2:(Control.enter unhide_rel).

Ltac2 hid (ty : constr) : constr option :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args => if Constr.equal f constr:(sf_hide) then Some (Array.get args 0) else None
| _ => None
end.
Ltac2 is_local (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
Ltac2 rel_prune () : unit :=
let ops := ops () in
let hs := Control.hyps () in

let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None =>
if is_local id then
match hid ty with
| Some p => if SF2.arith_logic p then Some (id, p, true, false) else None
| None => if SF2.arith_logic ty then Some (id, ty, false, SF2.plain_arith false ty) else None
end
else None
end) hs in
let step g := List.fold_left (fun g f => let (_, p, _, _) := f in
let ap := atoms ops [] p in if meets ap g then List.fold_left (fun g a => add_atom a g) g ap else g) g facts in
let g := step (step (atoms ops [] (Control.goal ()))) in
let drop := List.map_filter (fun f => let (id, p, hidden, plain) := f in
if plain then None else if meets (atoms ops [] p) g then None else Some id) facts in
(match drop with [] => () | _ :: _ => Std.clear drop end);
List.iter (fun f => let (id, p, hidden, _) := f in
if hidden then (if meets (atoms ops [] p) g then ltac1:(h |- unfold sf_hide in h) (Ltac1.of_ident id) else ()) else ()) facts.
Ltac zify_prune_rel_atoms := ltac2:(Control.enter rel_prune).

Ltac2 rel_prune_all (hops : int) : unit :=
let ops := ops () in
let hs := Control.hyps () in
let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None =>
if is_local id then
match hid ty with
| Some p => if SF2.arith_logic p then Some (id, p, true) else None
| None => if SF2.arith_logic ty then Some (id, ty, false) else None
end
else None
end) hs in
let step g := List.fold_left (fun g f => let (_, p, _) := f in
let ap := atoms ops [] p in if meets ap g then List.fold_left (fun g a => add_atom a g) g ap else g) g facts in
let rec close n g := if Int.equal n 0 then g else close (Int.sub n 1) (step g) in
let g := close hops (atoms ops [] (Control.goal ())) in
let drop := List.map_filter (fun f => let (id, p, _) := f in if meets (atoms ops [] p) g then None else Some id) facts in
(match drop with [] => () | _ :: _ => Std.clear drop end);
List.iter (fun f => let (id, p, hidden) := f in
if hidden then (if meets (atoms ops [] p) g then ltac1:(h |- unfold sf_hide in h) (Ltac1.of_ident id) else ()) else ()) facts.
Ltac zify_prune_rel_all1 := ltac2:(Control.enter (fun () => rel_prune_all 1)).

Ltac2 rel_prune_h (hops : int) : unit :=
let ops := ops () in
let hs := Control.hyps () in
let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None =>
if is_local id then
match hid ty with
| Some p => if SF2.arith_logic p then Some (id, p, true, false) else None
| None => if SF2.arith_logic ty then Some (id, ty, false, SF2.plain_arith false ty) else None
end
else None
end) hs in

let step g := List.fold_left (fun acc f => let (_, p, _, _) := f in
let ap := atoms ops [] p in if meets ap g then List.fold_left (fun acc a => add_atom a acc) acc ap else acc) g facts in
let rec close n g := if Int.equal n 0 then g else close (Int.sub n 1) (step g) in

let g0 := atoms ops [] (Control.goal ()) in
let g0 := match g0 with
| [] => List.fold_left (fun g f => let (_, p, _, _) := f in List.fold_left (fun g a => add_atom a g) g (atoms ops [] p))
[] (List.firstn (if Int.le (List.length facts) 4 then List.length facts else 4) (List.rev facts))
| _ :: _ => g0
end in
let g := close hops g0 in
let drop := List.map_filter (fun f => let (id, p, hidden, plain) := f in
if plain then None else if meets (atoms ops [] p) g then None else Some id) facts in
(match drop with [] => () | _ :: _ => Std.clear drop end);
List.iter (fun f => let (id, p, hidden, _) := f in
if hidden then (if meets (atoms ops [] p) g then ltac1:(h |- unfold sf_hide in h) (Ltac1.of_ident id) else ()) else ()) facts.
Ltac zify_prune_rel_h0 := ltac2:(Control.enter (fun () => rel_prune_h 0)).
Ltac zify_prune_rel_h1 := ltac2:(Control.enter (fun () => rel_prune_h 1)).
Ltac zify_prune_rel_h2 := ltac2:(Control.enter (fun () => rel_prune_h 2)).

Ltac2 ctx_small (k : int) : unit :=
if Int.le (List.length (Control.hyps ())) k then () else Control.zero (Tactic_failure None).
Ltac ctx_small40 := ltac2:(Control.enter (fun () => ctx_small 40)).
End RL.
Ltac sf_unhide_rel_atoms := RL.sf_unhide_rel_atoms.
Ltac zify_prune_rel_atoms := RL.zify_prune_rel_atoms.
Ltac zify_prune_rel_all1 := RL.zify_prune_rel_all1.
Ltac zify_prune_rel_h0 := RL.zify_prune_rel_h0.
Ltac zify_prune_rel_h1 := RL.zify_prune_rel_h1.
Ltac zify_prune_rel_h2 := RL.zify_prune_rel_h2.
Ltac ctx_small40 := RL.ctx_small40.
Ltac lia_rel := Qo9G.term_slim ltac:(zify_prune_rel_atoms; Zify.zify; xlia zchecker).

Ltac lia_rel0 := Qo9G.term_slim ltac:(zify_prune_rel_all1; Zify.zify; xlia zchecker).

Ltac lia_relh0 := Qo9G.term_slim ltac:(zify_prune_rel_h0; Zify.zify; xlia zchecker).
Ltac lia_relh1 := Qo9G.term_slim ltac:(zify_prune_rel_h1; Zify.zify; xlia zchecker).
Ltac lia_relh2 := Qo9G.term_slim ltac:(zify_prune_rel_h2; Zify.zify; xlia zchecker).

Ltac tlia_rel := first [ Qo9G.term_slim ltac:(zify_prune_plain; Zify.zify; xlia zchecker) | lia_relh0 | lia_relh1 ].

Ltac lia_walk := first [ Qo9G.term_slim ltac:(zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune; Zify.zify; xlia zchecker)
| lia_relh0
| lia_rel
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Ltac lia_walk_nf := first [ Qo9G.term_slim ltac:(zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(ctx_small40; Zify.zify; xlia zchecker)
| lia_relh0
| lia_relh1
| lia_relh2 ].

Ltac tslia_rel := first [ exact I | repeat match goal with |- _ /\ _ => split end; first [ exact I | tlia_rel ] ].
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QwAs Qc6I QJFf Qpj5 QCNF QdZp QWHo QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF QoNr.Mq0. Import QdZp.
Import QWHo QC9y.Mq0.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma impl_post_evt : forall segs {node R} (atn : node -> machine_state -> Prop) (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
Qc6I.impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> Qc6I.impl segs atn t Q' ms.
Proof.
intros segs node R atn t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. exact (HQ r).
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
Qed.
Lemma implM_post_evt : forall segs {St A} (c : M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
Qpj5.Mq1.implM segs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt segs (Q' a s') ms') -> Qpj5.Mq1.implM segs c s Q' ms.
Proof.
intros segs St A c s Q Q' ms H HQ. unfold Qpj5.Mq1.implM in *. eapply impl_post_evt; [exact H|].
intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I | apply HQ].
Qed.

Section Outs.
Variable segs : list Segment.
Context {St : Type}.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
Local Notation implM := (Qpj5.Mq1.implM segs).

Fixpoint outsk {B} (ps : list (list Z)) (k : M St B) : M St B :=
match ps with
| [] => k
| p :: ps' => OUT p ;;; outsk ps' k
end.

Lemma outsk_app : forall {B} ps qs (k : M St B), outsk (ps ++ qs) k = outsk ps (outsk qs k).
Proof. induction ps as [|p ps IH]; intros qs k; [reflexivity|]. cbn [outsk app]. rewrite IH. reflexivity. Qed.

Lemma outsk_mono : forall {B} ps (k1 k2 : M St B) Q,
(forall s ms, implM k1 s Q ms -> implM k2 s Q ms) ->
forall s ms, implM (outsk ps k1) s Q ms -> implM (outsk ps k2) s Q ms.
Proof.
induction ps as [|p ps IH]; intros k1 k2 Q HK s ms H; cbn [outsk] in *; [apply HK; exact H|].
eapply implM_bind_ext; [|exact H]. intros x s' ms' H'. eapply IH; [exact HK | exact H'].
Qed.

Lemma mpad_outs : forall {B} c w l fl pp (K : unit -> M St B) s Q ms,
pad_pieces c w l fl = Some pp ->
implM (mbind (mpad OUT c w l fl) K) s Q ms -> implM (outsk pp (K tt)) s Q ms.
Proof.
intros B c w l fl pp K s Q ms P H. unfold mpad, pad_pieces in *.
destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
- inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H.
- destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [outsk].
eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'.
Qed.

Lemma conv_tail_outs : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B) s Q ms,
tail_pieces cnt fl w p prefix body = Some (ps, r) ->
implM (mbind (conv_tail OUT cnt fl w p prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt fl w p prefix body ps r K s Q ms T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta in H.
destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
inversion T; subst. clear T.
match goal with |- implM (outsk ?L (K ?rr)) _ _ _ =>
replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
by (rewrite ?outsk_app; cbn [outsk]; rewrite ?outsk_app; cbn [outsk]; reflexivity) end.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P1) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s1 ms1 H.
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x2 s2 ms2 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P2) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s3 ms3 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P3) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s4 ms4 H.
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x5 s5 ms5 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P4) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s6 ms6 H.
apply implM_ret_l_rev in H. exact H.
Qed.

Lemma conv_int_outs : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B) s Q ms,
int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
implM (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt fl w p xp argi prefix body ps r K s Q ms T H. unfold conv_int, int_pieces in *.
destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta in H.
destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outs; eassumption.
Qed.

Lemma conv_outs : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
conv_pieces cnt d a = Some (ps, r) ->
implM (mbind (conv OUT OUTFP cnt d a) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt d a ps r K s Q ms T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta in H.
destruct a as [str|i|u|dd].
- destruct (negb (d_ty d =? T_PTR)); [discriminate|].
destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
eapply conv_tail_outs; eassumption.
- destruct (negb (d_ty d =? T_INT)); [discriminate|].
destruct (INTMAX_MAX <? i mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_outs; eassumption.
- destruct (negb (d_ty d =? T_UINT)); [discriminate|].
destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
- discriminate.
Qed.

Lemma printf_loop_outs : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
printf_pieces_loop fuel s args cnt = Some (ps, r) ->
implM (mbind (printf_loop OUT OUTFP fuel s args cnt) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
Proof.
induction fuel as [|fuel IH]; intros s args cnt ps r k st Q ms P H; [discriminate|].
cbn [printf_pieces_loop] in P. cbn [printf_loop] in H.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H. }
cbv zeta in P. cbv zeta in H. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
destruct (0 <? zlength lit).
- destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. cbn [outsk].
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
eapply IH; [exact R | exact H'].
- destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
inversion P; subst. clear P.
match goal with |- implM (outsk ?L (k ?rr)) _ _ _ =>
replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
cbn [outsk].
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
apply implM_assoc_rev in H'. apply (conv_outs _ _ _ _ _ _ _ _ _ C) in H'.
eapply outsk_mono; [|exact H']. cbv beta. intros s'' ms'' H''. eapply IH; [exact R | exact H''].
Qed.

Theorem printf_model_outs : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
printf_pieces fmt args = Some (ps, r) ->
implM (mbind (printf_model OUT OUTFP fmt args) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
Proof. intros B fmt args ps r k st Q ms P H. eapply printf_loop_outs; [exact P | exact H]. Qed.
End Outs.

Ltac lhs_cbvs := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces] in l in change l with l' end.
Lemma zlength_nonneg' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma digits_aux_nil : forall f acc, digits_aux f 10 (fun v => 48 + v) 0 acc = acc.
Proof. intros [|f] acc; reflexivity. Qed.

Lemma digits_aux_dec : forall f x acc, 0 < x < 10 ^ Z.of_nat f ->
digits_aux f 10 (fun v => 48 + v) x acc = dec_digits_fuel f x ++ acc.
Proof.
induction f as [|f IH]; intros x acc Hx.
- cbn in Hx. lia.
- cbn [digits_aux dec_digits_fuel]. replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
destruct (Z.ltb_spec x 10) as [LT|GE].
+ rewrite Z.div_small by lia. rewrite digits_aux_nil. rewrite Z.mod_small by lia. reflexivity.
+ rewrite IH by (split; [apply Z.div_str_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite <- app_assoc. reflexivity.
Qed.

Lemma PM_dec_digits_eq : forall x, 0 < x < 10 ^ 20 -> QWHo.dec_digits x = QdZp.dec_digits x.
Proof.
intros x Hx. unfold QWHo.dec_digits, QdZp.dec_digits.
rewrite digits_aux_dec by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; exact Hx). apply app_nil_r.
Qed.

Lemma digits_aux_length : forall f b d x acc, (length (digits_aux f b d x acc) <= f + length acc)%nat.
Proof.
induction f as [|f IH]; intros b d x acc; cbn [digits_aux]; [lia|].
destruct (x =? 0); [cbn; lia|]. specialize (IH b d (x / b) (d (x mod b) :: acc)). cbn [length] in IH. lia.
Qed.
Lemma PM_dec_digits_length : forall x, zlength (QWHo.dec_digits x) <= 20.
Proof. intros x. unfold zlength, QWHo.dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v) x []) as H. cbn [length Nat.add] in H. lia. Qed.

Lemma digits_aux_ne : forall f b d y acc, acc <> [] -> digits_aux f b d y acc <> [].
Proof. induction f as [|f IH]; intros b d y acc H; cbn [digits_aux]; [exact H|]. destruct (y =? 0); [exact H|]. apply IH. discriminate. Qed.
Lemma digits_aux_S : forall f b d x acc,
digits_aux (S f) b d x acc = if x =? 0 then acc else digits_aux f b d (x / b) (d (x mod b) :: acc).
Proof. reflexivity. Qed.
Lemma PM_dec_digits_pos : forall x, 0 < x -> QWHo.dec_digits x <> [].
Proof.
intros x Hx. unfold QWHo.dec_digits. change 20%nat with (S 19). rewrite digits_aux_S.
replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply digits_aux_ne. discriminate.
Qed.

Definition DIR_d : dir := {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |}.

Definition d_pieces (v : Z) : list (list Z) :=
if v =? 0 then [[]; [48]; []]
else if 0 <? v then [[]; QWHo.dec_digits v]
else [[45]; QWHo.dec_digits (- v)].
Definition d_count (v : Z) : Z :=
if v =? 0 then 1
else if 0 <? v then zlength (QWHo.dec_digits v)
else 1 + zlength (QWHo.dec_digits (- v)).

Lemma tail_pieces_plain : forall cnt prefix body, 0 <= cnt -> cnt + 25 <= INT_MAX ->
zlength prefix <= 2 -> 1 <= zlength body <= 20 ->
tail_pieces cnt 0 0 (zlength body) prefix body = Some ([prefix; body], cnt + zlength prefix + zlength body).
Proof.
intros cnt prefix body Hc Hc2 Hp Hb. pose proof (zlength_nonneg' prefix) as P0. unfold tail_pieces. cbv zeta.
rewrite Z.max_id.
replace (INT_MAX - zlength prefix <? zlength body) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX in *; lia).
replace (Z.max 0 (zlength prefix + zlength body)) with (zlength prefix + zlength body) by lia.
replace (INT_MAX - cnt <? zlength prefix + zlength body) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX in *; lia).
unfold pad_pieces. rewrite !Z.leb_refl, !orb_true_r. cbn [app]. f_equal. f_equal. lia.
Qed.

Lemma tail_pieces_zero : forall cnt, 0 <= cnt -> cnt + 25 <= INT_MAX ->
tail_pieces cnt 0 0 1 [] [] = Some ([[]; [48]; []], cnt + 1).
Proof.
intros cnt Hc Hc2. unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
change (Z.max 1 0) with 1. change (INT_MAX - 0 <? 1) with false. change (Z.max 0 (0 + 1)) with 1.
replace (INT_MAX - cnt <? 1) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX in *; lia).
reflexivity.
Qed.

Lemma conv_pieces_d : forall cnt v, 0 <= cnt -> cnt + 25 <= INT_MAX -> -2^31 <= v < 2^31 ->
conv_pieces cnt DIR_d (PA_i v) = Some (d_pieces v, cnt + d_count v).
Proof.
intros cnt v Hc Hc2 Hv. unfold d_pieces, d_count.
destruct (Z.eqb_spec v 0) as [->|NZ].
{ change (conv_pieces cnt DIR_d (PA_i 0)) with (tail_pieces cnt 0 0 1 [] []). apply tail_pieces_zero; assumption. }
unfold conv_pieces, DIR_d. cbn [d_fl d_w d_p d_xp d_t d_ty].
change (Z.land 0 LEFT_ADJ =? 0) with true. change (negb (T_INT =? T_INT)) with false. cbv iota.
change (Z.land 0 MARK_POS =? 0) with true. change (Z.land 0 PAD_POS =? 0) with true. cbn [negb].
assert (E64 : v mod 2^64 = (if 0 <? v then v else 2^64 + v)).
{ destruct (Z.ltb_spec 0 v). { apply Z.mod_small. lia. }
rewrite <- (Z.mod_add v 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia. }
rewrite E64. clear E64. destruct (Z.ltb_spec 0 v) as [POS|NEG].
+ replace (INTMAX_MAX <? v) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
unfold int_pieces. cbn [andb]. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
pose proof (PM_dec_digits_length v) as L. pose proof (PM_dec_digits_pos v POS) as NE.
assert (L1 : 1 <= zlength (QWHo.dec_digits v)).
{ unfold zlength in *. destruct (QWHo.dec_digits v); [congruence| cbn [length]; lia]. }
rewrite Z.add_0_r. replace (Z.max (-1) (zlength (QWHo.dec_digits v))) with (zlength (QWHo.dec_digits v)) by lia.
rewrite tail_pieces_plain; [| lia | lia | change (zlength (@nil Z)) with 0; lia | lia]. f_equal. f_equal. change (zlength (@nil Z)) with 0. lia.
+ replace (INTMAX_MAX <? 2^64 + v) with true by (symmetry; apply Z.ltb_lt; unfold INTMAX_MAX; lia).
replace ((- (2^64 + v)) mod 2^64) with (- v).
2:{ rewrite <- (Z.mod_add (- (2^64 + v)) 1 (2^64)) by lia. replace (- (2^64 + v) + 1 * 2^64) with (- v) by lia. symmetry. apply Z.mod_small. lia. }
unfold int_pieces. cbn [andb]. replace (- v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
pose proof (PM_dec_digits_length (- v)) as L. pose proof (PM_dec_digits_pos (- v) ltac:(lia)) as NE.
assert (L1 : 1 <= zlength (QWHo.dec_digits (- v))).
{ unfold zlength in *. destruct (QWHo.dec_digits (- v)); [congruence| cbn [length]; lia]. }
rewrite Z.add_0_r. replace (Z.max (-1) (zlength (QWHo.dec_digits (- v)))) with (zlength (QWHo.dec_digits (- v))) by lia.
rewrite tail_pieces_plain; [| lia | lia | change (zlength [45]) with 1; lia | lia]. f_equal. f_equal. change (zlength [45]) with 1. lia.
Qed.

Lemma d_count_range : forall v, 1 <= d_count v <= 21.
Proof.
intros v. unfold d_count. destruct (v =? 0); [lia|].
destruct (Z.ltb_spec 0 v).
- pose proof (PM_dec_digits_length v). pose proof (PM_dec_digits_pos v ltac:(lia)) as NE.
unfold zlength in *. destruct (QWHo.dec_digits v); [congruence| cbn [length] in *; lia].
- pose proof (PM_dec_digits_length (- v)). unfold zlength in *. lia.
Qed.

Lemma ppl_unfold : forall fuel s args cnt,
printf_pieces_loop (S fuel) s args cnt =
match s with
| [] => None
| c :: _ =>
if c =? 0 then Some ([], cnt) else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => None
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
else if 0 <? l then
(if INT_MAX - cnt <? l then None
else match printf_pieces_loop fuel s1 args (cnt + l) with Some (ps, r) => Some (lit :: ps, r) | None => None end)
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match conv_pieces cnt d a with
| Some (ps1, cnt') =>
match printf_pieces_loop fuel s3 args' cnt' with Some (ps, r) => Some ([] :: ps1 ++ ps, r) | None => None end
| None => None
end
| _, _ => None
end
end
end.
Proof. reflexivity. Qed.

Lemma ppl_noargs_shift_gen : forall fuel s c0 ps r,
printf_pieces_loop fuel s [] c0 = Some (ps, r) ->
c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> printf_pieces_loop fuel s [] (c0 + k) = Some (ps, r + k)).
Proof.
induction fuel as [|fuel IH]; intros s c0 ps r P; [discriminate|].
rewrite ppl_unfold in P. setoid_rewrite ppl_unfold.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. split; [lia|]. intros k _ _. reflexivity. }
cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
pose proof (zlength_nonneg' lit).
destruct (0 <? zlength lit).
- destruct (Z.ltb_spec (INT_MAX - c0) (zlength lit)); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) [] (c0 + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. destruct (IH _ _ _ _ R) as [LE SH].
split; [lia|]. intros k Hk Hr.
replace (INT_MAX - (c0 + k) <? zlength lit) with false by (symmetry; apply Z.ltb_ge; lia).
replace (c0 + k + zlength lit) with (c0 + zlength lit + k) by lia. rewrite (SH k Hk Hr). reflexivity.
- destruct (parse_dir s2) as [[d s3]|]; discriminate.
Qed.

Lemma ppl_noargs_shift : forall fuel s cnt ps r,
printf_pieces_loop fuel s [] 0 = Some (ps, r) -> 0 <= cnt -> cnt + r <= INT_MAX ->
printf_pieces_loop fuel s [] cnt = Some (ps, cnt + r).
Proof.
intros fuel s cnt ps r P Hc Hr. destruct (ppl_noargs_shift_gen _ _ _ _ _ P) as [_ SH].
rewrite <- (Z.add_0_l cnt). rewrite (SH cnt Hc ltac:(lia)). f_equal. f_equal. lia.
Qed.

Ltac ppl_step := rewrite ppl_unfold; match goal with |- ?l = _ => let l' := eval cbv -[printf_pieces_loop conv_pieces] in l in change l with l' end.

Lemma printf_pieces_emit_d : forall v, -2^31 <= v < 2^31 ->
printf_pieces FMT_emit_d [PA_i v] = Some ([] :: d_pieces v ++ [[10]], d_count v + 1).
Proof.
intros v Hv. pose proof (d_count_range v) as R. unfold printf_pieces.
change (Datatypes.length FMT_emit_d) with 4%nat.
ppl_step.
match goal with |- context [conv_pieces ?c ?d ?a] => change (conv_pieces c d a) with (conv_pieces 0 DIR_d (PA_i v)) end.
rewrite conv_pieces_d by (unfold INT_MAX; lia). cbv beta iota.
rewrite (ppl_noargs_shift 3 [10; 0] (0 + d_count v) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
repeat f_equal; lia.
Qed.

Lemma d_pieces_emit : forall v, -2^31 <= v < 2^31 -> [] :: d_pieces v ++ [[10]] = pieces_emit_d v.
Proof.
intros v Hv. unfold d_pieces, pieces_emit_d. destruct (Z.eqb_spec v 0) as [->|NZ]; [reflexivity|].
assert (P20 : 2^31 < 10^20) by (cbn; lia).
destruct (Z.ltb_spec 0 v).
- rewrite PM_dec_digits_eq by lia. reflexivity.
- rewrite PM_dec_digits_eq by lia. reflexivity.
Qed.

Lemma pieces_emit_d_short : forall v, -2^31 <= v < 2^31 -> Forall (fun p => zlength p <= 21) (pieces_emit_d v).
Proof.
intros v Hv. rewrite <- d_pieces_emit by exact Hv. unfold d_pieces.
pose proof (PM_dec_digits_length v) as L1. pose proof (PM_dec_digits_length (- v)) as L2.
destruct (v =? 0); [| destruct (0 <? v)]; cbn [app];
repeat (apply Forall_cons; [unfold zlength in *; cbn [length]; lia |]); apply Forall_nil.
Qed.

Lemma conv_pieces_s : forall cnt s, 0 <= cnt -> zlength s < INT_MAX - cnt ->
conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |} (PA_s s)
= Some ([[]; s], cnt + zlength s).
Proof.
intros cnt s Hc Hs. pose proof (zlength_nonneg' s) as H0.
unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_PTR Pos.eqb andb Z.ltb Z.compare].
replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; lia).
unfold tail_pieces. cbv zeta. rewrite firstn_all2 by (unfold zlength; lia).
change (zlength (@nil Z)) with 0.
replace (Z.max (zlength s) (zlength s)) with (zlength s) by lia.
replace (INT_MAX - 0 <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.max 0 (0 + zlength s)) with (zlength s) by lia.
replace (INT_MAX - cnt <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
unfold pad_pieces.
replace (zlength s <=? 0 + zlength s) with true by (symmetry; apply Z.leb_le; lia).
rewrite Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ].
reflexivity.
Qed.

Lemma printf_pieces_usage : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_usage [PA_s s] = Some (pieces_usage s, 14 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_usage) with 17%nat.
ppl_step. ppl_step. change QWHo.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 15 [32; 73; 78; 80; 85; 84; 10; 0] (7 + zlength s) [[32; 73; 78; 80; 85; 84; 10]] 7 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_usage. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_cannot_open : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_cannot_open [PA_s s] = Some (pieces_cannot_open s, 18 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_cannot_open) with 21%nat.
ppl_step. ppl_step. change QWHo.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 19 [10; 0] (17 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_cannot_open. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_read_error : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_read_error [PA_s s] = Some (pieces_read_error s, 20 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_read_error) with 23%nat.
ppl_step. ppl_step. change QWHo.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 21 [10; 0] (19 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_read_error. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_too_big : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.

Lemma fp_calls_emit_d : forall v, fp_calls (Datatypes.length FMT_emit_d) FMT_emit_d [PA_i v] = [].
Proof. intros v. vm_compute. reflexivity. Qed.

End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import QCiC.Mq1. Import QoNr.Mq0.
Import QWHo.
Import ListNotations.
Open Scope Z_scope.

Lemma Zrange_forallb : forall (P : Z -> bool) (lo : Z) (n : nat),
forallb P (map (fun k => lo + Z.of_nat k) (seq 0 n)) = true ->
forall c, lo <= c < lo + Z.of_nat n -> P c = true.
Proof.
intros P lo n H c Hc. rewrite forallb_forall in H. apply H.
apply in_map_iff. exists (Z.to_nat (c - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Notation M64 := 18446744073709551615.

Lemma digit_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
Bool.eqb (Z.land (c + -48) M64 <=? 9) (is_digit c) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma digit_test : forall c, 0 <= c < 256 -> (Z.land (c + -48) M64 <= 9 <-> is_digit c = true).
Proof.
intros c Hc. pose proof (digit_testb c ltac:(cbn; lia)) as E.
destruct (Z.leb_spec0 (Z.land (c + -48) M64) 9); destruct (is_digit c); cbn in E; try discriminate.
all: split; intros; first [reflexivity | assumption | discriminate | lia].
Qed.
Lemma digit_range : forall c, is_digit c = true <-> 48 <= c <= 57.
Proof. intros c. unfold is_digit. rewrite andb_true_iff, !Z.leb_le. lia. Qed.

Lemma sp_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
Bool.eqb (Z.land (c + -32) M64 <? 32) ((32 <=? c) && (c <? 64)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma sp_test : forall c, 0 <= c < 256 -> (Z.land (c + -32) M64 < 32 <-> 32 <= c < 64).
Proof.
intros c Hc. pose proof (sp_testb c ltac:(cbn; lia)) as E.
destruct (Z.ltb_spec0 (Z.land (c + -32) M64) 32); destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in E; try discriminate; lia.
Qed.

Definition flagw (c : Z) : Z := Z.land (bv_swrap 32 (Z.shiftl 1 ((c + -32) mod 32))) M64.

Lemma flag_noneb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
Bool.eqb (Z.land (flagw c) 75913 =? 0) (match flag_bit c with None => true | Some _ => false end) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_none : forall c, 32 <= c < 64 -> (Z.land (flagw c) 75913 = 0 <-> flag_bit c = None).
Proof.
intros c Hc. pose proof (flag_noneb c ltac:(cbn; lia)) as E.
destruct (Z.eqb_spec (Z.land (flagw c) 75913) 0); destruct (flag_bit c); cbn in E; try discriminate.
all: split; intros; first [reflexivity | assumption | discriminate | congruence | lia].
Qed.
Lemma flag_someb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
match flag_bit c with None => true | Some b => (flagw c =? b) && (0 <=? b) && (b <? 131072) end = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_some : forall c b, 32 <= c < 64 -> flag_bit c = Some b -> flagw c = b /\ 0 <= b < 131072.
Proof.
intros c b Hc Hb. pose proof (flag_someb c ltac:(cbn; lia)) as E. rewrite Hb in E.
rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3]. apply Z.eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. lia.
Qed.
Lemma flag_bit_range : forall c, flag_bit c <> None -> 32 <= c < 64.
Proof.
intros c H. unfold flag_bit in H.
destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in H; try lia; exfalso; apply H; reflexivity.
Qed.

Lemma lor_bound17 : forall a b, 0 <= a < 131072 -> 0 <= b < 131072 -> 0 <= Z.lor a b < 131072.
Proof.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
change 131072 with (2^17) in *.
destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma parse_flags_cons_some : forall c s fl b, flag_bit c = Some b -> parse_flags (c :: s) fl = parse_flags s (Z.lor fl b).
Proof. intros c s fl b H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_cons_none : forall c s fl, flag_bit c = None -> parse_flags (c :: s) fl = (fl, c :: s).
Proof. intros c s fl H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_range : forall s fl, 0 <= fl < 131072 -> 0 <= fst (parse_flags s fl) < 131072.
Proof.
induction s as [|c s IH]; intros fl Hfl; cbn; [exact Hfl|].
destruct (flag_bit c) as [b|] eqn:E; [|exact Hfl].
apply IH. pose proof (flag_some c b (flag_bit_range c ltac:(congruence)) E) as [_ Hb]. apply lor_bound17; lia.
Qed.

Lemma getint_cons_digit : forall c s i, is_digit c = true ->
getint (c :: s) i = if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None else getint s (10 * i + (c - 48)).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_cons_nondigit : forall c s i, is_digit c = false -> getint (c :: s) i = Some (i, c :: s).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_some_range : forall s i w s', 0 <= i <= INT_MAX -> getint s i = Some (w, s') -> 0 <= w <= INT_MAX.
Proof.
induction s as [|c s IH]; intros i w s' Hi H; cbn [getint] in H.
- inversion H; subst. exact Hi.
- destruct (is_digit c) eqn:D.
+ destruct (214748364 <? i) eqn:E1; [discriminate|]. destruct (INT_MAX - 10 * i <? c - 48) eqn:E2; [discriminate|]. cbn in H.
apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. apply digit_range in D. unfold INT_MAX in *. eapply IH; [|exact H]. lia.
+ inversion H; subst. exact Hi.
Qed.

Lemma lxor_imax : forall x, 0 <= x <= 2147483647 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof.
intros x Hx. change 2147483647 with (Z.ones 31).
assert (E : Z.lxor x (Z.ones 31) = (Z.lnot x) mod 2^31).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 31).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; cbn in *; lia|lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^31)) with (2^31 - 1).
replace (Z.lnot x) with (-x - 1) by (unfold Z.lnot; lia).
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by (cbn in *; lia). lia.
Qed.

Lemma parse_dir_shape : forall s d rest, parse_dir s = Some (d, rest) ->
match s with c0 :: c0b :: _ => is_digit c0 && (c0b =? 36) = false | [c0] => is_digit c0 = false | [] => True end /\
let (fl, s1) := parse_flags s 0 in
d_fl d = fl /\
exists c1 s1b, s1 = c1 :: s1b /\ c1 <> 42 /\
exists s2, getint s1 0 = Some (d_w d, s2) /\
exists c2 s2b, s2 = c2 :: s2b /\
( (c2 <> 46 /\ d_p d = -1 /\ d_xp d = false /\ d_t d = c2 /\ rest = s2b /\ conv_type c2 = Some (d_ty d))
\/ (c2 = 46 /\ d_xp d = true /\ exists c3 s3b, s2b = c3 :: s3b /\ c3 <> 42 /\
exists s3, getint s2b 0 = Some (d_p d, s3) /\ s3 = d_t d :: rest /\ conv_type (d_t d) = Some (d_ty d)) ).
Proof.
intros s d rest H. unfold parse_dir in H.
split. { destruct s as [|c0 [|c0b s0]]; try exact I. { destruct (is_digit c0); [discriminate|reflexivity]. } destruct (is_digit c0 && (c0b =? 36)); [discriminate|reflexivity]. }
match type of H with (if ?pp then None else _) = _ => destruct pp; [discriminate|] end.
destruct (parse_flags s 0) as [fl s1].
destruct s1 as [|c1 s1b]; [discriminate|].
destruct (Z.eqb_spec c1 42) as [E42|N42]; [discriminate|].
destruct (getint (c1 :: s1b) 0) as [[w s2]|] eqn:G; [|discriminate].
destruct s2 as [|c2 s2b]; [discriminate|].
destruct (Z.eqb_spec c2 46) as [E46|N46].
- destruct s2b as [|c3 s3b]; [discriminate|]. destruct (Z.eqb_spec c3 42) as [E42'|N42']; [discriminate|].
destruct (getint (c3 :: s3b) 0) as [[p s3]|] eqn:G2; [|discriminate].
destruct s3 as [|t s4]; [discriminate|]. destruct (conv_type t) as [ty|] eqn:CT; [|discriminate].
injection H as <- <-. cbn. split; [reflexivity|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
exists (c2 :: c3 :: s3b). split; [first [reflexivity | exact G]|]. exists c2, (c3 :: s3b). split; [reflexivity|].
right. split; [exact E46|]. split; [reflexivity|]. exists c3, s3b. split; [reflexivity|]. split; [exact N42'|].
exists (t :: s4). split; [first [reflexivity | exact G2]|]. split; first [reflexivity | exact CT].
- destruct (conv_type c2) as [ty|] eqn:CT; [|discriminate]. injection H as <- <-. cbn.
split; [reflexivity|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
exists (c2 :: s2b). split; [first [reflexivity | exact G]|]. exists c2, s2b. split; [reflexivity|].
left. split; [exact N46|]. repeat split; first [reflexivity | exact CT].
Qed.

Lemma parse_flags_suffix : forall s acc fl s1, parse_flags s acc = (fl, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
induction s as [|c s IH]; intros acc fl s1 H; cbn in H.
- injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
- destruct (flag_bit c) as [b|].
+ destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
+ injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.
Lemma getint_suffix : forall s acc w s1, getint s acc = Some (w, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
induction s as [|c s IH]; intros acc w s1 H; cbn [getint] in H.
- injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
- destruct (is_digit c).
+ destruct (_ || _); [discriminate|]. destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
+ injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.

Definition STATES0 : list Z :=
[25; 0; 11; 0; 25; 25; 25; 0; 0; 0; 0; 5; 0; 0; 0; 0; 0; 0; 9; 0; 0; 0; 0; 11; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 10; 10; 25; 25; 25; 3; 10; 7; 0; 1; 27; 9; 11; 24; 0; 0; 9; 6; 11; 0; 0; 11; 0; 6].
Lemma conv_type_range : forall t ty, conv_type t = Some ty -> 65 <= t <= 122.
Proof.
intros t ty H. unfold conv_type in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [try (injection H as <-)|] end; try discriminate;
repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end; try lia.
Qed.
Lemma states0_conv : forall t ty, conv_type t = Some ty -> znth STATES0 (t - 65) = ty.
Proof.
intros t ty H. unfold conv_type in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [injection H as <-|] end; try discriminate;
repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E; subst; reflexivity | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end.
Qed.

Definition conv_target (t : Z) : Z :=
if t =? 115 then 0x235b8
else if (t =? 100) || (t =? 105) then 0x23570
else if t =? 117 then 0x236a8
else if (t =? 120) || (t =? 88) then 0x23720
else 0x23520.

Lemma conv_type_ty : forall t ty, conv_type t = Some ty -> ty = 9 \/ ty = 10 \/ ty = 11 \/ ty = 25.
Proof.
intros t ty H. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c; [injection H as <-; lia|] end. discriminate.
Qed.

Lemma land_M64_neg : forall x, - 2^64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2^64.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma nzmask_bits : forall n, 0 <= n < 0 + Z.of_nat 64 -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma nzmask_eq : forall fl, 0 <= fl < 131072 -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof.
intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases n 64).
- pose proof (nzmask_bits n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
- replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
Qed.
Lemma land_bound : forall a m, 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
Proof.
intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
pose proof (Z.sub_land_same_l a m) as E.
assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha).
lia.
Qed.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.

Import QdTa Q0z1.
Open Scope Z_scope.

Module RL.
Import Ltac2.
Ltac2 ops () : constr list :=
[constr:(Z.add); constr:(Z.sub); constr:(Z.mul); constr:(Z.opp); constr:(Z.succ); constr:(Z.pred);
constr:(Z.le); constr:(Z.lt); constr:(Z.ge); constr:(Z.gt); constr:(@eq); constr:(and); constr:(or);
constr:(not); constr:(iff); constr:(Z.div); constr:(Z.modulo); constr:(Z.of_nat); constr:(Z.to_nat);
constr:(Z.min); constr:(Z.max); constr:(Z.pow);

constr:(Nat.add); constr:(Nat.sub); constr:(Nat.mul); constr:(Nat.div); constr:(Nat.modulo); constr:(Nat.pred);
constr:(Nat.min); constr:(Nat.max); constr:(N.add); constr:(N.sub); constr:(N.mul); constr:(N.of_nat); constr:(N.to_nat);
constr:(Z.of_N); constr:(Z.to_N); constr:(Z.abs); constr:(Z.quot); constr:(Z.rem)].
Ltac2 rec add_atom (c : constr) (acc : constr list) : constr list :=
if List.exist (Constr.equal c) acc then acc else c :: acc.

Ltac2 rec atoms (ops : constr list) (acc : constr list) (c : constr) : constr list :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f args =>
if List.exist (Constr.equal f) ops then Array.fold_left (atoms ops) acc args
else
match Constr.Unsafe.kind f with

| Constr.Unsafe.Constructor _ _ => Array.fold_left (atoms ops) acc args
| Constr.Unsafe.Ind _ _ => Array.fold_left (atoms ops) acc args
| _ => add_atom c acc
end
| Constr.Unsafe.Var _ => add_atom c acc
| Constr.Unsafe.Constant _ _ => add_atom c acc
| Constr.Unsafe.Prod b body => atoms ops (atoms ops acc (Constr.Binder.type b)) body
| Constr.Unsafe.Cast c _ _ => atoms ops acc c
| _ => acc
end.
Ltac2 rec meets (xs : constr list) (ys : constr list) : bool :=
match xs with
| [] => false
| x :: xs' => if List.exist (Constr.equal x) ys then true else meets xs' ys
end.

Ltac2 hop (ops : constr list) (g : constr list) : constr list :=
let sfh := constr:(sf_hide) in
List.fold_left (fun g h => let (id, body, ty) := h in
match body with
| Some _ => g
| None =>
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args =>
if Constr.equal f sfh then
let p := Array.get args 0 in
let ap := atoms ops [] p in
if meets ap g then
(ltac1:(h |- unfold sf_hide in h) (Ltac1.of_ident id);
List.fold_left (fun g a => add_atom a g) g ap)
else g
else g
| _ => g
end
end) g (Control.hyps ()).
Ltac2 unhide_rel () : unit :=
let ops := ops () in
let g := atoms ops [] (Control.goal ()) in
let g := hop ops g in
let _ := hop ops g in ().
Ltac sf_unhide_rel_atoms := ltac2:(Control.enter unhide_rel).

Ltac2 hid (ty : constr) : constr option :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args => if Constr.equal f constr:(sf_hide) then Some (Array.get args 0) else None
| _ => None
end.
Ltac2 is_local (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
Ltac2 rel_prune () : unit :=
let ops := ops () in
let hs := Control.hyps () in

let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None =>
if is_local id then
match hid ty with
| Some p => if SF2.arith_logic p then Some (id, p, true, false) else None
| None => if SF2.arith_logic ty then Some (id, ty, false, SF2.plain_arith false ty) else None
end
else None
end) hs in
let step g := List.fold_left (fun g f => let (_, p, _, _) := f in
let ap := atoms ops [] p in if meets ap g then List.fold_left (fun g a => add_atom a g) g ap else g) g facts in
let g := step (step (atoms ops [] (Control.goal ()))) in
let drop := List.map_filter (fun f => let (id, p, hidden, plain) := f in
if plain then None else if meets (atoms ops [] p) g then None else Some id) facts in
(match drop with [] => () | _ :: _ => Std.clear drop end);
List.iter (fun f => let (id, p, hidden, _) := f in
if hidden then (if meets (atoms ops [] p) g then ltac1:(h |- unfold sf_hide in h) (Ltac1.of_ident id) else ()) else ()) facts.
Ltac zify_prune_rel_atoms := ltac2:(Control.enter rel_prune).

Ltac2 rel_prune_all (hops : int) : unit :=
let ops := ops () in
let hs := Control.hyps () in
let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None =>
if is_local id then
match hid ty with
| Some p => if SF2.arith_logic p then Some (id, p, true) else None
| None => if SF2.arith_logic ty then Some (id, ty, false) else None
end
else None
end) hs in
let step g := List.fold_left (fun g f => let (_, p, _) := f in
let ap := atoms ops [] p in if meets ap g then List.fold_left (fun g a => add_atom a g) g ap else g) g facts in
let rec close n g := if Int.equal n 0 then g else close (Int.sub n 1) (step g) in
let g := close hops (atoms ops [] (Control.goal ())) in
let drop := List.map_filter (fun f => let (id, p, _) := f in if meets (atoms ops [] p) g then None else Some id) facts in
(match drop with [] => () | _ :: _ => Std.clear drop end);
List.iter (fun f => let (id, p, hidden) := f in
if hidden then (if meets (atoms ops [] p) g then ltac1:(h |- unfold sf_hide in h) (Ltac1.of_ident id) else ()) else ()) facts.
Ltac zify_prune_rel_all1 := ltac2:(Control.enter (fun () => rel_prune_all 1)).

Ltac2 rel_prune_h (hops : int) : unit :=
let ops := ops () in
let hs := Control.hyps () in
let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None =>
if is_local id then
match hid ty with
| Some p => if SF2.arith_logic p then Some (id, p, true, false) else None
| None => if SF2.arith_logic ty then Some (id, ty, false, SF2.plain_arith false ty) else None
end
else None
end) hs in

let step g := List.fold_left (fun acc f => let (_, p, _, _) := f in
let ap := atoms ops [] p in if meets ap g then List.fold_left (fun acc a => add_atom a acc) acc ap else acc) g facts in
let rec close n g := if Int.equal n 0 then g else close (Int.sub n 1) (step g) in

let g0 := atoms ops [] (Control.goal ()) in
let g0 := match g0 with
| [] => List.fold_left (fun g f => let (_, p, _, _) := f in List.fold_left (fun g a => add_atom a g) g (atoms ops [] p))
[] (List.firstn (if Int.le (List.length facts) 4 then List.length facts else 4) (List.rev facts))
| _ :: _ => g0
end in
let g := close hops g0 in
let drop := List.map_filter (fun f => let (id, p, hidden, plain) := f in
if plain then None else if meets (atoms ops [] p) g then None else Some id) facts in
(match drop with [] => () | _ :: _ => Std.clear drop end);
List.iter (fun f => let (id, p, hidden, _) := f in
if hidden then (if meets (atoms ops [] p) g then ltac1:(h |- unfold sf_hide in h) (Ltac1.of_ident id) else ()) else ()) facts.
Ltac zify_prune_rel_h0 := ltac2:(Control.enter (fun () => rel_prune_h 0)).
Ltac zify_prune_rel_h1 := ltac2:(Control.enter (fun () => rel_prune_h 1)).
Ltac zify_prune_rel_h2 := ltac2:(Control.enter (fun () => rel_prune_h 2)).

Ltac2 ctx_small (k : int) : unit :=
if Int.le (List.length (Control.hyps ())) k then () else Control.zero (Tactic_failure None).
Ltac ctx_small40 := ltac2:(Control.enter (fun () => ctx_small 40)).
End RL.
Ltac sf_unhide_rel_atoms := RL.sf_unhide_rel_atoms.
Ltac zify_prune_rel_atoms := RL.zify_prune_rel_atoms.
Ltac zify_prune_rel_all1 := RL.zify_prune_rel_all1.
Ltac zify_prune_rel_h0 := RL.zify_prune_rel_h0.
Ltac zify_prune_rel_h1 := RL.zify_prune_rel_h1.
Ltac zify_prune_rel_h2 := RL.zify_prune_rel_h2.
Ltac ctx_small40 := RL.ctx_small40.
Ltac lia_rel := Qo9G.term_slim ltac:(zify_prune_rel_atoms; Zify.zify; xlia zchecker).

Ltac lia_rel0 := Qo9G.term_slim ltac:(zify_prune_rel_all1; Zify.zify; xlia zchecker).

Ltac lia_relh0 := Qo9G.term_slim ltac:(zify_prune_rel_h0; Zify.zify; xlia zchecker).
Ltac lia_relh1 := Qo9G.term_slim ltac:(zify_prune_rel_h1; Zify.zify; xlia zchecker).
Ltac lia_relh2 := Qo9G.term_slim ltac:(zify_prune_rel_h2; Zify.zify; xlia zchecker).

Ltac tlia_rel := first [ Qo9G.term_slim ltac:(zify_prune_plain; Zify.zify; xlia zchecker) | lia_relh0 | lia_relh1 ].

Ltac lia_walk := first [ Qo9G.term_slim ltac:(zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune; Zify.zify; xlia zchecker)
| lia_relh0
| lia_rel
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Ltac lia_walk_nf := first [ Qo9G.term_slim ltac:(zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(ctx_small40; Zify.zify; xlia zchecker)
| lia_relh0
| lia_relh1
| lia_relh2 ].

Ltac tslia_rel := first [ exact I | repeat match goal with |- _ /\ _ => split end; first [ exact I | tlia_rel ] ].
End Mq4.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qs9x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qs9x. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma impl_post_evt : forall segs {node R} (atn : node -> machine_state -> Prop) (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
Qc6I.impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> Qc6I.impl segs atn t Q' ms.
Proof.
intros segs node R atn t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. exact (HQ r).
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
Qed.
Lemma implM_post_evt : forall segs {St A} (c : M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
Qpj5.Mq1.implM segs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt segs (Q' a s') ms') -> Qpj5.Mq1.implM segs c s Q' ms.
Proof.
intros segs St A c s Q Q' ms H HQ. unfold Qpj5.Mq1.implM in *. eapply impl_post_evt; [exact H|].
intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I | apply HQ].
Qed.

Section Outs.
Variable segs : list Segment.
Context {St : Type}.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
Local Notation implM := (Qpj5.Mq1.implM segs).

Fixpoint outsk {B} (ps : list (list Z)) (k : M St B) : M St B :=
match ps with
| [] => k
| p :: ps' => OUT p ;;; outsk ps' k
end.

Lemma outsk_app : forall {B} ps qs (k : M St B), outsk (ps ++ qs) k = outsk ps (outsk qs k).
Proof. induction ps as [|p ps IH]; intros qs k; [reflexivity|]. cbn [outsk app]. rewrite IH. reflexivity. Qed.

Lemma outsk_mono : forall {B} ps (k1 k2 : M St B) Q,
(forall s ms, implM k1 s Q ms -> implM k2 s Q ms) ->
forall s ms, implM (outsk ps k1) s Q ms -> implM (outsk ps k2) s Q ms.
Proof.
induction ps as [|p ps IH]; intros k1 k2 Q HK s ms H; cbn [outsk] in *; [apply HK; exact H|].
eapply implM_bind_ext; [|exact H]. intros x s' ms' H'. eapply IH; [exact HK | exact H'].
Qed.

Lemma mpad_outs : forall {B} c w l fl pp (K : unit -> M St B) s Q ms,
pad_pieces c w l fl = Some pp ->
implM (mbind (mpad OUT c w l fl) K) s Q ms -> implM (outsk pp (K tt)) s Q ms.
Proof.
intros B c w l fl pp K s Q ms P H. unfold mpad, pad_pieces in *.
destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
- inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H.
- destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [outsk].
eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'.
Qed.

Lemma conv_tail_outs : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B) s Q ms,
tail_pieces cnt fl w p prefix body = Some (ps, r) ->
implM (mbind (conv_tail OUT cnt fl w p prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt fl w p prefix body ps r K s Q ms T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta in H.
destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
inversion T; subst. clear T.
match goal with |- implM (outsk ?L (K ?rr)) _ _ _ =>
replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
by (rewrite ?outsk_app; cbn [outsk]; rewrite ?outsk_app; cbn [outsk]; reflexivity) end.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P1) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s1 ms1 H.
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x2 s2 ms2 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P2) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s3 ms3 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P3) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s4 ms4 H.
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x5 s5 ms5 H.
apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P4) in H. cbv beta in H.
eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s6 ms6 H.
apply implM_ret_l_rev in H. exact H.
Qed.

Lemma conv_int_outs : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B) s Q ms,
int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
implM (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt fl w p xp argi prefix body ps r K s Q ms T H. unfold conv_int, int_pieces in *.
destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta in H.
destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outs; eassumption.
Qed.

Lemma conv_outs : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
conv_pieces cnt d a = Some (ps, r) ->
implM (mbind (conv OUT OUTFP cnt d a) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
Proof.
intros B cnt d a ps r K s Q ms T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta in H.
destruct a as [str|i|u|dd].
- destruct (negb (d_ty d =? T_PTR)); [discriminate|].
destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
eapply conv_tail_outs; eassumption.
- destruct (negb (d_ty d =? T_INT)); [discriminate|].
destruct (INTMAX_MAX <? i mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_outs; eassumption.
- destruct (negb (d_ty d =? T_UINT)); [discriminate|].
destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
- discriminate.
Qed.

Lemma printf_loop_outs : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
printf_pieces_loop fuel s args cnt = Some (ps, r) ->
implM (mbind (printf_loop OUT OUTFP fuel s args cnt) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
Proof.
induction fuel as [|fuel IH]; intros s args cnt ps r k st Q ms P H; [discriminate|].
cbn [printf_pieces_loop] in P. cbn [printf_loop] in H.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H. }
cbv zeta in P. cbv zeta in H. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
destruct (0 <? zlength lit).
- destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. cbn [outsk].
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
eapply IH; [exact R | exact H'].
- destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
inversion P; subst. clear P.
match goal with |- implM (outsk ?L (k ?rr)) _ _ _ =>
replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
cbn [outsk].
apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
apply implM_assoc_rev in H'. apply (conv_outs _ _ _ _ _ _ _ _ _ C) in H'.
eapply outsk_mono; [|exact H']. cbv beta. intros s'' ms'' H''. eapply IH; [exact R | exact H''].
Qed.

Theorem printf_model_outs : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
printf_pieces fmt args = Some (ps, r) ->
implM (mbind (printf_model OUT OUTFP fmt args) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
Proof. intros B fmt args ps r k st Q ms P H. eapply printf_loop_outs; [exact P | exact H]. Qed.
End Outs.

Ltac lhs_cbvs := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces] in l in change l with l' end.
Lemma zlength_nonneg' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma digits_aux_nil : forall f acc, digits_aux f 10 (fun v => 48 + v) 0 acc = acc.
Proof. intros [|f] acc; reflexivity. Qed.

Lemma digits_aux_dec : forall f x acc, 0 < x < 10 ^ Z.of_nat f ->
digits_aux f 10 (fun v => 48 + v) x acc = dec_digits_fuel f x ++ acc.
Proof.
induction f as [|f IH]; intros x acc Hx.
- cbn in Hx. lia.
- cbn [digits_aux dec_digits_fuel]. replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
destruct (Z.ltb_spec x 10) as [LT|GE].
+ rewrite Z.div_small by lia. rewrite digits_aux_nil. rewrite Z.mod_small by lia. reflexivity.
+ rewrite IH by (split; [apply Z.div_str_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite <- app_assoc. reflexivity.
Qed.

Lemma PM_dec_digits_eq : forall x, 0 < x < 10 ^ 20 -> Qs9x.dec_digits x = QdZp.dec_digits x.
Proof.
intros x Hx. unfold Qs9x.dec_digits, QdZp.dec_digits.
rewrite digits_aux_dec by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; exact Hx). apply app_nil_r.
Qed.

Lemma digits_aux_length : forall f b d x acc, (length (digits_aux f b d x acc) <= f + length acc)%nat.
Proof.
induction f as [|f IH]; intros b d x acc; cbn [digits_aux]; [lia|].
destruct (x =? 0); [cbn; lia|]. specialize (IH b d (x / b) (d (x mod b) :: acc)). cbn [length] in IH. lia.
Qed.
Lemma PM_dec_digits_length : forall x, zlength (Qs9x.dec_digits x) <= 20.
Proof. intros x. unfold zlength, Qs9x.dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v) x []) as H. cbn [length Nat.add] in H. lia. Qed.

Lemma digits_aux_ne : forall f b d y acc, acc <> [] -> digits_aux f b d y acc <> [].
Proof. induction f as [|f IH]; intros b d y acc H; cbn [digits_aux]; [exact H|]. destruct (y =? 0); [exact H|]. apply IH. discriminate. Qed.
Lemma digits_aux_S : forall f b d x acc,
digits_aux (S f) b d x acc = if x =? 0 then acc else digits_aux f b d (x / b) (d (x mod b) :: acc).
Proof. reflexivity. Qed.
Lemma PM_dec_digits_pos : forall x, 0 < x -> Qs9x.dec_digits x <> [].
Proof.
intros x Hx. unfold Qs9x.dec_digits. change 20%nat with (S 19). rewrite digits_aux_S.
replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply digits_aux_ne. discriminate.
Qed.

Definition DIR_d : dir := {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |}.

Definition d_pieces (v : Z) : list (list Z) :=
if v =? 0 then [[]; [48]; []]
else if 0 <? v then [[]; Qs9x.dec_digits v]
else [[45]; Qs9x.dec_digits (- v)].
Definition d_count (v : Z) : Z :=
if v =? 0 then 1
else if 0 <? v then zlength (Qs9x.dec_digits v)
else 1 + zlength (Qs9x.dec_digits (- v)).

Lemma tail_pieces_plain : forall cnt prefix body, 0 <= cnt -> cnt + 25 <= INT_MAX ->
zlength prefix <= 2 -> 1 <= zlength body <= 20 ->
tail_pieces cnt 0 0 (zlength body) prefix body = Some ([prefix; body], cnt + zlength prefix + zlength body).
Proof.
intros cnt prefix body Hc Hc2 Hp Hb. pose proof (zlength_nonneg' prefix) as P0. unfold tail_pieces. cbv zeta.
rewrite Z.max_id.
replace (INT_MAX - zlength prefix <? zlength body) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX in *; lia).
replace (Z.max 0 (zlength prefix + zlength body)) with (zlength prefix + zlength body) by lia.
replace (INT_MAX - cnt <? zlength prefix + zlength body) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX in *; lia).
unfold pad_pieces. rewrite !Z.leb_refl, !orb_true_r. cbn [app]. f_equal. f_equal. lia.
Qed.

Lemma tail_pieces_zero : forall cnt, 0 <= cnt -> cnt + 25 <= INT_MAX ->
tail_pieces cnt 0 0 1 [] [] = Some ([[]; [48]; []], cnt + 1).
Proof.
intros cnt Hc Hc2. unfold tail_pieces. cbv zeta. change (zlength (@nil Z)) with 0.
change (Z.max 1 0) with 1. change (INT_MAX - 0 <? 1) with false. change (Z.max 0 (0 + 1)) with 1.
replace (INT_MAX - cnt <? 1) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX in *; lia).
reflexivity.
Qed.

Lemma conv_pieces_d : forall cnt v, 0 <= cnt -> cnt + 25 <= INT_MAX -> -2^31 <= v < 2^31 ->
conv_pieces cnt DIR_d (PA_i v) = Some (d_pieces v, cnt + d_count v).
Proof.
intros cnt v Hc Hc2 Hv. unfold d_pieces, d_count.
destruct (Z.eqb_spec v 0) as [->|NZ].
{ change (conv_pieces cnt DIR_d (PA_i 0)) with (tail_pieces cnt 0 0 1 [] []). apply tail_pieces_zero; assumption. }
unfold conv_pieces, DIR_d. cbn [d_fl d_w d_p d_xp d_t d_ty].
change (Z.land 0 LEFT_ADJ =? 0) with true. change (negb (T_INT =? T_INT)) with false. cbv iota.
change (Z.land 0 MARK_POS =? 0) with true. change (Z.land 0 PAD_POS =? 0) with true. cbn [negb].
assert (E64 : v mod 2^64 = (if 0 <? v then v else 2^64 + v)).
{ destruct (Z.ltb_spec 0 v). { apply Z.mod_small. lia. }
rewrite <- (Z.mod_add v 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia. }
rewrite E64. clear E64. destruct (Z.ltb_spec 0 v) as [POS|NEG].
+ replace (INTMAX_MAX <? v) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
unfold int_pieces. cbn [andb]. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
pose proof (PM_dec_digits_length v) as L. pose proof (PM_dec_digits_pos v POS) as NE.
assert (L1 : 1 <= zlength (Qs9x.dec_digits v)).
{ unfold zlength in *. destruct (Qs9x.dec_digits v); [congruence| cbn [length]; lia]. }
rewrite Z.add_0_r. replace (Z.max (-1) (zlength (Qs9x.dec_digits v))) with (zlength (Qs9x.dec_digits v)) by lia.
rewrite tail_pieces_plain; [| lia | lia | change (zlength (@nil Z)) with 0; lia | lia]. f_equal. f_equal. change (zlength (@nil Z)) with 0. lia.
+ replace (INTMAX_MAX <? 2^64 + v) with true by (symmetry; apply Z.ltb_lt; unfold INTMAX_MAX; lia).
replace ((- (2^64 + v)) mod 2^64) with (- v).
2:{ rewrite <- (Z.mod_add (- (2^64 + v)) 1 (2^64)) by lia. replace (- (2^64 + v) + 1 * 2^64) with (- v) by lia. symmetry. apply Z.mod_small. lia. }
unfold int_pieces. cbn [andb]. replace (- v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
pose proof (PM_dec_digits_length (- v)) as L. pose proof (PM_dec_digits_pos (- v) ltac:(lia)) as NE.
assert (L1 : 1 <= zlength (Qs9x.dec_digits (- v))).
{ unfold zlength in *. destruct (Qs9x.dec_digits (- v)); [congruence| cbn [length]; lia]. }
rewrite Z.add_0_r. replace (Z.max (-1) (zlength (Qs9x.dec_digits (- v)))) with (zlength (Qs9x.dec_digits (- v))) by lia.
rewrite tail_pieces_plain; [| lia | lia | change (zlength [45]) with 1; lia | lia]. f_equal. f_equal. change (zlength [45]) with 1. lia.
Qed.

Lemma d_count_range : forall v, 1 <= d_count v <= 21.
Proof.
intros v. unfold d_count. destruct (v =? 0); [lia|].
destruct (Z.ltb_spec 0 v).
- pose proof (PM_dec_digits_length v). pose proof (PM_dec_digits_pos v ltac:(lia)) as NE.
unfold zlength in *. destruct (Qs9x.dec_digits v); [congruence| cbn [length] in *; lia].
- pose proof (PM_dec_digits_length (- v)). unfold zlength in *. lia.
Qed.

Lemma ppl_unfold : forall fuel s args cnt,
printf_pieces_loop (S fuel) s args cnt =
match s with
| [] => None
| c :: _ =>
if c =? 0 then Some ([], cnt) else
let lit := lit_run s in
let l := zlength lit in
let s1 := skipn (Datatypes.length lit) s in
match s1 with
| [] => None
| c1 :: s2 =>
if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
else if 0 <? l then
(if INT_MAX - cnt <? l then None
else match printf_pieces_loop fuel s1 args (cnt + l) with Some (ps, r) => Some (lit :: ps, r) | None => None end)
else
match parse_dir s2, args with
| Some (d, s3), a :: args' =>
match conv_pieces cnt d a with
| Some (ps1, cnt') =>
match printf_pieces_loop fuel s3 args' cnt' with Some (ps, r) => Some ([] :: ps1 ++ ps, r) | None => None end
| None => None
end
| _, _ => None
end
end
end.
Proof. reflexivity. Qed.

Lemma ppl_noargs_shift_gen : forall fuel s c0 ps r,
printf_pieces_loop fuel s [] c0 = Some (ps, r) ->
c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> printf_pieces_loop fuel s [] (c0 + k) = Some (ps, r + k)).
Proof.
induction fuel as [|fuel IH]; intros s c0 ps r P; [discriminate|].
rewrite ppl_unfold in P. setoid_rewrite ppl_unfold.
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. split; [lia|]. intros k _ _. reflexivity. }
cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
pose proof (zlength_nonneg' lit).
destruct (0 <? zlength lit).
- destruct (Z.ltb_spec (INT_MAX - c0) (zlength lit)); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) [] (c0 + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. destruct (IH _ _ _ _ R) as [LE SH].
split; [lia|]. intros k Hk Hr.
replace (INT_MAX - (c0 + k) <? zlength lit) with false by (symmetry; apply Z.ltb_ge; lia).
replace (c0 + k + zlength lit) with (c0 + zlength lit + k) by lia. rewrite (SH k Hk Hr). reflexivity.
- destruct (parse_dir s2) as [[d s3]|]; discriminate.
Qed.

Lemma ppl_noargs_shift : forall fuel s cnt ps r,
printf_pieces_loop fuel s [] 0 = Some (ps, r) -> 0 <= cnt -> cnt + r <= INT_MAX ->
printf_pieces_loop fuel s [] cnt = Some (ps, cnt + r).
Proof.
intros fuel s cnt ps r P Hc Hr. destruct (ppl_noargs_shift_gen _ _ _ _ _ P) as [_ SH].
rewrite <- (Z.add_0_l cnt). rewrite (SH cnt Hc ltac:(lia)). f_equal. f_equal. lia.
Qed.

Ltac ppl_step := rewrite ppl_unfold; match goal with |- ?l = _ => let l' := eval cbv -[printf_pieces_loop conv_pieces] in l in change l with l' end.

Lemma printf_pieces_emit_d : forall v, -2^31 <= v < 2^31 ->
printf_pieces FMT_emit_d [PA_i v] = Some ([] :: d_pieces v ++ [[10]], d_count v + 1).
Proof.
intros v Hv. pose proof (d_count_range v) as R. unfold printf_pieces.
change (Datatypes.length FMT_emit_d) with 4%nat.
ppl_step.
match goal with |- context [conv_pieces ?c ?d ?a] => change (conv_pieces c d a) with (conv_pieces 0 DIR_d (PA_i v)) end.
rewrite conv_pieces_d by (unfold INT_MAX; lia). cbv beta iota.
rewrite (ppl_noargs_shift 3 [10; 0] (0 + d_count v) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
repeat f_equal; lia.
Qed.

Lemma d_pieces_emit : forall v, -2^31 <= v < 2^31 -> [] :: d_pieces v ++ [[10]] = pieces_emit_d v.
Proof.
intros v Hv. unfold d_pieces, pieces_emit_d. destruct (Z.eqb_spec v 0) as [->|NZ]; [reflexivity|].
assert (P20 : 2^31 < 10^20) by (cbn; lia).
destruct (Z.ltb_spec 0 v).
- rewrite PM_dec_digits_eq by lia. reflexivity.
- rewrite PM_dec_digits_eq by lia. reflexivity.
Qed.

Lemma pieces_emit_d_short : forall v, -2^31 <= v < 2^31 -> Forall (fun p => zlength p <= 21) (pieces_emit_d v).
Proof.
intros v Hv. rewrite <- d_pieces_emit by exact Hv. unfold d_pieces.
pose proof (PM_dec_digits_length v) as L1. pose proof (PM_dec_digits_length (- v)) as L2.
destruct (v =? 0); [| destruct (0 <? v)]; cbn [app];
repeat (apply Forall_cons; [unfold zlength in *; cbn [length]; lia |]); apply Forall_nil.
Qed.

Lemma conv_pieces_s : forall cnt s, 0 <= cnt -> zlength s < INT_MAX - cnt ->
conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |} (PA_s s)
= Some ([[]; s], cnt + zlength s).
Proof.
intros cnt s Hc Hs. pose proof (zlength_nonneg' s) as H0.
unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_PTR Pos.eqb andb Z.ltb Z.compare].
replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; lia).
unfold tail_pieces. cbv zeta. rewrite firstn_all2 by (unfold zlength; lia).
change (zlength (@nil Z)) with 0.
replace (Z.max (zlength s) (zlength s)) with (zlength s) by lia.
replace (INT_MAX - 0 <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.max 0 (0 + zlength s)) with (zlength s) by lia.
replace (INT_MAX - cnt <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
unfold pad_pieces.
replace (zlength s <=? 0 + zlength s) with true by (symmetry; apply Z.leb_le; lia).
rewrite Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ].
reflexivity.
Qed.

Lemma printf_pieces_usage : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_usage [PA_s s] = Some (pieces_usage s, 14 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_usage) with 17%nat.
ppl_step. ppl_step. change Qs9x.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 15 [32; 73; 78; 80; 85; 84; 10; 0] (7 + zlength s) [[32; 73; 78; 80; 85; 84; 10]] 7 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_usage. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_cannot_open : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_cannot_open [PA_s s] = Some (pieces_cannot_open s, 18 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_cannot_open) with 21%nat.
ppl_step. ppl_step. change Qs9x.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 19 [10; 0] (17 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_cannot_open. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_read_error : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FMT_read_error [PA_s s] = Some (pieces_read_error s, 20 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FMT_read_error) with 23%nat.
ppl_step. ppl_step. change Qs9x.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 21 [10; 0] (19 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_read_error. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_too_big : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.

Lemma fp_calls_emit_d : forall v, fp_calls (Datatypes.length FMT_emit_d) FMT_emit_d [PA_i v] = [].
Proof. intros v. vm_compute. reflexivity. Qed.

