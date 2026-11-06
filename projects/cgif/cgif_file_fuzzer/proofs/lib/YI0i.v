(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition cbb_chunk (BL : list Z) (k : nat) : list Z := 255 :: firstn 255 (skipn (255 * k) BL).
Definition cbb_prefix (BL : list Z) (i : nat) : list Z := concat (map (cbb_chunk BL) (seq 0 i)).
Definition cbb_tail (BL : list Z) (q : nat) : list Z :=
match skipn (255 * q) BL with [] => [0] | rest => Z.of_nat (length rest) :: rest ++ [0] end.
Lemma cbb_prefix_S : forall BL i, cbb_prefix BL (S i) = cbb_prefix BL i ++ cbb_chunk BL i.
Proof. intros BL i. unfold cbb_prefix. rewrite seq_S, map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.
Lemma cbb_chunk_length : forall BL k, (255 * S k <= length BL)%nat -> length (cbb_chunk BL k) = 256%nat.
Proof. intros BL k H. unfold cbb_chunk. cbn [length]. rewrite length_firstn, length_skipn. lia. Qed.
Lemma cbb_prefix_length : forall BL i, (255 * i <= length BL)%nat -> length (cbb_prefix BL i) = (256 * i)%nat.
Proof.
intros BL i. induction i as [|i IH]; intros H; [reflexivity|]. rewrite cbb_prefix_S, length_app, IH, cbb_chunk_length by lia. lia.
Qed.
Lemma cbb_chunk_shift : forall BL k, cbb_chunk BL (S k) = cbb_chunk (skipn 255 BL) k.
Proof. intros BL k. unfold cbb_chunk. rewrite skipn_skipn. do 3 f_equal. lia. Qed.
Lemma cbb_prefix_shift : forall BL i, cbb_prefix BL (S i) = cbb_chunk BL 0 ++ cbb_prefix (skipn 255 BL) i.
Proof.
intros BL i. unfold cbb_prefix. cbn [seq map concat]. f_equal. rewrite <- seq_shift, map_map. f_equal.
apply map_ext. intros k. apply cbb_chunk_shift.
Qed.
Lemma cbb_tail_shift : forall BL q, cbb_tail BL (S q) = cbb_tail (skipn 255 BL) q.
Proof. intros BL q. unfold cbb_tail. rewrite skipn_skipn. replace (255 * S q)%nat with (255 * q + 255)%nat by lia. reflexivity. Qed.
Lemma blocks255_nil : forall fuel, blocks255 fuel [] = [0].
Proof. intros [|f]; reflexivity. Qed.
Lemma blocks255_split : forall q BL fuel, (255 * q <= length BL)%nat -> (length BL - 255 * q < 255)%nat -> (q < fuel)%nat ->
blocks255 fuel BL = cbb_prefix BL q ++ cbb_tail BL q.
Proof.
induction q as [|q IH]; intros BL fuel Hq Hr Hf; (destruct fuel as [|f]; [lia|]).
- cbn [cbb_prefix seq map concat app]. unfold cbb_tail. cbn [Nat.mul skipn]. replace (255 * 0)%nat with 0%nat by lia. cbn [skipn].
destruct BL as [|x r]; [reflexivity|]. cbn [blocks255].
rewrite firstn_all2 by lia. rewrite skipn_all2 by lia. rewrite blocks255_nil. reflexivity.
- rewrite cbb_prefix_shift, cbb_tail_shift, <- app_assoc. rewrite <- (IH (skipn 255 BL) f); [| rewrite length_skipn; lia | rewrite length_skipn; lia | lia].
destruct BL as [|x r]; [cbn in Hq; lia|]. cbn [blocks255]. unfold cbb_chunk. replace (255 * 0)%nat with 0%nat by lia. cbn [skipn].
rewrite length_firstn. replace (Init.Nat.min 255 (length (x :: r))) with 255%nat by lia. reflexivity.
Qed.
Lemma blocks255_qrZ : forall BL q r, Z.of_nat (length BL) = 255 * q + r -> 0 <= q -> 0 <= r < 255 ->
blocks255 (S (length BL)) BL = cbb_prefix BL (Z.to_nat q) ++ (if r =? 0 then [0] else r :: skipn (255 * Z.to_nat q) BL ++ [0]) /\
Z.of_nat (length (blocks255 (S (length BL)) BL)) = 256 * q + (if r =? 0 then 1 else r + 2) /\
length (skipn (255 * Z.to_nat q) BL) = Z.to_nat r.
Proof.
intros BL q r Hlen Hq Hr.
assert (Hsk : length (skipn (255 * Z.to_nat q) BL) = Z.to_nat r) by (rewrite length_skipn; lia).
assert (E : blocks255 (S (length BL)) BL = cbb_prefix BL (Z.to_nat q) ++ (if r =? 0 then [0] else r :: skipn (255 * Z.to_nat q) BL ++ [0])).
{ rewrite (blocks255_split (Z.to_nat q)) by lia. f_equal. unfold cbb_tail.
destruct (skipn (255 * Z.to_nat q) BL) as [|x t] eqn:E.
- cbn [length] in Hsk. destruct (Z.eqb_spec r 0); [reflexivity | lia].
- destruct (Z.eqb_spec r 0) as [-> | NE]; [cbn [length] in Hsk; lia|]. rewrite Hsk, Z2Nat.id by lia. reflexivity. }
split; [exact E|]. split; [|exact Hsk].
rewrite E, length_app, cbb_prefix_length by lia. destruct (Z.eqb_spec r 0) as [-> | NE]; cbn [length]; [lia|].
rewrite length_app, Hsk. cbn [length]. lia.
Qed.
Definition pk_grow (L : Z) (s : pk_st) : bool := (p_len s <? 12) && (((p_n s - L) mod 2 ^ 32) =? p_dict s).
Definition pk_pack (bl : list Z) (off len code : Z) : list Z * bool :=
let bl1 := or_head bl ((code * 2 ^ off) mod 256) in
let tot := len + off in
let b1 := (code / 2 ^ (8 - off)) mod 256 in
let b2 := (code / 2 ^ (16 - off)) mod 256 in
if tot <? 8 then (bl1, false)
else if tot =? 8 then (0 :: bl1, true)
else if tot <? 16 then (b1 :: bl1, false)
else if tot =? 16 then (0 :: b1 :: bl1, true)
else (b2 :: b1 :: bl1, false).
Lemma pk_step_eq : forall L icl s code,
pk_step L icl s code =
let len := if pk_grow L s then p_len s + 1 else p_len s in
let n := if pk_grow L s then (p_n s * 2) mod 65536 else p_n s in
let bc := pk_pack (p_bl s) (p_off s) len code in
if code =? L then mkPk (fst bc) ((len + p_off s) mod 8) icl ((2 * L) mod 65536) 1 (snd bc)
else mkPk (fst bc) ((len + p_off s) mod 8) len n (p_dict s + 1) (snd bc).
Proof.
intros L icl s code. unfold pk_step, pk_grow, pk_pack. cbv zeta.
destruct ((p_len s <? 12) && ((p_n s - L) mod 2 ^ 32 =? p_dict s));
repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.
Lemma pk_grow_machine : forall L s, 0 <= L <= 65535 -> 0 <= p_n s < 65536 -> 0 <= p_dict s < 2 ^ 31 ->
pk_grow L s = (p_len s <? 12) && (p_n s - L =? p_dict s).
Proof.
intros L s HL Hn Hd. unfold pk_grow. f_equal.
destruct (Z.leb_spec L (p_n s)).
- rewrite Z.mod_small by lia. reflexivity.
- assert (E : (p_n s - L) mod 2 ^ 32 = 2 ^ 32 + (p_n s - L)) by (symmetry; apply Z.mod_unique_pos with (q := -1); lia).
rewrite E. destruct (Z.eqb_spec (2 ^ 32 + (p_n s - L)) (p_dict s)), (Z.eqb_spec (p_n s - L) (p_dict s)); try reflexivity; lia.
Qed.
Lemma pk_pack_shape : forall P Y0 off len code,
let Y0' := Z.lor Y0 ((code * 2 ^ off) mod 256) in
let b1 := (code / 2 ^ (8 - off)) mod 256 in let b2 := (code / 2 ^ (16 - off)) mod 256 in
let tot := len + off in
rev (fst (pk_pack (Y0 :: rev P) off len code)) =
P ++ (if tot <? 8 then [Y0'] else if tot =? 8 then [Y0'; 0] else if tot <? 16 then [Y0'; b1] else if tot =? 16 then [Y0'; b1; 0] else [Y0'; b1; b2]) /\
snd (pk_pack (Y0 :: rev P) off len code) = ((tot =? 8) || (tot =? 16)).
Proof.
intros P Y0 off len code. cbv zeta. unfold pk_pack. cbv zeta. cbn [or_head].
destruct (len + off <? 8) eqn:E1; [| destruct (len + off =? 8) eqn:E2; [| destruct (len + off <? 16) eqn:E3; [| destruct (len + off =? 16) eqn:E4]]];
cbn [fst snd rev app orb]; rewrite ?rev_involutive, <- ?app_assoc; cbn [app]; split; try reflexivity;
repeat match goal with
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H end;
repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end; try reflexivity; lia.
Qed.
Lemma pk_step_machine : forall D C0 pk X Lc b nreg dict L1 nreg1 L2 nreg2 dict2 b' m,
p_len pk = Lc -> p_off pk = b -> p_n pk = nreg mod 65536 -> p_dict pk = dict ->
0 <= D <= 65535 -> 1 <= dict < 2 ^ 31 -> 0 <= Lc <= 12 -> 0 <= C0 <= 12 -> 0 <= nreg <= 131070 * 2 ^ Lc ->
L1 = (if (Lc <? 12) && (nreg mod 65536 - D =? dict) then Lc + 1 else Lc) ->
nreg1 = (if (Lc <? 12) && (nreg mod 65536 - D =? dict) then 2 * nreg else nreg) ->
L2 = (if X =? D then C0 else L1) -> nreg2 = (if X =? D then 2 * D else nreg1) -> dict2 = (if X =? D then 1 else dict + 1) ->
b + L1 = 8 * m + b' -> 0 <= b' < 8 ->
p_len (pk_step D C0 pk X) = L2 /\ p_off (pk_step D C0 pk X) = b' /\ p_n (pk_step D C0 pk X) = nreg2 mod 65536 /\
p_dict (pk_step D C0 pk X) = dict2 /\
p_bl (pk_step D C0 pk X) = fst (pk_pack (p_bl pk) b L1 X) /\ p_corr (pk_step D C0 pk X) = snd (pk_pack (p_bl pk) b L1 X) /\
0 <= L2 <= 12 /\ 0 <= nreg2 <= 131070 * 2 ^ L2 /\ 1 <= dict2 <= dict + 1.
Proof.
intros D C0 pk X Lc b nreg dict L1 nreg1 L2 nreg2 dict2 b' m HLc Hb Hn Hd RD Rd RL RC Rn EL1 En1 EL2 En2 Ed2 Hm Hb'.
pose proof (Z.mod_pos_bound nreg 65536 ltac:(lia)) as Hnm.
rewrite pk_step_eq, pk_grow_machine by (rewrite ?Hn, ?Hd; lia). cbv zeta. rewrite HLc, Hb, Hn, Hd.
assert (Eoff : forall l, l = L1 -> (l + b) mod 8 = b').
{ intros l ->. replace (L1 + b) with (b' + m * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (P2 : forall k, 0 <= k -> 1 <= 2 ^ k) by (intros k Hk; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
assert (EL1' : (if (Lc <? 12) && (nreg mod 65536 - D =? dict) then Lc + 1 else Lc) = L1) by (symmetry; exact EL1).
rewrite EL1'.
destruct (Z.eqb_spec X D) as [EX | NX]; cbn [p_len p_off p_n p_dict p_bl p_corr]; subst L2 nreg2 dict2.
- repeat split; try reflexivity; try lia; try (apply Eoff; reflexivity); pose proof (P2 C0 ltac:(lia)); nia.
- destruct ((Lc <? 12) && (nreg mod 65536 - D =? dict)) eqn:G; subst L1 nreg1.
+ apply andb_prop in G as [G1 _]. apply Z.ltb_lt in G1.
repeat split; try reflexivity; try lia; try (apply Eoff; reflexivity).
* rewrite Zmult_mod_idemp_l. f_equal. lia.
* replace (Lc + 1) with (Z.succ Lc) by lia. rewrite Z.pow_succ_r by lia. lia.
+ repeat split; try reflexivity; try lia; apply Eoff; reflexivity.
Qed.
Lemma skipn_nth_consZ : forall (l : list Z) n, (n < length l)%nat -> skipn n l = nth n l 0 :: skipn (S n) l.
Proof. induction l as [|x r IH]; intros [|n] Hn; cbn in Hn |- *; try lia; [reflexivity|]. apply IH. lia. Qed.
