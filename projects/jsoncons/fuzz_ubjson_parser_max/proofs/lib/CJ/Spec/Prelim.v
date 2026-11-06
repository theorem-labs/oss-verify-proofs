(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_Prelim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prelim."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1length"; "1list"; "1nat"; "2and"; "2eq"; "2not"; "3lt"; "4nth"; "5Z"; "6upd_nat"; "6zlength"; "6znth"; "6zrepeat"; "6zupd"; "7In"; "8le"]; ["8lt"; "0i"; "0j"; "0l"; "0n"; "0v"]]).
Definition u8 (x : Z) : Z := x mod 2^8.
Definition u16 (x : Z) : Z := x mod 2^16.
Definition u32 (x : Z) : Z := x mod 2^32.
Definition u64 (x : Z) : Z := x mod 2^64.
Definition s32 (x : Z) : Z := (x + 2^31) mod 2^32 - 2^31.
Definition s64 (x : Z) : Z := (x + 2^63) mod 2^64 - 2^63.
Definition zlength {A} (l : list A) : Z := Z.of_nat (length l).
Definition znth (l : list Z) (i : Z) : Z :=
if i <? 0 then 0 else nth (Z.to_nat i) l 0.
Fixpoint upd_nat (l : list Z) (i : nat) (v : Z) : list Z :=
match l, i with
| [], _ => []
| _ :: t, O => v :: t
| h :: t, S i' => h :: upd_nat t i' v
end.
Definition zupd (l : list Z) (i : Z) (v : Z) : list Z :=
if i <? 0 then l else upd_nat l (Z.to_nat i) v.
Lemma upd_nat_length : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "A'1'8%211'2'4&0&9r3r2r1%43321%62:1%72;5%93:21pQ<=1pQ4<1pQ8>1").
Proof. induction l; intros [|i] v; cbn; auto. Qed.
Lemma zupd_length : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "A'1'8%211'4'2&0&=r3r2r1%43321%62:1%72;5%:3921pQ<=1pQ4>1pQ8>1").
Proof. intros. unfold zupd. destruct (i <? 0); auto using upd_nat_length. Qed.
Lemma zlength_zupd : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "@'1'8%211'4&:&=r3r2r1%43321%6291%72:5%93;21pQ<<1pQ4=1pQ8=1").
Proof. intros. unfold zlength. rewrite zupd_length. reflexivity. Qed.
Lemma nth_upd_nat_same : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "F'1'8%211'2&6r2&0r3%2271%5241'4&7&9r4%23179z%54?921%73@1<p091pQ<B1pQ4A1pQ8C1").
Proof. induction l; intros [|i] v H; cbn in *; try lia; auto. apply IHl. lia. Qed.
Lemma nth_upd_nat_other : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "H'1'8%211'2&5'4r3r2%33521%511&7&9r5r4%33217z%64?:21%74@;52%=3A21p0:1pQ<C1pQ6B1pQ4C1pQ8E1").
Proof. induction l; intros [|i] [|j] v H; cbn; auto; try congruence. Qed.
Lemma znth_zupd_eq : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "I'1'8%211'3&?zr2%3221&@&:r3%22:1%4261%:261'4&;&=r4%2318<%4219%63C1>p081pQ<E1pQ4F1pQ8F1").
Proof.
intros l i v H. unfold znth, zupd, zlength in *.
destruct (Z.ltb_spec i 0); [lia|]. apply nth_upd_nat_same. lia.
Qed.
Lemma znth_zupd_neq : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "F'1'8%211&5'4r3r2%33621%511&;&=r5r4%33217%5219%624:%<3?21p091pQ<A1pQ6B1pQ4C1pQ8C1").
Proof.
intros l i j v H. unfold znth, zupd.
destruct (Z.ltb_spec j 0); [reflexivity|]. destruct (Z.ltb_spec i 0); [reflexivity|].
apply nth_upd_nat_other. intros E. apply H. lia.
Qed.
Lemma znth_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "F'1'8%211'3&?zr1%3221&@&:r2%22:1%4261%:261&>&;r3%2217%43A12p061pQ4C1pQ8C1").
Proof.
intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|].
apply nth_In. lia.
Qed.
Definition zrepeat (v : Z) (n : Z) : list Z := repeat v (Z.to_nat n).
Lemma zlength_zrepeat : ltac2:(TCodec.tc2 tcn__CJ_Spec_Prelim "@'8&?zr1%3221'4&:&<r3r2%3221%52;1%73<13p091pQ:>1pQ<?1").
Proof. intros. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.
