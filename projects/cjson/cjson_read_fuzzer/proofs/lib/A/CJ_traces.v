(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Definition RA_PWLO : Z := 0x82454.
Definition trunc30 (l : list Z) : list Z := firstn 30 l.

(* [comment removed for export] *)
Definition tr_pv_pwlo (ra : Z) (b : nat) : list Z := trunc30 (PC0_MALLOC :: 0x8343c :: repeat 0x834b8 b ++ [0x8296c; ra]).
Definition tr_pv_pobj (b : nat) : list Z := trunc30 (PC0_MALLOC :: 0x8343c :: repeat 0x834b8 b ++ [0x866d4]).

Definition S_FUZZ : list (list Z) := [[PC0_FREE; 0x8249c]; [PC0_MALLOC; 0x824ac]; [PC0_FREE; 0x824d0]].
Definition S_PARSE_CONST : list (list Z) :=
  [[PC0_MALLOC; 0x86478]; [PC0_MALLOC; 0x85ab0]; [PC0_FREE; 0x860cc]].
Definition S_PARSE (ra : Z) : list (list Z) :=
  [PC0_MALLOC; 0x82938; ra] :: S_PARSE_CONST ++ map (tr_pv_pwlo ra) (seq 0 29) ++ map tr_pv_pobj (seq 0 29).
Definition S_DELETE : list (list Z) := [[PC0_FREE; 0x825c8]; [PC0_FREE; 0x8265c]; [PC0_FREE; 0x826a0]].
Definition S_PRINT_CONST : list (list Z) :=
  [[PC0_MALLOC; 0x83a5c]; [PC0_REALLOC; 0x83ac4]; [PC0_MALLOC; 0x83adc]; [PC0_FREE; 0x83b2c]; [PC0_FREE; 0x83b44];
   [PC0_MALLOC; 0x83bb8]; [PC0_FREE; 0x83c20]].

Definition S_LIB : list (list Z) := S_FUZZ ++ S_PARSE RA_PWLO ++ S_DELETE ++ S_PRINT_CONST.

Lemma S_LIB_length : Z.of_nat (length S_LIB) = 75.
Proof. vm_compute. reflexivity. Qed.

Lemma S_LIB_bound : Z.of_nat (length S_LIB) <= 4096.
Proof. rewrite S_LIB_length. lia. Qed.

(* [comment removed for export] *)
Definition tr_inb (tr : list Z) (S : list (list Z)) : bool :=
  if in_dec (list_eq_dec Z.eq_dec) tr S then true else false.
Lemma tr_inb_In : forall tr S, tr_inb tr S = true -> In tr S.
Proof. intros tr S H. unfold tr_inb in H. destruct (in_dec _ tr S); [assumption| discriminate]. Qed.

(* [comment removed for export] *)
Lemma firstn_repeat_le : forall {X} n k (x : X), (n <= k)%nat -> firstn n (repeat x k) = repeat x n.
Proof.
  intros X n. induction n as [|n IH]; intros k x Hk; [reflexivity|].
  destruct k as [|k]; [lia|]. cbn. f_equal. apply IH. lia.
Qed.

Lemma trunc30_sat : forall (p : list Z) c b tl, length p = 2%nat -> (28 <= b)%nat ->
  trunc30 (p ++ repeat c b ++ tl) = p ++ repeat c 28.
Proof.
  intros p c b tl Hp Hb. unfold trunc30. rewrite firstn_app, Hp. rewrite (firstn_all2 p) by lia.
  change (30 - 2)%nat with 28%nat. rewrite firstn_app, repeat_length, (firstn_repeat_le 28 b) by exact Hb.
  replace (28 - b)%nat with O by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma tr_pv_pwlo_sat : forall ra b, (28 <= b)%nat -> tr_pv_pwlo ra b = tr_pv_pwlo ra 28.
Proof.
  intros ra b Hb. unfold tr_pv_pwlo.
  change (PC0_MALLOC :: 0x8343c :: repeat 0x834b8 b ++ [0x8296c; ra]) with ([PC0_MALLOC; 0x8343c] ++ repeat 0x834b8 b ++ [0x8296c; ra]).
  change (PC0_MALLOC :: 0x8343c :: repeat 0x834b8 28 ++ [0x8296c; ra]) with ([PC0_MALLOC; 0x8343c] ++ repeat 0x834b8 28 ++ [0x8296c; ra]).
  rewrite !trunc30_sat by (reflexivity || lia). reflexivity.
Qed.

Lemma tr_pv_pobj_sat : forall b, (28 <= b)%nat -> tr_pv_pobj b = tr_pv_pobj 28.
Proof.
  intros b Hb. unfold tr_pv_pobj.
  change (PC0_MALLOC :: 0x8343c :: repeat 0x834b8 b ++ [0x866d4]) with ([PC0_MALLOC; 0x8343c] ++ repeat 0x834b8 b ++ [0x866d4]).
  change (PC0_MALLOC :: 0x8343c :: repeat 0x834b8 28 ++ [0x866d4]) with ([PC0_MALLOC; 0x8343c] ++ repeat 0x834b8 28 ++ [0x866d4]).
  rewrite !trunc30_sat by (reflexivity || lia). reflexivity.
Qed.

Lemma In_S_PARSE_pwlo : forall ra b, In (tr_pv_pwlo ra b) (S_PARSE ra).
Proof.
  intros ra b. unfold S_PARSE. right. apply in_or_app. right. apply in_or_app. left.
  destruct (Nat.le_gt_cases 28 b) as [Hb|Hb].
  - rewrite (tr_pv_pwlo_sat ra b Hb). apply in_map. apply in_seq. lia.
  - apply in_map. apply in_seq. lia.
Qed.

Lemma In_S_PARSE_pobj : forall ra b, In (tr_pv_pobj b) (S_PARSE ra).
Proof.
  intros ra b. unfold S_PARSE. right. apply in_or_app. right. apply in_or_app. right.
  destruct (Nat.le_gt_cases 28 b) as [Hb|Hb].
  - rewrite (tr_pv_pobj_sat b Hb). apply in_map. apply in_seq. lia.
  - apply in_map. apply in_seq. lia.
Qed.

Lemma In_S_LIB_parse : forall tr, In tr (S_PARSE RA_PWLO) -> In tr S_LIB.
Proof. intros tr H. unfold S_LIB. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma In_S_LIB_pv_pwlo : forall b, In (tr_pv_pwlo RA_PWLO b) S_LIB.
Proof. intros b. apply In_S_LIB_parse, In_S_PARSE_pwlo. Qed.

Lemma In_S_LIB_pv_pobj : forall b, In (tr_pv_pobj b) S_LIB.
Proof. intros b. apply In_S_LIB_parse, In_S_PARSE_pobj. Qed.

(* [comment removed for export] *)
Lemma In_S_LIB_consts :
  Forall (fun tr => In tr S_LIB)
    ([PC0_MALLOC; 0x82938; RA_PWLO] :: S_FUZZ ++ S_PARSE_CONST ++ S_DELETE ++ S_PRINT_CONST).
Proof.
  apply Forall_forall. intros tr H. apply tr_inb_In.
  repeat (destruct H as [<-|H]; [vm_compute; reflexivity|]). destruct H.
Qed.
