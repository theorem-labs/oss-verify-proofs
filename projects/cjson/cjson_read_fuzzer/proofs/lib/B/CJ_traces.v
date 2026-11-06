(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Definition RA_PWLO : Z := 0x824e4.
Definition trunc30 (l : list Z) : list Z := firstn 30 l.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PWLO_PV_RAS : list Z := [0x82a18; 0x82bf4].
Definition tr_pv_pwlo_at (site ra : Z) (b : nat) : list Z := trunc30 (PC0_MALLOC :: 0x836c8 :: repeat 0x83760 b ++ [site; ra]).
Definition tr_pv_pwlo (ra : Z) (b : nat) : list Z := tr_pv_pwlo_at 0x82a18 ra b.
Definition tr_pv_pobj (b : nat) : list Z := trunc30 (PC0_MALLOC :: 0x836c8 :: repeat 0x83760 b ++ [0x86064]).

Definition S_FUZZ : list (list Z) := [[PC0_FREE; 0x8252c]; [PC0_MALLOC; 0x8253c]; [PC0_FREE; 0x82568]].
Definition S_PARSE_CONST : list (list Z) :=
  [[PC0_MALLOC; 0x85dbc]; [PC0_MALLOC; 0x85558]; [PC0_FREE; 0x85a04]].
Definition S_PARSE (ra : Z) : list (list Z) :=
  [PC0_MALLOC; 0x829e8; ra] :: S_PARSE_CONST ++ map (tr_pv_pwlo_at 0x82a18 ra) (seq 0 29) ++ map (tr_pv_pwlo_at 0x82bf4 ra) (seq 0 29)
  ++ map tr_pv_pobj (seq 0 29).
Definition S_DELETE : list (list Z) := [[PC0_FREE; 0x82664]; [PC0_FREE; 0x82700]; [PC0_FREE; 0x82744]].
Definition S_PRINT_CONST : list (list Z) :=
  [[PC0_MALLOC; 0x83d58]; [PC0_REALLOC; 0x83dc8]; [PC0_MALLOC; 0x83de0]; [PC0_FREE; 0x83e34]; [PC0_FREE; 0x83e4c];
   [PC0_MALLOC; 0x83ec4]; [PC0_FREE; 0x83f2c]].

Definition S_LIB : list (list Z) := S_FUZZ ++ S_PARSE RA_PWLO ++ S_DELETE ++ S_PRINT_CONST.

Lemma S_LIB_length : Z.of_nat (length S_LIB) = 104.
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

Lemma tr_pv_pwlo_at_sat : forall site ra b, (28 <= b)%nat -> tr_pv_pwlo_at site ra b = tr_pv_pwlo_at site ra 28.
Proof.
  intros site ra b Hb. unfold tr_pv_pwlo_at.
  change (PC0_MALLOC :: 0x836c8 :: repeat 0x83760 b ++ [site; ra]) with ([PC0_MALLOC; 0x836c8] ++ repeat 0x83760 b ++ [site; ra]).
  change (PC0_MALLOC :: 0x836c8 :: repeat 0x83760 28 ++ [site; ra]) with ([PC0_MALLOC; 0x836c8] ++ repeat 0x83760 28 ++ [site; ra]).
  rewrite !trunc30_sat by (reflexivity || lia). reflexivity.
Qed.
Lemma tr_pv_pwlo_sat : forall ra b, (28 <= b)%nat -> tr_pv_pwlo ra b = tr_pv_pwlo ra 28.
Proof. intros. unfold tr_pv_pwlo. apply tr_pv_pwlo_at_sat. assumption. Qed.

Lemma tr_pv_pobj_sat : forall b, (28 <= b)%nat -> tr_pv_pobj b = tr_pv_pobj 28.
Proof.
  intros b Hb. unfold tr_pv_pobj.
  change (PC0_MALLOC :: 0x836c8 :: repeat 0x83760 b ++ [0x86064]) with ([PC0_MALLOC; 0x836c8] ++ repeat 0x83760 b ++ [0x86064]).
  change (PC0_MALLOC :: 0x836c8 :: repeat 0x83760 28 ++ [0x86064]) with ([PC0_MALLOC; 0x836c8] ++ repeat 0x83760 28 ++ [0x86064]).
  rewrite !trunc30_sat by (reflexivity || lia). reflexivity.
Qed.

Lemma In_S_PARSE_pwlo_at : forall site ra b, In site PWLO_PV_RAS -> In (tr_pv_pwlo_at site ra b) (S_PARSE ra).
Proof.
  intros site ra b [<-|[<-|[]]]; unfold S_PARSE; right; apply in_or_app; right.
  - apply in_or_app. left. destruct (Nat.le_gt_cases 28 b) as [Hb|Hb].
    + rewrite (tr_pv_pwlo_at_sat _ ra b Hb). apply in_map. apply in_seq. lia.
    + apply in_map. apply in_seq. lia.
  - apply in_or_app. right. apply in_or_app. left. destruct (Nat.le_gt_cases 28 b) as [Hb|Hb].
    + rewrite (tr_pv_pwlo_at_sat _ ra b Hb). apply in_map. apply in_seq. lia.
    + apply in_map. apply in_seq. lia.
Qed.
Lemma In_S_PARSE_pwlo : forall ra b, In (tr_pv_pwlo ra b) (S_PARSE ra).
Proof. intros. unfold tr_pv_pwlo. apply In_S_PARSE_pwlo_at. left. reflexivity. Qed.

Lemma In_S_PARSE_pobj : forall ra b, In (tr_pv_pobj b) (S_PARSE ra).
Proof.
  intros ra b. unfold S_PARSE. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
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
    ([PC0_MALLOC; 0x829e8; RA_PWLO] :: S_FUZZ ++ S_PARSE_CONST ++ S_DELETE ++ S_PRINT_CONST).
Proof.
  apply Forall_forall. intros tr H. apply tr_inb_In.
  repeat (destruct H as [<-|H]; [vm_compute; reflexivity|]). destruct H.
Qed.
