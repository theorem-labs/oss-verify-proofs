(* The record grammar of reac-repacer's warm-start lock, as rp_lock_lookup
   (src/repace_conf.c:114-145 at 3ac1cf10) reads it, over the file's bytes.
   Written by Theorem Labs for the fuzz_lock walks.
   UBSan copy: lib/Spec/LockSpec.v verbatim, with its StrFun import pointed at lib.U.Spec.StrFun
   (the UBSan image's copy of StrFun), so the UBSan walks import only lib/U files. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun.
Import ListNotations.
Open Scope Z_scope.

Definition bz (b : byte) : Z := bv_unsigned b.

(* [is_sep] of repace_conf.c:82 and fuzz_lock.c:49: space, tab, CR. *)
Definition is_sep (c : Z) : bool := (c =? 32) || (c =? 9) || (c =? 13).

(* the number of separators that start l *)
Fixpoint sep_run (l : list byte) : nat :=
  match l with [] => O | b :: r => if is_sep (bz b) then S (sep_run r) else O end.

(* the number of non-separators that start l *)
Fixpoint tok_run (l : list byte) : nat :=
  match l with [] => O | b :: r => if is_sep (bz b) then O else S (tok_run r) end.

(* [field] of repace_conf.c:87 on a line l, from offset o: the field's offset and length *)
Definition fld (l : list byte) (o : nat) : nat * nat :=
  let s := (o + sep_run (skipn o l))%nat in (s, tok_run (skipn s l)).

Definition slice (l : list byte) (s n : nat) : list byte := firstn n (skipn s l).

Fixpoint dig_go (l : list byte) (v : Z) : Z :=
  match l with
  | [] => v
  | b :: r => if (48 <=? bz b) && (bz b <=? 57) then dig_go r (v * 10 + (bz b - 48)) else -1
  end.

(* [digits] of repace_conf.c:101 and [number] of fuzz_lock.c:64 *)
Definition digits (l : list byte) : Z :=
  if (length l =? 0)%nat || (18 <? length l)%nat then -1 else dig_go l 0.

(* [std_period] of repace_conf.c:71 *)
Definition std_period (rate : Z) : Z :=
  if rate =? 44100 then 272109 else if rate =? 48000 then 250000 else if rate =? 96000 then 125000 else 0.

Definition is_some {X} (o : option X) : bool := match o with Some _ => true | None => false end.

(* The period one line restores, None when it is no matching record. *)
Definition line_val (p : list byte) (rate : Z) (l : list byte) : option Z :=
  let std := std_period rate in
  let '(s1, l1) := fld l 0 in
  let '(s2, l2) := fld l (s1 + l1) in
  let '(s3, l3) := fld l (s2 + l2) in
  if is_some (find_byte 0 l) then None
  else if (l1 =? 0)%nat || (bz (nth s1 l (Z_to_bv 8 0)) =? 35) then None
  else if (15 <? l1)%nat || negb (l1 =? length p)%nat
          || negb (match memcmp_model (slice l s1 l1) p l1 with Some 0 => true | _ => false end)
  then None
  else
    let per := digits (slice l s2 l2) in
    let lab := digits (slice l s3 l3) in
    if (per <? 0) || negb (lab =? rate) then None
    else if (per <? std - std / 20) || (std + std / 20 <? per) then None
    else Some per.

Definition upd (p : list byte) (rate : Z) (l : list byte) (found : Z) : Z :=
  match line_val p rate l with Some v => v | None => found end.

(* the loop of repace_conf.c:121-143 over the text t still to read *)
Fixpoint lk (fuel : nat) (p : list byte) (rate : Z) (t : list byte) (found : Z) : Z :=
  match fuel with
  | O => found
  | S f =>
      match t with
      | [] => found
      | _ =>
          match find_byte 10 t with
          | Some j => lk f p rate (skipn (S j) t) (upd p rate (firstn j t) found)
          | None => upd p rate t found
          end
      end
  end.

(* rp_lock_lookup(text, n, port, rate) with text's n bytes t and port's string p *)
Definition lock_lookup (t p : list byte) (rate : Z) : Z :=
  if (std_period rate =? 0) || (65536 <? Z.of_nat (length t)) then 0
  else lk (length t) p rate t 0.

(** Basic facts used by the walks. *)

Lemma memcmp_model_eq : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  memcmp_model l r n = Some 0 <-> firstn n l = firstn n r.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] Hl Hr; cbn in *; try lia.
  - split; reflexivity.
  - split; reflexivity.
  - split; reflexivity.
  - split; reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + assert (a = b) by (apply bv_eq; exact E). subst b.
      rewrite IH by lia. split; [intros ->; reflexivity | intros H; injection H; auto].
    + split; [intros H; injection H as H; pose proof (bv_unsigned_in_range _ a); pose proof (bv_unsigned_in_range _ b); lia|].
      intros H; injection H as -> _. lia.
Qed.

Lemma sep_run_le : forall l, (sep_run l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn; [lia|]. destruct (is_sep (bz b)); cbn; lia. Qed.

Lemma tok_run_le : forall l, (tok_run l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn; [lia|]. destruct (is_sep (bz b)); cbn; lia. Qed.

Lemma std_period_cases : forall rate, std_period rate = 0 \/
  (rate = 44100 /\ std_period rate = 272109) \/ (rate = 48000 /\ std_period rate = 250000) \/
  (rate = 96000 /\ std_period rate = 125000).
Proof.
  intros rate. unfold std_period.
  destruct (Z.eqb_spec rate 44100); [right; left; auto|].
  destruct (Z.eqb_spec rate 48000); [right; right; left; auto|].
  destruct (Z.eqb_spec rate 96000); [right; right; right; auto|]. left; reflexivity.
Qed.

(* The harness's [standard] (fuzz_lock.c:56) is std_period. *)
Lemma standard_is_std : forall rate, rate = 44100 \/ rate = 48000 \/ rate = 96000 ->
  (12000000000 + rate / 2) / rate = std_period rate.
Proof. intros rate [->|[->| ->]]; reflexivity. Qed.

Lemma digits_range : forall l, -1 <= digits l < 10 ^ 18.
Proof.
  intros l. unfold digits.
  destruct ((length l =? 0)%nat || (18 <? length l)%nat) eqn:E; [lia|].
  apply orb_false_iff in E. destruct E as [E1 E2]. apply Nat.eqb_neq in E1. apply Nat.ltb_ge in E2.
  assert (G : forall l v, 0 <= v < 10 ^ Z.of_nat (18 - length l) -> (length l <= 18)%nat ->
            -1 <= dig_go l v < 10 ^ 18).
  { induction l0 as [|b r IH]; intros v Hv Hl; cbn [dig_go length] in *.
    - replace (18 - 0)%nat with 18%nat in Hv by lia. cbn in Hv |- *. lia.
    - destruct ((48 <=? bz b) && (bz b <=? 57)) eqn:D; [|lia].
      apply andb_true_iff in D. destruct D as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2.
      apply IH; [|lia].
      replace (Z.of_nat (18 - S (length r))) with (Z.of_nat (18 - length r) - 1) in Hv by lia.
      assert (P : 10 ^ Z.of_nat (18 - length r) = 10 * 10 ^ (Z.of_nat (18 - length r) - 1)).
      { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
      rewrite P. lia. }
  apply G; [|lia]. split; [lia|]. apply Z.pow_pos_nonneg; lia.
Qed.
