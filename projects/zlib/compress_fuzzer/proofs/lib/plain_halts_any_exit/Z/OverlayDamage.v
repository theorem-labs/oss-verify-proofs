(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayTF.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayTrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma lsum_zsum_swap : forall (F : Z -> Z -> Z) (L : list Z) lo n,
  lsum (fun i => zsum (F i) lo n) L = zsum (fun t => lsum (fun i => F i t) L) lo n.
Proof.
  intros F L lo n. induction L as [|x L IH]; cbn [lsum].
  - symmetry. apply zsum_0. intros; reflexivity.
  - rewrite IH, <- zsum_add. reflexivity.
Qed.

Definition cnt (P : Z -> bool) (L : list Z) : Z := lsum (fun i => zind (P i)) L.

Lemma cnt_nonneg : forall P L, 0 <= cnt P L.
Proof. intros. unfold cnt. apply lsum_nonneg. intros; apply (proj1 (zind_le1 _)). Qed.

Lemma cnt_le_length : forall P L, cnt P L <= Z.of_nat (length L).
Proof. intros P L. unfold cnt. induction L; cbn [lsum length]; [lia|]. pose proof (zind_le1 (P a)). lia. Qed.

Lemma cnt_mono : forall (P Q : Z -> bool) L, (forall i, In i L -> P i = true -> Q i = true) -> cnt P L <= cnt Q L.
Proof.
  intros P Q L H. unfold cnt. apply lsum_le. intros i Hi. destruct (P i) eqn:E; [rewrite (H i Hi E); cbn; lia | pose proof (zind_le1 (Q i)); cbn; lia].
Qed.

Lemma cnt_ext : forall (P Q : Z -> bool) L, (forall i, In i L -> P i = Q i) -> cnt P L = cnt Q L.
Proof. intros. unfold cnt. apply lsum_ext. intros. rewrite H by assumption. reflexivity. Qed.

Lemma cnt_split : forall (P Q : Z -> bool) L, cnt P L = cnt (fun i => P i && Q i) L + cnt (fun i => P i && negb (Q i)) L.
Proof. intros. unfold cnt. rewrite <- lsum_add. apply lsum_ext. intros. destruct (P x), (Q x); reflexivity. Qed.

Lemma cnt_true : forall L, cnt (fun _ => true) L = Z.of_nat (length L).
Proof. intros. unfold cnt. cbn [zind]. induction L; cbn [lsum length]; lia. Qed.

Lemma cnt_pigeon : forall (P Q : Z -> bool) L, cnt Q L < cnt P L -> exists i, In i L /\ P i = true /\ Q i = false.
Proof.
  intros P Q L. unfold cnt. induction L as [|x L IH]; cbn [lsum]; [lia|]. intros H.
  destruct (P x) eqn:Px; destruct (Q x) eqn:Qx; cbn [zind] in H.
  - destruct (IH ltac:(lia)) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto].
  - exists x. split; [left; reflexivity | auto].
  - destruct (IH ltac:(lia)) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto].
  - destruct (IH ltac:(lia)) as (i & Hi & A & B). exists i. split; [right; exact Hi | auto].
Qed.

Lemma zsum_sub : forall f g lo n, zsum f lo n - zsum g lo n = zsum (fun i => f i - g i) lo n.
Proof. intros. induction n; cbn [zsum]; lia. Qed.

Definition Lc : Z := 254074700880.
Definition qtab (x : Z) : Z :=
  nth (Z.to_nat x) [254074700880; 254074700880; 127037350440; 84691566960; 50814940176; 31759337610; 19544207760;
                   12098795280; 7472785320; 4619540016; 2854771920; 1764407645; 1090449360] 0.

Definition hget (h : list Z) (b : Z) : Z := if (1 <=? b) && (b <=? 12) then nth (Z.to_nat (b - 1)) h 0 else 0.

Definition capf (hf : Z -> Z) : hist :=
  fun b => if b <? 1 then 0 else if b <? 7 then hf b else if b =? 7 then zsum hf 7 6 else 0.

Definition cumf (hf : Z -> Z) (u : Z) : Z := zsum hf 1 (Z.to_nat (u - 1)).
Definition rk (c : Z -> Z) (r : Z) : Z := zsum (fun u => zind (c u <? r)) 1 12.

Definition pval (hf : Z -> Z) : Z :=
  let n := zsum hf 1 12 in
  let cd := cumf hf in
  let cl := cumf (repair 7 (capf hf)) in
  zsum (fun r => Z.max 0 (rk cl r - rk cd r) * qtab (rk cd r)) 1 (Z.to_nat n).

Definition pval_fast (h : list Z) : Z :=
  let hf := hget h in
  let n := zsum hf 1 12 in
  let lam := map (repair 7 (capf hf)) (map Z.of_nat (seq 1 12)) in
  let cdl := map (cumf hf) (map Z.of_nat (seq 1 12)) in
  let cll := map (cumf (hget lam)) (map Z.of_nat (seq 1 12)) in
  let rkd := map (rk (hget cdl)) (map Z.of_nat (seq 1 (Z.to_nat n))) in
  let rkl := map (rk (hget cll)) (map Z.of_nat (seq 1 (Z.to_nat n))) in
  zsum (fun r => let dd := nth (Z.to_nat (r - 1)) rkd 0 in Z.max 0 (nth (Z.to_nat (r - 1)) rkl 0 - dd) * qtab dd) 1 (Z.to_nat n).
Definition ptest (rnum rden : Z) (h : list Z) : bool := rden * pval_fast h <=? rnum * Lc.

Fixpoint penum (lev : nat) (b krem nrem : Z) (acc : list Z) (test : list Z -> bool) : bool :=
  match lev with
  | O => if krem =? 0 then test (rev acc) else true
  | S lev' => let unit := 2 ^ (12 - b) in
      if nrem * unit <? krem then true
      else forallb (fun hb => penum lev' (b + 1) (krem - hb * unit) (nrem - hb) (hb :: acc) test)
                   (map Z.of_nat (seq 0 (S (Z.to_nat (Z.min nrem (krem / unit))))))
  end.

Definition dmg_cert (K rnum rden : Z) : bool :=
  (0 <=? rnum) && (1 <=? rden) && penum 12 1 4096 K [] (ptest rnum rden).

Fixpoint kr (b : Z) (hs : list Z) : Z :=
  match hs with [] => 0 | x :: r => x * 2 ^ (12 - b) + kr (b + 1) r end.

Lemma d_rep_find_ext : forall n (h h' : hist) b, (forall x, h x = h' x) -> rep_find n h b = rep_find n h' b.
Proof. induction n as [|n IH]; intros h h' b E; cbn [rep_find]; [reflexivity|]. rewrite E. destruct (h' b =? 0); [apply IH; exact E | reflexivity]. Qed.

Lemma d_rep_iter_ext : forall n ML (h h' : hist), (forall x, h x = h' x) -> forall x, rep_iter n ML h x = rep_iter n ML h' x.
Proof.
  induction n as [|n IH]; intros ML h h' E x; cbn [rep_iter]; [apply E|].
  apply IH. intros y. unfold rep_step. rewrite (d_rep_find_ext _ h h') by exact E. rewrite !E. reflexivity.
Qed.

Lemma d_repair_ext : forall ML (h h' : hist), (forall x, h x = h' x) -> forall x, repair ML h x = repair ML h' x.
Proof.
  intros ML h h' E x. unfold repair, kraftZ. rewrite (zsum_ext (fun b => h b * 2 ^ (ML - b)) (fun b => h' b * 2 ^ (ML - b))) by (intros; rewrite E; reflexivity).
  apply d_rep_iter_ext. exact E.
Qed.

Section Damage.
Variable L : list Z.
Variable w : Z -> Z.
Variable d : Z -> Z.
Variable l : Z -> Z.

Definition Wt : Z := lsum w L.
Definition nL : Z := Z.of_nat (length L).
Hypothesis Hw : forall i, In i L -> 1 <= w i.
Hypothesis Hd : forall i, In i L -> 1 <= d i <= 12.
Hypothesis Hl : forall i, In i L -> 1 <= l i <= 12.

Hypothesis Md : forall i j, In i L -> In j L -> w i < w j -> d j <= d i.
Hypothesis Ml : forall i j, In i L -> In j L -> w i < w j -> l j <= l i.

Hypothesis FIB : forall i, In i L -> w i * fib (d i + 1) <= Wt.

Definition mt (t : Z) : Z := cnt (fun i => t <=? w i) L.
Definition cv (v : Z -> Z) (u : Z) : Z := cnt (fun i => v i <? u) L.
Definition dv (v : Z -> Z) (r : Z) : Z := zsum (fun u => zind (cv v u <? r)) 1 12.
Definition Tr (r : Z) : Z := zsum (fun t => zind (r <=? mt t)) 1 (Z.to_nat Wt).

Definition er (r : Z) : Z := dv l r - dv d r.

Definition hd (b : Z) : Z := cnt (fun i => d i =? b) L.

End Damage.

Section Tree.
Variable z : ztree.
Variable F : Z -> Z.
Variable Fl : list Z.
Hypothesis TF : tree_facts z 19 7 F Fl.
Local Notation g := (zt_g z).
Let GG : gtree_ok g := G z 19 7 F Fl TF.
Let ZOK : ztree_ok z := tf_ok z 19 7 F Fl TF.
Local Notation W := (ffreq F Fl).
Local Notation Lv := (leaves g).
Local Notation wt := (g_wt g).
Local Notation dp := (g_depth g).
Definition ln : Z -> Z := fun i => zt_len z (g_code g i).

Lemma g_hist_cnt : forall (f : Z -> Z) b, g_hist g f b = cnt (fun i => f i =? b) Lv.
Proof.
  intros f b. unfold g_hist, cnt, leaves, allpos, npos. rewrite lsum_filter, lsum_zsum.
  apply zsum_ext. intros i Hi. destruct (g_leaf g i); reflexivity.
Qed.

End Tree.

