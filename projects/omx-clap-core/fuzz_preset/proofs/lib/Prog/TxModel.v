From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint zsum (ns : list Z) : Z :=
  match ns with
  | [] => 0
  | n :: r => n + zsum r
  end.

Definition plen (P : list (list Z)) : list Z := map (fun x => Z.of_nat (length x)) P.

Definition tx_cap1 (len cap n : Z) : Z := if len + n + 1 <=? cap then cap else 2 * (len + n + 1).

Fixpoint tx_capf (len cap : Z) (ns : list Z) : Z :=
  match ns with
  | [] => cap
  | n :: r => tx_capf (len + n) (tx_cap1 len cap n) r
  end.


Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1 as [|n l1 IH]; intros l2; cbn [app zsum]; [lia | rewrite IH; lia]. Qed.

Lemma zsum_plen : forall P, zsum (plen P) = Z.of_nat (length (concat P)).
Proof.
  induction P as [|x P IH]; [reflexivity|]. cbn [plen map zsum concat]. fold (plen P). rewrite IH, length_app. lia.
Qed.

Lemma plen_app : forall P Q, plen (P ++ Q) = plen P ++ plen Q.
Proof. intros. unfold plen. apply map_app. Qed.

Lemma tx_capf_app : forall l1 l2 len cap, tx_capf len cap (l1 ++ l2) = tx_capf (len + zsum l1) (tx_capf len cap l1) l2.
Proof.
  induction l1 as [|n l1 IH]; intros l2 len cap; cbn [app tx_capf zsum].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. f_equal. lia.
Qed.

Definition spcs (c : Z) : list (list Z) :=
  if (c =? 34) || (c =? 92) then [[92]; [c]] else [if special c then esc c else [c]].

Definition strp (bs : list Z) : list (list Z) := [34] :: concat (map spcs bs) ++ [[34]].

Fixpoint tvp (t : jv) (p : bool) (d : Z) {struct t} : list (list Z) :=
  match t with
  | JNull => [[110; 117; 108; 108]]
  | JFalse => [[102; 97; 108; 115; 101]]
  | JTrue => [[116; 114; 117; 101]]
  | JNum txt _ => [txt]
  | JStr s => strp s
  | JArr items =>
      [91] ::
      (fix go (i : nat) (l : list jv) {struct l} : list (list Z) :=
         match l with
         | [] => []
         | x :: r => wcomma i ++ wind p (d + 1) ++ tvp x p (d + 1) ++ go (S i) r
         end) 0%nat items
      ++ (match items with [] => [] | _ :: _ => wind p d end) ++ [[93]]
  | JObj members =>
      [123] ::
      (fix go (i : nat) (l : list (list Z * jv)) {struct l} : list (list Z) :=
         match l with
         | [] => []
         | (k, x) :: r => wcomma i ++ wind p (d + 1) ++ strp k ++ [[58]] ++ (if p then [[32]] else []) ++
                          tvp x p (d + 1) ++ go (S i) r
         end) 0%nat members
      ++ (match members with [] => [] | _ :: _ => wind p d end) ++ [[125]]
  end.

Definition tv_calls (t : jv) (p : bool) (d : Z) : list Z := plen (tvp t p d).

