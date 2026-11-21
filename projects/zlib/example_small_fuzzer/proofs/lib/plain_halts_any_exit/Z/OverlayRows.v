(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayLP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayBlock.

Module OverlayRuns.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeZ.OverlayHuff1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayBlock.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.



Fixpoint zr (L : Z -> Z) (i : Z) (n : nat) (cur : Z) : list Z :=
  match n with
  | O => if cur =? 0 then [] else [cur]
  | S k => if L i =? 0 then zr L (i + 1) k (cur + 1)
           else (if cur =? 0 then [] else [cur]) ++ zr L (i + 1) k 0
  end.

Lemma zruns_go_lsum : forall f L n i cur acc, lsum f (zruns_go L i n cur acc) = lsum f acc + lsum f (zr L i n cur).
Proof.
  intros f L. induction n as [|n IH]; intros i cur acc; cbn [zruns_go zr].
  - destruct (cur =? 0); cbn; lia.
  - destruct (L i =? 0); [apply IH|]. rewrite IH, lsum_app. destruct (cur =? 0); cbn; lia.
Qed.

Lemma zruns_lsum : forall f L lo n, lsum f (zruns L lo n) = lsum f (zr L lo n 0).
Proof. intros. unfold zruns. rewrite zruns_go_lsum. cbn. lia. Qed.

Lemma zr_zeros : forall L c m i cur, (forall j, i <= j < i + Z.of_nat c -> L j = 0) ->
  zr L i (c + m) cur = zr L (i + Z.of_nat c) m (cur + Z.of_nat c).
Proof.
  intros L. induction c as [|c IH]; intros m i cur Hz.
  - cbn [Nat.add]. rewrite !Z.add_0_r. reflexivity.
  - cbn [Nat.add zr]. rewrite (proj2 (Z.eqb_eq _ _) (Hz i ltac:(lia))).
    rewrite (IH m (i + 1) (cur + 1)) by (intros; apply Hz; lia). f_equal; lia.
Qed.

Lemma zr_nonzero : forall L m i cur, L i <> 0 -> zr L i (S m) cur = (if cur =? 0 then [] else [cur]) ++ zr L (i + 1) m 0.
Proof. intros L m i cur H. cbn [zr]. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma zr_end : forall L i cur, zr L i 0 cur = (if cur =? 0 then [] else [cur]).
Proof. reflexivity. Qed.

Lemma zr_sum : forall L n i cur, 0 <= cur ->
  lsum (fun r => r) (zr L i n cur) = cur + zsum (fun j => zind (L j =? 0)) i n.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc; cbn [zr].
  - cbn [zsum]. destruct (Z.eqb_spec cur 0); cbn; lia.
  - rewrite zsum_shift. cbv beta. destruct (Z.eqb_spec (L i) 0); cbn [zind].
    + rewrite IH by lia. lia.
    + rewrite lsum_app, IH by lia. destruct (Z.eqb_spec cur 0); cbn; lia.
Qed.

Lemma zr_pos : forall L n i cur, 0 <= cur -> forall r, In r (zr L i n cur) -> 1 <= r.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc r Hr; cbn [zr] in Hr.
  - destruct (Z.eqb_spec cur 0); cbn in Hr; [tauto | lia].
  - destruct (L i =? 0); [exact (IH (i + 1) (cur + 1) ltac:(lia) r Hr)|].
    apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [| exact (IH (i + 1) 0 ltac:(lia) r Hr)].
    destruct (Z.eqb_spec cur 0); cbn in Hr; [tauto | lia].
Qed.

Lemma zr_length : forall L n i cur, 0 <= cur ->
  Z.of_nat (length (zr L i n cur)) <= zsum (fun j => zind (negb (L j =? 0))) i n + 1.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc; cbn [zr].
  - cbn [zsum]. destruct (cur =? 0); cbn; lia.
  - rewrite zsum_shift. cbv beta. destruct (Z.eqb_spec (L i) 0); cbn [negb zind].
    + pose proof (IH (i + 1) (cur + 1) ltac:(lia)). lia.
    + rewrite length_app, Nat2Z.inj_add. pose proof (IH (i + 1) 0 ltac:(lia)).
      destruct (cur =? 0); cbn [length Z.of_nat Pos.of_succ_nat]; lia.
Qed.

Lemma zr_bound : forall L n i cur, 0 <= cur -> forall r, In r (zr L i n cur) -> r <= cur + Z.of_nat n.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc r Hr; cbn [zr] in Hr.
  - destruct (Z.eqb_spec cur 0); cbn in Hr; [tauto | lia].
  - destruct (L i =? 0); [pose proof (IH (i + 1) (cur + 1) ltac:(lia) r Hr); lia|].
    apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [| pose proof (IH (i + 1) 0 ltac:(lia) r Hr); lia].
    destruct (Z.eqb_spec cur 0); cbn in Hr; [tauto | lia].
Qed.

Lemma zr_split : forall f L a b i cur, L (i + Z.of_nat a) <> 0 ->
  lsum f (zr L i (a + S b) cur) = lsum f (zr L i a cur) + lsum f (zr L (i + Z.of_nat a + 1) b 0).
Proof.
  intros f L. induction a as [|a IH]; intros b i cur Hnz.
  - cbn [Nat.add]. rewrite Z.add_0_r in Hnz |- *. rewrite zr_nonzero, lsum_app, zr_end by exact Hnz. reflexivity.
  - cbn [Nat.add zr]. destruct (L i =? 0).
    + rewrite (IH b (i + 1) (cur + 1)) by (replace (i + 1 + Z.of_nat a) with (i + Z.of_nat (S a)) by lia; exact Hnz).
      f_equal. f_equal. f_equal. lia.
    + rewrite !lsum_app, (IH b (i + 1) 0) by (replace (i + 1 + Z.of_nat a) with (i + Z.of_nat (S a)) by lia; exact Hnz).
      replace (i + 1 + Z.of_nat a + 1) with (i + Z.of_nat (S a) + 1) by lia. lia.
Qed.

Lemma zruns_sum : forall L lo n, lsum (fun r => r) (zruns L lo n) = zsum (fun j => zind (L j =? 0)) lo n.
Proof. intros. rewrite zruns_lsum, zr_sum by lia. lia. Qed.

Lemma zruns_pos : forall L lo n r, In r (zruns L lo n) -> 1 <= r <= Z.of_nat n.
Proof.
  intros L lo n r Hr. unfold zruns in Hr.
  assert (G : forall m i cur acc B, 0 <= cur -> cur + Z.of_nat m <= B -> (forall x, In x acc -> 1 <= x <= B) ->
             forall x, In x (zruns_go L i m cur acc) -> 1 <= x <= B).
  { induction m as [|m IH]; intros i cur acc B Hc HB Hacc x Hx; cbn [zruns_go] in Hx.
    - destruct (Z.eqb_spec cur 0); [exact (Hacc x Hx)|]. destruct Hx as [<-|Hx]; [lia | exact (Hacc x Hx)].
    - destruct (L i =? 0).
      + exact (IH (i + 1) (cur + 1) acc B ltac:(lia) ltac:(lia) Hacc x Hx).
      + apply (IH (i + 1) 0 (if cur =? 0 then acc else cur :: acc) B ltac:(lia) ltac:(lia)); [| exact Hx].
        intros y Hy. destruct (Z.eqb_spec cur 0); [exact (Hacc y Hy)|]. destruct Hy as [<-|Hy]; [lia | exact (Hacc y Hy)]. }
  exact (G n lo 0 [] (Z.of_nat n) ltac:(lia) ltac:(lia) ltac:(intros x Hx; destruct Hx) r Hr).
Qed.

Lemma zruns_length : forall L lo n, Z.of_nat (length (zruns L lo n)) <= zsum (fun j => zind (negb (L j =? 0))) lo n + 1.
Proof.
  intros. pose proof (zr_length L n lo 0 ltac:(lia)).
  assert (E : forall l, Z.of_nat (length l) = lsum (fun _ => 1) l) by (induction l; cbn [length lsum]; lia).
  rewrite E, zruns_lsum, <- E. exact H.
Qed.

Lemma zruns_split : forall f L lo a b, L (lo + Z.of_nat a) <> 0 ->
  lsum f (zruns L lo (a + S b)) = lsum f (zruns L lo a) + lsum f (zruns L (lo + Z.of_nat a + 1) b).
Proof. intros. rewrite !zruns_lsum. apply zr_split. exact H. Qed.

End OverlayRuns.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record oprm := {
  p_lbs : Z;
  p_LL : Z;
  p_blc : Z;
  p_d1 : Z;
  p_n1 : Z;
  p_rnum : Z;
  p_rden : Z
}.

Definition orow := (list (ovar * Z) * cmp * Z)%type.
Definition mk (l : list (ovar * Z)) (c : cmp) (r : Z) : orow := (l, c, r).

Definition lens (prm : oprm) : list Z := zrange 1 (Z.to_nat (p_LL prm)).
Definition ks (n : nat) : list nat := seq 0 n.
Definition cat {A} (l : list (list A)) : list A := concat l.

Definition scale (c : Z) (l : list (ovar * Z)) : list (ovar * Z) := map (fun '(v, a) => (v, c * a)) l.
Definition uL (k : nat) (l : Z) : list (ovar * Z) := [(OU1 k l, 1); (OU2 k l, 1); (OU3 k l, 1)].
Definition FL (k : nat) (l : Z) : list (ovar * Z) := [(OU1 k l, 1); (OU2 k l, 2); (OF3 k l, 1)].
Definition vD (k : nat) (m : Z) : list (ovar * Z) :=
  [(OV1 k m, 1); (OV2 k m, 1); (OV3 k m, 1)] ++ (if Nat.eqb k 0 then [(OVF m, 1)] else []).
Definition GD (k : nat) (m : Z) : list (ovar * Z) := [(OV1 k m, 1); (OV2 k m, 2); (OG3 k m, 1)].

Definition capL (prm : oprm) (l : Z) : Z := p_lbs prm / fib (l + 1).
Definition capD (prm : oprm) (m : Z) : Z := (p_lbs prm + 1) / fib (m + 1).

Section Gen.
Variable prm : oprm.
Let Ls := lens prm.
Let lbs := p_lbs prm.

Definition rows_class : list orow :=
  map (fun k => mk (cat (map (uL k) Ls)) (if is_eob k then Eq else Le) (Z.of_nat (length (lc_codes (lcl k))))) (ks nLC)
  ++ map (fun k => mk (cat (map (vD k) Ls)) Le (Z.of_nat (length (dc_codes (dcl k))))) (ks nDC)
  ++ cat (map (fun k => if is_eob k then cat (map (fun l => [mk [(OU2 k l, 1)] Eq 0; mk [(OU3 k l, 1)] Eq 0]) Ls) else []) (ks nLC)).
Definition rows_dmin : list orow :=
  [mk (cat (map (fun k => cat (map (vD k) Ls)) (ks nDC))) Ge 2; mk (map (fun m => (OVF m, 1)) Ls) Le 2].
Definition rows_cells : list orow :=
  cat (map (fun k => cat (map (fun l =>
        [mk [(OF3 k l, 1); (OU3 k l, -3)] Ge 0; mk [(OF3 k l, 1); (OU3 k l, - capL prm l)] Le 0]
        ++ (if capL prm l <? 2 then [mk [(OU2 k l, 1)] Eq 0] else [])) Ls)) (ks nLC))
  ++ cat (map (fun k => cat (map (fun m =>
        [mk [(OG3 k m, 1); (OV3 k m, -3)] Ge 0; mk [(OG3 k m, 1); (OV3 k m, - capD prm m)] Le 0]
        ++ (if capD prm m <? 2 then [mk [(OV2 k m, 1)] Eq 0] else [])) Ls)) (ks nDC)).
Definition rows_kraft : list orow :=
  [mk (cat (map (fun k => cat (map (fun l => scale (2 ^ (15 - l)) (uL k l)) Ls)) (ks nLC))) Eq (2 ^ 15);
   mk (cat (map (fun k => cat (map (fun m => scale (2 ^ (15 - m)) (vD k m)) Ls)) (ks nDC))) Eq (2 ^ 15)].
Definition rows_defs : list orow :=
  [mk (cat (map (fun k => if is_len k then cat (map (FL k) Ls) else []) (ks nLC)) ++ [(OP, -1)]) Eq 0;
   mk (cat (map (fun k => if is_lit k then cat (map (FL k) Ls) else []) (ks nLC)) ++ [(ONLIT, -1)]) Eq 0;
   mk [(OP, 1); (ONLIT, 1); (ON, -1)] Eq 0;
   mk (cat (map (fun k => cat (map (GD k) Ls)) (ks nDC)) ++ [(OP, -1)]) Eq 0;
   mk [(ON, 1)] Le (lbs - 1);
   mk (cat (map (fun k => cat (map (uL k) Ls)) (ks nLC)) ++ [(OU, -1)]) Eq 0;
   mk (cat (map (fun k => if is_lit k then cat (map (uL k) Ls) else []) (ks nLC)) ++ [(ONLITC, -1)]) Eq 0;
   mk (cat (map (fun k => if is_len k then cat (map (uL k) Ls) else []) (ks nLC)) ++ [(ONLENC, -1)]) Eq 0;
   mk (cat (map (fun k => cat (map (vD k) Ls)) (ks nDC)) ++ [(OV, -1)]) Eq 0;
   mk (cat (map (fun k => cat (map (fun l => scale (lc_SL (lcl k) - l) (FL k l)) Ls)) (ks nLC))
       ++ cat (map (fun k => cat (map (fun m => scale (5 - m) (GD k m)) Ls)) (ks nDC)) ++ [(OSV, -1)]) Eq 0].
Definition rows_case : list orow :=
  cat (map (fun l =>
    if l <? p_d1 prm then [mk (map (fun k => (OU1 k l, 1)) (ks nLC)) Eq 0]
    else if l =? p_d1 prm then [mk (map (fun k => (OU1 k l, 1)) (ks nLC)) Ge 1]
    else if l =? p_d1 prm + 1 then cat (map (fun k => [mk [(OU2 k l, 1)] Eq 0; mk [(OU3 k l, 1)] Eq 0]) (ks nLC))
    else cat (map (fun k => [mk [(OU1 k l, 1)] Eq 0; mk [(OU2 k l, 1)] Eq 0; mk [(OU3 k l, 1)] Eq 0]) (ks nLC))) Ls)
  ++ [mk (cat (map (fun k => uL k 1) (ks nLC))) Eq (p_n1 prm)].
Definition As : list Z := zrange 1 (Z.to_nat (p_LL prm + 5)).
Definition Bs : list Z := zrange 1 (Z.to_nat (p_LL prm + 13)).
Definition pairsAB : list (Z * Z) := cat (map (fun a => map (fun c => (a, c)) (filter (fun c => 24 <? a + c) Bs)) As).
Definition rows_ex : list orow :=
  map (fun a => mk (map (fun c => (OPI a c, 1)) (filter (fun c => 24 <? a + c) Bs)
                    ++ cat (map (fun k => cat (map (fun l => if is_len k && (l + lc_xl (lcl k) =? a) then scale (-1) (FL k l) else []) Ls)) (ks nLC)))
                Le 0) As
  ++ map (fun c => mk (map (fun a => (OPI a c, 1)) (filter (fun a => 24 <? a + c) As)
                    ++ cat (map (fun k => cat (map (fun m => if m + dc_xd (dcl k) =? c then scale (-1) (GD k m) else []) Ls)) (ks nDC)))
                Le 0) Bs
  ++ [mk ((OEX, 1) :: map (fun ac => (OPI (fst ac) (snd ac), - (fst ac + snd ac - 24))) pairsAB) Le 0].
Definition rows_bc : list orow :=
  map (fun j => mk ((OBC j, 1) :: (if j <=? p_LL prm then cat (map (fun k => scale (-1) (uL k j)) (ks nLC)) ++ cat (map (fun k => scale (-1) (vD k j)) (ks nDC)) else [])) Le 0)
      (zrange 1 15)
  ++ [mk (map (fun j => (OBC j, 1)) (zrange 1 15) ++ [(OBC 16, 3); (OU, -1); (OV, -1)]) Le 0;
      mk [(OBC 16, 4); (OU, -1); (OV, -1)] Le 0].
Definition rows_runs : list orow :=
  [mk [(OR1 1, 1); (OR2 1, 1); (ORA 1, 1); (ORB 1, 1); (ONLITC, -1); (ORLONG, -1)] Le 1;
   mk [(OR1 1, 1); (OR2 1, 2); (ORA 1, 3); (ORB 1, 11); (ORLONG, 138); (ONLITC, 1)] Le 256;
   mk [(OR1 1, 1); (OR2 1, 2); (ORA 1, 10); (ORB 1, 138); (ORLONG, 138); (ONLITC, 1)] Ge 256;
   mk [(OR1 2, 1); (OR2 2, 1); (ORA 2, 1); (ORB 2, 1); (ONLENC, -1)] Le 0;
   mk [(OR1 2, 1); (OR2 2, 2); (ORA 2, 3); (ORB 2, 11); (ONLENC, 1)] Le 29;
   mk [(OR1 3, 1); (OR2 3, 1); (ORA 3, 1); (ORB 3, 1); (OV, -1)] Le 0;
   mk [(OR1 3, 1); (OR2 3, 2); (ORA 3, 3); (ORB 3, 11); (OV, 1)] Le 30;
   mk [(OBC 0, 1); (OR1 1, -1); (OR1 2, -1); (OR1 3, -1); (OR2 1, -2); (OR2 2, -2); (OR2 3, -2)] Eq 0;
   mk [(OBC 17, 1); (ORA 1, -1); (ORA 2, -1); (ORA 3, -1)] Eq 0;
   mk [(OBC 18, 1); (ORB 1, -1); (ORB 2, -1); (ORB 3, -1); (ORLONG, -1)] Eq 0;
   mk (map (fun x => (OBC x, 1)) (zrange 0 19) ++ [(OWB, -1)]) Eq 0].
Definition tmax (tau : list Z) : Z := fold_right Z.max 0 tau.
Definition row_tpl (tau : list Z) : orow :=
  mk ((OB, p_rden prm) :: map (fun x => (OBC x, - (p_rden prm * nth (Z.to_nat x) tau 0 + p_rnum prm))) (zrange 0 19))
     Le (2 * (p_rden prm * tmax tau + p_rnum prm)).
Definition rows_hdr : list orow :=
  [mk [(OH, 1); (OB, -1); (OBC 16, -2); (OBC 17, -3); (OBC 18, -7)] Le (14 + 3 * p_blc prm);
   mk [(OH, 1); (OSV, -1)] Le (-1)].

Definition all_vars : list ovar :=
  cat (map (fun k => cat (map (fun l => [OU1 k l; OU2 k l; OU3 k l; OF3 k l]) Ls)) (ks nLC))
  ++ cat (map (fun k => cat (map (fun m => [OV1 k m; OV2 k m; OV3 k m; OG3 k m]) Ls)) (ks nDC))
  ++ map OVF Ls
  ++ [OP; ONLIT; ON; OSV; OEX; OH; OU; OV; ONLITC; ONLENC]
  ++ map (fun ac => OPI (fst ac) (snd ac)) pairsAB
  ++ map OBC (zrange 0 19) ++ [OWB; OB]
  ++ cat (map (fun r => [OR1 r; OR2 r; ORA r; ORB r]) [1; 2; 3]) ++ [ORLONG].

Definition ubound (v : ovar) : Z :=
  match v with
  | OU1 _ _ | OU2 _ _ | OU3 _ _ | OU => 286 | OF3 _ _ | OG3 _ _ | OP | ONLIT | ON | OPI _ _ => lbs
  | OV1 _ _ | OV2 _ _ | OV3 _ _ | OV => 32 | OVF _ => 2
  | OSV => 32 * lbs | OEX => 24 * lbs | OH => 2 ^ 18 | ONLITC => 256 | ONLENC => 29
  | OBC _ => 640 | OWB => 19 * 640 | OB => 7 * 19 * 640
  | OR1 _ | OR2 _ | ORA _ | ORB _ => 316 | ORLONG => 3
  end.

Definition orows (T : list (list Z)) : list orow :=
  rows_class ++ rows_dmin ++ rows_cells ++ rows_kraft ++ rows_defs ++ rows_case ++ rows_ex ++ rows_bc ++ rows_runs
  ++ map row_tpl T ++ rows_hdr ++ map (fun v => mk [(v, 1)] Le (ubound v)) all_vars.

Definition oobj : list (ovar * Z) := [(OH, 1); (OEX, 1)].
Definition obound : Z := 8 * lbs - 10.

End Gen.

Fixpoint index_of (v : ovar) (l : list ovar) (i : positive) : positive :=
  match l with [] => i | w :: r => if ovar_eqb v w then i else index_of v r (Pos.succ i) end.
Definition tr_lin (vs : list ovar) (l : list (ovar * Z)) : lin := map (fun '(v, a) => (index_of v vs 1%positive, a)) l.
Definition tr_row (vs : list ovar) (r : orow) : row :=
  let '(l, c, b) := r in mkrow (tr_lin vs l) c b.
Definition to_lp (prm : oprm) (T : list (list Z)) : lp :=
  let vs := all_vars prm in
  mklp (length vs) (map (tr_row vs) (orows prm T)) (tr_lin vs (oobj)) (obound prm).

Definition xval (prm : oprm) (b : oblock) (i : positive) : Z := oval b (nth (Nat.pred (Pos.to_nat i)) (all_vars prm) OP).

Fixpoint oeval (b : oblock) (l : list (ovar * Z)) : Z :=
  match l with [] => 0 | (v, a) :: r => a * oval b v + oeval b r end.
Definition oholds (b : oblock) (r : orow) : Prop :=
  let '(l, c, rhs) := r in
  match c with Le => oeval b l <= rhs | Ge => oeval b l >= rhs | Eq => oeval b l = rhs end.
Definition oholdsb (b : oblock) (r : orow) : bool :=
  let '(l, c, rhs) := r in
  match c with Le => oeval b l <=? rhs | Ge => rhs <=? oeval b l | Eq => oeval b l =? rhs end.

Definition KT : Z := 20.
Definition tpl_okb (tau : list Z) : bool :=
  forallb (fun x => (1 <=? nth (Z.to_nat x) tau 0) && (nth (Z.to_nat x) tau 0 <=? KT)) (zrange 0 19)
  && (zsum (fun x => 2 ^ (KT - nth (Z.to_nat x) tau 0)) 0 19 <=? 2 ^ KT).
Definition vwfb (v : ovar) : bool :=
  match v with OBC x => (0 <=? x) && (x <? 19) | _ => true end.
