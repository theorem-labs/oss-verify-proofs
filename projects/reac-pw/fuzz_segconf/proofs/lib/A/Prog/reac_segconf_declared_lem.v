(* The model facts the segments of the walk of reac_segconf_declared (fuzz_segconf.asan, image A) share: the steps of
   SegModel.r_decl_go that one pass of the loop takes, the answers of vlan_add and vlan_split, and the growth of the
   table (it only grows, never past max). Pure Gallina over SegModel; no machine state. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dcl_skipn_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
intros A l. induction l as [|x l IH]; intros k d H; cbn [length] in H; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(* one pass of the loop over c->seg: entry i ignored, entry i not split, entry i split and added; the end *)
Lemma dcl_go_ignore : forall segs i t max added, (i < length segs)%nat -> rs_ignore (nth i segs rseg_d) = true ->
  r_decl_go (skipn i segs) t max added = r_decl_go (skipn (S i) segs) t max added.
Proof.
intros segs i t max added Hi Hg. rewrite (dcl_skipn_cons segs i rseg_d Hi). cbn [r_decl_go]. rewrite Hg.
reflexivity.
Qed.

Lemma dcl_go_nosplit : forall segs i t max added, (i < length segs)%nat -> rs_ignore (nth i segs rseg_d) = false ->
  vlan_split (rs_name (nth i segs rseg_d)) = None ->
  r_decl_go (skipn i segs) t max added = r_decl_go (skipn (S i) segs) t max added.
Proof.
intros segs i t max added Hi Hg Hs. rewrite (dcl_skipn_cons segs i rseg_d Hi). cbn [r_decl_go]. rewrite Hg, Hs.
reflexivity.
Qed.

Lemma dcl_go_split : forall segs i t max added p v, (i < length segs)%nat -> rs_ignore (nth i segs rseg_d) = false ->
  vlan_split (rs_name (nth i segs rseg_d)) = Some (p, v) ->
  r_decl_go (skipn i segs) t max added =
  if fst (vlan_add t max p v) <? 0 then (-1, snd (vlan_add t max p v))
  else r_decl_go (skipn (S i) segs) (snd (vlan_add t max p v)) max (added + fst (vlan_add t max p v)).
Proof.
intros segs i t max added p v Hi Hg Hs. rewrite (dcl_skipn_cons segs i rseg_d Hi). cbn [r_decl_go]. rewrite Hg, Hs.
destruct (vlan_add t max p v) as [rv t']. reflexivity.
Qed.

Lemma dcl_go_end : forall segs t max added, r_decl_go (skipn (length segs) segs) t max added = (added, t).
Proof. intros segs t max added. rewrite skipn_all. reflexivity. Qed.

(* vlan_add answers 0, 1 or -1; -1 leaves the table as it was *)
Lemma dcl_add_rv : forall t max p v,
  fst (vlan_add t max p v) = 0 \/ fst (vlan_add t max p v) = 1 \/ fst (vlan_add t max p v) = -1.
Proof.
intros t max p v. unfold vlan_add.
destruct (existsb _ t); [left; reflexivity|].
destruct (max <=? Z.of_nat (length t)); [right; right; reflexivity | right; left; reflexivity].
Qed.

Lemma dcl_add_neg : forall t max p v, fst (vlan_add t max p v) < 0 -> snd (vlan_add t max p v) = t.
Proof.
intros t max p v. unfold vlan_add.
destruct (existsb _ t); [cbn; lia|].
destruct (max <=? Z.of_nat (length t)); cbn; [reflexivity | lia].
Qed.

(* vlan_add only appends, and only below max *)
Lemma dcl_add_len : forall t max p v, Z.of_nat (length t) <= max ->
  (length t <= length (snd (vlan_add t max p v)))%nat /\ Z.of_nat (length (snd (vlan_add t max p v))) <= max.
Proof.
intros t max p v H. unfold vlan_add.
match goal with |- context [if existsb ?f ?l then _ else _] => destruct (existsb f l) end; [cbn [snd]; lia|].
destruct (max <=? Z.of_nat (length t)) eqn:E; [cbn [snd]; lia|].
apply Z.leb_gt in E. cbn [snd]. rewrite length_app. cbn [length]. lia.
Qed.

(* the table grows only, through the rest of the loop, and never past max *)
Lemma dcl_go_len : forall segs t max added, Z.of_nat (length t) <= max ->
  (length t <= length (snd (r_decl_go segs t max added)))%nat /\
  Z.of_nat (length (snd (r_decl_go segs t max added))) <= max.
Proof.
induction segs as [|s r IH]; intros t max added H; cbn [r_decl_go]; [cbn [snd]; lia|].
destruct (rs_ignore s); [apply IH; exact H|].
destruct (vlan_split (rs_name s)) as [[p v]|]; [|apply IH; exact H].
pose proof (dcl_add_len t max p v H) as L.
destruct (vlan_add t max p v) as [rv t'] eqn:E. cbn [snd] in L.
destruct (rv <? 0); [cbn [snd]; exact L|].
destruct (IH t' max (added + rv) (proj2 L)) as [A1 A2]. split; [lia | exact A2].
Qed.

(* vlan_split's vid is a uint16_t and its parent has at most 15 bytes *)
Lemma dcl_split_some : forall s p v, vlan_split s = Some (p, v) -> 0 <= v < 65536 /\ (length p <= 15)%nat.
Proof.
intros s p v. unfold vlan_split. destruct (strrchr s DOT) as [d|]; [|discriminate]. cbv zeta.
repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  intros H; try discriminate H.
injection H as <- <-.
repeat match goal with H : (_ || _)%bool = false |- _ => apply orb_false_iff in H as [? ?] end.
match goal with H : (16 <? d + 1)%nat = false |- _ => apply Nat.ltb_ge in H end.
split; [apply Z.mod_pos_bound; lia|]. rewrite length_firstn. lia.
Qed.

(* the count added so far stays between 0 and the number of passes done *)
Lemma dcl_add_rv_nonneg : forall t max p v, ~ fst (vlan_add t max p v) < 0 ->
  0 <= fst (vlan_add t max p v) <= 1.
Proof. intros t max p v H. destruct (dcl_add_rv t max p v) as [E | [E | E]]; rewrite E in *; lia. Qed.
