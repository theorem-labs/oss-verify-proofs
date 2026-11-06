(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require ZArith Lia.
Module CmpSdArith2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CmpSdArith2.

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Ltac2 Require Import Ltac2.
From Ltac2 Require FMap FSet.
Set Default Proof Mode "Classic".
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RC.

Inductive expr : Set :=
| EA (i : nat) | EC (z : Z) | EPow (b n : Z)
| EAdd (a b : expr) | ESub (a b : expr) | EOpp (a : expr) | EMul (a b : expr)
| EDiv (a b : expr) | EMod (a b : expr).

Fixpoint interp (env : list Z) (e : expr) : Z :=
  match e with
  | EA i => nth i env 0
  | EC z => z
  | EPow b n => b ^ n
  | EAdd a b => interp env a + interp env b
  | ESub a b => interp env a - interp env b
  | EOpp a => - interp env a
  | EMul a b => interp env a * interp env b
  | EDiv a b => interp env a / interp env b
  | EMod a b => interp env a mod interp env b
  end.

Fixpoint expr_eqb (a b : expr) : bool :=
  match a, b with
  | EA i, EA j => Nat.eqb i j
  | EC x, EC y => Z.eqb x y
  | EPow b1 n1, EPow b2 n2 => Z.eqb b1 b2 && Z.eqb n1 n2
  | EAdd a1 a2, EAdd b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | ESub a1 a2, ESub b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EOpp a1, EOpp b1 => expr_eqb a1 b1
  | EMul a1 a2, EMul b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EDiv a1 a2, EDiv b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EMod a1 a2, EMod b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | _, _ => false
  end.

Lemma expr_eqb_eq : forall a b, expr_eqb a b = true -> a = b.
Proof.
  induction a; intros e2; destruct e2; cbn; intros H; try discriminate;
    repeat match goal with
           | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
           end;
    repeat match goal with
           | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H; subst
           | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst
           | IH : forall b, expr_eqb ?a b = true -> ?a = b, H : expr_eqb ?a _ = true |- _ => apply IH in H; subst
           end; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition itv := (option Z * option Z)%type.
Definition in_lo (x : Z) (o : option Z) : Prop := match o with Some l => l <= x | None => True end.
Definition in_hi (x : Z) (o : option Z) : Prop := match o with Some h => x <= h | None => True end.
Definition in_itv (x : Z) (V : itv) : Prop := in_lo x (fst V) /\ in_hi x (snd V).
Definition itop : itv := (None, None).
Definition ipt (z : Z) : itv := (Some z, Some z).

Definition oadd (a b : option Z) : option Z := match a, b with Some x, Some y => Some (x + y) | _, _ => None end.
Definition omap (f : Z -> Z) (a : option Z) : option Z := match a with Some x => Some (f x) | None => None end.
Definition omax (a b : option Z) : option Z := match a, b with Some x, Some y => Some (Z.max x y) | Some x, None => Some x | None, o => o end.
Definition omin (a b : option Z) : option Z := match a, b with Some x, Some y => Some (Z.min x y) | Some x, None => Some x | None, o => o end.

Definition iadd (V W : itv) : itv := (oadd (fst V) (fst W), oadd (snd V) (snd W)).
Definition iopp (V : itv) : itv := (omap Z.opp (snd V), omap Z.opp (fst V)).
Definition isub (V W : itv) : itv := iadd V (iopp W).
Definition iscale (c : Z) (V : itv) : itv :=
  if c =? 0 then ipt 0
  else if 0 <? c then (omap (Z.mul c) (fst V), omap (Z.mul c) (snd V))
  else (omap (Z.mul c) (snd V), omap (Z.mul c) (fst V)).
Definition ipoint (V : itv) : option Z :=
  match V with (Some l, Some h) => if l =? h then Some l else None | _ => None end.
Definition imul (V W : itv) : itv :=
  match ipoint V with
  | Some c => iscale c W
  | None => match ipoint W with Some c => iscale c V | None => itop end
  end.
Definition idiv (V W : itv) : itv :=
  match ipoint W with
  | Some c => if 0 <? c then (omap (fun l => l / c) (fst V), omap (fun h => h / c) (snd V)) else itop
  | None => itop
  end.
Definition imod (V W : itv) : itv :=
  match ipoint W with
  | Some c => if 0 <? c then
                match V with
                | (Some l, Some h) => if (0 <=? l) && (h <? c) then V else (Some 0, Some (c - 1))
                | _ => (Some 0, Some (c - 1))
                end
              else itop
  | None => itop
  end.
Definition imeet (V W : itv) : itv := (omax (fst V) (fst W), omin (snd V) (snd W)).

Lemma in_itv_top : forall x, in_itv x itop. Proof. intros; split; exact Logic.I. Qed.
Lemma in_itv_pt : forall x, in_itv x (ipt x). Proof. intros; split; cbn; lia. Qed.
Lemma ipoint_ok : forall x V c, in_itv x V -> ipoint V = Some c -> x = c.
Proof.
  intros x [[l|] [h|]] c [H1 H2]; cbn in *; try discriminate.
  destruct (Z.eqb_spec l h); [|discriminate]. intros [= <-]. lia.
Qed.
Lemma iadd_ok : forall x y V W, in_itv x V -> in_itv y W -> in_itv (x + y) (iadd V W).
Proof. intros x y [[?|] [?|]] [[?|] [?|]] [? ?] [? ?]; split; cbn in *; lia. Qed.
Lemma iopp_ok : forall x V, in_itv x V -> in_itv (- x) (iopp V).
Proof. intros x [[?|] [?|]] [? ?]; split; cbn in *; lia. Qed.
Lemma isub_ok : forall x y V W, in_itv x V -> in_itv y W -> in_itv (x - y) (isub V W).
Proof. intros. unfold isub. replace (x - y) with (x + - y) by lia. apply iadd_ok; [assumption| apply iopp_ok; assumption]. Qed.
Lemma iscale_ok : forall c x V, in_itv x V -> in_itv (c * x) (iscale c V).
Proof.
  intros c x V [H1 H2]. unfold iscale.
  destruct (Z.eqb_spec c 0) as [->|]; [rewrite Z.mul_0_l; apply in_itv_pt|].
  destruct (Z.ltb_spec 0 c); destruct V as [[l|] [h|]]; split; cbn in *; try exact Logic.I; nia.
Qed.
Lemma imul_ok : forall x y V W, in_itv x V -> in_itv y W -> in_itv (x * y) (imul V W).
Proof.
  intros x y V W HI HJ. unfold imul.
  destruct (ipoint V) as [c|] eqn:E.
  - rewrite (ipoint_ok x V c HI E). apply iscale_ok; assumption.
  - destruct (ipoint W) as [c|] eqn:E'; [|apply in_itv_top].
    rewrite (ipoint_ok y W c HJ E'), Z.mul_comm. apply iscale_ok; assumption.
Qed.
Lemma idiv_ok : forall x y V W, in_itv x V -> in_itv y W -> in_itv (x / y) (idiv V W).
Proof.
  intros x y V W HI HJ. unfold idiv.
  destruct (ipoint W) as [c|] eqn:E; [|apply in_itv_top].
  rewrite (ipoint_ok y W c HJ E). destruct (Z.ltb_spec 0 c) as [Hc|Hc]; [|apply in_itv_top].
  destruct HI as [HI1 HI2]. destruct V as [[l|] [h|]]; split; cbn in *; try exact Logic.I; apply Z.div_le_mono; lia.
Qed.
Lemma imod_ok : forall x y V W, in_itv x V -> in_itv y W -> in_itv (x mod y) (imod V W).
Proof.
  intros x y V W HI HJ. unfold imod.
  destruct (ipoint W) as [c|] eqn:E; [|apply in_itv_top].
  rewrite (ipoint_ok y W c HJ E). destruct (Z.ltb_spec 0 c) as [Hc|Hc]; [|apply in_itv_top].
  pose proof (Z.mod_pos_bound x c ltac:(lia)) as HM.
  assert (D : in_itv (x mod c) (Some 0, Some (c - 1))) by (split; cbn; lia).
  destruct V as [[l|] [h|]]; try exact D.
  destruct (Z.leb_spec 0 l) as [Hl|Hl]; cbn [andb]; [|exact D]. destruct (Z.ltb_spec h c) as [Hh|Hh]; [|exact D].
  destruct HI as [HI1 HI2]; cbn in HI1, HI2. rewrite Z.mod_small by lia. split; cbn; lia.
Qed.
Lemma imeet_ok : forall x V W, in_itv x V -> in_itv x W -> in_itv x (imeet V W).
Proof. intros x [[?|] [?|]] [[?|] [?|]] [? ?] [? ?]; split; cbn in *; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bnds := list (nat * itv).
Fixpoint blookup (B : bnds) (i : nat) : itv :=
  match B with
  | [] => itop
  | (j, V) :: t => if Nat.eqb i j then V else blookup t i
  end.
Definition bvalid (env : list Z) (B : bnds) : Prop := forall i V, In (i, V) B -> in_itv (nth i env 0) V.
Lemma blookup_ok : forall env B i, bvalid env B -> in_itv (nth i env 0) (blookup B i).
Proof.
  induction B as [|[j V] t IH]; intros i HB; cbn; [apply in_itv_top|].
  destruct (Nat.eqb_spec i j) as [->|]; [apply HB; left; reflexivity|].
  apply IH. intros k K HK. apply HB. right. exact HK.
Qed.
Lemma bvalid_nil : forall env, bvalid env []. Proof. intros env i V []. Qed.
Lemma bvalid_cons : forall env B i V, bvalid env B -> in_itv (nth i env 0) V -> bvalid env ((i, V) :: B).
Proof. intros env B i V HB HI k K [E|HK]; [injection E as <- <-; exact HI| apply HB; exact HK]. Qed.

Fixpoint ival (B : bnds) (e : expr) : itv :=
  match e with
  | EA i => blookup B i
  | EC z => ipt z
  | EPow b n => ipt (b ^ n)
  | EAdd a b => iadd (ival B a) (ival B b)
  | ESub a b => isub (ival B a) (ival B b)
  | EOpp a => iopp (ival B a)
  | EMul a b => imul (ival B a) (ival B b)
  | EDiv a b => idiv (ival B a) (ival B b)
  | EMod a b => imod (ival B a) (ival B b)
  end.
Lemma ival_ok : forall env B e, bvalid env B -> in_itv (interp env e) (ival B e).
Proof.
  intros env B e HB. induction e; cbn.
  - apply blookup_ok; exact HB.
  - apply in_itv_pt.
  - apply in_itv_pt.
  - apply iadd_ok; assumption.
  - apply isub_ok; assumption.
  - apply iopp_ok; assumption.
  - apply imul_ok; assumption.
  - apply idiv_ok; assumption.
  - apply imod_ok; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lin := list (expr * Z).
Definition lform := (lin * Z)%type.
Fixpoint eval_lin (env : list Z) (l : lin) : Z :=
  match l with [] => 0 | (k, c) :: t => c * interp env k + eval_lin env t end.
Definition eval_lf (env : list Z) (lf : lform) : Z := eval_lin env (fst lf) + snd lf.

Fixpoint ladd1 (k : expr) (c : Z) (l : lin) : lin :=
  match l with
  | [] => [(k, c)]
  | (k', c') :: t => if expr_eqb k k' then (k', c + c') :: t else (k', c') :: ladd1 k c t
  end.
Fixpoint ladd (l1 l2 : lin) : lin :=
  match l1 with [] => l2 | (k, c) :: t => ladd1 k c (ladd t l2) end.
Definition lscale (c : Z) (l : lin) : lin := map (fun kc => (fst kc, c * snd kc)) l.
Definition lf_add (a b : lform) : lform := (ladd (fst a) (fst b), snd a + snd b).
Definition lf_scale (c : Z) (a : lform) : lform := (lscale c (fst a), c * snd a).

Lemma ladd1_ok : forall env k c l, eval_lin env (ladd1 k c l) = c * interp env k + eval_lin env l.
Proof.
  induction l as [|[k' c'] t IH]; cbn; [lia|].
  destruct (expr_eqb k k') eqn:E; cbn.
  - apply expr_eqb_eq in E. subst. lia.
  - rewrite IH. lia.
Qed.
Lemma ladd_ok : forall env l1 l2, eval_lin env (ladd l1 l2) = eval_lin env l1 + eval_lin env l2.
Proof. induction l1 as [|[k c] t IH]; intros l2; cbn; [lia|]. rewrite ladd1_ok, IH. lia. Qed.
Lemma lscale_ok : forall env c l, eval_lin env (lscale c l) = c * eval_lin env l.
Proof. induction l as [|[k d] t IH]; cbn [lscale map eval_lin fst snd]; [lia|]. fold (lscale c t). rewrite IH. lia. Qed.
Lemma lf_add_ok : forall env a b, eval_lf env (lf_add a b) = eval_lf env a + eval_lf env b.
Proof. intros env [l1 c1] [l2 c2]. unfold eval_lf, lf_add; cbn [fst snd]. rewrite ladd_ok. lia. Qed.
Lemma lf_scale_ok : forall env c a, eval_lf env (lf_scale c a) = c * eval_lf env a.
Proof. intros env c [l d]. unfold eval_lf, lf_scale; cbn [fst snd]. rewrite lscale_ok. lia. Qed.

Fixpoint lin_of (e : expr) : lform :=
  match e with
  | EA i => ([(EA i, 1)], 0)
  | EC z => ([], z)
  | EPow b n => ([], b ^ n)
  | EAdd a b => lf_add (lin_of a) (lin_of b)
  | ESub a b => lf_add (lin_of a) (lf_scale (-1) (lin_of b))
  | EOpp a => lf_scale (-1) (lin_of a)
  | EMul a b =>
      match lin_of a, lin_of b with
      | ([], c), lb => lf_scale c lb
      | la, ([], c) => lf_scale c la
      | _, _ => ([(EMul a b, 1)], 0)
      end
  | EDiv a b => ([(EDiv a b, 1)], 0)
  | EMod a b => ([(EMod a b, 1)], 0)
  end.
Lemma lin_of_ok : forall env e, eval_lf env (lin_of e) = interp env e.
Proof.
  intros env e. induction e; cbn [lin_of interp].
  - unfold eval_lf; cbn [eval_lin fst snd interp]. lia.
  - unfold eval_lf; cbn [eval_lin fst snd interp]. lia.
  - unfold eval_lf; cbn [eval_lin fst snd interp]. lia.
  - rewrite lf_add_ok, IHe1, IHe2. reflexivity.
  - rewrite lf_add_ok, lf_scale_ok, IHe1, IHe2. lia.
  - rewrite lf_scale_ok, IHe. lia.
  - destruct (lin_of e1) as [[|p1 t1] c1] eqn:E1.
    + rewrite lf_scale_ok, IHe2. rewrite <- IHe1. unfold eval_lf; cbn [eval_lin fst snd]. lia.
    + destruct (lin_of e2) as [[|p2 t2] c2] eqn:E2.
      * rewrite lf_scale_ok, IHe1. rewrite <- IHe2. unfold eval_lf; cbn [eval_lin fst snd]. lia.
      * unfold eval_lf; cbn [eval_lin fst snd interp]. lia.
  - unfold eval_lf; cbn [eval_lin fst snd interp]. lia.
  - unfold eval_lf; cbn [eval_lin fst snd interp]. lia.
Qed.

Fixpoint ival_lin (B : bnds) (l : lin) : itv :=
  match l with [] => ipt 0 | (k, c) :: t => iadd (iscale c (ival B k)) (ival_lin B t) end.
Definition ival_lf (B : bnds) (lf : lform) : itv := iadd (ival_lin B (fst lf)) (ipt (snd lf)).
Lemma ival_lin_ok : forall env B l, bvalid env B -> in_itv (eval_lin env l) (ival_lin B l).
Proof.
  intros env B l HB. induction l as [|[k c] t IH]; cbn; [apply in_itv_pt|].
  apply iadd_ok; [apply iscale_ok, ival_ok; exact HB| exact IH].
Qed.
Lemma ival_lf_ok : forall env B lf, bvalid env B -> in_itv (eval_lf env lf) (ival_lf B lf).
Proof. intros env B [l c] HB. unfold eval_lf, ival_lf; cbn. apply iadd_ok; [apply ival_lin_ok; exact HB| apply in_itv_pt]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive fact : Set := FLe (a b : expr) | FLt (a b : expr) | FEq (a b : expr).
Definition interp_fact (env : list Z) (f : fact) : Prop :=
  match f with
  | FLe a b => interp env a <= interp env b
  | FLt a b => interp env a < interp env b
  | FEq a b => interp env a = interp env b
  end.
Fixpoint interp_facts (env : list Z) (fs : list fact) : Prop :=
  match fs with [] => True | f :: t => interp_fact env f /\ interp_facts env t end.

(* [comment removed for export] *)
Definition fact_lf (f : fact) (dir : bool) : option lform :=
  match f with
  | FLe a b => if dir then None else Some (lin_of (ESub a b))
  | FLt a b => if dir then None else Some (lin_of (ESub (EAdd a (EC 1)) b))
  | FEq a b => Some (if dir then lin_of (ESub b a) else lin_of (ESub a b))
  end.
Lemma some_inj : forall (A : Type) (x y : A), Some x = Some y -> x = y.
Proof. intros A x y E. congruence. Qed.
Lemma fact_lf_ok : forall env f dir lf, interp_fact env f -> fact_lf f dir = Some lf -> eval_lf env lf <= 0.
Proof.
  intros env f dir lf H E. destruct f; destruct dir; cbn [fact_lf interp_fact] in *; try discriminate;
    apply some_inj in E; subst lf; rewrite lin_of_ok; cbn [interp]; lia.
Qed.
Lemma interp_facts_nth : forall env fs j f, interp_facts env fs -> nth_error fs j = Some f -> interp_fact env f.
Proof.
  induction fs as [|g t IH]; intros [|j] f H E; cbn in *; try discriminate.
  - injection E as <-. tauto.
  - apply (IH j); tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record step : Set := mkStep { s_fact : nat; s_dir : bool; s_pos : nat }.

Fixpoint lsplit (p : nat) (l : lin) : option ((expr * Z) * lin) :=
  match l with
  | [] => None
  | x :: t => match p with
              | O => Some (x, t)
              | S q => match lsplit q t with Some (y, r) => Some (y, x :: r) | None => None end
              end
  end.
Lemma lsplit_ok : forall env p l k c r, lsplit p l = Some ((k, c), r) -> eval_lin env l = c * interp env k + eval_lin env r.
Proof.
  induction p as [|q IH]; intros [|[k' c'] t] k c r E; cbn in *; try discriminate.
  - injection E as -> -> ->. reflexivity.
  - destruct (lsplit q t) as [[[k2 c2] r2]|] eqn:E2; [|discriminate]. injection E as -> -> <-.
    cbn. rewrite (IH t k c r2 E2). lia.
Qed.

(* [comment removed for export] *)
Definition derive (B : bnds) (lf : lform) (p : nat) : option (nat * itv) :=
  match lsplit p (fst lf) with
  | Some ((EA i, c), r) =>
      match fst (ival_lf B (r, snd lf)) with
      | Some lo =>
          if 0 <? c then Some (i, (None, Some ((- lo) / c)))
          else if c <? 0 then Some (i, (Some (- ((- lo) / (- c))), None))
          else None
      | None => None
      end
  | _ => None
  end.
Lemma derive_ok : forall env B lf p i V, bvalid env B -> eval_lf env lf <= 0 -> derive B lf p = Some (i, V) -> in_itv (nth i env 0) V.
Proof.
  intros env B [l d] p i V HB HL E. unfold derive in E; cbn [fst snd] in E.
  destruct (lsplit p l) as [[[k c] r]|] eqn:ES; [|discriminate]. destruct k; try discriminate.
  pose proof (lsplit_ok env p l _ _ _ ES) as EQ. cbn [interp] in EQ.
  pose proof (ival_lf_ok env B (r, d) HB) as [HR _]. unfold eval_lf in HR, HL; cbn [fst snd] in HR, HL.
  destruct (fst (ival_lf B (r, d))) as [lo|]; [|discriminate]. cbn in HR.
  destruct (Z.ltb_spec 0 c).
  - injection E as <- <-. split; cbn; [exact Logic.I|]. apply Z.div_le_lower_bound; lia.
  - destruct (Z.ltb_spec c 0); [|discriminate]. injection E as <- <-. split; cbn; [|exact Logic.I].
    assert (- nth i0 env 0 <= (- lo) / (- c)) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Definition apply_step (fs : list fact) (B : bnds) (s : step) : bnds :=
  match nth_error fs (s_fact s) with
  | Some f => match fact_lf f (s_dir s) with
              | Some lf => match derive B lf (s_pos s) with
                           | Some (i, V) => (i, imeet (blookup B i) V) :: B
                           | None => B
                           end
              | None => B
              end
  | None => B
  end.
Lemma apply_step_ok : forall env fs B s, interp_facts env fs -> bvalid env B -> bvalid env (apply_step fs B s).
Proof.
  intros env fs B s HF HB. unfold apply_step.
  destruct (nth_error fs (s_fact s)) as [f|] eqn:E; [|exact HB].
  destruct (fact_lf f (s_dir s)) as [lf|] eqn:EL; [|exact HB].
  destruct (derive B lf (s_pos s)) as [[i V]|] eqn:ED; [|exact HB].
  apply bvalid_cons; [exact HB|]. apply imeet_ok; [apply blookup_ok; exact HB|].
  eapply derive_ok; [exact HB| |exact ED]. eapply fact_lf_ok; [|exact EL]. eapply interp_facts_nth; eassumption.
Qed.
Definition apply_steps (fs : list fact) (B : bnds) (ss : list step) : bnds := fold_left (apply_step fs) ss B.
Lemma apply_steps_ok : forall env fs ss B, interp_facts env fs -> bvalid env B -> bvalid env (apply_steps fs B ss).
Proof. intros env fs ss. induction ss as [|s t IH]; intros B HF HB; cbn; [exact HB|]. apply IH; [exact HF|]. apply apply_step_ok; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive goal : Set :=
| GLe (a b : expr) | GLt (a b : expr) | GGe (a b : expr) | GGt (a b : expr) | GEq (a b : expr) | GNe (a b : expr)
| GAnd (g h : goal) | GOr (g h : goal).
Fixpoint interp_goal (env : list Z) (g : goal) : Prop :=
  match g with
  | GLe a b => interp env a <= interp env b
  | GLt a b => interp env a < interp env b
  | GGe a b => interp env a >= interp env b
  | GGt a b => interp env a > interp env b
  | GEq a b => interp env a = interp env b
  | GNe a b => interp env a <> interp env b
  | GAnd g h => interp_goal env g /\ interp_goal env h
  | GOr g h => interp_goal env g \/ interp_goal env h
  end.

(* [comment removed for export] *)
Definition use := (nat * bool * Z)%type.
Inductive gcert : Set := CUse (mu : Z) (us : list use) | CUse2 (mu : Z) (us : list use) (nu : Z) (vs : list use) | CAnd (c d : gcert) | CLeft (c : gcert) | CRight (c : gcert).

Fixpoint sub_uses (fs : list fact) (lf : lform) (us : list use) : option lform :=
  match us with
  | [] => Some lf
  | (j, dir, la) :: t =>
      if la <? 0 then None else
      match nth_error fs j with
      | Some f => match fact_lf f dir with
                  | Some lj => sub_uses fs (lf_add lf (lf_scale (- la) lj)) t
                  | None => None
                  end
      | None => None
      end
  end.
Lemma sub_uses_ok : forall env fs us lf lf', interp_facts env fs -> sub_uses fs lf us = Some lf' -> eval_lf env lf <= eval_lf env lf'.
Proof.
  intros env fs us. induction us as [|[[j dir] la] t IH]; intros lf lf' HF E; cbn in E.
  - injection E as <-. lia.
  - destruct (Z.ltb_spec la 0); [discriminate|].
    destruct (nth_error fs j) as [f|] eqn:EN; [|discriminate].
    destruct (fact_lf f dir) as [lj|] eqn:EL; [|discriminate].
    specialize (IH _ _ HF E). rewrite lf_add_ok, lf_scale_ok in IH.
    pose proof (fact_lf_ok env f dir lj (interp_facts_nth env fs j f HF EN) EL). nia.
Qed.

(* [comment removed for export] *)
Definition check_le0 (fs : list fact) (B : bnds) (lf : lform) (mu : Z) (us : list use) : bool :=
  (0 <? mu) &&
  match sub_uses fs (lf_scale mu lf) us with
  | Some lf' => match snd (ival_lf B lf') with Some h => h <=? 0 | None => false end
  | None => false
  end.
Lemma check_le0_ok : forall env fs B lf mu us, interp_facts env fs -> bvalid env B -> check_le0 fs B lf mu us = true -> eval_lf env lf <= 0.
Proof.
  intros env fs B lf mu us HF HB E. unfold check_le0 in E. apply andb_true_iff in E. destruct E as [Emu E].
  apply Z.ltb_lt in Emu.
  destruct (sub_uses fs (lf_scale mu lf) us) as [lf'|] eqn:ES; [|discriminate].
  pose proof (sub_uses_ok env fs us _ lf' HF ES) as H1. rewrite lf_scale_ok in H1.
  pose proof (ival_lf_ok env B lf' HB) as [_ HH].
  destruct (snd (ival_lf B lf')) as [h|]; [|discriminate]. cbn in HH. apply Z.leb_le in E. nia.
Qed.

Fixpoint check_goal (fs : list fact) (B : bnds) (g : goal) (c : gcert) : bool :=
  match g, c with
  | GLe a b, CUse mu us => check_le0 fs B (lin_of (ESub a b)) mu us
  | GLt a b, CUse mu us => check_le0 fs B (lin_of (ESub (EAdd a (EC 1)) b)) mu us
  | GGe a b, CUse mu us => check_le0 fs B (lin_of (ESub b a)) mu us
  | GGt a b, CUse mu us => check_le0 fs B (lin_of (ESub (EAdd b (EC 1)) a)) mu us
  | GEq a b, CUse2 mu us nu vs => check_le0 fs B (lin_of (ESub a b)) mu us && check_le0 fs B (lin_of (ESub b a)) nu vs
  | GNe a b, CLeft (CUse mu us) => check_le0 fs B (lin_of (ESub (EAdd a (EC 1)) b)) mu us
  | GNe a b, CRight (CUse mu us) => check_le0 fs B (lin_of (ESub (EAdd b (EC 1)) a)) mu us
  | GAnd g h, CAnd c d => check_goal fs B g c && check_goal fs B h d
  | GOr g h, CLeft c => check_goal fs B g c
  | GOr g h, CRight d => check_goal fs B h d
  | _, _ => false
  end.
Lemma check_goal_ok : forall env fs B g c, interp_facts env fs -> bvalid env B -> check_goal fs B g c = true -> interp_goal env g.
Proof.
  intros env fs B g. induction g; intros c HF HB E; destruct c; cbn [check_goal] in E; try discriminate.
  - pose proof (check_le0_ok env fs B _ _ _ HF HB E) as H. rewrite lin_of_ok in H. cbn [interp interp_goal] in *. lia.
  - pose proof (check_le0_ok env fs B _ _ _ HF HB E) as H. rewrite lin_of_ok in H. cbn [interp interp_goal] in *. lia.
  - pose proof (check_le0_ok env fs B _ _ _ HF HB E) as H. rewrite lin_of_ok in H. cbn [interp interp_goal] in *. lia.
  - pose proof (check_le0_ok env fs B _ _ _ HF HB E) as H. rewrite lin_of_ok in H. cbn [interp interp_goal] in *. lia.
  - apply andb_true_iff in E. destruct E as [E1 E2].
    pose proof (check_le0_ok env fs B _ _ _ HF HB E1) as H1. pose proof (check_le0_ok env fs B _ _ _ HF HB E2) as H2.
    rewrite lin_of_ok in H1, H2. cbn [interp interp_goal] in *. lia.
  - destruct c; try discriminate.
    pose proof (check_le0_ok env fs B _ _ _ HF HB E) as H. rewrite lin_of_ok in H. cbn [interp interp_goal] in *. lia.
  - destruct c; try discriminate.
    pose proof (check_le0_ok env fs B _ _ _ HF HB E) as H. rewrite lin_of_ok in H. cbn [interp interp_goal] in *. lia.
  - apply andb_true_iff in E. destruct E as [E1 E2]. split; [eapply IHg1| eapply IHg2]; eassumption.
  - left. eapply IHg1; eassumption.
  - right. eapply IHg2; eassumption.
Qed.

Definition rc_check (fs : list fact) (g : goal) (ss : list step) (c : gcert) : bool :=
  check_goal fs (apply_steps fs [] ss) g c.

Theorem rc_sound : forall (env : list Z) (fs : list fact) (g : goal) (ss : list step) (c : gcert),
  interp_facts env fs -> rc_check fs g ss c = true -> interp_goal env g.
Proof.
  intros env fs g ss c HF E. unfold rc_check in E.
  eapply check_goal_ok; [exact HF| |exact E]. apply apply_steps_ok; [exact HF| apply bvalid_nil].
Qed.

(* [comment removed for export] *)
Fixpoint impl_facts (env : list Z) (fs : list fact) (G : Prop) : Prop :=
  match fs with [] => G | f :: t => interp_fact env f -> impl_facts env t G end.
Lemma impl_facts_intro : forall env fs (G : Prop), (interp_facts env fs -> G) -> impl_facts env fs G.
Proof.
  induction fs as [|f t IH]; intros G H; cbn [impl_facts interp_facts] in *; [exact (H Logic.I)|].
  intros Hf. apply IH. intros Ht. apply H. split; assumption.
Qed.
Theorem rc_sound_impl : forall (env : list Z) (fs : list fact) (g : goal) (ss : list step) (c : gcert),
  rc_check fs g ss c = true -> impl_facts env fs (interp_goal env g).
Proof. intros env fs g ss c E. apply impl_facts_intro. intros HF. exact (rc_sound env fs g ss c HF E). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition readings (fs : list fact) : list (nat * bool * lform) :=
  flat_map (fun jf => match fact_lf (snd jf) false, fact_lf (snd jf) true with
                      | Some l0, Some l1 => [(fst jf, false, l0); (fst jf, true, l1)]
                      | Some l0, None => [(fst jf, false, l0)]
                      | None, Some l1 => [(fst jf, true, l1)]
                      | None, None => []
                      end) (combine (seq 0 (length fs)) fs).

Definition better (old new : itv) : bool :=
  (match fst new, fst old with Some n, Some o => o <? n | Some _, None => true | None, _ => false end) ||
  (match snd new, snd old with Some n, Some o => n <? o | Some _, None => true | None, _ => false end).

(* [comment removed for export] *)
Fixpoint prop_positions (B : bnds) (tr : list (step * nat)) (j : nat) (dir : bool) (lf : lform) (p : nat) (n : nat) : bnds * list (step * nat) :=
  match n with
  | O => (B, tr)
  | S n' =>
      match derive B lf p with
      | Some (i, V) =>
          let old := blookup B i in
          if better old V then prop_positions ((i, imeet old V) :: B) ((mkStep j dir p, i) :: tr) j dir lf (S p) n'
          else prop_positions B tr j dir lf (S p) n'
      | None => prop_positions B tr j dir lf (S p) n'
      end
  end.
Fixpoint prop_round (rs : list (nat * bool * lform)) (B : bnds) (tr : list (step * nat)) : bnds * list (step * nat) :=
  match rs with
  | [] => (B, tr)
  | (j, dir, lf) :: t => let (B', tr') := prop_positions B tr j dir lf 0 (length (fst lf)) in prop_round t B' tr'
  end.
(* [comment removed for export] *)
Fixpoint prop_rounds (fuel : nat) (rs : list (nat * bool * lform)) (B : bnds) (tr : list (step * nat)) : bnds * list (step * nat) * bool :=
  match fuel with
  | O => (B, tr, false)
  | S f => let (B', tr') := prop_round rs B tr in
           if Nat.eqb (length tr') (length tr) then (B', tr', true) else prop_rounds f rs B' tr'
  end.

(* [comment removed for export] *)
Fixpoint lcoef (k : expr) (l : lin) : Z :=
  match l with [] => 0 | (k', c) :: t => if expr_eqb k k' then c else lcoef k t end.
Definition hi_le0 (B : bnds) (lf : lform) : bool :=
  match snd (ival_lf B lf) with Some h => h <=? 0 | None => false end.
Definition key_open (B : bnds) (kc : expr * Z) : bool :=
  let (k, c) := kc in
  if 0 <? c then (match snd (ival B k) with None => true | Some _ => false end)
  else if c <? 0 then (match fst (ival B k) with None => true | Some _ => false end)
  else false.
Definition is_atom_key (kc : expr * Z) : bool := match fst kc with EA _ => negb (snd kc =? 0) | _ => false end.
Definition scale_uses (a : Z) (us : list use) : list use := map (fun u => (fst u, a * snd u)) us.
Definition used_in (j : nat) (dir : bool) (us : list use) : bool :=
  existsb (fun u => Nat.eqb (fst (fst u)) j && Bool.eqb (snd (fst u)) dir) us.

Fixpoint fm_try (fm : lform -> Z -> list use -> option (Z * list use)) (rs : list (nat * bool * lform))
                (cur : lform) (mu : Z) (us : list use) (k : expr) (cL : Z) : option (Z * list use) :=
  match rs with
  | [] => None
  | (j, dir, F) :: t =>
      let cF := lcoef k (fst F) in
      if (negb (cF =? 0)) && ((0 <? cF) && (0 <? cL) || (cF <? 0) && (cL <? 0)) && negb (used_in j dir us) then
        let a := Z.abs cF in let b := Z.abs cL in
        match fm (lf_add (lf_scale a cur) (lf_scale (- b) F)) (a * mu) ((j, dir, b) :: scale_uses a us) with
        | Some r => Some r
        | None => fm_try fm t cur mu us k cL
        end
      else fm_try fm t cur mu us k cL
  end.
Fixpoint fm_keys (fm : lform -> Z -> list use -> option (Z * list use)) (rs : list (nat * bool * lform))
                 (cur : lform) (mu : Z) (us : list use) (keys : lin) : option (Z * list use) :=
  match keys with
  | [] => None
  | (k, c) :: t => match fm_try fm rs cur mu us k c with Some r => Some r | None => fm_keys fm rs cur mu us t end
  end.
Definition fm_leaf (B : bnds) (cur : lform) (mu : Z) (us : list use) : option (Z * list use) :=
  if hi_le0 B cur then Some (mu, us) else None.
Fixpoint fm_search (fuel : nat) (B : bnds) (rs : list (nat * bool * lform)) (cur : lform) (mu : Z) (us : list use) {struct fuel} : option (Z * list use) :=
  if hi_le0 B cur then Some (mu, us)
  else match fuel with
       | O => None
       | S f =>
           let opens := filter (key_open B) (fst cur) in
           match opens with
           | _ :: _ => fm_keys (fm_search f B rs) rs cur mu us opens
           | [] => fm_keys (fm_leaf B) rs cur mu us (filter is_atom_key (fst cur))
           end
       end.
Definition solve_le0 (fs : list fact) (B : bnds) (rs : list (nat * bool * lform)) (lf : lform) : option (Z * list use) :=
  match fm_search 3 B rs lf 1 [] with
  | Some (mu, us) => if check_le0 fs B lf mu us then Some (mu, us) else None
  | None => None
  end.
Fixpoint solve_goal (fs : list fact) (B : bnds) (rs : list (nat * bool * lform)) (g : goal) : option gcert :=
  let cu (r : option (Z * list use)) := option_map (fun p => CUse (fst p) (snd p)) r in
  match g with
  | GLe a b => cu (solve_le0 fs B rs (lin_of (ESub a b)))
  | GLt a b => cu (solve_le0 fs B rs (lin_of (ESub (EAdd a (EC 1)) b)))
  | GGe a b => cu (solve_le0 fs B rs (lin_of (ESub b a)))
  | GGt a b => cu (solve_le0 fs B rs (lin_of (ESub (EAdd b (EC 1)) a)))
  | GEq a b => match solve_le0 fs B rs (lin_of (ESub a b)), solve_le0 fs B rs (lin_of (ESub b a)) with
               | Some p, Some q => Some (CUse2 (fst p) (snd p) (fst q) (snd q))
               | _, _ => None
               end
  | GNe a b => match solve_le0 fs B rs (lin_of (ESub (EAdd a (EC 1)) b)) with
               | Some p => Some (CLeft (CUse (fst p) (snd p)))
               | None => option_map (fun p => CRight (CUse (fst p) (snd p))) (solve_le0 fs B rs (lin_of (ESub (EAdd b (EC 1)) a)))
               end
  | GAnd g h => match solve_goal fs B rs g, solve_goal fs B rs h with
                | Some c, Some d => Some (CAnd c d)
                | _, _ => None
                end
  | GOr g h => match solve_goal fs B rs g with
               | Some c => Some (CLeft c)
               | None => option_map CRight (solve_goal fs B rs h)
               end
  end.

(* [comment removed for export] *)
Fixpoint atoms_of (e : expr) (acc : list nat) : list nat :=
  match e with
  | EA i => if existsb (Nat.eqb i) acc then acc else i :: acc
  | EC _ | EPow _ _ => acc
  | EAdd a b | ESub a b | EMul a b | EDiv a b | EMod a b => atoms_of a (atoms_of b acc)
  | EOpp a => atoms_of a acc
  end.
Definition fact_atoms (f : fact) (acc : list nat) : list nat :=
  match f with FLe a b | FLt a b | FEq a b => atoms_of a (atoms_of b acc) end.
Fixpoint goal_atoms (g : goal) (acc : list nat) : list nat :=
  match g with
  | GLe a b | GLt a b | GGe a b | GGt a b | GEq a b | GNe a b => atoms_of a (atoms_of b acc)
  | GAnd g h | GOr g h => goal_atoms g (goal_atoms h acc)
  end.
Definition uses_facts (us : list use) (acc : list nat) : list nat :=
  fold_right (fun u a => if existsb (Nat.eqb (fst (fst u))) a then a else fst (fst u) :: a) acc us.
Fixpoint cert_facts (c : gcert) (acc : list nat) : list nat :=
  match c with
  | CUse _ us => uses_facts us acc
  | CUse2 _ us _ vs => uses_facts (us ++ vs) acc
  | CAnd c d => cert_facts c (cert_facts d acc)
  | CLeft c | CRight c => cert_facts c acc
  end.
(* [comment removed for export] *)
Fixpoint slice (fs : list fact) (tr : list (step * nat)) (needed : list nat) (kept : list step) : list step :=
  match tr with
  | [] => kept
  | (s, i) :: t =>
      if existsb (Nat.eqb i) needed
      then slice fs t (match nth_error fs (s_fact s) with Some f => fact_atoms f needed | None => needed end) (s :: kept)
      else slice fs t needed kept
  end.
(* [comment removed for export] *)
Fixpoint minimise (fuel : nat) (fs : list fact) (g : goal) (c : gcert) (pre post : list step) : list step :=
  match fuel, post with
  | S f, s :: t => if rc_check fs g (pre ++ t) c then minimise f fs g c pre t else minimise f fs g c (pre ++ [s]) t
  | _, _ => pre ++ post
  end.

Fixpoint index_of (x : nat) (l : list nat) (k : nat) : nat :=
  match l with [] => k | y :: t => if Nat.eqb x y then k else index_of x t (S k) end.
Definition re_use (used : list nat) (u : use) : use := (index_of (fst (fst u)) used 0, snd (fst u), snd u).
Fixpoint re_cert (used : list nat) (c : gcert) : gcert :=
  match c with
  | CUse mu us => CUse mu (map (re_use used) us)
  | CUse2 mu us nu vs => CUse2 mu (map (re_use used) us) nu (map (re_use used) vs)
  | CAnd c d => CAnd (re_cert used c) (re_cert used d)
  | CLeft c => CLeft (re_cert used c)
  | CRight c => CRight (re_cert used c)
  end.
Fixpoint insert_sorted (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: t => if Nat.eqb x y then l else if Nat.ltb x y then x :: l else y :: insert_sorted x t
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mask (used : list nat) (n : nat) : list bool := map (fun i => existsb (Nat.eqb i) used) (seq 0 n).

(* [comment removed for export] *)
Record solution : Set := mkSol { so_fmask : list bool; so_amask : list bool; so_steps : list step; so_cert : gcert }.

(* [comment removed for export] *)
Fixpoint refutable (fs : list fact) (B : bnds) (rs : list (nat * bool * lform)) (g : goal) : bool :=
  let yes (lf : lform) := match solve_le0 fs B rs lf with Some _ => true | None => false end in
  match g with
  | GLe a b => yes (lin_of (ESub (EAdd b (EC 1)) a))                 (* [comment removed for export] *)
  | GLt a b => yes (lin_of (ESub b a))                               (* [comment removed for export] *)
  | GGe a b => yes (lin_of (ESub (EAdd a (EC 1)) b))                 (* [comment removed for export] *)
  | GGt a b => yes (lin_of (ESub a b))                               (* [comment removed for export] *)
  | GEq a b => yes (lin_of (ESub (EAdd a (EC 1)) b)) || yes (lin_of (ESub (EAdd b (EC 1)) a))
  | GNe a b => yes (lin_of (ESub a b)) && yes (lin_of (ESub b a))
  | GAnd g h => refutable fs B rs g || refutable fs B rs h
  | GOr g h => refutable fs B rs g && refutable fs B rs h
  end.

(* [comment removed for export] *)
Inductive answer : Set := AYes (s : solution) | ANo (definitely_false : bool) (saturated : bool).

Definition rc_solve (rounds : nat) (fs : list fact) (g : goal) : answer :=
  (* [comment removed for export] *)
  let rs := rev (readings fs) in
  let '(B, tr, sat) := prop_rounds rounds rs [] [] in
  match solve_goal fs B rs g with
  | None => ANo (refutable fs B rs g) sat
  | Some c =>
      let needed := fold_right (fun j acc => match nth_error fs j with Some f => fact_atoms f acc | None => acc end)
                               (goal_atoms g []) (cert_facts c []) in
      let ss0 := slice fs tr needed [] in
      let ss := if Nat.leb (length ss0) 12 then minimise (length ss0) fs g c [] ss0 else ss0 in
      let used := fold_right insert_sorted [] (cert_facts c [] ++ map s_fact ss) in
      let fs1 := map (fun j => nth j fs (FLe (EC 0) (EC 0))) used in
      let ss1 := map (fun s => mkStep (index_of (s_fact s) used 0) (s_dir s) (s_pos s)) ss in
      let c1 := re_cert used c in
      let atoms := fold_right fact_atoms (goal_atoms g []) fs1 in
      if rc_check fs1 g ss1 c1 then
        AYes (mkSol (mask used (length fs)) (mask atoms (S (fold_right Nat.max 0%nat atoms))) ss1 c1)
      else ANo false false
  end.

(* [comment removed for export] *)
Definition itv_empty (V : itv) : bool := match V with (Some l, Some h) => h <? l | _ => false end.
Definition lf_const_pos (lf : lform) : bool := forallb (fun kc => snd kc =? 0) (fst lf) && (0 <? snd lf).
Fixpoint pair_contra (l : lform) (n : nat) (rs : list (nat * bool * lform)) : bool :=
  match rs with
  | [] => false
  | (_, _, l2) :: t => (Nat.eqb (length (fst l2)) n && lf_const_pos (lf_add l l2)) || pair_contra l n t
  end.
Fixpoint pairs_contra (rs : list (nat * bool * lform)) : bool :=
  match rs with
  | [] => false
  | (_, _, l) :: t => lf_const_pos l || pair_contra l (length (fst l)) t || pairs_contra t
  end.
Definition rc_inconsistent (rounds : nat) (fs : list fact) : bool :=
  let rs := rev (readings fs) in
  let '(B, _, _) := prop_rounds rounds rs [] [] in
  existsb (fun iv => itv_empty (snd iv)) B
  || existsb (fun r => lf_const_pos (snd r)) rs
  || pairs_contra (filter (fun r => match fst (snd r) with _ :: _ :: _ => true | _ => false end) rs).   (* [comment removed for export] *)

(* [comment removed for export] *)

End RC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module RF.
Import Ltac2.

Ltac2 mutable rc_debug : bool := false.
Ltac2 mutable rc_why : bool := false.      (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 mutable rc_atom_facts : constr -> (constr * constr) list := fun _ => [].
(* [comment removed for export] *)
Ltac2 mutable rc_boxes : unit -> constr list := fun () => [].
(* [comment removed for export] *)
Ltac2 mutable rc_skip_hyps : unit -> ident list := fun () => [].
Ltac2 mutable rc_rounds : int := 24.
Ltac2 mutable rc_consist_rounds : int := 2.   (* [comment removed for export] *)
Ltac2 mutable rc_max_consist : int := 400.   (* [comment removed for export] *)
Ltac2 mutable rc_max_facts : int := 32.
Ltac2 mutable rc_depth : int := 6.
Ltac2 mutable rc_phase : int := 9.   (* [comment removed for export] *)

Ltac2 Type rctx := {
  hmap : (constant, int) FMap.t; imap : (inductive, int) FMap.t; tmap : (inductive, int) FMap.t;
  h_z : constr; h_o : constr; h_s : constr; h_xh : constr; h_xo : constr; h_xi : constr; h_z0 : constr; h_zpos : constr;
  h_eq : constr; h_true : constr;
  c_EA : constr; c_EC : constr; c_EPow : constr; c_EAdd : constr; c_ESub : constr; c_EOpp : constr;
  c_EMul : constr; c_EDiv : constr; c_EMod : constr;
  c_FLe : constr; c_FLt : constr; c_FEq : constr;
  c_GLe : constr; c_GLt : constr; c_GGe : constr; c_GGt : constr; c_GEq : constr; c_GNe : constr; c_GAnd : constr; c_GOr : constr;
  c_zle : constr; c_zlt : constr;
  c_proj1 : constr; c_proj2 : constr; c_ge_le : constr; c_gt_lt : constr; c_eq_refl : constr; c_nil : constr; c_cons : constr }.

Ltac2 gref (r : Std.reference) : constr := Env.instantiate r.
Ltac2 hadd (r : Std.reference) (k : int) (m : (constant, int) FMap.t) : (constant, int) FMap.t :=
  match r with Std.ConstRef c => FMap.add c k m | _ => m end.
Ltac2 iadd (r : Std.reference) (k : int) (m : (inductive, int) FMap.t) : (inductive, int) FMap.t :=
  match r with Std.IndRef c => FMap.add c k m | _ => m end.
(* [comment removed for export] *)
Ltac2 hadds (rs : Std.reference list) (k : int) (m : (constant, int) FMap.t) : (constant, int) FMap.t :=
  List.fold_left (fun m r => match r with Std.ConstRef c => FMap.add c k m | _ => m end) m rs.
Ltac2 mk_rctx () : rctx := {
  hmap := hadd reference:(Z.add) 1 (hadd reference:(Z.sub) 2 (hadd reference:(Z.mul) 3 (hadd reference:(Z.div) 4
          (hadd reference:(Z.modulo) 5 (hadd reference:(Z.pow) 6 (hadd reference:(Z.opp) 7 (hadd reference:(Z.of_nat) 8
          (hadd reference:(Z.le) 10 (hadd reference:(Z.lt) 11 (hadd reference:(Z.ge) 12 (hadd reference:(Z.gt) 13
          (hadd reference:(not) 14
          (hadds [reference:(iff); reference:(Z.divide); reference:(lt); reference:(ge); reference:(gt);
                  reference:(N.le); reference:(N.lt); reference:(N.ge); reference:(N.gt);
                  reference:(Pos.le); reference:(Pos.lt); reference:(Pos.ge); reference:(Pos.gt); reference:(is_true)] 30
          (hadds [reference:(Z.min); reference:(Z.max); reference:(Z.abs); reference:(Z.sgn); reference:(Z.rem); reference:(Z.quot);
                  reference:(Z.succ); reference:(Z.pred); reference:(Z.b2z); reference:(Z.of_N); reference:(Z.double);
                  reference:(Z.succ_double); reference:(Z.pred_double); reference:(Z.square); reference:(Z.div2); reference:(Z.quot2);
                  reference:(Z.pow_pos); reference:(Z.to_nat); reference:(Z.abs_nat); reference:(N.to_nat); reference:(Pos.to_nat);
                  reference:(Nat.add); reference:(Nat.sub); reference:(Nat.mul); reference:(Nat.div); reference:(Nat.modulo);
                  reference:(Nat.pred); reference:(Nat.min); reference:(Nat.max); reference:(Nat.div2); reference:(Nat.double)] 40
          (FMap.empty FSet.Tags.constant_tag)))))))))))))));
  imap := iadd reference:(and) 20 (iadd reference:(or) 21 (iadd reference:(eq) 22 (iadd reference:(le) 31 (FMap.empty FSet.Tags.inductive_tag))));
  tmap := iadd reference:(nat) 1 (iadd reference:(N) 1 (iadd reference:(positive) 1 (iadd reference:(bool) 1 (FMap.empty FSet.Tags.inductive_tag))));
  h_z := gref reference:(Z); h_o := gref reference:(O); h_s := gref reference:(S);
  h_xh := gref reference:(xH); h_xo := gref reference:(xO); h_xi := gref reference:(xI);
  h_z0 := gref reference:(Z0); h_zpos := gref reference:(Zpos); h_eq := gref reference:(eq); h_true := gref reference:(true);
  c_EA := gref reference:(RC.EA); c_EC := gref reference:(RC.EC); c_EPow := gref reference:(RC.EPow);
  c_EAdd := gref reference:(RC.EAdd); c_ESub := gref reference:(RC.ESub); c_EOpp := gref reference:(RC.EOpp);
  c_EMul := gref reference:(RC.EMul); c_EDiv := gref reference:(RC.EDiv); c_EMod := gref reference:(RC.EMod);
  c_FLe := gref reference:(RC.FLe); c_FLt := gref reference:(RC.FLt); c_FEq := gref reference:(RC.FEq);
  c_GLe := gref reference:(RC.GLe); c_GLt := gref reference:(RC.GLt); c_GGe := gref reference:(RC.GGe);
  c_GGt := gref reference:(RC.GGt); c_GEq := gref reference:(RC.GEq); c_GNe := gref reference:(RC.GNe);
  c_GAnd := gref reference:(RC.GAnd); c_GOr := gref reference:(RC.GOr);
  c_zle := gref reference:(Z.le); c_zlt := gref reference:(Z.lt);
  c_proj1 := gref reference:(proj1); c_proj2 := gref reference:(proj2); c_ge_le := gref reference:(Z.ge_le);
  c_gt_lt := gref reference:(Z.gt_lt); c_eq_refl := gref reference:(eq_refl); c_nil := gref reference:(nil);
  c_cons := gref reference:(cons) }.

Ltac2 mk_app (f : constr) (a : constr array) : constr := Constr.Unsafe.make (Constr.Unsafe.App f a).
Ltac2 fail_rc (s : string) := Control.zero (Tactic_failure (Some (Message.of_string s))).
Ltac2 dbg (l : message list) : unit := Message.print (List.fold_right Message.concat l (Message.of_string "")).

(* [comment removed for export] *)
Ltac2 head_code (x : rctx) (f : constr) : int :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Constant c _ => match FMap.find_opt c (x.(hmap)) with Some k => k | None => 0 end
  | Constr.Unsafe.Ind i _ => match FMap.find_opt i (x.(imap)) with Some k => k | None => 0 end
  | Constr.Unsafe.Constructor _ _ => 9
  | _ => 0
  end.

(* [comment removed for export] *)
Ltac2 num_sign (x : rctx) (a : constr) : int :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App g _ =>
      match Constr.Unsafe.kind g with
      | Constr.Unsafe.Constructor _ _ => if Constr.equal g (x.(h_zpos)) then 1 else -1
      | _ => 2
      end
  | Constr.Unsafe.Constructor _ _ => 0
  | _ => 2
  end.
Ltac2 is_num (a : constr) : bool :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App g _ => match Constr.Unsafe.kind g with Constr.Unsafe.Constructor _ _ => true | _ => false end
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 is_cst (x : rctx) (a : constr) : bool :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App g args =>
      match Constr.Unsafe.kind g with
      | Constr.Unsafe.Constructor _ _ => true
      | Constr.Unsafe.Constant c _ =>
          (match FMap.find_opt c (x.(hmap)) with
           | Some 6 => if is_num (Array.get args 0) then is_num (Array.get args 1) else false
           | _ => false
           end)
      | _ => false
      end
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec nat_lit (x : rctx) (c : constr) (k : int) (acc : int) : int :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Constr.equal f (x.(h_s)) then (if Int.le k 0 then -1 else nat_lit x (Array.get args 0) (Int.sub k 1) (Int.add acc 1)) else -1
  | Constr.Unsafe.Constructor _ _ => if Constr.equal c (x.(h_o)) then acc else -1
  | _ => -1
  end.
Ltac2 rec pos_of_int (x : rctx) (n : int) : constr :=
  if Int.le n 1 then x.(h_xh)
  else if Int.equal (Int.mod n 2) 0 then mk_app (x.(h_xo)) [| pos_of_int x (Int.div n 2) |]
  else mk_app (x.(h_xi)) [| pos_of_int x (Int.div n 2) |].
Ltac2 z_of_int (x : rctx) (n : int) : constr :=
  if Int.equal n 0 then x.(h_z0) else mk_app (x.(h_zpos)) [| pos_of_int x n |].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 neg (s : int) : int := match s with 1 => -1 | -1 => 1 | _ => s end.
Ltac2 smul (s : int) (k : int) : int := match s with 5 => 5 | 0 => 0 | _ => match k with 1 => s | -1 => neg s | _ => 0 end end.
(* [comment removed for export] *)
Ltac2 mor (a : int) (b : int) : int :=
  match a with
  | 0 => b
  | 3 => 3
  | 1 => (match b with 0 => 1 | 1 => 1 | _ => 3 end)
  | _ => (match b with 0 => 2 | 2 => 2 | _ => 3 end)
  end.
Ltac2 mand (a : int) (b : int) : int :=
  match a with
  | 0 => 0
  | 3 => b
  | 1 => (match b with 1 => 1 | 3 => 1 | _ => 0 end)
  | _ => (match b with 2 => 2 | 3 => 2 | _ => 0 end)
  end.
Ltac2 meq (a : int) (b : int) : bool :=
  match a with
  | 0 => (match b with 0 => true | _ => false end)
  | 1 => (match b with 1 => true | _ => false end)
  | 2 => (match b with 2 => true | _ => false end)
  | _ => (match b with 3 => true | _ => false end)
  end.
Ltac2 rec leaves (x : rctx) (c : constr) (s : int) (acc : (constr * int) list) : (constr * int) list :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      match head_code x f with
      | 1 => leaves x (Array.get args 0) s (leaves x (Array.get args 1) s acc)
      | 2 => leaves x (Array.get args 0) s (leaves x (Array.get args 1) (neg s) acc)
      | 3 => let a := Array.get args 0 in let b := Array.get args 1 in
             let sb := num_sign x b in
             if Int.lt sb 2 then leaves x a (smul s sb) acc
             else (let sa := num_sign x a in
                   if Int.lt sa 2 then leaves x b (smul s sa) acc
                   else if is_cst x b then leaves x a 0 acc else if is_cst x a then leaves x b 0 acc else (c, s) :: acc)
      | 4 => if is_cst x (Array.get args 1) then leaves x (Array.get args 0) 5 acc else (c, s) :: acc
      | 5 => if is_cst x (Array.get args 1) then leaves x (Array.get args 0) 5 acc else (c, s) :: acc
      | 6 => if (if is_num (Array.get args 0) then is_num (Array.get args 1) else false) then acc else (c, s) :: acc
      | 7 => leaves x (Array.get args 0) (neg s) acc
      | 8 => if Int.le 0 (nat_lit x (Array.get args 0) 4096 0) then acc else (c, s) :: acc
      | 9 => acc
      | _ => (c, s) :: acc
      end
  | Constr.Unsafe.Constructor _ _ => acc
  | _ => (c, s) :: acc
  end.

(* [comment removed for export] *)
Ltac2 rec vars_of (c : constr) (acc : ident list) : ident list :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id => if List.exist (Ident.equal id) acc then acc else id :: acc
  | Constr.Unsafe.App f args => Array.fold_left (fun a y => vars_of y a) (vars_of f acc) args
  | Constr.Unsafe.Cast y _ _ => vars_of y acc
  | Constr.Unsafe.Proj _ _ y => vars_of y acc
  | _ => acc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 Type cand := { cd_root : constr; cd_rty : constr; cd_path : bool list; cd_rel : int; cd_flip : bool;
                     cd_l : constr; cd_r : constr; cd_leaves : (constr * int) list; mutable cd_sel : bool; mutable cd_done : bool }.
Ltac2 mk_cand (x : rctx) (root : constr) (rty : constr) (path : bool list) (rel : int) (flip : bool) (l : constr) (r : constr) : cand :=
  { cd_root := root; cd_rty := rty; cd_path := path; cd_rel := rel; cd_flip := flip; cd_l := l; cd_r := r;
    cd_leaves := leaves x l 1 (leaves x r -1 []); cd_sel := false; cd_done := false }.

(* [comment removed for export] *)
Ltac2 is_blocker (x : rctx) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App f args =>
      (match head_code x f with
       | 14 => true | 21 => true | 30 => true | 31 => true
       | 22 => (match Constr.Unsafe.kind (Array.get args 0) with
                | Constr.Unsafe.Ind i _ => (match FMap.find_opt i (x.(tmap)) with Some _ => true | None => false end)
                | _ => false
                end)
       | _ => false
       end)
  | Constr.Unsafe.Prod b _ =>
      (match Constr.Unsafe.kind (Constr.Binder.type b) with
       | Constr.Unsafe.App f _ => (match head_code x f with 0 => false | 9 => false | _ => true end)
       | _ => false
       end)
  | _ => false
  end.

Ltac2 rec scan_prop (x : rctx) (blk : constr list Ref.ref) (root : constr) (rty : constr) (path : bool list) (ty : constr) (acc : cand list) : cand list :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App f args =>
      match head_code x f with
      | 10 => mk_cand x root rty path 0 false (Array.get args 0) (Array.get args 1) :: acc
      | 11 => mk_cand x root rty path 1 false (Array.get args 0) (Array.get args 1) :: acc
      | 20 => scan_prop x blk root rty (false :: path) (Array.get args 0) (scan_prop x blk root rty (true :: path) (Array.get args 1) acc)
      | 12 => mk_cand x root rty path 0 true (Array.get args 1) (Array.get args 0) :: acc
      | 13 => mk_cand x root rty path 1 true (Array.get args 1) (Array.get args 0) :: acc
      | 22 => if Constr.equal (Array.get args 0) (x.(h_z)) then mk_cand x root rty path 2 false (Array.get args 1) (Array.get args 2) :: acc
              else ((if is_blocker x ty then Ref.set blk (ty :: Ref.get blk) else ()); acc)
      | 0 => acc
      | _ => (if is_blocker x ty then Ref.set blk (ty :: Ref.get blk) else ()); acc
      end
  | Constr.Unsafe.Prod _ _ => (if is_blocker x ty then Ref.set blk (ty :: Ref.get blk) else ()); acc
  | _ => acc
  end.

(* [comment removed for export] *)
Ltac2 rec proj_along (x : rctx) (pf : constr) (ty : constr) (rpath : bool list) : constr :=
  match rpath with
  | [] => pf
  | isr :: rest =>
      match Constr.Unsafe.kind ty with
      | Constr.Unsafe.App _ args =>
          let a := Array.get args 0 in let b := Array.get args 1 in
          if isr then proj_along x (mk_app (x.(c_proj2)) [| a; b; pf |]) b rest
          else proj_along x (mk_app (x.(c_proj1)) [| a; b; pf |]) a rest
      | _ => fail_rc "rc_lia: proj"
      end
  end.
Ltac2 cand_proof (x : rctx) (c : cand) : constr :=
  let pf := proj_along x (c.(cd_root)) (c.(cd_rty)) (List.rev (c.(cd_path))) in
  if c.(cd_flip) then
    (* [comment removed for export] *)
    mk_app (if Int.equal (c.(cd_rel)) 0 then x.(c_ge_le) else x.(c_gt_lt)) [| c.(cd_r); c.(cd_l); pf |]
  else pf.

(* [comment removed for export] *)
Ltac2 Type ahyp := { ah_id : ident; ah_ty : constr }.
Ltac2 Type scanned := { sc_hyps : ahyp list; sc_defs : (ident * constr) list; sc_blk : constr list; sc_ors : ahyp list;
                        sc_negs : ahyp list; sc_nats : ahyp list }.
Ltac2 scan_hyps (x : rctx) (boxes : constr list) : scanned :=
  let hs := Ref.ref [] in
  let ds := Ref.ref [] in
  let bs := Ref.ref [] in
  let ors := Ref.ref [] in
  let negs := Ref.ref [] in
  let nats := Ref.ref [] in
  let skips := rc_skip_hyps () in
  List.iter (fun hd =>
    let (id, body, ty0) := hd in
    let ty := match boxes with
              | [] => ty0
              | _ :: _ =>
                  (match Constr.Unsafe.kind ty0 with
                   | Constr.Unsafe.App f args =>
                       if List.exist (Constr.equal f) boxes then Array.get args (Int.sub (Array.length args) 1) else ty0
                   | _ => ty0
                   end)
              end in
    match body with
    | Some b => if Constr.equal ty (x.(h_z)) then Ref.set ds ((id, b) :: Ref.get ds) else ()
    | None =>
        if (match skips with [] => false | _ :: _ => List.exist (Ident.equal id) skips end) then
          (match Constr.Unsafe.kind ty with
           | Constr.Unsafe.App f _ => (match head_code x f with 0 => () | 9 => () | _ => Ref.set bs (ty :: Ref.get bs) end)
           | _ => ()
           end)
        else
        match Constr.Unsafe.kind ty with
        | Constr.Unsafe.App f args =>
            (match head_code x f with
             | 0 => () | 9 => ()
             | 10 => Ref.set hs ({ ah_id := id; ah_ty := ty } :: Ref.get hs)
             | 11 => Ref.set hs ({ ah_id := id; ah_ty := ty } :: Ref.get hs)
             | 12 => Ref.set hs ({ ah_id := id; ah_ty := ty } :: Ref.get hs)
             | 13 => Ref.set hs ({ ah_id := id; ah_ty := ty } :: Ref.get hs)
             | 20 => Ref.set hs ({ ah_id := id; ah_ty := ty } :: Ref.get hs)
             | 22 => if Constr.equal (Array.get args 0) (x.(h_z)) then Ref.set hs ({ ah_id := id; ah_ty := ty } :: Ref.get hs)
                     else if is_blocker x ty then (Ref.set bs (ty :: Ref.get bs); Ref.set nats ({ ah_id := id; ah_ty := ty } :: Ref.get nats)) else ()
             | 21 => Ref.set bs (ty :: Ref.get bs); Ref.set ors ({ ah_id := id; ah_ty := ty } :: Ref.get ors)
             | 14 => Ref.set bs (ty :: Ref.get bs); Ref.set negs ({ ah_id := id; ah_ty := ty } :: Ref.get negs)
             | 30 => Ref.set bs (ty :: Ref.get bs); Ref.set nats ({ ah_id := id; ah_ty := ty } :: Ref.get nats)
             | 31 => Ref.set bs (ty :: Ref.get bs); Ref.set nats ({ ah_id := id; ah_ty := ty } :: Ref.get nats)
             | _ => if is_blocker x ty then Ref.set bs (ty :: Ref.get bs) else ()
             end)
        | Constr.Unsafe.Prod _ _ => if is_blocker x ty then Ref.set bs (ty :: Ref.get bs) else ()
        | _ => ()
        end
    end) (Control.hyps ());
  { sc_hyps := Ref.get hs; sc_defs := Ref.get ds; sc_blk := Ref.get bs; sc_ors := Ref.get ors; sc_negs := Ref.get negs; sc_nats := Ref.get nats }.

Ltac2 mentions_vars (vs : ident list) (c : constr) : bool :=
  if Constr.Unsafe.closedn 0 (Constr.Unsafe.closenl vs 1 c) then false else true.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 Type needs := { mutable nd_vars : (ident, int) FMap.t; mutable nd_other : (constr * int) list;
                      mutable nd_new : constr list; mutable nd_work : constr list }.
Ltac2 rec other_get (l : (constr * int) list) (a : constr) : int :=
  match l with [] => 0 | p :: r => let (b, m) := p in if Constr.equal a b then m else other_get r a end.
Ltac2 rec other_set (l : (constr * int) list) (a : constr) (m : int) : (constr * int) list :=
  match l with
  | [] => [(a, m)]
  | p :: r => let (b, _) := p in if Constr.equal a b then (b, m) :: r else p :: other_set r a m
  end.
Ltac2 need_get (nd : needs) (a : constr) : int :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.Var id => match FMap.find_opt id (nd.(nd_vars)) with Some m => m | None => 0 end
  | _ => other_get (nd.(nd_other)) a
  end.
Ltac2 need_add (nd : needs) (a : constr) (m : int) : unit :=
  let old := need_get nd a in
  let new := mor old m in
  if meq new old then () else
  ((match old with 0 => nd.(nd_new) := a :: nd.(nd_new) | _ => () end);
   nd.(nd_work) := a :: nd.(nd_work);
   (match Constr.Unsafe.kind a with
    | Constr.Unsafe.Var id => nd.(nd_vars) := FMap.add id new (nd.(nd_vars))
    | _ => nd.(nd_other) := other_set (nd.(nd_other)) a new
    end)).

(* [comment removed for export] *)
Ltac2 trig (rel : int) (s : int) (m : int) : int :=
  match m with
  | 0 => 0
  | _ =>
      let o := match s with
               | 1 => (match m with 1 => 2 | 2 => 1 | _ => 3 end)      (* [comment removed for export] *)
               | -1 => (match m with 1 => 1 | 2 => 2 | _ => 3 end)
               | 0 => 3
               | _ => 0
               end in
      match rel with 2 => o | _ => mand o 1 end
  end.
(* [comment removed for export] *)
Ltac2 wants (om : int) (s : int) : int :=
  match s with
  | 1 => (match om with 1 => 1 | 2 => 2 | _ => 3 end)
  | -1 => (match om with 1 => 2 | 2 => 1 | _ => 3 end)
  | _ => 3
  end.

(* [comment removed for export] *)
Ltac2 rec goal_needs (x : rctx) (nd : needs) (g : constr) : unit :=
  let cmp (a : constr) (b : constr) (both : bool) :=
    List.iter (fun p => let (l, s) := p in
                 need_add nd l (if both then 3 else match s with 1 => 2 | -1 => 1 | _ => 3 end))
              (leaves x a 1 (leaves x b -1 [])) in
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.App f args =>
      match head_code x f with
      | 20 => goal_needs x nd (Array.get args 0); goal_needs x nd (Array.get args 1)
      | 21 => goal_needs x nd (Array.get args 0); goal_needs x nd (Array.get args 1)
      | 10 => cmp (Array.get args 0) (Array.get args 1) false
      | 11 => cmp (Array.get args 0) (Array.get args 1) false
      | 12 => cmp (Array.get args 1) (Array.get args 0) false
      | 13 => cmp (Array.get args 1) (Array.get args 0) false
      | 22 => if Constr.equal (Array.get args 0) (x.(h_z)) then cmp (Array.get args 1) (Array.get args 2) true else fail_rc "rc_lia: goal shape"
      | 14 => (match Constr.Unsafe.kind (Array.get args 0) with
               | Constr.Unsafe.App f2 args2 =>
                   if (match head_code x f2 with 22 => Constr.equal (Array.get args2 0) (x.(h_z)) | _ => false end)
                   then cmp (Array.get args2 1) (Array.get args2 2) true else fail_rc "rc_lia: goal shape"
               | _ => fail_rc "rc_lia: goal shape"
               end)
      | _ => fail_rc "rc_lia: goal shape"
      end
  | _ => fail_rc "rc_lia: goal shape"
  end.

(* [comment removed for export] *)
Ltac2 atom_facts (x : rctx) (blk : constr list Ref.ref) (a : constr) (acc : cand list) : cand list :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App f args =>
      let acc :=
        match head_code x f with
        | 8 => (let pf := mk_app (gref reference:(Nat2Z.is_nonneg)) [| Array.get args 0 |] in
                mk_cand x pf (x.(h_true)) [] 0 false (x.(h_z0)) a :: acc)
        | _ => acc
        end in
      List.fold_left (fun ac p => let (pf, ty) := p in scan_prop x blk pf ty [] ty ac) acc (rc_atom_facts a)
  | _ => acc
  end.

(* [comment removed for export] *)
Ltac2 Type selection := { se_facts : cand list; se_vars : ident list; se_blk : constr list; se_others : constr list; se_open : bool;
                          se_pool : cand list; se_pend : ahyp list }.
Ltac2 rec has_var_leaf (l : (constr * int) list) : bool :=
  match l with
  | [] => false
  | p :: r => let (a, _) := p in match Constr.Unsafe.kind a with Constr.Unsafe.Var _ => true | _ => has_var_leaf r end
  end.

(* [comment removed for export] *)
Ltac2 def_usable (x : rctx) (b : constr) : bool :=
  match leaves x b 1 [] with
  | [] => false
  | ls =>
      if List.for_all (fun p => let (a, _) := p in match vars_of a [] with [] => false | _ :: _ => true end) ls then
        (match ls with
         | [p] => let (a, _) := p in if Constr.equal a b then false else true
         | _ => true
         end)
      else false
  end.

Ltac2 select_n (maxf : int) (x : rctx) (nd : needs) (sc : scanned) : selection :=
  let sel := Ref.ref [] in
  let nsel := Ref.ref 0 in
  let pend_h := Ref.ref (sc.(sc_hyps)) in
  let pend_d := Ref.ref (sc.(sc_defs)) in
  let blk := Ref.ref (sc.(sc_blk)) in
  let warm := Ref.ref [] in
  let cold := Ref.ref [] in
  let npool := Ref.ref 0 in
  let allvars := Ref.ref [] in
  let novar := Ref.ref false in
  (* [comment removed for export] *)
  let opn := Ref.ref false in
  let examine (c : cand) : unit :=
    if c.(cd_done) then () else
    let rel := c.(cd_rel) in
    let ntrig := Ref.ref 0 in
    let om := List.fold_left (fun o p => let (l, s) := p in
                match s with
                | 5 => (match need_get nd l with 0 => () | _ => Ref.set opn true end); o
                | _ =>
                    match trig rel s (need_get nd l) with
                    | 0 => o
                    | t => (Ref.set ntrig (match Ref.get ntrig with 0 => 1 | _ => 2 end); mor o t)
                    end
                end) 0 (c.(cd_leaves)) in
    match om with
    | 0 => ()
    | _ =>
        if (if c.(cd_sel) then false else Int.le maxf (Ref.get nsel)) then Ref.set opn true
        else
          ((if c.(cd_sel) then () else
              ((if rc_debug then dbg [Message.of_string "RC-DEBUG sel: "; Message.of_constr (c.(cd_l)); Message.of_string " ["; Message.of_int rel;
                                      Message.of_string "] "; Message.of_constr (c.(cd_r)); Message.of_string "  orient="; Message.of_int om] else ());
               c.(cd_sel) := true; Ref.set sel (c :: Ref.get sel); Ref.set nsel (Int.add (Ref.get nsel) 1)));
           (match Ref.get ntrig with 2 => (match rel with 2 => (match om with 3 => c.(cd_done) := true | _ => () end) | _ => c.(cd_done) := true end) | _ => () end);
           let single := match Ref.get ntrig with 1 => true | _ => false end in
           List.iter (fun p => let (l, s) := p in
             if (if single then (match trig rel s (need_get nd l) with 0 => true | _ => false end) else true)
             then need_add nd l (wants om s) else ()) (c.(cd_leaves)))
    end in
  let add_cands (cs : cand list) : unit :=
    List.iter (fun c => Ref.set npool (Int.add (Ref.get npool) 1);
                        (if has_var_leaf (c.(cd_leaves)) then Ref.set warm (c :: Ref.get warm) else Ref.set cold (c :: Ref.get cold));
                        examine c) cs in
  let rec loop (fuel : int) : unit :=
    if Int.le fuel 0 then Ref.set opn true else
    match nd.(nd_new) with
    | _ :: _ =>
        (* [comment removed for export] *)
        let na := nd.(nd_new) in
        nd.(nd_new) := [];
        let newvars := Ref.ref [] in
        List.iter (fun a =>
          add_cands (atom_facts x blk a []);
          (match Constr.Unsafe.kind a with
           | Constr.Unsafe.Var _ => ()
           | _ => List.iter (fun c => if List.exist (fun p => let (l, _) := p in Constr.equal l a) (c.(cd_leaves)) then examine c else ()) (Ref.get cold)
           end);
          (match vars_of a [] with
           | [] => Ref.set novar true      (* [comment removed for export] *)
           | vs => List.iter (fun v => if List.exist (Ident.equal v) (Ref.get allvars) then ()
                                       else (Ref.set allvars (v :: Ref.get allvars); Ref.set newvars (v :: Ref.get newvars))) vs
           end)) na;
        let nv := Ref.get newvars in
        (if Ref.get novar then
           (* [comment removed for export] *)
           (List.iter (fun hy => add_cands (scan_prop x blk (Constr.Unsafe.make (Constr.Unsafe.Var (hy.(ah_id)))) (hy.(ah_ty)) [] (hy.(ah_ty)) [])) (Ref.get pend_h);
            Ref.set pend_h [];
            List.iter (fun d => let (id, b) := d in
                         let v := Constr.Unsafe.make (Constr.Unsafe.Var id) in
                         if def_usable x b then add_cands [mk_cand x (mk_app (x.(c_eq_refl)) [| x.(h_z); v |]) (x.(h_true)) [] 2 false v b]
                         else ()) (Ref.get pend_d);
            Ref.set pend_d []; Ref.set novar false)
         else ());
        (match nv with
         | [] => ()
         | _ :: _ =>
             Ref.set pend_h (List.filter (fun hy =>
               if mentions_vars nv (hy.(ah_ty)) then
                 (add_cands (scan_prop x blk (Constr.Unsafe.make (Constr.Unsafe.Var (hy.(ah_id)))) (hy.(ah_ty)) [] (hy.(ah_ty)) []); false)
               else true) (Ref.get pend_h));
             Ref.set pend_d (List.filter (fun d =>
               let (id, b) := d in
               if (if List.exist (Ident.equal id) nv then true else mentions_vars nv b) then
                 (let v := Constr.Unsafe.make (Constr.Unsafe.Var id) in
                  (if def_usable x b then add_cands [mk_cand x (mk_app (x.(c_eq_refl)) [| x.(h_z); v |]) (x.(h_true)) [] 2 false v b] else ());
                  false)
               else true) (Ref.get pend_d))
         end);
        loop (Int.sub fuel 1)
    | [] =>
        match nd.(nd_work) with
        | [] => ()
        | _ :: _ =>
            (* [comment removed for export] *)
            nd.(nd_work) := [];
            List.iter examine (Ref.get warm);
            loop (Int.sub fuel 1)
        end
    end
  in
  loop 40;
  (if rc_debug then
     dbg [Message.of_string "RC-DEBUG select: hyps="; Message.of_int (List.length (sc.(sc_hyps)));
          Message.of_string " unparsed="; Message.of_int (List.length (Ref.get pend_h));
          Message.of_string " pool="; Message.of_int (Ref.get npool);
          Message.of_string " warm="; Message.of_int (List.length (Ref.get warm));
          Message.of_string " sel="; Message.of_int (Ref.get nsel);
          Message.of_string " vars="; Message.of_int (List.length (Ref.get allvars));
          Message.of_string " blockers="; Message.of_int (List.length (Ref.get blk))]
   else ());
  { se_facts := List.rev (Ref.get sel); se_vars := Ref.get allvars; se_blk := Ref.get blk;
    se_others := List.map (fun p => let (a, _) := p in a) (nd.(nd_other)); se_open := Ref.get opn;
    se_pool := List.append (Ref.get warm) (Ref.get cold); se_pend := Ref.get pend_h }.
Ltac2 select (x : rctx) (nd : needs) (sc : scanned) : selection := select_n (rc_max_facts) x nd sc.

(* [comment removed for export] *)
Ltac2 zify_opaque (x : rctx) (a : constr) : bool :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App f args =>
      (match head_code x f with
       | 0 => true
       | 8 => (* [comment removed for export] *)
              (match Constr.Unsafe.kind (Array.get args 0) with
               | Constr.Unsafe.Var _ => true
               | Constr.Unsafe.App g _ => (match head_code x g with 0 => true | _ => false end)
               | _ => false
               end)
       | _ => false
       end)
  | Constr.Unsafe.Var _ => true
  | Constr.Unsafe.Constant _ _ => true
  | _ => false
  end.
Ltac2 may_refute (x : rctx) (se : selection) : bool :=
  if se.(se_open) then ((if rc_why then dbg [Message.of_string "RC-WHY open"] else ()); false)
  else if List.for_all (zify_opaque x) (se.(se_others)) then
    (match se.(se_vars) with
     | [] => true
     | _ :: _ =>
         (match List.find_opt (mentions_vars (se.(se_vars))) (se.(se_blk)) with
          | Some b => (if rc_why then dbg [Message.of_string "RC-WHY blocker: "; Message.of_constr b] else ()); false
          | None => true
          end)
     end)
  else ((if rc_why then
           dbg [Message.of_string "RC-WHY non-opaque atom: ";
                Message.of_constr (List.find (fun a => if zify_opaque x a then false else true) (se.(se_others)))] else ()); false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 Type tbl := { mutable t_vars : (ident, constr * constr) FMap.t; mutable t_other : (constr * (constr * constr)) list;
                    mutable t_n : int; mutable t_nat : constr; mutable t_atoms : constr list; mutable t_divmod : bool;
                    mutable t_ids : ident list; mutable t_avoid : Fresh.Free.t }.
Ltac2 rec other_find (l : (constr * (constr * constr)) list) (c : constr) : (constr * constr) option :=
  match l with
  | [] => None
  | p :: r => let (a, v) := p in if Constr.equal a c then Some v else other_find r c
  end.
Ltac2 new_atom (x : rctx) (t : tbl) (c : constr) : constr * constr :=
  let ea := mk_app (x.(c_EA)) [| t.(t_nat) |] in
  let id := Fresh.fresh (t.(t_avoid)) @rcx in
  t.(t_avoid) := Fresh.Free.union (t.(t_avoid)) (Fresh.Free.of_ids [id]);
  t.(t_ids) := id :: t.(t_ids);
  t.(t_nat) := mk_app (x.(h_s)) [| t.(t_nat) |];
  t.(t_n) := Int.add (t.(t_n)) 1;
  t.(t_atoms) := c :: t.(t_atoms);
  (ea, Constr.Unsafe.make (Constr.Unsafe.Var id)).
(* [comment removed for export] *)
Ltac2 atom (x : rctx) (t : tbl) (ab : bool) (c : constr) : constr :=
  let pick (v : constr * constr) : constr := let (ea, ph) := v in if ab then ph else ea in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id =>
      match FMap.find_opt id (t.(t_vars)) with
      | Some v => pick v
      | None => let v := new_atom x t c in t.(t_vars) := FMap.add id v (t.(t_vars)); pick v
      end
  | _ =>
      match other_find (t.(t_other)) c with
      | Some v => pick v
      | None => let v := new_atom x t c in t.(t_other) := (c, v) :: t.(t_other); pick v
      end
  end.

(* [comment removed for export] *)
Ltac2 rec reify (x : rctx) (t : tbl) (ab : bool) (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      let bin (k : constr) := if ab then mk_app f [| reify x t ab (Array.get args 0); reify x t ab (Array.get args 1) |]
                              else mk_app k [| reify x t ab (Array.get args 0); reify x t ab (Array.get args 1) |] in
      match head_code x f with
      | 1 => bin (x.(c_EAdd))
      | 2 => bin (x.(c_ESub))
      | 3 => let a := Array.get args 0 in let b := Array.get args 1 in
             if (if is_cst x b then true else is_cst x a) then bin (x.(c_EMul)) else atom x t ab c
      | 4 => if is_cst x (Array.get args 1) then (t.(t_divmod) := true; bin (x.(c_EDiv))) else atom x t ab c
      | 5 => if is_cst x (Array.get args 1) then (t.(t_divmod) := true; bin (x.(c_EMod))) else atom x t ab c
      | 6 => let a := Array.get args 0 in let b := Array.get args 1 in
             if (if is_num a then is_num b else false) then (if ab then c else mk_app (x.(c_EPow)) [| a; b |]) else atom x t ab c
      | 7 => if ab then mk_app f [| reify x t ab (Array.get args 0) |] else mk_app (x.(c_EOpp)) [| reify x t ab (Array.get args 0) |]
      | 8 => let n := nat_lit x (Array.get args 0) 4096 0 in
             if Int.le 0 n then (if ab then c else mk_app (x.(c_EC)) [| z_of_int x n |]) else atom x t ab c
      | 9 => if ab then c else mk_app (x.(c_EC)) [| c |]       (* [comment removed for export] *)
      | _ => atom x t ab c
      end
  | Constr.Unsafe.Constructor _ _ => if ab then c else mk_app (x.(c_EC)) [| c |]    (* [comment removed for export] *)
  | _ => atom x t ab c
  end.

Ltac2 rec reify_goal (x : rctx) (t : tbl) (ab : bool) (g : constr) : constr :=
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.App f args =>
      let cmp (k : constr) (i : int) (j : int) :=
        if ab then mk_app f [| reify x t ab (Array.get args 0); reify x t ab (Array.get args 1) |]
        else mk_app k [| reify x t ab (Array.get args i); reify x t ab (Array.get args j) |] in
      match head_code x f with
      | 20 => if ab then mk_app f [| reify_goal x t ab (Array.get args 0); reify_goal x t ab (Array.get args 1) |]
              else mk_app (x.(c_GAnd)) [| reify_goal x t ab (Array.get args 0); reify_goal x t ab (Array.get args 1) |]
      | 10 => cmp (x.(c_GLe)) 0 1
      | 11 => cmp (x.(c_GLt)) 0 1
      | 21 => if ab then mk_app f [| reify_goal x t ab (Array.get args 0); reify_goal x t ab (Array.get args 1) |]
              else mk_app (x.(c_GOr)) [| reify_goal x t ab (Array.get args 0); reify_goal x t ab (Array.get args 1) |]
      | 12 => cmp (x.(c_GGe)) 0 1
      | 13 => cmp (x.(c_GGt)) 0 1
      | 22 => if ab then mk_app f [| Array.get args 0; reify x t ab (Array.get args 1); reify x t ab (Array.get args 2) |]
              else mk_app (x.(c_GEq)) [| reify x t ab (Array.get args 1); reify x t ab (Array.get args 2) |]
      | 14 => (match Constr.Unsafe.kind (Array.get args 0) with
               | Constr.Unsafe.App f2 args2 =>
                   if ab then mk_app f [| mk_app f2 [| Array.get args2 0; reify x t ab (Array.get args2 1); reify x t ab (Array.get args2 2) |] |]
                   else mk_app (x.(c_GNe)) [| reify x t ab (Array.get args2 1); reify x t ab (Array.get args2 2) |]
               | _ => fail_rc "rc_lia: goal shape"
               end)
      | _ => fail_rc "rc_lia: goal shape"
      end
  | _ => fail_rc "rc_lia: goal shape"
  end.

Ltac2 reify_cand (x : rctx) (t : tbl) (c : cand) : constr :=
  let l := reify x t false (c.(cd_l)) in let r := reify x t false (c.(cd_r)) in
  mk_app (if Int.equal (c.(cd_rel)) 0 then x.(c_FLe) else if Int.equal (c.(cd_rel)) 1 then x.(c_FLt) else x.(c_FEq)) [| l; r |].
(* [comment removed for export] *)
Ltac2 abs_cand (x : rctx) (t : tbl) (c : cand) : constr :=
  let l := reify x t true (c.(cd_l)) in let r := reify x t true (c.(cd_r)) in
  if Int.equal (c.(cd_rel)) 0 then mk_app (x.(c_zle)) [| l; r |]
  else if Int.equal (c.(cd_rel)) 1 then mk_app (x.(c_zlt)) [| l; r |]
  else mk_app (x.(h_eq)) [| x.(h_z); l; r |].

Ltac2 rec mk_list (x : rctx) (ty : constr) (l : constr list) : constr :=
  match l with
  | [] => mk_app (x.(c_nil)) [| ty |]
  | a :: r => mk_app (x.(c_cons)) [| ty; a; mk_list x ty r |]
  end.

(* [comment removed for export] *)
Ltac2 rec by_mask (x : rctx) (m : constr) (l : 'a list) : 'a list :=
  match l with
  | [] => []
  | a :: r =>
      match Constr.Unsafe.kind m with
      | Constr.Unsafe.App _ margs =>
          if Int.equal (Array.length margs) 3 then
            (if Constr.equal (Array.get margs 1) (x.(h_true)) then a :: by_mask x (Array.get margs 2) r else by_mask x (Array.get margs 2) r)
          else []
      | _ => []
      end
  end.

(* [comment removed for export] *)
Ltac2 rec fill_mask (x : rctx) (m : constr) (l : constr list) : constr list :=
  match l with
  | [] => []
  | a :: r =>
      match Constr.Unsafe.kind m with
      | Constr.Unsafe.App _ margs =>
          if Int.equal (Array.length margs) 3 then
            (if Constr.equal (Array.get margs 1) (x.(h_true)) then a else x.(h_z0)) :: fill_mask x (Array.get margs 2) r
          else x.(h_z0) :: fill_mask x m r
      | _ => x.(h_z0) :: fill_mask x m r
      end
  end.

Ltac2 Type verdict := [ Proved | Refuted | Unknown ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rc_run (refute : int) : verdict :=
  let g := Control.goal () in
  if Constr.has_evar g then fail_rc "rc_lia: evars" else
  let x := mk_rctx () in
  let nd := { nd_vars := FMap.empty FSet.Tags.ident_tag; nd_other := []; nd_new := []; nd_work := [] } in
  goal_needs x nd g;
  let sc := scan_hyps x (rc_boxes ()) in
  if Int.equal (rc_phase) 103 then fail_rc "phase 103" else
  let se := select x nd sc in
  let sel := se.(se_facts) in
  if Int.le (rc_phase) 1 then fail_rc "phase 1" else
  let t := { t_vars := FMap.empty FSet.Tags.ident_tag; t_other := []; t_n := 0; t_nat := x.(h_o); t_atoms := []; t_divmod := false;
             t_ids := []; t_avoid := Fresh.Free.of_goal () } in
  let rg := reify_goal x t false g in
  let fact_ty := gref reference:(RC.fact) in
  let rfs := List.map (reify_cand x t) sel in
  let fs1 := mk_list x fact_ty rfs in
  let call := mk_app (gref reference:(RC.rc_solve)) [| mk_app (gref reference:(Z.to_nat)) [| z_of_int x (rc_rounds) |]; fs1; rg |] in
  let res := Std.eval_vm None call in
  if Int.le (rc_phase) 2 then fail_rc "phase 2" else
  (if rc_debug then (dbg [Message.of_string "RC-DEBUG call: "; Message.of_constr call]; dbg [Message.of_string "RC-DEBUG res: "; Message.of_constr res]) else ());
  match Constr.Unsafe.kind res with
  | Constr.Unsafe.App rc rargs =>
      if Constr.equal rc (gref reference:(RC.AYes)) then
        (* [comment removed for export] *)
        match Constr.Unsafe.kind (Array.get rargs 0) with
        | Constr.Unsafe.App _ s =>
            let usedf := by_mask x (Array.get s 0) (List.combine sel rfs) in
            (* [comment removed for export] *)
            let ids := List.rev (t.(t_ids)) in
            let mkv (id : ident) := Constr.Unsafe.make (Constr.Unsafe.Var id) in
            let env := mk_list x (x.(h_z)) (List.map mkv ids) in
            let anon (ty : constr) := Constr.Binder.make None ty in
            let stmt := List.fold_right (fun p acc => let (c, _) := p in Constr.Unsafe.make (Constr.Unsafe.Prod (anon (abs_cand x t c)) acc))
                                        usedf (reify_goal x t true g) in
            let rel (n : int) := Constr.Unsafe.make (Constr.Unsafe.Rel n) in
            let bool_ty := gref reference:(bool) in
            let chk := mk_app (gref reference:(RC.rc_check)) [| rel 4; rel 3; rel 2; rel 1 |] in
            let eqt := mk_app (x.(h_eq)) [| bool_ty; chk; x.(h_true) |] in
            let prf := Constr.Unsafe.make (Constr.Unsafe.Cast (mk_app (x.(c_eq_refl)) [| bool_ty; x.(h_true) |]) Constr.Cast.vm eqt) in
            let body := Constr.Unsafe.make (Constr.Unsafe.Cast (mk_app (gref reference:(RC.rc_sound_impl)) [| env; rel 4; rel 3; rel 2; rel 1; prf |])
                                                               Constr.Cast.default stmt) in
            let bnd (nm : ident) (ty : constr) := Constr.Binder.make (Some nm) ty in
            let list_ty (a : constr) := mk_app (gref reference:(list)) [| a |] in
            let lets :=
              Constr.Unsafe.make (Constr.Unsafe.LetIn (bnd @rcF (list_ty fact_ty)) (mk_list x fact_ty (List.map (fun p => let (_, r) := p in r) usedf))
               (Constr.Unsafe.make (Constr.Unsafe.LetIn (bnd @rcG (gref reference:(RC.goal))) rg
                (Constr.Unsafe.make (Constr.Unsafe.LetIn (bnd @rcS (list_ty (gref reference:(RC.step)))) (Array.get s 2)
                 (Constr.Unsafe.make (Constr.Unsafe.LetIn (bnd @rcC (gref reference:(RC.gcert))) (Array.get s 3) body))))))) in
            (* [comment removed for export] *)
            let lam := List.fold_left (fun acc id => Constr.Unsafe.make (Constr.Unsafe.Lambda (bnd id (x.(h_z))) acc)) (Constr.Unsafe.closenl ids 1 lets) ids in
            (* [comment removed for export] *)
            let atoms := List.rev (fill_mask x (Array.get s 1) (List.rev (t.(t_atoms)))) in
            let term := match List.append atoms (List.map (fun p => let (c, _) := p in cand_proof x c) usedf) with
                        | [] => lam
                        | l => mk_app lam (Array.of_list l)
                        end in
            (if Int.equal (rc_phase) 7 then Control.refine (fun () => term) else Std.exact_no_check term);
            Proved
        | _ => fail_rc "rc_lia: result"
        end
      else if Int.le 1 refute then
        (* [comment removed for export] *)
        let consistent () : bool :=
          let blk2 := Ref.ref [] in
          let extra := List.fold_left (fun acc hy => scan_prop x blk2 (x.(h_true)) (hy.(ah_ty)) [] (hy.(ah_ty)) acc) [] (se.(se_pend)) in
          let extra := List.fold_left (fun acc ty => scan_prop x blk2 (x.(h_true)) ty [] ty acc) extra (se.(se_blk)) in
          let all := List.append (se.(se_pool)) extra in
          if Int.lt (rc_max_consist) (List.length all) then ((if rc_why then dbg [Message.of_string "RC-WHY context too large"] else ()); false) else
          let call2 := mk_app (gref reference:(RC.rc_inconsistent))
                         [| mk_app (gref reference:(Z.to_nat)) [| z_of_int x (rc_consist_rounds) |]; mk_list x fact_ty (List.map (reify_cand x t) all) |] in
          (if rc_debug then dbg [Message.of_string "RC-DEBUG call2: "; Message.of_constr call2] else ());
          if Constr.equal (Std.eval_vm None call2) (x.(h_true)) then ((if rc_why then dbg [Message.of_string "RC-WHY contradictory context"] else ()); false)
          else true in
        (* [comment removed for export] *)
        (if Constr.equal (Array.get rargs 0) (x.(h_true)) then (if consistent () then Refuted else Unknown)
         else if Int.le refute 1 then Unknown
         else if Constr.equal (Array.get rargs 1) (x.(h_true)) then
           (if t.(t_divmod) then ((if rc_why then dbg [Message.of_string "RC-WHY divmod"] else ()); Unknown)     (* [comment removed for export] *)
            else if may_refute x se then (if consistent () then Refuted else Unknown) else Unknown)
         else ((if rc_why then dbg [Message.of_string "RC-WHY unsaturated"] else ()); Unknown))
      else Unknown
  | _ => fail_rc "rc_lia: result"
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 mutable rc_or_boxes : unit -> constr list := fun () => [].
Ltac2 mutable rc_or_max : int := 4.
Ltac2 mutable rc_prune_max_facts : int := 80.
(* [comment removed for export] *)
Ltac2 rec zify_subleaves (x : rctx) (d : int) (a : constr) (acc : constr list) : constr list :=
  if Int.le d 0 then acc else
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App f args =>
      (match head_code x f with
       | 8 => zify_subleaves x (Int.sub d 1) (Array.get args 0) acc
       | 40 => Array.fold_left (fun ac y => zify_subleaves x (Int.sub d 1) y ac) acc args
       | 0 => acc
       | 9 => acc
       | _ => List.fold_left (fun ac p => let (l, _) := p in if Constr.equal l a then ac else l :: ac) acc (leaves x a 1 [])
       end)
  | Constr.Unsafe.Var _ => a :: acc
  | _ => acc
  end.
Ltac2 rec side_leaves (x : rctx) (ty : constr) (acc : constr list) : constr list option :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App f args =>
      let cmp (a : constr) (b : constr) := Some (List.fold_left (fun ac p => let (l, _) := p in l :: ac) acc (leaves x a 1 (leaves x b -1 []))) in
      (match head_code x f with
       | 10 => cmp (Array.get args 0) (Array.get args 1)
       | 11 => cmp (Array.get args 0) (Array.get args 1)
       | 12 => cmp (Array.get args 0) (Array.get args 1)
       | 13 => cmp (Array.get args 0) (Array.get args 1)
       | 22 => if Constr.equal (Array.get args 0) (x.(h_z)) then cmp (Array.get args 1) (Array.get args 2) else None
       | 20 => (match side_leaves x (Array.get args 0) acc with Some ac => side_leaves x (Array.get args 1) ac | None => None end)
       | 21 => (match side_leaves x (Array.get args 0) acc with Some ac => side_leaves x (Array.get args 1) ac | None => None end)
       | _ => None
       end)
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 rec goal_needs_l (x : rctx) (nd : needs) (g : constr) : unit :=
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.App f args =>
      (match head_code x f with
       | 20 => goal_needs_l x nd (Array.get args 0); goal_needs_l x nd (Array.get args 1)
       | 21 => goal_needs_l x nd (Array.get args 0); goal_needs_l x nd (Array.get args 1)
       | _ => goal_needs x nd g
       end)
  | Constr.Unsafe.Ind _ _ => ()
  | _ => fail_rc "rc_prune_lia: goal shape"
  end.
Ltac2 rc_prune_lia_run () : unit :=
  let g := Control.goal () in
  if Constr.has_evar g then fail_rc "rc_prune_lia: evars" else
  let x := mk_rctx () in
  let nd := { nd_vars := FMap.empty FSet.Tags.ident_tag; nd_other := []; nd_new := []; nd_work := [] } in
  goal_needs_l x nd g;
  let gleaves := List.append (FMap.fold (fun id _ acc => Constr.Unsafe.make (Constr.Unsafe.Var id) :: acc) (nd.(nd_vars)) [])
                             (List.map (fun p => let (a, _) := p in a) (nd.(nd_other))) in
  (match gleaves with [] => fail_rc "rc_prune_lia: no atoms" | _ => () end);
  let sc := scan_hyps x (rc_or_boxes ()) in
  (* [comment removed for export] *)
  List.iter (fun a => List.iter (fun l => need_add nd l 3) (zify_subleaves x 4 a [])) (List.map (fun p => let (a, _) := p in a) (nd.(nd_other)));
  (* [comment removed for export] *)
  let scored := Ref.ref [] in
  let rec ins (sc0 : int) (o : ahyp * constr list) (l : (int * (ahyp * constr list)) list) :=
    match l with
    | [] => [(sc0, o)]
    | p :: r => let (s1, _) := p in if Int.lt s1 sc0 then (sc0, o) :: l else p :: ins sc0 o r
    end in
  List.iter (fun hy =>
    match side_leaves x (hy.(ah_ty)) [] with
    | Some lvs =>
        let shared := List.fold_left (fun n a => if List.exist (Constr.equal a) gleaves then Int.add n 1 else n) 0 lvs in
        if Int.le shared 0 then () else
        Ref.set scored (ins (Int.sub (Int.mul 3 shared) (List.length lvs)) (hy, lvs) (Ref.get scored))
    | None => ()
    end) (sc.(sc_ors));
  let rec take (n : int) (l : (int * (ahyp * constr list)) list) : (ahyp * constr list) list :=
    match l with
    | [] => []
    | p :: r => if Int.le n 0 then [] else (let (_, o) := p in o :: take (Int.sub n 1) r)
    end in
  let orl := take (rc_or_max) (Ref.get scored) in
  List.iter (fun o => let (_, lvs) := o in List.iter (fun a => need_add nd a 3) lvs) orl;
  let se := select_n (rc_prune_max_facts) x nd sc in
  let sel := se.(se_facts) in
  (* [comment removed for export] *)
  let rec firstn (n : int) (l : ahyp list) : ahyp list :=
    match l with [] => [] | a :: r => if Int.le n 0 then [] else a :: firstn (Int.sub n 1) r end in
  let negl := firstn 3 (List.filter (fun hy =>
                match Constr.Unsafe.kind (hy.(ah_ty)) with
                | Constr.Unsafe.App _ nargs =>
                    (match side_leaves x (Array.get nargs 0) [] with
                     | Some lvs => List.exist (fun a => match need_get nd a with 0 => false | _ => true end) lvs
                     | None => false
                     end)
                | _ => false
                end) (sc.(sc_negs))) in
  let natargs := List.fold_left (fun acc p => let (a, _) := p in
                   match Constr.Unsafe.kind a with
                   | Constr.Unsafe.App f args => (match head_code x f with 8 => Array.get args 0 :: acc | _ => acc end)
                   | _ => acc
                   end) [] (nd.(nd_other)) in
  let rec contains (t : constr) (c : constr) : bool :=
    if Constr.equal c t then true else
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args => if contains t f then true else Array.fold_left (fun b y => if b then true else contains t y) false args
    | _ => false
    end in
  let natl := match natargs with
              | [] => []
              | _ :: _ => firstn 4 (List.filter (fun hy => List.exist (fun t => contains t (hy.(ah_ty))) natargs) (sc.(sc_nats)))
              end in
  (* [comment removed for export] *)
  let orl2 := List.filter (fun hy =>
                if List.exist (fun o => let (h0, _) := o in Ident.equal (h0.(ah_id)) (hy.(ah_id))) orl then false else
                match side_leaves x (hy.(ah_ty)) [] with
                | Some lvs => (match lvs with [] => false | _ :: _ => List.for_all (fun a => match need_get nd a with 0 => false | _ => true end) lvs end)
                | None => false
                end) (sc.(sc_ors)) in
  let orl := List.append orl (List.map (fun hy => (hy, [])) (firstn (Int.sub (rc_or_max) (List.length orl)) orl2)) in
  let orl := List.append orl (List.map (fun hy => (hy, [])) (List.append negl natl)) in
  (* [comment removed for export] *)
  let anon (ty : constr) := Constr.Binder.make None ty in
  let stmt_of (c : cand) : constr :=
    if Int.equal (c.(cd_rel)) 0 then mk_app (x.(c_zle)) [| c.(cd_l); c.(cd_r) |]
    else if Int.equal (c.(cd_rel)) 1 then mk_app (x.(c_zlt)) [| c.(cd_l); c.(cd_r) |]
    else mk_app (x.(h_eq)) [| x.(h_z); c.(cd_l); c.(cd_r) |] in
  let stmt := List.fold_right (fun c acc => Constr.Unsafe.make (Constr.Unsafe.Prod (anon (stmt_of c)) acc)) sel
                (List.fold_right (fun o acc => let (hy, _) := o in Constr.Unsafe.make (Constr.Unsafe.Prod (anon (hy.(ah_ty))) acc)) orl g) in
  (if rc_debug then dbg [Message.of_string "RC-DEBUG prune-lia: facts="; Message.of_int (List.length sel); Message.of_string " ors="; Message.of_int (List.length orl);
                         Message.of_string " stmt: "; Message.of_constr stmt] else ());
  let h := Fresh.fresh (Fresh.Free.of_goal ()) @rcP in
  Std.assert (Std.AssertType (Some (Std.IntroNaming (Std.IntroIdentifier h))) stmt
                (Some (fun () => Std.keep []; ltac1:(intros; Zify.zify; xlia zchecker))));
  let args := List.append (List.map (cand_proof x) sel)
                          (List.map (fun o => let (hy, _) := o in Constr.Unsafe.make (Constr.Unsafe.Var (hy.(ah_id)))) orl) in
  let hv := Constr.Unsafe.make (Constr.Unsafe.Var h) in
  Std.exact_no_check (match args with [] => hv | l => mk_app hv (Array.of_list l) end).
Ltac2 rc_prune_lia () : unit := Control.enter (fun () => Control.once rc_prune_lia_run).

(* [comment removed for export] *)
Ltac2 rc_lia () : unit :=
  Control.enter (fun () => match rc_run 0 with Proved => () | _ => fail_rc "rc_lia: no certificate" end).
(* [comment removed for export] *)
Ltac2 rc_decide_lvl (lvl : int) (orig : unit -> unit) : unit :=
  Control.enter (fun () =>
    let v := Control.once (fun () => Control.plus (fun () => rc_run lvl) (fun _ => Unknown)) in
    match v with
    | Proved => ()
    | Refuted => fail_rc "rc_decide: refused"
    | Unknown => orig ()
    end).
Ltac2 rc_decide (orig : unit -> unit) : unit := rc_decide_lvl 2 orig.
(* [comment removed for export] *)
Ltac2 rc_decide1 (orig : unit -> unit) : unit := rc_decide_lvl 1 orig.
(* [comment removed for export] *)
Ltac2 mutable rc_census_level : int := 2.
Ltac2 rc_verdict () : int :=
  let v := Control.once (fun () => Control.plus (fun () => rc_run (rc_census_level)) (fun _ => Unknown)) in
  match v with Proved => 0 | Refuted => 1 | Unknown => 2 end.
(* [comment removed for export] *)
Ltac2 rc_vp () : unit :=
  Control.enter (fun () =>
    let v := rc_verdict () in
    dbg [Message.of_string "RCD-VERDICT "; Message.of_int v];
    match v with 0 => () | _ => fail_rc "rc_vp" end).
End RF.

Ltac rc_lia := ltac2:(RF.rc_lia ()).
Ltac rc_prune_lia := ltac2:(RF.rc_prune_lia ()).
Ltac rc_vp := ltac2:(RF.rc_vp ()).
Ltac rc_decide orig := let f := ltac2:(orig |- RF.rc_decide (fun () => Ltac1.run orig)) in f orig.
Ltac rc_decide1 orig := let f := ltac2:(orig |- RF.rc_decide1 (fun () => Ltac1.run orig)) in f orig.


(* [comment removed for export] *)
(* [comment removed for export] *)
Module RCTest.
Section T.
Variables (a2 qoff n i2 pbs x y z w u : Z) (f : Z -> Z) (l : list nat).
Hypothesis NB : 10000 <= n <= pbs * 100000 + -19 + 19.
Hypothesis PB : 1 <= pbs <= 9.
Hypothesis QO : n + 34 <= qoff <= n + 35.
Hypothesis A2R : 0 < a2 /\ a2 + (pbs * 400000 + 136) <= 140737479966720.
Hypothesis Hi2 : 0 <= i2 <= n + 26.
Hypothesis By0 : 0 <= f (i2 + 0) < 256.
Hypothesis H1 : x <= y.
Hypothesis H2 : y < z.
Hypothesis H3 : z <= w + 3.
Hypothesis Hu : 0 <= u < 2 ^ 32.
Hypothesis Hl : (length l <= 5)%nat.
Goal 0 <= (i2 + 1) * 4294967296 < 2 ^ 64. Proof. rc_lia. Qed.
Goal 0 <= 18446744073709551615 - (a2 + qoff) < 2 ^ 64. Proof. rc_lia. Qed.
Goal (i2 + 1) * 2 <= 18446744073709551615 - (a2 + qoff). Proof. rc_lia. Qed.
Goal 0 <= f (i2 + 0) < 2 ^ 64. Proof. rc_lia. Qed.
Goal 0 <= (a2 + i2) / 4 + (f 3) mod 16 < 2 ^ 64. Proof. rc_lia. Qed.
Goal x + 1 <= w + 3. Proof. rc_lia. Qed.
Goal z <> x. Proof. rc_lia. Qed.
Goal forall (v := x + 5), 0 <= x < 10 -> 5 <= v < 15. Proof. intros. rc_lia. Qed.
Goal 0 <= Z.of_nat (length l) + 3. Proof. rc_lia. Qed.
(* [comment removed for export] *)
Goal True. Proof. (tryif (assert (0 <= u < 2 ^ 31) by rc_decide ltac:(idtac)) then fail else idtac). exact I. Qed.
Goal Z.of_nat (length l) < 7. Proof. (tryif rc_lia then fail else idtac). rc_decide ltac:(lia). Qed.
End T.
(* [comment removed for export] *)
Definition hide (P : Prop) := P.
Section O.
Variables a n b k A e S L16 nn ucr av dlen DST : Z. Variable tbl : list Z.
Hypothesis H : id (a + n <= b \/ b + k <= a).
Hypothesis Hn : 0 <= n. Hypothesis Hk : 0 <= k.
Hypothesis H1 : a <= A. Hypothesis H2 : A + 4 <= a + n. Hypothesis H3 : b <= e. Hypothesis H4 : e + 8 <= b + k.
Hypothesis SEP : hide (S + 64144 <= L16 \/ L16 + 200000 * nn <= S).
Hypothesis NN : 1 <= nn <= 9. Hypothesis U : 0 <= ucr < 257.
Hypothesis SD : id (S + 64144 <= DST \/ DST + dlen <= S). Hypothesis AV : 0 <= av <= dlen. Hypothesis K0 : hide (av <> 0).
Hypothesis TL : length tbl = 512%nat. Hypothesis IA : id (DST + dlen <= 65536 \/ 212992 <= DST).
#[local] Ltac2 Set RF.rc_or_boxes := fun () => [constr:(@id); constr:(hide)].
Goal A + 4 <= e \/ e + 8 <= A. Proof. (tryif rc_lia then fail else idtac). rc_prune_lia. Qed.
Goal forall i, 0 <= i < 200000 * nn -> L16 + 200000 * nn <= S + 2124 + 4 * ucr \/ S + 2124 + 4 * ucr + 4 <= L16 + i. Proof. intros. rc_prune_lia. Qed.
Goal S + Z.of_nat 68 <= DST + (dlen - av) \/ DST + (dlen - av) + 1 <= S. Proof. rc_prune_lia. Qed.
Goal 168936 + 4 * Z.of_nat (length tbl) <= DST + (dlen - av) \/ DST + (dlen - av) + 1 <= 168936. Proof. rc_prune_lia. Qed.
End O.
(* [comment removed for export] *)
Fixpoint heavy (n : nat) : Z := match n with O => 1 | S k => heavy k + heavy k end.
Goal forall i : nat, 0 <= heavy (22 + i) <= 255 -> True.
Proof. intros i H. set (nb := heavy (22 + i)) in *. clearbody nb. assert (0 <= nb < 2 ^ 64) by rc_lia. exact I. Qed.
End RCTest.
