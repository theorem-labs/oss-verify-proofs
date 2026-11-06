(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib GWin.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UG GW.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.

Module GVE.

Definition f1_pairs (f : fact) : list (sv * sv) :=
  match f with
  | FEq e (VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL s))) =>
      (e, VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL s))) ::
      match e, b with
      | VP ke oe, VP kb ob => [(VP ke (wadd oe s), VAlu ALU_ADD (VP kb (wadd ob s)) (VMd M_MUL (VP j o) (VL s)))]
      | _, _ => []
      end
  | _ => []
  end.

Definition f1_pairs_s (f : fact) : list (sv * sv) :=
  match f with
  | FEq _ (VAlu ALU_ADD _ (VMd M_MUL _ (VL s))) => if weqb s (wlit 8%uint63) then [] else f1_pairs f
  | _ => f1_pairs f
  end.
Fixpoint pairs (fs : list fact) : list (sv * sv) :=
  match fs with
  | [] => []
  | f :: t => f1_pairs_s f ++ pairs t
  end.

Definition same_end (fs : list fact) (v t : sv) : bool :=
  if sv_eqb v t then true
  else match v, t with
       | VP k o, VP kt ot => fact_lookup fs (is_FEq (VP kt wzero) (VP k (wsub o ot)))
       | _, _ => false
       end.

Lemma same_end_sound : forall E fs v t, facts_hold E fs -> same_end fs v t = true -> den E v = den E t.
Proof.
  intros E fs v t FH H. unfold same_end in H. destruct (sv_eqb v t) eqn:Q.
  - apply sv_eqb_eq in Q. subst v. reflexivity.
  - destruct v as [|k o| | | | | | | | |]; try discriminate. destruct t as [|kt ot| | | | | | | | |]; try discriminate.
    pose proof (proj2 (syntactic_eq_sound E fs FH (VP kt wzero) (VP k (wsub o ot))) H) as Hf. cbn [den] in Hf.
    apply bv_eq. apply (f_equal bv_unsigned) in Hf. rewrite !bv_add_unsigned, !wbv_unsigned in Hf. rewrite wsub_ok, wzero_ok in Hf.
    unfold bv_wrap in Hf. rewrite bv_modulus_64 in Hf. rewrite Z.add_0_r in Hf.
    pose proof (bv_unsigned_in_range _ (ev E kt)) as RK. rewrite bv_modulus_64 in RK. rewrite (Z.mod_small _ _ RK) in Hf.
    cbn [den]. rewrite !bv_add_unsigned, !wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. rewrite Hf.
    rewrite Zplus_mod_idemp_l.
    replace (bv_unsigned (ev E k) + (w2Z o - w2Z ot) mod two64 + w2Z ot) with ((bv_unsigned (ev E k) + w2Z ot) + (w2Z o - w2Z ot) mod two64) by lia.
    rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Fixpoint rw (fs : list fact) (ps : list (sv * sv)) (v : sv) : sv :=
  match ps with
  | [] => v
  | (e, r) :: t => if same_end fs v e then r else rw fs t v
  end.

Definition rw_fact (fs : list fact) (ps : list (sv * sv)) (f : fact) : fact :=
  match f with
  | FULt a b => FULt (rw fs ps a) (rw fs ps b)
  | FULe a b => FULe (rw fs ps a) (rw fs ps b)
  | FEq a b => FEq (rw fs ps a) (rw fs ps b)
  | FNe a b => FNe (rw fs ps a) (rw fs ps b)
  | FSLt a b => FSLt (rw fs ps a) (rw fs ps b)
  | FSLe a b => FSLe (rw fs ps a) (rw fs ps b)
  | FRange _ _ _ | FAlign _ _ => f
  end.
Definition trivial_eq (f : fact) : bool := match f with FEq a b => sv_eqb a b | _ => false end.
Fixpoint new_facts (fs0 : list fact) (ps : list (sv * sv)) (fs : list fact) : list fact :=
  match fs with
  | [] => []
  | f :: t => let f' := rw_fact fs0 ps f in
              if fact_eqb f' f || trivial_eq f' then new_facts fs0 ps t else f' :: new_facts fs0 ps t
  end.
Fixpoint addfacts (st : sstate) (l : list fact) : sstate :=
  match l with [] => st | f :: t => addfacts (addfact st f) t end.

Section WithPc.
Variable S_PC : int.
Variable KREG : int.
Variable NF : nat.

Definition gve_apply (st : sstate) : option (list sstate) :=
  match IMap.find KREG (s_regs st) with
  | Some r1 =>
      match pairs (firstn NF (s_facts st)) with
      | [] => None
      | ps => if PrimInt63.eqb KREG 0%uint63 then None
              else let st2 := addfacts st (new_facts (s_facts st) ps (firstn NF (s_facts st))) in
                   Some [setregs st2 (IMap.add KREG (subst_cells (rw (s_facts st) ps) r1) (s_regs st2))]
      end
  | None => None
  end.

Definition gve_contract : contract := Contract S_PC gve_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma addmod_cong : forall x y c, x mod two64 = y mod two64 -> (x + c) mod two64 = (y + c) mod two64.
Proof. intros x y c H. rewrite <- (Zplus_mod_idemp_l x), <- (Zplus_mod_idemp_l y), H. reflexivity. Qed.

Lemma f1_pairs_sound : forall E f, fact_holds E f -> forall e r, In (e, r) (f1_pairs f) -> den E e = den E r.
Proof.
  intros E f Hf e r HI. unfold f1_pairs in HI.
  destruct f as [? ? ?|? ?|? ?|? ?|e0 rhs|? ?|? ?|? ?]; try (destruct HI; fail).
  destruct rhs as [?|? ?|op b m|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try (destruct HI; fail). destruct op; try (destruct HI; fail).
  destruct m as [?|? ?|? ? ?|? ? ?|mo mj ms_|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try (destruct HI; fail). destruct mo; try (destruct HI; fail).
  destruct mj as [?|j o|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try (destruct HI; fail).
  destruct ms_ as [s|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try (destruct HI; fail).
  cbn [fact_holds] in Hf.
  destruct HI as [EQ|HI]; [injection EQ as <- <-; exact Hf|].
  destruct e0 as [?|ke oe|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try (destruct HI; fail).
  destruct b as [?|kb ob|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ?]; try (destruct HI; fail).
  destruct HI as [EQ|[]]. injection EQ as <- <-.
  apply bv_eq. apply (f_equal bv_unsigned) in Hf.
  set (Mt := VMd M_MUL (VP j o) (VL s)) in *.
  change (den E (VAlu ALU_ADD (VP kb ob) Mt)) with (bv_add (den E (VP kb ob)) (den E Mt)) in Hf.
  change (den E (VAlu ALU_ADD (VP kb (wadd ob s)) Mt)) with (bv_add (den E (VP kb (wadd ob s))) (den E Mt)).
  cbn [den] in Hf |- *. rewrite !bv_add_unsigned, !wbv_unsigned in Hf |- *. rewrite !wadd_ok.
  unfold bv_wrap in *. rewrite bv_modulus_64 in *.
  set (a := bv_unsigned (ev E ke)) in *. set (b := bv_unsigned (ev E kb)) in *. set (m := bv_unsigned (den E Mt)) in *.
  rewrite Zplus_mod_idemp_l in Hf.
  assert (L : (a + (w2Z oe + w2Z s) mod two64) mod two64 = ((a + w2Z oe) + w2Z s) mod two64).
  { rewrite Zplus_mod_idemp_r. f_equal. lia. }
  assert (R : ((b + (w2Z ob + w2Z s) mod two64) mod two64 + m) mod two64 = ((b + w2Z ob + m) + w2Z s) mod two64).
  { rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ m), Z.add_assoc, Zplus_mod_idemp_r. f_equal. lia. }
  rewrite L, R. apply addmod_cong. exact Hf.
Qed.

Lemma f1_pairs_s_incl : forall f p, In p (f1_pairs_s f) -> In p (f1_pairs f).
Proof.
  intros f p H. unfold f1_pairs_s in H.
  repeat match type of H with context [match ?x with _ => _ end] => destruct x end; try exact H; destruct H.
Qed.

Lemma pairs_sound : forall E fs, Forall (fact_holds E) fs -> forall e r, In (e, r) (pairs fs) -> den E e = den E r.
Proof.
  intros E fs FH. induction FH as [|f t Hf Ht IH]; intros e r HI; cbn [pairs] in HI; [destruct HI|].
  apply in_app_iff in HI as [HI|HI]; [exact (f1_pairs_sound E f Hf e r (f1_pairs_s_incl f (e, r) HI))| exact (IH e r HI)].
Qed.

Lemma rw_den : forall E fs ps, facts_hold E fs -> (forall e r, In (e, r) ps -> den E e = den E r) -> forall v, den E (rw fs ps v) = den E v.
Proof.
  intros E fs ps FH. induction ps as [|[e r] t IH]; intros H v; cbn [rw]; [reflexivity|].
  destruct (same_end fs v e) eqn:Q.
  - rewrite (same_end_sound E fs v e FH Q). symmetry. apply H. left. reflexivity.
  - apply IH. intros e' r' HI. apply H. right. exact HI.
Qed.

Lemma Forall_firstn : forall A (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; cbn [firstn]; [constructor|].
  destruct H as [|x l Hx Hl]; [constructor|]. constructor; [exact Hx| exact (IH l Hl)].
Qed.

Lemma rw_fact_holds : forall E fs ps, (forall v, den E (rw fs ps v) = den E v) -> forall f, fact_holds E f -> fact_holds E (rw_fact fs ps f).
Proof. intros E fs ps H f Hf. destruct f; cbn [rw_fact fact_holds] in *; rewrite ?H; exact Hf. Qed.

Lemma new_facts_hold : forall E fs0 ps, (forall v, den E (rw fs0 ps v) = den E v) -> forall fs, Forall (fact_holds E) fs -> Forall (fact_holds E) (new_facts fs0 ps fs).
Proof.
  intros E fs0 ps H fs FH. induction FH as [|f t Hf Ht IH]; cbn [new_facts]; [constructor|].
  destruct (fact_eqb (rw_fact fs0 ps f) f || trivial_eq (rw_fact fs0 ps f)); [exact IH|].
  constructor; [exact (rw_fact_holds E fs0 ps H f Hf)| exact IH].
Qed.

Lemma addfacts_regs : forall l st, s_regs (addfacts st l) = s_regs st.
Proof. induction l as [|f t IH]; intros st; cbn [addfacts]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma addfacts_next : forall l st, s_next (addfacts st l) = s_next st.
Proof. induction l as [|f t IH]; intros st; cbn [addfacts]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma addfacts_sound : forall E l st ms model, st_ok segs OPS E st ms model -> Forall (fact_holds E) l -> st_ok segs OPS E (addfacts st l) ms model.
Proof.
  intros E l. induction l as [|f t IH]; intros st ms model HS FH; cbn [addfacts]; [exact HS|].
  inversion FH as [|? ? Hf Ht]; subst. apply IH; [apply addfact_sound; assumption| exact Ht].
Qed.

Theorem gve_sound : contract_sound segs OPS MP PB gve_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gve_contract c_apply] in HA. unfold gve_apply in HA.
  destruct (IMap.find KREG (s_regs st)) as [r1|] eqn:F1; [|discriminate HA].
  destruct (pairs (firstn NF (s_facts st))) as [|p ps] eqn:PS; [discriminate HA|].
  destruct (PrimInt63.eqb KREG 0%uint63) eqn:K0; [discriminate HA|]. injection HA as <-.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  assert (RW : forall v, den E (rw (s_facts st) (p :: ps) v) = den E v).
  { apply rw_den; [exact FH|]. rewrite <- PS. apply pairs_sound. apply Forall_firstn. exact FH. }
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply (st_ok_subst_cells segs OPS E _ ms model KREG r1 (rw (s_facts st) (p :: ps))); [| rewrite addfacts_regs; exact F1| exact K0| exact RW].
  apply addfacts_sound; [exact HS|]. apply new_facts_hold; [exact RW|]. apply Forall_firstn. exact FH.
Qed.

End Sound.
End WithPc.
End GVE.
