(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib GWin GVEnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UG GW.
Open Scope Z_scope.
Arguments Uint63.to_Z : simpl never.

Module GVEA.
Import GVE.

Fixpoint resp_keys (f : sv -> sv) (ks : list int) (st : sstate) : sstate :=
  match ks with
  | [] => st
  | k :: t =>
      if PrimInt63.eqb k 0%uint63 then resp_keys f t st
      else match IMap.find k (s_regs st) with
           | Some r => resp_keys f t (setregs st (IMap.add k (subst_cells f r) (s_regs st)))
           | None => resp_keys f t st
           end
  end.

Section WithPc.
Variable S_PC : int.
Variable NF : nat.

Definition gvea_apply (st : sstate) : option (list sstate) :=
  match pairs (firstn NF (s_facts st)) with
  | [] => None
  | ps => let f := rw (s_facts st) ps in
          let st2 := addfacts st (new_facts (s_facts st) ps (firstn NF (s_facts st))) in
          Some [resp_keys f (List.map fst (IMap.elements (s_regs st2))) st2]
  end.

Definition gvea_contract : contract := Contract S_PC gvea_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma resp_keys_facts : forall f ks st, s_facts (resp_keys f ks st) = s_facts st.
Proof.
  intros f ks. induction ks as [|k t IH]; intros st; cbn [resp_keys]; [reflexivity|].
  destruct (PrimInt63.eqb k 0%uint63); [apply IH|]. destruct (IMap.find k (s_regs st)); rewrite IH; reflexivity.
Qed.
Lemma resp_keys_next : forall f ks st, s_next (resp_keys f ks st) = s_next st.
Proof.
  intros f ks. induction ks as [|k t IH]; intros st; cbn [resp_keys]; [reflexivity|].
  destruct (PrimInt63.eqb k 0%uint63); [apply IH|]. destruct (IMap.find k (s_regs st)); rewrite IH; reflexivity.
Qed.

Lemma resp_keys_sound : forall E f ks st ms model,
  (forall v, den E (f v) = den E v) -> st_ok segs OPS E st ms model -> st_ok segs OPS E (resp_keys f ks st) ms model.
Proof.
  intros E f ks. induction ks as [|k t IH]; intros st ms model HF HS; cbn [resp_keys]; [exact HS|].
  destruct (PrimInt63.eqb k 0%uint63) eqn:K0; [exact (IH st ms model HF HS)|].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:F; [|exact (IH st ms model HF HS)].
  apply IH; [exact HF|]. exact (st_ok_subst_cells segs OPS E st ms model k r f HS F K0 HF).
Qed.

Theorem gvea_sound : contract_sound segs OPS MP PB gvea_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gvea_contract c_apply] in HA. unfold gvea_apply in HA.
  destruct (pairs (firstn NF (s_facts st))) as [|p ps] eqn:PS; [discriminate HA|]. injection HA as <-.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  assert (RW : forall v, den E (rw (s_facts st) (p :: ps) v) = den E v).
  { apply (rw_den E); [exact FH|]. rewrite <- PS. apply (pairs_sound E). apply Forall_firstn. exact FH. }
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply resp_keys_sound; [exact RW|]. apply (addfacts_sound segs OPS E); [exact HS|].
  apply new_facts_hold; [exact RW|]. apply Forall_firstn. exact FH.
Qed.

End Sound.
End WithPc.

Definition K_BLOCKw : w64 := wlit 1%uint63.
Definition K_TWINw : w64 := wlit 9%uint63.
Definition twin_len_t (n : sv) : sv := sv_alu ALU_SRL (sv_alu ALU_ADD n (VL (wlit 7%uint63))) (VL (wlit 3%uint63)).
Definition f1_pair1 (f : fact) : list (sv * sv) :=
  match f with
  | FEq e (VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL s))) => if weqb s (wlit 8%uint63) then [] else [(e, VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL s)))]
  | _ => []
  end.
Fixpoint pairs1 (fs : list fact) : list (sv * sv) :=
  match fs with [] => [] | f :: t => f1_pair1 f ++ pairs1 t end.

Fixpoint block_rws (fs : list fact) (ws : list (sv * sv * sv)) (ps : list (sv * sv)) : list (int * w64 * sv) :=
  match ps with
  | [] => []
  | (e, VAlu ALU_ADD (VP kb ob) M) :: ps' =>
      (if weqb ob wzero then
         List.flat_map (fun w : sv * sv * sv =>
           match w with
           | (VP kb' ob', VL n, VL kd) =>
               if PrimInt63.eqb kb' kb && weqb ob' wzero && weqb kd K_BLOCKw && negb (wt n) && same_end fs (VP kb n) e then [(kb, n, M)] else []
           | _ => []
           end) ws
       else []) ++ block_rws fs ws ps'
  | _ :: ps' => block_rws fs ws ps'
  end.

Definition is_link_of (t kb : int) (f : fact) : bool :=
  match f with
  | FEq (VP t' z) (VAlu ALU_ADD (VAlu ALU_SRL (VP kb' z') (VL c)) (VL _)) =>
      PrimInt63.eqb t' t && PrimInt63.eqb kb' kb && weqb z wzero && weqb z' wzero && weqb c (wlit 3%uint63)
  | _ => false
  end.
Definition tw_lit (n : w64) : w64 := walu ALU_SRL (walu ALU_ADD n (wlit 7%uint63)) (wlit 3%uint63).
Fixpoint find_brw_block (kb : int) (n : w64) (l : list (int * w64 * sv)) : option sv :=
  match l with
  | [] => None
  | (kb', n', M) :: l' => if PrimInt63.eqb kb' kb && weqb n' n then Some M else find_brw_block kb n l'
  end.
Fixpoint find_brw_twin (fs : list fact) (t : int) (m : w64) (l : list (int * w64 * sv)) : option sv :=
  match l with
  | [] => None
  | (kb, n, M) :: l' => if existsb (is_link_of t kb) fs && weqb (tw_lit n) m then Some M else find_brw_twin fs t m l'
  end.
Definition win_rw (fs : list fact) (brw : list (int * w64 * sv)) (w : sv * sv * sv) : sv * sv * sv :=
  match w with
  | (VP k z, VL n, VL kd) =>
      if negb (weqb z wzero) then w
      else if weqb kd K_BLOCKw then match find_brw_block k n brw with Some M => (VP k z, M, VL kd) | None => w end
      else if weqb kd K_TWINw then match find_brw_twin fs k n brw with Some M => (VP k z, twin_len_t M, VL kd) | None => w end
      else w
  | _ => w
  end.
Fixpoint rw_nwin (f : sv * sv * sv -> sv * sv * sv) (n : nat) (l : list sv) : list sv :=
  match n with
  | O => l
  | S n' => match l with
            | a :: b :: c :: rest => let '(a', b', c') := f (a, b, c) in a' :: b' :: c' :: rw_nwin f n' rest
            | _ => l
            end
  end.
Definition rw_args (f : sv * sv * sv -> sv * sv * sv) (args : list sv) : list sv :=
  match args with
  | md :: aw :: nw :: rest => match lit nw with Some ni => md :: aw :: nw :: rw_nwin f (Z.to_nat (to_Z ni)) rest | None => args end
  | _ => args
  end.
Definition rw_ops (f : sv * sv * sv -> sv * sv * sv) (os : list opinst) : list opinst :=
  List.map (fun o => if is_heap o then OpI (op_id o) (rw_args f (op_args o)) else o) os.
Definition setops (st : sstate) (os : list opinst) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) os (s_priv st) (s_next st).

Fixpoint hi_rws (fs : list fact) (brw : list (int * w64 * sv)) (ws : list (sv * sv * sv)) (st : sstate) : sstate :=
  match ws with
  | [] => st
  | (VP t z, VL m, VL kd) :: ws' =>
      let st' :=
        if weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb t 0%uint63) then
          match find_brw_twin fs t m brw, IMap.find t (s_regs st) with
          | Some M, Some r => match rg_hi r with
                              | VL m' => if weqb m' m then setregs st (IMap.add t (Region (rg_lo r) (twin_len_t M) (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)) else st
                              | _ => st
                              end
          | _, _ => st
          end
        else st in
      hi_rws fs brw ws' st'
  | _ :: ws' => hi_rws fs brw ws' st
  end.

Section WithPc2.
Variable S_PC : int.
Variable NF : nat.

Definition gvea2_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in
  match pairs1 (firstn NF fs) with
  | [] => None
  | ps => let f := rw fs ps in
          let st2 := addfacts st (new_facts fs ps (firstn NF fs)) in
          let st3 := resp_keys f (List.map fst (IMap.elements (s_regs st2))) st2 in
          match the_op st3 with
          | Some (_, _, ws, _) =>
              let brw := block_rws fs ws ps in
              let st4 := setops st3 (rw_ops (win_rw fs brw) (s_ops st3)) in
              Some [hi_rws fs brw ws st4]
          | None => Some [st3]
          end
  end.
Definition gvea2_contract : contract := Contract S_PC gvea2_apply.

Section Sound2.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma pairs1_sound : forall E fs, Forall (fact_holds E) fs -> forall e r, In (e, r) (pairs1 fs) -> den E e = den E r.
Proof.
  intros E fs FH. induction fs as [|f t IH]; intros e r H; [destruct H|].
  cbn [pairs1] in H. apply in_app_iff in H as [H|H]; [|inversion FH; subst; exact (IH ltac:(assumption) e r H)].
  inversion FH as [|f' t' Hf Ht]; subst.
  destruct f as [| | | |a b| | |]; try (destruct H; fail); cbn [f1_pair1] in H; try (destruct H).
  destruct b as [| |op x y| | | | | | | |]; try (destruct H). destruct op; try (destruct H).
  destruct y as [| | | |mo u v| | | | | |]; try (destruct H). destruct mo; try (destruct H).
  destruct u as [|j o| | | | | | | | |]; try (destruct H). destruct v as [sl| | | | | | | | | |]; try (destruct H).
  destruct (weqb sl (wlit 8%uint63)); [destruct H|]. destruct H as [H|H]; [|destruct H]. injection H as <- <-. exact Hf.
Qed.

Definition brw_ok (E : env) (brw : list (int * w64 * sv)) : Prop := forall kb n M, In (kb, n, M) brw -> den E (VL n) = den E M.

Lemma find_brw_block_in : forall kb n l M, find_brw_block kb n l = Some M -> In (kb, n, M) l.
Proof.
  induction l as [|[[kb' n'] M'] l IH]; intros M H; cbn [find_brw_block] in H; [discriminate|].
  destruct (PrimInt63.eqb kb' kb && weqb n' n) eqn:C.
  - injection H as <-. apply andb_prop in C as [C1 C2]. apply Uint63.eqb_correct in C1. apply (proj1 (weqb_ok _ _)) in C2. subst. left; reflexivity.
  - right. exact (IH M H).
Qed.
Lemma find_brw_twin_in : forall fs t m l M, find_brw_twin fs t m l = Some M -> exists kb n, In (kb, n, M) l /\ tw_lit n = m.
Proof.
  induction l as [|[[kb' n'] M'] l IH]; intros M H; cbn [find_brw_twin] in H; [discriminate|].
  destruct (existsb (is_link_of t kb') fs && weqb (tw_lit n') m) eqn:C.
  - injection H as <-. apply andb_prop in C as [_ C2]. apply (proj1 (weqb_ok _ _)) in C2. exists kb', n'. split; [left; reflexivity| exact C2].
  - destruct (IH M H) as (kb & n & H1 & H2). exists kb, n. split; [right; exact H1| exact H2].
Qed.

Lemma twin_len_t_den : forall E n M, den E (VL n) = den E M -> den E (VL (tw_lit n)) = den E (twin_len_t M).
Proof.
  intros E n M H. unfold twin_len_t, tw_lit. rewrite !den_sv_alu, <- H.
  change (den E (VL (walu ALU_SRL (walu ALU_ADD n (wlit 7%uint63)) (wlit 3%uint63)))) with (wbv (walu ALU_SRL (walu ALU_ADD n (wlit 7%uint63)) (wlit 3%uint63))).
  rewrite !walu_ok. reflexivity.
Qed.

Lemma block_rws_ok : forall E fs ws ps, facts_hold E fs -> (forall e r, In (e, r) ps -> den E e = den E r) -> brw_ok E (block_rws fs ws ps).
Proof.
  intros E fs ws ps FH PS. induction ps as [|[e r] ps IH]; cbn [block_rws]; intros kb n M Hin; [destruct Hin|].
  assert (IH' : brw_ok E (block_rws fs ws ps)) by (apply IH; intros e' r' H'; apply PS; right; exact H').
  destruct r as [| |op x M0| | | | | | | |]; try exact (IH' kb n M Hin). destruct op; try exact (IH' kb n M Hin).
  destruct x as [|kb0 ob| | | | | | | | |]; try exact (IH' kb n M Hin).
  apply in_app_iff in Hin as [Hin|Hin]; [|exact (IH' kb n M Hin)].
  destruct (weqb ob wzero) eqn:OB; [|destruct Hin].
  apply in_flat_map in Hin as ([[a l] kdv] & Wi & Hin).
  destruct a as [|kb' ob'| | | | | | | | |]; try (destruct Hin; fail). destruct l as [n0| | | | | | | | | |]; try (destruct Hin; fail).
  destruct kdv as [kd| | | | | | | | | |]; try (destruct Hin; fail).
  destruct (PrimInt63.eqb kb' kb0 && weqb ob' wzero && weqb kd K_BLOCKw && negb (wt n0) && same_end fs (VP kb0 n0) e) eqn:C; [|destruct Hin].
  destruct Hin as [Hin|Hin]; [|destruct Hin]. injection Hin as <- <- <-.
  apply andb_prop in C as [C SE].
  pose proof (same_end_sound E fs (VP kb0 n0) e FH SE) as E1. rewrite (PS e _ (or_introl eq_refl)) in E1.

  apply (proj1 (weqb_ok _ _)) in OB. subst ob.
  apply (f_equal bv_unsigned) in E1. rewrite den_VPu in E1.
  change (den E (VAlu ALU_ADD (VP kb0 wzero) M0)) with (alu64 ALU_ADD (den E (VP kb0 wzero)) (den E M0)) in E1. cbn [alu64 alu] in E1.
  rewrite bv_add_unsigned in E1. unfold bv_wrap in E1. rewrite bv_modulus_64, den_VPu, wzero_ok, Z.add_0_r in E1.
  pose proof (bv_unsigned_in_range _ (ev E kb0)) as RK. rewrite bv_modulus_64 in RK. rewrite (Z.mod_small _ _ RK) in E1.
  pose proof (bv_unsigned_in_range _ (den E M0)) as RM. rewrite bv_modulus_64 in RM.
  pose proof (w2Z_range n0) as RN.
  assert (EQ : w2Z n0 = bv_unsigned (den E M0)).
  { apply (f_equal (fun z => (z - bv_unsigned (ev E kb0)) mod two64)) in E1. cbn beta in E1.
    rewrite !Zminus_mod_idemp_l in E1.
    replace (bv_unsigned (ev E kb0) + w2Z n0 - bv_unsigned (ev E kb0)) with (w2Z n0) in E1 by lia.
    replace (bv_unsigned (ev E kb0) + bv_unsigned (den E M0) - bv_unsigned (ev E kb0)) with (bv_unsigned (den E M0)) in E1 by lia.
    rewrite !Z.mod_small in E1 by (unfold two64 in *; lia). exact E1. }
  change (den E (VL n0)) with (wbv n0). apply wbv_eq_of_w2Z. exact EQ.
Qed.

Lemma win_rw_den : forall E fs brw w, brw_ok E brw ->
  let '(a, b, c) := w in let '(a', b', c') := win_rw fs brw w in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c.
Proof.
  intros E fs brw [[a b] c] BR. cbn beta.
  unfold win_rw. destruct a as [|k z| | | | | | | | |]; try (repeat split; reflexivity).
  destruct b as [n| | | | | | | | | |]; try (repeat split; reflexivity). destruct c as [kd| | | | | | | | | |]; try (repeat split; reflexivity).
  destruct (negb (weqb z wzero)); [repeat split; reflexivity|].
  destruct (weqb kd K_BLOCKw).
  - destruct (find_brw_block k n brw) as [M|] eqn:F; [|repeat split; reflexivity].
    repeat split; try reflexivity. symmetry. exact (BR k n M (find_brw_block_in _ _ _ _ F)).
  - destruct (weqb kd K_TWINw); [|repeat split; reflexivity].
    destruct (find_brw_twin fs k n brw) as [M|] eqn:F; [|repeat split; reflexivity].
    destruct (find_brw_twin_in _ _ _ _ _ F) as (kb & n' & Hin & TL). subst n.
    repeat split; try reflexivity. symmetry. apply twin_len_t_den. exact (BR kb n' M Hin).
Qed.

Lemma rw_nwin_den : forall E f, (forall a b c, let '(a', b', c') := f (a, b, c) in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c) ->
  forall n l, map (den E) (rw_nwin f n l) = map (den E) l.
Proof.
  intros E f HF. induction n as [|n IH]; intros l; cbn [rw_nwin]; [reflexivity|].
  destruct l as [|a [|b [|c rest]]]; try reflexivity.
  specialize (HF a b c). destruct (f (a, b, c)) as [[a' b'] c']. destruct HF as (Ha & Hb & Hc).
  cbn [map]. rewrite Ha, Hb, Hc, IH. reflexivity.
Qed.

Lemma rw_args_den : forall E f, (forall a b c, let '(a', b', c') := f (a, b, c) in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c) ->
  forall args, map (den E) (rw_args f args) = map (den E) args.
Proof.
  intros E f HF args. unfold rw_args. destruct args as [|md [|aw [|nw rest]]]; try reflexivity.
  destruct (lit nw) as [ni|]; [|reflexivity]. cbn [map]. rewrite (rw_nwin_den E f HF). reflexivity.
Qed.

Lemma st_ok_ops_ext : forall E st ms model (g : opinst -> opinst),
  (forall o, op_id (g o) = op_id o /\ map (den E) (op_args (g o)) = map (den E) (op_args o)) ->
  st_ok segs OPS E st ms model -> st_ok segs OPS E (setops st (List.map g (s_ops st))) ms model.
Proof.
  intros E st ms model g HG HS.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (INS : insts E (List.map g (s_ops st)) = insts E (s_ops st)).
  { unfold insts. rewrite List.map_map. apply List.map_ext. intros o. destruct (HG o) as [H1 H2]. rewrite H1, H2. reflexivity. }
  constructor; cbn [setops s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - unfold ops_hold in *. apply Forall_map. eapply Forall_impl; [|exact Pops]. cbn beta. intros o Ho.
    destruct (HG o) as [H1 H2]. rewrite H1, H2. exact Ho.
  - unfold ops_apart in *. apply Forall_map. eapply Forall_impl; [|exact Papart]. cbn beta. intros o Ho a Ha.
    destruct (HG o) as [H1 H2]. rewrite H1, H2 in Ha. exact (Ho a Ha).
  - intros a FA. rewrite INS. exact (Pcov a FA).
Qed.

Lemma hi_rws_sound : forall E fs brw ws, brw_ok E brw ->
  forall st ms model, st_ok segs OPS E st ms model -> st_ok segs OPS E (hi_rws fs brw ws st) ms model.
Proof.
  intros E fs brw ws BR. induction ws as [|[[a l] kdv] ws IH]; intros st ms model HS; cbn [hi_rws]; [exact HS|].
  destruct a as [|t z| | | | | | | | |]; try exact (IH st ms model HS).
  destruct l as [m| | | | | | | | | |]; try exact (IH st ms model HS). destruct kdv as [kd| | | | | | | | | |]; try exact (IH st ms model HS).
  apply IH.
  destruct (weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb t 0%uint63)) eqn:C; [|exact HS].
  destruct (find_brw_twin fs t m brw) as [M|] eqn:F; [|exact HS].
  destruct (IMap.find t (s_regs st)) as [r|] eqn:R; [|exact HS].
  destruct (rg_hi r) as [m'| | | | | | | | | |] eqn:RH; try exact HS.
  destruct (weqb m' m) eqn:MM; [|exact HS].
  apply andb_prop in C as [C T0]. apply negb_true_iff in T0.
  apply (sethi_sound segs OPS E st ms model t r (twin_len_t M) HS R T0).
  rewrite RH. apply (proj1 (weqb_ok _ _)) in MM. subst m'.
  destruct (find_brw_twin_in _ _ _ _ _ F) as (kb & n & Hin & TL). subst m. apply twin_len_t_den. exact (BR kb n M Hin).
Qed.

Lemma hi_rws_facts : forall fs brw ws st, s_facts (hi_rws fs brw ws st) = s_facts st /\ s_next (hi_rws fs brw ws st) = s_next st.
Proof.
  intros fs brw ws. induction ws as [|[[a l] kdv] ws IH]; intros st; cbn [hi_rws]; [split; reflexivity|].
  destruct a as [|t z| | | | | | | | |]; try apply IH. destruct l as [m| | | | | | | | | |]; try apply IH. destruct kdv as [kd| | | | | | | | | |]; try apply IH.
  match goal with |- context [hi_rws fs brw ws ?S] => destruct (IH S) as [A B]; rewrite A, B end.
  destruct (weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb t 0%uint63)); [|split; reflexivity].
  destruct (find_brw_twin fs t m brw); [|split; reflexivity]. destruct (IMap.find t (s_regs st)) as [r|]; [|split; reflexivity].
  destruct (rg_hi r); try (split; reflexivity). destruct (weqb _ m); split; reflexivity.
Qed.

Theorem gvea2_sound : contract_sound segs OPS MP PB gvea2_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gvea2_contract c_apply] in HA. unfold gvea2_apply in HA.
  destruct (pairs1 (firstn NF (s_facts st))) as [|p ps] eqn:PS; [discriminate HA|].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  assert (PSD : forall e r, In (e, r) (p :: ps) -> den E e = den E r).
  { rewrite <- PS. apply (pairs1_sound E). apply Forall_firstn. exact FH. }
  assert (RW : forall v, den E (rw (s_facts st) (p :: ps) v) = den E v).
  { apply (rw_den E); [exact FH| exact PSD]. }
  set (st2 := addfacts st (new_facts (s_facts st) (p :: ps) (firstn NF (s_facts st)))) in HA.
  set (st3 := resp_keys (rw (s_facts st) (p :: ps)) (List.map fst (IMap.elements (s_regs st2))) st2) in HA.
  assert (HS3 : st_ok segs OPS E st3 ms model).
  { subst st3 st2. apply resp_keys_sound; [exact RW|]. apply (addfacts_sound segs OPS E); [exact HS|].
    apply new_facts_hold; [exact RW|]. apply Forall_firstn. exact FH. }
  assert (NX3 : s_next st3 = s_next st).
  { subst st3 st2. rewrite resp_keys_next, addfacts_next. reflexivity. }
  destruct (the_op st3) as [[[[mdi aw] ws] ca]|] eqn:TOP.
  - injection HA as <-.
    set (brw := block_rws (s_facts st) ws (p :: ps)).
    assert (BR : brw_ok E brw) by (apply block_rws_ok; [exact FH| exact PSD]).
    assert (WD : forall a b c, let '(a', b', c') := win_rw (s_facts st) brw (a, b, c) in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c).
    { intros a b c. exact (win_rw_den E (s_facts st) brw (a, b, c) BR). }
    set (st4 := setops st3 (rw_ops (win_rw (s_facts st) brw) (s_ops st3))).
    assert (HS4 : st_ok segs OPS E st4 ms model).
    { subst st4. unfold rw_ops. apply (st_ok_ops_ext E st3 ms model); [|exact HS3].
      intros o. destruct (is_heap o); [|split; reflexivity]. cbn [op_id op_args]. split; [reflexivity|]. apply rw_args_den. exact WD. }
    refine (Hk _ (or_introl eq_refl) E ms model _ HMP _).
    + apply env_ext_refl.
    + apply hi_rws_sound; [exact BR| exact HS4].
  - injection HA as <-. refine (Hk _ (or_introl eq_refl) E ms model _ HMP HS3). apply env_ext_refl.
Qed.
End Sound2.
End WithPc2.

Section WithPc3.
Variable S_PC : int.
Variable NF : nat.

Definition gvea3_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in
  match pairs1 (firstn NF fs) with
  | [] => None
  | ps => let f := rw fs ps in
          let st2 := addfacts st (new_facts fs ps (firstn NF fs)) in
          let st3 := resp_keys f (List.map fst (IMap.elements (s_regs st2))) st2 in
          match the_op st3 with
          | Some (_, _, ws, _) =>
              let brw := block_rws fs ws ps in
              Some [setops st3 (rw_ops (win_rw fs brw) (s_ops st3))]
          | None => Some [st3]
          end
  end.
Definition gvea3_contract : contract := Contract S_PC gvea3_apply.

Section Sound3.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem gvea3_sound : contract_sound segs OPS MP PB gvea3_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gvea3_contract c_apply] in HA. unfold gvea3_apply in HA.
  destruct (pairs1 (firstn NF (s_facts st))) as [|p ps] eqn:PS; [discriminate HA|].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  assert (PSD : forall e r, In (e, r) (p :: ps) -> den E e = den E r).
  { rewrite <- PS. apply (pairs1_sound E). apply Forall_firstn. exact FH. }
  assert (RW : forall v, den E (rw (s_facts st) (p :: ps) v) = den E v).
  { apply (rw_den E); [exact FH| exact PSD]. }
  set (st2 := addfacts st (new_facts (s_facts st) (p :: ps) (firstn NF (s_facts st)))) in HA.
  set (st3 := resp_keys (rw (s_facts st) (p :: ps)) (List.map fst (IMap.elements (s_regs st2))) st2) in HA.
  assert (HS3 : st_ok segs OPS E st3 ms model).
  { subst st3 st2. apply resp_keys_sound; [exact RW|]. apply (addfacts_sound segs OPS E); [exact HS|].
    apply new_facts_hold; [exact RW|]. apply Forall_firstn. exact FH. }
  destruct (the_op st3) as [[[[mdi aw] ws] ca]|] eqn:TOP.
  - injection HA as <-.
    set (brw := block_rws (s_facts st) ws (p :: ps)).
    assert (BR : brw_ok E brw) by (apply block_rws_ok; [exact FH| exact PSD]).
    assert (WD : forall a b c, let '(a', b', c') := win_rw (s_facts st) brw (a, b, c) in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c).
    { intros a b c. exact (win_rw_den E (s_facts st) brw (a, b, c) BR). }
    refine (Hk _ (or_introl eq_refl) E ms model _ HMP _).
    + apply env_ext_refl.
    + unfold rw_ops. apply st_ok_ops_ext; [|exact HS3].
      intros o. destruct (is_heap o); [|split; reflexivity]. cbn [op_id op_args]. split; [reflexivity|]. apply rw_args_den. exact WD.
  - injection HA as <-. refine (Hk _ (or_introl eq_refl) E ms model _ HMP HS3). apply env_ext_refl.
Qed.
End Sound3.
End WithPc3.
End GVEA.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GWin OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GVEnd.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UG GW.
Open Scope Z_scope.
Arguments Uint63.to_Z : simpl never.

Module GVEA.
Import GVE.

Fixpoint resp_keys (f : sv -> sv) (ks : list int) (st : sstate) : sstate :=
  match ks with
  | [] => st
  | k :: t =>
      if PrimInt63.eqb k 0%uint63 then resp_keys f t st
      else match IMap.find k (s_regs st) with
           | Some r => resp_keys f t (setregs st (IMap.add k (subst_cells f r) (s_regs st)))
           | None => resp_keys f t st
           end
  end.

Section WithPc.
Variable S_PC : int.
Variable NF : nat.

Definition gvea_apply (st : sstate) : option (list sstate) :=
  match pairs (firstn NF (s_facts st)) with
  | [] => None
  | ps => let f := rw (s_facts st) ps in
          let st2 := addfacts st (new_facts (s_facts st) ps (firstn NF (s_facts st))) in
          Some [resp_keys f (List.map fst (IMap.elements (s_regs st2))) st2]
  end.

Definition gvea_contract : contract := Contract S_PC gvea_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma resp_keys_facts : forall f ks st, s_facts (resp_keys f ks st) = s_facts st.
Proof.
  intros f ks. induction ks as [|k t IH]; intros st; cbn [resp_keys]; [reflexivity|].
  destruct (PrimInt63.eqb k 0%uint63); [apply IH|]. destruct (IMap.find k (s_regs st)); rewrite IH; reflexivity.
Qed.
Lemma resp_keys_next : forall f ks st, s_next (resp_keys f ks st) = s_next st.
Proof.
  intros f ks. induction ks as [|k t IH]; intros st; cbn [resp_keys]; [reflexivity|].
  destruct (PrimInt63.eqb k 0%uint63); [apply IH|]. destruct (IMap.find k (s_regs st)); rewrite IH; reflexivity.
Qed.

Lemma resp_keys_sound : forall E f ks st ms model,
  (forall v, den E (f v) = den E v) -> st_ok segs OPS E st ms model -> st_ok segs OPS E (resp_keys f ks st) ms model.
Proof.
  intros E f ks. induction ks as [|k t IH]; intros st ms model HF HS; cbn [resp_keys]; [exact HS|].
  destruct (PrimInt63.eqb k 0%uint63) eqn:K0; [exact (IH st ms model HF HS)|].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:F; [|exact (IH st ms model HF HS)].
  apply IH; [exact HF|]. exact (st_ok_subst_cells segs OPS E st ms model k r f HS F K0 HF).
Qed.

Theorem gvea_sound : contract_sound segs OPS MP PB gvea_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gvea_contract c_apply] in HA. unfold gvea_apply in HA.
  destruct (pairs (firstn NF (s_facts st))) as [|p ps] eqn:PS; [discriminate HA|]. injection HA as <-.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  assert (RW : forall v, den E (rw (s_facts st) (p :: ps) v) = den E v).
  { apply (rw_den E); [exact FH|]. rewrite <- PS. apply (pairs_sound E). apply Forall_firstn. exact FH. }
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply resp_keys_sound; [exact RW|]. apply (addfacts_sound segs OPS E); [exact HS|].
  apply new_facts_hold; [exact RW|]. apply Forall_firstn. exact FH.
Qed.

End Sound.
End WithPc.

Definition K_BLOCKw : w64 := wlit 1%uint63.
Definition K_TWINw : w64 := wlit 9%uint63.
Definition twin_len_t (n : sv) : sv := sv_alu ALU_SRL (sv_alu ALU_ADD n (VL (wlit 7%uint63))) (VL (wlit 3%uint63)).
Definition f1_pair1 (f : fact) : list (sv * sv) :=
  match f with
  | FEq e (VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL s))) => if weqb s (wlit 8%uint63) then [] else [(e, VAlu ALU_ADD b (VMd M_MUL (VP j o) (VL s)))]
  | _ => []
  end.
Fixpoint pairs1 (fs : list fact) : list (sv * sv) :=
  match fs with [] => [] | f :: t => f1_pair1 f ++ pairs1 t end.

Fixpoint block_rws (fs : list fact) (ws : list (sv * sv * sv)) (ps : list (sv * sv)) : list (int * w64 * sv) :=
  match ps with
  | [] => []
  | (e, VAlu ALU_ADD (VP kb ob) M) :: ps' =>
      (if weqb ob wzero then
         List.flat_map (fun w : sv * sv * sv =>
           match w with
           | (VP kb' ob', VL n, VL kd) =>
               if PrimInt63.eqb kb' kb && weqb ob' wzero && weqb kd K_BLOCKw && negb (wt n) && same_end fs (VP kb n) e then [(kb, n, M)] else []
           | _ => []
           end) ws
       else []) ++ block_rws fs ws ps'
  | _ :: ps' => block_rws fs ws ps'
  end.

Definition is_link_of (t kb : int) (f : fact) : bool :=
  match f with
  | FEq (VP t' z) (VAlu ALU_ADD (VAlu ALU_SRL (VP kb' z') (VL c)) (VL _)) =>
      PrimInt63.eqb t' t && PrimInt63.eqb kb' kb && weqb z wzero && weqb z' wzero && weqb c (wlit 3%uint63)
  | _ => false
  end.
Definition tw_lit (n : w64) : w64 := walu ALU_SRL (walu ALU_ADD n (wlit 7%uint63)) (wlit 3%uint63).
Fixpoint find_brw_block (kb : int) (n : w64) (l : list (int * w64 * sv)) : option sv :=
  match l with
  | [] => None
  | (kb', n', M) :: l' => if PrimInt63.eqb kb' kb && weqb n' n then Some M else find_brw_block kb n l'
  end.
Fixpoint find_brw_twin (fs : list fact) (t : int) (m : w64) (l : list (int * w64 * sv)) : option sv :=
  match l with
  | [] => None
  | (kb, n, M) :: l' => if existsb (is_link_of t kb) fs && weqb (tw_lit n) m then Some M else find_brw_twin fs t m l'
  end.
Definition win_rw (fs : list fact) (brw : list (int * w64 * sv)) (w : sv * sv * sv) : sv * sv * sv :=
  match w with
  | (VP k z, VL n, VL kd) =>
      if negb (weqb z wzero) then w
      else if weqb kd K_BLOCKw then match find_brw_block k n brw with Some M => (VP k z, M, VL kd) | None => w end
      else if weqb kd K_TWINw then match find_brw_twin fs k n brw with Some M => (VP k z, twin_len_t M, VL kd) | None => w end
      else w
  | _ => w
  end.
Fixpoint rw_nwin (f : sv * sv * sv -> sv * sv * sv) (n : nat) (l : list sv) : list sv :=
  match n with
  | O => l
  | S n' => match l with
            | a :: b :: c :: rest => let '(a', b', c') := f (a, b, c) in a' :: b' :: c' :: rw_nwin f n' rest
            | _ => l
            end
  end.
Definition rw_args (f : sv * sv * sv -> sv * sv * sv) (args : list sv) : list sv :=
  match args with
  | md :: aw :: nw :: rest => match lit nw with Some ni => md :: aw :: nw :: rw_nwin f (Z.to_nat (to_Z ni)) rest | None => args end
  | _ => args
  end.
Definition rw_ops (f : sv * sv * sv -> sv * sv * sv) (os : list opinst) : list opinst :=
  List.map (fun o => if is_heap o then OpI (op_id o) (rw_args f (op_args o)) else o) os.
Definition setops (st : sstate) (os : list opinst) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) os (s_priv st) (s_next st).

Fixpoint hi_rws (fs : list fact) (brw : list (int * w64 * sv)) (ws : list (sv * sv * sv)) (st : sstate) : sstate :=
  match ws with
  | [] => st
  | (VP t z, VL m, VL kd) :: ws' =>
      let st' :=
        if weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb t 0%uint63) then
          match find_brw_twin fs t m brw, IMap.find t (s_regs st) with
          | Some M, Some r => match rg_hi r with
                              | VL m' => if weqb m' m then setregs st (IMap.add t (Region (rg_lo r) (twin_len_t M) (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)) else st
                              | _ => st
                              end
          | _, _ => st
          end
        else st in
      hi_rws fs brw ws' st'
  | _ :: ws' => hi_rws fs brw ws' st
  end.

Section WithPc2.
Variable S_PC : int.
Variable NF : nat.

Definition gvea2_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in
  match pairs1 (firstn NF fs) with
  | [] => None
  | ps => let f := rw fs ps in
          let st2 := addfacts st (new_facts fs ps (firstn NF fs)) in
          let st3 := resp_keys f (List.map fst (IMap.elements (s_regs st2))) st2 in
          match the_op st3 with
          | Some (_, _, ws, _) =>
              let brw := block_rws fs ws ps in
              let st4 := setops st3 (rw_ops (win_rw fs brw) (s_ops st3)) in
              Some [hi_rws fs brw ws st4]
          | None => Some [st3]
          end
  end.
Definition gvea2_contract : contract := Contract S_PC gvea2_apply.

Section Sound2.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma pairs1_sound : forall E fs, Forall (fact_holds E) fs -> forall e r, In (e, r) (pairs1 fs) -> den E e = den E r.
Proof.
  intros E fs FH. induction fs as [|f t IH]; intros e r H; [destruct H|].
  cbn [pairs1] in H. apply in_app_iff in H as [H|H]; [|inversion FH; subst; exact (IH ltac:(assumption) e r H)].
  inversion FH as [|f' t' Hf Ht]; subst.
  destruct f as [| | | |a b| | |]; try (destruct H; fail); cbn [f1_pair1] in H; try (destruct H).
  destruct b as [| |op x y| | | | | | | |]; try (destruct H). destruct op; try (destruct H).
  destruct y as [| | | |mo u v| | | | | |]; try (destruct H). destruct mo; try (destruct H).
  destruct u as [|j o| | | | | | | | |]; try (destruct H). destruct v as [sl| | | | | | | | | |]; try (destruct H).
  destruct (weqb sl (wlit 8%uint63)); [destruct H|]. destruct H as [H|H]; [|destruct H]. injection H as <- <-. exact Hf.
Qed.

Definition brw_ok (E : env) (brw : list (int * w64 * sv)) : Prop := forall kb n M, In (kb, n, M) brw -> den E (VL n) = den E M.

Lemma find_brw_block_in : forall kb n l M, find_brw_block kb n l = Some M -> In (kb, n, M) l.
Proof.
  induction l as [|[[kb' n'] M'] l IH]; intros M H; cbn [find_brw_block] in H; [discriminate|].
  destruct (PrimInt63.eqb kb' kb && weqb n' n) eqn:C.
  - injection H as <-. apply andb_prop in C as [C1 C2]. apply Uint63.eqb_correct in C1. apply (proj1 (weqb_ok _ _)) in C2. subst. left; reflexivity.
  - right. exact (IH M H).
Qed.
Lemma find_brw_twin_in : forall fs t m l M, find_brw_twin fs t m l = Some M -> exists kb n, In (kb, n, M) l /\ tw_lit n = m.
Proof.
  induction l as [|[[kb' n'] M'] l IH]; intros M H; cbn [find_brw_twin] in H; [discriminate|].
  destruct (existsb (is_link_of t kb') fs && weqb (tw_lit n') m) eqn:C.
  - injection H as <-. apply andb_prop in C as [_ C2]. apply (proj1 (weqb_ok _ _)) in C2. exists kb', n'. split; [left; reflexivity| exact C2].
  - destruct (IH M H) as (kb & n & H1 & H2). exists kb, n. split; [right; exact H1| exact H2].
Qed.

Lemma twin_len_t_den : forall E n M, den E (VL n) = den E M -> den E (VL (tw_lit n)) = den E (twin_len_t M).
Proof.
  intros E n M H. unfold twin_len_t, tw_lit. rewrite !den_sv_alu, <- H.
  change (den E (VL (walu ALU_SRL (walu ALU_ADD n (wlit 7%uint63)) (wlit 3%uint63)))) with (wbv (walu ALU_SRL (walu ALU_ADD n (wlit 7%uint63)) (wlit 3%uint63))).
  rewrite !walu_ok. reflexivity.
Qed.

Lemma block_rws_ok : forall E fs ws ps, facts_hold E fs -> (forall e r, In (e, r) ps -> den E e = den E r) -> brw_ok E (block_rws fs ws ps).
Proof.
  intros E fs ws ps FH PS. induction ps as [|[e r] ps IH]; cbn [block_rws]; intros kb n M Hin; [destruct Hin|].
  assert (IH' : brw_ok E (block_rws fs ws ps)) by (apply IH; intros e' r' H'; apply PS; right; exact H').
  destruct r as [| |op x M0| | | | | | | |]; try exact (IH' kb n M Hin). destruct op; try exact (IH' kb n M Hin).
  destruct x as [|kb0 ob| | | | | | | | |]; try exact (IH' kb n M Hin).
  apply in_app_iff in Hin as [Hin|Hin]; [|exact (IH' kb n M Hin)].
  destruct (weqb ob wzero) eqn:OB; [|destruct Hin].
  apply in_flat_map in Hin as ([[a l] kdv] & Wi & Hin).
  destruct a as [|kb' ob'| | | | | | | | |]; try (destruct Hin; fail). destruct l as [n0| | | | | | | | | |]; try (destruct Hin; fail).
  destruct kdv as [kd| | | | | | | | | |]; try (destruct Hin; fail).
  destruct (PrimInt63.eqb kb' kb0 && weqb ob' wzero && weqb kd K_BLOCKw && negb (wt n0) && same_end fs (VP kb0 n0) e) eqn:C; [|destruct Hin].
  destruct Hin as [Hin|Hin]; [|destruct Hin]. injection Hin as <- <- <-.
  apply andb_prop in C as [C SE].
  pose proof (same_end_sound E fs (VP kb0 n0) e FH SE) as E1. rewrite (PS e _ (or_introl eq_refl)) in E1.

  apply (proj1 (weqb_ok _ _)) in OB. subst ob.
  apply (f_equal bv_unsigned) in E1. rewrite den_VPu in E1.
  change (den E (VAlu ALU_ADD (VP kb0 wzero) M0)) with (alu64 ALU_ADD (den E (VP kb0 wzero)) (den E M0)) in E1. cbn [alu64 alu] in E1.
  rewrite bv_add_unsigned in E1. unfold bv_wrap in E1. rewrite bv_modulus_64, den_VPu, wzero_ok, Z.add_0_r in E1.
  pose proof (bv_unsigned_in_range _ (ev E kb0)) as RK. rewrite bv_modulus_64 in RK. rewrite (Z.mod_small _ _ RK) in E1.
  pose proof (bv_unsigned_in_range _ (den E M0)) as RM. rewrite bv_modulus_64 in RM.
  pose proof (w2Z_range n0) as RN.
  assert (EQ : w2Z n0 = bv_unsigned (den E M0)).
  { apply (f_equal (fun z => (z - bv_unsigned (ev E kb0)) mod two64)) in E1. cbn beta in E1.
    rewrite !Zminus_mod_idemp_l in E1.
    replace (bv_unsigned (ev E kb0) + w2Z n0 - bv_unsigned (ev E kb0)) with (w2Z n0) in E1 by lia.
    replace (bv_unsigned (ev E kb0) + bv_unsigned (den E M0) - bv_unsigned (ev E kb0)) with (bv_unsigned (den E M0)) in E1 by lia.
    rewrite !Z.mod_small in E1 by (unfold two64 in *; lia). exact E1. }
  change (den E (VL n0)) with (wbv n0). apply wbv_eq_of_w2Z. exact EQ.
Qed.

Lemma win_rw_den : forall E fs brw w, brw_ok E brw ->
  let '(a, b, c) := w in let '(a', b', c') := win_rw fs brw w in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c.
Proof.
  intros E fs brw [[a b] c] BR. cbn beta.
  unfold win_rw. destruct a as [|k z| | | | | | | | |]; try (repeat split; reflexivity).
  destruct b as [n| | | | | | | | | |]; try (repeat split; reflexivity). destruct c as [kd| | | | | | | | | |]; try (repeat split; reflexivity).
  destruct (negb (weqb z wzero)); [repeat split; reflexivity|].
  destruct (weqb kd K_BLOCKw).
  - destruct (find_brw_block k n brw) as [M|] eqn:F; [|repeat split; reflexivity].
    repeat split; try reflexivity. symmetry. exact (BR k n M (find_brw_block_in _ _ _ _ F)).
  - destruct (weqb kd K_TWINw); [|repeat split; reflexivity].
    destruct (find_brw_twin fs k n brw) as [M|] eqn:F; [|repeat split; reflexivity].
    destruct (find_brw_twin_in _ _ _ _ _ F) as (kb & n' & Hin & TL). subst n.
    repeat split; try reflexivity. symmetry. apply twin_len_t_den. exact (BR kb n' M Hin).
Qed.

Lemma rw_nwin_den : forall E f, (forall a b c, let '(a', b', c') := f (a, b, c) in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c) ->
  forall n l, map (den E) (rw_nwin f n l) = map (den E) l.
Proof.
  intros E f HF. induction n as [|n IH]; intros l; cbn [rw_nwin]; [reflexivity|].
  destruct l as [|a [|b [|c rest]]]; try reflexivity.
  specialize (HF a b c). destruct (f (a, b, c)) as [[a' b'] c']. destruct HF as (Ha & Hb & Hc).
  cbn [map]. rewrite Ha, Hb, Hc, IH. reflexivity.
Qed.

Lemma rw_args_den : forall E f, (forall a b c, let '(a', b', c') := f (a, b, c) in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c) ->
  forall args, map (den E) (rw_args f args) = map (den E) args.
Proof.
  intros E f HF args. unfold rw_args. destruct args as [|md [|aw [|nw rest]]]; try reflexivity.
  destruct (lit nw) as [ni|]; [|reflexivity]. cbn [map]. rewrite (rw_nwin_den E f HF). reflexivity.
Qed.

Lemma st_ok_ops_ext : forall E st ms model (g : opinst -> opinst),
  (forall o, op_id (g o) = op_id o /\ map (den E) (op_args (g o)) = map (den E) (op_args o)) ->
  st_ok segs OPS E st ms model -> st_ok segs OPS E (setops st (List.map g (s_ops st))) ms model.
Proof.
  intros E st ms model g HG HS.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (INS : insts E (List.map g (s_ops st)) = insts E (s_ops st)).
  { unfold insts. rewrite List.map_map. apply List.map_ext. intros o. destruct (HG o) as [H1 H2]. rewrite H1, H2. reflexivity. }
  constructor; cbn [setops s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - unfold ops_hold in *. apply Forall_map. eapply Forall_impl; [|exact Pops]. cbn beta. intros o Ho.
    destruct (HG o) as [H1 H2]. rewrite H1, H2. exact Ho.
  - unfold ops_apart in *. apply Forall_map. eapply Forall_impl; [|exact Papart]. cbn beta. intros o Ho a Ha.
    destruct (HG o) as [H1 H2]. rewrite H1, H2 in Ha. exact (Ho a Ha).
  - intros a FA. rewrite INS. exact (Pcov a FA).
Qed.

Lemma hi_rws_sound : forall E fs brw ws, brw_ok E brw ->
  forall st ms model, st_ok segs OPS E st ms model -> st_ok segs OPS E (hi_rws fs brw ws st) ms model.
Proof.
  intros E fs brw ws BR. induction ws as [|[[a l] kdv] ws IH]; intros st ms model HS; cbn [hi_rws]; [exact HS|].
  destruct a as [|t z| | | | | | | | |]; try exact (IH st ms model HS).
  destruct l as [m| | | | | | | | | |]; try exact (IH st ms model HS). destruct kdv as [kd| | | | | | | | | |]; try exact (IH st ms model HS).
  apply IH.
  destruct (weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb t 0%uint63)) eqn:C; [|exact HS].
  destruct (find_brw_twin fs t m brw) as [M|] eqn:F; [|exact HS].
  destruct (IMap.find t (s_regs st)) as [r|] eqn:R; [|exact HS].
  destruct (rg_hi r) as [m'| | | | | | | | | |] eqn:RH; try exact HS.
  destruct (weqb m' m) eqn:MM; [|exact HS].
  apply andb_prop in C as [C T0]. apply negb_true_iff in T0.
  apply (sethi_sound segs OPS E st ms model t r (twin_len_t M) HS R T0).
  rewrite RH. apply (proj1 (weqb_ok _ _)) in MM. subst m'.
  destruct (find_brw_twin_in _ _ _ _ _ F) as (kb & n & Hin & TL). subst m. apply twin_len_t_den. exact (BR kb n M Hin).
Qed.

Lemma hi_rws_facts : forall fs brw ws st, s_facts (hi_rws fs brw ws st) = s_facts st /\ s_next (hi_rws fs brw ws st) = s_next st.
Proof.
  intros fs brw ws. induction ws as [|[[a l] kdv] ws IH]; intros st; cbn [hi_rws]; [split; reflexivity|].
  destruct a as [|t z| | | | | | | | |]; try apply IH. destruct l as [m| | | | | | | | | |]; try apply IH. destruct kdv as [kd| | | | | | | | | |]; try apply IH.
  match goal with |- context [hi_rws fs brw ws ?S] => destruct (IH S) as [A B]; rewrite A, B end.
  destruct (weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb t 0%uint63)); [|split; reflexivity].
  destruct (find_brw_twin fs t m brw); [|split; reflexivity]. destruct (IMap.find t (s_regs st)) as [r|]; [|split; reflexivity].
  destruct (rg_hi r); try (split; reflexivity). destruct (weqb _ m); split; reflexivity.
Qed.

Theorem gvea2_sound : contract_sound segs OPS MP PB gvea2_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gvea2_contract c_apply] in HA. unfold gvea2_apply in HA.
  destruct (pairs1 (firstn NF (s_facts st))) as [|p ps] eqn:PS; [discriminate HA|].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  assert (PSD : forall e r, In (e, r) (p :: ps) -> den E e = den E r).
  { rewrite <- PS. apply (pairs1_sound E). apply Forall_firstn. exact FH. }
  assert (RW : forall v, den E (rw (s_facts st) (p :: ps) v) = den E v).
  { apply (rw_den E); [exact FH| exact PSD]. }
  set (st2 := addfacts st (new_facts (s_facts st) (p :: ps) (firstn NF (s_facts st)))) in HA.
  set (st3 := resp_keys (rw (s_facts st) (p :: ps)) (List.map fst (IMap.elements (s_regs st2))) st2) in HA.
  assert (HS3 : st_ok segs OPS E st3 ms model).
  { subst st3 st2. apply resp_keys_sound; [exact RW|]. apply (addfacts_sound segs OPS E); [exact HS|].
    apply new_facts_hold; [exact RW|]. apply Forall_firstn. exact FH. }
  assert (NX3 : s_next st3 = s_next st).
  { subst st3 st2. rewrite resp_keys_next, addfacts_next. reflexivity. }
  destruct (the_op st3) as [[[[mdi aw] ws] ca]|] eqn:TOP.
  - injection HA as <-.
    set (brw := block_rws (s_facts st) ws (p :: ps)).
    assert (BR : brw_ok E brw) by (apply block_rws_ok; [exact FH| exact PSD]).
    assert (WD : forall a b c, let '(a', b', c') := win_rw (s_facts st) brw (a, b, c) in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c).
    { intros a b c. exact (win_rw_den E (s_facts st) brw (a, b, c) BR). }
    set (st4 := setops st3 (rw_ops (win_rw (s_facts st) brw) (s_ops st3))).
    assert (HS4 : st_ok segs OPS E st4 ms model).
    { subst st4. unfold rw_ops. apply (st_ok_ops_ext E st3 ms model); [|exact HS3].
      intros o. destruct (is_heap o); [|split; reflexivity]. cbn [op_id op_args]. split; [reflexivity|]. apply rw_args_den. exact WD. }
    refine (Hk _ (or_introl eq_refl) E ms model _ HMP _).
    + apply env_ext_refl.
    + apply hi_rws_sound; [exact BR| exact HS4].
  - injection HA as <-. refine (Hk _ (or_introl eq_refl) E ms model _ HMP HS3). apply env_ext_refl.
Qed.
End Sound2.
End WithPc2.

Section WithPc3.
Variable S_PC : int.
Variable NF : nat.

Definition gvea3_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in
  match pairs1 (firstn NF fs) with
  | [] => None
  | ps => let f := rw fs ps in
          let st2 := addfacts st (new_facts fs ps (firstn NF fs)) in
          let st3 := resp_keys f (List.map fst (IMap.elements (s_regs st2))) st2 in
          match the_op st3 with
          | Some (_, _, ws, _) =>
              let brw := block_rws fs ws ps in
              Some [setops st3 (rw_ops (win_rw fs brw) (s_ops st3))]
          | None => Some [st3]
          end
  end.
Definition gvea3_contract : contract := Contract S_PC gvea3_apply.

Section Sound3.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem gvea3_sound : contract_sound segs OPS MP PB gvea3_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gvea3_contract c_apply] in HA. unfold gvea3_apply in HA.
  destruct (pairs1 (firstn NF (s_facts st))) as [|p ps] eqn:PS; [discriminate HA|].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  assert (PSD : forall e r, In (e, r) (p :: ps) -> den E e = den E r).
  { rewrite <- PS. apply (pairs1_sound E). apply Forall_firstn. exact FH. }
  assert (RW : forall v, den E (rw (s_facts st) (p :: ps) v) = den E v).
  { apply (rw_den E); [exact FH| exact PSD]. }
  set (st2 := addfacts st (new_facts (s_facts st) (p :: ps) (firstn NF (s_facts st)))) in HA.
  set (st3 := resp_keys (rw (s_facts st) (p :: ps)) (List.map fst (IMap.elements (s_regs st2))) st2) in HA.
  assert (HS3 : st_ok segs OPS E st3 ms model).
  { subst st3 st2. apply resp_keys_sound; [exact RW|]. apply (addfacts_sound segs OPS E); [exact HS|].
    apply new_facts_hold; [exact RW|]. apply Forall_firstn. exact FH. }
  destruct (the_op st3) as [[[[mdi aw] ws] ca]|] eqn:TOP.
  - injection HA as <-.
    set (brw := block_rws (s_facts st) ws (p :: ps)).
    assert (BR : brw_ok E brw) by (apply block_rws_ok; [exact FH| exact PSD]).
    assert (WD : forall a b c, let '(a', b', c') := win_rw (s_facts st) brw (a, b, c) in den E a' = den E a /\ den E b' = den E b /\ den E c' = den E c).
    { intros a b c. exact (win_rw_den E (s_facts st) brw (a, b, c) BR). }
    refine (Hk _ (or_introl eq_refl) E ms model _ HMP _).
    + apply env_ext_refl.
    + unfold rw_ops. apply st_ok_ops_ext; [|exact HS3].
      intros o. destruct (is_heap o); [|split; reflexivity]. cbn [op_id op_args]. split; [reflexivity|]. apply rw_args_den. exact WD.
  - injection HA as <-. refine (Hk _ (or_introl eq_refl) E ms model _ HMP HS3). apply env_ext_refl.
Qed.
End Sound3.
End WithPc3.
End GVEA.
End TwinB.
