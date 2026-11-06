(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GViewDrop2.

Definition link_anchor (S : w64) (sh : int) (f : fact) : option int :=
  match f with
  | FEq (VP s z) (VAlu ALU_ADD (VAlu ALU_SRL (VP n z') (VL c)) (VL s')) =>
      if PrimInt63.eqb s sh && weqb z wzero && weqb z' wzero && PrimInt63.eqb (shamt6 c) 3%uint63 && weqb s' S then Some n else None
  | _ => None
  end.
Fixpoint block_of_twin (S : w64) (fs : list fact) (sh : int) : option int :=
  match fs with [] => None | f :: fs' => match link_anchor S sh f with Some n => Some n | None => block_of_twin S fs' sh end end.
Fixpoint has_lbk_to (fs : list fact) (n k : int) : bool :=
  match fs with
  | [] => false
  | FULe (VP k' _) (VP n' z) :: fs' => (PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero) || has_lbk_to fs' n k
  | FEq (VP n' z) (VP k' _) :: fs' => (PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero) || has_lbk_to fs' n k
  | _ :: fs' => has_lbk_to fs' n k
  end.

Definition sv_mentions (k : int) (v : sv) : bool := in_vs k (sv_vs v []).
Definition region_mentions (k : int) (r : region) : bool :=
  sv_mentions k (rg_hi r) || negb (IMap.forallb (fun _ gr => forallb (fun c => negb (sv_mentions k (c_v c))) (g_cells gr)) (rg_cells r)).
Definition st_mentions (k : int) (st : sstate) : bool :=
  negb (rf_allb (fun v => negb (sv_mentions k v)) (s_rf st))
  || negb (rf_allb (fun v => negb (sv_mentions k v)) (s_ff st))
  || (match s_resv st with RAddr a => sv_mentions k a | _ => false end)
  || negb (IMap.forallb (fun _ r => negb (region_mentions k r)) (s_regs st))
  || existsb (fun f => in_vs k (fact_vs f)) (s_facts st)
  || existsb (fun o => existsb (sv_mentions k) (op_args o)) (s_ops st).
Definition orphan (st : sstate) (s2 : int) : bool := negb (st_mentions s2 st).

Definition is_view_shape (r : region) : bool :=
  negb (rg_w r) && (match rg_bg r with BGZero => true | _ => false end) && (match rg_cells r with IMap.Leaf => true | _ => false end).

Definition win_keys (st : sstate) : list int :=
  match the_op st with
  | Some (_, _, ws, _) => List.fold_right (fun w acc => match w with (VP s _, _, _) => s :: acc | _ => acc end) [] ws
  | None => []
  end.
Fixpoint in_keys (k : int) (l : list int) : bool := match l with [] => false | x :: l' => PrimInt63.eqb k x || in_keys k l' end.

Definition block_keys (st : sstate) : list int :=
  match the_op st with
  | Some (_, _, ws, _) => List.fold_right (fun w acc => match w with (VP s _, _, VL kd) => if weqb kd (wlit 1%uint63) then s :: acc else acc | _ => acc end) [] ws
  | None => []
  end.

Local Notation "a &&& b" := (if a then b else false) (at level 40, left associativity, only parsing).
Local Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing).
Definition selected_l (S : w64) (st : sstate) (WK BK : list int) (mode : option int) (s2 : int) (r2 : region) : bool :=
  is_view_shape r2 &&& negb (PrimInt63.eqb s2 0%uint63) &&& negb (PrimInt63.eqb s2 1%uint63) &&& negb (in_keys s2 WK) &&&
  (match block_of_twin S (s_facts st) s2 with
   | Some n =>
       match mode with
       | None => negb (PrimInt63.eqb n 0%uint63) &&& negb (PrimInt63.eqb n 1%uint63)
                 &&& ((match IMap.find n (s_regs st) with None => true | Some _ => false end)
                      ||| in_keys n BK)
       | Some k => negb (PrimInt63.eqb n k) &&& has_lbk_to (s_facts st) n k
       end
   | None => match mode with None => orphan st s2 | Some _ => false end
   end).

Definition selected (S : w64) (st : sstate) (mode : option int) (s2 : int) (r2 : region) : bool :=
  negb (PrimInt63.eqb s2 0%uint63) && negb (PrimInt63.eqb s2 1%uint63) && is_view_shape r2 && negb (in_keys s2 (win_keys st)) &&
  (match block_of_twin S (s_facts st) s2 with
   | Some n =>
       match mode with
       | None => negb (PrimInt63.eqb n 0%uint63) && negb (PrimInt63.eqb n 1%uint63)
                 && ((match IMap.find n (s_regs st) with None => true | Some _ => false end)
                     || in_keys n (block_keys st))
       | Some k => negb (PrimInt63.eqb n k) && has_lbk_to (s_facts st) n k
       end
   | None => match mode with None => orphan st s2 | Some _ => false end
   end).
Lemma selected_l_eq : forall S st mode s2 r2, selected_l S st (win_keys st) (block_keys st) mode s2 r2 = selected S st mode s2 r2.
Proof.
  intros S st mode s2 r2. unfold selected_l, selected.
  destruct (is_view_shape r2); destruct (PrimInt63.eqb s2 0%uint63); destruct (PrimInt63.eqb s2 1%uint63); destruct (in_keys s2 (win_keys st)); cbn [negb andb];
  destruct (block_of_twin S (s_facts st) s2) as [n|]; try reflexivity; destruct mode as [k|]; try reflexivity;
  destruct (PrimInt63.eqb n 0%uint63); destruct (PrimInt63.eqb n 1%uint63); destruct (PrimInt63.eqb n k) || idtac; cbn [negb andb];
  try reflexivity; destruct (IMap.find n (s_regs st)); reflexivity.
Qed.

Definition fact_subject (f : fact) : option int :=
  match f with FEq (VP s _) _ => Some s | FRange s _ _ => Some s | FAlign s _ => Some s | _ => None end.
Definition keep_fact (ks : list int) (f : fact) : bool := match fact_subject f with Some s => negb (in_keys s ks) | None => true end.

Definition drop_keys (S : w64) (st : sstate) (mode : option int) : list int :=
  let WK := win_keys st in let BK := block_keys st in
  List.map fst (List.filter (fun kr => selected_l S st WK BK mode (fst kr) (snd kr)) (IMap.elements (s_regs st))).
Lemma drop_keys_eq : forall S st mode,
  drop_keys S st mode = List.map fst (List.filter (fun kr => selected S st mode (fst kr) (snd kr)) (IMap.elements (s_regs st))).
Proof. intros S st mode. unfold drop_keys. f_equal. apply filter_ext. intros kr. apply selected_l_eq. Qed.

Definition dropped (st : sstate) (ks : list int) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (remove_keys ks (s_regs st)) (List.filter (keep_fact ks) (s_facts st)) (s_ops st) (s_priv st) (s_next st).

Section WithPc.
Variable S_PC : int.
Variable S : w64.
Variable MODE : sstate -> option (option int).

Definition gviewdrop_apply (st : sstate) : option (list sstate) :=
  match MODE st with
  | Some m => match drop_keys S st m with [] => None | ks => Some [dropped st ks] end
  | None => None
  end.

Definition gviewdrop_contract : contract := Contract S_PC gviewdrop_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma in_keys_In : forall k l, in_keys k l = true -> In k l.
Proof.
  induction l as [|x l IH]; cbn [in_keys]; intros H; [discriminate|]. apply orb_prop in H as [H|H]; [left; symmetry; apply Uint63.eqb_correct; exact H| right; exact (IH H)].
Qed.

Lemma st_ok_dropped : forall E st ms mo ks, ~ In 0%uint63 ks ->
  st_ok segs OPS E st ms mo -> st_ok segs OPS E (dropped st ks) ms mo.
Proof.
  intros E st ms mo ks N0 HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (FIND : forall k r, IMap.find k (remove_keys ks (s_regs st)) = Some r -> IMap.find k (s_regs st) = Some r).
  { intros k r F. exact (proj2 (proj1 (find_remove_keys ks _ k r Pbst) F)). }
  assert (BASED : forall a, in_based E (remove_keys ks (s_regs st)) a -> in_based E (s_regs st) a).
  { intros a (k & r & F & K & R). exists k, r. split; [exact (FIND k r F)| split; assumption]. }
  constructor; cbn [dropped s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply remove_keys_bst. exact Pbst.
  - intros k r F. exact (Preg k r (FIND k r F)).
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a A. exact (Pdisj k1 r1 k2 r2 (FIND _ _ F1) (FIND _ _ F2) NE K1 K2 W a A).
  - intros r0 g gr c F0. exact (Ppub r0 g gr c (FIND _ _ F0)).
  - unfold facts_hold in *. apply Forall_forall. intros f Hf. apply filter_In in Hf as [Hf _]. exact (proj1 (Forall_forall _ _) Pfacts f Hf).
  - unfold ops_apart in *. apply Forall_forall. intros o Ho a Ha. pose proof (proj1 (Forall_forall _ _) Papart o Ho a Ha) as [A B].
    split; [| exact B]. intros X. apply A. exact (BASED a X).
  - intros a FA. apply Pcov. destruct FA as [B|Sg]; [left; exact (BASED a B)| right; exact Sg].
Qed.

Lemma drop_keys_no0 : forall st m, ~ In 0%uint63 (drop_keys S st m).
Proof.
  intros st m H. rewrite drop_keys_eq in H. apply in_map_iff in H as ([k r] & EQ & Hin). cbn [fst] in EQ. subst k.
  apply filter_In in Hin as [_ SEL]. unfold selected in SEL. cbn [fst snd] in SEL.
  apply andb_prop in SEL as [SEL _]. apply andb_prop in SEL as [SEL _]. apply andb_prop in SEL as [SEL _]. apply andb_prop in SEL as [SEL _].
  rewrite Uint63.eqb_refl in SEL. discriminate SEL.
Qed.

Theorem gviewdrop_sound : contract_sound segs OPS MP PB gviewdrop_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gviewdrop_contract c_apply] in HAP. unfold gviewdrop_apply in HAP.
  destruct (MODE st) as [m|]; [|discriminate].
  destruct (drop_keys S st m) as [|k0 ks0] eqn:DK; [discriminate|]. injection HAP as <-.
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl _ _) HMP _).
  apply st_ok_dropped; [| exact HS]. rewrite <- DK. apply drop_keys_no0.
Qed.

End Sound.
End WithPc.

Definition mode_gc (_ : sstate) : option (option int) := Some None.
Definition mode_reg (r : r5) (st : sstate) : option (option int) := match getr st r with VP k _ => Some (Some k) | _ => None end.
Definition mode_carg (i : nat) (st : sstate) : option (option int) :=
  match the_op st with
  | Some (_, _, _, ca) => match nth_error ca i with Some (VP k _) => Some (Some k) | _ => None end
  | None => None
  end.
Definition gviewgc_contract (pc : int) (S : w64) : contract := gviewdrop_contract pc S mode_gc.
Definition gviewdrop_reg_contract (pc : int) (S : w64) (r : r5) : contract := gviewdrop_contract pc S (mode_reg r).

Definition gviewdrop_carg_contract (pc : int) (S : w64) (i : nat) : contract := gviewdrop_contract pc S (mode_carg i).

End GViewDrop2.
