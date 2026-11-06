(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.

Module GCurA.

Fixpoint flat (v : sv) (acc : list sv) : list sv :=
  match v with
  | VAlu ALU_ADD a b => flat a (flat b acc)
  | _ => v :: acc
  end.

Definition ro_anchor (R : IMap.t region) (v : sv) : bool :=
  match v with
  | VP k _ => negb (PrimInt63.eqb k 0%uint63) && negb (PrimInt63.eqb k 1%uint63)
              && match IMap.find k R with Some r => negb (rg_w r) || match rg_bg r with BGBlob _ _ => true | _ => false end | None => false end
  | _ => false
  end.

Fixpoint take_anchor (R : IMap.t region) (xs : list sv) : option (sv * list sv) :=
  match xs with
  | [] => None
  | x :: xs' =>
      if ro_anchor R x then Some (x, xs')
      else match take_anchor R xs' with Some (a, r) => Some (a, x :: r) | None => None end
  end.

Definition rebuild (a : sv) (rest : list sv) : sv :=
  match a, rest with
  | VP k o, x :: xs =>
      let off := fold_left (fun acc y => sv_alu ALU_ADD acc y) xs x in
      sv_alu ALU_ADD (VP k wzero) (sv_alu ALU_ADD off (VL o))
  | _, _ => a
  end.

Definition canon (R : IMap.t region) (v : sv) : sv :=
  match v with
  | VAlu ALU_ADD _ _ =>
      match take_anchor R (flat v []) with
      | Some (a, ((_ :: _) as rest)) => let c := rebuild a rest in if UG.msame v c then c else v
      | _ => v
      end
  | _ => v
  end.

Lemma canon_den : forall E R v, den E (canon R v) = den E v.
Proof.
  intros E R v. unfold canon. destruct v; try reflexivity. destruct op; try reflexivity.
  destruct (take_anchor R (flat (VAlu ALU_ADD v1 v2) [])) as [[a rest]|]; [|reflexivity].
  destruct rest as [|x xs]; [reflexivity|].
  destruct (UG.msame (VAlu ALU_ADD v1 v2) (rebuild a (x :: xs))) eqn:M; [|reflexivity].
  symmetry. exact (UG.msame_sound E _ _ M).
Qed.

Section WithPc.
Variable CUR_PC : int.

Definition regs_map_nostack (f : sv -> sv) (R : IMap.t region) : IMap.t region :=
  let R' := IMap.map (region_map f) R in
  match IMap.find 1%uint63 R with Some r1 => IMap.add 1%uint63 r1 R' | None => R' end.

Lemma find_nostack : forall f R k, IMap.bst R ->
  IMap.find k (regs_map_nostack f R) = match IMap.find k R with Some r0 => Some (if PrimInt63.eqb k 1%uint63 then r0 else region_map f r0) | None => None end.
Proof.
  intros f R k B. unfold regs_map_nostack.
  destruct (IMap.find 1%uint63 R) as [r1|] eqn:F1.
  - destruct (PrimInt63.eqb k 1%uint63) eqn:K.
    + apply Uint63.eqb_correct in K. subst k. rewrite IMap.find_add_same by (apply IMap.bst_map; exact B). rewrite F1. reflexivity.
    + rewrite IMap.find_add_other; [| apply IMap.bst_map; exact B | intros E1; subst k; rewrite Uint63.eqb_refl in K; discriminate K].
      rewrite IMap.find_map. destruct (IMap.find k R); reflexivity.
  - rewrite IMap.find_map. destruct (IMap.find k R) as [r0|] eqn:F0; [|reflexivity]. cbn [option_map].
    destruct (PrimInt63.eqb k 1%uint63) eqn:K; [|reflexivity].
    apply Uint63.eqb_correct in K. subst k. rewrite F1 in F0. discriminate F0.
Qed.

Lemma bst_nostack : forall f R, IMap.bst R -> IMap.bst (regs_map_nostack f R).
Proof.
  intros f R B. unfold regs_map_nostack. destruct (IMap.find 1%uint63 R); [apply IMap.add_bst|]; apply IMap.bst_map; exact B.
Qed.

Lemma hiZ_sel : forall E f (b : bool) r, (forall a, den E (f a) = den E a) -> hiZ E (if b then r else region_map f r) = hiZ E r.
Proof. intros E f b r VS'. destruct b; [reflexivity| apply (hiZ_map _ E VS')]. Qed.
Lemma loZ_sel : forall f (b : bool) r, loZ (if b then r else region_map f r) = loZ r.
Proof. intros f b r. destruct b; [reflexivity| apply (loZ_map _)]. Qed.
Lemma w_sel : forall f (b : bool) r, rg_w (if b then r else region_map f r) = rg_w r.
Proof. intros f b r. destruct b; reflexivity. Qed.
Lemma lo_sel : forall f (b : bool) r, rg_lo (if b then r else region_map f r) = rg_lo r.
Proof. intros f b r. destruct b; reflexivity. Qed.

Definition gcur_apply (st : sstate) : option (list sstate) :=
  let f := canon (s_regs st) in
  Some [SS (s_pc st) (rf_map f (s_rf st)) (s_ff st) (s_resv st) (regs_map_nostack f (s_regs st))
           (List.map (fact_map f) (s_facts st)) (s_ops st) (s_priv st) (s_next st)].

Definition gcur_contract : contract := Contract CUR_PC gcur_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma gcur_st_ok : forall E st ms model (f : sv -> sv),
  (forall a, den E (f a) = den E a) -> f (VL wzero) = VL wzero ->
  st_ok segs OPS E st ms model ->
  st_ok segs OPS E (SS (s_pc st) (rf_map f (s_rf st)) (s_ff st) (s_resv st) (regs_map_nostack f (s_regs st))
                       (List.map (fact_map f) (s_facts st)) (s_ops st) (s_priv st) (s_next st)) ms model.
Proof.
  intros E st ms model f VS' FZ HS.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - rewrite rf_get_map, Px0. exact FZ.
  - intros r. rewrite rf_get_map, VS'. exact (Pregs r).
  - apply bst_nostack. exact Pbst.
  - intros k r F. rewrite (find_nostack f _ k Pbst) in F. destruct (IMap.find k (s_regs st)) as [r0|] eqn:F0; [|discriminate F].
    injection F as <-. destruct (PrimInt63.eqb k 1%uint63); [exact (Preg k r0 F0)|]. apply region_ok_map; [exact VS'|]. exact (Preg k r0 F0).
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a. rewrite (find_nostack f _ k1 Pbst) in F1. rewrite (find_nostack f _ k2 Pbst) in F2.
    destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
    destruct (IMap.find k2 (s_regs st)) as [q2|] eqn:G2; [|discriminate F2].
    injection F1 as <-. injection F2 as <-.
    rewrite !(hiZ_sel E f _ _ VS'), !(loZ_sel f). rewrite !(w_sel f) in W. apply (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2). exact W.
  - intros r0 g gr c F0 Fg Hc i Hi. rewrite (find_nostack f _ 0%uint63 Pbst) in F0.
    destruct (IMap.find 0%uint63 (s_regs st)) as [q0|] eqn:G0; [|discriminate F0]. change (PrimInt63.eqb 0 1) with false in F0. cbn beta iota in F0. injection F0 as <-.
    unfold region_map in Fg; cbn [rg_cells] in Fg. rewrite IMap.find_map in Fg.
    destruct (IMap.find g (rg_cells q0)) as [gr0|] eqn:Fg0; [|discriminate Fg]. cbn [option_map] in Fg. injection Fg as <-.
    cbn [gran_map g_cells] in Hc. apply in_map_iff in Hc as (c0 & <- & Hc0). cbn [cell_map c_idx c_w] in Hi |- *.
    exact (Ppub q0 g gr0 c0 G0 Fg0 Hc0 i Hi).
  - unfold facts_hold in *. apply Forall_map. eapply Forall_impl; [|exact Pfacts].
    intros x Hx. apply fact_map_holds; [exact VS'| exact Hx].
  - unfold ops_apart in *. eapply Forall_impl; [|exact Papart]. cbn beta. intros o Ho a Ha.
    destruct (Ho a Ha) as [NB PR]. split; [|exact PR]. intros (k1 & r1 & F1 & K1 & R1). apply NB.
    rewrite (find_nostack f _ k1 Pbst) in F1. destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
    injection F1 as <-. rewrite (hiZ_sel E f _ _ VS'), (loZ_sel f) in R1.
    exists k1, q1. auto.
  -
    intros a FA. apply Pcov. revert a FA. apply fx_acc_based. intros a (k1 & r1 & F1 & K1 & R1).
    rewrite (find_nostack f _ k1 Pbst) in F1. destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
    injection F1 as <-. rewrite (hiZ_sel E f _ _ VS'), (loZ_sel f) in R1.
    exists k1, q1. auto.
Qed.

Theorem gcur_sound : contract_sound segs OPS MP PB gcur_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gcur_contract c_apply] in HA. unfold gcur_apply in HA. injection HA as <-.
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply gcur_st_ok; [intros a; apply canon_den| reflexivity| exact HS].
Qed.

End Sound.
End WithPc.
End GCurA.
