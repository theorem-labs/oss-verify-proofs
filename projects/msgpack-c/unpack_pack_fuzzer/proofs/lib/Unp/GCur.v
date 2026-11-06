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

Module GCur.

Fixpoint flat (v : sv) (acc : list sv) : list sv :=
  match v with
  | VAlu ALU_ADD a b => flat a (flat b acc)
  | _ => v :: acc
  end.

Definition ro_anchor (R : IMap.t region) (v : sv) : bool :=
  match v with
  | VP k _ => negb (PrimInt63.eqb k 0%uint63) && negb (PrimInt63.eqb k 1%uint63)
              && match IMap.find k R with Some r => negb (rg_w r) | None => false end
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

Definition gcur_apply (st : sstate) : option (list sstate) :=
  let f := canon (s_regs st) in
  Some [SS (s_pc st) (rf_map f (s_rf st)) (s_ff st) (s_resv st) (IMap.map (region_map f) (s_regs st))
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
  st_ok segs OPS E (SS (s_pc st) (rf_map f (s_rf st)) (s_ff st) (s_resv st) (IMap.map (region_map f) (s_regs st))
                       (List.map (fact_map f) (s_facts st)) (s_ops st) (s_priv st) (s_next st)) ms model.
Proof.
  intros E st ms model f VS' FZ HS.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - rewrite rf_get_map, Px0. exact FZ.
  - intros r. rewrite rf_get_map, VS'. exact (Pregs r).
  - apply IMap.bst_map. exact Pbst.
  - intros k r F. rewrite IMap.find_map in F. destruct (IMap.find k (s_regs st)) as [r0|] eqn:F0; [|discriminate F].
    cbn [option_map] in F. injection F as <-. apply region_ok_map; [exact VS'|]. exact (Preg k r0 F0).
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a. rewrite IMap.find_map in F1, F2.
    destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
    destruct (IMap.find k2 (s_regs st)) as [q2|] eqn:G2; [|discriminate F2].
    cbn [option_map] in F1, F2. injection F1 as <-. injection F2 as <-.
    rewrite !(hiZ_map _ E VS'), !(loZ_map _). apply (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2). exact W.
  - intros r0 g gr c F0 Fg Hc i Hi. rewrite IMap.find_map in F0.
    destruct (IMap.find 0%uint63 (s_regs st)) as [q0|] eqn:G0; [|discriminate F0]. cbn [option_map] in F0. injection F0 as <-.
    unfold region_map in Fg; cbn [rg_cells] in Fg. rewrite IMap.find_map in Fg.
    destruct (IMap.find g (rg_cells q0)) as [gr0|] eqn:Fg0; [|discriminate Fg]. cbn [option_map] in Fg. injection Fg as <-.
    cbn [gran_map g_cells] in Hc. apply in_map_iff in Hc as (c0 & <- & Hc0). cbn [cell_map c_idx c_w] in Hi |- *.
    exact (Ppub q0 g gr0 c0 G0 Fg0 Hc0 i Hi).
  - unfold facts_hold in *. apply Forall_map. eapply Forall_impl; [|exact Pfacts].
    intros x Hx. apply fact_map_holds; [exact VS'| exact Hx].
  - unfold ops_apart in *. eapply Forall_impl; [|exact Papart]. cbn beta. intros o Ho a Ha.
    destruct (Ho a Ha) as [NB PR]. split; [|exact PR]. intros (k1 & r1 & F1 & K1 & R1). apply NB.
    rewrite IMap.find_map in F1. destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
    cbn [option_map] in F1. injection F1 as <-. rewrite (hiZ_map _ E VS'), (loZ_map _) in R1.
    exists k1, q1. auto.
  -
    intros a FA. apply Pcov. revert a FA. apply fx_acc_based. intros a (k1 & r1 & F1 & K1 & R1).
    rewrite IMap.find_map in F1. destruct (IMap.find k1 (s_regs st)) as [q1|] eqn:G1; [|discriminate F1].
    cbn [option_map] in F1. injection F1 as <-. rewrite (hiZ_map _ E VS'), (loZ_map _) in R1.
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
End GCur.
