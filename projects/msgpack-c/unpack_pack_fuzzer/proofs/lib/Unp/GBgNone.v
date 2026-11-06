(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GBgNone.

Definition anchor_of (v : sv) : option int :=
  match v with
  | VP k _ => Some k
  | VAlu ALU_SUB (VP k _) _ => Some k
  | _ => None
  end.

Definition forget_bg (r : region) : region := Region (rg_lo r) (rg_hi r) (rg_w r) BGNone (rg_cells r).

Section WithPc.
Variable B_PC : int.
Variable R : r5.

Definition gbgnone_apply (st : sstate) : option (list sstate) :=
  match anchor_of (getr st R) with
  | Some k =>
      if PrimInt63.eqb k 0%uint63 then None else
      match IMap.find k (s_regs st) with
      | Some r => match rg_bg r with
                  | BGUnk => Some [setregs st (IMap.add k (forget_bg r) (s_regs st))]
                  | _ => None
                  end
      | None => None
      end
  | None => None
  end.

Definition gbgnone_contract : contract := Contract B_PC gbgnone_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma region_ok_forget_bg : forall priv E m k r, region_ok segs priv E m k r -> region_ok segs priv E m k (forget_bg r).
Proof.
  intros priv E m k r [Rbst Rrange Rvalid Rcells Rin Rbg].
  constructor; cbn [forget_bg rg_cells rg_lo rg_hi rg_w]; try assumption.
  intros o _ _ _. unfold bg_byte. cbn [forget_bg rg_bg]. exact I.
Qed.

Lemma st_ok_forget_bg : forall E st ms mo k r, PrimInt63.eqb k 0%uint63 = false -> IMap.find k (s_regs st) = Some r ->
  st_ok segs OPS E st ms mo -> st_ok segs OPS E (setregs st (IMap.add k (forget_bg r) (s_regs st))) ms mo.
Proof.
  intros E st ms mo k r K0 F HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  assert (FIND : forall k' r', IMap.find k' (IMap.add k (forget_bg r) (s_regs st)) = Some r' ->
                  exists r0, IMap.find k' (s_regs st) = Some r0 /\ (r' = r0 \/ r' = forget_bg r0)).
  { intros k' r' F'. destruct (PrimInt63.eqb k k') eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k'. rewrite (IMap.find_add_same _ _ _ Pbst) in F'. injection F' as <-. exists r. split; [exact F| right; reflexivity].
    - rewrite (IMap.find_add_other_eqb _ _ _ _ Pbst Q) in F'. exists r'. split; [exact F'| left; reflexivity]. }
  assert (SAME : forall r' r0, r' = r0 \/ r' = forget_bg r0 -> loZ r' = loZ r0 /\ hiZ E r' = hiZ E r0 /\ rg_w r' = rg_w r0 /\ rg_cells r' = rg_cells r0).
  { intros r' r0 [->| ->]; repeat split; reflexivity. }
  assert (BASED : forall a, in_based E (IMap.add k (forget_bg r) (s_regs st)) a -> in_based E (s_regs st) a).
  { intros a (k' & r' & F' & K' & RG). destruct (FIND k' r' F') as (r0 & F0 & EQ). destruct (SAME r' r0 EQ) as (L & H & _ & _).
    exists k', r0. split; [exact F0| split; [exact K'|]]. rewrite <- L, <- H. exact RG. }
  constructor; cbn [setregs s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.add_bst. exact Pbst.
  - intros k' r' F'. destruct (FIND k' r' F') as (r0 & F0 & [->| ->]); [exact (Preg k' r0 F0)| apply region_ok_forget_bg; exact (Preg k' r0 F0)].
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a A.
    destruct (FIND k1 r1 F1) as (r10 & F10 & EQ1). destruct (FIND k2 r2 F2) as (r20 & F20 & EQ2).
    destruct (SAME r1 r10 EQ1) as (L1 & H1 & W1 & _). destruct (SAME r2 r20 EQ2) as (L2 & H2 & W2 & _).
    rewrite L1, H1, L2, H2 in A. rewrite W1, W2 in W. exact (Pdisj k1 r10 k2 r20 F10 F20 NE K1 K2 W a A).
  - intros r0 g gr c F0. assert (Q : PrimInt63.eqb k 0%uint63 = false) by exact K0.
    rewrite (IMap.find_add_other_eqb _ _ _ _ Pbst Q) in F0. exact (Ppub r0 g gr c F0).
  - unfold ops_apart in *. apply Forall_forall. intros o Ho a Ha. pose proof (proj1 (Forall_forall _ _) Papart o Ho a Ha) as [A B].
    split; [| exact B]. intros X. apply A. exact (BASED a X).
  - intros a FA. apply Pcov. destruct FA as [B|Sg]; [left; exact (BASED a B)| right; exact Sg].
Qed.

Theorem gbgnone_sound : contract_sound segs OPS MP PB gbgnone_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gbgnone_contract c_apply] in HA. unfold gbgnone_apply in HA.
  destruct (anchor_of (getr st R)) as [k|]; [|discriminate].
  destruct (PrimInt63.eqb k 0%uint63) eqn:K0; [discriminate|].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:F; [|discriminate].
  destruct (rg_bg r); try discriminate. injection HA as <-.
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl _ E) HMP _).
  apply st_ok_forget_bg; assumption.
Qed.

End Sound.
End WithPc.
End GBgNone.
