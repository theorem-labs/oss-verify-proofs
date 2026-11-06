(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound KnownT.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.

Module GBndA.

Definition ybound (fs : list fact) (y : sv) : w64 :=
  let h := snd (sv_bounds fs y) in
  match y with
  | VAlu ALU_SUB a b => match KnownT.KnownT.decide_ltu_tt fs a b with Some false => wminu h (snd (sv_bounds fs a)) | _ => h end
  | _ => h
  end.

Lemma ybound_sound : forall E fs, facts_hold E fs -> forall y, bv_unsigned (den E y) <= w2Z (ybound fs y).
Proof.
  intros E fs FH y. pose proof (sv_bounds_sound E fs FH y) as I0. unfold inb in I0. unfold ybound.
  destruct y; try lia.
  match goal with |- context [match ?o with ALU_SUB => _ | _ => _ end] => destruct o; try lia end.
  match goal with |- context [KnownT.KnownT.decide_ltu_tt fs ?a ?b] => rename a into y1; rename b into y2 end.
  destruct (KnownT.KnownT.decide_ltu_tt fs y1 y2) as [[|]|] eqn:D; try lia.
  pose proof (KnownT.KnownT.decide_ltu_tt_sound E fs FH y1 y2 false D) as L.
  pose proof (sv_bounds_sound E fs FH y1) as I1. unfold inb in I1.
  unfold wminu. rewrite wltu_w2Z.
  apply (proj1 (ltu_iff _ _ false)) in L.
  assert (S : bv_unsigned (den E (VAlu ALU_SUB y1 y2)) <= bv_unsigned (den E y1)).
  { change (den E (VAlu ALU_SUB y1 y2)) with (alu64 ALU_SUB (den E y1) (den E y2)). cbn [alu64 alu].
    rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
    pose proof (bv_unsigned_in_range _ (den E y1)) as R1. pose proof (bv_unsigned_in_range _ (den E y2)) as R2.
    rewrite bv_modulus_64 in R1, R2. rewrite Z.mod_small by lia. lia. }
  destruct (Z.ltb_spec (w2Z (snd (sv_bounds fs (VAlu ALU_SUB y1 y2)))) (w2Z (snd (sv_bounds fs y1)))); lia.
Qed.

Fixpoint via_hi (fs0 fs : list fact) (v : sv) (best : w64) : w64 :=
  match fs with
  | [] => best
  | f :: fs' =>
      via_hi fs0 fs' v
        (match f with
         | FULe x y | FULt x y => if sv_eqb x v then wminu best (ybound fs0 y) else best
         | _ => best
         end)
  end.

Lemma via_hi_sound : forall E fs0, facts_hold E fs0 -> forall fs v best,
  Forall (fact_holds E) fs -> bv_unsigned (den E v) <= w2Z best -> bv_unsigned (den E v) <= w2Z (via_hi fs0 fs v best).
Proof.
  intros E fs0 FH0 fs. induction fs as [|f fs IH]; intros v best FH B; cbn [via_hi]; [exact B|].
  inversion FH as [|? ? Hf FH']; subst. apply IH; [exact FH'|].
  destruct f; try exact B.
  - destruct (sv_eqb a v) eqn:EQ; [|exact B]. apply sv_eqb_eq in EQ. subst a. cbn [fact_holds] in Hf.
    pose proof (ybound_sound E fs0 FH0 b) as I0.
    unfold wminu. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z best) (w2Z (ybound fs0 b))); lia.
  - destruct (sv_eqb a v) eqn:EQ; [|exact B]. apply sv_eqb_eq in EQ. subst a. cbn [fact_holds] in Hf.
    pose proof (ybound_sound E fs0 FH0 b) as I0.
    unfold wminu. rewrite wltu_w2Z. destruct (Z.ltb_spec (w2Z best) (w2Z (ybound fs0 b))); lia.
Qed.

Section WithPc.
Variable B_PC : int.
Variable R : r5.

Definition gbnd_apply (st : sstate) : option (list sstate) :=
  let v := getr st R in let fs := s_facts st in
  let cur := snd (sv_bounds fs v) in
  let h := via_hi fs fs v cur in
  if wltu h cur then Some [addfact st (FULe v (VL h))] else None.

Definition gbnd_contract : contract := Contract B_PC gbnd_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem gbnd_sound : contract_sound segs OPS MP PB gbnd_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gbnd_contract c_apply] in HA. unfold gbnd_apply in HA.
  destruct (wltu _ _) eqn:LT; [|discriminate]. injection HA as <-.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply addfact_sound; [exact HS|]. cbn [fact_holds den]. rewrite wbv_unsigned.
  apply (via_hi_sound E (s_facts st) FH (s_facts st) (getr st R) _ FH).
  pose proof (sv_bounds_sound E (s_facts st) FH (getr st R)) as I0. unfold inb in I0. lia.
Qed.

End Sound.
End WithPc.
End GBndA.
