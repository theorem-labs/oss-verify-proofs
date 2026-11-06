(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module CapLen.

Definition cap_sub (kB : int) (cap : sv) : sv := VAlu ALU_SUB cap (VP kB wzero).
Definition cap_len (kB : int) (cap : sv) : option sv :=
  match cap with
  | VP k off => if PrimInt63.eqb k kB && negb (wt off) && PrimInt63.ltb 0%uint63 (wl off) then Some (VL off) else Some (cap_sub kB cap)
  | VAlu ALU_ADD (VP k1 o1) (VP k2 o2) =>
      if weqb o1 wzero && weqb o2 wzero then
        (if PrimInt63.eqb k1 kB then Some (VP k2 wzero) else if PrimInt63.eqb k2 kB then Some (VP k1 wzero) else Some (cap_sub kB cap))
      else Some (cap_sub kB cap)
  | _ => Some (cap_sub kB cap)
  end.

Definition empty_region (len : sv) : region := Region 0%uint63 len true BGNone IMap.empty.

Lemma cap_len_below : forall n kB cap len, cap_len kB cap = Some len -> sv_vars_below n cap = true ->
  PrimInt63.ltb kB n = true -> sv_vars_below n len = true.
Proof.
  intros n kB cap len H VB KB.
  assert (SUBV : sv_vars_below n (cap_sub kB cap) = true) by (unfold cap_sub; cbn [sv_vars_below]; rewrite VB, KB; reflexivity).
  unfold cap_len in H.
  destruct cap as [|k off|op a1 a2| | | | | | | |]; try (injection H as <-; exact SUBV).
  - destruct (PrimInt63.eqb k kB && negb (wt off) && PrimInt63.ltb 0%uint63 (wl off)); injection H as <-; [reflexivity| exact SUBV].
  - destruct op; try (injection H as <-; exact SUBV).
    destruct a1 as [|k1 o1| | | | | | | | |]; try (injection H as <-; exact SUBV).
    destruct a2 as [|k2 o2| | | | | | | | |]; try (injection H as <-; exact SUBV).
    destruct (weqb o1 wzero && weqb o2 wzero); [|injection H as <-; exact SUBV].
    pose proof VB as VB'. cbn [sv_vars_below] in VB'. apply andb_prop in VB' as [V1 V2].
    destruct (PrimInt63.eqb k1 kB); [injection H as <-; exact V2|].
    destruct (PrimInt63.eqb k2 kB); injection H as <-; [exact V1| exact SUBV].
Qed.

Lemma mod_add_cancel : forall B X L, 0 <= B -> 0 <= X < two64 -> 0 <= L -> B + L < two64 -> (B + X) mod two64 = B + L -> X = L.
Proof.
  intros B X L HB HX HL HBL H. pose proof two64_eq as T. set (M := two64) in *. clearbody M.
  destruct (Z_lt_ge_dec (B + X) M) as [Lt|Ge].
  - rewrite Z.mod_small in H by lia. lia.
  - exfalso. assert (E : (B + X) mod M = B + X - M).
    { symmetry. apply (Z.mod_unique_pos _ _ 1); lia. }
    rewrite E in H. lia.
Qed.

Lemma cap_sub_sound : forall E kB cap bytes,
  bv_unsigned (den E cap) = bv_unsigned (ev E kB) + bytes -> 0 <= bytes ->
  bv_unsigned (ev E kB) + bytes <= 4611686018427387904 ->
  bv_unsigned (den E (cap_sub kB cap)) = bytes.
Proof.
  intros E kB cap bytes D HB HC. unfold cap_sub.
  pose proof (bv_unsigned_in_range 64 (ev E kB)) as RB. rewrite bv_modulus_64 in RB.
  pose proof two64_eq as T64.
  change (den E (VAlu ALU_SUB cap (VP kB wzero))) with (bv_sub (den E cap) (den E (VP kB wzero))).
  rewrite bv_sub_unsigned, (den_VP0 E kB wzero (weqb_refl _)), D. unfold bv_wrap. rewrite bv_modulus_64.
  replace (bv_unsigned (ev E kB) + bytes - bv_unsigned (ev E kB)) with bytes by lia.
  apply Z.mod_small. lia.
Qed.

Lemma cap_len_sound : forall E kB cap len bytes,
  cap_len kB cap = Some len ->
  bv_unsigned (den E cap) = bv_unsigned (ev E kB) + bytes -> 0 <= bytes ->
  bv_unsigned (ev E kB) + bytes <= 4611686018427387904 ->
  bv_unsigned (den E len) = bytes.
Proof.
  intros E kB cap len bytes H D HB HC.
  pose proof (cap_sub_sound E kB cap bytes D HB HC) as SUBS.
  unfold cap_len in H.
  pose proof (bv_unsigned_in_range 64 (ev E kB)) as RB. rewrite bv_modulus_64 in RB.
  pose proof two64_eq as T64.
  destruct cap as [|k off|op a1 a2| | | | | | | |]; try (injection H as <-; exact SUBS).
  - destruct (PrimInt63.eqb k kB && negb (wt off) && PrimInt63.ltb 0%uint63 (wl off)) eqn:C; [|injection H as <-; exact SUBS]. injection H as <-.
    apply andb_prop in C as [C LT]. apply andb_prop in C as [K TP]. apply Uint63.eqb_correct in K. subst k.
    apply negb_true_iff in TP.
    assert (OFF : w2Zs off = to_Z (wl off)) by (rewrite w2Zs_eq; unfold w2Z; rewrite TP; lia).
    pose proof (int_range (wl off)) as RO.
    rewrite den_VP, OFF in D. rewrite Z.mod_small in D by (unfold two63 in *; lia).
    rewrite den_VL. unfold w2Z. rewrite TP. lia.
  - destruct op; try (injection H as <-; exact SUBS).
    destruct a1 as [|k1 o1| | | | | | | | |]; try (injection H as <-; exact SUBS).
    destruct a2 as [|k2 o2| | | | | | | | |]; try (injection H as <-; exact SUBS).
    destruct (weqb o1 wzero && weqb o2 wzero) eqn:OO; [|injection H as <-; exact SUBS]. apply andb_prop in OO as [O1 O2].
    assert (DC : (bv_unsigned (ev E k1) + bv_unsigned (ev E k2)) mod two64 = bv_unsigned (ev E kB) + bytes).
    { rewrite <- D. change (den E (VAlu ALU_ADD (VP k1 o1) (VP k2 o2))) with (bv_add (den E (VP k1 o1)) (den E (VP k2 o2))).
      rewrite bv_add_unsigned, (den_VP0 E k1 o1 O1), (den_VP0 E k2 o2 O2). unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
    pose proof (bv_unsigned_in_range 64 (ev E k1)) as R1. rewrite bv_modulus_64 in R1.
    pose proof (bv_unsigned_in_range 64 (ev E k2)) as R2. rewrite bv_modulus_64 in R2.
    destruct (PrimInt63.eqb k1 kB) eqn:K1.
    + injection H as <-. apply Uint63.eqb_correct in K1. subst k1. rewrite (den_VP0 E k2 wzero (weqb_refl _)).
      apply (mod_add_cancel (bv_unsigned (ev E kB))); lia.
    + destruct (PrimInt63.eqb k2 kB) eqn:K2; [|injection H as <-; exact SUBS]. injection H as <-. apply Uint63.eqb_correct in K2. subst k2.
      rewrite (den_VP0 E k1 wzero (weqb_refl _)). rewrite Z.add_comm in DC.
      apply (mod_add_cancel (bv_unsigned (ev E kB))); lia.
Qed.

Definition VD_MAXZ : Z := 288230376151711744.
Definition VD_MAX : w64 := wlit 288230376151711744%uint63.
Definition vd_facts (b e : sv) (j : int) (s : int) : list fact :=
  [FEq e (VAlu ALU_ADD b (VMd M_MUL (VP j wzero) (VL (wlit s)))); FULe (VP j wzero) (VL VD_MAX); FULe b e].

Lemma vd_facts_sound : forall E b e j s B cnt,
  bv_unsigned (den E b) = B -> bv_unsigned (den E e) = B + to_Z s * cnt ->
  0 <= cnt <= VD_MAXZ -> 0 <= B -> B + to_Z s * cnt < two64 ->
  ev E j = Z_to_bv 64 cnt ->
  Forall (fact_holds E) (vd_facts b e j s).
Proof.
  intros E b e j s B cnt HB HE HC HB0 HW EJ. unfold vd_facts.
  pose proof two64_eq as T64. pose proof (int_range s) as RS.
  assert (CJ : bv_unsigned (ev E j) = cnt).
  { rewrite EJ, Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold VD_MAXZ in HC. lia. }
  assert (SC : 0 <= to_Z s * cnt) by (apply Z.mul_nonneg_nonneg; lia).
  constructor; [| constructor; [| constructor; [| constructor]]].
  - cbn [fact_holds]. apply bv_eq. rewrite HE.
    change (den E (VAlu ALU_ADD b (VMd M_MUL (VP j wzero) (VL (wlit s))))) with (bv_add (den E b) (bv_mul (den E (VP j wzero)) (den E (VL (wlit s))))).
    rewrite bv_add_unsigned, bv_mul_unsigned, HB, (den_VP0 E j wzero (weqb_refl _)), CJ, den_VL, wlit_ok.
    unfold bv_wrap. rewrite bv_modulus_64.
    rewrite (Z.mod_small (cnt * to_Z s)) by lia. rewrite Z.mod_small by lia. lia.
  - cbn [fact_holds]. rewrite (den_VP0 E j wzero (weqb_refl _)), CJ, den_VL. unfold VD_MAX. rewrite wlit_ok.
    change (to_Z 288230376151711744%uint63) with 288230376151711744. unfold VD_MAXZ in HC. lia.
  - cbn [fact_holds]. rewrite HB, HE. lia.
Qed.

End CapLen.
