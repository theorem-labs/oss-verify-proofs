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

Module GMid.

Definition w3 : w64 := wlit 3%uint63.
Definition B63 : w64 := {| wt := true; wl := 0%uint63 |}.
Definition B60 : w64 := wlit 1152921504606846976%uint63.

Definition mid_of1 (b sh : sv) : option (sv * sv * sv) :=
  match sh with
  | VAlu ALU_SLL (VAlu ALU_SRA (VAlu ALU_SUB e b') (VL s1) as cnt) (VL s2) =>
      if sv_eqb b b' && weqb s1 w3 && weqb s2 w3 then Some (b, e, cnt) else None
  | _ => None
  end.

Definition mid_of (v : sv) : option (sv * sv * sv * bool) :=
  match v with
  | VAlu ALU_ADD x y =>
      match mid_of1 x y with
      | Some r => Some (r, true)
      | None => match mid_of1 y x with Some r => Some (r, false) | None => None end
      end
  | _ => None
  end.

Section WithPc.
Variable M_PC : int.
Variable R : r5.

Definition gmid_apply (st : sstate) : option (list sstate) :=
  let v := getr st R in let fs := s_facts st in
  match mid_of v with
  | Some (b, e, cnt, _) =>
      if negb (r5_eqb R X0)
         && aligned fs b 3%uint63 && aligned fs e 3%uint63
         && match decide_ltu fs e b with Some false => true | _ => false end
         && wltu (snd (sv_bounds fs e)) B63
      then Some [addfact (setr st R e) (FULt cnt (VL B60))] else None
  | None => None
  end.

Definition gmid_contract : contract := Contract M_PC gmid_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma mid_of1_spec : forall b sh b0 e cnt, mid_of1 b sh = Some (b0, e, cnt) ->
  b0 = b /\ cnt = VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3) /\ sh = VAlu ALU_SLL cnt (VL w3).
Proof.
  intros b sh b0 e cnt H. unfold mid_of1 in H.
  destruct sh as [| |o2 y1 y2| | | | | | | |]; try discriminate H. destruct o2; try discriminate H.
  destruct y1 as [| |o3 z1 z2| | | | | | | |]; try discriminate H. destruct o3; try discriminate H.
  destruct z1 as [| |o4 u1 u2| | | | | | | |]; try discriminate H. destruct o4; try discriminate H.
  destruct z2 as [s1| | | | | | | | | |]; try discriminate H.
  destruct y2 as [s2| | | | | | | | | |]; try discriminate H.
  destruct (sv_eqb b u2) eqn:EB; [|discriminate H].
  destruct (weqb s1 w3) eqn:E1; [|discriminate H]. destruct (weqb s2 w3) eqn:E2; [|discriminate H].
  cbn [andb] in H. injection H as <- <- <-.
  apply sv_eqb_eq in EB. subst u2. apply (proj1 (weqb_ok _ _)) in E1. apply (proj1 (weqb_ok _ _)) in E2. subst s1 s2. repeat split; reflexivity.
Qed.

Lemma mid_of_spec : forall v b e cnt o, mid_of v = Some (b, e, cnt, o) ->
  cnt = VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3) /\
  v = (if o then VAlu ALU_ADD b (VAlu ALU_SLL cnt (VL w3)) else VAlu ALU_ADD (VAlu ALU_SLL cnt (VL w3)) b).
Proof.
  intros v b e cnt o H. unfold mid_of in H.
  destruct v as [| |op x y| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct (mid_of1 x y) as [[[b1 e1] c1]|] eqn:M1.
  - injection H as <- <- <- <-. apply mid_of1_spec in M1 as (-> & -> & ->). split; reflexivity.
  - destruct (mid_of1 y x) as [[[b1 e1] c1]|] eqn:M2; [|discriminate H].
    injection H as <- <- <- <-. apply mid_of1_spec in M2 as (-> & -> & ->). split; reflexivity.
Qed.

Lemma mid_core : forall E (b e : sv), let Bz := bv_unsigned (den E b) in let Ez := bv_unsigned (den E e) in
  Bz <= Ez -> Ez < 2 ^ 63 -> Bz mod 8 = 0 -> Ez mod 8 = 0 ->
  bv_unsigned (den E (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3))) = (Ez - Bz) / 8 /\
  den E (VAlu ALU_ADD b (VAlu ALU_SLL (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3)) (VL w3))) = den E e.
Proof.
  intros E b e Bz Ez LE HI MB ME.
  pose proof (bv_unsigned_in_range _ (den E b)) as RB. rewrite bv_modulus_64 in RB. fold Bz in RB. unfold two64 in RB.
  assert (DM : (Ez - Bz) mod 8 = 0) by (rewrite Zminus_mod, ME, MB; reflexivity).
  pose proof (Z_div_mod_eq_full (Ez - Bz) 8) as DE. rewrite DM in DE.
  assert (Q0 : 0 <= (Ez - Bz) / 8) by (apply Z.div_pos; lia).
  assert (Q1 : (Ez - Bz) / 8 < 2 ^ 60) by (apply Z.div_lt_upper_bound; lia).

  assert (SUBu : bv_unsigned (den E (VAlu ALU_SUB e b)) = Ez - Bz).
  { change (den E (VAlu ALU_SUB e b)) with (alu64 ALU_SUB (den E e) (den E b)). cbn [alu64 alu].
    rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64. fold Ez Bz. unfold two64. rewrite Z.mod_small by lia. reflexivity. }

  assert (SH3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3) by (rewrite shamt6_bv; reflexivity).
  assert (SRAu : bv_unsigned (den E (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3))) = (Ez - Bz) / 8).
  { change (den E (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3))) with (alu64 ALU_SRA (den E (VAlu ALU_SUB e b)) (den E (VL w3))).
    cbn [alu64 alu]. change (den E (VL w3)) with (wbv w3). rewrite bv_ashiftr_unsigned, SH3.
    rewrite (bv_signed_small63 (den E (VAlu ALU_SUB e b))) by (rewrite SUBu; unfold two63; lia).
    rewrite SUBu, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold two64. lia. }
  split; [exact SRAu|].
  apply bv_eq.
  change (den E (VAlu ALU_ADD b (VAlu ALU_SLL (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3)) (VL w3))))
    with (alu64 ALU_ADD (den E b) (alu64 ALU_SLL (den E (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3))) (den E (VL w3)))).
  cbn [alu64 alu]. change (den E (VL w3)) with (wbv w3). rewrite bv_add_unsigned, bv_shiftl_unsigned, SH3, SRAu, Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold bv_wrap. rewrite bv_modulus_64. fold Bz Ez. unfold two64.
  rewrite (Z.mod_small ((Ez - Bz) / 8 * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Theorem gmid_sound : contract_sound segs OPS MP PB gmid_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gmid_contract c_apply] in HA. unfold gmid_apply in HA.
  destruct (mid_of (getr st R)) as [[[[b e] cnt] o]|] eqn:MO; [|discriminate].
  destruct (negb (r5_eqb R X0)) eqn:RX; [|discriminate].
  destruct (aligned (s_facts st) b 3%uint63) eqn:AB; [|discriminate].
  destruct (aligned (s_facts st) e 3%uint63) eqn:AE; [|discriminate].
  destruct (decide_ltu (s_facts st) e b) as [[|]|] eqn:DL; try discriminate.
  destruct (wltu (snd (sv_bounds (s_facts st) e)) B63) eqn:HB; [|discriminate].
  cbn [andb] in HA. injection HA as <-.
  apply mid_of_spec in MO as [-> MV].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  pose proof (aligned_sound E (s_facts st) FH b 3%uint63 AB ltac:(change (to_Z 3%uint63) with 3; lia)) as MB.
  pose proof (aligned_sound E (s_facts st) FH e 3%uint63 AE ltac:(change (to_Z 3%uint63) with 3; lia)) as ME.
  change (to_Z 3%uint63) with 3 in MB, ME. change (2 ^ 3) with 8 in MB, ME.
  pose proof (decide_ltu_sound E (s_facts st) FH e b false DL) as LE. apply (proj1 (ltu_iff _ _ false)) in LE.
  pose proof (sv_bounds_sound E (s_facts st) FH e) as I0. unfold inb in I0.
  rewrite wltu_w2Z in HB. apply Z.ltb_lt in HB. replace (w2Z B63) with (2 ^ 63) in HB by (vm_compute; reflexivity).
  destruct (mid_core E b e LE ltac:(lia) MB ME) as [CNT MID].
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply addfact_sound.
  -
    apply setreg_sound; [exact HS| |].
    + intros EQ. rewrite EQ in RX. cbn in RX. discriminate RX.
    + rewrite MV. destruct o; [exact MID|].
      rewrite <- MID. apply bv_eq.
      change (den E (VAlu ALU_ADD (VAlu ALU_SLL (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3)) (VL w3)) b))
        with (alu64 ALU_ADD (den E (VAlu ALU_SLL (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3)) (VL w3))) (den E b)).
      change (den E (VAlu ALU_ADD b (VAlu ALU_SLL (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3)) (VL w3))))
        with (alu64 ALU_ADD (den E b) (den E (VAlu ALU_SLL (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3)) (VL w3)))).
      cbn [alu64 alu]. rewrite !bv_add_unsigned. f_equal. lia.
  - cbn [fact_holds]. rewrite CNT, den_VL. change (w2Z B60) with (2 ^ 60).
    pose proof (bv_unsigned_in_range _ (den E b)) as RB. rewrite bv_modulus_64 in RB. unfold two64 in RB.
    apply Z.div_lt_upper_bound; lia.
Qed.

End Sound.
End WithPc.
End GMid.
