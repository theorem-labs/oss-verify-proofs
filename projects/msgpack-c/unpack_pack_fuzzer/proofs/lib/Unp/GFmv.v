(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem StepSoundAlu PlanSound Acc StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS CtrLib.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GFmv.
Section WithSegs.
Variable segs : list Segment.

Definition fsgnj_at (pc : int) : option (ffmt * r5 * r5) :=
  match fetch_word segs (Z_to_bv 64 (to_Z pc)) with
  | Some w =>
      if is_ecall w then None else
      match decode_any w with
      | Some (Fsgnj F_SGNJ fmt rd rs1 rs2, z) =>
          if Z.eqb z 4 then
            match r5_of_reg rd, r5_of_reg rs1, r5_of_reg rs2 with
            | Some d, Some s1, Some s2 => if r5_eqb s1 s2 then Some (fmt, d, s1) else None
            | _, _, _ => None
            end
          else None
      | _ => None
      end
  | None => None
  end.

Definition boxed_form (v : sv) : bool :=
  match v with
  | VF1 F1_NANBOX _ => true
  | VF1 (F1_FCVT _ FMT_S _) _ => true
  | _ => false
  end.

Definition gfmv_apply (st : sstate) : option (list sstate) :=
  if PrimInt63.ltb (s_pc st) bit62i then
    match fsgnj_at (s_pc st) with
    | Some (fmt, rd, rs) =>
        if match fmt with FMT_D => true | FMT_S => boxed_form (getf st rs) end
        then Some [setpc (setf st rd (getf st rs)) (pc4 st)]
        else None
    | None => None
    end
  else None.
Definition gfmv_contract (pc : int) : contract := Contract pc gfmv_apply.
End WithSegs.

Lemma testbit_small_high : forall u n i, 0 <= u < 2 ^ n -> 0 <= n <= i -> Z.testbit u i = false.
Proof.
  intros u n i Hu Hi. rewrite <- (Z.mod_small u (2 ^ n)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma testbit_b2z : forall (b : bool) i, 0 <= i -> Z.testbit (if b then 1 else 0) i = (b && (i =? 0))%bool.
Proof.
  intros b i Hi. destruct b.
  - change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 0 i), (Z.eqb_spec i 0); cbn; congruence.
  - rewrite Z.testbit_0_l. reflexivity.
Qed.

Lemma sgnj_self : forall (n : N) (a : bv n), (0 < n)%N -> sgnj_val F_SGNJ a a = a.
Proof.
  intros n a Hn. apply bv_eq. unfold sgnj_val, bit.
  rewrite bv_concat_unsigned', bv_extract_0_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  unfold bv_modulus.
  pose proof (bv_unsigned_in_range n a) as R. unfold bv_modulus in R.
  set (u := bv_unsigned a) in *. set (m := Z.of_N n) in *.
  assert (Hm : 0 < m) by lia.
  replace (Z.of_N (n - 1)) with (m - 1) by lia. replace (Z.of_N 1) with 1 by lia.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i m) as [LT|GE].
  2:{ rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (testbit_small_high u m i); lia. }
  rewrite (Z.mod_pow2_bits_low _ m i) by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z_lt_le_dec i (m - 1)) as [LT1|GE1].
  - rewrite (Z.mod_pow2_bits_low u (m - 1) i) by lia. rewrite (Z.testbit_neg_r _ (i - (m - 1))) by lia. reflexivity.
  - assert (i = m - 1) by lia. subst i. rewrite (Z.mod_pow2_bits_high u (m - 1) (m - 1)) by lia. rewrite Z.sub_diag, orb_false_r.
    rewrite (Z.mod_small _ (2 ^ 1)) by (destruct (Z.testbit u (m - 1)); cbn; lia).
    rewrite testbit_b2z by lia. rewrite andb_true_r. reflexivity.
Qed.

Lemma nan_box_high : forall (y : bv 32), bv_unsigned (bv_extract 32 32 (nan_box y)) = Z.ones 32.
Proof.
  intros y. unfold nan_box. rewrite bv_extract_unsigned, bv_concat_unsigned', Z_to_bv_unsigned. unfold bv_wrap.
  unfold bv_modulus. pose proof (bv_unsigned_in_range 32 y) as R. unfold bv_modulus in R.
  set (u := bv_unsigned y) in *. change (Z.of_N 32) with 32 in *. change (Z.of_N 64) with 64.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i 32) as [LT|GE].
  2:{ rewrite (Z.mod_pow2_bits_high _ 32 i), Z.ones_spec_high by lia. reflexivity. }
  rewrite (Z.mod_pow2_bits_low _ 32 i), Z.ones_spec_low by lia. rewrite Z.shiftr_spec by lia.
  rewrite (Z.mod_pow2_bits_low _ 64 (i + 32)) by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
  replace (i + 32 - 32) with i by lia.
  rewrite (Z.mod_pow2_bits_low (-1) 32 i) by lia. rewrite Z.bits_m1 by lia. reflexivity.
Qed.

Lemma nan_box_low : forall (y : bv 32), low32 (nan_box y) = y.
Proof.
  intros y. apply bv_eq. unfold low32, nan_box. rewrite bv_extract_0_unsigned, bv_concat_unsigned', Z_to_bv_unsigned. unfold bv_wrap.
  unfold bv_modulus. pose proof (bv_unsigned_in_range 32 y) as R. unfold bv_modulus in R.
  set (u := bv_unsigned y) in *. change (Z.of_N 32) with 32 in *. change (Z.of_N 64) with 64.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i 32) as [LT|GE].
  2:{ rewrite (Z.mod_pow2_bits_high _ 32 i) by lia. symmetry. apply (testbit_small_high u 32 i); lia. }
  rewrite (Z.mod_pow2_bits_low _ 32 i) by lia. rewrite (Z.mod_pow2_bits_low _ 64 i) by lia.
  rewrite Z.lor_spec, Z.shiftl_spec by lia.
  rewrite (Z.testbit_neg_r _ (i - 32)) by lia. reflexivity.
Qed.

Lemma unbox_nan_box : forall (y : bv 32), unbox_s (nan_box y) = y.
Proof.
  intros y. unfold unbox_s. rewrite nan_box_high, Z.eqb_refl. apply nan_box_low.
Qed.

Lemma fmv_s_boxed : forall (y : bv 32), nan_box (sgnj_val F_SGNJ (unbox_s (nan_box y)) (unbox_s (nan_box y))) = nan_box y.
Proof. intros y. rewrite unbox_nan_box, sgnj_self; [reflexivity| reflexivity]. Qed.

Lemma boxed_form_den : forall E v, boxed_form v = true -> exists y, den E v = nan_box y.
Proof.
  intros E v H. destruct v; try discriminate H. cbn [boxed_form] in H.
  destruct op as [| |sf df md]; try discriminate H.
  - eexists. cbn [den fop1_sem]. reflexivity.
  - destruct df; try discriminate H. eexists. cbn [den fop1_sem]. reflexivity.
Qed.

Lemma fsgnj_at_spec : forall segs pc fmt rd rs, fsgnj_at segs pc = Some (fmt, rd, rs) ->
  exists w rd' rs1' rs2', fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\ is_ecall w = false /\
    decode_any w = Some (Fsgnj F_SGNJ fmt rd' rs1' rs2', 4%Z) /\
    r5_of_reg rd' = Some rd /\ r5_of_reg rs1' = Some rs /\ r5_of_reg rs2' = Some rs.
Proof.
  intros segs pc fmt rd rs H. unfold fsgnj_at in H.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:F; [|discriminate].
  destruct (is_ecall w) eqn:EC; [discriminate|].
  destruct (decode_any w) as [[i z]|] eqn:D; [|discriminate].
  destruct i; try discriminate. destruct op; try discriminate.
  destruct (Z.eqb_spec z 4); [|discriminate]. subst z.
  destruct (r5_of_reg rd0) as [d|] eqn:RD; [|discriminate].
  destruct (r5_of_reg rs1) as [s1|] eqn:R1; [|discriminate].
  destruct (r5_of_reg rs2) as [s2|] eqn:R2; [|discriminate].
  destruct (r5_eqb s1 s2) eqn:EQ; [|discriminate]. apply r5_eqb_spec in EQ. subst s2.
  injection H as <- <- <-. exists w, rd0, rs1, rs2. auto 10.
Qed.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma gfmv_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> gfmv_apply segs st = Some sts ->
  exists st' ms', sts = [st'] /\ mi_account_step segs ms model = MachineOk (ms', model) /\ st_ok segs OPS E st' ms' model.
Proof.
  intros E st ms model sts HS AP. unfold gfmv_apply in AP.
  destruct (PrimInt63.ltb (s_pc st) bit62i) eqn:PCB; [|discriminate].
  destruct (fsgnj_at segs (s_pc st)) as [[[fmt rd] rs]|] eqn:FA; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end. injection AP as <-.
  destruct (fsgnj_at_spec segs (s_pc st) fmt rd rs FA) as (w & rd' & rs1' & rs2' & FW & EC & DEC & RD & RS1 & RS2).
  pose proof (reg_of_r5_of_reg _ _ RD) as HRD. pose proof (reg_of_r5_of_reg _ _ RS1) as HRS1. pose proof (reg_of_r5_of_reg _ _ RS2) as HRS2.
  pose proof FW as FW'. rewrite <- (so_pc _ _ _ _ _ _ HS) in FW'.

  assert (VAL : exists wv, den E (getf st rs) = wv /\
            Sem.exec (Z_to_bv 64 4) (Fsgnj F_SGNJ fmt rd' rs1' rs2') (core_of ms)
            = EDone (fset (reg_of_r5 rd) wv (with_pc (Sem.c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms)))).
  { rewrite <- HRD, <- HRS1, <- HRS2. cbn [Sem.exec].
    pose proof (StepA.getf_den segs OPS E st ms model rs HS) as GD.
    destruct fmt.
    -
      destruct (boxed_form_den E (getf st rs) C) as [y Hy].
      exists (den E (getf st rs)). split; [reflexivity|]. rewrite <- GD, Hy, fmv_s_boxed. reflexivity.
    - exists (den E (getf st rs)). split; [reflexivity|]. rewrite <- GD, sgnj_self; [reflexivity| reflexivity]. }
  destruct VAL as (wv & DV & EX).
  destruct (StepA.case_freg segs OPS E st ms model rd (getf st rs) wv HS PCB DV) as (c & m' & IE & HS').
  rewrite <- EX in IE.
  assert (NM : forall cc a n, ~ Acc.mem_acc (Fsgnj F_SGNJ fmt rd' rs1' rs2') cc a n) by (intros cc a n Hc; exact Hc).
  assert (STEP : RiscvSemantics.step segs ms = MachineOk (ms_upd ms c m')).
  { rewrite (step_exec segs ms w _ FW' EC DEC), IE. reflexivity. }
  exists (setpc (setf st rd (getf st rs)) (pc4 st)), (ms_upd ms c m'). split; [reflexivity|]. split; [|exact HS'].
  exact (Acc.account_step_noacc segs ms w _ (ms_upd ms c m') model FW' EC DEC NM STEP).
Qed.

Theorem gfmv_sound : forall pc, contract_sound segs OPS MP PB (gfmv_contract segs pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gfmv_contract c_apply] in HAP.
  destruct (gfmv_sound_main E st ms model sts HS HAP) as (st' & ms' & -> & STEP & HS').
  apply (rz_astep segs ms model ms' model K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  apply (Hk st' (or_introl eq_refl) E ms' model); [| exact HMP| exact HS'].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.
End Sound.
End GFmv.
