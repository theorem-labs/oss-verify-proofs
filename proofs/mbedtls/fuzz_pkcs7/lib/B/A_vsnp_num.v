(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge Mem Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SeqExec EnframeArith.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Fixpoint ndig (base : Z) (k : nat) (v : Z) : Z :=
  match k with
  | O => 1
  | S k' => if v <? base then 1 else 1 + ndig base k' (v / base)
  end.

Lemma ndig_ge1 : forall base k v, 1 <= ndig base k v.
Proof. intros base k; induction k as [|k IH]; intros v; cbn; [lia|]. destruct (v <? base); [lia|]. specialize (IH (v / base)). lia. Qed.

Lemma ndig_le : forall base k v, 2 <= base -> 0 <= v < base ^ Z.of_nat k -> ndig base k v <= Z.max 1 (Z.of_nat k).
Proof.
  intros base k; induction k as [|k IH]; intros v Hb Hv; cbn [ndig]; [lia|].
  destruct (Z.ltb_spec0 v base); [lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia.
  assert (H : 0 <= v / base < base ^ Z.of_nat k) by nia.
  specialize (IH (v / base) Hb H).
  destruct k as [|k]; [|lia].
  exfalso. change (base ^ Z.of_nat 0) with (base ^ 0) in H. rewrite Z.pow_0_r in H. nia.
Qed.

(* [comment removed for export] *)

Lemma swrap32_mod64 : forall x d, -2^31 <= x + d < 2^31 -> bv_swrap 32 (x mod 18446744073709551616 + d) = x + d.
Proof.
  intros x d H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (Z.of_N 32) with 32. change (2 ^ (32 - 1)) with (2^31).
  change 18446744073709551616 with (2^32 * 2^32).
  pose proof (Z.div_mod x (2^32 * 2^32) ltac:(lia)) as E. pose proof (Z.mod_pos_bound x (2^32 * 2^32) ltac:(lia)) as B.
  set (q := x / (2^32 * 2^32)) in *. set (r := x mod (2^32 * 2^32)) in *. clearbody q r.
  nia.
Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  End Walk.
