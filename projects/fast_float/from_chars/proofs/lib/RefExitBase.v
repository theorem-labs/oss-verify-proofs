(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require DriverCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.MmapSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim.ExitSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Export SumWalkTac DriverCfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP1.
Context {fx : FPState}.
#[using="Type"] Lemma ref_wseg_1c : wseg_ok RSEGS (0x64db8 : word) 202996%nat = true.
Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma store_ok_data : forall m (a : word) n,
  (0x64db8 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x966ac)%Z ->
  store_ok RSEGS m a n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a n Hlo Hhi.
  eapply (store_ok_window RSEGS m (0x64db8 : word) a 202996%nat n 0x64db8 0x966ac);
    [reflexivity | reflexivity | lia | exact ref_wseg_1c | exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_wbytes_hitw : forall m (a v : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn RSEGS (wbytes m a (word_to_le_bytes n v)) a n = Some (word_to_le_bytes n v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a v n Hnw.
  pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes n v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zbv_succ : forall x : Z, (Z_to_bv 64 x + 1)%bv = Z_to_bv 64 (x + 1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1%bv : bv 64)) with 1%Z. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

#[using="Type"] Lemma rdn_total : forall n mem (z : Z), (0 <= z)%Z -> (z + Z.of_nat n <= 2^64)%Z ->
  (forall k, (k < n)%nat -> seg_rom RSEGS (Z_to_bv 64 (z + Z.of_nat k)) <> None) ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 z) n = Some bs /\ length bs = n.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros mem z Hz Hn Hrom; [exists []; split; reflexivity|].
  cbn [rdn].
  assert (Hb : exists b, match mem (Z_to_bv 64 z) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 z) end = Some b).
  { destruct (mem (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity|].
    pose proof (Hrom 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
    destruct (seg_rom RSEGS (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity | exfalso; exact (H0 eq_refl)]. }
  destruct Hb as [b Hb]. rewrite Hb.
  destruct (IH mem (z + 1)%Z ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
  { intros k Hk. replace (z + 1 + Z.of_nat k)%Z with (z + Z.of_nat (S k))%Z by lia. apply Hrom. lia. }
  rewrite zbv_succ, Hbs. exists (b :: bs). split; [reflexivity | cbn [length]; rewrite Hl; reflexivity].
Qed.

#[using="Type"] Lemma rdn_dso : forall mem, exists dbs, rdn RSEGS mem (Z_to_bv 64 0x64db8) 8%nat = Some dbs /\ length dbs = 8%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem. apply rdn_total; [lia | lia |].
  intros k Hk.
  do 8 (destruct k as [|k]; [vm_compute; discriminate|]). lia.
Qed.
End WithFP1.
Ltac rdn_solvew :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b ?n = _ =>
      tryif constr_eq a b then
        (lazymatch n with
         | 8%nat => apply rdn_wbytes_hit8; zsimp; lia
         | _ => apply rdn_wbytes_hitw; zsimp; lia
         end)
      else (rdn_peel1; rdn_solvew)
  | |- _ => rdn_hyp
  end.
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithFP2.
Context {fx : FPState}.
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

(* [comment removed for export] *)
Definition stdio_globals (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x95e63) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x96290) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x96280) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x64ff8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x64f10)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x64f08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x64e20)). (* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

