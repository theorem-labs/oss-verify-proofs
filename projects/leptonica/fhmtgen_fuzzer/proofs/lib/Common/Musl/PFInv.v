(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFCore.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition low_frame (sp0 : Z) (m m' : word -> option byte) : Prop :=
  exists rs, frame_mod m m' rs /\ (forall x : word, sp0 - 2768 <= bv_unsigned x -> outside x rs).
End GD_1.

Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma low_frame_wb : forall sp0 m (a : Z) bs,
  0 <= a -> a + Z.of_nat (length bs) <= sp0 - 2768 -> sp0 < 2 ^ 64 ->
  low_frame sp0 m (wbytes m (Z_to_bv 64 a) bs).
Proof.
  intros sp0 m a bs Ha Hhi Hsp. exists [(Z_to_bv 64 a, Z.of_nat (length bs))]. split.
  - apply frame_mod_wbytes. rewrite u_Z2bv by lia. lia.
  - intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_Z2bv by lia. lia.
Qed.
End VP1.

Section VP2.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma low_frame_refl : forall sp0 m, low_frame sp0 m m.
Proof. intros. exists []. split; [apply frame_mod_refl | intros; exact I]. Qed.

Lemma low_frame_trans : forall sp0 m1 m2 m3,
  low_frame sp0 m1 m2 -> low_frame sp0 m2 m3 -> low_frame sp0 m1 m3.
Proof.
  intros sp0 m1 m2 m3 (rs1 & F1 & O1) (rs2 & F2 & O2). exists (rs1 ++ rs2). split.
  - eapply frame_mod_trans; eassumption.
  - intros x Hx. apply outside_app. split; auto.
Qed.
End VP2.

Section VP3.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma low_frame_sub : forall sp0 m m' rs,
  frame_mod m m' rs -> (forall x : word, sp0 - 2768 <= bv_unsigned x -> outside x rs) -> low_frame sp0 m m'.
Proof. intros. exists rs. auto. Qed.

Lemma low_rdn : forall sp0 m m' (a : Z) (n : nat),
  low_frame sp0 m m' -> 4096 <= sp0 -> sp0 - 2768 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn SEGS m' (Z_to_bv 64 a) n = rdn SEGS m (Z_to_bv 64 a) n.
Proof.
  intros sp0 m m' a n (rs & FM & O) Hsp Ha Hn.
  destruct n as [|n']; [reflexivity|].
  apply (frame_mod_rdn SEGS m m' rs (S n') (Z_to_bv 64 a) FM).
  - intros i Hi. apply O. rewrite (u_Z2bv a) by lia. rewrite u_Z2bv; lia.
  - rewrite u_Z2bv by lia. lia.
Qed.
End VP3.

Section VP4.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma FILEc_low : forall sp0 m m', 4096 <= sp0 < 2 ^ 63 ->
  FILEc m sp0 -> low_frame sp0 m m' -> FILEc m' sp0.
Proof.
  intros sp0 m m' Hsp FC LF. destruct FC.
  split; (rewrite (low_rdn sp0 m m'); [assumption | assumption | lia | lia | cbn; lia]).
Qed.
End VP4.

Section VP5.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma FILEst_low : forall sp0 m m' u j, 4096 <= sp0 < 2 ^ 63 ->
  FILEst m sp0 u j -> low_frame sp0 m m' -> FILEst m' sp0 u j.
Proof.
  intros sp0 m m' u j Hsp (A & B & (C1 & C2 & C3) & D & E) LF.
  pose proof LF as (rs & FM & O).
  split; [|split; [|split; [|split]]].
  - rewrite (low_rdn sp0 m m'); [exact A | exact LF | lia | lia | cbn; lia].
  - rewrite (low_rdn sp0 m m'); [exact B | exact LF | lia | lia | cbn; lia].
  - split; [|split; [|exact C3]]; (rewrite (low_rdn sp0 m m'); [eassumption | exact LF | lia | lia | cbn; lia]).
  - exact D.
  - eapply defined_grows; [|exact E]. destruct FM as [_ G]. exact G.
Qed.
End VP5.

(* [comment removed for export] *)
Section VP6.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma cell_low : forall sp0 m m' (a : Z) (n : nat) v,
  low_frame sp0 m m' -> 4096 <= sp0 -> sp0 - 2768 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn SEGS m (Z_to_bv 64 a) n = Some v -> rdn SEGS m' (Z_to_bv 64 a) n = Some v.
Proof. intros. rewrite (low_rdn sp0 m m'); assumption. Qed.

(* [comment removed for export] *)
Definition pc_gap (sp0 a len : Z) : Prop :=
  a + len <= sp0 - 3272 \/ (sp0 - 3200 <= a /\ a + len <= sp0 - 2880) \/ sp0 - 2768 <= a.

Lemma PCc_wb : forall sp0 cv regs ret m (a : Z) bs,
  4096 <= sp0 < 2 ^ 63 -> 0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  pc_gap sp0 a (Z.of_nat (length bs)) ->
  PCc m sp0 cv regs ret -> PCc (wbytes m (Z_to_bv 64 a) bs) sp0 cv regs ret.
Proof.
  intros sp0 cv regs ret m a bs Hsp Ha Hn G PC. unfold pc_gap in G. destruct PC.
  split; (rewrite rdn_wbytes_out; [assumption | rewrite !u_Z2bv by lia; lia | rewrite u_Z2bv by lia; cbn; lia | rewrite u_Z2bv by lia; lia]).
Qed.
End VP6.

Section VP7.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma FILEc_wb : forall sp0 m (a : Z) bs,
  4096 <= sp0 < 2 ^ 63 -> 0 <= a -> a + Z.of_nat (length bs) <= sp0 - 2768 ->
  FILEc m sp0 -> FILEc (wbytes m (Z_to_bv 64 a) bs) sp0.
Proof.
  intros sp0 m a bs Hsp Ha Hn FC. eapply FILEc_low; [exact Hsp | exact FC | apply low_frame_wb; lia].
Qed.
End VP7.

Section VP8.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma FILEst_wb : forall sp0 m (a : Z) bs u j,
  4096 <= sp0 < 2 ^ 63 -> 0 <= a -> a + Z.of_nat (length bs) <= sp0 - 2768 ->
  FILEst m sp0 u j -> FILEst (wbytes m (Z_to_bv 64 a) bs) sp0 u j.
Proof.
  intros sp0 m a bs u j Hsp Ha Hn FS. eapply FILEst_low; [exact Hsp | exact FS | apply low_frame_wb; lia].
Qed.
End VP8.

(* [comment removed for export] *)
Section VP9.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma VAslot_wb : forall sp0 m (a : Z) bs q w,
  4096 <= sp0 < 2 ^ 63 -> 0 <= a -> a + Z.of_nat (length bs) <= sp0 - 56 -> 0 <= q < 7 ->
  VAslot m sp0 q w -> VAslot (wbytes m (Z_to_bv 64 a) bs) sp0 q w.
Proof.
  intros sp0 m a bs q w Hsp Ha Hn Hq V. unfold VAslot in *.
  rewrite rdn_wbytes_out; [exact V | rewrite !u_Z2bv by lia; lia | rewrite u_Z2bv by lia; cbn; lia | rewrite u_Z2bv by lia; lia].
Qed.
End VP9.

(* [comment removed for export] *)
Section VP10.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma strnlen_sub_pc : forall sp0 a, 4096 <= sp0 < 2 ^ 63 ->
  outside a (pc_regions sp0) -> outside a [(Z_to_bv 64 (sp0 - 3312 - 32), 32)].
Proof.
  intros sp0 a H0 Ho. unfold pc_regions in *. cbn [outside] in *. unfold in_rng in *.
  revert Ho. unorm. intros Ho. repeat split; lia.
Qed.
End VP10.

Section VP11.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma strnlen_low : forall sp0 m m', 4096 <= sp0 < 2 ^ 63 ->
  frame_mod m m' [(Z_to_bv 64 (sp0 - 3312 - 32), 32)] -> low_frame sp0 m m'.
Proof.
  intros sp0 m m' H0 FM. eapply low_frame_sub; [exact FM|].
  intros x Hx. cbn [outside]. unfold in_rng. unorm. lia.
Qed.
End VP11.
