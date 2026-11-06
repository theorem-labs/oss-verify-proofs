(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ABytes RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import FsKit F_memset. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_rsrvshadow APoisonR_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Lemma shlen_div8 : forall L, shlen L = L / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shad_div8 : forall a, shad a = a / 8 + ASHOFF.
Proof. intros. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.

Lemma zeros_app : forall a b, 0 <= a -> 0 <= b -> zeros a ++ zeros b = zeros (a + b).
Proof. intros a b Ha Hb. unfold zeros. rewrite Z2Nat.inj_add by lia. rewrite repeat_app. reflexivity. Qed.
Lemma rw_zeros_join : forall m A a b,
  rw_cells asegs m A [CB (Z.to_nat a) (zeros a)] -> rw_cells asegs m (A + a) [CB (Z.to_nat b) (zeros b)] ->
  0 <= a -> 0 <= b -> rw_cells asegs m A [CB (Z.to_nat (a + b)) (zeros (a + b))].
Proof.
  intros m A a b H1 H2 Ha Hb.
  assert (H : rw_cells asegs m A ([CB (Z.to_nat a) (zeros a)] ++ [CB (Z.to_nat b) (zeros b)])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge asegs m A [] ([CB (Z.to_nat a) (zeros a)] ++ [CB (Z.to_nat b) (zeros b)]) []) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. rewrite zeros_app, <- Z2Nat.inj_add in M by lia. exact M.
Qed.

Lemma repeat0_zeros : forall n, repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat n) = zeros n.
Proof. intros n. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rw_cells_nil0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells asegs m A [CB 0%nat []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - unfold bytes_at. cbn [length cells_bytes cbytes app Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - unfold wr_at. cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

End CANSEC1.
Ltac memset_call D WM RSH RET Z :=
  let bs := fresh "bs" in let DX := fresh "DX" in
  destruct (dc_at_any _ _ _ _ D WM ltac:(lia)) as [bs DX];
  eapply evtF_cut;
  [ eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DX | assumption | rewrite !unsigned_lit by lia; eapply rng_sub; [exact RSH | lia | lia] ]
  | clear DX;
    let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in let MI2 := fresh "MI2" in
    intros ms' PO; unfold memset_post in PO; destruct_exs PO; destruct PO as (-> & MU2 & WM2 & MI2 & Z);
    rewrite !unsigned_lit in MU2, Z by lia; rewrite repeat0_zeros in Z;
    lazymatch type of MU2 with munch _ ?ma ?mb =>
      transport_after_call asegs ma mb MU2 WM2; clear MU2 WM2; try match goal with H : mem_inv asegs ma |- _ => clear H end end;
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]) ].

Section CANSEC2. Context {rc : runConstT}.
Theorem poison_remap_proof : poison_remap_stmt.
Proof.

  unfold poison_remap_stmt. intros. exfalso.
  match goal with H : 0xffffffffffffffff <= shlen _ |- _ => rewrite shlen_div8 in H end.
  match goal with H1 : _ + ?sz <= 2^47, H2 : ablk _ _ |- _ => unfold ablk, KLS, AIMG_HI in H2 end.
  Z.div_mod_to_equations. lia.
Qed.
Definition poison_remap : poison_remap_stmt := poison_remap_proof.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ABytes.TwinB RT_stubs.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import FsKit.TwinB F_memset.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import F_rsrvshadow.TwinB APoisonR_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Lemma shlen_div8 : forall L, shlen L = L / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shad_div8 : forall a, shad a = a / 8 + ASHOFF.
Proof. intros. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.

Lemma zeros_app : forall a b, 0 <= a -> 0 <= b -> zeros a ++ zeros b = zeros (a + b).
Proof. intros a b Ha Hb. unfold zeros. rewrite Z2Nat.inj_add by lia. rewrite repeat_app. reflexivity. Qed.
Lemma rw_zeros_join : forall m A a b,
  rw_cells bsegs m A [CB (Z.to_nat a) (zeros a)] -> rw_cells bsegs m (A + a) [CB (Z.to_nat b) (zeros b)] ->
  0 <= a -> 0 <= b -> rw_cells bsegs m A [CB (Z.to_nat (a + b)) (zeros (a + b))].
Proof.
  intros m A a b H1 H2 Ha Hb.
  assert (H : rw_cells bsegs m A ([CB (Z.to_nat a) (zeros a)] ++ [CB (Z.to_nat b) (zeros b)])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  pose proof (rw_cells_merge bsegs m A [] ([CB (Z.to_nat a) (zeros a)] ++ [CB (Z.to_nat b) (zeros b)]) []) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. rewrite zeros_app, <- Z2Nat.inj_add in M by lia. exact M.
Qed.

Lemma repeat0_zeros : forall n, repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat n) = zeros n.
Proof. intros n. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma rw_cells_nil0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells bsegs m A [CB 0%nat []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - unfold bytes_at. cbn [length cells_bytes cbytes app Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - unfold wr_at. cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

End CANSEC1.
Ltac memset_call D WM RSH RET Z :=
  let bs := fresh "bs" in let DX := fresh "DX" in
  destruct (dc_at_any _ _ _ _ D WM ltac:(lia)) as [bs DX];
  eapply evtF_cut;
  [ eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DX | assumption | rewrite !unsigned_lit by lia; eapply rng_sub; [exact RSH | lia | lia] ]
  | clear DX;
    let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in let MI2 := fresh "MI2" in
    intros ms' PO; unfold memset_post in PO; destruct_exs PO; destruct PO as (-> & MU2 & WM2 & MI2 & Z);
    rewrite !unsigned_lit in MU2, Z by lia; rewrite repeat0_zeros in Z;
    lazymatch type of MU2 with munch _ ?ma ?mb =>
      transport_after_call bsegs ma mb MU2 WM2; clear MU2 WM2; try match goal with H : mem_inv bsegs ma |- _ => clear H end end;
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]) ].

Section CANSEC2. Context {rc : runConstT}.
Theorem poison_remap_proof : poison_remap_stmt.
Proof.

  unfold poison_remap_stmt. intros. exfalso.
  match goal with H : 0xffffffffffffffff <= shlen _ |- _ => rewrite shlen_div8 in H end.
  match goal with H1 : _ + ?sz <= 2^47, H2 : ablk _ _ |- _ => unfold ablk, KLS, AIMG_HI in H2 end.
  Z.div_mod_to_equations. lia.
Qed.
Definition poison_remap : poison_remap_stmt := poison_remap_proof.
End CANSEC2.
End TwinB.
