(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Globals.

Import ListNotations.
Open Scope Z_scope.

Lemma cells_size_desc : forall ds, Z.of_nat (cells_size (desc_cells ds)) = 64 * Z.of_nat (length ds).
Proof.
  induction ds as [|d r IH]; [reflexivity|]. destruct d as [[[[[[[b sz] srz] nm] md] dy] loc] odr].
  change (desc_cells ((b, sz, srz, nm, md, dy, loc, odr) :: r)) with (desc_cells1 (b, sz, srz, nm, md, dy, loc, odr) ++ desc_cells r).
  rewrite cells_size_app, Nat2Z.inj_add, IH. cbn [desc_cells1 cells_size csize Nat.add length]. lia.
Qed.
Lemma desc_cells_wf : forall ds, cells_wf (desc_cells ds).
Proof.
  induction ds as [|d r IH]; [exact I|]. destruct d as [[[[[[[b sz] srz] nm] md] dy] loc] odr].
  change (desc_cells ((b, sz, srz, nm, md, dy, loc, odr) :: r)) with (desc_cells1 (b, sz, srz, nm, md, dy, loc, odr) ++ desc_cells r).
  cbn [desc_cells1 app cells_wf cell_wf]. repeat (split; [exact I|]). exact IH.
Qed.

Lemma dtor_cells6_init : forall V (m : mem), Forall (mfact_ok asegs V m) asan_mem_facts ->
  rw_cells asegs m 0xaad58 [C8 (Z_to_bv 64 0xaedc0); C8 (Z_to_bv 64 0xb0240)]
  /\ rw_cells asegs m 0xaa0b0 [C8 (Z_to_bv 64 0x1433a0)]
  /\ rw_cells asegs m 0x1454a0 [C8 (Z_to_bv 64 18446744073709551615)]
  /\ rw_cells asegs m 0xb315c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xb11b0 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xaedc0 (desc_cells A0_DESCS).
Proof.
  intros V m HM.
  split. { aimg V m HM 0xaad58 [C8 (Z_to_bv 64 0xaedc0); C8 (Z_to_bv 64 0xb0240)] H. exact H. }
  split. { aimg V m HM 0xaa0b0 [C8 (Z_to_bv 64 0x1433a0)] H. exact H. }
  split. { mf V m HM (MCell (ZLit 1332384) 8 (ZLit 18446744073709551615)) H. exact H. }
  split. { mf V m HM (MCell (ZLit 733532) 1 (ZLit 1)) H. exact H. }
  split. { mf V m HM (MCell (ZLit 725424) 8 (ZLit 0)) H. exact H. }
  apply (aimg_chunk V m _ 0xaedc0 (desc_cells A0_DESCS) HM); [vm_compute; reflexivity| apply desc_cells_wf| vm_compute; reflexivity| lia|].
  rewrite cells_size_desc. change (length A0_DESCS) with 82%nat. lia.
Qed.
