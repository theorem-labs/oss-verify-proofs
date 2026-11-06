(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Agree Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7G Require Import GlueKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Globals.

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

Lemma dtor_cells6_init : forall V (m : mem), Forall (mfact_ok asegs V m) both_mem_facts ->
  rw_cells asegs m 0xab9b8 [C8 (Z_to_bv 64 0xafa20); C8 (Z_to_bv 64 0xb0e60)]
  /\ rw_cells asegs m 0xaad10 [C8 (Z_to_bv 64 0x143fe0)]
  /\ rw_cells asegs m 0x1460e0 [C8 (Z_to_bv 64 18446744073709551615)]
  /\ rw_cells asegs m 0xb3d9c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xb1df0 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xafa20 (desc_cells A0_DESCS).
Proof.
  intros V m HM.
  split. { aimg V m HM 0xab9b8 [C8 (Z_to_bv 64 0xafa20); C8 (Z_to_bv 64 0xb0e60)] H. exact H. }
  split. { aimg V m HM 0xaad10 [C8 (Z_to_bv 64 0x143fe0)] H. exact H. }
  split. { mf V m HM (MCell (ZLit 1335520) 8 (ZLit 18446744073709551615)) H. exact H. }
  split. { mf V m HM (MCell (ZLit 736668) 1 (ZLit 1)) H. exact H. }
  split. { mf V m HM (MCell (ZLit 728560) 8 (ZLit 0)) H. exact H. }
  apply (aimg_chunk V m _ 0xafa20 (desc_cells A0_DESCS) HM); [vm_compute; reflexivity| apply desc_cells_wf| vm_compute; reflexivity| lia|].
  rewrite cells_size_desc. change (length A0_DESCS) with 81%nat. lia.
Qed.
