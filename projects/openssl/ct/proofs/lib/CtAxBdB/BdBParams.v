(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxTabs.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxEntryS AxSumCk.
Require OSSVerify.openssl.ct.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
Notation BDB_SEGS := OSSVerify.openssl.ct.images.AsanUbsan.M.loaded_segments (only parsing).
Notation BDB_PC := OSSVerify.openssl.ct.images.AsanUbsan.M.init_pc (only parsing).
Notation BDB_PH := OSSVerify.openssl.ct.images.AsanUbsan.M.phdrs (only parsing).

Definition bdb_tabs : img_tabs := {|
  (* [comment removed for export] *)
  t_rip := Some (0x1c0f18, (0x1d13fc, 0x5e1b38, 0x5e1b40, 0x5e1b48, 0x5e1b50, 0x6a4e78, 0x6a5b68, 0x6a5b70, 0x6a5b60));
  (* [comment removed for export] *)
  t_amc := Some (0x1be69c, (0x1c0f18, 0x5e26c0, 0x6a5b59, 0x5e4da8, 0x563e30));
  (* [comment removed for export] *)
  t_chr := Some (0x563d34, (0x104f0, 0x104b8));
  (* [comment removed for export] *)
  t_sw := Some (0x55e4d0, 0x558d08);
  (* [comment removed for export] *)
  t_cks := [(4, 0x1c0f18); (6, 0x563e30); (9, 0x1be69c)]
|}.

(* [comment removed for export] *)
Lemma bdb_img_ok : img_ok BDB_SEGS BDB_PC = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma bdb_tabs_ok : tabs_ok bdb_tabs = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bdb_cks_ok : cks_ok bdb_tabs BDB_SEGS = true.
Proof. vm_compute. reflexivity. Qed.
