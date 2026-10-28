(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxTabs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxEntryS AxSumCk.
Require OssFuzzTheorems.openssl.bndiv.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
Notation BDA_SEGS := OssFuzzTheorems.openssl.bndiv.images.AsanUbsan.M.loaded_segments (only parsing).
Notation BDA_PC := OssFuzzTheorems.openssl.bndiv.images.AsanUbsan.M.init_pc (only parsing).
Notation BDA_PH := OssFuzzTheorems.openssl.bndiv.images.AsanUbsan.M.phdrs (only parsing).

Definition bda_tabs : img_tabs := {|
  (* [comment removed for export] *)
  t_rip := Some (0x1c01f4, (0x1d06d8, 0x5e0cd8, 0x5e0ce0, 0x5e0ce8, 0x5e0cf0, 0x6a39f8, 0x6a46e8, 0x6a46f0, 0x6a46e0));
  (* [comment removed for export] *)
  t_amc := Some (0x1bd978, (0x1c01f4, 0x5e1860, 0x6a46d9, 0x5e3f10, 0x563070));
  (* [comment removed for export] *)
  t_chr := Some (0x562f74, (0x104e0, 0x104a8));
  (* [comment removed for export] *)
  t_sw := Some (0x55d4c8, 0x557d00);
  (* [comment removed for export] *)
  t_cks := [(4, 0x1c01f4); (6, 0x563070); (9, 0x1bd978)]
|}.

(* [comment removed for export] *)
Lemma bda_img_ok : img_ok BDA_SEGS BDA_PC = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma bda_tabs_ok : tabs_ok bda_tabs = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bda_cks_ok : cks_ok bda_tabs BDA_SEGS = true.
Proof. vm_compute. reflexivity. Qed.
