(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxTabs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxEntryS AxSumCk.
Require OSSVerify.openssl.bndiv.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
Notation BDA_SEGS := OSSVerify.openssl.bndiv.images.Asan.M.loaded_segments (only parsing).
Notation BDA_PC := OSSVerify.openssl.bndiv.images.Asan.M.init_pc (only parsing).
Notation BDA_PH := OSSVerify.openssl.bndiv.images.Asan.M.phdrs (only parsing).

Definition bda_tabs : img_tabs := {|
  (* [comment removed for export] *)
  t_rip := Some (0x1c5290, (0x1d5774, 0x5a84d8, 0x5a84e0, 0x5a84e8, 0x5a84f0, 0x670c38, 0x671928, 0x671930, 0x671920));
  (* [comment removed for export] *)
  t_amc := Some (0x1c2a14, (0x1c5290, 0x5a9060, 0x671919, 0x5ab710, 0x52a3ec));
  (* [comment removed for export] *)
  t_chr := Some (0x52a2f0, (0x104c8, 0x10490));
  (* [comment removed for export] *)
  t_sw := Some (0x524844, 0x51f07c);
  (* [comment removed for export] *)
  t_cks := [(4, 0x1c5290); (6, 0x52a3ec); (9, 0x1c2a14)]
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
