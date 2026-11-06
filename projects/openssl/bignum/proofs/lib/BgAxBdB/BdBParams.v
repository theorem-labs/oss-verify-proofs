(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxTabs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxEntryS AxSumCk.
Require OSSVerify.openssl.bignum.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Notation BDB_SEGS := OSSVerify.openssl.bignum.images.AsanUbsan.M.loaded_segments (only parsing).
Notation BDB_PC := OSSVerify.openssl.bignum.images.AsanUbsan.M.init_pc (only parsing).
Notation BDB_PH := OSSVerify.openssl.bignum.images.AsanUbsan.M.phdrs (only parsing).

Definition bdb_tabs : img_tabs := {|

  t_rip := Some (0x1bfe6c, (0x1d0350, 0x5dcf18, 0x5dcf20, 0x5dcf28, 0x5dcf30, 0x69fa38, 0x6a0728, 0x6a0730, 0x6a0720));

  t_amc := Some (0x1bd5f0, (0x1bfe6c, 0x5ddaa0, 0x6a0719, 0x5e0148, 0x55f2c4));

  t_chr := Some (0x55f1c8, (0x104e8, 0x104b0));

  t_sw := Some (0x5597fc, 0x554034);

  t_cks := [(4, 0x1bfe6c); (6, 0x55f2c4); (9, 0x1bd5f0)]
|}.

Lemma bdb_img_ok : img_ok BDB_SEGS BDB_PC = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bdb_tabs_ok : tabs_ok bdb_tabs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bdb_cks_ok : cks_ok bdb_tabs BDB_SEGS = true.
Proof. vm_compute. reflexivity. Qed.
