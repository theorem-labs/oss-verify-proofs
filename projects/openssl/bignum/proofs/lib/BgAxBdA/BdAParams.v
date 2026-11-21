(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the image's no-kernel-mapping fact the start-up now takes). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxTabs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxEntryS AxSumCk.
Require OSSVerify.openssl.bignum.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Notation BDA_SEGS := OSSVerify.openssl.bignum.images.Asan.M.loaded_segments (only parsing).
Notation BDA_PC := OSSVerify.openssl.bignum.images.Asan.M.init_pc (only parsing).
Notation BDA_PH := OSSVerify.openssl.bignum.images.Asan.M.phdrs (only parsing).

Definition bda_tabs : img_tabs := {|

  t_rip := Some (0x1c4e80, (0x1d5364, 0x5a4bb8, 0x5a4bc0, 0x5a4bc8, 0x5a4bd0, 0x66d138, 0x66de28, 0x66de30, 0x66de20));

  t_amc := Some (0x1c2604, (0x1c4e80, 0x5a5740, 0x66de19, 0x5a7de8, 0x526ae0));

  t_chr := Some (0x5269e4, (0x104d0, 0x10498));

  t_sw := Some (0x521018, 0x51b850);

  t_cks := [(4, 0x1c4e80); (6, 0x526ae0); (9, 0x1c2604)]
|}.

Lemma bda_img_ok : img_ok BDA_SEGS BDA_PC = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma bda_tabs_ok : tabs_ok bda_tabs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bda_cks_ok : cks_ok bda_tabs BDA_SEGS = true.
Proof. vm_compute. reflexivity. Qed.

(* asum_ck_ok and AxStart's Section Start take this as a premise rather than deriving
   it: img_ok's seg_ok1 (AxEntryS.v:68-75) says nothing about seg_kernel_map, and segs
   is abstract there, so Himg cannot give it.  BDA_SEGS is this unit's own ELF image,
   so here it is concrete and closes by computation. *)
Lemma bda_segs_nk : forallb (fun s => negb (seg_kernel_map s)) BDA_SEGS = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
