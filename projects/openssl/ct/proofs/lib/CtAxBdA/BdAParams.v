(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxTabs.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxEntryS AxSumCk.
Require OSSVerify.openssl.ct.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

(* [comment removed for export] *)
Notation BDA_SEGS := OSSVerify.openssl.ct.images.Asan.M.loaded_segments (only parsing).
Notation BDA_PC := OSSVerify.openssl.ct.images.Asan.M.init_pc (only parsing).
Notation BDA_PH := OSSVerify.openssl.ct.images.Asan.M.phdrs (only parsing).

Definition bda_tabs : img_tabs := {|
  (* [comment removed for export] *)
  t_rip := Some (0x1c5f88, (0x1d646c, 0x5a9238, 0x5a9240, 0x5a9248, 0x5a9250, 0x672038, 0x672d28, 0x672d30, 0x672d20));
  (* [comment removed for export] *)
  t_amc := Some (0x1c370c, (0x1c5f88, 0x5a9dc0, 0x672d19, 0x5ac4a8, 0x52b0ac));
  (* [comment removed for export] *)
  t_chr := Some (0x52afb0, (0x104d8, 0x104a0));
  (* [comment removed for export] *)
  t_sw := Some (0x52574c, 0x51ff84);
  (* [comment removed for export] *)
  t_cks := [(4, 0x1c5f88); (6, 0x52b0ac); (9, 0x1c370c)]
|}.

(* [comment removed for export] *)
Lemma bda_img_ok : img_ok BDA_SEGS BDA_PC = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* NEW: no_lazy_img/no_lazy_imgn gained the seg_kernel_map discriminant when
   segments_reserved began filtering it (LPS@75d69e00 Run.v:253-254), so asum_ck_ok
   and Section Start now take it as a premise -- they cannot derive it, since img_ok
   is forallb seg_ok1 and seg_ok1 says nothing about seg_kernel_map.  Here BDA_SEGS is
   concrete, which is exactly where AsanWLazy.v:100-105 says to close it, so this is
   bda_img_ok's discharge applied to the sibling fact. *)
Lemma bda_segs_nk : forallb (fun s => negb (seg_kernel_map s)) BDA_SEGS = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma bda_tabs_ok : tabs_ok bda_tabs = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bda_cks_ok : cks_ok bda_tabs BDA_SEGS = true.
Proof. vm_compute. reflexivity. Qed.
