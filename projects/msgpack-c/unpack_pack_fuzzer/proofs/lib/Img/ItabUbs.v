(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 IMap Instr ItabOk.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs.
Import FI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PCS : list int := pcs_from 127540%uint63 TEXT_N.
Definition ITAB : itab := Eval vm_compute in build_itab SEGS PCS IMap.empty.

Lemma ITAB_eq : build_itab SEGS PCS IMap.empty = ITAB.
Proof. vm_cast_no_check (eq_refl ITAB). Qed.

Lemma ITAB_ok : itab_ok SEGS ITAB.
Proof. exact (ItabOk.build_itab_ok_of_eq SEGS PCS ITAB ITAB_eq). Qed.

Lemma ITAB_bst : IMap.bst ITAB.
Proof. exact (ItabOk.build_itab_bst_of_eq SEGS PCS ITAB ITAB_eq). Qed.
