(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 IMap Mem Rot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations Mem.
Unset Lia Cache.

Definition GKS : list int := Mem.gkeys_from 8192%uint63 7680 ++ Mem.gkeys_from 42496%uint63 2048 ++ Mem.gkeys_from 44544%uint63 26112.
Definition ROT : Mem.rotab := Eval vm_compute in Mem.build_rot SEGS GKS IMap.empty.
Lemma ROT_eq : Mem.build_rot SEGS GKS IMap.empty = ROT.
Proof. vm_cast_no_check (eq_refl ROT). Qed.
Lemma ROT_ok : Rot.rot_ok SEGS ROT.
Proof. exact (Rot.build_rot_ok_of_eq SEGS GKS ROT ROT_eq). Qed.
