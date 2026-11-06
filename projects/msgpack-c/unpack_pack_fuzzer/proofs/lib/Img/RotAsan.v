(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 IMap Mem Rot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgAsan.
Import ListNotations Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition GKS : list int := Mem.gkeys_from 8192%uint63 22016 ++ Mem.gkeys_from 108118%uint63 2 ++ Mem.gkeys_from 108153%uint63 1 ++ Mem.gkeys_from 109415%uint63 277 ++ Mem.gkeys_from 109695%uint63 2 ++ Mem.gkeys_from 109706%uint63 1 ++ Mem.gkeys_from 110170%uint63 1 ++ Mem.gkeys_from 110190%uint63 1 ++ Mem.gkeys_from 186156%uint63 1 ++ Mem.gkeys_from 792610%uint63 10 ++ Mem.gkeys_from 792621%uint63 1 ++ Mem.gkeys_from 792686%uint63 279 ++ Mem.gkeys_from 792966%uint63 9 ++ Mem.gkeys_from 792978%uint63 3 ++ Mem.gkeys_from 792982%uint63 11 ++ Mem.gkeys_from 793207%uint63 28 ++ Mem.gkeys_from 809361%uint63 87 ++ Mem.gkeys_from 809449%uint63 410 ++ Mem.gkeys_from 809860%uint63 129 ++ Mem.gkeys_from 809990%uint63 166.
Definition ROT : Mem.rotab := Eval vm_compute in Mem.build_rot SEGS GKS IMap.empty.
Lemma ROT_eq : Mem.build_rot SEGS GKS IMap.empty = ROT.
Proof. vm_cast_no_check (eq_refl ROT). Qed.
Lemma ROT_ok : Rot.rot_ok SEGS ROT.
Proof. exact (Rot.build_rot_ok_of_eq SEGS GKS ROT ROT_eq). Qed.
