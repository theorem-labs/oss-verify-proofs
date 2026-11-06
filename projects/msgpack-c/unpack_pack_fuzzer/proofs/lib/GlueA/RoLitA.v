(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem.
Open Scope Z_scope.

Module RoLitA.
Record cfg := Cfg { relro_lo : int; relro_hi : int; shbase_addr : int; flag_addr : int }.
Definition CFG_ASAN : cfg := Cfg 839680%uint63 864256%uint63 891576%uint63 891584%uint63.
Definition CFG_BOTH : cfg := Cfg 847872%uint63 872448%uint63 900216%uint63 900224%uint63.
Definition VIDS : list int := [1%uint63].

Definition wok_b (n : int) : bool := PrimInt63.eqb n 1%uint63 || PrimInt63.eqb n 2%uint63 || PrimInt63.eqb n 4%uint63 || PrimInt63.eqb n 8%uint63.

Definition RV (c : cfg) (segs : list Segment) (a n : int) : option w64 :=
  if wok_b n && PrimInt63.leb (relro_lo c) a && PrimInt63.leb (PrimInt63.add a n) (relro_hi c) then
    match img_bytes segs (to_Z a) (Z.to_nat (to_Z n)) with
    | Some bs => Some (bytes_to_w64 bs)
    | None => None
    end
  else if PrimInt63.eqb a (shbase_addr c) && PrimInt63.eqb n 8%uint63 then Some (wlit 2147450880%uint63)
  else if PrimInt63.eqb a (flag_addr c) && PrimInt63.eqb n 4%uint63 then Some (wlit 1%uint63)
  else None.
End RoLitA.
