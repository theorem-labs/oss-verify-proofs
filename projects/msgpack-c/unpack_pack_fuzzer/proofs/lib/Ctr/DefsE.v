(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module CtrE.
Section WithImg.
Variable segs : list Segment.
Variables (ERRNO LIBC GOT GUARD TP : int) (CANARY : sv).

Variable IMG_HI : int.

Definition aligned_alloc1_apply (st : sstate) : option (list sstate) :=
  match CtrA.alloc_call segs ERRNO LIBC GOT GUARD TP CANARY CtrA.ALIGNED_STACK st, getr st X10 with
  | Some (r, ksp, hargs0, _), VL al =>
      match CtrA.heap_drop_A hargs0 with
      | Some hargs =>
          let n := getr st X11 in
          if weqb al (wlit 16%uint63) && CtrA.size_ok (s_facts st) n
          then CtrA.malloc_posts ERRNO LIBC GOT GUARD CANARY st r ksp hargs hargs n else None
      | None => None
      end
  | _, _ => None
  end.
Definition aligned_alloc1_c (pc : int) : contract := Contract pc aligned_alloc1_apply.

Fixpoint has_block_window (fs : list fact) (k : int) (n : nat) (rest : list sv) : bool :=
  match n, rest with
  | S n', lo :: len :: kd :: rest' =>
      (match lo, kd with
       | VP k' o, VL kw => PrimInt63.eqb k' k && weqb o wzero && weqb kw K_BLOCK && known_ltu fs (VL wzero) len
       | _, _ => false
       end) || has_block_window fs k n' rest'
  | _, _ => false
  end.

Definition blk_side_apply (st : sstate) : option (list sstate) :=
  match getr st X10, find_op HEAP_ID (s_ops st) with
  | VP k o, Some hargs =>
      match heap_nwin hargs, hargs with
      | Some n, _ :: _ :: _ :: rest =>
          if weqb o wzero && has_block_window (s_facts st) k n rest
          then Some [addfact st (FRange k CtrA.BLK_LO (wsub CtrA.IMG_LO wone));
                     addfact st (FRange k (wlit IMG_HI) CtrA.BLK_HI)]
          else None
      | _, _ => None
      end
  | _, _ => None
  end.
Definition blk_side_c (pc : int) : contract := Contract pc blk_side_apply.

End WithImg.
End CtrE.
