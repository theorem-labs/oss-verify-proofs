(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module CtrW.
Section WithSegs.
Variable segs : list Segment.
Variable errno_addr : int.

Definition MEMCPYW_MAX : Z := 4096.

Fixpoint copy_words (n : nat) (i : int) (src dst : sv) (st : sstate) : option sstate :=
  match n with
  | O => Some st
  | S n' =>
      match do_load segs st (sv_alu ALU_ADD src (VL (wlit i))) 8%uint63 false with
      | inl (Some v) =>
          match do_store segs st (sv_alu ALU_ADD dst (VL (wlit i))) 8%uint63 v with
          | inl st' => copy_words n' (PrimInt63.add i 8%uint63) src dst st'
          | inr _ => None
          end
      | _ => None
      end
  end.

Definition ww_separated (st : sstate) (n : int) : bool :=
  match addr_of (getr st X10), addr_of (getr st X11) with
  | Some (kd, od), Some (ks, os) =>
      negb (PrimInt63.eqb ks kd)
      || match okey od, okey os with
         | Some a, Some b => Z.leb (keyZ a + to_Z n) (keyZ b) || Z.leb (keyZ b + to_Z n) (keyZ a)
         | _, _ => false
         end
  | _, _ => false
  end.

Definition memcpy_w_apply (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X12 with
  | Some r, VL n =>
      if wt n || negb (Z.leb (to_Z (wl n)) MEMCPYW_MAX) || PrimInt63.eqb (wl n) 0%uint63
         || negb (PrimInt63.eqb (PrimInt63.land (wl n) 7%uint63) 0%uint63) || negb (ww_separated st (wl n)) then None else
      match copy_words (Z.to_nat (to_Z (wl n) / 8)) 0%uint63 (getr st X11) (getr st X10) st with
      | Some st1 =>
          match havoc_errno segs errno_addr (clobber st1) with
          | Some st2 => Some [setpc st2 r]
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition memcpy_w_c (pc : int) : contract := Contract pc memcpy_w_apply.

End WithSegs.
End CtrW.
