(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan.
Unset Lia Cache.

Module DrvRoot.
Section WithSegs.
Variable segs : list Segment.

Definition wokb (w : int) : bool :=
  PrimInt63.eqb w 1%uint63 || PrimInt63.eqb w 2%uint63 || PrimInt63.eqb w 4%uint63 || PrimInt63.eqb w 8%uint63.
Definition remat1 (st : sstate) (aw : int * int) : option sstate :=
  let a := VL (wlit (fst aw)) in
  if negb (wokb (snd aw)) then None else
  match do_load segs st a (snd aw) false with
  | inl (Some v) =>
      match do_store segs st a (snd aw) v with
      | inl st' => Some st'
      | inr _ => None
      end
  | _ => None
  end.

Fixpoint remat (st : sstate) (l : list (int * int)) : option sstate :=
  match l with
  | [] => Some st
  | aw :: l' => match remat1 st aw with Some st' => remat st' l' | None => None end
  end.

Definition prune_region (r : region) (ghi : int) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) BGNone
         (imap_of (List.filter (fun kv => negb (kltb (fst kv) ghi)) (IMap.elements (rg_cells r)))).

Definition prune1 (st : sstate) (ghi : int) : option sstate :=
  match IMap.find 1%uint63 (s_regs st) with
  | Some r => Some (setregs st (IMap.add 1%uint63 (prune_region r ghi) (s_regs st)))
  | None => None
  end.

Definition with_ops_priv (st : sstate) (ops : list opinst) (priv : list (int * int)) : option sstate :=
  match s_ops st, s_priv st with
  | [], [] => Some (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) ops priv (s_next st))
  | _, _ => None
  end.

Definition drv_of_main (rm : list (int * int)) (ghi : int) (ops : list opinst) (priv : list (int * int))
           (st : sstate) : option sstate :=
  match remat st rm with
  | Some st1 => match prune1 st1 ghi with
                | Some st2 => with_ops_priv st2 ops priv
                | None => None
                end
  | None => None
  end.

End WithSegs.
End DrvRoot.
