(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan.
Open Scope Z_scope.
Unset Lia Cache.

Module CtrLib.

Definition lit_of (v : sv) : option w64 := match v with VL w => Some w | _ => None end.

Definition small_lit (v : sv) : option int :=
  match v with
  | VL w => if negb (wt w) && PrimInt63.ltb (wl w) bit62i then Some (wl w) else None
  | _ => None
  end.

Definition ret_pc (st : sstate) : option int := small_lit (getr st X1).

Definition fresh_ok (st : sstate) : bool :=
  st_vars_below (s_next st) st && PrimInt63.ltb 0%uint63 (s_next st)
  && PrimInt63.ltb (s_next st) 4611686018427387648%uint63.

Definition call_pre (st : sstate) : option int :=
  match s_resv st with
  | RNone => if fresh_ok st then
               match ret_pc st with
               | Some r => if PrimInt63.eqb (PrimInt63.land r 1%uint63) 0%uint63 then Some r else None
               | None => None
               end
             else None
  | _ => None
  end.

Definition STACK_ID : int := 1%uint63.
Definition stack_room (st : sstate) (n : int) : bool :=
  match getr st X2, IMap.find STACK_ID (s_regs st) with
  | VP k off, Some r =>
      PrimInt63.eqb k STACK_ID && rg_w r &&
      match okey (wsub off (wlit n)), okey off with
      | Some klo, Some ksp => kleb (rg_lo r) klo && kleb klo ksp
      | _, _ => false
      end
  | _, _ => false
  end.

Definition forget_stack_below_sp (st : sstate) : option sstate :=
  match getr st X2, IMap.find STACK_ID (s_regs st) with
  | VP k off, Some r =>
      if PrimInt63.eqb k STACK_ID then
        match okey off with
        | Some ksp => Some (setregs st (IMap.add STACK_ID (region_forget r (granule (rg_lo r)) (granule ksp)) (s_regs st)))
        | None => None
        end
      else None
  | _, _ => None
  end.

Definition set_next (st : sstate) (n : int) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) n.
Definition set_ops (st : sstate) (os : list opinst) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) os (s_priv st) (s_next st).

Definition fresh (st : sstate) : int * sstate :=
  (s_next st, set_next st (PrimInt63.add (s_next st) 1%uint63)).

Definition clobber_regs : list r5 := [X1; X5; X6; X7; X11; X12; X13; X14; X15; X16; X17; X28; X29; X30; X31].

Fixpoint clobber_from (rs : list r5) (n : int) (st : sstate) : sstate :=
  match rs with
  | [] => st
  | r :: rs' => clobber_from rs' (PrimInt63.add n 1%uint63) (setr st r (VP n wzero))
  end.

Definition clobber (st : sstate) : sstate :=
  let n := s_next st in
  set_next (clobber_from clobber_regs n st) (PrimInt63.add n 15%uint63).

Fixpoint find_op (id : int) (os : list opinst) : option (list sv) :=
  match os with
  | [] => None
  | o :: os' => if PrimInt63.eqb (op_id o) id then Some (op_args o) else find_op id os'
  end.

Fixpoint set_op (id : int) (args : list sv) (os : list opinst) : list opinst :=
  match os with
  | [] => []
  | o :: os' => if PrimInt63.eqb (op_id o) id then OpI id args :: os' else o :: set_op id args os'
  end.

Fixpoint remove_op (id : int) (os : list opinst) : list opinst :=
  match os with
  | [] => []
  | o :: os' => if PrimInt63.eqb (op_id o) id then os' else o :: remove_op id os'
  end.

Definition HEAP_ID : int := 1%uint63.
Definition K_BLOCK : w64 := wone.

Definition heap_nwin (args : list sv) : option nat :=
  match args with
  | VL _ :: _ :: VL nw :: rest =>
      if wt nw then None else
      let n := Z.to_nat (to_Z (wl nw)) in
      if Nat.leb (3 * n) (length rest) then Some n else None
  | _ => None
  end.

Definition heap_A (args : list sv) : option sv :=
  match args with
  | VL _ :: a :: VL _ :: _ => Some a
  | _ => None
  end.
Definition heap_set_A (args : list sv) (a : sv) : option (list sv) :=
  match args with
  | VL md :: _ :: VL nw :: rest => Some (VL md :: a :: VL nw :: rest)
  | _ => None
  end.

Definition heap_add_window (args : list sv) (lo len kind : sv) : option (list sv) :=
  match heap_nwin args, args with
  | Some n, VL md :: a :: VL nw :: rest =>
      Some (VL md :: a :: VL (wadd nw wone) :: firstn (3 * n) rest ++ [lo; len; kind] ++ skipn (3 * n) rest)
  | _, _ => None
  end.

Fixpoint del_window (n : nat) (ws : list sv) (lo : sv) : option (list sv) :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      if sv_eqb l lo && sv_eqb kd (VL K_BLOCK) then Some ws'
      else match del_window n' ws' lo with Some ws'' => Some (l :: sz :: kd :: ws'') | None => None end
  | _, _ => None
  end.

Definition heap_del_window (args : list sv) (lo : sv) : option (list sv) :=
  match heap_nwin args, args with
  | Some n, VL md :: a :: VL nw :: rest =>
      match del_window n (firstn (3 * n) rest) lo with
      | Some ws => Some (VL md :: a :: VL (wsub nw wone) :: ws ++ skipn (3 * n) rest)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint find_window (n : nat) (ws : list sv) (lo : sv) : option (sv * sv * sv) :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' => if sv_eqb l lo then Some (l, sz, kd) else find_window n' ws' lo
  | _, _ => None
  end.
Definition heap_find_window (args : list sv) (lo : sv) : option (sv * sv * sv) :=
  match heap_nwin args, args with
  | Some n, _ :: _ :: _ :: rest => find_window n rest lo
  | _, _ => None
  end.

Section WithSegs.
Variable segs : list Segment.

Definition store4_abs (addr : int) (st : sstate) (v : sv) : option sstate :=
  match do_store segs st (VL (wlit addr)) 4%uint63 v with
  | inl st' => Some st'
  | inr _ => None
  end.

Definition havoc_errno (errno_addr : int) (st : sstate) : option sstate :=
  let (e, st1) := fresh st in store4_abs errno_addr st1 (VP e wzero).

End WithSegs.

Definition sysret (st : sstate) (v : sv) : sstate := setpc (setr st X10 v) (PrimInt63.add (s_pc st) 4%uint63).

Definition known_ltu (fs : list fact) (a b : sv) : bool := dec_true (decide_ltu fs a b).
Definition known_leu (fs : list fact) (a b : sv) : bool := dec_false (decide_ltu fs b a).
Definition known_eq (fs : list fact) (a b : sv) : bool := dec_true (decide_eq fs a b).

End CtrLib.
