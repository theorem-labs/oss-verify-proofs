(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import W64 Val Mem FI St Step Plan.
Unset Lia Cache.

Definition force_some {A} (o : option A) (d : A) : A := match o with Some x => x | None => d end.
Definition wp (i : int) : w64 := W64 false i.
Definition wn (i : int) : w64 := W64 true i.
Definition imap_of {A} (l : list (int * A)) : IMap.t A :=
  fold_left (fun m kv => IMap.add (fst kv) (snd kv) m) l IMap.empty.

Definition reg_upd (r : region) (adds : list (int * gran)) (rems : list int) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r)
         (fold_left (fun m kv => IMap.add (fst kv) (snd kv) m) adds (fold_left (fun m k => IMap.remove k m) rems (rg_cells r))).
Definition rf_of {A} (d : A) (l : list A) : rf A :=
  match l with
  | [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15;a16;a17;a18;a19;a20;a21;a22;a23;a24;a25;a26;a27;a28;a29;a30;a31] =>
      RF a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31
  | _ => rf_init d
  end.

Definition dump_region (r : region) :=
  (rg_lo r, rg_hi r, rg_w r, rg_bg r, List.map (fun kv => (fst kv, g_dirty (snd kv), g_cells (snd kv))) (IMap.elements (rg_cells r))).
Definition dump_state (st : sstate) :=
  (s_pc st, rf_to_list (s_rf st), rf_to_list (s_ff st), s_resv st,
   List.map (fun kv => (fst kv, dump_region (snd kv))) (IMap.elements (s_regs st)),
   s_facts st, s_ops st, s_priv st, s_next st).
Definition dump_sres (r : sres) :=
  match r with
  | SOk st => (KFuel, dump_state st)
  | SStop why st => (why, dump_state st)
  end.
