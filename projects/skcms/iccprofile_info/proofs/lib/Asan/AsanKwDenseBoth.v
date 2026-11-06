(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanKwGcBoth.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition dense_map (gb : nat) (cs : acs) : list (nat * nat) := compact_map gb cs.
Definition dense_start (nx0 gb : nat) (cs : acs) : acs :=
  match node_rename nx0 cs (dense_map gb cs) with Some x => x | None => cs end.
Definition dense_ok (nx0 gb : nat) (cs : acs) : bool :=
  match node_rename nx0 cs (dense_map gb cs) with Some _ => true | None => false end.

Fixpoint e_first_var (e : expr) : option nat :=
  match e with
  | ELit _ => None
  | EVar n => Some n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => match e_first_var x with Some v => Some v | None => e_first_var y end
  | EExt _ _ _ x => e_first_var x
  | EBlob _ _ _ _ => None
  end.
Definition reg_var (r : nat) (cs : acs) : nat :=
  match e_first_var (nth r (s_regs (a_ss cs)) (ELit 0)) with Some v => v | None => 0%nat end.

(* [comment removed for export] *)
Fixpoint kn_dedupe (seen : list kentry) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if existsb (kentry_eqb K) seen then kn_dedupe seen r else K :: kn_dedupe (K :: seen) r
  end.
Definition gc_all (d : list nat) (cs : acs) : acs :=
  let cs1 := gc_dead d cs in set_kn cs1 (kn_dedupe [] (kn cs1)).
Definition gc_info (cs : acs) : nat * nat * nat := (nxt cs, length (kn cs), length (csvars_fo 0 cs)).
