(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Fixpoint e_mentions (d : list nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar n => existsb (Nat.eqb n) d
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => e_mentions d x || e_mentions d y
  | EExt _ _ _ x => e_mentions d x
  | EBlob _ _ _ _ => false
  end.
Definition sa_mentions (d : list nat) (a : saddr) : bool := e_mentions d (a_base a).
Definition sa_lit (a : saddr) : bool := match a_base a with ELit _ => true | _ => false end.
Definition k_dead (d : list nat) (K : kentry) : bool :=
  match K with
  | KWord a _ _ | KZero a _ | KBlob a _ _ | KWr a _ | KFill a _ _ | KUnk a _ => sa_mentions d a
  | KDisj a1 n1 a2 n2 =>   (* [comment removed for export] *)
      (sa_mentions d a1 && negb (sa_lit a2)) || (sa_mentions d a2 && negb (sa_lit a1)) || e_mentions d n1 || e_mentions d n2
  | KRange e _ _ => match e with EVar _ => false | _ => e_mentions d e end
  | KAlign e _ => match e with EVar _ => false | _ => e_mentions d e end
  | KImg _ _ => false
  | KInv _ _ => false
  end.
Definition gc_dead (d : list nat) (cs : acs) : acs := set_kn cs (List.filter (fun K => negb (k_dead d K)) (kn cs)).
(* [comment removed for export] *)
Fixpoint e_young (gb : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar n => Nat.leb gb n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => e_young gb x || e_young gb y
  | EExt _ _ _ x => e_young gb x
  | EBlob _ _ _ _ => false
  end.
Definition k_dead_gb (gb : nat) (d : list nat) (K : kentry) : bool :=
  match K with
  | KDisj a1 n1 a2 n2 =>
      (sa_mentions d a1 && e_young gb (a_base a2)) || (sa_mentions d a2 && e_young gb (a_base a1)) || e_mentions d n1 || e_mentions d n2
  | _ => k_dead d K
  end.
Definition gc_dead_gb (gb : nat) (d : list nat) (cs : acs) : acs := set_kn cs (List.filter (fun K => negb (k_dead_gb gb d K)) (kn cs)).
(* [comment removed for export] *)
Definition k_valdead (d : list nat) (K : kentry) : bool :=
  match K with KWord a _ v => negb (sa_mentions d a) && e_mentions d v | _ => false end.
Definition gc_census (d : list nat) (cs : acs) : nat * nat * nat * nat :=
  (length (kn cs), length (List.filter (k_dead d) (kn cs)),
   length (List.filter (fun K => match K with KDisj _ _ _ _ => k_dead d K | _ => false end) (kn cs)),
   length (List.filter (k_valdead d) (kn cs))).
