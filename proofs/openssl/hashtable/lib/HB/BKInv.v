(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition kinv (base : acs) (J : nat) (steps : list (nat * Z)) (hav : list nat) (fd : afd) (extra : list kentry) (drop : list nat) : acs :=
  let rs0 := s_regs (a_ss base) in
  let rs1 := fold_left (fun rs p => sr_upd rs (fst p) (eadd (nth (fst p) rs (ELit 0)) (escale (snd p) (EVar J)))) steps rs0 in
  let rs2 := fold_left (fun rs r => sr_upd rs r (EVar (S J + r))) hav rs1 in
  ACS (mk_ss (pc base) rs2 (extra ++ drop_ixs drop 0 (kn base)) (S J + 32))
      (a_maps base) (a_totsz base) (a_ylo base) (a_eager base) (a_vis base) (a_ghost base) (a_abytes base) (a_brk base) fd (a_tidset base).

(* [comment removed for export] *)
Definition kcompact (s : acs) : acs := match APC.node_compact 12 s with Some c => c | None => s end.
Definition kn0 (s : acs) : nat := nxt s.
Definition kvar_of (e : expr) : nat := match e with EMd M_MUL (ELit 4096) (EVar v) => v | _ => O end.
Definition kvb (s : acs) : nat := match a_maps s with m :: _ => kvar_of (am_base m) | [] => O end.
Definition kvp (s : acs) : nat :=
  match find (fun m => match am_len m with ELit n => Z.eqb n 137439023104 | _ => false end) (a_maps s) with Some m => kvar_of (am_base m) | None => O end.
Definition kvl (s : acs) : nat := match a_fd s with FdFile _ (EVar v) _ => v | _ => O end.
