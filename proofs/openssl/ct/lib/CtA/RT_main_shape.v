(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_state.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive lbase : Type :=
| LB_lit | LB_sp0 | LB_top | LB_PRB | LB_SB | LB_RIS (* [comment removed for export] *) | LB_PAB | LB_T | LB_TCX | LB_DTV | LB_FSB | LB_DNB | LB_SSB | LB_ACEIL (* [comment removed for export] *).

Definition den_base (L : layoutA) (b : lbase) : Z :=
  match b with
  | LB_lit => 0 | LB_sp0 => l_sp0 L | LB_top => l_top L | LB_PRB => l_PRB L | LB_SB => l_SB L | LB_RIS => l_SB L + 2 ^ 37 | LB_PAB => l_PAB L
  | LB_T => l_T L | LB_TCX => l_TCX L | LB_DTV => l_DTV L | LB_FSB => l_FSB L | LB_DNB => l_DNB L | LB_SSB => l_SSB L | LB_ACEIL => l_ACEIL L
  end.

(* [comment removed for export] *)
Inductive saddr : Type :=
| SA (b : lbase) (off : Z)
| SAsh (b : lbase) (off : Z) (shoff : Z).          (* [comment removed for export] *)

Definition den_addr (L : layoutA) (a : saddr) : Z :=
  match a with SA b off => den_base L b + off | SAsh b off shoff => shad (den_base L b + off) + shoff end.

(* [comment removed for export] *)
Inductive lnum : Type := LN_f0 | LN_tid.
Definition den_num (L : layoutA) (n : lnum) : Z := match n with LN_f0 => l_f0 L | LN_tid => l_tid L end.

(* [comment removed for export] *)
Inductive scell : Type :=
| SC_lit (w : nat) (v : Z)          (* [comment removed for export] *)
| SC_ptr (a : saddr)                (* [comment removed for export] *)
| SC_num (w : nat) (n : lnum)       (* [comment removed for export] *)
| SC_bytes (bs : list Z)            (* [comment removed for export] *)
| SC_any (n : nat).                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition wcell (w : nat) (v : Z) : cell :=
  match w with 1%nat => C1 (Z_to_bv 8 v) | 2%nat => C2 (Z_to_bv 64 v) | 4%nat => C4 (Z_to_bv 64 v) | _ => C8 (Z_to_bv 64 v) end.
Definition den_cell (L : layoutA) (c : scell) (junk : list byte) : cell :=
  match c with
  | SC_lit w v => wcell w v
  | SC_ptr a => C8 (Z_to_bv 64 (den_addr L a))
  | SC_num w n => wcell w (den_num L n)
  | SC_bytes bs => CB (length bs) (map (Z_to_bv 8) bs)
  | SC_any n => CB n junk
  end.

(* [comment removed for export] *)
Fixpoint den_cells (L : layoutA) (cs : list scell) (junks : list (list byte)) : list cell :=
  match cs with
  | [] => []
  | c :: cs' => den_cell L c (hd [] junks) :: den_cells L cs' (tl junks)
  end.
Definition rw_fact (L : layoutA) (m : mem) (e : saddr * list scell) : Prop := exists junks, rw_cells ctasegs m (den_addr L (fst e)) (den_cells L (snd e) junks).
Definition ro_fact (L : layoutA) (m : mem) (e : saddr * list scell) : Prop := exists junks, ro_cells ctasegs m (den_addr L (fst e)) (den_cells L (snd e) junks).
Definition zero_fact (L : layoutA) (m : mem) (e : saddr * Z) : Prop :=
  bytes_at ctasegs m (den_addr L (fst e)) (repeat (Z_to_bv 8 0) (Z.to_nat (snd e))) /\ wr_at ctasegs m (den_addr L (fst e)) (snd e).
Definition stk_fact (L : layoutA) (m : mem) (e : saddr * saddr) : Prop := stk ctasegs m (den_addr L (fst e)) (den_addr L (snd e)).
