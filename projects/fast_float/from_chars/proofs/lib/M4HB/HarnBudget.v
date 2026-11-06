(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HarnLoop HarnSite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition UKEY : positive := 48.
Definition NUSE : Z := 3.
(* [comment removed for export] *)
Definition MARKU : Z := 7919.
Definition MARKC : Z := 7907.
Definition sgnz (k : Z) : Z := if Z.ltb k 9223372036854775808 then k else k - 18446744073709551616.
Definition rU (S : sst) : lin :=
  match List.flat_map (fun f => match f with FRange (LIN 0 [(v, k)]) _ _ => if Z.eqb k MARKU then [lvar v] else [] | _ => [] end) (s_facts S) with
  | l :: _ => l
  | [] => lconst 0
  end.
Definition rC (S : sst) : lin :=
  match List.flat_map (fun f => match f with
                                | FRange (LIN c [(v, k)]) _ _ => if (Z.eqb k MARKC && Z.eqb (sgnz c mod MARKC) 0)%bool then [laddc (lvar v) (sgnz c / MARKC)] else []
                                | _ => [] end) (s_facts S) with
  | l :: _ => l
  | [] => lconst 0
  end.
Definition blin (S : sst) (l : lin) (d D : Z) : lin := ladd (ladd l (lscale D (rC S))) (lsub (lconst (NUSE * d)) (lscale d (rU S))).

(* [comment removed for export] *)
Definition stat_base (S : sst) : option lin :=
  match List.filter (fun R => match is_const (rg_size R), l_t (rg_base R) with Some 72, _ :: _ => Z.eqb (l_c (rg_base R)) 2800 | _, _ => false end) (s_rgs S) with
  | R :: _ => Some (rg_base R)
  | [] => None
  end.
Definition stat_at (o : Z) (S : sst) : option lin := match stat_base S with Some b => Some (laddc b o) | None => None end.
(* [comment removed for export] *)
Fixpoint pri_pos_b (l : list lin) (i : nat) : option nat :=
  match l with
  | x :: ((y :: _) as t) => match ldivz x 8 with
                            | Some x8 => if lin_eqb y (laddc x8 2147450880) then Some i else pri_pos_b t (S i)
                            | None => pri_pos_b t (S i)
                            end
  | _ => None
  end.

(* [comment removed for export] *)
Definition DOF (dt : Z * Z) : Z := NUSE * fst dt + snd dt.
Definition pri_tab : list (nat * (Z * Z)) :=
  List.map (fun c => ((5 + 2 * (c - 1))%nat, (2, 2))) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat ++ [(66%nat, (2, 4)); (67%nat, (320, 640))].
Definition nl_tab : Z * Z := (4, 6).
Definition cell_tab : list ((sst -> option lin) * (Z * Z)) :=
  [((fun S => Some (laddc (FSof S) 16)), (0, 1)); ((fun S => Some (FSof S)), (1, 0))].      (* [comment removed for export] *)      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition bslots (P : sst) (als : list lin) : list (lin * Z * Z) :=
  (match als with nl :: _ => [(nl, fst nl_tab, DOF nl_tab)] | [] => [] end) ++
  (match pri_pos_b als O with
   | Some p => List.flat_map (fun '(i, dt) => match nth_error als (p + i) with Some l => [(l, fst dt, DOF dt)] | None => [] end) pri_tab
   | None => [] end) ++
  List.flat_map (fun '(a, dt) => match a P with Some ad => match cell P ad with Some l => [(l, fst dt, DOF dt)] | None => [] end | None => [] end) cell_tab.
(* [comment removed for export] *)
Definition hl_budget (P : sst) (als : list lin) : list lin := List.map (fun '(l, d, D) => blin P l d D) (bslots P als).

(* [comment removed for export] *)
Definition slot_vars (P : sst) (als : list lin) : list positive :=
  List.flat_map (fun '(l, _, _) => match l with LIN 0 [(v, 1)] => [v] | _ => [] end) (bslots P als).
(* [comment removed for export] *)
Definition SLOT_MAX : Z := 1099511627776.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_cells : list (sst -> option lin) := [stat_at 0; stat_at 8; stat_at 16; stat_at 24; stat_at 32].
Definition free_vars (P : sst) : list positive :=
  List.flat_map (fun a => match a P with Some ad => match cell P ad with Some (LIN _ [(v, 1)]) => [v] | _ => [] end | None => [] end) free_cells.
Definition mentions (vs : list positive) (f : fact) : bool := existsb (fun x => existsb (Pos.eqb x) vs) (FxChMain.fact_vars f).
Definition drop_slot_abs (P : sst) (als : list lin) : sst :=
  let vs := slot_vars P als in let fv := free_vars P in
  SST (s_pc P) (s_regs P) (s_rgs P)
      (List.map (fun v => FRange (lvar v) 0 SLOT_MAX)
         (List.filter (fun v => existsb (fun f => match f with FRange (LIN 0 [(w, 1)]) _ hi => (Pos.eqb v w && Z.leb hi SLOT_MAX)%bool | _ => false end) (s_facts P)) vs) ++      (* [comment removed for export] *)
       List.filter (fun f => negb (mentions fv f)) (List.filter (fun f => match f with FRange (LIN 0 [(v, 1)]) _ _ => negb (existsb (Pos.eqb v) vs) | _ => true end) (s_facts P)))
      (s_next P) (s_resv P).
(* [comment removed for export] *)
