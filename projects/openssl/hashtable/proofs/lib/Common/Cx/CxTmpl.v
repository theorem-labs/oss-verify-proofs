(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import CAP.
Open Scope Z_scope.

Definition memo : Type := list (expr * expr * nat).
Definition memo_find (tb : memo) (e1 e2 : expr) : option nat :=
  match List.find (fun t => expr_eqb (fst (fst t)) e1 && expr_eqb (snd (fst t)) e2)%bool tb with Some t => Some (snd t) | None => None end.

Section AU.
Variable vs : nat.
Variable create : bool.   (* [comment removed for export] *)

Fixpoint au_e (e1 e2 : expr) (tb : memo) {struct e1} : option (expr * memo) :=
  if expr_eqb e1 e2 then Some (e1, tb) else
  let var := match memo_find tb e1 e2 with
             | Some x => Some (EVar x, tb)
             | None => if create then let x := (vs + length tb)%nat in Some (EVar x, (e1, e2, x) :: tb) else None
             end in
  match e1, e2 with
  | EAlu o1 a1 b1, EAlu o2 a2 b2 =>
      if aluop_eqb o1 o2 then
        match au_e a1 a2 tb with
        | Some (a, tb1) => match au_e b1 b2 tb1 with Some (b, tb2) => Some (EAlu o1 a b, tb2) | None => var end
        | None => var
        end
      else var
  | EMd o1 a1 b1, EMd o2 a2 b2 =>
      if mulop_eqb o1 o2 then
        match au_e a1 a2 tb with
        | Some (a, tb1) => match au_e b1 b2 tb1 with Some (b, tb2) => Some (EMd o1 a b, tb2) | None => var end
        | None => var
        end
      else var
  | _, _ => var
  end.
End AU.

Definition au_new (vs : nat) := au_e vs true.
Definition au_old (vs : nat) := au_e vs false.

Fixpoint au_list (vs : nat) (l1 l2 : list expr) (tb : memo) : option (list expr * memo) :=
  match l1, l2 with
  | [], [] => Some ([], tb)
  | a :: r1, b :: r2 => match au_new vs a b tb with
                        | Some (e, tb1) => match au_list vs r1 r2 tb1 with Some (r, tb2) => Some (e :: r, tb2) | None => None end
                        | None => None end
  | _, _ => None
  end.

Definition au_addr (vs : nat) (a1 a2 : saddr) (tb : memo) : option saddr :=
  if Z.eqb (a_off a1) (a_off a2) then match au_old vs (a_base a1) (a_base a2) tb with Some (b, _) => Some (SA b (a_off a1)) | None => None end else None.
Definition au_len (vs : nat) (n1 n2 : expr) (tb : memo) : option expr :=
  match au_old vs n1 n2 tb with Some (n, _) => Some n | None => None end.

(* [comment removed for export] *)
Definition au_k (vs : nat) (K1 K2 : kentry) (tb : memo) : option (kentry * memo) :=
  match K1, K2 with
  | KWord a1 w1 v1, KWord a2 w2 v2 =>
      if Nat.eqb w1 w2 then match au_addr vs a1 a2 tb with
                            | Some a => match au_new vs v1 v2 tb with Some (v, tb') => Some (KWord a w1 v, tb') | None => None end
                            | None => None end else None
  | KZero a1 n1, KZero a2 n2 => match au_addr vs a1 a2 tb, au_len vs n1 n2 tb with Some a, Some n => Some (KZero a n, tb) | _, _ => None end
  | KUnk a1 n1, KUnk a2 n2 => match au_addr vs a1 a2 tb, au_len vs n1 n2 tb with Some a, Some n => Some (KUnk a n, tb) | _, _ => None end
  | KWr a1 n1, KWr a2 n2 => match au_addr vs a1 a2 tb, au_len vs n1 n2 tb with Some a, Some n => Some (KWr a n, tb) | _, _ => None end
  | KBlob a1 n1 k1, KBlob a2 n2 k2 => if Nat.eqb k1 k2 then match au_addr vs a1 a2 tb, au_len vs n1 n2 tb with Some a, Some n => Some (KBlob a n k1, tb) | _, _ => None end else None
  | KFill a1 n1 c1, KFill a2 n2 c2 => if Z.eqb c1 c2 then match au_addr vs a1 a2 tb, au_len vs n1 n2 tb with Some a, Some n => Some (KFill a n c1, tb) | _, _ => None end else None
  | KDisj a1 n1 b1 m1, KDisj a2 n2 b2 m2 =>
      match au_addr vs a1 a2 tb, au_len vs n1 n2 tb, au_addr vs b1 b2 tb, au_len vs m1 m2 tb with
      | Some a, Some n, Some b, Some m => Some (KDisj a n b m, tb) | _, _, _, _ => None end
  | KRange e1 lo1 hi1, KRange e2 lo2 hi2 => match au_len vs e1 e2 tb with Some e => Some (KRange e (Z.min lo1 lo2) (Z.max hi1 hi2), tb) | None => None end
  | KAlign e1 m1, KAlign e2 m2 => if Z.eqb m1 m2 then match au_len vs e1 e2 tb with Some e => Some (KAlign e m1, tb) | None => None end else None
  | KImg lo1 hi1, KImg lo2 hi2 => if (Z.eqb lo1 lo2 && Z.eqb hi1 hi2)%bool then Some (K1, tb) else None
  | _, _ => None
  end.

Fixpoint au_first0 (vs : nat) (K1 : kentry) (k2 : list kentry) (tb : memo) : option (kentry * memo) :=
  match k2 with
  | [] => None
  | K2 :: r => match au_k vs K1 K2 tb with Some x => Some x | None => au_first0 vs K1 r tb end
  end.
(* [comment removed for export] *)
Definition addr_same (a b : saddr) : bool := (Z.eqb (a_off a) (a_off b) && expr_eqb (a_base a) (a_base b))%bool.
Definition same_key (K1 K2 : kentry) : bool :=
  match K1, K2 with
  | KWord a1 w1 _, KWord a2 w2 _ => (Nat.eqb w1 w2 && addr_same a1 a2)%bool
  | KZero a1 _, KZero a2 _ | KUnk a1 _, KUnk a2 _ | KWr a1 _, KWr a2 _ | KBlob a1 _ _, KBlob a2 _ _ | KFill a1 _ _, KFill a2 _ _ => addr_same a1 a2
  | KDisj a1 _ b1 _, KDisj a2 _ b2 _ => (addr_same a1 a2 && addr_same b1 b2)%bool
  | KRange e1 _ _, KRange e2 _ _ => expr_eqb e1 e2
  | KAlign e1 _, KAlign e2 _ => expr_eqb e1 e2
  | KImg _ _, KImg _ _ => true
  | _, _ => false
  end.
Definition au_first (vs : nat) (K1 : kentry) (k2 : list kentry) (tb : memo) : option (kentry * memo) :=
  match au_first0 vs K1 (List.filter (same_key K1) k2) tb with
  | Some x => Some x
  | None => au_first0 vs K1 k2 tb
  end.
Fixpoint au_kn (vs : nat) (k1 k2 : list kentry) (tb : memo) : list kentry * memo :=
  match k1 with
  | [] => ([], tb)
  | K1 :: r => match au_first vs K1 k2 tb with
               | Some (K, tb1) => let (kr, tb2) := au_kn vs r k2 tb1 in (K :: kr, tb2)
               | None => au_kn vs r k2 tb
               end
  end.

Fixpoint au_maps (vs : nat) (m1 m2 : list amap) (tb : memo) : option (list amap * memo) :=
  match m1, m2 with
  | [], [] => Some ([], tb)
  | a :: r1, b :: r2 =>
      if mkind_eqb (am_kind a) (am_kind b) then
        match au_new vs (am_base a) (am_base b) tb with
        | Some (ba, tb1) => match au_new vs (am_len a) (am_len b) tb1 with
                            | Some (le, tb2) => match au_maps vs r1 r2 tb2 with Some (r, tb3) => Some (AM ba le (am_kind a) :: r, tb3) | None => None end
                            | None => None end
        | None => None end
      else None
  | _, _ => None
  end.
Fixpoint au_pairs (vs : nat) (p1 p2 : list (expr * expr)) (tb : memo) : option (list (expr * expr) * memo) :=
  match p1, p2 with
  | [], [] => Some ([], tb)
  | a :: r1, b :: r2 =>
      match au_new vs (fst a) (fst b) tb with
      | Some (x, tb1) => match au_new vs (snd a) (snd b) tb1 with
                         | Some (y, tb2) => match au_pairs vs r1 r2 tb2 with Some (r, tb3) => Some ((x, y) :: r, tb3) | None => None end
                         | None => None end
      | None => None end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition au_state (vs top : nat) (c1 c2 : acs) : option (acs * list (nat * expr) * list (nat * expr)) :=
  if negb (Z.eqb (pc c1) (pc c2) && afd_eqb (a_fd c1) (a_fd c2) && Bool.eqb (a_tidset c1) (a_tidset c2))%bool then None else
  match au_maps vs (a_maps c1) (a_maps c2) [] with
  | Some (ms, tb1) =>
    match au_pairs vs (a_vis c1) (a_vis c2) tb1 with
    | Some (vis, tb2) =>
      match au_pairs vs (a_ghost c1) (a_ghost c2) tb2 with
      | Some (gh, tb3) =>
        match au_list vs (s_regs (a_ss c1)) (s_regs (a_ss c2)) tb3 with
        | Some (regs, tb4) =>
          match au_new vs (a_brk c1) (a_brk c2) tb4 with
          | Some (brk, tb5) =>
              let (k, tb6) := au_kn vs (kn c1) (kn c2) tb5 in
              Some (ACS (mk_ss (pc c1) regs k top) ms (Z.max (a_totsz c1) (a_totsz c2)) (Z.min (a_ylo c1) (a_ylo c2))
                        (Z.max (a_eager c1) (a_eager c2)) vis gh (Z.max (a_abytes c1) (a_abytes c2)) brk (a_fd c1) (a_tidset c1),
                    List.map (fun t => (snd t, fst (fst t))) tb6, List.map (fun t => (snd t, snd (fst t))) tb6)
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.
