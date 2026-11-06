(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.

Module Asankdu.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition MSB_A0 : Z := 0x7fffffffffff.         (* [comment removed for export] *)
Definition MSB_A1 : Z := 0x5555555555555555.
Definition MSB_A2 : Z := 0x3333333333333333.
Definition MSB_A3 : Z := 0x0f0f0f0f0f0f0f0f.
Definition MSB_A4 : Z := 0x0101010101010101.
Definition MSB_A5 : Z := 0x7fff.
Definition MSB_LEN : Z := 0x70.                  (* [comment removed for export] *)

Definition xn_msb (msbpc : Z) (cs : acs) : option acs :=
  if Z.eqb (pc cs) msbpc then
    match xlo (kn cs) (reg cs 10), xhi (kn cs) (reg cs 10) with
    | Some lo, Some hi =>
        if (Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool then
          Some (set_pc (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg cs
                  10 (ELit MSB_A0)) 11 (ELit MSB_A1)) 12 (ELit MSB_A2)) 13 (ELit MSB_A3)) 14 (ELit MSB_A4)) 15 (ELit MSB_A5))
                  (msbpc + MSB_LEN))
        else None
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Fixpoint bytes_hit (segs : list Segment) (k : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match know_lookup segs k b off 1 false [] [] with
            | LHit _ [] _ => bytes_hit segs k b (off + 1) n'
            | _ => false
            end
  end.

(* [comment removed for export] *)
Definition xn_wordcell (segs : list Segment) (nx0 : nat) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; ELit n] =>
      let w := Z.to_nat n in
      if (Z.leb 1 n && Z.leb n 8 && fresh_ok nx0 cs && expr_vars_lt (nxt cs) b
          && flat_x (kn cs) b off (ELit n) && bytes_hit segs (kn cs) b off w)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KWord (SA b off) w (EVar v) :: s_know ss) (S v))
                 (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint qc_cover (allk k : list kentry) (b : expr) (o : Z) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      (xinside allk b (o - 7) (ELit 8) zb zk zn && Z.leb 3 (ealign allk (eaddz (eadd zb zn) zk))) || qc_cover allk rest b o
  | _ :: rest => qc_cover allk rest b o
  end.
(* [comment removed for export] *)
Definition qc_fact (k fk : list kentry) (r : expr) : list kentry :=
  let '(b, o) := split_lit r in
  if qc_cover k k b o then
    let '(c, q) := split_lit (mkAluK fk Instr.ALU_AND r (ELit (-8))) in
    if flat_x k c q (ELit 8) then [KZero (SA c q) (ELit 8)] else []
  else [].
Definition xn_qczero (cs : acs) : option acs :=
  let k := kn cs in let fk := facts_of k in
  Some (set_kn cs (qc_fact k fk (reg cs 13) ++ qc_fact k fk (reg cs 14) ++ k)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition two_atom (ts : list (Z * expr)) (x y : expr) : option (Z * Z) :=
  match ts with
  | [(k1, a1); (k2, a2)] =>
      if (expr_eqb a1 x && expr_eqb a2 y)%bool then Some (k1, k2)
      else if (expr_eqb a1 y && expr_eqb a2 x)%bool then Some (k2, k1) else None
  | _ => None
  end.
(* [comment removed for export] *)
Fixpoint find_fact2 (allk k : list kentry) (x y : expr) {struct k} : option (Z * Z * Z * Z) :=
  match k with
  | [] => None
  | KRange e lo hi :: rest =>
      match two_atom (snd (lin_of e)) x y with
      | Some (kx, ky) => if fact_nowrap allk e hi then Some (kx, ky, lo - fst (lin_of e), hi - fst (lin_of e)) else find_fact2 allk rest x y
      | None => find_fact2 allk rest x y
      end
  | _ :: rest => find_fact2 allk rest x y
  end.
Definition xn_pgdiff (args : list expr) (cs : acs) : option acs :=
  match args with
  | [EVar v; EVar w; EVar x; ELit c] =>
      let k := kn cs in
      match find_fact2 k k (EVar x) (EVar v), find_fact2 k k (EVar x) (EVar w) with
      | Some (kx1, kv, l1, h1), Some (kx2, kw, l2, h2) =>
          if (Z.eqb kx1 kx2 && Z.eqb kv (- c) && Z.eqb kw (- c) && Z.ltb 0 c && negb (Nat.eqb v w))%bool then
            let a := zcdiv (l2 - h1) c in let b := (h2 - l1) / c in
            if (Z.leb 0 a && Z.leb a b && Z.ltb b two64)%bool then Some (set_kn cs (KRange (esub (EVar v) (EVar w)) a b :: k)) else Some cs
          else Some cs
      | _, _ => Some cs
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition XN1 (segs : list Segment) (A : atable) (nx0 : nat) (msbpc : Z) (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with 1%nat => xn_msb msbpc cs | 2%nat => xn_wordcell segs nx0 args cs | 3%nat => xn_qczero cs | 5%nat => xn_pgdiff args cs | _ => None end.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

(* [comment removed for export] *)
Definition MSB_PC_ASAN : Z := 0x6b8d8.
Definition MSB_PC_BOTH : Z := 0x6b7b8.   (* [comment removed for export] *)
Definition XNa (nx0 : nat) := XN1 Asan.M.loaded_segments ASAN nx0 MSB_PC_ASAN.
Definition XNb (nx0 : nat) := XN1 AsanUbsan.M.loaded_segments BOTH nx0 MSB_PC_BOTH.
End Asankdu.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition cut_cell1 (b : expr) (off : Z) (n : nat) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      match b with
      | ELit 0 =>
          if (Z.leb lo off && Z.leb (off + Z.of_nat n) hi)%bool then
            (if Z.ltb lo (Z.min off hi) then [KImg lo (Z.min off hi)] else [])
            ++ (let lo2 := Z.max lo (off + Z.of_nat n) in if Z.ltb lo2 hi then [KImg lo2 hi] else [])
          else [K]
      | _ => [K]
      end
  | KZero (SA zb zk) (ELit l0) =>
      if (expr_eqb zb b && Z.leb zk off && Z.leb (off + Z.of_nat n) (zk + l0) && Z.leb 0 l0 && Z.ltb l0 two64)%bool
      then ktrim KZero zb zk l0 off n else [K]
  | _ => [K]
  end.

Definition xn_cell (segs : list Segment) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; ELit n] =>
      let w := Z.to_nat n in
      if (Z.leb 1 n && Z.leb n 8 && flat_x (kn cs) b off (ELit n))%bool then
        match know_lookup segs (kn cs) b off w false [] [] with
        | LHit v [] _ => Some (set_kn cs (KWord (SA b off) w v :: flat_map (cut_cell1 b off w) (kn cs)))
        | _ => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint respell_first (allk k : list kentry) (a : saddr) (e : expr) : option (list kentry) :=
  match k with
  | [] => None
  | KWord a' w v :: r =>
      if saddr_eqb a' a then (if respell_ok allk v e then Some (KWord a' w e :: r) else None)
      else match respell_first allk r a e with Some r' => Some (KWord a' w v :: r') | None => None end
  | K :: r => match respell_first allk r a e with Some r' => Some (K :: r') | None => None end
  end.

Definition xn_respell_cell (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; e] =>
      if expr_vars_lt (nxt cs) e then
        match respell_first (kn cs) (kn cs) (SA b off) e with
        | Some k' => Some (set_kn cs k')
        | None => None
        end
      else None
  | _ => None
  end.

Definition BITPIN_MAX : Z := 2 ^ 62.
Definition xn_bitpin (args : list expr) (cs : acs) : option acs :=
  match args with
  | [X; EVar b; ELit k] =>
      let k0 := kn cs in
      let e2 := esub X (escale k (EVar b)) in
      match xlo k0 X, xhi k0 X, xlo k0 e2, xhi k0 e2, xhi k0 (EVar b) with
      | Some lo1, Some hi1, Some lo2, Some hi2, Some bh =>
          if (Z.ltb 0 k && Z.ltb k BITPIN_MAX && Z.leb 0 bh && Z.ltb (k * bh) BITPIN_MAX
              && Z.ltb hi1 BITPIN_MAX && Z.ltb hi2 BITPIN_MAX)%bool then
            let a := Z.max 0 (zcdiv (lo1 - hi2) k) in
            let c := Z.min bh ((hi1 - lo2) / k) in
            if Z.leb a c then Some (set_kn cs (KRange (EVar b) a c :: k0)) else None
          else None
      | _, _, _, _, _ => None
      end
  | _ => None
  end.


(* [comment removed for export] *)
Fixpoint take_kword0 (k : list kentry) (a : saddr) (w : nat) : option (list kentry) :=
  match k with
  | [] => None
  | KWord a' w' v :: r =>
      if saddr_eqb a' a then (match v with ELit 0 => if Nat.eqb w' w then Some r else None | _ => None end)
      else match take_kword0 r a w with Some r' => Some (KWord a' w' v :: r') | None => None end
  | K :: r => match take_kword0 r a w with Some r' => Some (K :: r') | None => None end
  end.
Fixpoint take_kzero (k : list kentry) (a : saddr) : option (Z * list kentry) :=
  match k with
  | [] => None
  | KZero a' (ELit m) :: r =>
      if saddr_eqb a' a then Some (m, r)
      else match take_kzero r a with Some (m', r') => Some (m', KZero a' (ELit m) :: r') | None => None end
  | K :: r => match take_kzero r a with Some (m', r') => Some (m', K :: r') | None => None end
  end.
Definition xn_zjoin (A : atable) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; ELit n] =>
      let w := Z.to_nat n in
      if (Z.leb 1 n && Z.leb n 8 && Z.leb (img_lo A) (img_hi A) && flat_x (kn cs) b off (ELit n) && off_image_x A (kn cs) b off (ELit n))%bool then
        match take_kword0 (kn cs) (SA b off) w with
        | Some k1 =>
            match take_kzero k1 (SA b (off + n)) with
            | Some (m, k2) => if (Z.leb 0 m && Z.ltb (n + m) two64)%bool then Some (set_kn cs (KZero (SA b off) (ELit (n + m)) :: k2)) else None
            | None => None
            end
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition XN2 (segs : list Segment) (A : atable) (nx0 : nat) (msbpc : Z) (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 6%nat => xn_cell segs args cs
  | 7%nat => xn_respell_cell args cs
  | 8%nat => xn_bitpin args cs
  | 9%nat => xn_zjoin A args cs
  | _ => XN1 segs A nx0 msbpc id args cs
  end.
Definition XNa2 (nx0 : nat) := XN2 Asan.M.loaded_segments ASAN nx0 MSB_PC_ASAN.
