(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore.
Import ListNotations.
Import AX2. Import APC.
Unset Lia Cache.
Open Scope Z_scope.

Module SLN.

Record sltab : Type := SLT { sl_entry : Z; sl_exit : Z; bs_entry : Z; bs_exit : Z }.
(* [comment removed for export] *)
Definition SL_ASAN : sltab := SLT 0x35e74 0x35f1c 0x35f68 0x35f80.
Definition SL_BOTH : sltab := SLT 0x35ea0 0x35f48 0x35f94 0x35fac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition sltab_of (A : atable) : sltab := if Z.eqb (x_memcpy A) 0x97e1c then SL_ASAN else SL_BOTH.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.
Variable T : sltab.

(* [comment removed for export] *)
Definition sl_prod (m : Z) : Z :=
  let y := 2 ^ 64 - 2 ^ (m + 1) in
  let y1 := y - Z.land (Z.shiftr y 1) 0x5555555555555555 in
  let y2 := Z.land y1 0x3333333333333333 + Z.land (Z.shiftr y1 2) 0x3333333333333333 in
  let y3 := Z.land (y2 + Z.shiftr y2 4) 0x0F0F0F0F0F0F0F0F in
  (y3 * 0x0101010101010101) mod 2 ^ 64.
Definition sl_regs (sr : list expr) (m : Z) (cell : expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 19 (ELit (63 - m))) 11 (ELit (sl_prod m))) 12 (ELit 0x0101010101010101))
          14 cell) 15 (ELit 0x0F0F0F0F0F0F0F0F)) 16 (ELit 0x01010101).

(* [comment removed for export] *)
Definition sl_regs_r (sr : list expr) (v : nat) (cell : expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 19 (EVar v)) 11 (EVar (S v))) 12 (ELit 0x0101010101010101))
          14 cell) 15 (ELit 0x0F0F0F0F0F0F0F0F)) 16 (ELit 0x01010101).

Definition node_sizelog (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (sl_entry T)) then None else
  let x := reg cs 18 in
  let '(cb, ck) := split_lit (eaddz (reg cs 9) 48) in
  match xlo k x, xhi k x with
  | Some lo, Some hi =>
    if (Z.leb 1 lo && Z.leb lo hi && Z.ltb hi two64 && flat_x k cb ck (ELit 8) && fresh_ok nx0 cs)%bool then
      match know_lookup segs k cb ck 8 false [] [] with
      | LHit v nil _ =>
          if Z.eqb (Z.log2 lo) (Z.log2 hi)
          then Some (with_ss cs (mk_ss (sl_exit T) (sl_regs (s_regs (a_ss cs)) (Z.log2 lo) (extK k v)) k (nxt cs)))
          else (* [comment removed for export] *)
            match erange k (extK k v) with
            | Some (c1, c2) =>
                if Z.eqb c1 c2 then
                  let nv := nxt cs in
                  Some (with_ss cs (mk_ss (sl_exit T) (sl_regs_r (s_regs (a_ss cs)) nv (ELit c1))
                                          (KRange (EVar nv) (63 - Z.log2 hi) (63 - Z.log2 lo) :: k) (S (S nv))))
                else None
            | None => None
            end
      | _ => None
      end
    else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition BS_WIN : Z := 520.
Definition node_bysizelog (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (bs_entry T)) then None else
  let i := reg cs 11 in
  let '(wb, wk) := split_lit (eaddz (reg cs 9) 96) in
  let k' := kn_havoc k wb wk (ELit BS_WIN) in
  match xlo k i, xhi k i, xlo k (reg cs 9), xhi k (reg cs 9) with
  | Some ilo, Some ihi, Some slo, Some shi =>
    if (Z.leb 0 ilo && Z.leb ihi 63 && Z.leb 0 slo && Z.ltb (shi + 616) two64
        && kwritable k k wb wk BS_WIN && flat_x k wb wk (ELit BS_WIN) && fresh_ok nx0 cs && kn_vars_lt (nxt cs) k')%bool then
      let nv := nxt cs in
      let sr := s_regs (a_ss cs) in
      Some (with_ss cs (mk_ss (bs_exit T) (sr_upd (sr_upd sr 11 (EVar nv)) 13 (EVar (S nv))) k' (S (S nv))))
    else None
  | _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition diag_sizelog (cs : acs) : nat :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (sl_entry T)) then 100%nat else
  let x := reg cs 18 in
  let '(cb, ck) := split_lit (eaddz (reg cs 9) 48) in
  match xlo k x, xhi k x with
  | Some lo, Some hi =>
      let tests := [Z.leb 1 lo; Z.leb lo hi; true (* [comment removed for export] *); Z.ltb hi two64; flat_x k cb ck (ELit 8); fresh_ok nx0 cs;
                    match know_lookup segs k cb ck 8 false [] [] with LHit _ nil _ => true | _ => false end]%bool in
      (fix ff (i : nat) (l : list bool) : nat := match l with [] => 0%nat | b :: l' => if b then ff (S i) l' else i end) 1%nat tests
  | _, _ => 102%nat
  end.

(* [comment removed for export] *)
Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 105 then node_sizelog cs else if Nat.eqb id 106 then node_bysizelog cs else None.
End WithSegs.
End SLN.
