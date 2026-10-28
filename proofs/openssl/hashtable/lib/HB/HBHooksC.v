(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AsanPlanCore CxPlan HBPlanImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import CAP.
Open Scope Z_scope.
Definition MAXVA : Z := 0x7fffffffffff.
Definition MAXVA_PTRCELL : Z := 0x731510.
Definition MAXVA_PC : Z := 0x1d1b68.
Definition MAXVA_GOT : Z := 0x5deb18.      (* [comment removed for export] *)
Definition MAXVA_PTRSLOT : Z := 0x5df6a8.  (* [comment removed for export] *)

Section Checker.
Variable nx0 : nat.

(* [comment removed for export] *)
Definition node_maxva (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) MAXVA_PC) then None else
  match ret_lit cs, kreadZ HASEGS k (ELit 0) MAXVA_GOT 8, kreadZ HASEGS k (ELit 0) MAXVA_PTRSLOT 8, kread8e HASEGS k (ELit 0) MAXVA_PTRCELL with
  | Some ret, Some g, Some ptr, Some ve =>
      let sp := reg cs 2 in
      let '(spb, spk) := split_lit sp in
      match xlo k ve, xhi k ve, xlo k sp, xhi k sp with
      | Some vlo, Some vhi, Some slo, Some shi =>
          if (Z.eqb g 1 && Z.eqb ptr MAXVA_PTRCELL
              && Z.leb (2 ^ 46) vlo && Z.ltb vhi (2 ^ 47)
              && Z.leb (MAXVA_PTRCELL + 24) slo && Z.ltb shi (2 ^ 63)
              && kwritable k k spb (spk - 8) 8 && kwritable k k spb (spk - 16) 8
              && fresh_ok nx0 cs)%bool
          then
            let v := nxt cs in
            let rs := s_regs (a_ss cs) in
            let rs' := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd rs 10 (ELit MAXVA)) 11 (EVar v)) 12 (EVar (v + 1)%nat))
                                13 (EVar (v + 2)%nat)) 14 (EVar (v + 3)%nat)) 15 (EVar (v + 4)%nat) in
            let k' := KWord (SA spb (spk - 8)) 8 (reg cs 1) :: KWord (SA spb (spk - 16)) 8 (reg cs 8)
                      :: kn_havoc k spb (spk - 16) (ELit 16) in
            Some (with_ss cs (mk_ss ret rs' k' (v + 5)%nat))
          else None
      | _, _, _, _ => None
      end
  | _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition ha_xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 50 then node_maxva cs else None.
End Checker.

