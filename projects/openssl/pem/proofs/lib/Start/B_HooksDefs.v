(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanDescs AsanGcDm AsanRehash AsanRegModel AsanRegRun B_RegConsts B_Gsh AsanSort B_PlanImage B_Atable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_MAXVA : Z := 0x7fffffffffff.
Definition B_MAXVA_PC : Z := 0x1d153c.
Definition B_MAXVA_GOT : Z := 0x5dc878.         (* [comment removed for export] *)
Definition B_MAXVA_PTRSLOT : Z := 0x5dd408.     (* [comment removed for export] *)
Definition B_MAXVA_PTRCELL : Z := 0x72edd0.     (* [comment removed for export] *)

Definition B_node_maxva (nx0 : nat) (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) B_MAXVA_PC) then None else
  match ret_lit cs, kreadZ B_SEGS k (ELit 0) B_MAXVA_GOT 8, kreadZ B_SEGS k (ELit 0) B_MAXVA_PTRSLOT 8, kread8e B_SEGS k (ELit 0) B_MAXVA_PTRCELL with
  | Some ret, Some g, Some ptr, Some ve =>
      let sp := reg cs 2 in
      let '(spb, spk) := split_lit sp in
      match xlo k ve, xhi k ve, xlo k sp, xhi k sp with
      | Some vlo, Some vhi, Some slo, Some shi =>
          if (Z.eqb g 1 && Z.eqb ptr B_MAXVA_PTRCELL
              && Z.leb (2 ^ 46) vlo && Z.ltb vhi (2 ^ 47)
              && Z.leb (B_MAXVA_PTRCELL + 24) slo && Z.ltb shi (2 ^ 63)
              && kwritable k k spb (spk - 8) 8 && kwritable k k spb (spk - 16) 8
              && fresh_ok nx0 cs)%bool
          then
            let v := nxt cs in
            let rs := s_regs (a_ss cs) in
            let rs' := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd rs 10 (ELit B_MAXVA)) 11 (EVar v)) 12 (EVar (v + 1)%nat))
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
Definition B_node_descs (nx0 : nat) (cs : acs) (args : list expr) : option acs := DSC.node_descs (DSC.st_scan B_SEGS) nx0 cs args.
Definition B_node_descs_refine (nx0 : nat) (cs : acs) (args : list expr) : option acs := DSC.node_descs_refine B_SEGS (DSC.st_scan B_SEGS) nx0 cs args.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition B_RT : RHN.rtab := RHN.RT 0x1a69ec 0x69cc18.       (* [comment removed for export] *)
Definition B_xn (nx0 : nat) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 50 then B_node_maxva nx0 cs else if Nat.eqb id 60 then B_node_descs nx0 cs args
  else if Nat.eqb id 61 then B_node_descs_refine nx0 cs args
  else if Nat.eqb id 63 then GCD.node_drop_zero cs args else if Nat.eqb id 64 then GCD.node_drop_vals cs args
  else if Nat.eqb id 65 then RHN.node_rehash B_SEGS B_T nx0 B_RT cs
  (* [comment removed for export] *)
  else if Nat.eqb id 66 then RGN.node_regrun B_SEGS B_T nx0 B_RGC B_HULLS cs args
  else if Nat.eqb id 67 then HSN.node_isort B_SEGS B_T nx0 0x1bc200 cs else None.
Definition B_XN0 : nat -> list expr -> acs -> option acs := B_xn NX0.
Definition B_XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition B_XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
