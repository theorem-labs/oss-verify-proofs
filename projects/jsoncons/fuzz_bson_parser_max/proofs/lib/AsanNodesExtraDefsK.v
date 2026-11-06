(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2K. Import APCK.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.

Definition node_absbytes (cs : acs) (b : expr) (off : Z) (n : nat) : option acs :=
  let k := kn cs in
  if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) b && Nat.leb 1 n && Nat.leb n 8
      && (kn_readable segs k k b off n || kwritable k k b off (Z.of_nat n)))%bool then   (* [comment removed for export] *)
    let v := nxt cs in
    Some (set_kn (bump cs 1) (KWord (SA b off) n (EVar v) :: KRange (EVar v) 0 (2 ^ (8 * Z.of_nat n) - 1) :: k))
  else None.

(* [comment removed for export] *)
Definition xn_absbytes (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; ELit n] => if Z.leb 0 n then node_absbytes cs b off (Z.to_nat n) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition smearva_vals : list Z :=
  [140737488355327; 18446744073709551615; 3689348814741910323; 1085102592571150095; 72340172838076673; 9223301668110598144].

Definition node_smearva (base : Z) (cs : acs) : option acs :=
  let k := kn cs in
  match xlo k (reg cs 10), xhi k (reg cs 10) with
  | Some lo, Some hi =>
      if (Z.eqb (pc cs) base && Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool then
        Some (set_pc (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg cs
                 10 (ELit (nth 0 smearva_vals 0))) 11 (ELit (nth 1 smearva_vals 0))) 12 (ELit (nth 2 smearva_vals 0)))
                 13 (ELit (nth 3 smearva_vals 0))) 14 (ELit (nth 4 smearva_vals 0))) 15 (ELit (nth 5 smearva_vals 0)))
                 (base + 180))
      else None
  | _, _ => None
  end.

Definition xn_smearva (base : Z) (args : list expr) (cs : acs) : option acs :=
  match args with [] => node_smearva base cs | _ => None end.

(* [comment removed for export] *)
Record aim_params := mkAIM {
  aim_entry : Z;                              (* [comment removed for export] *)
  aim_got1 : Z; aim_got2 : Z; aim_got3 : Z;   (* [comment removed for export] *)
  aim_g1 : Z; aim_g2 : Z; aim_g3 : Z          (* [comment removed for export] *)
}.
Definition aim_regs : list nat := [14; 15; 16; 17; 5; 6; 7; 28]%nat.
Definition aim_cell (k : list kentry) (c v : Z) : bool :=
  (Z.leb 0 c && Z.ltb (c + 8) two64 && match kreadZ segs k (ELit 0) c 8 with Some z => Z.eqb z v | None => false end)%bool.
Definition node_addrisinmem (prm : aim_params) (cs : acs) : option acs :=
  let k := kn cs in
  let '(b, off) := split_lit (reg cs 10) in
  match reg cs 11, reg cs 9, reg cs 14, base_range k b with
  | ELit n, ELit s1, ELit a4, Some (lo, hi) =>
      if (Z.eqb (pc cs) (aim_entry prm) && Z.eqb s1 0x7fff8000 && Z.eqb a4 0x7fff7fff
          && Z.leb 8 n && Z.ltb n two64 && Z.eqb (n mod 8) 0
          && Z.leb 0 (lo + off) && Z.leb (hi + off + n) (2 ^ 47)
          && ranges_apart k b off n (ELit 0) 0x7fff7000 0x100000001000          (* [comment removed for export] *)
          && aim_cell k (aim_got1 prm) (aim_g1 prm) && aim_cell k (aim_got2 prm) (aim_g2 prm) && aim_cell k (aim_got3 prm) (aim_g3 prm)
          && aim_cell k (aim_g1 prm) 0 && aim_cell k (aim_g2 prm) 0 && aim_cell k (aim_g3 prm) (2 ^ 47 - 1))%bool
      then match node_havoc nx0 (set_reg cs 11 (eaddz (eadd (reg cs 10) (reg cs 11)) (-8))) aim_regs with
           | Some cs1 => Some (set_pc cs1 (aim_entry prm + 0x22c))
           | None => None
           end
      else None
  | _, _, _, _ => None
  end.

Definition xn_addrisinmem (prm : aim_params) (args : list expr) (cs : acs) : option acs :=
  match args with [] => node_addrisinmem prm cs | _ => None end.
End WithSegs.
