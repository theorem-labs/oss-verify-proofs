(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module MVN.

Definition MOVE_ID : nat := 111.

Section Node.
  Context {fx : FPState}.
  Variable IT : itab.
  Variable A : atable.

  Definition r5 (z : Z) : bv 5 := Z_to_bv 5 z.
  Definition rq (r : bv 5) (z : Z) : bool := bv_eqb r (r5 z).

  (* [comment removed for export] *)
  Definition is_beq (r1 r2 : Z) (i : option instr) : bool :=
    match i with Some (Branch BC_EQ a b _) => rq a r1 && rq b r2 | _ => false end%bool.
  Definition bgeu_off (r1 r2 : Z) (i : option instr) : option Z :=
    match i with Some (Branch BC_GEU a b imm) => if (rq a r1 && rq b r2)%bool then Some (bv_signed imm) else None | _ => None end.
  Definition is_op (o : aluop) (rd r1 r2 : Z) (i : option instr) : bool :=
    match i with Some (Op o' d a b) => aluop_eqb o' o && rq d rd && rq a r1 && rq b r2 | _ => false end%bool.
  Definition is_slli1 (rd r1 : Z) (i : option instr) : bool :=
    match i with Some (ShiftImm o' d a sh) => aluop_eqb o' ALU_SLL && rq d rd && rq a r1 && Z.eqb (bv_unsigned sh) 1 | _ => false end%bool.
  Definition jal0_off (i : option instr) : option Z :=
    match i with Some (Jal d imm) => if rq d 0 then Some (bv_signed imm) else None | _ => None end.

  (* [comment removed for export] *)
  Definition memmove_pro (pc : Z) : option Z :=
    match bgeu_off 14 13 (itab_lookup IT (pc + 20)) with
    | Some o5 =>
        let pcJ := pc + 20 + o5 in
        match jal0_off (itab_lookup IT pcJ) with
        | Some oj =>
            if (is_beq 10 11 (itab_lookup IT pc) && is_op ALU_ADD 13 12 10 (itab_lookup IT (pc + 4))
                && is_slli1 14 12 (itab_lookup IT (pc + 8)) && is_op ALU_SUB 13 11 13 (itab_lookup IT (pc + 12))
                && is_op ALU_SUB 14 0 14 (itab_lookup IT (pc + 16))
                && Z.eqb (pcJ + oj) (x_memcpy A) && Z.leb 0 pc && Z.ltb (pc + 24) two64
                && Z.leb 0 pcJ && Z.ltb (pcJ + 4) two64 && Z.leb 0 (x_memcpy A) && Z.ltb (x_memcpy A) two64)%bool
            then Some (x_memcpy A) else None
        | None => None
        end
    | None => None
    end.

  Definition xn (args : list expr) (cs : acs) : option acs :=
    match args with
    | [] =>
        match memmove_pro (pc cs) with
        | Some tgt =>
            let k := kn cs in
            let d := reg cs 10 in let s := reg cs 11 in let n := reg cs 12 in
            let '(db, dk) := split_lit d in let '(sb, sk) := split_lit s in
            match xlo k n, xhi k n with
            | Some nlo, Some nhi =>
                if (Z.leb 1 nlo && Z.leb nhi (2 ^ 62) && flat_x k db dk n && flat_x k sb sk n && ranges_apart_x k db dk n sb sk n
                    && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
                then
                  let ss := a_ss cs in
                  (* [comment removed for export] *)
                  let sr0 := s_regs ss in
                  let sr1 := sr_upd sr0 13 (mkAlu ALU_ADD (sr_get sr0 12) (sr_get sr0 10)) in
                  let sr2 := sr_upd sr1 14 (mkAlu ALU_SLL (sr_get sr1 12) (ELit 1)) in
                  let sr3 := sr_upd sr2 13 (mkAlu ALU_SUB (sr_get sr2 11) (sr_get sr2 13)) in
                  let sr4 := sr_upd sr3 14 (mkAlu ALU_SUB (sr_get sr3 0) (sr_get sr3 14)) in
                  Some (with_ss cs (mk_ss tgt sr4 (s_know ss) (s_next ss)))
                else None
            | _, _ => None
            end
        | None => None
        end
    | _ => None
    end.
End Node.
End MVN.
