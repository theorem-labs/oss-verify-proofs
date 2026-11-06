(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib CtrA.
Open Scope Z_scope.
Unset Lia Cache.

Module CtrB.
Section WithImg.
Variable segs : list Segment.
Variable ERRNO : int.

Definition RSTAGE_ID : int := 3%uint63.
Definition new_hi (fs : list fact) (X n : sv) : sv :=
  match n with
  | VAlu ALU_SUB sz X' => if known_eq fs X' X then sz else sv_alu ALU_ADD X n
  | _ => sv_alu ALU_ADD X n
  end.

Definition rstage_apply (RS : int) (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X11, stack_ok st 0%uint63 with
  | Some r, VL rs, Some (_, klo1) =>
      if negb (weqb rs (wlit RS)) || negb (Nat.eqb (count_op RSTAGE_ID (s_ops st)) 1%nat) then None else
      match heap_windows st klo1, sym_offset (s_regs st) (getr st X10), find_op RSTAGE_ID (s_ops st) with
      | Some (_, [(kw, wlen, kd)]), Some (kb, X), Some [off; n'] =>
          if negb (PrimInt63.eqb kw kb) || negb (weqb kd K_BLOCK) then None else
          match IMap.find kb (s_regs st) with
          | Some rb =>
              match rg_cells rb with
              | IMap.Leaf =>
                  let n := getr st X12 in
                  let fs := s_facts st in
                  let hi' := new_hi fs X n in
                  if ((match rg_bg rb with BGBlob j sh => PrimInt63.eqb j 4%uint63 && PrimInt63.eqb sh 0%uint63 | _ => false end
                       && known_eq fs (rg_hi rb) X)
                      || known_eq fs X (VL wzero))
                     && PrimInt63.eqb (rg_lo rb) 0%uint63 && rg_w rb
                     && known_eq fs off X && known_eq fs n' n
                     && known_leu fs X wlen && known_leu fs n (sv_alu ALU_SUB wlen X)
                  then
                    let st1 := setregs st (IMap.add kb (Region 0%uint63 hi' true (BGBlob 4%uint63 0%uint63) IMap.empty) (s_regs st)) in
                    let st2 := set_ops st1 (set_op RSTAGE_ID [sv_alu ALU_ADD off n; VL wzero] (s_ops st1)) in
                    match havoc_errno segs ERRNO (clobber st2) with
                    | Some st3 => Some [setpc st3 r]
                    | None => None
                    end
                  else None
              | _ => None
              end
          | None => None
          end
      | _, _, _ => None
      end
  | _, _, _ => None
  end.
Definition rstage_c (RS pc : int) : contract := Contract pc (rstage_apply RS).

End WithImg.
End CtrB.
