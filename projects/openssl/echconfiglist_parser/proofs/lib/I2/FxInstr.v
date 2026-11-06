(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive finstr : Type :=
| FLi (rd : int) (v : w64)                                  (* [comment removed for export] *)
| FJal (rd : int) (tgt : int) (link : w64)
| FJalr (rd rs1 : int) (imm link : w64)
| FBranch (c : branch_cond) (rs1 rs2 : int) (tgt npc : int)
| FLoad (sz : msize) (sgn : bool) (rd rs1 : int) (imm : w64)
| FStore (sz : msize) (rs1 rs2 : int) (imm : w64)
| FOpImm (op : aluop) (rd rs1 : int) (imm : w64)            (* [comment removed for export] *)
| FOp (op : aluop) (rd rs1 rs2 : int)
| FOpImm32 (op : aluop) (rd rs1 : int) (imm : w64)          (* [comment removed for export] *)
| FOp32 (op : aluop) (rd rs1 rs2 : int)
| FMul (op : mulop) (rd rs1 rs2 : int)
| FMul32 (op : mulop) (rd rs1 rs2 : int)
| FLr (wd : awidth) (rd rs1 : int)
| FSc (wd : awidth) (rd rs1 rs2 : int)
| FAmo (op : amoop) (wd : awidth) (rd rs1 rs2 : int)
| FNop
| FEcall.

(* [comment removed for export] *)
Definition ireg (r : reg) : int := of_Z (bv_unsigned r).

(* [comment removed for export] *)
Definition pc_bound : Z := 2 ^ 62.

(* [comment removed for export] *)
Definition pc_of_word (w : word) : option int :=
  if (bv_unsigned w <? pc_bound)%Z then Some (of_Z (bv_unsigned w)) else None.

Definition uimm (imm : bv 20) : word := sext 64 (bv_concat 32 imm (Z_to_bv 12 0)).

Definition compile (pc : Z) (i : instr) : option finstr :=
  let pcw : word := Z_to_bv 64 pc in
  let npcw : word := bv_add pcw (Z_to_bv 64 4) in
  match i with
  | Lui rd imm => Some (FLi (ireg rd) (w_of_bv (uimm imm)))
  | Auipc rd imm => Some (FLi (ireg rd) (w_of_bv (bv_add pcw (uimm imm))))
  | Jal rd imm =>
      match pc_of_word (bv_add pcw (sext 64 imm)) with
      | Some t => Some (FJal (ireg rd) t (w_of_bv npcw))
      | None => None
      end
  | Jalr rd rs1 imm => Some (FJalr (ireg rd) (ireg rs1) (w_of_bv (sext 64 imm)) (w_of_bv npcw))
  | Branch bc rs1 rs2 imm =>
      match pc_of_word (bv_add pcw (sext 64 imm)), pc_of_word npcw with
      | Some t, Some n => Some (FBranch bc (ireg rs1) (ireg rs2) t n)
      | _, _ => None
      end
  | Load msz sgn rd rs1 imm => Some (FLoad msz sgn (ireg rd) (ireg rs1) (w_of_bv (sext 64 imm)))
  | Store msz rs1 rs2 imm => Some (FStore msz (ireg rs1) (ireg rs2) (w_of_bv (sext 64 imm)))
  | OpImm op rd rs1 imm => Some (FOpImm op (ireg rd) (ireg rs1) (w_of_bv (sext 64 imm)))
  | ShiftImm op rd rs1 shamt => Some (FOpImm op (ireg rd) (ireg rs1) (w_of_bv (zext 64 shamt)))
  | Op op rd rs1 rs2 => Some (FOp op (ireg rd) (ireg rs1) (ireg rs2))
  | OpImm32 rd rs1 imm => Some (FOpImm32 ALU_ADD (ireg rd) (ireg rs1) (w_of_bv (sext 64 imm)))
  | ShiftImm32 op rd rs1 shamt => Some (FOpImm32 op (ireg rd) (ireg rs1) (w_of_bv (zext 64 shamt)))
  | Op32 op rd rs1 rs2 => Some (FOp32 op (ireg rd) (ireg rs1) (ireg rs2))
  | Fence _ _ _ _ _ | FenceI _ _ _ => Some FNop
  | Mul op rd rs1 rs2 => Some (FMul op (ireg rd) (ireg rs1) (ireg rs2))
  | Mul32 op rd rs1 rs2 => Some (FMul32 op (ireg rd) (ireg rs1) (ireg rs2))
  | Lr wd _ _ rd rs1 => Some (FLr wd (ireg rd) (ireg rs1))
  | Sc wd _ _ rd rs1 rs2 => Some (FSc wd (ireg rd) (ireg rs1) (ireg rs2))
  | Amo op wd _ _ rd rs1 rs2 => Some (FAmo op wd (ireg rd) (ireg rs1) (ireg rs2))
  | _ => None
  end.

(* [comment removed for export] *)
Definition build_entry (segs : list Segment) (pc : Z) : option finstr :=
  if (pc <? pc_bound - 4)%Z && (0 <=? pc)%Z then
    match fetch_word segs (Z_to_bv 64 pc) with
    | Some w =>
        if is_ecall w then Some FEcall
        else match decode_any w with
             | Some (i, 4%Z) => compile pc i
             | _ => None
             end
    | None => None
    end
  else None.
