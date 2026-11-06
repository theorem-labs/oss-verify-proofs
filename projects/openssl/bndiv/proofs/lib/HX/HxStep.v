(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie AxFetchFast AxFetchFast2 AxDecInt.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive dinstr : Type :=
| DLui (rd : rix) (v : w64)
| DAuipc (rd : rix) (v : w64)
| DJal (rd : rix) (off : w64)
| DJalr (rd rs1 : rix) (off : w64)
| DBranch (bc : branch_cond) (rs1 rs2 : rix) (off : w64)
| DLoad (sz : msize) (sg : bool) (rd rs1 : rix) (off : w64)
| DStore (sz : msize) (rs1 rs2 : rix) (off : w64)
| DOpImm (op : aluop) (rd rs1 : rix) (imm : w64)
| DShiftImm (op : aluop) (rd rs1 : rix) (sh : w64)
| DOp (op : aluop) (rd rs1 rs2 : rix)
| DOpImm32 (rd rs1 : rix) (imm : w64)
| DShiftImm32 (op : aluop) (rd rs1 : rix) (sh : w64)
| DOp32 (op : aluop) (rd rs1 rs2 : rix)
| DMul (op : mulop) (rd rs1 rs2 : rix)
| DMul32 (op : mulop) (rd rs1 rs2 : rix)
| DFence
| DLr (wd : awidth) (rd rs1 : rix)
| DSc (wd : awidth) (rd rs1 rs2 : rix)
| DAmo (op : amoop) (wd : awidth) (rd rs1 rs2 : rix)
| DUnsupported.

Definition predec (i : instr) : dinstr :=
  match i with
  | Lui rd imm => DLui (rix_of_reg rd) (w_of_bv (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))))
  | Auipc rd imm => DAuipc (rix_of_reg rd) (w_of_bv (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))))
  | Jal rd imm => DJal (rix_of_reg rd) (w_of_bv (sext 64 imm))
  | Jalr rd rs1 imm => DJalr (rix_of_reg rd) (rix_of_reg rs1) (w_of_bv (sext 64 imm))
  | Branch bc rs1 rs2 imm => DBranch bc (rix_of_reg rs1) (rix_of_reg rs2) (w_of_bv (sext 64 imm))
  | Load sz sg rd rs1 imm => DLoad sz sg (rix_of_reg rd) (rix_of_reg rs1) (w_of_bv (sext 64 imm))
  | Store sz rs1 rs2 imm => DStore sz (rix_of_reg rs1) (rix_of_reg rs2) (w_of_bv (sext 64 imm))
  | OpImm op rd rs1 imm => DOpImm op (rix_of_reg rd) (rix_of_reg rs1) (w_of_bv (sext 64 imm))
  | ShiftImm op rd rs1 sh => DShiftImm op (rix_of_reg rd) (rix_of_reg rs1) (w_of_bv (zext 64 sh))
  | Op op rd rs1 rs2 => DOp op (rix_of_reg rd) (rix_of_reg rs1) (rix_of_reg rs2)
  | OpImm32 rd rs1 imm => DOpImm32 (rix_of_reg rd) (rix_of_reg rs1) (w_of_bv (sext 64 (sext 32 imm)))
  | ShiftImm32 op rd rs1 sh => DShiftImm32 op (rix_of_reg rd) (rix_of_reg rs1) (w_of_bv (zext 64 (zext 32 sh)))
  | Op32 op rd rs1 rs2 => DOp32 op (rix_of_reg rd) (rix_of_reg rs1) (rix_of_reg rs2)
  | Mul op rd rs1 rs2 => DMul op (rix_of_reg rd) (rix_of_reg rs1) (rix_of_reg rs2)
  | Mul32 op rd rs1 rs2 => DMul32 op (rix_of_reg rd) (rix_of_reg rs1) (rix_of_reg rs2)
  | Fence _ _ _ _ _ => DFence
  | FenceI _ _ _ => DFence
  | Lr wd _ _ rd rs1 => DLr wd (rix_of_reg rd) (rix_of_reg rs1)
  | Sc wd _ _ rd rs1 rs2 => DSc wd (rix_of_reg rd) (rix_of_reg rs1) (rix_of_reg rs2)
  | Amo op wd _ _ rd rs1 rs2 => DAmo op wd (rix_of_reg rd) (rix_of_reg rs1) (rix_of_reg rs2)
  | _ => DUnsupported
  end.

Definition is_unsupported (d : dinstr) : bool := match d with DUnsupported => true | _ => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive hresv : Type := RNone | RSome (a : hval) | RUnk.

(* [comment removed for export] *)
Definition veq (a b : hval) : option bool :=
  match a, b with
  | VC x, VC y => Some (w_eqb x y)
  | VP t1 o1, VP t2 o2 => if (t1 =? t2)%uint63 then Some (w_eqb o1 o2) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition inval (r : hresv) (a : hval) : hresv :=
  match r with
  | RNone => RNone
  | RSome x => match veq x a with Some true => RNone | Some false => RSome x | None => RUnk end
  | RUnk => RUnk
  end.

Record sstate : Type := SS {
  s_pc : w64;
  s_regs : regfile hval;
  s_resv : hresv;
  s_mem : mem;
  s_abs : abstab;
  s_next : int
}.

Definition rget (S : sstate) (r : rix) : hval := rf_get vzero (s_regs S) r.

Definition with_reg_pc (S : sstate) (rd : rix) (v : hval) (pc : w64) : sstate :=
  SS pc (rf_set (s_regs S) rd v) (s_resv S) (s_mem S) (s_abs S) (s_next S).

Definition with_pc (S : sstate) (pc : w64) : sstate :=
  SS pc (s_regs S) (s_resv S) (s_mem S) (s_abs S) (s_next S).

Definition with_mem_pc (S : sstate) (M : mem) (a : hval) (pc : w64) : sstate :=
  SS pc (s_regs S) (inval (s_resv S) a) M (s_abs S) (s_next S).

Definition with_all (S : sstate) (rd : rix) (v : hval) (r : hresv) (M : mem) (pc : w64) : sstate :=
  SS pc (rf_set (s_regs S) rd v) r M (s_abs S) (s_next S).

(* [comment removed for export] *)
Definition amo_al (ctx : vctx) (wd : awidth) (a : hval) : bool :=
  let m := match wd with AW => 3 | AD => 7 end%uint63 in
  match a with
  | VC w => (wl w land m =? 0)%uint63
  | VP t o => inb ctx t o && (wl o land m =? 0)%uint63 && match ctx t with Some (al, _) => (3 <=? al)%uint63 | None => false end
  | VU | VN _ _ => false
  end.

Definition amo_sz (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.

(* [comment removed for export] *)
Definition amo_new (op : amoop) (wd : awidth) (old src : w64) : w64 :=
  match wd with
  | AW => w_of_bv (zext 64 (amo_val op (low32 (wbv old)) (low32 (wbv src))))
  | AD => w_of_bv (amo_val op (wbv old) (wbv src))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ICD : nat := 24.

(* [comment removed for export] *)
Definition pc_ok (pc : w64) : bool :=
  if wh pc then false else ((wl pc land 3 =? 0)%uint63 && (wl pc <? 67108864)%uint63).

Definition ic_key (pc : w64) : int := (wl pc >> 2)%uint63.

Definition icache := itrie dinstr.
Definition ic_get (ic : icache) (pc : w64) : option dinstr := iget ICD ic (ic_key pc).
Definition ic_set (ic : icache) (pc : w64) (d : dinstr) : icache := iset ICD ic (ic_key pc) d.

Definition hx_fetch (segs : list Segment) (ic : icache) (pc : w64) : option (dinstr * icache) :=
  if pc_ok pc then
    match ic_get ic pc with
    | Some d => Some (d, ic)
    | None =>
        match fetch_fast2 segs pc with
        | Some w =>
            if is_ecall_fast w then None else
            match fdecode w with
            | Some (i, isz) =>
                if (isz =? 4) then
                  let d := predec i in
                  if is_unsupported d then None else Some (d, ic_set ic pc d)
                else None
            | None => None
            end
        | None => None
        end
    end
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sres : Type :=
| SNext (S : sstate)
| SStuck (code : int) (S : sstate).

Definition w_four : w64 := W false 4%uint63.
Definition w_notone : w64 := W true 9223372036854775806%uint63.

Definition hx_exec (segs : list Segment) (d : dinstr) (S : sstate) : sres :=
  let pc := s_pc S in
  let npc := w_add pc w_four in
  match d with
  | DLui rd v => SNext (with_reg_pc S rd (VC v) npc)
  | DAuipc rd v => SNext (with_reg_pc S rd (VC (w_add pc v)) npc)
  | DJal rd off => SNext (with_reg_pc S rd (VC npc) (w_add pc off))
  | DJalr rd rs1 off =>
      match rget S rs1 with
      | VC a => SNext (with_reg_pc S rd (VC npc) (w_and (w_add a off) w_notone))
      | _ => SStuck 2 S
      end
  | DBranch bc rs1 rs2 off =>
      match v_branch (ctx_of (s_mem S)) bc (rget S rs1) (rget S rs2) with
      | Some true => SNext (with_pc S (w_add pc off))
      | Some false => SNext (with_pc S npc)
      | None => SStuck 3 S
      end
  | DLoad sz sg rd rs1 off =>
      let a := v_alu64 (ctx_of (s_mem S)) ALU_ADD (rget S rs1) (VC off) in
      match hx_load segs (s_mem S) (s_abs S) a sz sg with
      | Some v => SNext (with_reg_pc S rd v npc)
      | None => SStuck 4 S
      end
  | DStore sz rs1 rs2 off =>
      let a := v_alu64 (ctx_of (s_mem S)) ALU_ADD (rget S rs1) (VC off) in
      match hx_store segs (s_mem S) (s_abs S) a sz (rget S rs2) with
      | Some M' => SNext (with_mem_pc S M' a npc)
      | None => SStuck 5 S
      end
  | DOpImm op rd rs1 imm => SNext (with_reg_pc S rd (v_alu64 (ctx_of (s_mem S)) op (rget S rs1) (VC imm)) npc)
  | DShiftImm op rd rs1 sh => SNext (with_reg_pc S rd (v_alu64 (ctx_of (s_mem S)) op (rget S rs1) (VC sh)) npc)
  | DOp op rd rs1 rs2 => SNext (with_reg_pc S rd (v_alu64 (ctx_of (s_mem S)) op (rget S rs1) (rget S rs2)) npc)
  | DOpImm32 rd rs1 imm => SNext (with_reg_pc S rd (v_op32 ALU_ADD (rget S rs1) (VC imm)) npc)
  | DShiftImm32 op rd rs1 sh => SNext (with_reg_pc S rd (v_op32 op (rget S rs1) (VC sh)) npc)
  | DOp32 op rd rs1 rs2 => SNext (with_reg_pc S rd (v_op32 op (rget S rs1) (rget S rs2)) npc)
  | DMul op rd rs1 rs2 => SNext (with_reg_pc S rd (v_muldiv op (rget S rs1) (rget S rs2)) npc)
  | DMul32 op rd rs1 rs2 => SNext (with_reg_pc S rd (v_muldiv32 op (rget S rs1) (rget S rs2)) npc)
  | DFence => SNext (with_pc S npc)
  | DLr wd rd rs1 =>
      let a := rget S rs1 in
      if amo_al (ctx_of (s_mem S)) wd a then
        match hx_load segs (s_mem S) (s_abs S) a (amo_sz wd) true with
        | Some v => SNext (with_all S rd v (RSome a) (s_mem S) npc)
        | None => SStuck 7 S
        end
      else SStuck 8 S
  | DSc wd rd rs1 rs2 =>
      let a := rget S rs1 in
      if amo_al (ctx_of (s_mem S)) wd a then
        match s_resv S with
        | RNone => SNext (with_all S rd (VC w_one) RNone (s_mem S) npc)
        | RSome r =>
            match veq r a with
            | Some true =>
                match hx_store segs (s_mem S) (s_abs S) a (amo_sz wd) (rget S rs2) with
                | Some M' => SNext (with_all S rd (VC w_zero) RNone M' npc)
                | None => SStuck 9 S
                end
            | Some false => SNext (with_all S rd (VC w_one) RNone (s_mem S) npc)
            | None => SStuck 10 S
            end
        | RUnk => SStuck 10 S
        end
      else SStuck 8 S
  | DAmo op wd rd rs1 rs2 =>
      let a := rget S rs1 in
      if amo_al (ctx_of (s_mem S)) wd a then
        match hx_load segs (s_mem S) (s_abs S) a (amo_sz wd) true, rget S rs2 with
        | Some (VC old), VC src =>
            match hx_store segs (s_mem S) (s_abs S) a (amo_sz wd) (VC (amo_new op wd old src)) with
            | Some M' => SNext (with_all S rd (VC old) (inval (s_resv S) a) M' npc)
            | None => SStuck 9 S
            end
        | _, _ => SStuck 11 S
        end
      else SStuck 8 S
  | DUnsupported => SStuck 6 S
  end.

Definition hx_step (segs : list Segment) (ic : icache) (S : sstate) : icache * sres :=
  match hx_fetch segs ic (s_pc S) with
  | Some (d, ic') => (ic', hx_exec segs d S)
  | None => (ic, SStuck 1 S)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive rres : Type :=
| RRun (S : sstate)               (* [comment removed for export] *)
| RStop (S : sstate)              (* [comment removed for export] *)
| RStuck (code : int) (S : sstate).

Section Run.
Variable segs : list Segment.
Variable stop : w64 -> bool.

Definition hx_step1 (ic : icache) (S : sstate) : icache * rres :=
  if stop (s_pc S) then (ic, RStop S) else
  match hx_step segs ic S with
  | (ic', SNext S') => (ic', RRun S')
  | (ic', SStuck c S') => (ic', RStuck c S')
  end.

Fixpoint hx_run (n : nat) (ic : icache) (S : sstate) : icache * rres :=
  match n with
  | O => hx_step1 ic S
  | Datatypes.S n' =>
      match hx_run n' ic S with
      | (ic', RRun S') => hx_run n' ic' S'
      | r => r
      end
  end.

End Run.
