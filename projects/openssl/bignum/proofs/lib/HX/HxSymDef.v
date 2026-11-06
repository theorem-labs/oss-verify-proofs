(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Inductive sarg : Type := AC (w : w64) | AN (t : int).
Inductive sop : Type := SAlu (op : aluop) | SMul (op : mulop).
Record snode : Type := SN { sn_t : int; sn_op : sop; sn_a : sarg; sn_b : sarg }.

Definition valw (rho : valuation) (a : sarg) : bv 64 :=
  match a with AC w => wbv w | AN t => Z_to_bv 64 (rho t) end.

Definition sop_eval (op : sop) (x y : bv 64) : bv 64 :=
  match op with SAlu o => alu64 o x y | SMul o => mul_div o x y end.

Definition node_ok (rho : valuation) (n : snode) : Prop :=
  rho (sn_t n) = bv_unsigned (sop_eval (sn_op n) (valw rho (sn_a n)) (valw rho (sn_b n))).

Definition arg_below (n : int) (a : sarg) : Prop := match a with AC _ => True | AN t => to_Z t < to_Z n end.

Definition node_below (n : int) (nd : snode) : Prop :=
  to_Z (sn_t nd) < to_Z n /\ arg_below n (sn_a nd) /\ arg_below n (sn_b nd).

Definition log_ok (rho : valuation) (log : list snode) : Prop := Forall (node_ok rho) log.
Definition log_below (n : int) (log : list snode) : Prop := Forall (node_below n) log.

Definition sarg_of (v : hval) : option sarg :=
  match v with
  | VC w => Some (AC w)
  | VP t o => if is_zero o then Some (AN t) else None
  | _ => None
  end.

Definition TAGMAX : int := 1048576.

Section Sym.
Variable segs : list Segment.

Definition sym_result (log : list snode) (S : sstate) (rd : rix) (op : sop) (a b normal : hval) : option (list snode * sstate) :=
  let npc := w_add (s_pc S) w_four in
  match normal with
  | VU =>
      match sarg_of a, sarg_of b with
      | Some x, Some y =>
          let t := s_next S in
          if (t <? TAGMAX)%uint63 then
            Some (SN t op x y :: log, SS npc (rf_set (s_regs S) rd (VP t w_zero)) (s_resv S) (s_mem S) (s_abs S) (t + 1)%uint63)
          else None
      | _, _ => Some (log, with_reg_pc S rd normal npc)
      end
  | _ => Some (log, with_reg_pc S rd normal npc)
  end.

Definition sx_step (log : list snode) (S : sstate) : option (list snode * sstate) :=
  match hx_fetch segs IEmpty (s_pc S) with
  | Some (DOp op rd rs1 rs2, _) =>
      sym_result log S rd (SAlu op) (rget S rs1) (rget S rs2) (v_alu64 (ctx_of (s_mem S)) op (rget S rs1) (rget S rs2))
  | Some (DOpImm op rd rs1 imm, _) =>
      sym_result log S rd (SAlu op) (rget S rs1) (VC imm) (v_alu64 (ctx_of (s_mem S)) op (rget S rs1) (VC imm))
  | Some (DShiftImm op rd rs1 sh, _) =>
      sym_result log S rd (SAlu op) (rget S rs1) (VC sh) (v_alu64 (ctx_of (s_mem S)) op (rget S rs1) (VC sh))
  | Some (DMul op rd rs1 rs2, _) =>
      sym_result log S rd (SMul op) (rget S rs1) (rget S rs2) (v_muldiv op (rget S rs1) (rget S rs2))
  | Some (_, _) =>
      match hx_step segs IEmpty S with
      | (_, SNext S') => Some (log, S')
      | (_, SStuck _ _) => None
      end
  | None => None
  end.

End Sym.

Section SymRun.
Variable segs : list Segment.
Variable stop : w64 -> bool.

Fixpoint sx_run (n : nat) (log : list snode) (S : sstate) : option (list snode * sstate) :=
  match n with
  | O => Some (log, S)
  | Datatypes.S n' =>
      if stop (s_pc S) then Some (log, S) else
      match sx_step segs log S with
      | Some (log', S') => sx_run n' log' S'
      | None => None
      end
  end.

End SymRun.
