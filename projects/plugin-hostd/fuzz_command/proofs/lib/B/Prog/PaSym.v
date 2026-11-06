(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0a.v for fuzz_command's program walk, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/PaSym.v for fuzz_command.asan-ubsan: module paths. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section g.
Variable psym : Type.
#[local] Notation pinstr := (@pinstr psym).
Definition ptree := tree pinstr.
Definition pkey (k : Z) : positive := Z.to_pos (k / 4 + 1).
Fixpoint ptree_of_list_from (i : Z) (l : list pinstr) (t : ptree) : ptree :=
match l with [] => t | e :: l' => ptree_of_list_from (i + 1) l' (tset (Z.to_pos (i + 1)) e t) end.
Definition ptree_of_list (l : list pinstr) : ptree := ptree_of_list_from 0 l TEmpty.
Definition plookup (t : ptree) (k : Z) : option pinstr :=
if ((0 <=? k) && (k mod 4 =? 0))%bool then tget (pkey k) t else None.
Inductive psres :=
| PRun (ss : sstate)
| PEcall (ss : sstate)
| PCallx (s : psym) (ss : sstate)
| PStop (why : stop_reason).
Definition codeptr (k : Z) : sv := SOff A_TEXT k.
Definition is_hi (v : sv) (j : nat) : bool :=
match v with SOff n z => (Nat.eqb n (A_HI j) && (z =? 0))%bool | _ => false end.
Definition sload_pi (G : facts) (rs : smem) (b : option nat) (off : Z) (sz : msize) (sg : bool) : option sv :=
let n := Z.of_nat (nbytes sz) in
match find_region rs b off n with
| None => None
| Some r =>
match find_chunk (r_chunks r) off n with
| None => None
| Some c =>
let k := off - YP09.c_off c in
match YP09.c_val c with
| CVal w v =>
if negb (Z.of_N w <=? 8) then None
else if (k =? 0) then Some (loadres G sz sg v)
else Some (loadres G sz sg (s_alu G ALU_SRL v (SLit (8 * k))))
| CZero _ => Some (SLit 0)
| CImg _ => None
| CData d s _ => if 0 <=? s then Some (loadres G sz sg (SData d (s + k) (N.of_nat (nbytes sz)))) else None
end
end
end.
Section h.
Variable tpi : ptree.
Definition sym_step_pi (ss : sstate) : psres :=
let k := ss_pc ss in
let G := ss_facts ss in
let R := sr_get (ss_regs ss) in
match plookup tpi k with
| None => PStop SR_fetch
| Some e =>
match e with
| PCall s rd => PCallx s (setreg ss rd (codeptr (k + 4)) (k + 4))
| PTail s => PCallx s ss
| PHi rd j => PRun (setreg ss rd (SOff (A_HI j) 0) (k + 4))
| PAddHi rd rs j a off => if is_hi (R rs) j then (if Nat.leb A_TEXT a then PRun (setreg ss rd (SOff a off) (k + 4)) else PStop SR_unsupported) else PStop (SR_addr (R rs))
| PLdHi rd rs j a off sz sg =>
if is_hi (R rs) j then
if negb (Nat.leb A_TEXT a) then PStop SR_unsupported else
match sload_pi G (ss_mem ss) (Some a) off sz sg with
| Some v => PRun (setreg ss rd v (k + 4))
| None => PStop (SR_load (Some a) off)
end
else PStop (SR_addr (R rs))
| PW wz =>
let w := Z_to_bv 32 wz in
if is_ecall w then PStop SR_unsupported else
match decode_any w with
| None => PStop SR_decode
| Some (i, isz) =>
if negb (isz =? 4) then PStop SR_unsupported else
match i with
| Lui rd imm => PRun (setreg ss rd (SLit (bv_signed (bv_concat 32 imm (Z_to_bv 12 0)))) (k + 4))
| Auipc _ _ => PStop SR_unsupported
| Jal rd imm => PRun (setreg ss rd (codeptr (k + 4)) (k + bv_signed imm))
| Jalr rd rs1 imm =>
match R rs1 with
| SOff n t => if (Nat.eqb n A_TEXT && ((t + bv_signed imm) mod 2 =? 0))%bool
then PRun (setreg ss rd (codeptr (k + 4)) (t + bv_signed imm))
else PStop (SR_jalr (R rs1))
| v => PStop (SR_jalr v)
end
| Branch c rs1 rs2 imm =>
match decide_cond2 G c (R rs1) (R rs2) with
| Some true => PRun (setpc ss (k + bv_signed imm))
| Some false => PRun (setpc ss (k + 4))
| None => PStop (SR_branch c (R rs1) (R rs2))
end
| Load sz sg rd rs1 imm =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match addr_of a with
| None => PStop (SR_addr a)
| Some (b, off) =>
match sload_pi G (ss_mem ss) b off sz sg with
| Some v => PRun (setreg ss rd v (k + 4))
| None => PStop (SR_load b off)
end
end
| Store sz rs1 rs2 imm =>
match ss_resv ss with
| Some _ => PStop SR_resv
| None =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match addr_of a with
| None => PStop (SR_addr a)
| Some (b, off) =>
match sstore (ss_mem ss) b off sz (R rs2) with
| Some m' => PRun (mkSST (k + 4) (ss_regs ss) (ss_fregs ss) m' None G)
| None => PStop (SR_store b off)
end
end
end
| OpImm op rd rs1 imm => PRun (setreg ss rd (s_alu2 G op (R rs1) (SLit (bv_signed imm))) (k + 4))
| ShiftImm op rd rs1 sh => PRun (setreg ss rd (s_alu2 G op (R rs1) (SLit (bv_unsigned sh))) (k + 4))
| Op op rd rs1 rs2 => PRun (setreg ss rd (s_alu2 G op (R rs1) (R rs2)) (k + 4))
| OpImm32 rd rs1 imm => PRun (setreg ss rd (s_aluw3 G ALU_ADD (R rs1) (SLit (bv_signed imm))) (k + 4))
| ShiftImm32 op rd rs1 sh => PRun (setreg ss rd (s_aluw3 G op (R rs1) (SLit (bv_unsigned sh))) (k + 4))
| Op32 op rd rs1 rs2 => PRun (setreg ss rd (s_aluw3 G op (R rs1) (R rs2)) (k + 4))
| Mul op rd rs1 rs2 => PRun (setreg ss rd (s_md op (R rs1) (R rs2)) (k + 4))
| Mul32 op rd rs1 rs2 => PRun (setreg ss rd (s_mdw op (R rs1) (R rs2)) (k + 4))
| Fence _ _ _ _ _ | FenceI _ _ _ => PRun (setpc ss (k + 4))
| _ => PStop SR_unsupported
end
end
end
end.
Inductive prun_status := PRS_running | PRS_ecall | PRS_call (s : psym) | PRS_stopped (why : stop_reason).
Fixpoint sym_run_pi (fuel : nat) (ss : sstate) : sstate * prun_status :=
match fuel with
| O => (ss, PRS_running)
| S f => match sym_step_pi ss with
| PRun ss' => sym_run_pi f ss'
| PEcall ss' => (ss', PRS_ecall)
| PCallx s ss' => (ss', PRS_call s)
| PStop why => (ss, PRS_stopped why)
end
end.
Fixpoint sym_run_to_pi (fuel : nat) (stop_k : Z) (ss : sstate) : sstate * prun_status :=
match fuel with
| O => (ss, PRS_running)
| S f => if ss_pc ss =? stop_k then (ss, PRS_running) else
match sym_step_pi ss with
| PRun ss' => sym_run_to_pi f stop_k ss'
| PEcall ss' => (ss', PRS_ecall)
| PCallx s ss' => (ss', PRS_call s)
| PStop why => (ss, PRS_stopped why)
end
end.
Definition sym_runN_pi (n : N) (ss : sstate) := sym_run_pi (N.to_nat n) ss.
Definition sym_run_toN_pi (n : N) (stop_k : Z) (ss : sstate) := sym_run_to_pi (N.to_nat n) stop_k ss.
End h.
End g.
Arguments ptree_of_list {psym} _.
Arguments plookup {psym} _ _.
Arguments sym_step_pi {psym} _ _.
Arguments sym_run_pi {psym} _ _ _.
Arguments sym_run_to_pi {psym} _ _ _ _.
Arguments sym_runN_pi {psym} _ _ _.
Arguments sym_run_toN_pi {psym} _ _ _ _.
Arguments PRun {psym} _.
Arguments PEcall {psym} _.
Arguments PCallx {psym} _ _.
Arguments PStop {psym} _.
Arguments PRS_running {psym}.
Arguments PRS_ecall {psym}.
Arguments PRS_call {psym} _.
Arguments PRS_stopped {psym} _.
Arguments codeptr _ /.
