(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0l.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).
Definition sr_get (sr : list sv) (r : reg) : sv :=
if bv_eqb r 0 then SLit 0 else nth (ridx r) sr (SLit 0).
Fixpoint sr_upd (sr : list sv) (n : nat) (e : sv) : list sv :=
match n with
| O => match sr with [] => [e] | _ :: t => e :: t end
| S n' => match sr with
| [] => SLit 0 :: sr_upd [] n' e
| h :: t => h :: sr_upd t n' e
end
end.
Definition sr_set (sr : list sv) (r : reg) (e : sv) : list sv :=
if bv_eqb r 0 then sr else sr_upd sr (ridx r) e.
Lemma nth_sr_upd : forall n sr e i,
nth i (sr_upd sr n e) (SLit 0) = if Nat.eqb i n then e else nth i sr (SLit 0).
Proof.
induction n as [|n IH]; intros sr e i.
- destruct sr; destruct i; cbn; try reflexivity; destruct i; reflexivity.
- destruct sr as [|h t]; destruct i as [|i]; cbn; try reflexivity.
+ rewrite IH. destruct (Nat.eqb i n); [reflexivity|]. destruct i; reflexivity.
+ apply IH.
Qed.
Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof.
intros r r' H. apply bv_eq. unfold ridx in H.
pose proof (u5_range r). pose proof (u5_range r'). lia.
Qed.
Definition regs_ok (E : env) (sr : list sv) (regs : bvmap 5 word) : Prop :=
forall r : reg, getr regs r = sv_denot E (sr_get sr r).
Lemma regs_ok_set : forall E sr regs r v e,
regs_ok E sr regs -> sv_denot E e = v ->
regs_ok E (sr_set sr r e) (if bv_eqb r 0 then regs else regupd regs r v).
Proof.
intros E sr regs r v e Hr Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
specialize (Hr r').
unfold getr, regupd, sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'.
unfold reg_get. rewrite bvmap_get_set_same. symmetry. exact Hv.
- apply Nat.eqb_neq in Hi.
unfold reg_get in *. rewrite bvmap_get_set_other by (intros Heq; apply Hi; rewrite Heq; reflexivity).
exact Hr.
Qed.
Record sstate := mkSST {
ss_pc : Z;
ss_regs : list sv;
ss_fregs : list sv;
ss_mem : smem;
ss_resv : option sv;
ss_facts : facts
}.
Abbreviation mkSS pc regs mem resv facts := (mkSST pc regs nil mem resv facts).
Definition sfr_get (sfr : list sv) (r : reg) : sv := nth (ridx r) sfr (SLit 0).
Definition sfr_set (sfr : list sv) (r : reg) (e : sv) : list sv := sr_upd sfr (ridx r) e.
Lemma sfr_get_set : forall sfr r r' e,
sfr_get (sfr_set sfr r e) r' = if bv_eqb r' r then e else sfr_get sfr r'.
Proof.
intros sfr r r' e. unfold sfr_get, sfr_set. rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. rewrite bv_eqb_refl. reflexivity.
- apply Nat.eqb_neq in Hi. destruct (bv_eqb r' r) eqn:Hb; [|reflexivity].
unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq in Hb. subst. congruence.
Qed.
Lemma sfr_set_nonnil : forall sfr r e, sfr_set sfr r e <> [].
Proof. intros sfr r e. unfold sfr_set. destruct (ridx r); destruct sfr; cbn; congruence. Qed.
Definition fregs_ok (E : env) (sfr : list sv) (fregs : bvmap 5 word) : Prop :=
forall r : reg, reg_get fregs r = sv_denot E (sfr_get sfr r).
Lemma fregs_ok_set : forall E sfr fregs r v e,
fregs_ok E sfr fregs -> sv_denot E e = v ->
fregs_ok E (sfr_set sfr r e) (bvmap_set r v fregs).
Proof.
intros E sfr fregs r v e Hf Hv r'. rewrite sfr_get_set.
destruct (bv_eqb r' r) eqn:Hb.
- unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq in Hb. subst r'. unfold reg_get. rewrite bvmap_get_set_same. symmetry. exact Hv.
- unfold reg_get. rewrite bvmap_get_set_other.
+ apply Hf.
+ intros Heq. subst. rewrite bv_eqb_refl in Hb. discriminate.
Qed.
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Definition resv_denot (E : env) (o : option sv) : option word :=
match o with Some a => Some (sv_denot E a) | None => None end.
Definition st_ok (E : env) (ss : sstate) (ms : machine_state) : Prop :=
ms_fregs ms = fp_regs
/\ ms_pc_val ms = Z_to_bv 64 (ss_pc ss)
/\ ms_svc_pending ms = None
/\ ms_resv ms = resv_denot E (ss_resv ss)
/\ ms_fcsr ms = fp_csr
/\ ms_rom ms = seg_rom segs
/\ regs_ok E (ss_regs ss) (ms_regs ms)
/\ mem_ok segs E (ms_mem ms) (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Definition st_ok_ecall (E : env) (ss : sstate) (ms : machine_state) : Prop :=
ms_fregs ms = fp_regs
/\ ms_pc_val ms = Z_to_bv 64 (ss_pc ss)
/\ ms_svc_pending ms = Some (sv_denot E (sr_get (ss_regs ss) 17))
/\ ms_resv ms = resv_denot E (ss_resv ss)
/\ ms_fcsr ms = fp_csr
/\ ms_rom ms = seg_rom segs
/\ regs_ok E (ss_regs ss) (ms_regs ms)
/\ mem_ok segs E (ms_mem ms) (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Definition st_okF (E : env) (ss : sstate) (ms : machine_state) : Prop :=
fregs_ok E (ss_fregs ss) (ms_fregs ms)
/\ ms_pc_val ms = Z_to_bv 64 (ss_pc ss)
/\ ms_svc_pending ms = None
/\ ms_resv ms = resv_denot E (ss_resv ss)
/\ frm_zero (ms_fcsr ms)
/\ ms_rom ms = seg_rom segs
/\ regs_ok E (ss_regs ss) (ms_regs ms)
/\ mem_ok segs E (ms_mem ms) (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Definition st_okF_ecall (E : env) (ss : sstate) (ms : machine_state) : Prop :=
fregs_ok E (ss_fregs ss) (ms_fregs ms)
/\ ms_pc_val ms = Z_to_bv 64 (ss_pc ss)
/\ ms_svc_pending ms = Some (sv_denot E (sr_get (ss_regs ss) 17))
/\ ms_resv ms = resv_denot E (ss_resv ss)
/\ frm_zero (ms_fcsr ms)
/\ ms_rom ms = seg_rom segs
/\ regs_ok E (ss_regs ss) (ms_regs ms)
/\ mem_ok segs E (ms_mem ms) (ss_mem ss)
/\ facts_ok E (ss_facts ss).
Inductive stop_reason :=
| SR_fetch | SR_decode | SR_unsupported | SR_branch (c : branch_cond) (a b : sv)
| SR_addr (a : sv) | SR_load (b : option nat) (off : Z) | SR_store (b : option nat) (off : Z)
| SR_jalr (t : sv) | SR_resv | SR_align.
Inductive sres :=
| SRun (ss : sstate)
| SEcall (ss : sstate)
| SStop (why : stop_reason)  .
Definition setpc (ss : sstate) (pc : Z) : sstate :=
mkSST pc (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition setreg (ss : sstate) (rd : reg) (v : sv) (pc : Z) : sstate :=
mkSST pc (sr_set (ss_regs ss) rd v) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition setfreg (ss : sstate) (rd : reg) (v : sv) (pc : Z) : sstate :=
mkSST pc (ss_regs ss) (sfr_set (ss_fregs ss) rd v) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition addr_of (a : sv) : option (option nat * Z) :=
match a with
| SLit z => Some (None, zcanon z)
| SOff n z => Some (Some n, z)
| _ => None
end.
Definition aligned_dec (G : facts) (a : sv) (al : Z) : bool :=
match a with
| SLit z => zcanon z mod al =? 0
| SOff n z => match atom_lookup (f_atoms G) n with
| Some f => (al <=? 2 ^ af_al2 f) && (2 ^ af_al2 f mod al =? 0) && (z mod al =? 0)
| None => false
end
| _ => false
end.
Definition amo_bytes_of (wd : awidth) : Z := match wd with AW => 4 | AD => 8 end.
Definition amo_sz (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
Definition sym_step (ss : sstate) : sres :=
let pc := ss_pc ss in
let G := ss_facts ss in
let R := sr_get (ss_regs ss) in
match clookup tbl pc with
| None => SStop SR_fetch
| Some wz =>
let w := Z_to_bv 32 wz in
if is_ecall w then SEcall ss else
match decode_any w with
| None => SStop SR_decode
| Some (i, isz) =>
if negb (isz =? 4) then SStop SR_unsupported else
match i with
| Lui rd imm =>
SRun (setreg ss rd (SLit (bv_signed (bv_concat 32 imm (Z_to_bv 12 0)))) (pc + 4))
| Auipc rd imm =>
SRun (setreg ss rd (SLit (zcanon (pc + bv_signed (bv_concat 32 imm (Z_to_bv 12 0))))) (pc + 4))
| Jal rd imm =>
SRun (setreg ss rd (SLit (zcanon (pc + 4))) (zcanon (pc + bv_signed imm)))
| Jalr rd rs1 imm =>
match R rs1 with
| SLit t => SRun (setreg ss rd (SLit (zcanon (pc + 4)))
(zalu64 ALU_AND (t + bv_signed imm) (-2)))
| t => SStop (SR_jalr t)
end
| Branch c rs1 rs2 imm =>
match decide_cond2 G c (R rs1) (R rs2) with
| Some true => SRun (setpc ss (zcanon (pc + bv_signed imm)))
| Some false => SRun (setpc ss (pc + 4))
| None => SStop (SR_branch c (R rs1) (R rs2))
end
| Load sz sg rd rs1 imm =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match addr_of a with
| None => SStop (SR_addr a)
| Some (b, off) =>
match sload segs G (ss_mem ss) b off sz sg with
| Some v => SRun (setreg ss rd v (pc + 4))
| None => SStop (SR_load b off)
end
end
| Store sz rs1 rs2 imm =>
match ss_resv ss with
| Some _ => SStop SR_resv
| None =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match addr_of a with
| None => SStop (SR_addr a)
| Some (b, off) =>
match sstore (ss_mem ss) b off sz (R rs2) with
| Some m' => SRun (mkSST (pc + 4) (ss_regs ss) (ss_fregs ss) m' None G)
| None => SStop (SR_store b off)
end
end
end
| OpImm op rd rs1 imm => SRun (setreg ss rd (s_alu2 G op (R rs1) (SLit (bv_signed imm))) (pc + 4))
| ShiftImm op rd rs1 sh => SRun (setreg ss rd (s_alu2 G op (R rs1) (SLit (bv_unsigned sh))) (pc + 4))
| Op op rd rs1 rs2 => SRun (setreg ss rd (s_alu2 G op (R rs1) (R rs2)) (pc + 4))
| OpImm32 rd rs1 imm => SRun (setreg ss rd (s_aluw3 G ALU_ADD (R rs1) (SLit (bv_signed imm))) (pc + 4))
| ShiftImm32 op rd rs1 sh => SRun (setreg ss rd (s_aluw3 G op (R rs1) (SLit (bv_unsigned sh))) (pc + 4))
| Op32 op rd rs1 rs2 => SRun (setreg ss rd (s_aluw3 G op (R rs1) (R rs2)) (pc + 4))
| Mul op rd rs1 rs2 => SRun (setreg ss rd (s_md op (R rs1) (R rs2)) (pc + 4))
| Mul32 op rd rs1 rs2 => SRun (setreg ss rd (s_mdw op (R rs1) (R rs2)) (pc + 4))
| Fence _ _ _ _ _ | FenceI _ _ _ => SRun (setpc ss (pc + 4))
| Lr wd _ _ rd rs1 =>
let a := R rs1 in
if negb (aligned_dec G a (amo_bytes_of wd)) then SStop SR_align else
match addr_of a with
| None => SStop (SR_addr a)
| Some (b, off) =>
match sload segs G (ss_mem ss) b off (amo_sz wd) true with
| Some v => SRun (mkSST (pc + 4) (sr_set (ss_regs ss) rd v) (ss_fregs ss) (ss_mem ss) (Some a) G)
| None => SStop (SR_load b off)
end
end
| Sc wd _ _ rd rs1 rs2 =>
let a := R rs1 in
if negb (aligned_dec G a (amo_bytes_of wd)) then SStop SR_align else
match ss_resv ss with
| None => SRun (mkSST (pc + 4) (sr_set (ss_regs ss) rd (SLit 1)) (ss_fregs ss) (ss_mem ss) None G)
| Some a' =>
if negb (sv_eqb a' a) then SStop SR_resv else
match addr_of a with
| None => SStop (SR_addr a)
| Some (b, off) =>
match sstore (ss_mem ss) b off (amo_sz wd) (R rs2) with
| Some m' => SRun (mkSST (pc + 4) (sr_set (ss_regs ss) rd (SLit 0)) (ss_fregs ss) m' None G)
| None => SStop (SR_store b off)
end
end
end
| _ => SStop SR_unsupported
end
end
end.
Inductive run_status := RS_running | RS_ecall | RS_stopped (why : stop_reason).
Fixpoint sym_run (fuel : nat) (ss : sstate) : sstate * run_status :=
match fuel with
| O => (ss, RS_running)
| S f => match sym_step ss with
| SRun ss' => sym_run f ss'
| SEcall ss' => (ss', RS_ecall)
| SStop why => (ss, RS_stopped why)
end
end.
Fixpoint sym_run_to (fuel : nat) (stop_pc : Z) (ss : sstate) : sstate * run_status :=
match fuel with
| O => (ss, RS_running)
| S f => if ss_pc ss =? stop_pc then (ss, RS_running) else
match sym_step ss with
| SRun ss' => sym_run_to f stop_pc ss'
| SEcall ss' => (ss', RS_ecall)
| SStop why => (ss, RS_stopped why)
end
end.
End d.
