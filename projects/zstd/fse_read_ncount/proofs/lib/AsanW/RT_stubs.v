(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition eff_mem (m : word -> option byte) (e : resp) : word -> option byte :=
apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps e)) (eff_zeros e)) (eff_copies e)) (eff_writes e).
#[using="Type"] Lemma nret_MSsvc_gen : forall R F pc x8 fc rv m ro e,
nret (MSsvc R F pc x8 fc rv m ro) e = MS (bvmap_set 10 (eff_ret e) R) F (pc + Z_to_bv 64 4) fc rv (eff_mem m e) ro.
Proof. intros. destruct e. reflexivity. Qed.
#[using="Type"] Lemma eff_mem_zeros : forall m r z ci, eff_mem m (mkEffectU r [] [z] [] [] ci) = apply_zeros m [z].
Proof. reflexivity. Qed.
Section STUBS.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Definition rt_regs (a0 a1 a2 a3 a4 a5 a7 : word) : bvmap 5 word :=
mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Local Ltac stub_tail HF Hdec rsp :=
rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
let p' := eval vm_compute in (p + 4)%Z in
replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
end).
#[using="Type"] Lemma rt_mmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
(addr len prot flags : Z) (x17 : word),
@implF node asegs (at_nodeA asegs) fst _ RNG (enode (NMmap addr len prot flags) dec)
(epostF (fun a RNG' ms' => exists rsp,
fst (NMmap addr len prot flags) rsp RNG RNG' /\ dec rsp = Some a /\
ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 222))
F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
(MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) x17)
F (Z_to_bv 64 0x64b0c) fc None m (seg_rom asegs)).
Proof.
intros fst RNG X dec addr len prot flags x17. unfold rt_regs. apply implF_enode.
step. step_ecall. split. { at_nodeA_solve. }
intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
step.
apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.
End STUBS.
End CANSEC1.
