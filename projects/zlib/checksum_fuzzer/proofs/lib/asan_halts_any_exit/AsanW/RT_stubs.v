(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import SysStepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition eff_mem (m : word -> option byte) (e : resp) : word -> option byte :=
  apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps e)) (eff_zeros e)) (eff_copies e)) (eff_writes e).

Lemma nret_MSsvc_gen : forall R F pc x8 fc rv m ro e,
  (* port727 (): the return from a syscall clears the LR/SC reservation (Run.v advance_past_svc) *)
  nret (MSsvc R F pc x8 fc rv m ro) e = MS (bvmap_set 10 (eff_ret e) R) F (pc + Z_to_bv 64 4) fc None (eff_mem m e) ro.
Proof. intros. destruct e. reflexivity. Qed.

Lemma eff_mem_zeros : forall m r z ci, eff_mem m (mkEffectU r [] [z] [] [] ci) = apply_zeros m [z].
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


Lemma rt_mmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len prot flags : Z) (x17 : word),
  @implF node asegs (at_nodeA asegs) fst _ RNG (enode (NMmap addr len prot flags) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMmap addr len prot flags) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 222))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) x17)
        F (Z_to_bv 64 0x641ec) fc None m (seg_rom asegs)).
Proof.
  intros fst RNG X dec addr len prot flags x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.




End STUBS.
End CANSEC1.
