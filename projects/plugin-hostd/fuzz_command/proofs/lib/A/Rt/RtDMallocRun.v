(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states of the walk of plugin-hostd/fuzz_command's malloc
   interceptor body ___interceptor_malloc 0x58b58, down to its call of __asan::asan_malloc 0x34528. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YN2j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* Measured on the pinned fuzz_command.asan (___interceptor_malloc 0x58b58, 87 instructions, frame 2,128 bytes;
   the trampoline __interceptor_trampoline_malloc 0x58984 is one  j 0x58b58 ).

     58b58 addi sp,sp,-2032; sd ra,2024(sp) .. sd s5,1976(sp); addi s0,sp,2032; addi sp,sp,-96
     58b80 mv s2,ra; mv s1,a0; jal 5f640            __asan::TryAsanInitFromRtl
     58b8c beqz a0,58bec                            the uninitialised arm (DlsymAlloc), not taken
     58b90 addi s4,s0,-2048; addi s4,s4,-80         s4 = &trace  = sp0 - 2128
     58b98 addi a0,s0,-2048; addi a0,a0,-64         a0 = &buffer = sp0 - 2112
     58ba0 addi s5,s4,2047; sd zero,9(s5)           trace.top_frame_bp = 0   (sp0 - 72)
     58ba8 sd a0,0(s4); sd zero,8(s4)               trace.trace = &buffer, size = 0, tag = 0
     58bb0 jal 603c8; li a1,2; bltu a1,a0,58c1c     __asan::GetMallocContextSize = [0xb1dbc] = 30 > 2
     58c1c jal 78e88                                StackTrace::GetCurrentPc = ra = 0x58c20
     58c20 auipc a1; ld a1,1984(a1)                 a1 = [0xa63e0] = 0x142be8 = &common_flags
     58c28 lbu s3,34(a1)                            fast_unwind_on_malloc = [0x142c0a] = 1
     58c2c mv s2,a0; jal 603c8; mv a5,a0            a5 = 30
     58c38 seqz a0,a0; addi a0,a0,-1; and a1,a0,s0  trace.top_frame_bp = s0 = sp0 (30 <> 0)
     58c44 li a0,1; sd a1,9(s5); bltu a0,a5,58c60   1 < 30
     58c60 addi a0,s0,-2048; addi a0,a0,-80         a0 = this = sp0 - 2128
     58c68 mv a1,s2; mv a2,s0; li a3,0; mv a4,s3    pc = 0x58c20, bp = sp0, context = 0, request_fast = 1
     58c78 jal 603d8                                BufferedStackTrace::UnwindImpl, a5 = 30 = max_depth
     58c7c addi a1,s0,-2048; addi a1,a1,-80; mv a0,s1
     58c88 jal 34528                                __asan::asan_malloc(size, &trace), ra = 0x58c8c
     58c8c addi sp,sp,96; ld ra,2024(sp) .. ld s5,1976(sp); addi sp,sp,2032; ret

   The walk reads four constant cells of the record (lib/A/AF0m.v Tfib_const_abs): the initialised flag 0xb1d98 = 1,
   the malloc context size 0xb1dbc = 30, the flags pointer 0xa63e0 = 0x142be8 and the flag word 0x142c08, whose
   byte 2 (0x142c0a, common + 34) is fast_unwind_on_malloc = 1. It writes only in [sp0 - 2128, sp0). *)

Definition DM_BODY : Z := 0x58b58.
Definition DM_TRAMP : Z := 0x58984.
Definition DM_PC0 : Z := 0x58c20.
Definition DM_ASAN : Z := 0x34528.
Definition DM_UNWIND : Z := 0x603d8.
Definition DM_RET1 : Z := 0x58c7c.
Definition DM_RET2 : Z := 0x58c8c.
Definition DM_EXIT : Z := 0x58cb0.
Definition DM_FRAME : Z := 2128.
Definition DM_WIN : Z := 14208.
Definition DM_KEEP : Z := 64.

Definition dm_rodata : list (Z * Z * list (Z * N * Z)) :=
[ (0xb1d98, 1, [(0, 1%N, 1)]);
(0xb1dbc, 4, [(0, 4%N, 30)]);
(0xa63e0, 8, [(0, 8%N, 0x142be8)]);
(0x142c08, 8, [(0, 8%N, 0x1e00010000)]) ].
Lemma dm_rodata_chk : forall ly, rodata_chk ly dm_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Definition dm_stk : YP09.region := YP09.mkRegion (Some 2%nat) (- DM_WIN) 0 (- DM_WIN) 0 [].
Definition DM_SS0 : sstate := mkSS DM_BODY sr_atoms (dm_stk :: map ro_region dm_rodata) None (mkFacts [] [] []).

Definition dm_runto (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL pc ss).

(* The prefix, 0x58b58 to the call of the unwinder. *)
Definition DM_U : sstate := Eval vm_compute in dm_runto DM_UNWIND DM_SS0.

Lemma dm_u_shape :
ss_pc DM_U = DM_UNWIND /\ ss_resv DM_U = None /\
sr_get (ss_regs DM_U) 1%bv = SLit DM_RET1 /\
sr_get (ss_regs DM_U) 2%bv = SOff 2 (- DM_FRAME) /\
sr_get (ss_regs DM_U) 4%bv = SOff 4 0 /\
sr_get (ss_regs DM_U) 8%bv = SOff 2 0 /\
sr_get (ss_regs DM_U) 9%bv = SOff 10 0 /\
sr_get (ss_regs DM_U) 10%bv = SOff 2 (- DM_FRAME) /\
sr_get (ss_regs DM_U) 11%bv = SLit DM_PC0 /\
sr_get (ss_regs DM_U) 12%bv = SOff 2 0 /\
sr_get (ss_regs DM_U) 13%bv = SLit 0 /\
sr_get (ss_regs DM_U) 14%bv = SLit 1 /\
sr_get (ss_regs DM_U) 15%bv = SLit 30.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The unwinder's call: the state keeps only the seven saved registers of the frame, [sp0 - 64, sp0), which lie
   above both the trace object [sp0 - 2128, sp0 - 64) and the unwinder's own frame. *)
Definition DM_HAV : nat := 64.
Definition dm_rsU : smem :=
Eval vm_compute in match ss_mem DM_U with r0 :: _ => [trim_lo r0 (- DM_KEEP)] | [] => [] end.
Definition DM_1 : sstate := Eval vm_compute in ss_after_call DM_U dm_rsU DM_HAV DM_RET1.
Definition DM_A : sstate := Eval vm_compute in dm_runto DM_ASAN DM_1.

(* asan_malloc's call, and the epilogue down to the return. *)
Definition DM_HAV2 : nat := 96.
Definition DM_2 : sstate := Eval vm_compute in ss_after_call DM_A (ss_mem DM_A) DM_HAV2 DM_RET2.
Definition DM_R : sstate := Eval vm_compute in dm_runto DM_EXIT DM_2.

(* The trampoline: one forward jump into the body, with no memory of its own. *)
Definition DM_SJ : sstate := mkSS DM_TRAMP sr_atoms [] None (mkFacts [] [] []).
Definition DM_J : sstate := Eval vm_compute in dm_runto DM_BODY DM_SJ.

Definition dm_u_r0 : YP09.region := Eval vm_compute in hd dm_stk (ss_mem DM_U).
Definition dm_a_r0 : YP09.region := Eval vm_compute in hd dm_stk (ss_mem DM_A).

Lemma dm_run_j : sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL DM_BODY DM_SJ = (DM_J, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma dm_run_u : sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL DM_UNWIND DM_SS0 = (DM_U, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma dm_run_a : sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL DM_ASAN DM_1 = (DM_A, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma dm_run_r : sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL DM_EXIT DM_2 = (DM_R, RS_running).
Proof. vm_compute. reflexivity. Qed.

Lemma dm_j_shape :
ss_pc DM_J = DM_BODY /\ ss_resv DM_J = None /\ ss_mem DM_J = [] /\
sr_get (ss_regs DM_J) 1%bv = SOff 1 0 /\
sr_get (ss_regs DM_J) 2%bv = SOff 2 0 /\
sr_get (ss_regs DM_J) 3%bv = SOff 3 0 /\
sr_get (ss_regs DM_J) 4%bv = SOff 4 0 /\
sr_get (ss_regs DM_J) 8%bv = SOff 8 0 /\
sr_get (ss_regs DM_J) 9%bv = SOff 9 0 /\
sr_get (ss_regs DM_J) 10%bv = SOff 10 0 /\
sr_get (ss_regs DM_J) 18%bv = SOff 18 0 /\
sr_get (ss_regs DM_J) 19%bv = SOff 19 0 /\
sr_get (ss_regs DM_J) 20%bv = SOff 20 0 /\
sr_get (ss_regs DM_J) 21%bv = SOff 21 0 /\
sr_get (ss_regs DM_J) 22%bv = SOff 22 0 /\
sr_get (ss_regs DM_J) 23%bv = SOff 23 0 /\
sr_get (ss_regs DM_J) 24%bv = SOff 24 0 /\
sr_get (ss_regs DM_J) 25%bv = SOff 25 0 /\
sr_get (ss_regs DM_J) 26%bv = SOff 26 0 /\
sr_get (ss_regs DM_J) 27%bv = SOff 27 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma dm_u_mem0 : nth_error (ss_mem DM_U) 0 = Some dm_u_r0.
Proof. vm_compute. reflexivity. Qed.
Lemma dm_u_r0_shape :
YP09.r_base dm_u_r0 = Some 2%nat /\ YP09.r_lo dm_u_r0 = - DM_WIN /\ YP09.r_hi dm_u_r0 = 0 /\
YP09.r_wlo dm_u_r0 = - DM_WIN /\ YP09.r_whi dm_u_r0 = 0 /\
nth_error (YP09.r_chunks dm_u_r0) 1 = Some (YP09.mkChunk (- 2120) (CVal 8 (SLit 0))) /\
nth_error (YP09.r_chunks dm_u_r0) 2 = Some (YP09.mkChunk (- DM_FRAME) (CVal 8 (SOff 2 (- 2112)))).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma dm_submem_u : submem dm_rsU (ss_mem DM_U).
Proof. apply submemb_sound. vm_compute. reflexivity. Qed.

Lemma dm_a_shape :
ss_pc DM_A = DM_ASAN /\ ss_resv DM_A = None /\ ss_mem DM_A = [dm_a_r0] /\
YP09.r_base dm_a_r0 = Some 2%nat /\ YP09.r_lo dm_a_r0 = - DM_KEEP /\ YP09.r_hi dm_a_r0 = 0 /\
YP09.r_wlo dm_a_r0 = - DM_KEEP /\ YP09.r_whi dm_a_r0 = 0 /\
sr_get (ss_regs DM_A) 1%bv = SLit DM_RET2 /\
sr_get (ss_regs DM_A) 2%bv = SOff 2 (- DM_FRAME) /\
sr_get (ss_regs DM_A) 3%bv = SOff 3 0 /\
sr_get (ss_regs DM_A) 4%bv = SOff 4 0 /\
sr_get (ss_regs DM_A) 10%bv = SOff 10 0 /\
sr_get (ss_regs DM_A) 11%bv = SOff 2 (- DM_FRAME).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma dm_r_shape :
ss_pc DM_R = DM_EXIT /\ ss_resv DM_R = None /\ ss_mem DM_R = [dm_a_r0] /\
sr_get (ss_regs DM_R) 1%bv = SOff 1 0 /\
sr_get (ss_regs DM_R) 2%bv = SOff 2 0 /\
sr_get (ss_regs DM_R) 3%bv = SOff 3 0 /\
sr_get (ss_regs DM_R) 4%bv = SOff 4 0 /\
sr_get (ss_regs DM_R) 8%bv = SOff 8 0 /\
sr_get (ss_regs DM_R) 9%bv = SOff 9 0 /\
sr_get (ss_regs DM_R) 18%bv = SOff 18 0 /\
sr_get (ss_regs DM_R) 19%bv = SOff 19 0 /\
sr_get (ss_regs DM_R) 20%bv = SOff 20 0 /\
sr_get (ss_regs DM_R) 21%bv = SOff 21 0 /\
sr_get (ss_regs DM_R) 22%bv = SOff 22 0 /\
sr_get (ss_regs DM_R) 23%bv = SOff 23 0 /\
sr_get (ss_regs DM_R) 24%bv = SOff 24 0 /\
sr_get (ss_regs DM_R) 25%bv = SOff 25 0 /\
sr_get (ss_regs DM_R) 26%bv = SOff 26 0 /\
sr_get (ss_regs DM_R) 27%bv = SOff 27 0 /\
sr_get (ss_regs DM_R) 10%bv = SOff 100 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma dm_ret_word : clookup tfibtbl_rtA DM_EXIT = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* One run of the table, in the form the walk uses it: the world is unchanged and the model only materializes. *)
Lemma dm_phase : forall (W : world tfibsegs) E ss ss' ms md stop,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL stop ss = (ss', RS_running) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' ms md stop HS Hrun.
eapply (SRr_run_to_sh_gen tfibsegs tfibtbl_rtA tfibtbl_rtA_ok AF0x.Hwx_tfa W FUEL stop E ss ss' RS_running ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1.
split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
End p.
