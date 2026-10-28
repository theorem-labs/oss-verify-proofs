(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1bs X1c2 X1bn X1cc X1c6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1rl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qv X0qx.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1fd.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.
Import X1bs.Exc.

Notation rsegs := X1ff.rsegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x6d6d8%Z (only parsing).
Notation RTLL := 0x6d458%Z (only parsing).
Notation RTD := 0x4d388%Z (only parsing).
Notation RTP := 0x4d450%Z (only parsing).
Notation RSYSINFO := 0x6d6c0%Z (only parsing).
Notation RDEFSTACK := 0x3d2f0%Z (only parsing).
Notation RGOT_DYNAMIC := 0x3bfe8%Z (only parsing).

Definition rinit_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (sysinfo auxvp page_size : word) (m : word -> option byte) (t : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RTD, 0x4d4d8); (0x6d460, 0x6d490); (RLIBC, 0x6d740)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' RTD (td_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
(Z_to_bv 64 0x4d400)   (Z_to_bv 64 0x6d710)   (Z_to_bv 64 0x4d460)   z64)
/\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) auxvp (Z_to_bv 64 224) (Z_to_bv 64 8) page_size)

/\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
/\ rw_cells rsegs m' RSYSINFO [C8 sysinfo]
/\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
/\ (0 < t < 4194304)%Z.

Lemma rinit_tls_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sysinfo page_size auxvp : word),
stk rsegs m lo (bv_unsigned sp) ->

rw_cells rsegs m (bv_unsigned a0 + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 10)] ->
rw_cells rsegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
rw_cells rsegs m RLIBC (libc_cells (Z_to_bv 8 0) auxvp z64 z64 page_size) ->
rw_cells rsegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
rw_cells rsegs m RSYSINFO [C8 sysinfo] ->
rw_cells rsegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
mem_inv rsegs m ->
(lo <= bv_unsigned sp - 64)%Z -> (0x6e000 <= lo)%Z ->
(bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 48 <= 2^64)%Z ->
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid)
(epost (rinit_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo sysinfo auxvp page_size m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x310d4) fc None m (seg_rom rsegs)).
Proof.
intros until auxvp. intros ST AUX TDC LC MT SI DS GD MI LO LOLO A0LO A0HI.
unfold td_cells, libc_cells in *.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RTD, 0x4d4d8); (0x6d460, 0x6d490); (RLIBC, 0x6d740)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
apply impl_enode.
carve_frame 64%nat ST.

steps_to 0x311ac%Z.

steps_to 0x31330%Z.

step_ecall.
split. { at_node_solve. }
intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [Hc Ht].
sys_nret.
steps_to 0x31380%Z.
release_frame FR ST (bv_unsigned sp). astep.
unfold rinit_tls_post, td_cells, libc_cells. unfold PID_MAX_ENVELOPE in Ht. sys_finish; lia.
Qed.
