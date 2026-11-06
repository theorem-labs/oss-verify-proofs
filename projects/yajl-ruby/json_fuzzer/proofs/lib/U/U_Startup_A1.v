(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import STRW_tac.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import U_StartupLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_memset UF_memcpy.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.


(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x55930%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x556a8%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x355d8%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x356a0%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x55918%Z (only parsing).
Notation RDEFSTACK := 0x25548%Z (only parsing).
Notation RGOT_DYNAMIC := 0x24218%Z (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rinit_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (sysinfo auxvp page_size : word) (m : word -> option byte) (t : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x355d8, 0x35728); (0x556b0, 0x556e0); (RLIBC, 0x55998)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' RTD (td_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x35650) (* [comment removed for export] *) (Z_to_bv 64 0x55968) (* [comment removed for export] *) (Z_to_bv 64 0x356b0) (* [comment removed for export] *) z64)
    /\ rw_cells usegs m' RLIBC (libc_cells (Z_to_bv 8 1) auxvp (Z_to_bv 64 224) (Z_to_bv 64 8) page_size)
    (* [comment removed for export] *)
    /\ rw_cells usegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells usegs m' RSYSINFO [C8 sysinfo]
    /\ rw_cells usegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells usegs m' RGOT_DYNAMIC [C8 z64]
    /\ (0 < t < 4194304)%Z.


(* [comment removed for export] *)
Lemma rinit_tls_from_17098 : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) fc (m m0 : word -> option byte) (lo : Z) (sysinfo page_size auxvp : word) (pad : list byte),
  rw_cells usegs m0 (bv_unsigned a0 + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 10)] ->
  rw_cells usegs m0 RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
  rw_cells usegs m0 RLIBC (libc_cells (Z_to_bv 8 0) auxvp z64 z64 page_size) ->
  rw_cells usegs m0 RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
  rw_cells usegs m0 RSYSINFO [C8 sysinfo] ->
  rw_cells usegs m0 RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
  rw_cells usegs m0 RGOT_DYNAMIC [C8 z64] ->
  mem_inv usegs m0 ->
  (lo <= bv_unsigned sp + -64)%Z -> (0x57000 <= lo)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 48 <= 2^64)%Z ->
  munch [((bv_unsigned sp + -64)%Z, bv_unsigned sp); (0x355d8%Z, 0x35728%Z); (0x556b0%Z, 0x556e0%Z); (RLIBC%Z, 0x55998%Z)] m m0 ->
  wmono usegs m m0 ->
  (0 <= bv_unsigned sp < 2^64)%Z ->
  stk usegs m0 lo (bv_unsigned sp + -64) ->
  rw_cells usegs m0 (bv_unsigned sp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt usegs (fun ms1 : machine_state => at_node usegs NSetTid ms1 /\ forall (rsp : resp) (a : Z), dec_set_tid rsp = Some a ->
               evt usegs (rinit_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo sysinfo auxvp page_size m a) (nret ms1 rsp))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp z64 (Z_to_bv 64 2) (Z_to_bv 64 7) (Z_to_bv 64 1879048195)
             (Z_to_bv 64 RLIBC) (Z_to_bv 64 56) (Z_to_bv 64 RTLL) z64 z64 (Z_to_bv 64 0x259f4) (Z_to_bv 64 0x10040) (Z_to_bv 64 6) z64
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1685382481) (Z_to_bv 64 0x10270) (zx32 (Z_to_bv 64 0x20000)) z64)
        F (Z_to_bv 64 0x17a8c) fc None m0 (seg_rom usegs)).
Proof.
  intros until pad. intros AUX TDC LC MT SI DS GD MI LO LOLO A0LO A0HI MU WM RSP ST FR.
  unfold td_cells, libc_cells in *.
  (* [comment removed for export] *)
  steps_to 0x17c10%Z.
  (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [-> Ht].
  unfold eff0. sys_nret.
  steps_to 0x17c60%Z.
  release_frame FR ST (bv_unsigned sp). astep.
  unfold rinit_tls_post, td_cells, libc_cells. unfold PID_MAX_ENVELOPE in Ht. sys_finish; lia.
Qed.
