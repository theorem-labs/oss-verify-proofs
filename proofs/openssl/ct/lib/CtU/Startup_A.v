(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Startup_B.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation ctusegs := ImageCt.ctusegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition init_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (sysinfo auxvp page_size : word) (m : word -> option byte) (t : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x333160, 0x353268); (RLIBC, 0x353520)]%Z m m'
    /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' RTD (td_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x3331d8) (* [comment removed for export] *) (Z_to_bv 64 0x3534f0) (* [comment removed for export] *) (Z_to_bv 64 0x333238) (* [comment removed for export] *) z64)
    /\ rw_cells ctusegs m' RLIBC (libc_cells (Z_to_bv 8 1) auxvp (Z_to_bv 64 224) (Z_to_bv 64 8) page_size)
    (* [comment removed for export] *)
    /\ rw_cells ctusegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells ctusegs m' RSYSINFO [C8 sysinfo]
    /\ rw_cells ctusegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells ctusegs m' RGOT_DYNAMIC [C8 z64]
    /\ (0 < t < 4194304)%Z.

Lemma init_tls_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sysinfo page_size auxvp : word),
  stk ctusegs m lo (bv_unsigned sp) ->
  (* [comment removed for export] *)
  rw_cells ctusegs m (bv_unsigned a0 + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 10)] ->
  rw_cells ctusegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
  rw_cells ctusegs m RLIBC (libc_cells (Z_to_bv 8 0) auxvp z64 z64 page_size) ->
  rw_cells ctusegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
  rw_cells ctusegs m RSYSINFO [C8 sysinfo] ->
  rw_cells ctusegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
  rw_cells ctusegs m RGOT_DYNAMIC [C8 z64] ->
  mem_inv ctusegs m ->
  (lo <= bv_unsigned sp - 64)%Z -> (0x355000 <= lo)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 48 <= 2^64)%Z ->
  impl ctusegs (at_node ctusegs) (enode NSetTid dec_set_tid)
       (epost (init_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo sysinfo auxvp page_size m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x2b298c) fc None m (seg_rom ctusegs)).
Proof.
  intros until auxvp. intros ST AUX TDC LC MT SI DS GD MI LO LOLO A0LO A0HI.
  unfold td_cells, libc_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x333160, 0x353268); (RLIBC, 0x353520)]%Z m) as MU.
  pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  apply impl_enode.
  carve_frame 64%nat ST.
  (* [comment removed for export] *)
  steps_to 0x2b2a64%Z.
  (* [comment removed for export] *)
  steps_to 0x2b2be8%Z.
  (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [-> Ht].
  unfold eff0. sys_nret.
  steps_to 0x2b2c38%Z.
  release_frame FR ST (bv_unsigned sp). astep.
  unfold init_tls_post, td_cells, libc_cells. unfold PID_MAX_ENVELOPE in Ht; cbn in Ht. sys_finish; lia.
Qed.

