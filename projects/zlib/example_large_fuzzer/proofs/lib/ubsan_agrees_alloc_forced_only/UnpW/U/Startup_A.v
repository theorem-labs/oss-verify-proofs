(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ITree Nodes Decode. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import RegsEquiv. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Image.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import StrFun.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Startup_B.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_example_large_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import StoreFast.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation usegs := Image.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition init_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (sysinfo auxvp page_size : word) (m : word -> option byte) (t : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x3d708, 0x5d7d8); (0x5d7e0, 0x5d810); (RLIBC, 0x5dac0)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' RTD (td_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x3d780) (* [comment removed for export] *) (Z_to_bv 64 0x5da90) (* [comment removed for export] *) (Z_to_bv 64 0x3d7e0) (* [comment removed for export] *) z64)
    /\ rw_cells usegs m' RLIBC (libc_cells (Z_to_bv 8 1) auxvp (Z_to_bv 64 224) (Z_to_bv 64 8) page_size)
    (* [comment removed for export] *)
    /\ rw_cells usegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells usegs m' RSYSINFO [C8 sysinfo]
    /\ rw_cells usegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells usegs m' RGOT_DYNAMIC [C8 z64]
    /\ (0 < t < 4194304)%Z.

Lemma init_tls_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sysinfo page_size auxvp : word),
  stk usegs m lo (bv_unsigned sp) ->
  (* [comment removed for export] *)
  rw_cells usegs m (bv_unsigned a0 + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 10)] ->
  rw_cells usegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
  rw_cells usegs m RLIBC (libc_cells (Z_to_bv 8 0) auxvp z64 z64 page_size) ->
  rw_cells usegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
  rw_cells usegs m RSYSINFO [C8 sysinfo] ->
  rw_cells usegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
  rw_cells usegs m RGOT_DYNAMIC [C8 z64] ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 64)%Z -> (0x5f000 <= lo)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 48 <= 2^64)%Z ->
  impl usegs (at_node usegs) (enode NSetTid dec_set_tid)
       (epost (init_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo sysinfo auxvp page_size m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x231e0) fc None m (seg_rom usegs)).
Proof.
  intros until auxvp. intros ST AUX TDC LC MT SI DS GD MI LO LOLO A0LO A0HI.
  unfold td_cells, libc_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x3d708, 0x5d7d8); (0x5d7e0, 0x5d810); (RLIBC, 0x5dac0)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  apply impl_enode.
  carve_frame 64%nat ST.
  (* [comment removed for export] *)
  steps_to 0x232b8%Z.
  (* [comment removed for export] *)
  steps_to 0x2343c%Z.
  (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [-> Ht].
  unfold eff0. sys_nret.
  steps_to 0x2348c%Z.
  release_frame FR ST (bv_unsigned sp). astep.
  unfold init_tls_post, td_cells, libc_cells. unfold PID_MAX_ENVELOPE in Ht; cbn in Ht. sys_finish; lia.
Qed.

