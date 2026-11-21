(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (time_sr_stmt's vdso_func cell resolves to the vDSO entry hvdso, and TIME_STACK is 320: time's and clock_gettime's frames and the vDSO call's frame; the pre-revision proof of time_sr through a NULL __vdsosym and the clock_gettime trap, with vdsosym_spec, cgt_init_spec, time_front and dec_cg, is removed, the statement being proved for the run's instance in F_timeRun.v). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame ITree Nodes Decode.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time Require Import PosixTimers.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog STree Malloc MmNodes KLink CgNode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import RMalloc_iface RMalloc_ifaceP HeapSR_iface MallocSR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SReach SReachTree.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMallocRep RMallocTree RF_am_E F_syscalls. From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import STRW_tac.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition P_time : Z := 0x2c4ab4.
Definition P_clock_gettime : Z := 0x2c4574.
Definition P_cgt_init : Z := 0x2c462c.
Definition P_vdsosym : Z := 0x2c46b4.
Definition A_vdso_func : Z := 0x3234c0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amo_aligned_Z : forall wd z, 0 <= z < 2^64 -> z mod amo_bytes wd = 0 -> amo_aligned wd (Z_to_bv 64 z) = true.
Proof. intros wd z Hz Hm. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Ltac amo_fix :=
  repeat match goal with
  | |- context [amo_aligned ?wd (Z_to_bv 64 ?z)] =>
      rewrite (amo_aligned_Z wd z) by (first [cbn [amo_bytes]; lia | cbn [amo_bytes]; nia]); cbn [negb]
  end;
  repeat match goal with
  | |- context [Z.eqb ?x ?x] => rewrite (Z.eqb_refl x)
  end;
  cbv beta iota delta [amo_val inval_resv with_resv c_resv].
Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          amo_fix; simp_regs;
          try solve_load; try solve_store; reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.
Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

(* time()'s stack: its own 48-byte frame, clock_gettime's 32 bytes, and the vDSO call's frame
   F = [Vdso.vi_frame] = 240 (Vdso.v:314) below clock_gettime's sp: [Run.vdso_post]
   (Run.v:623-635) writes at most F bytes, into [[sp - F, sp)].  cgt_init's 32 bytes and
   __vdsosym's 112 lie inside that window.  48 + 32 + 240 = 320. *)
Definition TIME_STACK : Z := 320.

(* THE INTERFACE.  At LPS 727298f3 the auxv publishes the vDSO, so the first time() resolves
   [__clock_gettime]'s [vdso_func] cell from [P_cgt_init] to the vDSO's clock_gettime entry
   [hvdso] and every call reads the clock there (the model's vDSO node, [Spec/VdNode.v]).  The
   pre-revision proof of this statement (a NULL [__vdsosym] result and the clock_gettime trap)
   is false at the revision; the statement is proved for the run's instance
   ([F_timeRun.v]), whose reach is over the run's segment list. *)
Section Iface.
  Variable H : HeapSR_iface.hsr.
  (* [comment removed for export] *)
  Definition time_sr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list RMalloc_iface_stmt.block) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 (tv : word) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 tv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ HeapSR_iface.hs_KREL H s (cfg_model c) /\ HeapSR_iface.hs_MPRES H mo (cfg_model c)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv] /\ HeapSR_iface.hs_rauxv_ok H m' B /\ HeapSR_iface.hs_RHEAP H s LB m'
      /\ munch [(bv_unsigned sp - TIME_STACK, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8); (errno_addr tp, errno_addr tp + 4)]%Z m m' /\ wmono usegs m m'
      /\ rw_cells usegs m' A_vdso_func [C8 (Z_to_bv 64 hvdso)].

  Definition time_sr_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list RMalloc_iface_stmt.block) (lo B vf : Z) (errv : word) (mo : Model),
      HeapSR_iface.hs_RHEAP H s LB m -> HeapSR_iface.hs_KREL H s mo -> HeapSR_iface.hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      a0 = Z_to_bv 64 0 -> rw_cells usegs m A_vdso_func [C8 (Z_to_bv 64 vf)] -> (vf = hvdso \/ vf = P_cgt_init) ->
      HeapSR_iface.hs_SR H (time_sr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 entry) fc None m (seg_rom usegs)) mo).
  Definition time_sr_stmt : Prop := time_sr_stmt_at P_time TIME_STACK.
End Iface.
End HCW.
