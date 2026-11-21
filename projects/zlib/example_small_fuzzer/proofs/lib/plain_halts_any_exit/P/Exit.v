(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require ITree Nodes Decode SysStep RegsEquiv Image.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Decode OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.SysStep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Image.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.

Module F_atexit.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require ITree Nodes Decode SysStep RegsEquiv Image.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Decode OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.SysStep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Image.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.
Export OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac.Layout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Local Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte) (only parsing).

Definition RINIT_FLAG : Z := 0x3a380.
Definition RIN_CB : Z := 0x3a384.
Definition RATX_FIN : Z := 0x5a4d0.
Definition RATX_LOCK : Z := 0x5a4d4.
Definition RATX_HEAD : Z := 0x5a4e0.
Definition RATX_BUILTIN : Z := 0x5a4e8.
Definition RATX_A0 : Z := 0x5a5f0.
Definition RDSO : Z := 0x2a118.
Definition RLIBC_HEAD : Z := 0x5a718.
Definition R_ATEXIT : Z := 0x201e0.
Definition R_CALL : Z := 0x202a4.
Definition R_FUNCS_ON_EXIT : Z := 0x20114.
Definition R_AEF_GUARD : Z := 0x15d70.
Definition ATEXIT_STACK : Z := 48.

Inductive atx_state := ATX0 | ATX1.
Definition atx_n (k : atx_state) : Z := match k with ATX0 => 0 | ATX1 => 1 end.
Definition atx_head (k : atx_state) : Z := match k with ATX0 => 0 | ATX1 => RATX_BUILTIN end.
Definition atx_f0 (k : atx_state) : Z := match k with ATX0 => 0 | ATX1 => R_CALL end.
Definition atx_a0 (k : atx_state) : Z := match k with ATX0 => 0 | ATX1 => R_AEF_GUARD end.

Definition adp_cells (k : atx_state) (m : mem) : Prop :=
     rw_cells psegs m RINIT_FLAG [C1 (Z_to_bv 8 (atx_n k))]
  /\ rw_cells psegs m RIN_CB [C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m RATX_FIN [C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m RATX_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (atx_n k))]
  /\ rw_cells psegs m RATX_HEAD [C8 (Z_to_bv 64 (atx_head k)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (atx_f0 k))]
  /\ rw_cells psegs m RATX_A0 [C8 (Z_to_bv 64 (atx_a0 k))].

Definition rdrv_statics (m : mem) : Prop := exists k, adp_cells k m.

Definition drv_addr (a : Z) : Prop := (RINIT_FLAG <= a < RINIT_FLAG + 5) \/ (RATX_FIN <= a < RATX_FIN + 296).

Definition DRV_IVS : list (Z * Z) := [(RINIT_FLAG, RINIT_FLAG + 5); (RATX_FIN, RATX_FIN + 296)].

Lemma rdrv_statics_of : forall k m, adp_cells k m -> rdrv_statics m.
Proof. intros k m H. exists k. exact H. Qed.

Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (fn : word) (cdt thr sec : byte) (tm1 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5a4d8, 0x5a4f8); (0x5a5f0, 0x5a5f8)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' RATX_FIN [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m' RATX_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1)]
    /\ rw_cells psegs m' RATX_HEAD [C8 (Z_to_bv 64 RATX_BUILTIN); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 R_CALL)]
    /\ rw_cells psegs m' RATX_A0 [C8 fn]
    /\ rw_cells psegs m' RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].

Lemma atexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (f0 g0 : word) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) ->
  rw_cells psegs m RATX_FIN [C1 (Z_to_bv 8 0)] ->
  rw_cells psegs m RATX_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells psegs m RATX_HEAD [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 f0] ->
  rw_cells psegs m RATX_A0 [C8 g0] ->
  rw_cells psegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv psegs m ->
  lo <= bv_unsigned sp - 48 -> GLOBALS_TOP <= lo ->
  evt psegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 cdt thr sec tm1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R_ATEXIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST FIN LCK HD A0 LIBC MI LO LOLO.
  unfold RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0, RLIBC_HEAD, R_ATEXIT, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5a4d8, 0x5a4f8); (0x5a5f0, 0x5a5f8)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x202a0%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold atexit_post, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0, RATX_BUILTIN, R_CALL, RLIBC_HEAD. sys_finish.
Qed.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5a4d0, 0x5a4e8)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' RATX_FIN [C1 (Z_to_bv 8 1)].

Lemma funcs_on_exit_spec : forall (k : atx_state) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) ->
  rw_cells psegs m RIN_CB [C1 (Z_to_bv 8 0)] ->
  rw_cells psegs m RATX_FIN [C1 (Z_to_bv 8 0)] ->
  rw_cells psegs m RATX_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (atx_n k))] ->
  rw_cells psegs m RATX_HEAD [C8 (Z_to_bv 64 (atx_head k)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (atx_f0 k))] ->
  rw_cells psegs m RATX_A0 [C8 (Z_to_bv 64 (atx_a0 k))] ->
  rw_cells psegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv psegs m ->
  lo <= bv_unsigned sp - 48 -> GLOBALS_TOP <= lo ->
  evt psegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R_FUNCS_ON_EXIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST CB FIN LCK HD A0 LIBC MI LO LOLO.
  unfold RIN_CB, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0, RLIBC_HEAD, R_FUNCS_ON_EXIT, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5a4d0, 0x5a4e8)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  destruct k; cbn [atx_n atx_head atx_f0 atx_a0] in *; unfold RATX_BUILTIN, R_CALL, R_AEF_GUARD in *.
  -
    carve_frame 48%nat ST.
    xsteps_to 0x27dc0%Z. xstep. xstep. xstep.
    release_frame FR ST (bv_unsigned sp).
    unfold funcs_on_exit_post. sys_finish.
  -
    carve_frame 48%nat ST.
    xsteps_to 0x27dc0%Z.
    xstep. xstep. xstep.
    xsteps_to 0x15d70%Z.
    xsteps_to 0x20194%Z.
    xsteps_to 0x201b4%Z.
    xsteps_to 0x27dc0%Z. xstep. xstep. xstep.
    release_frame FR ST (bv_unsigned sp).
    unfold funcs_on_exit_post. sys_finish.
Qed.
End F_atexit.

Export OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Exit.F_atexit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.

Module Drv_sys.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac ITree Nodes SysStep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Image.
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call psegs m mm MU WM end end.
Import ListNotations.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Local Open Scope Z_scope.
Local Open Scope bv_scope.
Abbreviation rsegs := psegs.

Definition sysret_entry := 0x204d4%Z.
Definition read_entry := 0x27ed4%Z.
Definition close_entry := 0x27e74%Z.
Definition open_entry := 0x20388%Z.


Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt rsegs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x204d4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  -
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.


Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells rsegs m' B [CB n junk]
                    /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells rsegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Lemma read_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (0 < count <= 16777216)%Z ->
  (bv_unsigned a1 + count <= 2^63 - 1)%Z ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x27ed4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST DST ERR MI -> -> FD CNT TSM LO SEP1 SEP2 SEP3 TP.
  pose proof (rw_cells_below _ _ _ _ MI DST ltac:(cbn; lia)) as TOP47.
  cbn [cells_size csize] in TOP47. unfold UTOP in TOP47. rewrite Nat.add_0_r, Z2Nat.id in TOP47 by lia.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_read_Some in Hdec; [|lia].
  destruct ans as [e|bs].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    finish; lia.
  - destruct Hdec as [-> Hlen]. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    finish; lia.
Qed.


Lemma eintr_mask_errno : forall e, (1 <= e <= 4095)%Z ->
  Z_to_bv 64 (Z.land ((Z.b2z ((bv_unsigned (errno_ret e) + 4) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                     (bv_unsigned (errno_ret e)))
  = if (e =? 4)%Z then Z_to_bv 64 0 else errno_ret e.
Proof.
  intros e He. rewrite unsigned_errno_ret by lia.
  destruct (Z.eqb_spec e 4) as [->|Hne].
  - replace ((2 ^ 64 - 4 + 4) mod 18446744073709551616)%Z with 0%Z by reflexivity.
    cbn. reflexivity.
  - assert (Hnz : ((2 ^ 64 - e + 4) mod 18446744073709551616 <? 1)%Z = false).
    { apply Z.ltb_ge. destruct (Z.ltb_spec0 e 4).
      - replace (2 ^ 64 - e + 4)%Z with ((4 - e) + 1 * 18446744073709551616)%Z by lia.
        rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    rewrite Hnz. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. change (2^64)%Z with 18446744073709551616%Z.
    rewrite Z.mod_small by lia. unfold errno_ret. rewrite <- (Z_to_bv_minus_mod (18446744073709551616 - e)). f_equal. lia.
Qed.

Definition close_ret (a : sret) : word :=
  match a with
  | SVal _ => Z_to_bv 64 0
  | SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
  end.
Definition close_errno (a : sret) (errv : word) : word :=
  match a with
  | SVal _ => errv
  | SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
  end.

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (close_errno a errv)].

Lemma close_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NClose fd) dec_close)
       (epost (close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x27e74) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR MI -> FD LO SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|v].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 2 step. rewrite sextw_errno by lia.
    do 4 zstep. rewrite eintr_mask_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *.
    destruct (Z.eqb_spec e 4) as [->|Hne].
    + rewrite errno_of_lit in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. rewrite Z.eqb_refl. finish.
    + rewrite errno_of_errno_ret in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. replace (e =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). finish.
  - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. unfold eff0. sys_nret.
    do 6 zstep. rewrite Z.land_0_r. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed.


Definition got_ssp := 0x29100%Z.
Definition ssp_guard := 0x5a6f8%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at rsegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells rsegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Lemma open_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells rsegs m ssp_guard [C8 canary] ->
  mem_inv rsegs m ->
  a1 = Z_to_bv 64 0 ->
  ~ In (Z_to_bv 8 0) path ->
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NOpen path) dec_open)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x20388) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST SRC ERR GOT SSP MI -> NUL LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  (* at 727298f3 at_node (NOpen path) also asks the path's end below TASK_SIZE (Lib/Nodes,
     CHANGE-LIST row 3); it follows from MI and SRC by Lib/Mem's bytes_at_below; at_node_solve closes it by lia *)
  pose proof (bytes_at_below rsegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) MI SRC
                ltac:(intro E; apply app_eq_nil in E; destruct E as [_ E]; discriminate E)) as BT.
  rewrite length_app in BT. cbn [length] in BT. unfold UTOP in BT.
  apply impl_enode.
  carve_frame 96%nat ST.
  zidle_begin sp 96%Z MUz WMz.
  do 9 step.
  zidle_end MUz WMz.
  do 9 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. do 8 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. unfold eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.
End Drv_sys.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation psegs := Image.psegs.


Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells psegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells psegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells psegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x5ab58 0 2 mode 0xffffffff tail).

Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x2a318); (RSTDOUT_BUF, 0x5af60)]%Z m m'
      /\ wmono psegs m m' /\ mem_inv psegs m'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = [] 
      /\ stderr_file m'
      /\ rw_cells psegs m' 0x29100 [C8 (Z_to_bv 64 0x5a6f8)] /\ rw_cells psegs m' 0x5a6f8 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk psegs m lo (bv_unsigned sp) ->
      rw_cells psegs m 0x5a718 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      rw_cells psegs m 0x5ab48 [C8 z64] ->
      rw_cells psegs m 0x5ab38 [C8 z64] ->
      rw_cells psegs m 0x2a318 [C8 (Z_to_bv 64 RSTDOUT)] ->
      rw_cells psegs m 0x2a228 [C8 (Z_to_bv 64 RSTDERR)] ->
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells psegs m 0x29100 [C8 (Z_to_bv 64 0x5a6f8)] -> rw_cells psegs m 0x5a6f8 [C8 guard] ->
      mem_inv psegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x5b000 <= lo)%Z ->
      implM psegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x226f0) fc None m (seg_rom psegs)).
End StdioExitStatement.


Definition exit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (td0 td1 td2 td3 ra : word) (cdt thr sec : byte) (tm1 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x20364) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x226f0) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0x5a6f0, 0x5a6f4); (0x2a378, 0x2a379); (0x5a4d0, 0x5a4e8)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells psegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells psegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m' 0x5a6f0 [C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m' 0x2a378 [C1 (Z_to_bv 8 1)]
    /\ rw_cells psegs m' RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].

Lemma exit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
    (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) ->
  rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
  rw_cells psegs m 0x5a6f0 [C4 z64] ->
  rw_cells psegs m 0x29108 [C8 (Z_to_bv 64 0x28f18); C8 (Z_to_bv 64 0x28f10)] ->
  rw_cells psegs m 0x28f10 [C8 (Z_to_bv 64 0x158b8)] ->
  rw_cells psegs m 0x2a378 [C1 (Z_to_bv 8 0)] ->
  rw_cells psegs m 0x290a8 [C8 (Z_to_bv 64 0x201dc); C8 z64] ->
  rw_cells psegs m RDSO [C8 (Z_to_bv 64 RDSO)] ->
  rdrv_statics m ->
  rw_cells psegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 80)%Z -> (0x5b000 <= lo)%Z ->
  evt psegs (exit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra cdt thr sec tm1 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x202f8) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO [k ATX] LCH MI -> -> Ht LO LOLO.
  destruct ATX as (AL & ACB & AFIN & ALCK & AHD & AA0).
  unfold RINIT_FLAG, RIN_CB, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0, RLIBC_HEAD, RDSO in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0x5a6f0, 0x5a6f4); (0x2a378, 0x2a379); (0x5a4d0, 0x5a4e8)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  carve_frame 16%nat ST.
  do 6 lstep.
  replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  lstep. lstep.
  amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
  lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
  lstep. lstep.
  call_sp (funcs_on_exit_spec k);
    [ exact ST | exact ACB | exact AFIN | exact ALCK | exact AHD | exact AA0 | exact LCH | exact MI
    | lia | unfold GLOBALS_TOP; lia | ].
  lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST end.
  steps_to 0x202ac%Z.
  carve_frame 32%nat ST. steps_to 0x158b8%Z.
  carve_frame 16%nat ST. steps_to 0x15944%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
  steps_to 0x202f4%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
  astep.
  unfold exit_prefix_post. sys_finish.
Time Qed.

Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word),
    stk psegs m lo (bv_unsigned sp) ->
    rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells psegs m 0x5a6f0 [C4 z64] ->
    rw_cells psegs m 0x29108 [C8 (Z_to_bv 64 0x28f18); C8 (Z_to_bv 64 0x28f10)] ->
    rw_cells psegs m 0x28f10 [C8 (Z_to_bv 64 0x158b8)] ->
    rw_cells psegs m 0x2a378 [C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m 0x290a8 [C8 (Z_to_bv 64 0x201dc); C8 z64] ->
    rw_cells psegs m RDSO [C8 (Z_to_bv 64 RDSO)] ->
    rdrv_statics m ->
    rw_cells psegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells psegs m 0x5ab48 [C8 z64] -> rw_cells psegs m 0x5ab38 [C8 z64] ->
    rw_cells psegs m 0x2a318 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells psegs m 0x2a228 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells psegs m 0x29100 [C8 (Z_to_bv 64 0x5a6f8)] -> rw_cells psegs m 0x5a6f8 [C8 guard] ->
    mem_inv psegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x5b000 <= lo)%Z ->
    implM psegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x202f8) fc None m (seg_rom psegs)).
  Proof.
    intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO ATX LCH OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO.
    unfold RLIBC_HEAD, RDSO in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind psegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x20364) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x20364) fc None m' (seg_rom psegs))).
    -
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      call exit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact ATX | exact LCH | exact MI
                              | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x20364)) with (Z_to_bv 64 0x20364) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    -
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Time Qed.
End ExitProof.


Definition at_exit {St : Type} (get_so : St -> stdout_st) (code : Z) (s : St) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t : Z) (td0 td1 td2 td3 guard : word)
         (cdt thr sec : byte) (tm1 : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x202f8) fc None m (seg_rom psegs)
    /\ stk psegs m lo (bv_unsigned sp)
    /\ rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m 0x5a6f0 [C4 z64]
    /\ rw_cells psegs m 0x29108 [C8 (Z_to_bv 64 0x28f18); C8 (Z_to_bv 64 0x28f10)]
    /\ rw_cells psegs m 0x28f10 [C8 (Z_to_bv 64 0x158b8)]
    /\ rw_cells psegs m 0x2a378 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m 0x290a8 [C8 (Z_to_bv 64 0x201dc); C8 z64]
    /\ rw_cells psegs m RDSO [C8 (Z_to_bv 64 RDSO)]
    /\ rdrv_statics m
    /\ rw_cells psegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells psegs m 0x5ab48 [C8 z64] /\ rw_cells psegs m 0x5ab38 [C8 z64]
    /\ rw_cells psegs m 0x2a318 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells psegs m 0x2a228 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (get_so s) /\ stderr_file m
    /\ rw_cells psegs m 0x29100 [C8 (Z_to_bv 64 0x5a6f8)] /\ rw_cells psegs m 0x5a6f8 [C8 guard]
    /\ mem_inv psegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ (0 < t < 4194304)%Z /\ (lo <= bv_unsigned sp - 176)%Z /\ (0x5b000 <= lo)%Z.

Lemma exit_from_at_exit {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) :
  stdio_exit_spec_stmt get_so set_so ->
  forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop) code ms,
    at_exit get_so code s ms -> implM psegs (Driver.exit_model (io_S get_so set_so) code) s Q ms.
Proof.
  intros STDIO_EXIT s Q code ms H.
  destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                 td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & -> & H).
  destruct H as (ST & TD & EXL & GF & FA & FIN & GCX & DSO & ATX & LCH & OFL & SIN & SOU & SEU & SOF & SEF & GG & GU & MI & Htp & Ha0 & Ht & LO & LOLO).
  eapply (exit_spec get_so set_so STDIO_EXIT s Q);
    [exact ST | exact TD | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact ATX | exact LCH | exact OFL | exact SIN | exact SOU | exact SEU | exact SOF | exact SEF | exact GG | exact GU | exact MI | exact Htp | exact Ha0 | exact Ht | exact LO | exact LOLO].
Qed.

Lemma impl_msys_of_enode : forall segs {St A} (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
  impl segs (at_node segs) (enode n pl) (epost Q) ms ->
  impl segs (at_node segs) (Monad.msys n pl s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
  intros segs St A n pl Q s ms H. unfold Monad.msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.
