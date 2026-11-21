(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Export Layout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_example_large_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RINIT_FLAG : Z := 0x3a6a0.     (* [comment removed for export] *)
Definition RIN_CB : Z := 0x3a6a4.         (* [comment removed for export] *)
Definition RATX_FIN : Z := 0x5a7f0.       (* [comment removed for export] *)
Definition RATX_LOCK : Z := 0x5a7f4.      (* [comment removed for export] *)
Definition RATX_HEAD : Z := 0x5a800.      (* [comment removed for export] *)
Definition RATX_BUILTIN : Z := 0x5a808.   (* [comment removed for export] *)
Definition RATX_A0 : Z := 0x5a910.        (* [comment removed for export] *)
Definition RDSO : Z := 0x2a438.           (* [comment removed for export] *)
Definition RLIBC_HEAD : Z := 0x5aa38.     (* [comment removed for export] *)
Definition R_ATEXIT : Z := 0x20534.
Definition R_CALL : Z := 0x205f8.
Definition R_FUNCS_ON_EXIT : Z := 0x20468.
Definition R_AEF_GUARD : Z := 0x15df4.
Definition ATEXIT_STACK : Z := 48.        (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive atx_state := ATX0 | ATX1.
Definition atx_n (k : atx_state) : Z := match k with ATX0 => 0 | ATX1 => 1 end.          (* [comment removed for export] *)
Definition atx_head (k : atx_state) : Z := match k with ATX0 => 0 | ATX1 => RATX_BUILTIN end.
Definition atx_f0 (k : atx_state) : Z := match k with ATX0 => 0 | ATX1 => R_CALL end.
Definition atx_a0 (k : atx_state) : Z := match k with ATX0 => 0 | ATX1 => R_AEF_GUARD end.

(* [comment removed for export] *)
Definition adp_cells (k : atx_state) (m : mem) : Prop :=
     rw_cells psegs m RINIT_FLAG [C1 (Z_to_bv 8 (atx_n k))]
  /\ rw_cells psegs m RIN_CB [C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m RATX_FIN [C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m RATX_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (atx_n k))]
  /\ rw_cells psegs m RATX_HEAD [C8 (Z_to_bv 64 (atx_head k)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (atx_f0 k))]
  /\ rw_cells psegs m RATX_A0 [C8 (Z_to_bv 64 (atx_a0 k))].

Definition rdrv_statics (m : mem) : Prop := exists k, adp_cells k m.

(* [comment removed for export] *)
Definition drv_addr (a : Z) : Prop := (RINIT_FLAG <= a < RINIT_FLAG + 5) \/ (RATX_FIN <= a < RATX_FIN + 296).

(* [comment removed for export] *)
Definition DRV_IVS : list (Z * Z) := [(RINIT_FLAG, RINIT_FLAG + 5); (RATX_FIN, RATX_FIN + 296)].

(* [comment removed for export] *)
Lemma rdrv_statics_of : forall k m, adp_cells k m -> rdrv_statics m.
Proof. intros k m H. exists k. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5a7f8, 0x5a818); (0x5a910, 0x5a918)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
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
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5a7f8, 0x5a818); (0x5a910, 0x5a918)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x205f4%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold atexit_post, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0, RATX_BUILTIN, R_CALL, RLIBC_HEAD. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5a7f0, 0x5a808)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
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
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5a7f0, 0x5a808)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  destruct k; cbn [atx_n atx_head atx_f0 atx_a0] in *; unfold RATX_BUILTIN, R_CALL, R_AEF_GUARD in *.
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    xsteps_to 0x280e0%Z. xstep. xstep. xstep.
    release_frame FR ST (bv_unsigned sp).
    unfold funcs_on_exit_post. sys_finish.
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    xsteps_to 0x280e0%Z. (* [comment removed for export] *)
    xstep. xstep. xstep.
    xsteps_to 0x15df4%Z. (* [comment removed for export] *)
    xsteps_to 0x204e8%Z. (* [comment removed for export] *)
    xsteps_to 0x20508%Z.
    xsteps_to 0x280e0%Z. xstep. xstep. xstep.
    release_frame FR ST (bv_unsigned sp).
    unfold funcs_on_exit_post. sys_finish.
Qed.
