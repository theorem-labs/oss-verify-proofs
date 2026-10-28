(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Exit Startup Printf_stdio_iface Fz_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_walk.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_ax.     (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN : Z := 0xe15bc.
Definition RTARGET_ALLOC_INIT : Z := 0xe18b8.   (* [comment removed for export] *)
Definition RTARGET_ALLOC_COUNT : Z := 0xe18bc.  (* [comment removed for export] *)
Definition RTARGET_RUN : Z := 0xe18c4.
Definition REMIT_PRINTF : Z := 0xe1a64.
(* [comment removed for export] *)
Definition RINIT_FLAG : Z := 0x32ddf0.    (* [comment removed for export] *)
Definition RGOT_LLVMINIT : Z := 0x31bed8. (* [comment removed for export] *)
Definition REMPTY : Z := LX_EMPTY.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RTARGET_RUN_STACK : Z := 80 + LX_FUZZ_STACK.

(* [comment removed for export] *)
Definition ceil_ok (sp0 : word) : Prop := alloc_ceiling <= bv_unsigned sp0 - 8388608.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DRVW : list (Z * Z) :=
  LXW_CLIENT ++ [LXW_STDERR; (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024); (RINIT_FLAG, RINIT_FLAG + 1);
   (RAEF_INCB, RAEF_INCB + 1); (RATEXIT, RATEXIT + 40); (RATEXIT_A0, RATEXIT_A0 + 8)].    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rdrv_pres (LB : list block) (SP : Z) (m m' : mem) : Prop := lx_pres LB SP DRVW m m'.

Lemma rdrv_pres_refl : forall LB SP m, rdrv_pres LB SP m m.
Proof. intros; apply lx_pres_refl. Qed.

Lemma rdrv_pres_trans : forall LB SP m1 m2 m3, rdrv_pres LB SP m1 m2 -> rdrv_pres LB SP m2 m3 -> rdrv_pres LB SP m1 m3.
Proof. intros LB SP m1 m2 m3; apply lx_pres_trans. Qed.

Lemma rdrv_pres_of_lx : forall LB SP m m', lx_pres LB SP (LXW_CLIENT ++ [LXW_STDERR]) m m' -> rdrv_pres LB SP m m'.
Proof. intros LB SP m m' H. eapply lx_pres_weaken; [exact H| lia| auto|]. intros a Ha. unfold DRVW, LXW_CLIENT in *. cbn in Ha |- *. tauto. Qed.

Lemma rdrv_pres_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> rdrv_pres LB SP m m'.
Proof. intros LB SP m m' H. apply lx_pres_of_heap_pres. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rtarget_run_post (C : cli_sig) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (B lo : Z) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' : word) (ib' : byte) (CLB' : list block),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ 0 <= r <= 2
    /\ mem_inv usegs m' /\ frm0 fc' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ RHEAP s' (CLB' ++ LB) m'                            (* [comment removed for export] *)
    /\ lx_statics m' /\ (exists fl, lx_flags m' fl) /\ stderr_wfile m' /\ ssp_cells m' rr_guard
    /\ stdout_file m' (ps_so s')
    /\ rw_cells usegs m' RINIT_FLAG [C1 ib']
    /\ AXSTAT true m'                                   (* [comment removed for export] *)
    /\ rdrv_pres LB (bv_unsigned sp) m m'
    /\ CLI C m' CLB'.

Definition rtarget_run_stmt (C : cli_sig) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (B lo : Z)
         (errv flags : word),
  RHEAP s LB m -> In (p, A, cap) LB ->
  bytes_at usegs m A (to_bytes content) -> Forall (fun c => 0 <= c < 256) content ->
  zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
  lx_statics m -> lx_flags m flags -> stderr_wfile m -> ssp_cells m rr_guard ->
  stdout_file m (ps_so s) ->
  rw_cells usegs m RINIT_FLAG [C1 (Z_to_bv 8 0)] -> rw_cells usegs m RGOT_LLVMINIT [C8 (wz LX_INIT)] ->
  AXSTAT false m ->                                     (* [comment removed for export] *)
  CLI0 C m ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - RTARGET_RUN_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv usegs m -> frm0 fc ->
  bv_unsigned sp mod 16 = 0 ->
  a0 = wz (A + 2) -> a1 = wz L -> a2 = wz (A + 6 + L) -> a3 = wz (zlength content - 6 - L) ->
  implM usegs (run (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
        (rtarget_run_post C ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB B lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz RTARGET_RUN) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cli0_at_main (C : cli_sig) : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) R F pc fc rv (m : mem) ro,
    at_main sp0 argv envp uid (MS R F pc fc rv m ro) -> CLI0 C m.

Definition rmain_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp ->
    entry_stack_fits sp0 argv envp ->
    at_main sp0 argv envp uid ms ->
    implM usegs (main_model io raw_malloc raw_free ustage alloc_init run alloc_count (argv_Z argv))
          (ps_init (reservedZ usegs))
          (fun code s' ms' => at_exit ps_so code s' ms') ms.
End WithCeiling0.
