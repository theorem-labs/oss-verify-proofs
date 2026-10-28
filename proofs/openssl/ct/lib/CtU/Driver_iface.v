(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog StrFun LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit X_atexit Exit_defs Startup Printf_stdio_iface Lib_iface Lib_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation ctusegs := ImageCt.ctusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.
Definition RMAIN : Z := 0xe1fe4.
Definition RTARGET_ALLOC_INIT : Z := 0xe22e0.   (* [comment removed for export] *)
Definition RTARGET_ALLOC_COUNT : Z := 0xe22e4.  (* [comment removed for export] *)
Definition RTARGET_RUN : Z := 0xe22ec.
Definition REMIT_PRINTF : Z := 0xe248c.
(* [comment removed for export] *)
Definition RINIT_FLAG : Z := 0x3306b0.    (* [comment removed for export] *)
Definition RGOT_LLVMINIT : Z := 0x31e790. (* [comment removed for export] *)
Definition REMPTY : Z := LX_EMPTY.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RTARGET_RUN_STACK : Z := 80 + LX_FUZZ_STACK.

(* [comment removed for export] *)
Definition ceil_ok (sp0 : word) : Prop := alloc_ceiling <= bv_unsigned sp0 - 8388608.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DRVW : list (Z * Z) :=
  [(RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024); (RINIT_FLAG, RINIT_FLAG + 5);
   (0x353278, 0x3532a0); (0x353398, 0x3533a0)] ++ LIBW.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rdrv_pres (LB : list block) (SP : Z) (m m' : mem) : Prop := lx_pres LB SP DRVW m m'.

Lemma rdrv_pres_refl : forall LB SP m, rdrv_pres LB SP m m.
Proof. intros; apply lx_pres_refl. Qed.

Lemma rdrv_pres_trans : forall LB SP m1 m2 m3, rdrv_pres LB SP m1 m2 -> rdrv_pres LB SP m2 m3 -> rdrv_pres LB SP m1 m3.
Proof. intros LB SP m1 m2 m3; apply lx_pres_trans. Qed.

Lemma rin_ivs_app : forall X Y a, rin_ivs (X ++ Y) a <-> rin_ivs X a \/ rin_ivs Y a.
Proof. induction X as [|iv X IH]; intros Y a; cbn; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Lemma rdrv_pres_of_lx : forall LB SP m m', lx_pres LB SP LIBW m m' -> rdrv_pres LB SP m m'.
Proof.
  intros LB SP m m' H. eapply lx_pres_weaken; [exact H| lia| auto|]. intros a Ha. unfold DRVW. apply rin_ivs_app. right. exact Ha.
Qed.
Lemma rdrv_pres_of_lx0 : forall LB SP m m', lx_pres LB SP [] m m' -> rdrv_pres LB SP m m'.
Proof. intros LB SP m m' H. eapply lx_pres_weaken; [exact H| lia| auto|]. intros a Ha. cbn in Ha. tauto. Qed.

Lemma rdrv_pres_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> rdrv_pres LB SP m m'.
Proof. intros LB SP m m' H. apply lx_pres_of_heap_pres. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIB_TCB : list (Z * Z) := [(0x333192, 0x333193); (0x3331c8, 0x3331d8)].
Definition tcb_lib_cells (m : mem) : Prop :=
  rw_cells ctusegs m 0x333192 [C1 (Z_to_bv 8 0)] /\ rw_cells ctusegs m 0x3331c8 [C8 (wz 0); C8 (wz 0)].

Definition drv_addr (a : Z) : Prop :=
  stdout_addr a \/ stderr_addr a \/ lxs_addr a \/ ssp_addr a \/ exit_statics_addr a
  \/ (RINIT_FLAG <= a < RINIT_FLAG + 32)              (* [comment removed for export] *)
  \/ (RGOT_LLVMINIT <= a < RGOT_LLVMINIT + 8)
  \/ (ctustage <= a < ctustage + 65536)                   (* [comment removed for export] *)
  \/ (0x320660 <= a < 0x320661) \/ (0x333158 <= a < 0x353528 /\ ~ rin_ivs LIB_TCB a).     (* [comment removed for export] *)

Class LibLaws : Prop := {
  LIBW_img : forall a, rin_ivs LIBW a -> 0x2c2000 <= a < 0x355000 /\ ~ ralloc_static a /\ ~ drv_addr a;
  LIB_STACK_lo : 8592 <= LIB_STACK;
  LIB_STACK_hi : LIB_STACK <= 4194304;
  lib_pristine_intro : forall m : mem, (forall a, 0 <= a < 2^64 -> rin_ivs LIBW a -> ~ rin_ivs LIB_TCB a -> m (wa a) = None) ->
                       tcb_lib_cells m -> lib_pristine m;   (* [comment removed for export] *)
  lib_pristine_agree : forall m m', lib_pristine m -> agree_on (fun a => rin_ivs LIBW a) m m' -> lib_pristine m';
  lib_inv_agree : forall ls OW m m', lib_inv ls m OW -> agree_on (fun a => rin_ivs LIBW a \/ in_block OW a) m m' -> lib_inv ls m' OW
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rtarget_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (B lo : Z) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' : word) (ib' : byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ 0 <= r <= 2
    /\ mem_inv ctusegs m' /\ frm0 fc' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ (exists OW', RHEAP s' (OW' ++ LB) m')          (* [comment removed for export] *)
    /\ ossl_exit_cells m'                              (* [comment removed for export] *)
    /\ lx_statics m' /\ stderr_wfile m' /\ ssp_cells m' rr_guard
    /\ stdout_file m' (ps_so s')
    /\ rw_cells ctusegs m' RINIT_FLAG [C1 ib']
    /\ atexit_cells_st true m'                         (* [comment removed for export] *)
    /\ rdrv_pres LB (bv_unsigned sp) m m'.

Definition rtarget_run_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (B lo : Z)
         (errv : word),
  RHEAP s LB m -> In (p, A, cap) LB ->
  bytes_at ctusegs m A (to_bytes content) -> Forall (fun c => 0 <= c < 256) content ->
  zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
  lx_statics m -> stderr_wfile m -> ssp_cells m rr_guard ->
  stdout_file m (ps_so s) ->
  rw_cells ctusegs m RINIT_FLAG [C1 (Z_to_bv 8 0)] -> rw_cells ctusegs m RGOT_LLVMINIT [C8 (wz LX_INIT)] ->   (* [comment removed for export] *)
  atexit_cells_st false m ->                            (* [comment removed for export] *)
  lib_pristine m ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - RTARGET_RUN_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv ctusegs m -> frm0 fc ->
  bv_unsigned sp mod 16 = 0 ->
  a0 = wz (A + 2) -> a1 = wz L -> a2 = wz (A + 6 + L) -> a3 = wz (zlength content - 6 - L) ->
  implM ctusegs (runG (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
        (rtarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB B lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz RTARGET_RUN) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rmain_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp ->
    entry_stack_fits sp0 argv envp ->
    at_main sp0 argv envp uid ms ->
    implM ctusegs (main_model io raw_malloc raw_free ctustage alloc_init runG alloc_count (argv_Z argv))
          (ps_init (reservedZ ctusegs))
          (fun code s' ms' => at_exit code s' ms') ms.
End WithCeiling0.
