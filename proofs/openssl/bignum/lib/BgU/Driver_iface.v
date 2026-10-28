(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog StrFun LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Exit X_atexit Exit_defs Startup Printf_stdio_iface Lib_iface Lib_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation bgusegs := ImageBg.bgusegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.
Definition RMAIN : Z := 0xe15bc.
Definition RTARGET_ALLOC_INIT : Z := 0xe18b8.
Definition RTARGET_ALLOC_COUNT : Z := 0xe18bc.
Definition RTARGET_RUN : Z := 0xe18c4.
Definition REMIT_PRINTF : Z := 0xe1a64.

Definition RINIT_FLAG : Z := 0x32e420.
Definition RGOT_LLVMINIT : Z := 0x31c508.
Definition REMPTY : Z := LX_EMPTY.

Definition RTARGET_RUN_STACK : Z := 80 + LX_FUZZ_STACK.

Definition ceil_ok (sp0 : word) : Prop := alloc_ceiling <= bv_unsigned sp0 - 8388608.

Definition DRVW : list (Z * Z) :=
  [(RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024); (RINIT_FLAG, RINIT_FLAG + 5);
   (0x350fe8, 0x351010); (0x351108, 0x351110)] ++ LIBW.

Definition rdrv_pres (LB : list block) (SP : Z) (m m' : mem) : Prop := lx_pres LB SP DRVW m m'.

Lemma rdrv_pres_trans : forall LB SP m1 m2 m3, rdrv_pres LB SP m1 m2 -> rdrv_pres LB SP m2 m3 -> rdrv_pres LB SP m1 m3.
Proof. intros LB SP m1 m2 m3; apply lx_pres_trans. Qed.

Lemma rin_ivs_app : forall X Y a, rin_ivs (X ++ Y) a <-> rin_ivs X a \/ rin_ivs Y a.
Proof. induction X as [|iv X IH]; intros Y a; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma rdrv_pres_of_lx : forall LB SP m m', lx_pres LB SP LIBW m m' -> rdrv_pres LB SP m m'.
Proof.
  intros LB SP m m' H. eapply lx_pres_weaken; [exact H| lia| auto|]. intros a Ha. unfold DRVW. apply rin_ivs_app. right. exact Ha.
Qed.

Lemma rdrv_pres_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> rdrv_pres LB SP m m'.
Proof. intros LB SP m m' H. apply lx_pres_of_heap_pres. exact H. Qed.

Definition LIB_TCB : list (Z * Z) := [(0x330f02, 0x330f03); (0x330f38, 0x330f48)].
Definition tcb_lib_cells (m : mem) : Prop :=
  rw_cells bgusegs m 0x330f02 [C1 (Z_to_bv 8 0)] /\ rw_cells bgusegs m 0x330f38 [C8 (wz 0); C8 (wz 0)].

Definition drv_addr (a : Z) : Prop :=
  stdout_addr a \/ stderr_addr a \/ lxs_addr a \/ ssp_addr a \/ exit_statics_addr a
  \/ (RINIT_FLAG <= a < RINIT_FLAG + 32)
  \/ (RGOT_LLVMINIT <= a < RGOT_LLVMINIT + 8)
  \/ (bgustage <= a < bgustage + 65536)
  \/ (0x31e3d0 <= a < 0x31e3d1) \/ (0x330ec8 <= a < 0x351298 /\ ~ rin_ivs LIB_TCB a).

Class LibLaws : Prop := {
  LIBW_img : forall a, rin_ivs LIBW a -> 0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ ~ drv_addr a;
  LIB_STACK_lo : 8592 <= LIB_STACK;
  LIB_STACK_hi : LIB_STACK <= 4194304;
  lib_pristine_intro : forall m : mem, (forall a, 0 <= a < 2^64 -> rin_ivs LIBW a -> ~ rin_ivs LIB_TCB a -> m (wa a) = None) ->
                       tcb_lib_cells m -> lib_pristine m;
  lib_pristine_agree : forall m m', lib_pristine m -> agree_on (fun a => rin_ivs LIBW a) m m' -> lib_pristine m';
  lib_inv_agree : forall ls OW m m', lib_inv ls m OW -> agree_on (fun a => rin_ivs LIBW a \/ in_block OW a) m m' -> lib_inv ls m' OW
}.

Definition rtarget_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (B lo : Z) (m : mem)
    (r : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (errv' : word) (ib' : byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bgusegs)
    /\ 0 <= r <= 2
    /\ mem_inv bgusegs m' /\ frm0 fc' /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ rw_cells bgusegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ (exists OW', RHEAP s' (OW' ++ LB) m')
    /\ ossl_exit_cells m'
    /\ lx_statics m' /\ stderr_wfile m' /\ ssp_cells m' rr_guard
    /\ stdout_file m' (ps_so s')
    /\ rw_cells bgusegs m' RINIT_FLAG [C1 ib']
    /\ atexit_cells_st true m'
    /\ rdrv_pres LB (bv_unsigned sp) m m'.

Definition rtarget_run_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A cap L : Z) (content : list Z) (B lo : Z)
         (errv : word),
  RHEAP s LB m -> In (p, A, cap) LB ->
  bytes_at bgusegs m A (to_bytes content) -> Forall (fun c => 0 <= c < 256) content ->
  zlength content <= cap -> cap <= 2^26 -> 0 <= L -> 6 + L <= zlength content ->
  lx_statics m -> stderr_wfile m -> ssp_cells m rr_guard ->
  stdout_file m (ps_so s) ->
  rw_cells bgusegs m RINIT_FLAG [C1 (Z_to_bv 8 0)] -> rw_cells bgusegs m RGOT_LLVMINIT [C8 (wz LX_INIT)] ->
  atexit_cells_st false m ->
  lib_pristine m ->
  rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - RTARGET_RUN_STACK ->
  rw_cells bgusegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
  mem_inv bgusegs m -> frm0 fc ->
  bv_unsigned sp mod 16 = 0 ->
  a0 = wz (A + 2) -> a1 = wz L -> a2 = wz (A + 6 + L) -> a3 = wz (zlength content - 6 - L) ->
  implM bgusegs (runG (if 0 <? L then znth content 2 else 0) (skipn (Z.to_nat (6 + L)) content)) s
        (rtarget_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB B lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz RTARGET_RUN) fc None m (seg_rom bgusegs)).

Definition rmain_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp ->
    entry_stack_fits sp0 argv envp ->
    at_main sp0 argv envp uid ms ->
    implM bgusegs (main_model io raw_malloc raw_free bgustage alloc_init runG alloc_count (argv_Z argv))
          (ps_init (reservedZ bgusegs))
          (fun code s' ms' => at_exit code s' ms') ms.
End WithCeiling0.
