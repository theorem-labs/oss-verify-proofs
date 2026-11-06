(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface Malloc_ifaceP.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Driver Prog.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Exit Lib_iface Lib_kit X_atexit.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition EXIT_STACK : Z := 16 + 32 + 32 + 32 + 32 + 256 + RMALLOC_STACK.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RTHR : Z := 0x3329fc.     (* [comment removed for export] *)
Definition thr_cells : list cell := [C4 (wz 0); C1 (Z_to_bv 8 0)].

Definition exit_statics (TID : Z) (m : mem) : Prop :=
  (* [comment removed for export] *)
  rw_cells usegs m 0x3329d0 [C8 (wz 0x3329d0); C8 (wz 0x3329d0); C8 (wz 0x3329d0); C8 (wz 0); C4 (wz TID)]
  /\ rw_cells usegs m RTHR thr_cells
  (* [comment removed for export] *)
  /\ rw_cells usegs m 0x352d08 [C4 (wz 0)]
  (* [comment removed for export] *)
  /\ rw_cells usegs m 0x31e598 [C8 (wz 0x2c2750); C8 (wz 0x2c2740)]
  /\ rw_cells usegs m 0x2c2740 [C8 (wz 0xe14b8); C8 (wz 0xf2b04)]
  (* [comment removed for export] *)
  /\ rw_cells usegs m 0x31fee8 [C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m 0x31dfc0 [C8 (wz 0x2b2424); C8 (wz 0)]
  /\ rw_cells usegs m 0x31f5a8 [C8 (wz 0x31f5a8)]
  (* [comment removed for export] *)
  /\ rw_cells usegs m 0x353160 [C8 (wz 0)]
  /\ rw_cells usegs m 0x31fd88 [C8 (wz 0x31fca0)]
  /\ rw_cells usegs m (0x31fca0 + 8) [C8 (wz 0); C8 (wz 0)]
  /\ rw_cells usegs m (0x31fca0 + 40) [C8 (wz 0); C8 (wz 0); C8 (wz 0)]
  /\ rw_cells usegs m (0x31fca0 + 140) [C4 (wz 0xffffffff)]
  /\ rw_cells usegs m 0x31fe78 [C8 (wz RSTDOUT)]
  /\ rw_cells usegs m 0x31fc98 [C8 (wz RSTDERR)].

(* [comment removed for export] *)
Definition exit_statics_addr (a : Z) : Prop :=
  (0x3329d0 <= a < 0x3329f4) \/ (0x3329fc <= a < 0x332a01) \/ (0x352d08 <= a < 0x352d0c)
  \/ (0x31e598 <= a < 0x31e5a8) \/ (0x2c2740 <= a < 0x2c2750)
  \/ (0x31fee8 <= a < 0x31fee9) \/ (0x31dfc0 <= a < 0x31dfd0) \/ (0x31f5a8 <= a < 0x31f5b0)
  \/ (0x353160 <= a < 0x353168) \/ (0x31fca0 <= a < 0x31fd90) \/ (0x31fe78 <= a < 0x31fe80) \/ (0x31fc98 <= a < 0x31fca0).

(* [comment removed for export] *)
Definition ossl_exit_addr (a : Z) : Prop := OSSL_BASE_INITED <= a < OSSL_BASE_INITED + 8.

(* [comment removed for export] *)
Lemma exit_statics_agree : forall (P : Z -> Prop) TID m m',
  (forall a, 0 <= a < 2^64 -> P a ->
     m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  (forall a, exit_statics_addr a -> P a) -> exit_statics TID m -> exit_statics TID m'.
Proof.
  intros P TID m m' AG0 HP H. assert (AG : agree_on P m m') by exact AG0. unfold exit_statics, RTHR, thr_cells in *.
  repeat (destruct H as [H0 H]; split;
          [eapply rw_cells_agree; [exact AG| exact H0| intros a Ha; apply HP; unfold exit_statics_addr; cbn in Ha; lia]| clear H0]).
  eapply rw_cells_agree; [exact AG| exact H| intros a Ha; apply HP; unfold exit_statics_addr; cbn in Ha; lia].
Qed.

(* [comment removed for export] *)
Lemma exit_statics_addr_client : forall a, exit_statics_addr a -> 0x2c2000 <= a < GLOBALS_TOP /\ ~ ralloc_static a.
Proof.
  intros a Ha. unfold exit_statics_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP,
    RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP in *. lia.
Qed.

(* [comment removed for export] *)
Lemma exit_statics_cancel : forall TID m, exit_statics TID m ->
  rw_cells usegs m (RMallocRep.RATP + -156) [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)].
Proof.
  intros TID m (_ & T & _). unfold RTHR, thr_cells in T.
  pose proof (proj1 (rw_cells_app usegs m 0x3329fc [C4 (wz 0); C1 (Z_to_bv 8 0)] _) T) as [H _].
  exact H.
Qed.

(* [comment removed for export] *)
Lemma ossl_exit_cells_agree : forall (P : Z -> Prop) m m',
  (forall a, 0 <= a < 2^64 -> P a ->
     m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  (forall a, ossl_exit_addr a -> P a) -> ossl_exit_cells m -> ossl_exit_cells m'.
Proof.
  intros P m m' AG0 HP (b0 & H1 & H2). assert (AG : agree_on P m m') by exact AG0. exists b0.
  unfold ossl_exit_addr, OSSL_BASE_INITED, OSSL_DO_GLOBAL_CLEANUP in *.
  split; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; cbn in Ha; lia]).
Qed.

Lemma ossl_exit_addr_client : forall a, ossl_exit_addr a -> 0x2c2000 <= a < GLOBALS_TOP /\ ~ ralloc_static a.
Proof.
  intros a Ha. unfold ossl_exit_addr, OSSL_BASE_INITED, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP,
    RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP in *. lia.
Qed.

(* [comment removed for export] *)
Definition atexit_vals (reg : bool) (slot head f0 a0v : Z) : Prop :=
  if reg then slot = 1 /\ head = 0x352b00 /\ f0 = 0x2b24ec /\ a0v = 0xe19bc else slot = 0 /\ head = 0 /\ f0 = 0 /\ a0v = 0.
Definition atexit_cells_st (reg : bool) (m : mem) : Prop :=
  exists (p1 p2 : list byte) (slot head f0 a0v : Z),
    rw_cells usegs m 0x352ae8 (atexit_cells (Z_to_bv 8 0) p1 p2 slot head 0 f0)
    /\ rw_cells usegs m 0x352c08 [C8 (Z_to_bv 64 a0v)]
    /\ rw_cells usegs m 0x32fef4 [C1 (Z_to_bv 8 0)]
    /\ atexit_vals reg slot head f0 a0v.

Definition atexit_addr (a : Z) : Prop :=
  (0x352ae8 <= a < 0x352b10) \/ (0x352c08 <= a < 0x352c10) \/ (0x32fef4 <= a < 0x32fef5).

Lemma atexit_cells_st_agree : forall (P : Z -> Prop) reg m m',
  (forall a, 0 <= a < 2^64 -> P a ->
     m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  (forall a, atexit_addr a -> P a) -> atexit_cells_st reg m -> atexit_cells_st reg m'.
Proof.
  intros P reg m m' AG0 HP (p1 & p2 & slot & head & f0 & a0v & H1 & H2 & H3 & HV). assert (AG : agree_on P m m') by exact AG0.
  exists p1, p2, slot, head, f0, a0v. unfold atexit_addr in HP.
  split; [| split; [| split; [| exact HV]]].
  - eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. apply HP. unfold atexit_cells in Ha. cbn in Ha. lia.
  - eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. apply HP. cbn in Ha. lia.
  - eapply rw_cells_agree; [exact AG| exact H3|]. intros a Ha. apply HP. cbn in Ha. lia.
Qed.

Lemma atexit_addr_client : forall a, atexit_addr a -> 0x2c2000 <= a < GLOBALS_TOP /\ ~ ralloc_static a.
Proof.
  intros a Ha. unfold atexit_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RATP,
    RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, GLOBALS_TOP in *. lia.
Qed.

(* [comment removed for export] *)
Definition at_exit (code : Z) (s : PState) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo TID B : Z) (LB : list block) (errv : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2b2540) fc None m (seg_rom usegs)
    /\ stk usegs m lo (bv_unsigned sp)
    /\ exit_statics TID m
    /\ (exists reg : bool, atexit_cells_st reg m)
    /\ ossl_exit_cells m
    /\ RHEAP s LB m
    /\ rw_cells usegs m (errno_addr tp) [C4 errv]
    /\ rauxv_ok m B /\ bv_unsigned sp <= B
    /\ stdout_file m (ps_so s) /\ stderr_file m
    /\ mem_inv usegs m
    /\ tp = Z_to_bv 64 RMallocRep.RATP /\ a0 = Z_to_bv 64 code
    /\ 0 < TID < 4194304
    /\ lo <= bv_unsigned sp - EXIT_STACK /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo.

(* [comment removed for export] *)
Definition exit_from_at_exit_stmt : Prop :=
  forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop) (code : Z) (ms : machine_state),
    at_exit code s ms -> implM usegs (Driver.exit_model io exit_hook code) s Q ms.
End WithCeiling0.
