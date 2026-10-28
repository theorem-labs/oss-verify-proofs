(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition FR_CRYPTO_THREAD_wrap : Z := FR_CRYPTO_THREAD_read_lock.   (* [comment removed for export] *)
Definition FR_get_local_ex : Z := FR_CRYPTO_THREAD_get_local_ex.
Definition CRWLOCK_STACK : Z := FR_CRYPTO_THREAD_wrap.                       (* [comment removed for export] *)
Definition CUNLOCK_STACK : Z := FR_CRYPTO_THREAD_wrap + FR_mutex_unlock.
Definition CRUNONCE_STACK : Z := FR_CRYPTO_THREAD_wrap.
Definition CGETLOCAL_STACK : Z := FR_CRYPTO_THREAD_wrap.
Definition CGETLOCALEX_STACK : Z := FR_get_local_ex + FR_CRYPTO_THREAD_wrap.  (* [comment removed for export] *)
Definition CINITCRYPTO_STACK : Z := FR_OPENSSL_init_crypto + 32 + AFS_STACK.   (* [comment removed for export] *)

Definition OPENSSL_INIT_BASE_ONLY : Z := 262144.   (* [comment removed for export] *)
Definition CRYPTO_THREAD_LOCAL_ERR_KEY : Z := 3.
Definition CRYPTO_THREAD_NO_CONTEXT : Z := 1.

(* [comment removed for export] *)
Definition chain_below (c : errchain) (lo : Z) : Prop :=
     blk_addr (ec_mkey c) + 72 <= lo /\ blk_addr (ec_sa c) + 32 <= lo
  /\ blk_addr (ec_nodes c) + 128 <= lo /\ blk_addr (ec_es c) + ERRST_SIZE <= lo
  /\ 0 <= blk_addr (ec_mkey c) /\ 0 <= blk_addr (ec_sa c) /\ 0 <= blk_addr (ec_nodes c) /\ 0 <= blk_addr (ec_es c).

  (* [comment removed for export] *)
  Definition c2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : Z) (W : list (Z * Z)) (X : mem -> Prop) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ X m'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition crwlock_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (M lo : Z),
      a0 = Z_to_bv 64 M -> MUTEX m M 0 -> M mod 4 = 0 -> M + MUTEX_SIZE <= lo ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CRWLOCK_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (c2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 (mutex_foot M) (fun m' => MUTEX m' M MUTEX_HELD) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition cread_lock_stmt : Prop := crwlock_stmt_at P_CRYPTO_THREAD_read_lock.
  Definition cwrite_lock_stmt : Prop := crwlock_stmt_at P_CRYPTO_THREAD_write_lock.

  (* [comment removed for export] *)
  Definition cunlock_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (M lk lo : Z),
      a0 = Z_to_bv 64 M -> MUTEX m M lk -> 0 <= lk < 2^31 -> M mod 4 = 0 -> M + MUTEX_SIZE <= lo ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CUNLOCK_STACK -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (c2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 (mutex_foot M) (fun m' => MUTEX m' M 0) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_THREAD_unlock) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition crunonce_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (C lo : Z) (rest : list cell),
      a0 = Z_to_bv 64 C -> rw_cells asegs m C (C4 (wz 2) :: rest) -> (C + 4 <= lo \/ bv_unsigned sp <= C) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CRUNONCE_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (c2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 [] (fun _ => True) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_THREAD_run_once) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition cgetlocal_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (K k v lo : Z) (rest : list cell),
      a0 = Z_to_bv 64 K -> rw_cells asegs m K (C4 (wz k) :: rest) -> 0 <= k < 128 -> (K + 4 <= lo \/ bv_unsigned sp <= K) ->
      accessible m K 4 -> (K + 4 <= ALOWSH_LO \/ AHI_LO <= K) -> K mod 4 = 0 -> K <> 0 -> ACONST m ->   (* [comment removed for export] *)
      tp = Z_to_bv 64 ATP ->
      rw_cells asegs m A_td_tsd [C8 (wz A_tsd_main)] -> rw_cells asegs m (A_tsd_main + 8 * k) [C8 (wz v)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CGETLOCAL_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (c2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v [] (fun _ => True) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_THREAD_get_local) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition cgetlocalex_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LIB : list block) (c : errchain) (exl : ctxinfo) (lo : Z),
      a0 = Z_to_bv 64 CRYPTO_THREAD_LOCAL_ERR_KEY -> a1 = Z_to_bv 64 CRYPTO_THREAD_NO_CONTEXT -> tp = Z_to_bv 64 ATP ->
      CTX_statics m exl -> ERR_statics m c -> ERR_chain LIB m c -> chain_below c aceil ->          (* [comment removed for export] *)
      lib_shad LIB m -> ACONST m ->                                                              (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CGETLOCALEX_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (c2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (blk_addr (ec_es c)) []
                   (fun m' => CTX_statics m' exl /\ ERR_statics m' c /\ ERR_chain LIB m' c) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_THREAD_get_local_ex) fc None m (seg_rom asegs)).

Section W.
  Variable H : asr.
  (* [comment removed for export] *)
  Definition cinit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (c : errchain) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (XS : list (Z * Z)),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ Forall (fs_scratch H LF) XS
      /\ munch ((lo, bv_unsigned sp) :: XS) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ ERR_statics m' c /\ as_RFS H LF m' /\ ACONST m' /\ arelro_lib m'.
  Definition cinitcrypto_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (c : errchain) (LF : list fframe) (lo : Z),
      a0 = Z_to_bv 64 OPENSSL_INIT_BASE_ONLY -> a1 = Z_to_bv 64 0 ->
      ERR_statics m c ->
      ACONST m -> arelro_lib m ->                                                               (* [comment removed for export] *)
      as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> athr_cells m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->                                                               (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CINITCRYPTO_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (cinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF c lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_init_crypto) fc None m (seg_rom asegs)).

  Definition C2_stmts : Prop :=
    cread_lock_stmt /\ cwrite_lock_stmt /\ cunlock_stmt /\ crunonce_stmt /\ cgetlocal_stmt /\ cgetlocalex_stmt /\ cinitcrypto_stmt.
End W.

End HCW.
