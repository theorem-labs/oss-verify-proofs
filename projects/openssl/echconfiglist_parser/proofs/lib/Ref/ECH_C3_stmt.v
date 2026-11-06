(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState
     ECH_C0_stmt ECH_C1_stmt ECH_C2_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition CTXINIT_CNT : Z := 160.
Definition CTXINIT_BYTES : Z := 2^16.
Definition CTXINIT_BIG : Z := 2.
Definition CTXINIT_STACK : Z := 1024 + RREALLOC_STACK.
Definition GETDEFCTX_STACK : Z := FR_get_default_context + CGETLOCAL_STACK.                 (* [comment removed for export] *)
Definition ctxph_cnt (ph : ctxphase) : Z := match ph with CtxFresh => CTXINIT_CNT | CtxReady _ => 0 end.
Definition ctxph_bytes (ph : ctxphase) : Z := match ph with CtxFresh => CTXINIT_BYTES | CtxReady _ => 0 end.
Definition ctxph_big (ph : ctxphase) : Z := match ph with CtxFresh => CTXINIT_BIG | CtxReady _ => 0 end.
Definition ctxph_stack (ph : ctxphase) : Z := match ph with CtxFresh => FR_get_default_context + CTXINIT_STACK | CtxReady _ => GETDEFCTX_STACK end.
(* [comment removed for export] *)
Definition ctxph_foot (ph : ctxphase) : list (Z * Z) := match ph with CtxFresh => CTX_X | CtxReady _ => [] end.
Lemma Forall_ctxph_foot : forall (P : Z * Z -> Prop) ph, Forall P CTX_X -> Forall P (ctxph_foot ph).
Proof. intros P [|x] HF; [exact HF| apply Forall_nil]. Qed.
Lemma rin_ivs_ctxph_foot : forall ph a, rin_ivs (ctxph_foot ph) a -> rin_ivs CTX_X a.
Proof. intros [|x] a Ha; [exact Ha| destruct Ha]. Qed.
Definition ctxph_delta (ph : ctxphase) (LBN : list block) (x : ctxinfo) : Prop :=
  match ph with
  | CtxReady x0 => x = x0 /\ LBN = []
  | CtxFresh => Z.of_nat (length LBN) <= CTXINIT_CNT /\ lb_bytes LBN <= CTXINIT_BYTES /\ lb_big LBN <= 1
               /\ In (cx_exlock x) LBN /\ (exists po pi, In (po, cx_olock x, 40) LBN /\ In (pi, cx_ilock x, 40) LBN)
  end.
Definition GETGLOBAL_STACK (ph : ctxphase) : Z := FR_ossl_lib_ctx_get_ex_data_global + ctxph_stack ph.
Definition GETANDLOCK_STACK : Z := FR_get_and_lock + CRWLOCK_STACK.
Definition NEWEX_INNER : Z := Z.max GETANDLOCK_STACK CUNLOCK_STACK.                            (* [comment removed for export] *)
Definition CNEWEX_STACK (ph : ctxphase) : Z := FR_CRYPTO_new_ex_data + FR_ossl_crypto_new_ex_data_ex + Z.max (GETGLOBAL_STACK ph) NEWEX_INNER.
Definition CNEWEX_READY_STACK : Z := FR_CRYPTO_new_ex_data + FR_ossl_crypto_new_ex_data_ex + Z.max (FR_ossl_lib_ctx_get_ex_data_global + GETDEFCTX_STACK) NEWEX_INNER.
Definition GETGLOBAL_READY_STACK : Z := FR_ossl_lib_ctx_get_ex_data_global + GETDEFCTX_STACK.
Definition CFREEEX_STACK : Z := FR_CRYPTO_free_ex_data + Z.max GETGLOBAL_READY_STACK NEWEX_INNER.
Definition CRYPTO_EX_INDEX_BIO : Z := 12.
Definition A_defctx_global : Z := A_defctx + 8.      (* [comment removed for export] *)

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  Definition c3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : Z) (W : list (Z * Z)) (X : mem -> Prop) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ a0 = Z_to_bv 64 rv
      /\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ X m'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition getdefctx_ready_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (x : ctxinfo) (lo : Z),
      tp = Z_to_bv 64 RATP -> CTX_statics m x ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - GETDEFCTX_STACK -> mem_inv rsegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt rsegs (c3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_defctx [] (fun m' => CTX_statics m' x) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_get_default_context) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition getdefctx_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (ph : ctxphase) (rv lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBN : list block) (x : ctxinfo),
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' (LBN ++ LB) m' /\ ctxph_delta ph LBN x /\ CTXPH (LBN ++ LB) m' (CtxReady x) /\ (ph = CtxFresh -> CTX_keys m')
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ relro_lib m'
      /\ xpres LB (bv_unsigned sp) (ctxph_foot ph) m m'.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition getdefctx_stmt_for (entry rv : Z) (stack : ctxphase -> Z) (ph : ctxphase) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (lo B : Z) (errv : word),
      a0 = Z_to_bv 64 0 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + ctxph_bytes ph <= hs_LIVE_MAX H -> Z.of_nat (length LB) + ctxph_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big LB + ctxph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack ph ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m -> CTXPH LB m ph -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (getdefctx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph rv lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)) mo).
  Definition getdefctx_stmt_at (entry rv : Z) (stack : ctxphase -> Z) : Prop := forall ph, getdefctx_stmt_for entry rv stack ph.
  Definition getdefctx_fresh_stmt : Prop := getdefctx_stmt_for P_get_default_context A_defctx ctxph_stack CtxFresh.
  (* [comment removed for export] *)
  Definition getdefctx_stmt : Prop := getdefctx_stmt_at P_get_default_context A_defctx ctxph_stack.
  Definition getglobal_stmt : Prop := getdefctx_stmt_at P_ossl_lib_ctx_get_ex_data_global A_defctx_global GETGLOBAL_STACK.
  Definition getglobal_ready_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (x : ctxinfo) (lo : Z),
      a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 RATP -> CTX_statics m x ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - GETGLOBAL_READY_STACK -> mem_inv rsegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt rsegs (c3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_defctx_global [] (fun m' => CTX_statics m' x) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_lib_ctx_get_ex_data_global) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition getandlock_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (x : ctxinfo) (rd lo : Z),
      let b := cx_exlock x in
      a0 = Z_to_bv 64 A_defctx_global -> a1 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a2 = Z_to_bv 64 rd -> 0 <= rd < 2 ->
      CTX_statics m x -> EXLOCK LB m b ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - GETANDLOCK_STACK -> mem_inv rsegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt rsegs (c3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_defctx_exmeth_bio (mutex_foot (blk_addr b))
                   (fun m' => CTX_statics m' x /\ MUTEX m' (blk_addr b) MUTEX_HELD) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_get_and_lock) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cnewex_ready_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (x : ctxinfo) (obj ad c0 k0 lo : Z),
      let b := cx_exlock x in
      a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a1 = Z_to_bv 64 obj -> a2 = Z_to_bv 64 ad -> tp = Z_to_bv 64 RATP ->
      rw_cells rsegs m ad [C8 (wz c0); C8 (wz k0)] -> ad + 16 <= lo -> off_image ad 16 ->
      CTX_statics m x -> EXLOCK LB m b -> (ad + 16 <= blk_addr b \/ blk_addr b + MUTEX_SIZE <= ad) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - CNEWEX_READY_STACK -> mem_inv rsegs m ->
      IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (c3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 ((ad, ad + 16) :: mutex_foot (blk_addr b))
                   (fun m' => CTX_statics m' x /\ EXLOCK LB m' b /\ rw_cells rsegs m' ad [C8 (wz 0); C8 (wz 0)]) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_new_ex_data) fc None m (seg_rom rsegs)).
  (* [comment removed for export] *)
  Definition cnewex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (ph : ctxphase) (ad lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBN : list block) (x : ctxinfo),
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' (LBN ++ LB) m' /\ ctxph_delta ph LBN x /\ CTXPH (LBN ++ LB) m' (CtxReady x) /\ (ph = CtxFresh -> CTX_keys m')
      /\ rw_cells rsegs m' ad [C8 (wz 0); C8 (wz 0)]
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ relro_lib m'
      /\ xpres LB (bv_unsigned sp) ((ad, ad + 16) :: ctxph_foot ph) m m'.   (* [comment removed for export] *)
  Definition cnewex_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (ph : ctxphase)
           (obj ad c0 k0 lo B : Z) (errv : word),
      a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a1 = Z_to_bv 64 obj -> a2 = Z_to_bv 64 ad ->
      rw_cells rsegs m ad [C8 (wz c0); C8 (wz k0)] -> xclient_range LB (bv_unsigned sp) CTX_X ad 16 -> off_image ad 16 -> ad + 16 <= B ->
      (forall x, ph = CtxReady x -> ad + 16 <= blk_addr (cx_exlock x) \/ blk_addr (cx_exlock x) + MUTEX_SIZE <= ad) ->
                                                  (* [comment removed for export] *)
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + ctxph_bytes ph <= hs_LIVE_MAX H -> Z.of_nat (length LB) + ctxph_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big LB + ctxph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - CNEWEX_STACK ph ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m -> CTXPH LB m ph -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (cnewex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph ad lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_new_ex_data) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cfreeex_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (x : ctxinfo) (obj ad lo : Z),
      let b := cx_exlock x in
      a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a1 = Z_to_bv 64 obj -> a2 = Z_to_bv 64 ad -> tp = Z_to_bv 64 RATP ->
      rw_cells rsegs m ad [C8 (wz 0); C8 (wz 0)] -> ad + 16 <= lo -> off_image ad 16 ->
      CTX_statics m x -> EXLOCK LB m b -> (ad + 16 <= blk_addr b \/ blk_addr b + MUTEX_SIZE <= ad) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - CFREEEX_STACK -> mem_inv rsegs m ->
      IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (c3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 ((ad, ad + 16) :: mutex_foot (blk_addr b))
                   (fun m' => CTX_statics m' x /\ EXLOCK LB m' b /\ rw_cells rsegs m' ad [C8 (wz 0); C8 (wz 0)]) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_free_ex_data) fc None m (seg_rom rsegs)).

  Definition C3_stmts : Prop :=
    getdefctx_ready_stmt /\ getdefctx_stmt /\ getglobal_ready_stmt /\ getglobal_stmt /\ getandlock_stmt
    /\ cnewex_ready_stmt /\ cnewex_stmt /\ cfreeex_stmt.
End W.
End HCW.
