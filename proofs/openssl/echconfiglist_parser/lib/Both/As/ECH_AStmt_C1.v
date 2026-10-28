(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition CMALLOC_STACK : Z := FR_CRYPTO_malloc + AMALLOC_STACK.        (* [comment removed for export] *)
Definition CZALLOC_STACK : Z := FR_CRYPTO_zalloc + CMALLOC_STACK.         (* [comment removed for export] *)
Definition CFREE_STACK : Z := 16 + AFREE_STACK.
Definition CMEMDUP_STACK : Z := FR_CRYPTO_memdup + CMALLOC_STACK.
Definition CSTRNDUP_STACK : Z := FR_CRYPTO_strndup + CMALLOC_STACK.
Definition CARRAY_STACK : Z := FR_CRYPTO_array + CZALLOC_STACK.           (* [comment removed for export] *)
Definition CREALLOC_STACK : Z := FR_CRYPTO_realloc + AREALLOC_STACK.
Definition CREALLOC_ARRAY_STACK : Z := FR_CRYPTO_array + CREALLOC_STACK.
(* [comment removed for export] *)
Definition AREALLOC_MAX : Z := 64512.

(* [comment removed for export] *)
Definition MEMFLAG (m : mem) (v : Z) : Prop :=
  exists fb : byte, rw_cells asegs m A_mem_inited [C1 fb] /\ bv_unsigned fb = v /\ (v = 0 \/ v = 1).
Definition memflag_foot : list (Z * Z) := [(A_mem_inited, A_mem_inited + 1)].

(* [comment removed for export] *)
Definition ashobj (H : asr) (LB : list block) (SP A n : Z) : Prop :=
     (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b)
  \/ (as_FSB H <= A /\ A + n <= as_FSB H + AFS_SIZE)
  \/ SP <= A.
(* [comment removed for export] *)
Definition offchain (CH : list (Z * Z)) (A n : Z) : Prop := forall fp' ra', In (fp', ra') CH -> A + n <= fp' - 16 \/ fp' <= A.

(* [comment removed for export] *)
Fixpoint strnlen (bs : list byte) : nat :=
  match bs with [] => 0 | b :: bs' => if (bv_unsigned b =? 0)%Z then 0 else S (strnlen bs') end.
Lemma strnlen_le : forall bs, (strnlen bs <= length bs)%nat.
Proof. induction bs as [|b bs IH]; cbn; [lia|]. destruct (bv_unsigned b =? 0); cbn; lia. Qed.

(* [comment removed for export] *)
Definition PF_cmalloc : list (Z * list Z) := [(APC0_MALLOC, [R_CRYPTO_malloc_malloc])].
Definition PF_czalloc : list (Z * list Z) := pf_shift R_CRYPTO_zalloc_CRYPTO_malloc PF_cmalloc.
Definition PF_cfree : list (Z * list Z) := [(APC0_FREE, [])].                       (* [comment removed for export] *)
Definition PF_cmemdup : list (Z * list Z) := pf_shift R_CRYPTO_memdup_CRYPTO_malloc PF_cmalloc.
Definition PF_cstrndup : list (Z * list Z) := pf_shift R_CRYPTO_strndup_CRYPTO_malloc PF_cmalloc.
Definition PF_crealloc : list (Z * list Z) := [(APC0_REALLOC, [R_CRYPTO_realloc_realloc])].   (* [comment removed for export] *)

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) junk (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ ablock_range H A n /\ as_RHEAP H s' ((p, A, n) :: LB) m'
      /\ rw_cells asegs m' A [CB (Z.to_nat n) junk] /\ addressable m' A n
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H n.

  Definition cmalloc_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (n v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 n -> 1 <= n <= 2^28 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + n <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_cmalloc (bv_unsigned ra) CH -> as_Cm H n <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      as_SR H (cmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo) (mkCfg msF mo).
  Definition cmalloc_stmt : Prop := cmalloc_stmt_at P_CRYPTO_malloc CMALLOC_STACK.
  (* [comment removed for export] *)
  Definition cmalloc_array_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (num size v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_CRYPTO_malloc_array) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 num -> a1 = Z_to_bv 64 size -> 0 <= num < 2^32 -> 0 <= size < 2^32 -> 1 <= num * size <= 2^28 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + num * size <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CARRAY_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_cmalloc (bv_unsigned ra) CH -> as_Cm H (num * size) <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      as_SR H (cmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (num * size) lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition cmalloc0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp).
  Definition cmalloc0_stmt_at (entry fr : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - fr -> mem_inv asegs m -> ACONST m -> IMPL_mem m -> GOT_mem m ->   (* [comment removed for export] *)
      evt asegs (cmalloc0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition cmalloc0_stmt : Prop := cmalloc0_stmt_at P_CRYPTO_malloc FR_CRYPTO_malloc.
  Definition cmalloc_array0_stmt : Prop := cmalloc0_stmt_at P_CRYPTO_malloc_array (FR_CRYPTO_array + FR_CRYPTO_malloc).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition czalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (n lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ ablock_range H A n /\ as_RHEAP H s' ((p, A, n) :: LB) m'
      /\ rw_cells asegs m' A [CB (Z.to_nat n) (zeros (Z.to_nat n))] /\ addressable m' A n
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H n.
  Definition czalloc_stmt_gen (entry stack : Z) (arr : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (num size v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 num -> (if arr then a1 = Z_to_bv 64 size /\ 0 <= num < 2^32 /\ 0 <= size < 2^32 else size = 1) ->
      1 <= num * size <= 2^28 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + num * size <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_czalloc (bv_unsigned ra) CH -> as_Cm H (num * size) <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      as_SR H (czalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (num * size) lo B m mo) (mkCfg msF mo).
  Definition czalloc_stmt : Prop := czalloc_stmt_gen P_CRYPTO_zalloc CZALLOC_STACK false.
  Definition ccalloc_stmt : Prop := czalloc_stmt_gen P_CRYPTO_calloc CARRAY_STACK true.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (p : bptr) (n lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ xpres H (as_lb_remove H p LB) (bv_unsigned sp) [] m m'
      /\ as_RHEAP H s' (as_lb_remove H p LB) m'
      /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cf H n.
  Definition cfree_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (CH : list (Z * Z)) (bs : list byte),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 A -> as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> In (p, A, n) LB ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_cfree (bv_unsigned ra) CH -> as_Cf H n <= as_AL H s ->
      rw_cells asegs m A [CB (Z.to_nat n) bs] -> addressable m A n ->
      IMPL_mem m -> GOT_mem m ->
      as_SR H (cfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n lo B errv m mo) (mkCfg msF mo).

  Definition cfree_null_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) [] m m'
      /\ as_RHEAP H s' LB m'
      /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cf H 0.
  Definition cfree_null_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (lo B : Z) (errv : word)
           (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> as_Cf H 0 <= as_AL H s ->          (* [comment removed for export] *)
      IMPL_mem m -> GOT_mem m ->
      as_SR H (cfree_null_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo) (mkCfg msF mo).

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cmemdup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (bs : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ ablock_range H A (zlength bs) /\ as_RHEAP H s' ((p, A, zlength bs) :: LB) m'
      /\ rw_cells asegs m' A [CB (length bs) bs] /\ addressable m' A (zlength bs)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H (zlength bs).
  Definition cmemdup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (bD : block) (D v lo B : Z) (bs : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength bs) -> 1 <= zlength bs <= 2^28 ->
      (* [comment removed for export] *)
      bytes_at asegs m D bs -> In bD LB -> blk_addr bD <= D -> D + zlength bs <= blk_addr bD + blk_size bD ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + zlength bs <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CMEMDUP_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_cmemdup (bv_unsigned ra) CH -> as_Cm H (zlength bs) <= as_AL H s ->
      accessible m D (zlength bs) ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      as_SR H (cmemdup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB bs lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cstrndup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (bs : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : as_St H),
      let k := strnlen bs in
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ ablock_range H A (Z.of_nat k + 1) /\ as_RHEAP H s' ((p, A, Z.of_nat k + 1) :: LB) m'
      /\ rw_cells asegs m' A [CB k (firstn k bs); C1 (b8 0)] /\ addressable m' A (Z.of_nat k + 1)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H (Z.of_nat k + 1).
  Definition cstrndup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (bS : block) (S v lo B : Z) (bs : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_CRYPTO_strndup) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 S -> 0 < S < 2^64 -> a1 = Z_to_bv 64 (zlength bs) -> zlength bs < 2^28 ->
      (* [comment removed for export] *)
      bytes_at asegs m S bs -> In bS LB -> blk_addr bS <= S -> S + zlength bs <= blk_addr bS + blk_size bS ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + (zlength bs + 1) <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CSTRNDUP_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_cstrndup (bv_unsigned ra) CH -> as_Cm H (zlength bs + 1) <= as_AL H s ->
      accessible m S (zlength bs) ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      as_SR H (cstrndup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB bs lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition crealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (p : bptr) (old n : Z) (obs : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A' : Z) junk (p' : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H (as_lb_remove H p LB) (bv_unsigned sp) [] m m'
      /\ ablock_range H A' n /\ as_RHEAP H s' ((p', A', n) :: as_lb_remove H p LB) m'
      /\ rw_cells asegs m' A' [CB (Z.to_nat (Z.min old n)) (firstn (Z.to_nat (Z.min old n)) obs); CB (Z.to_nat (n - Z.min old n)) junk]
      /\ addressable m' A' n
      /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H n - as_Cf H old.
  Definition crealloc_stmt_gen (entry stack : Z) (arr : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (p : bptr)
           (A old num size lo B : Z) (obs : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 num ->
      (if arr then a2 = Z_to_bv 64 size /\ 0 <= num < 2^32 /\ 0 <= size < 2^32 else size = 1) ->
      1 <= num * size <= AREALLOC_MAX -> old <= AREALLOC_MAX ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> In (p, A, old) LB -> rw_cells asegs m A [CB (Z.to_nat old) obs] -> zlength obs = old ->
      lb_bytes LB + num * size <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_crealloc (bv_unsigned ra) CH -> as_Cm H (num * size) + as_Cf H old <= as_AL H s ->
      addressable m A old ->
      IMPL_mem m -> GOT_mem m ->
      as_SR H (crealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p old (num * size) obs lo B m mo) (mkCfg msF mo).
  Definition crealloc_stmt : Prop := crealloc_stmt_gen P_CRYPTO_realloc CREALLOC_STACK false.
  Definition crealloc_array_stmt : Prop := crealloc_stmt_gen P_CRYPTO_realloc_array CREALLOC_ARRAY_STACK true.

  (* [comment removed for export] *)
  Definition C1_stmts : Prop :=
    cmalloc_stmt /\ cmalloc_array_stmt /\ cmalloc0_stmt /\ cmalloc_array0_stmt /\ czalloc_stmt /\ ccalloc_stmt
    /\ cfree_stmt /\ cfree_null_stmt /\ cmemdup_stmt /\ cstrndup_stmt /\ crealloc_stmt /\ crealloc_array_stmt.
End W.

End HCW.
