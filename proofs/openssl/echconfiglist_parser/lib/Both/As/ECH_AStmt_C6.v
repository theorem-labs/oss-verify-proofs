(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition BUFNEW_STACK : Z := FR_BUF_MEM_new + CZALLOC_STACK.
Definition BUFFREE_STACK : Z := FR_BUF_MEM_free + CFREE_STACK.   (* [comment removed for export] *)
Definition BIOACC_STACK : Z := FR_BIO_set_data.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bio_with_ptr (B : biorep) (p : Z) : biorep :=
  mkBIO (bio_method B) (bio_init B) (bio_shutdown B) (bio_flags B) (bio_retry B) (bio_numf B) p (bio_next B) (bio_prev B) (bio_refs B) (bio_nread B) (bio_nwrite B).
Definition bio_with_init (B : biorep) (i : Z) : biorep :=
  mkBIO (bio_method B) i (bio_shutdown B) (bio_flags B) (bio_retry B) (bio_numf B) (bio_ptr B) (bio_next B) (bio_prev B) (bio_refs B) (bio_nread B) (bio_nwrite B).
Definition bio_with_flags (B : biorep) (f : Z) : biorep :=
  mkBIO (bio_method B) (bio_init B) (bio_shutdown B) f (bio_retry B) (bio_numf B) (bio_ptr B) (bio_next B) (bio_prev B) (bio_refs B) (bio_nread B) (bio_nwrite B).
Definition bio_ok (B : biorep) : Prop :=
     0 <= bio_method B < 2^64 /\ 0 <= bio_init B < 2^32 /\ 0 <= bio_shutdown B < 2^32 /\ 0 <= bio_flags B < 2^31
  /\ 0 <= bio_retry B < 2^32 /\ 0 <= bio_numf B < 2^32 /\ 0 <= bio_ptr B < 2^64 /\ 0 <= bio_next B < 2^64
  /\ 0 <= bio_prev B < 2^64 /\ 0 <= bio_refs B < 2^32 /\ 0 <= bio_nread B < 2^64 /\ 0 <= bio_nwrite B < 2^64.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition R_BUF_MEM_new_CRYPTO_zalloc : Z := 0x24b964.   (* [comment removed for export] *)
Definition PF_bufnew : list (Z * list Z) := pf_shift R_BUF_MEM_new_CRYPTO_zalloc PF_czalloc.
Definition PF_buffree : list (Z * list Z) := PF_cfree.    (* [comment removed for export] *)

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition BIO_ranges (a : Z) : Prop := ablock_range H a BIO_SIZE.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bufnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ ablock_range H A BUFMEM_SIZE /\ as_RHEAP H s' ((p, A, BUFMEM_SIZE) :: LB) m'
      /\ rw_cells asegs m' A (buf_cells (mkBUF 0 0 0 0)) /\ addressable m' A BUFMEM_SIZE
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H BUFMEM_SIZE.
  Definition bufnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_BUF_MEM_new) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 0 ->                 (* [comment removed for export] *)
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + BUFMEM_SIZE <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BUFNEW_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_bufnew (bv_unsigned ra) CH ->
      as_Cm H BUFMEM_SIZE <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      as_SR H (bufnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition buffree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ xpres H (as_lb_remove H p LB) (bv_unsigned sp) [] m m'
      /\ as_RHEAP H s' (as_lb_remove H p LB) m' /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cf H BUFMEM_SIZE.
  Definition buffree_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (p : bptr) (A len mx fl lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_BUF_MEM_free) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 A -> In (p, A, BUFMEM_SIZE) LB -> rw_cells asegs m A (buf_cells (mkBUF len 0 mx fl)) -> addressable m A BUFMEM_SIZE ->
      0 <= len < 2^64 -> 0 <= mx < 2^64 -> 0 <= fl < 2^64 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BUFFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_buffree (bv_unsigned ra) CH ->
      as_Cf H BUFMEM_SIZE <= as_AL H s ->
      IMPL_mem m -> GOT_mem m ->
      as_SR H (buffree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bioacc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : word) (a : Z) (B' : biorep) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (a, a + BIO_SIZE)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' a (bio_cells B').
  (* [comment removed for export] *)
  Definition bioacc_stmt_at (entry : Z) (rv : Z -> biorep -> Z -> word) (upd : biorep -> Z -> biorep) (xmax : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a x lo : Z) (B : biorep),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 x -> 0 <= x < xmax -> rw_cells asegs m a (bio_cells B) -> bio_ok B -> a + BIO_SIZE <= lo ->
      addressable m a BIO_SIZE -> BIO_ranges a -> ACONST m ->     (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOACC_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (bioacc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (rv a B x) a (upd B x) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition biosetdata_stmt : Prop := bioacc_stmt_at P_BIO_set_data (fun a _ _ => Z_to_bv 64 (a + O_BIO_PTR)) bio_with_ptr (2^64).
  Definition biogetdata_stmt : Prop := bioacc_stmt_at P_BIO_get_data (fun _ B _ => Z_to_bv 64 (bio_ptr B)) (fun B _ => B) (2^64).
  Definition biosetinit_stmt : Prop := bioacc_stmt_at P_BIO_set_init (fun a _ _ => Z_to_bv 64 (a + O_BIO_INIT)) bio_with_init (2^31).
  Definition bioclearflags_stmt : Prop :=
    bioacc_stmt_at P_BIO_clear_flags (fun a _ _ => Z_to_bv 64 (a + O_BIO_FLAGS)) (fun B x => bio_with_flags B (Z.land (bio_flags B) (Z.lnot x))) (2^31).
  Definition biotestflags_stmt : Prop :=
    bioacc_stmt_at P_BIO_test_flags (fun _ B x => Z_to_bv 64 (Z.land (bio_flags B) x)) (fun B _ => B) (2^31).
  Definition biosetflags_stmt : Prop :=
    bioacc_stmt_at P_BIO_set_flags (fun a _ _ => Z_to_bv 64 (a + O_BIO_FLAGS)) (fun B x => bio_with_flags B (Z.lor (bio_flags B) x)) (2^31).
  (* [comment removed for export] *)
  Definition bionext_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a x lo : Z) (B : biorep),
      a0 = Z_to_bv 64 a -> 0 < a -> rw_cells asegs m a (bio_cells B) -> bio_ok B -> a + BIO_SIZE <= lo ->
      addressable m a BIO_SIZE -> BIO_ranges a -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOACC_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (bioacc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (bio_next B)) a B lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_next) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition biofb64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOACC_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_b64_method) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m' (seg_rom asegs)
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_f_base64) fc None m (seg_rom asegs)).

  Definition C6_stmts : Prop :=
    bufnew_stmt /\ buffree_stmt /\ biosetdata_stmt /\ biogetdata_stmt /\ biosetinit_stmt
    /\ bioclearflags_stmt /\ biotestflags_stmt /\ biosetflags_stmt /\ bionext_stmt /\ biofb64_stmt.
End W.
End HCW.
