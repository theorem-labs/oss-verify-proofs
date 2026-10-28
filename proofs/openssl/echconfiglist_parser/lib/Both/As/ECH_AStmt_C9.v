(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
     ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition B64CTRL_STACK : Z := FR_b64_ctrl + BIOCTRL_STACK.                 (* [comment removed for export] *)
Definition BIOCTRL_B64_STACK : Z := FR_BIO_ctrl + B64CTRL_STACK.
Definition BIOPUSH_STACK : Z := FR_BIO_push + BIOCTRL_B64_STACK.
Definition B64READ_STACK : Z :=
  FR_b64_read + 16 + Z.max AFS_STACK (Z.max BIOREAD_STACK (Z.max DECUPDATE_STACK (Z.max DECFINAL_STACK (Z.max DECINIT_STACK AINTRIN_STACK)))).
Definition BIOREAD_B64_STACK : Z := FR_BIO_read + 16 + Z.max AFS_STACK (FR_bio_read_intern + FR_bread_conv + Z.max B64READ_STACK BIOCTRL_B64_STACK).
(* [comment removed for export] *)
Definition B64NEW_STACK : Z := FR_b64_new + Z.max CZALLOC_STACK (Z.max ENCNEW_STACK (Z.max AINTRIN_STACK BIOACC_STACK)).
Definition BIONEW_B64_STACK (x : ctxinfo) : Z := FR_BIO_new_ex + Z.max CZALLOC_STACK (Z.max (CNEWEX_STACK (CtxReady x)) B64NEW_STACK).   (* [comment removed for export] *)
Definition B64FREE_STACK : Z := FR_b64_free + Z.max BIOACC_STACK (Z.max CFREE_STACK (Z.max AINTRIN_STACK ENCFREE_STACK)).
Definition BIOFREEINT_B64_STACK : Z := FR_BIO_free_int + Z.max B64FREE_STACK (Z.max CFREEEX_STACK CFREE_STACK).
Definition BIOFREEALL_STACK : Z := FR_BIO_free_all + Z.max BIOFREEINT_B64_STACK BIOFREEINT_STACK.

(* [comment removed for export] *)
Definition R_b64_new_CRYPTO_zalloc : Z := 0x5574c0.            Definition R_b64_new_asan_memset : Z := 0x557538.
Definition R_b64_new_EVP_ENCODE_CTX_new : Z := 0x557540.      Definition R_b64_new_BIO_set_data : Z := 0x55756c.
Definition R_b64_new_BIO_set_init : Z := 0x557580.
Definition R_b64_free_BIO_get_data : Z := 0x55764c.            Definition R_b64_free_CRYPTO_free : Z := 0x55768c.        (* [comment removed for export] *)
Definition R_b64_free_asan_memset : Z := 0x51e0b8.            Definition R_b64_free_EVP_ENCODE_CTX_free : Z := 0x5576d0.
Definition R_b64_free_CRYPTO_free_2 : Z := 0x5576e8.          (* [comment removed for export] *)
Definition R_b64_free_BIO_set_data : Z := 0x5576f8.            Definition R_b64_free_BIO_set_init : Z := 0x557708.
Definition R_BIO_free_all_BIO_free_int : Z := 0x239168.
(* [comment removed for export] *)
Definition PF_b64new : list (Z * list Z) :=
  pf_shift R_b64_new_CRYPTO_zalloc PF_czalloc ++ pf_shift R_b64_new_EVP_ENCODE_CTX_new PF_encnew.
Definition PF_bionew_b64 (x : ctxinfo) : list (Z * list Z) :=
  pf_shift R_BIO_new_ex_CRYPTO_zalloc PF_czalloc ++ pf_shift R_BIO_new_ex_CRYPTO_new_ex_data (PF_ctx (CtxReady x)) ++ pf_shift R_BIO_new_ex_create PF_b64new.
Definition PF_b64free : list (Z * list Z) :=
  pf_shift R_b64_free_EVP_ENCODE_CTX_free PF_encfree ++ pf_shift R_b64_free_CRYPTO_free_2 PF_cfree.
Definition PF_biofreeint_b64 : list (Z * list Z) := pf_shift R_BIO_free_int_destroy PF_b64free ++ pf_shift R_BIO_free_int_CRYPTO_free PF_cfree.
Definition PF_biofreeall : list (Z * list Z) := pf_shift R_BIO_free_all_BIO_free_int (PF_biofreeint_b64 ++ PF_biofreeint).   (* [comment removed for export] *)


Definition B64F_below (a : Z) (R : b64frep) (lo : Z) : Prop :=
  a + BIO_SIZE <= lo /\ bf_ctx R + B64CTX_SIZE <= lo /\ bf_enc R + 92 <= lo.
(* [comment removed for export] *)
Definition B64F_shad (m : mem) (a : Z) (R : b64frep) : Prop :=
  addressable m a BIO_SIZE /\ addressable m (bf_ctx R) B64CTX_SIZE /\ addressable m (bf_enc R) 92.

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition BIONEW_B64_COST (x : ctxinfo) : Z := as_Cm H BIO_SIZE + ctxph_cost H (CtxReady x) + as_Cf H 0 + as_Cm H B64CTX_SIZE + as_Cm H ENCCTX_SIZE.
  Definition B64FREE_COST : Z := as_Cf H 0 + as_Cf H ENCCTX_SIZE + as_Cf H B64CTX_SIZE.
  Definition BIOFREEINT_B64_COST : Z := B64FREE_COST + as_Cf H 0 + as_Cf H BIO_SIZE.
  Definition BIOFREEALL_COST : Z := BIOFREEINT_B64_COST + BIOFREE_COST H.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition biopush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (a : Z) (R : b64frep) (mb : Z) (M : membio) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (a, a + BIO_SIZE); (mb, mb + BIO_SIZE)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ B64F_fresh H LB m' a (bf_with_hdr R (bf_flags R) (bf_retry R) (bf_nread R) mb (bf_prev R))
      /\ MEMBIO H LB m' mb (mb_with_hdr M (mb_flags M) (mb_numf M) (mb_next M) a).
  Definition biopush_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb lo : Z) (R : b64frep) (M : membio),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 mb ->
      B64F_fresh H LB m a R -> B64F_apart a R -> bf_next R = 0 -> B64F_below a R lo -> MEMBIO H LB m mb M -> MEMBIO_below mb M lo -> MEMBIO_sep mb M ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m ->
      B64F_shad m a R -> MEMBIO_shad m mb M -> ACONST m ->                                              (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOPUSH_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (biopush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB a R mb M lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_push) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bioread_b64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (LF : list fframe) (sA : as_St H) (a : Z) (R : b64frep) (mb : Z) (M : membio) (txt : list byte) (out outl : Z) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (R' : b64frep) (d' : list Z) (M' : membio) junk' (XS : list (Z * Z)),
      let r := b64_read_spec (map bv_unsigned txt) outl in
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (br_rv r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ Forall (fs_scratch H LF) XS                                                                     (* [comment removed for export] *)
      /\ munch ((lo, bv_unsigned sp) :: (out, out + outl) :: XS ++ B64F_foot a R ++ MEMBIO_foot mb M) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ B64F_used H LB m' a R' /\ blocks_B64F a R' = blocks_B64F a R /\ bf_next R' = mb /\ ENCCTX H LB m' (bf_enc R) d' (bf_eid R)
      /\ MEMBIO H LB m' mb M' /\ blocks_MEMBIO mb M' = blocks_MEMBIO mb M /\ mb_buf M' = mb_buf M /\ mb_len M' = mb_len M /\ mb_next M' = mb_next M
      /\ bytes_at asegs m' (mb_buf M) txt
      /\ rw_cells asegs m' out [CB (length (br_out r)) (map (Z_to_bv 8) (br_out r)); CB (Z.to_nat outl - length (br_out r)) junk']
      /\ as_RFS H LF m' /\ arelro_lib m' /\ as_RHEAP H sA LB m'.                                          (* [comment removed for export] *)
  Definition bioread_b64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (sA : as_St H) (a mb out outl lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      B64F_fresh H LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX H LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO H LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at asegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->   (* [comment removed for export] *)
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      (out + outl <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= out) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m ->
      B64F_shad m a R -> MEMBIO_shad m mb M -> PAYLOAD_shad m M -> OUT_shad m out outl -> ACONST m -> arelro_lib m ->    (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + 2 < AFS_MAXLIVE)%nat -> tp = Z_to_bv 64 ATP -> as_RHEAP H sA LB m -> bv_unsigned sp mod 16 = 0 -> (* [comment removed for export] *)
      fsobj H LF out outl -> fsobj H LF (mb_buf M) (mb_len M) ->                                                      (* [comment removed for export] *)
      afs_write_ok H LF (out, out + outl) -> aclient_write_ok H LB (out, out + outl) -> AIMG_TOP <= out ->             (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOREAD_B64_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (bioread_b64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF sA a R mb M txt out outl lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_read) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition b64ctrl_rv (cmd : Z) : Z := if cmd =? BIO_CTRL_EOF then 1 else 0.
  Definition b64ctrl_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb cmd parg lo : Z) (R : b64frep) (M : membio)
           (hdr junk : list byte) (elen cont : Z),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 cmd -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 parg -> 0 <= parg < 2^64 ->
      rw_cells asegs m a (bio_cells (b64f_bio R)) -> bf_next R = mb -> B64F_blocks H LB a R -> B64F_below a R lo ->
      rw_cells asegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen) -> length hdr = 32%nat ->
      map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [cont; cont / 256; cont / 65536; cont / 16777216] ->
      ((cmd = BIO_CTRL_PUSH /\ MEMBIO H LB m mb M /\ MEMBIO_below mb M lo /\ MEMBIO_sep mb M /\ METH_mem m /\ MEMBIO_shad m mb M
        /\ Forall (fun b => a + BIO_SIZE <= blk_addr b \/ blk_addr b + blk_size b <= a) (blocks_MEMBIO mb M))
       \/ (cmd = BIO_CTRL_EOF /\ - 2^31 <= cont <= 0)) ->
      B64F_apart a R -> B64F_shad m a R -> ACONST m ->              (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - B64CTRL_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b64ctrl_rv cmd)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom asegs)
                   /\ munch [(lo, bv_unsigned sp); (a, a + BIO_SIZE)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
                   /\ rw_cells asegs m' a (bio_cells (b64f_bio R)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_b64_ctrl) fc None m (seg_rom asegs)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bionew_b64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (a : Z) (R : b64frep) (XS : list (Z * Z)),
      let LB' := blocks_B64F a R ++ LB in
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ CTXPH LB' m' (CtxReady x)
      /\ rw_cells asegs m' a (bio_cells (b64f_bio R)) /\ bf_flags R = 0 /\ bf_retry R = 0 /\ bf_nread R = 0 /\ bf_next R = 0 /\ bf_prev R = 0
      /\ (exists junk, length junk = 2528%nat /\ rw_cells asegs m' (bf_ctx R) (b64ctx_fresh_cells (bf_enc R) junk))
      /\ B64F_blocks H LB' a R /\ B64F_apart a R /\ ENCCTX H LB' m' (bf_enc R) [] (bf_eid R) /\ 0 < a
      /\ B64F_shad m' a R                                                                          (* [comment removed for export] *)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ METH_b64 m' /\ arelro_lib m'
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'                                              (* [comment removed for export] *)
      /\ xpres H LB (bv_unsigned sp) (memflag_foot ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - BIONEW_B64_COST x.
  Definition bionew_b64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo)
           (v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_BIO_new) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 A_b64_method ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + B64F_BYTES <= as_LIVE_MAX H -> Z.of_nat (length LB) + 3 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIONEW_B64_STACK x ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> METH_b64 m -> arelro_lib m -> CTXPH LB m (CtxReady x) ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + 1 <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_bionew_b64 x) (bv_unsigned ra) CH -> BIONEW_B64_COST x <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (bionew_b64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF x lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition biofreeint_b64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo) (a : Z) (R : b64frep) (rbp shi lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBr : list block) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k)
      /\ as_AKREL H s' k /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LBr m' /\ Permutation LB (blocks_B64F a R ++ LBr)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ METH_b64 m' /\ METH_mem m' /\ arelro_lib m' /\ CTXPH LBr m' (CtxReady x)
      /\ rw_cells asegs m' rbp [C4 (wz 0)] /\ stack0 m' lo shi
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'
      /\ xpres H LBr (bv_unsigned sp) ((rbp, rbp + 4) :: mutex_foot (blk_addr (cx_exlock x)) ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - BIOFREEINT_B64_COST.
  Definition biofreeint_b64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo)
           (a rbp shi lo B : Z) (R : b64frep) (d : list Z) (errv jv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_BIO_free_int) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 rbp -> rw_cells asegs m rbp [C4 jv] -> bv_unsigned sp <= rbp -> rbp mod 4 = 0 -> rbp + 8 <= shi -> shi <= B ->
      stack0 m lo shi ->                                                                     (* [comment removed for export] *)
      B64F_used H LB m a R -> B64F_apart a R -> ENCCTX H LB m (bf_enc R) d (bf_eid R) -> B64F_shad m a R -> CTXPH LB m (CtxReady x) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOFREEINT_B64_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> METH_b64 m -> METH_mem m -> arelro_lib m ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      (forall fp' ra', In (fp', ra') CH -> rbp + 4 <= fp' - 16 \/ fp' <= rbp) ->                 (* [comment removed for export] *)
      pf_ok (as_TR H) PF_biofreeint_b64 (bv_unsigned ra) CH -> BIOFREEINT_B64_COST <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (biofreeint_b64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF x a R rbp shi lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition biofreeall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo) (a : Z) (R : b64frep) (mb : Z) (M : membio) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBr : list block) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LBr m' /\ Permutation LB (blocks_B64F a R ++ blocks_MEMBIO mb M ++ LBr)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ METH_b64 m' /\ METH_mem m' /\ arelro_lib m' /\ CTXPH LBr m' (CtxReady x)
      /\ stack0 m' lo (bv_unsigned sp)
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'
      /\ xpres H LBr (bv_unsigned sp) (mutex_foot (blk_addr (cx_exlock x)) ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - BIOFREEALL_COST.
  Definition biofreeall_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo)
           (a mb lo B : Z) (R : b64frep) (M : membio) (d : list Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> B64F_used H LB m a R -> B64F_apart a R -> bf_next R = mb -> ENCCTX H LB m (bf_enc R) d (bf_eid R) ->
      MEMBIO H LB m mb M -> mb_next M = 0 -> MEMBIO_apart mb M -> CTXPH LB m (CtxReady x) ->
      List.NoDup (map blk_id (blocks_B64F a R ++ blocks_MEMBIO mb M)) ->
      B64F_shad m a R -> MEMBIO_shad m mb M -> stack0 m lo (bv_unsigned sp) ->                                     (* [comment removed for export] *)
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOFREEALL_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> METH_b64 m -> METH_mem m -> arelro_lib m ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) PF_biofreeall (bv_unsigned ra) CH -> BIOFREEALL_COST <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (biofreeall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF x a R mb M lo B m mo) (mkCfg msF mo).

  Definition C9_stmts : Prop := bionew_b64_stmt /\ biopush_stmt /\ bioread_b64_stmt /\ biofreeall_stmt /\ b64ctrl_stmt.
End W.
End HCW.
