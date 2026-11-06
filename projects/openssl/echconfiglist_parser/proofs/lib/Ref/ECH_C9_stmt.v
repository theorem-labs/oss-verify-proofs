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
     ECH_B64 ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition B64NEW_STACK : Z := FR_b64_new + Z.max CZALLOC_STACK ENCNEW_STACK.
Definition BIONEW_B64_STACK : Z := FR_BIO_new + FR_BIO_new_ex + Z.max CZALLOC_STACK (Z.max CNEWEX_READY_STACK B64NEW_STACK).
Definition B64CTRL_STACK : Z := FR_b64_ctrl + BIOCTRL_STACK.                 (* [comment removed for export] *)
Definition BIOCTRL_B64_STACK : Z := FR_BIO_ctrl + B64CTRL_STACK.
Definition BIOPUSH_STACK : Z := FR_BIO_push + BIOCTRL_B64_STACK.
Definition B64READ_STACK : Z := FR_b64_read + Z.max BIOREAD_STACK (Z.max DECUPDATE_STACK DECFINAL_STACK).
Definition BIOREAD_B64_STACK : Z := FR_BIO_read + FR_bio_read_intern + FR_bread_conv + Z.max B64READ_STACK BIOCTRL_B64_STACK.
Definition B64FREE_STACK : Z := FR_b64_free + Z.max ENCFREE_STACK CFREE_STACK.
Definition BIOFREE_B64_STACK : Z := FR_BIO_free + FR_BIO_free_int + Z.max B64FREE_STACK (Z.max CFREEEX_STACK CFREE_STACK).
Definition BIOFREEALL_STACK : Z := FR_BIO_free_all + Z.max BIOFREE_B64_STACK BIOFREE_STACK.

Definition B64F_below (a : Z) (R : b64frep) (lo : Z) : Prop :=
  a + BIO_SIZE <= lo /\ bf_ctx R + B64CTX_SIZE <= lo /\ bf_enc R + 92 <= lo.

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bionew_b64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (x : ctxinfo) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (a : Z) (R : b64frep),
      let LB' := blocks_B64F a R ++ LB in
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' LB' m' /\ CTXPH LB' m' (CtxReady x)
      /\ rw_cells rsegs m' a (bio_cells (b64f_bio R)) /\ bf_flags R = 0 /\ bf_retry R = 0 /\ bf_nread R = 0 /\ bf_next R = 0 /\ bf_prev R = 0
      /\ (exists junk, length junk = 2528%nat /\ rw_cells rsegs m' (bf_ctx R) (b64ctx_fresh_cells (bf_enc R) junk))
      /\ B64F_blocks LB' a R /\ B64F_apart a R /\ ENCCTX LB' m' (bf_enc R) [] (bf_eid R) /\ 0 < a   (* [comment removed for export] *)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ METH_b64 m' /\ relro_lib m'
      /\ xpres LB (bv_unsigned sp) memflag_foot m m'.
  Definition bionew_b64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (x : ctxinfo) (v lo B : Z) (errv : word),
      a0 = Z_to_bv 64 A_b64_method ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + B64F_BYTES <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 3 <= hs_LIVE_CNT_MAX H -> lb_big LB + 1 <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIONEW_B64_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> METH_b64 m -> relro_lib m -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (bionew_b64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB x lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_new) fc None m (seg_rom rsegs)) mo).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition biopush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (a : Z) (R : b64frep) (mb : Z) (M : membio) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (a, a + BIO_SIZE); (mb, mb + BIO_SIZE)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ B64F_fresh LB m' a (bf_with_hdr R (bf_flags R) (bf_retry R) (bf_nread R) mb (bf_prev R))
      /\ MEMBIO LB m' mb (mb_with_hdr M (mb_flags M) (mb_numf M) (mb_next M) a).
  Definition biopush_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb lo : Z) (R : b64frep) (M : membio),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 mb ->
      B64F_fresh LB m a R -> B64F_apart a R -> bf_next R = 0 -> B64F_below a R lo -> MEMBIO LB m mb M -> MEMBIO_below mb M lo -> MEMBIO_sep mb M ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOPUSH_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (biopush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB a R mb M lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_push) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bioread_b64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (a : Z) (R : b64frep) (mb : Z) (M : membio) (txt : list byte) (out outl : Z) (lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (R' : b64frep) (d' : list Z) (M' : membio) junk',
      let r := b64_read_spec (map bv_unsigned txt) outl in
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (br_rv r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch ((lo, bv_unsigned sp) :: (out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ B64F_used LB m' a R' /\ blocks_B64F a R' = blocks_B64F a R /\ bf_next R' = mb /\ ENCCTX LB m' (bf_enc R) d' (bf_eid R)
      /\ MEMBIO LB m' mb M' /\ blocks_MEMBIO mb M' = blocks_MEMBIO mb M /\ mb_buf M' = mb_buf M /\ mb_len M' = mb_len M /\ mb_next M' = mb_next M   (* [comment removed for export] *)
      /\ bytes_at rsegs m' (mb_buf M) txt
      /\ rw_cells rsegs m' out [CB (length (br_out r)) (map (Z_to_bv 8) (br_out r)); CB (Z.to_nat outl - length (br_out r)) junk'].
  Definition bioread_b64_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb out outl lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      B64F_fresh LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at rsegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->   (* [comment removed for export] *)
      rw_cells rsegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      (out + outl <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= out) ->       (* [comment removed for export] *)
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m -> B64TAB m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOREAD_B64_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (bioread_b64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB a R mb M txt out outl lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_read) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition biofreeall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (a : Z) (R : b64frep) (mb : Z) (M : membio) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBr : list block),
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' LBr m' /\ Permutation LB (blocks_B64F a R ++ blocks_MEMBIO mb M ++ LBr)
      /\ IMPL_mem m' /\ GOT_mem m' /\ METH_b64 m' /\ METH_mem m'
      /\ xpres LBr (bv_unsigned sp) [] m m'.
  Definition biofreeall_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (x : ctxinfo)
           (a mb lo B : Z) (R : b64frep) (M : membio) (d : list Z) (errv : word),
      a0 = Z_to_bv 64 a -> B64F_used LB m a R -> bf_next R = mb -> ENCCTX LB m (bf_enc R) d (bf_eid R) ->
      MEMBIO LB m mb M -> mb_next M = 0 -> CTXPH LB m (CtxReady x) ->
      List.NoDup (map blk_id (blocks_B64F a R ++ blocks_MEMBIO mb M)) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOFREEALL_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      IMPL_mem m -> GOT_mem m -> METH_b64 m -> METH_mem m -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (biofreeall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a R mb M lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition b64ctrl_rv (cmd : Z) : Z := if cmd =? BIO_CTRL_EOF then 1 else 0.
  Definition b64ctrl_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb cmd parg lo : Z) (R : b64frep) (M : membio)
           (hdr junk : list byte) (elen cont : Z),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 cmd -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 parg -> 0 <= parg < 2^64 ->
      rw_cells rsegs m a (bio_cells (b64f_bio R)) -> bf_next R = mb -> B64F_blocks LB a R -> B64F_below a R lo ->
      rw_cells rsegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen) -> length hdr = 32%nat ->
      map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [cont; cont / 256; cont / 65536; cont / 16777216] ->
      ((cmd = BIO_CTRL_PUSH /\ MEMBIO LB m mb M /\ MEMBIO_below mb M lo /\ MEMBIO_sep mb M /\ METH_mem m) \/ (cmd = BIO_CTRL_EOF /\ - 2^31 <= cont <= 0)) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - B64CTRL_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b64ctrl_rv cmd)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom rsegs)
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_b64_ctrl) fc None m (seg_rom rsegs)).
  (* [comment removed for export] *)

  Definition C9_stmts : Prop := bionew_b64_stmt /\ biopush_stmt /\ bioread_b64_stmt /\ biofreeall_stmt /\ b64ctrl_stmt.
End W.
End HCW.
