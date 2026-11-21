(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_defl_iface Z_trees_iface Z_defl_model Z_defl_path Zg_defl_path Zg_defl_path2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Export Zg_defl_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz DeflateBlk Deflate DeflateSafe Trees FillWinModel RefDeflFast6 RefDeflSlow6 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition Z_DEFLATE_FAST : Z := 0x18f8c.

Definition Z_FAST_STACK : Z := 128 + 512.

Definition deflate_fast_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (d : deflate_state) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (bs_code (snd (deflate_fast d flush)))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Aw L, dl_Aw L + DS_WIN);
              (dl_Ap L, dl_Ap L + 2 * DS_NPREV); (dl_Ah L, dl_Ah L + 2 * DS_NHEAD); (dl_Ab L, dl_Ab L + DS_PEND);
              (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DREP m' L (fst (deflate_fast d flush)) /\ din m' L inp /\ dout m' L rest0 (ds_strm (fst (deflate_fast d flush))).

Definition deflate_fast_stmtg : Prop :=
  forall (L : dlay) (d : deflate_state) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> din m L inp -> din_tie inp d -> dout m L rest0 (ds_strm d) -> mem_inv psegs m -> relro_clean m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_FAST_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo ->
  fast_safe d flush -> 0 <= flush <= 5 ->
  ds_w_size d = 32768 -> ds_hash_size d = 32768 -> ds_lit_bufsize d = 16384 -> ds_wrap d <> 2 -> ds_wrap d <> 0 -> - 2 <= ds_wrap d <= 2 ->
  cs_avail_in (ds_strm d) < 2^31 -> 0 <= cs_avail_out (ds_strm d) < 2^31 ->
  (length (cs_out_rev (ds_strm (fst (deflate_fast d flush)))) <= length rest0)%nat ->
  a0 = wz (dl_As L) -> a1 = wz flush ->
  evt psegs (deflate_fast_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L d flush inp rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE_FAST) fc None m (seg_rom psegs)).

Definition deflate_in_stmtg2 : Prop :=
  forall (L : dlay) (d : deflate_state) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> din m L inp -> dout m L rest0 (ds_strm d) -> mem_inv psegs m -> relro_clean m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_DEFLATE_IN_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) -> dio_sep L (zlength inp) (Z.of_nat (length rest0)) lo ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK) ->
  defl_pathg2 inp flush (deflate_core d flush) d ->
  (length (cs_out_rev (ds_strm (fst (deflate_core d flush)))) <= length rest0)%nat ->
  a0 = wz (dl_S L) -> a1 = wz flush ->
  evt psegs (deflate_in_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L (fst (deflate_core d flush)) (snd (deflate_core d flush)) inp rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATE_PC) fc None m (seg_rom psegs)).

