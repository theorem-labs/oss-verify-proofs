(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition Z_BI_FLUSH : Z := 0x1c0b8.
Lemma bi_flush_spec : forall (L : dlay) (s : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv usegs m ->
  BINV DS_PEND s -> ds_pending (tr_flush_bits s) <= DS_PEND ->
  a0 = wz (dl_As L) ->
  evt usegs (tr_flush_bits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_BI_FLUSH) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST MI BI ROOM ->. unfold Z_BI_FLUSH.
  destruct BI as (RBV & RBB & RPD). unfold tr_flush_bits in ROOM.
  pose proof (munch_refl [(dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MUf.
  open_DST ST. lay_open LAY. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  open_D GD.
  gF. zs2. al8 (dl_As L). gF.
  do 3 zstep. zs. do 2 zstep.
  if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    do 2 zstep.
    if_cases K2; zify_cond K2; rewrite ?signed_wz in K2 by lia.
    +
      zstep. apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      unfold tr_flush_bits. rewrite bi_flush_eq0 by lia. rewrite upd4_self.
      constructor; [exact GA| exact GB| exact GC| exists hD0, hD1, hD2, hD3, hD4; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    +
      rewrite bi_flush_eq8, upd4_pending in ROOM by lia.
      open_A GA. open_pend Gpend.
      zstep. zstep. zstep. rewrite zx16_small by lia. zs2. zs2. zstep.
      gF. zs2. zs2. zs2. gX. gF.
      pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (ds_bi_buf s)) ltac:(apply b0h_w; lia).
      zs2. rd_c2 GD 55%nat 1. zstep. zs. rewrite (bv8_small (Z.shiftr (ds_bi_buf s) 8)) by (apply shr8_small; lia).
      zs2. gF. zstep. zstep.
      apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      unfold tr_flush_bits. rewrite bi_flush_eq8 by lia. tr_groups MUf WM.
      constructor; [eexists _, _, _, _, _; unfold dsA_cells, upd4; dsred; close_cells GA| exact GB| exact GC
                   | eexists _, _, _, _, _; unfold dsD_cells, upd4; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend, upd4; dsred; exact Gpend| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
  -
    rewrite bi_flush_eq16, upd4_pending in ROOM by lia.
    open_A GA. open_pend Gpend.
    zstep. zstep. zstep. rewrite zx16_small by lia. zs2. zs2. zstep.
    gF. zs2. zs2. zs2. gX. gF.
    pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255)) ltac:(apply b0h_land; lia).
    zstep. zstep. rd_c2 GD 55%nat 1. zstep. zs2.
    zs2. zstep.
    gF. zs2. zs2. zs2. gX. gF.
    zs2.
    pb_store Gpend (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255))) 65536 (dl_Ab L) (ds_pending s + 1)
             (wrap8 (Z.shiftr (wrap16 (ds_bi_buf s)) 8)) ltac:(apply b1_val; lia).
    zstep. zstep. zstep. zstep.
    apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    unfold tr_flush_bits. rewrite bi_flush_eq16 by lia. tr_groups MUf WM.
    constructor; [eexists _, _, _, _, _; unfold dsA_cells, upd4; dsred; close_cells GA| exact GB| exact GC
                 | eexists _, _, _, _, _; unfold dsD_cells, upd4; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| unfold dpend, upd4; dsred; exact Gpend| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
Qed.
Lemma tr_flush_bits_spec : tr_flush_bits_stmt.
Proof.
  unfold tr_flush_bits_stmt. intros until m. intros ST MI BI ROOM Ea0. unfold Z_TR_FLUSH_BITS.
  zstep. apply (bi_flush_spec L s); assumption.
Qed.
