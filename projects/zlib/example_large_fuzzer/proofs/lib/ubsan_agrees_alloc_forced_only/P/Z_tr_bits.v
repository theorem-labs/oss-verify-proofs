(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tr_flush_bits_spec : tr_flush_bits_stmt.
Proof.
  unfold tr_flush_bits_stmt. intros until m. intros ST MI BI ROOM ->. unfold Z_TR_FLUSH_BITS.
  destruct BI as (RBV & RBB & RPD). unfold tr_flush_bits in ROOM.
  pose proof (munch_refl [(dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MUf.
  open_DST ST. lay_open LAY. pose proof (ln_pend _ LENS) as LNP.
  open_D GD.
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
      do 2 zstep. rd_c2 GD 55%nat 0. zstep. do 3 zstep.
      pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (ds_bi_buf s)) ltac:(apply b0_val_w; lia).
      rd_c2 GD 55%nat 1. zstep. zs. rewrite (bv8_small (Z.shiftr (ds_bi_buf s) 8)) by (apply shr8_small; lia).
      do 4 zstep.
      apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      unfold tr_flush_bits. rewrite bi_flush_eq8 by lia. tr_groups MUf WM.
      constructor; [eexists _, _, _, _, _; unfold dsA_cells, upd4; dsred; close_cells GA| exact GB| exact GC
                   | eexists _, _, _, _, _; unfold dsD_cells, upd4; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend, upd4; dsred; exact Gpend| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
  -
    rewrite bi_flush_eq16, upd4_pending in ROOM by lia.
    open_A GA. open_pend Gpend.
    do 3 zstep. rd_c2 GD 55%nat 0. zstep. do 3 zstep.
    pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255)) ltac:(apply b0_val_land; lia).
    do 2 zstep. rd_c2 GD 55%nat 1. zstep. do 3 zstep.
    pb_store Gpend (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255))) 65536 (dl_Ab L) (ds_pending s + 1)
             (wrap8 (Z.shiftr (wrap16 (ds_bi_buf s)) 8)) ltac:(apply b1_val; lia).
    do 4 zstep.
    apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    unfold tr_flush_bits. rewrite bi_flush_eq16 by lia. tr_groups MUf WM.
    constructor; [eexists _, _, _, _, _; unfold dsA_cells, upd4; dsred; close_cells GA| exact GB| exact GC
                 | eexists _, _, _, _, _; unfold dsD_cells, upd4; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| unfold dpend, upd4; dsred; exact Gpend| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
Qed.
