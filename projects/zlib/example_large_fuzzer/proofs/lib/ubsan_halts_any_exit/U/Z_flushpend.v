(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface F_memcpy Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz SendModel FillWinModel RefDeflFast1 RefDeflFastM DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition Z_FLUSH_PENDING : Z := 0x18538.
Lemma tr_flush_bits_strm : forall s, ds_strm (tr_flush_bits s) = ds_strm s.
Proof. intros s. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity. Qed.
Definition flush_pending_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (d : deflate_state) (rest0 : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND);
              (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DREP m' L (flush_pending d) /\ dout m' L rest0 (ds_strm (flush_pending d)).
Ltac fp_close_tac ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY OUT ES Ek :=
  rewrite ES; split; [split|];
  [ eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
    rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS
  | constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY]
  | dsred; exact OUT ].
Section FP.
Hypothesis HTFB : tr_flush_bits_stmt.
Lemma flush_pending_spec : forall (L : dlay) (d : deflate_state) (rest0 : list byte) (nin lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L d -> dout m L rest0 (ds_strm d) -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> dlay_below L lo (bv_unsigned sp) ->
  dio_sep L nin (Z.of_nat (length rest0)) lo ->
  fp_ok d -> ds_lit_bufsize d * 4 = 65536 -> 0 <= cs_avail_out (ds_strm d) < 2^31 ->
  (length (cs_out_rev (ds_strm (flush_pending d))) <= length rest0)%nat ->
  a0 = wz (dl_S L) ->
  evt usegs (flush_pending_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L d rest0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_FLUSH_PENDING) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros [ZS ST] OUT MI STK LO BEL IO FPOK PBL RAO ROOM ->. unfold Z_FLUSH_PENDING.
  destruct FPOK as [BI FPK]. rewrite PBL in BI, FPK. cbv zeta in FPK.
  pose proof (tr_flush_bits_strm d) as ES.
  pose proof (flush_pending_eq d) as EF. cbv zeta in EF. rewrite EF in ROOM.
  remember (tr_flush_bits d) as d1 eqn:Ed1.
  destruct FPK as (RP & RPB & RPO0 & RPO1 & RTO).
  assert (EL : fp_len d1 = if cs_avail_out (ds_strm d) <? ds_pending d1 then cs_avail_out (ds_strm d) else ds_pending d1).
  { unfold fp_len. rewrite ES, wrap32_id by lia. reflexivity. }
  remember (fp_len d1) as flen eqn:Eflen. clear Eflen.
  open_zs ZS. unfold dout in OUT.
  assert (OL0 : (length (cs_out_rev (ds_strm d)) <= length rest0)%nat).
  { destruct (flen =? 0); [rewrite ES in ROOM; exact ROOM|].
    unfold fp_tail in ROOM. cbv zeta in ROOM. rewrite ES in ROOM.
    destruct (ds_pending d1 - flen =? 0); dsred in ROOM; unfold cs_emit in ROOM; dsred in ROOM;
      rewrite rev_append_rev, length_app, length_rev in ROOM; lia. }
  pose proof (outv_length rest0 (ds_strm d) OL0) as OL.
  pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. below_open BEL. io_open IO.
  pose proof (lo_S _ LAY) as BKS. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND);
              (dl_NO L, dl_NO L + Z.of_nat (length rest0))] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf.
  carve_frame 32%nat STK.
  do 5 zstep.
  gF. zstep. zstep. al8 (dl_S L). gF.
  zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ST0 : DST mm L d) by
      (apply (DST_agree m mm); [exact ST| eapply ag_blocks_munch; [exact LAY| exact MUf| exact WM| | | | |]; cbn [disjoint_from]; slia]) end.
  clear MUf.
  call (HTFB L d).
  1:{ exact ST0. } 1:{ exact MI. } 1:{ exact BI. } 1:{ rewrite <- Ed1. exact RPB. } 1:{ reflexivity. }
  clear ST0 ST. rewrite <- Ed1 in POST.
  open_DST POST. open_A GA.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] mm) as MUf;
    pose proof (wmono_refl usegs mm) as WMf end.
  gF. zstep. al8 (dl_As L). gF.
  zs. zs. zstep.
  assert (FL : 0 <= flen /\ flen <= cs_avail_out (ds_strm d) /\ flen <= ds_pending d1) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm d)) (ds_pending d1)); lia).
  eapply (evt_cut usegs (fun ms' => ms' = _)).
  { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (cs_avail_out (ds_strm d) <? ds_pending d1) with false in EL by (symmetry; apply Z.ltb_ge; lia).
      replace (wz (ds_pending d1)) with (wz flen) by (f_equal; lia). apply evt_done. reflexivity.
    - zstep.
      replace (wz (cs_avail_out (ds_strm d))) with (wz flen)
        by (f_equal; destruct (Z.ltb_spec (cs_avail_out (ds_strm d)) (ds_pending d1)); lia).
      apply evt_done. reflexivity. }
  intros ms' ->. clear EL.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  -
    do 5 zstep.
    release_frame FR STK (bv_unsigned sp). zstep.
    apply evt_done. unfold flush_pending_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EF. replace (flen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    split; [split|].
    + rewrite ES. exists zp1, zp2, zp3, zresv. exact ZS.
    + constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    + rewrite ES. exact OUT.
  -
    do 3 zstep. rewrite ?Z.mod_small by lia.
    remember (length (cs_out_rev (ds_strm d))) as k eqn:Ek.
    assert (KL : (k + Z.to_nat flen <= length rest0)%nat).
    { replace (flen =? 0) with false in ROOM by (symmetry; apply Z.eqb_neq; lia).
      unfold fp_tail in ROOM. cbv zeta in ROOM. rewrite ES in ROOM.
      destruct (ds_pending d1 - flen =? 0); dsred in ROOM; rewrite cs_emit_out_len, arr_slice_length', <- Ek in ROOM; lia. }
    pose proof (u8arr_sub_bytes _ (dl_Ab L) _ (Z.to_nat (ds_pending_out d1)) (Z.to_nat flen) Gpend ltac:(rewrite av8_length; lia)) as SRC.
    rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
    assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) = Z.to_nat flen)
      by (rewrite length_map; apply arr_slice_length').
    destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat flen) OUT ltac:(rewrite OL; lia)) as (O1 & O2 & O3). clear OUT.
    remember (firstn k (outv rest0 (ds_strm d))) as o1 eqn:Eo1.
    assert (LO1 : Z.of_nat (length o1) = Z.of_nat k) by (rewrite Eo1, length_firstn, OL; lia).
    remember (skipn (k + Z.to_nat flen) (outv rest0 (ds_strm d))) as o3 eqn:Eo3.
    assert (LO3 : Z.of_nat (length o3) = Z.of_nat (length rest0) - Z.of_nat k - flen) by (rewrite Eo3, length_skipn, OL; lia).
    zstep.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Ab L + ds_pending_out d1) flen);
                        [exact SRC| exact LSRC| exact O2| zsep| eassumption| lia| lia| lia]
                      | clear O2 SRC; post_call segs mm ] end.
    assert (LO1n : length o1 = k) by lia.
    pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat flen) LO1n O1 PC O3) as OUT. subst o1 o3.
    fold (zb8 (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) in OUT.
    rewrite <- (arr_slice_length' (ds_pending_buf d1) (ds_pending_out d1) flen) in OUT. rewrite Ek in OUT.
    rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
    assert (OL' : length (outv rest0 (cs_emit (ds_strm d) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen))) = length rest0).
    { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
    assert (OLz : Z.of_nat (length (outv rest0 (cs_emit (ds_strm d) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)))) = Z.of_nat (length rest0)) by (rewrite OL'; reflexivity).
    clear O1 O3 PC POST LSRC LO1 LO3 LO1n.
    zs. zstep. gF. gF. gF.
    zs. zstep. zs. gF. gF. gF.
    zs. zs. zs. zstep. zs. zs. zs. zstep. zs. zs.
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    +
      do 5 zstep.
      release_frame FR STK (bv_unsigned sp). zstep.
      apply evt_done. unfold flush_pending_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
      rewrite EF. replace (flen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold fp_tail. cbv zeta. replace (ds_pending d1 - flen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      tr_groups MUf WMf.
      fp_close_tac ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY OUT ES Ek.
    +
      do 2 zs. do 5 zstep.
      release_frame FR STK (bv_unsigned sp). zstep.
      apply evt_done. unfold flush_pending_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
      rewrite EF. replace (flen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold fp_tail. cbv zeta. replace (ds_pending d1 - flen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      tr_groups MUf WMf.
      fp_close_tac ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY OUT ES Ek.
Qed.
End FP.
