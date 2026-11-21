(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.

Module Z_tr_stored.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition tsb_head_post (L : dlay) (s : deflate_state) (last len : Z)
    (ra sp gp tp t0 t1 t2 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a3 a4 a5 a6 a7 wbb wbv m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz len) (wz (dl_As L)) (wz 65535) a1 (wz (dl_As L + 5936)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1ac58) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + DS_PEND)] m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ EM m' L s (tsb_hA s last) (tsb_hP s) wbb wbv.

Lemma tsb_head : forall (L : dlay) (s : deflate_state) (last len : Z) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem),
  EM m L s (ds_pending_buf s) (ds_pending s) (wz (ds_bi_buf s)) (wz (ds_bi_valid s)) ->
  dlay_ok L -> BINV 65536 s -> tsb_hP s <= 65536 -> 0 <= last <= 1 ->
  munch [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + DS_PEND)] m0 m -> wmono psegs m0 m -> mem_inv psegs m ->
  a0 = wz (dl_As L) -> a2 = wz len -> a3 = wz last ->
  evt psegs (tsb_head_post L s last len ra sp gp tp t0 t1 t2 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1ab50) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH LAY (RBV & RBB & RPD) ROOM RL MU WM MI -> -> ->.
  lay_open LAY. open_EM EMH.
  do 5 zstep. zs. do 3 zstep.
  zstep. br_cases K.
  -
    zs. zs. zs.
    match goal with |- context [wz (Z.lor ?a ?b)] => remember (wz (Z.lor a b)) as w eqn:Ew end.
    assert (LO : bv_unsigned w mod 2^16 = sb_nb s last mod 2^16) by (rewrite Ew, sb_nb_canon by lia; apply or_lh_sllw; lia).
    clear Ew.
    zstep. zs. zstep. zstep. zstep. (* 1.4: + sw a4, 4(a2) = bi_valid *)
    br_cases K2.
    +
      assert (RM : ds_pending s + 1 <= 65536).
      { unfold tsb_hP in ROOM. rewrite (proj2 (Z.leb_le _ _)) in ROOM by lia. lia. }
      zstep. br_false.
      do 5 zstep.
      pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (sb_nb s last)) ltac:(apply lo8_wrap8; exact LO).
      zstep.
      apply evt_done. unfold tsb_head_post. do 8 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      unfold tsb_hA, tsb_hP. rewrite (proj2 (Z.leb_le _ _)) by lia. cbv zeta.
      close_EM GA GD Gpend.
    +
      assert (RM : ds_pending s + 2 <= 65536).
      { unfold tsb_hP in ROOM. rewrite (proj2 (Z.leb_gt _ _)), (proj2 (Z.leb_le _ _)) in ROOM by lia. lia. }
      do 5 zstep.
      pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (Z.land (sb_nb s last) 255)) ltac:(apply lo8_wrap8_land; exact LO).
      do 2 zstep. rd_c2 GD 55%nat 1. zstep. do 3 zstep.
      pb_store Gpend (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (sb_nb s last) 255))) 65536 (dl_Ab L) (ds_pending s + 1)
               (wrap8 (Z.shiftr (wrap16 (sb_nb s last)) 8)) ltac:(apply hi8_lo16; exact LO).
      apply evt_done. unfold tsb_head_post. do 8 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      unfold tsb_hA, tsb_hP. rewrite (proj2 (Z.leb_gt _ _)), (proj2 (Z.leb_le _ _)) by lia. cbv zeta.
      close_EM GA GD Gpend.
  -
    assert (RM : ds_pending s + 3 <= 65536).
    { unfold tsb_hP in ROOM. rewrite !(proj2 (Z.leb_gt _ _)) in ROOM by lia. lia. }
    zs. do 2 zstep. zs. zs.
    match goal with |- context [wz (Z.lor ?a ?b)] => remember (wz (Z.lor a b)) as w eqn:Ew end.
    assert (LO : bv_unsigned w mod 2^16 = sb_nb s last mod 2^16) by (rewrite Ew, sb_nb_canon by lia; apply or_lh_sllw; lia).
    clear Ew.
    do 4 zstep.
    pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (Z.land (sb_nb s last) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    do 2 zstep. rd_c2 GD 55%nat 1. zstep. do 3 zstep.
    pb_store Gpend (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (sb_nb s last) 255))) 65536 (dl_Ab L) (ds_pending s + 1)
             (wrap8 (Z.shiftr (wrap16 (sb_nb s last)) 8)) ltac:(apply hi8_lo16; exact LO).
    zs. zs. zs. zs. zs. rewrite srlw_val by lia.
    pose proof (shiftr_wrap16_range last (16 - ds_bi_valid s) ltac:(lia)) as RSH.
    zstep. zs. zstep. zstep. zstep. (* 1.4: + sw a4, 4(a2) = bi_valid *)
    br_false.
    zstep. br_false.
    do 5 zstep.
    pb_store Gpend (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (sb_nb s last) 255))) (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (sb_nb s last)) 8)))
             65536 (dl_Ab L) (ds_pending s + 1 + 1) (wrap8 (Z.shiftr (wrap16 last) (16 - ds_bi_valid s))) ltac:(apply lo8_wz_wrap8; lia).
    zstep.
    apply evt_done. unfold tsb_head_post. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold tsb_hA, tsb_hP. rewrite !(proj2 (Z.leb_gt _ _)) by lia. cbv zeta. unfold Buf_size.
    close_EM GA GD Gpend.
Qed.

Definition Z_TR_STORED : Z := 0x1ab40.
Definition buf_ptr (L : dlay) (buf : option Z) : Z := match buf with Some off => dl_Aw L + off | None => 0 end.

Definition tr_stored_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (buf : option Z) (len last : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DST m' L (tr_stored_block s buf len last).

Lemma tr_stored_block_spec : forall (L : dlay) (s : deflate_state) (buf : option Z) (len last lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 s -> ds_pending (tr_stored_block s buf len last) <= 65536 -> (len <> 0 -> buf <> None) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  a0 = wz (dl_As L) -> a1 = wz (buf_ptr L buf) -> a2 = wz len -> a3 = wz last ->
  evt psegs (tr_stored_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s buf len last lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_STORED) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST MI STK LO BEL BI ROOM NZ BOK RLEN RL -> -> -> ->. unfold Z_TR_STORED.
  pose proof BI as (RBV & RBB & RPD).
  rewrite tr_stored_block_eq in ROOM by lia. rewrite tsb_tail_pending in ROOM.
  pose proof (tsb_hP_range s) as RHP.
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MUf.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
  open_DST ST. lay_open LAY. below_open BEL. pose proof (ln_pend _ LENS) as LNP.
  carve_frame 32%nat STK.
  do 4 zstep.
  mv_group dsA_munch GA MUs WM. mv_group dsD_munch GD MUs WM. mv_group dpend_munch Gpend MUs WM. clear MUs.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH. clear GA GD Gpend.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => call (tsb_head L s last len mc) end.
  1:{ exact EMH. } 1:{ exact LAY. } 1:{ exact BI. } 1:{ lia. } 1:{ exact RL. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ eassumption. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  clear EMH. open_EM POST.
  do 8 zstep. do 4 zstep. (* 1.4 bi_windup: bi_used = ((bi_valid - 1) & 7) + 1 stored at 5944 *)
  remember (tsb_hA s last) as A1 eqn:EA1. remember (tsb_hP s) as P1 eqn:EP1.
  assert (LA1 : arr_len A1 = 65536) by (rewrite EA1, tsb_hA_len; exact LNP).
  pb_store Gpend A1 65536 (dl_Ab L) P1 (wrap8 (Z.land (wrap16 len) 255)) ltac:(apply lenb0).
  do 6 zstep.
  pb_store Gpend (arr_set A1 P1 (wrap8 (Z.land (wrap16 len) 255))) 65536 (dl_Ab L) (P1 + 1) (wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8)) ltac:(apply lenb1).
  do 6 zstep.
  pb_store Gpend (arr_set (arr_set A1 P1 (wrap8 (Z.land (wrap16 len) 255))) (P1 + 1) (wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8))) 65536 (dl_Ab L) (P1 + 1 + 1)
           (wrap8 (Z.land (wrap16 (Z.lnot len)) 255)) ltac:(apply lenb2).
  do 6 zstep.
  pb_store Gpend (arr_set (arr_set (arr_set A1 P1 (wrap8 (Z.land (wrap16 len) 255))) (P1 + 1) (wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8))) (P1 + 1 + 1)
                          (wrap8 (Z.land (wrap16 (Z.lnot len)) 255))) 65536 (dl_Ab L) (P1 + 1 + 1 + 1)
           (wrap8 (Z.shiftr (wrap16 (wrap16 (Z.lnot len))) 8)) ltac:(apply lenb3).
  fold (tsb_lenA A1 P1 len) in *.
  assert (LA2 : arr_len (tsb_lenA A1 P1 len) = 65536) by (unfold tsb_lenA; rewrite !arr_len_set; exact LA1).
  zstep. br_cases K.
  -
    do 3 zstep. do 5 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold tr_stored_block_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite tr_stored_block_eq by lia. unfold tsb_tail. cbv zeta. rewrite <- EA1, <- EP1.
    replace (negb (len =? 0)) with false by (symmetry; apply negb_false_iff, Z.eqb_eq; exact K).
    tr_groups MUf WM.
    lazymatch type of GA with rw_cells _ ?mc _ _ =>
      assert (EMF : EM mc L s (tsb_lenA A1 P1 len) (P1 + 1 + 1 + 1 + 1 + len) (wz 0) (wz 0)) by close_EM GA GD Gpend end.
    destruct (EM_to_groups _ _ _ _ _ _ _ 0 0 EMF eq_refl eq_refl) as (HA & HD & HP).
    constructor; [exact HA| exact GB| exact GC| exact HD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact HP| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
  -
    destruct buf as [off|]; [|exfalso; apply NZ; [exact K| reflexivity]]. cbn [fb_buf_ok buf_ptr] in *.
    do 5 zstep.
    mv_group dwin_munch Gwin MUf WM. open_win Gwin.
    pose proof (u8arr_sub_bytes _ (dl_Aw L) _ (Z.to_nat off) (Z.to_nat len) Gwin ltac:(rewrite av8_length; lia)) as SRC.
    rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
    assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_window s) off len)) = Z.to_nat len) by (rewrite length_map; apply arr_slice_length').
    destruct (u8arr_split3 _ (dl_Ab L) _ (Z.to_nat (P1 + 4)) (Z.to_nat len) Gpend ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3).
    rewrite !Z2Nat.id in O2 by lia. rewrite !Z2Nat.id in O3 by lia.
    assert (LO1 : length (firstn (Z.to_nat (P1 + 4)) (av8 (tsb_lenA A1 P1 len) 65536)) = Z.to_nat (P1 + 4)) by (rewrite length_firstn, av8_length; lia).
    assert (LO3 : length (skipn (Z.to_nat (P1 + 4) + Z.to_nat len) (av8 (tsb_lenA A1 P1 len) 65536)) = (Z.to_nat 65536 - (Z.to_nat (P1 + 4) + Z.to_nat len))%nat)
      by (rewrite length_skipn, av8_length; reflexivity).
    clear Gpend.
    call (memcpy_Z (dl_Ab L + (P1 + 4)) (dl_Aw L + off) len).
    1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    pose proof (u8arr_join3z _ (dl_Ab L) _ _ _ (P1 + 4) len ltac:(lia) ltac:(lia) LO1 O1 PC O3) as Gpend.
    rewrite av8_blit' in Gpend by lia.
    pose proof (av8_zlength (arr_blit (tsb_lenA A1 P1 len) (P1 + 4) (ds_window s) off len) 65536 ltac:(lia)) as LPBf.
    clear O1 O3 PC POST SRC LSRC LO1 LO3.
    do 3 zstep. do 5 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold tr_stored_block_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite tr_stored_block_eq by lia. unfold tsb_tail. cbv zeta. rewrite <- EA1, <- EP1.
    replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact K).
    replace (P1 + 1 + 1 + 1 + 1) with (P1 + 4) by lia.
    lazymatch type of Gwin with u8arr _ ?mc _ _ => fold (dwin mc L s) in Gwin end. tr_groups MUf WM.
    lazymatch type of GA with rw_cells _ ?mc _ _ =>
      assert (EMF : EM mc L s (arr_blit (tsb_lenA A1 P1 len) (P1 + 4) (ds_window s) off len) (P1 + 4 + len) (wz 0) (wz 0)) by close_EM GA GD Gpend end.
    destruct (EM_to_groups _ _ _ _ _ _ _ 0 0 EMF eq_refl eq_refl) as (HA & HD & HP).
    constructor; [exact HA| exact GB| exact GC| exact HD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact HP| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
Qed.
End Z_tr_stored.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.

Module Z_tr_fb3.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_init OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fbtail OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_arm_stored : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> RefFlushBlk13.sto_ok 65536 X buf len last -> RefFlushBlk13.post_ok 65536 last (tr_stored_block X buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tr_stored_block X buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b418) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI (ROOM & NN) (BIY & ROOMY) BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO.
  pose proof BEL as BEL0. below_open BEL0.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  unfold tfR. do 5 zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl psegs m1) as WMz.
  call (tr_stored_block_spec L X buf len last lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BI. } 1:{ exact ROOM. } 1:{ exact NN. } 1:{ exact BOK. } 1:{ exact Rlen. } 1:{ exact Rl. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST. name_mem m2.
  remember (tr_stored_block X buf len last) as Y eqn:EY.
  assert (ESY : ds_strm Y = c).
  { rewrite EY, (k_tr_stored_block _ _ _ keeps_strm eq_refl). exact ESTRM. }
  zs2. zs2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
  call (init_block_spec L Y).
  1:{ eassumption. } 1:{ eassumption. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite ESP in *.
  zstep. name_mem m3.
  br_cases_s K.
  - eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1b7f4 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
  - zs2. eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1b868 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
Qed.
End Z_tr_fb3.

Module Z_tr_st14.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_st13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_st13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_st13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_st13.Z_tr_st1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_st13.Z_tr_st12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_st13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4.RefSendTree3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition st_loop_post (L : dlay) (s : deflate_state) (T mc : Z) (R : deflate_state)
    (ra sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists n' nl' s0 s1 s2 s3 s4 s5 s6 s7 s8 wbb PB' PD' BB' BV' m',
    ms' = MS (stR L T (mc + 1) n' nl' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1cbc4) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV'.

Lemma st_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (tfc tdl bfc bdl : arr) (T N mc : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV n prevlen nextlen count mx mn : Z) (wbb : word)
    (ra sp gp tp s0 s2 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 T tfc tdl N -> tdl = tree_dl s t -> 0 < T -> T + 4 * N < 2^63 -> mc + 1 < N -> N <= 573 ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bfc i < 65536) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get tdl i <= 15) -> (forall i, 0 <= i < N -> 0 <= arr_get tdl i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get tdl n -> Z.of_nat (S f) = mc + 1 - n ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  R = send_tree_loop (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  send_tree_ok 65536 (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  evt psegs (st_loop_post L s T mc R ra sp gp tp s9 s10 s11 F fc m0)
      (MS (stR L T (mc + 1) n nextlen ra sp gp tp s0 (wz count) s2 (wz mx) (wz mn) (wz prevlen) s6 s7 s8 s9 s10 s11) F (wz 0x1c720) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros EMH HBB MI LAY MU WM RDT Etdl RT1 RT2 RmcN RN RDB Ebfc Ebdl RBf RTl RTn Rn Enl Ef RBV RPD Rc Rmx Rmn Rpl ER OK.
  - call (st_iter L s t tfc tdl bfc bdl T N mc n 0%nat R m PB PD BB BV prevlen nextlen count mx mn wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Etdl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RmcN. } 1:{ exact RN. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Ebfc. } 1:{ exact Ebdl. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. }
    1:{ exact Rn. } 1:{ exact Enl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. } 1:{ exact ER. } 1:{ exact OK. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    match goal with E : R = send_tree_loop 0 _ _ _ _ _ _ _ _ _ |- _ => rewrite send_loop_0 in E; rename E into ER' end.
    apply evt_done. unfold st_loop_post. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER'].
  - call (st_iter L s t tfc tdl bfc bdl T N mc n (S f) R m PB PD BB BV prevlen nextlen count mx mn wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Etdl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RmcN. } 1:{ exact RN. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Ebfc. } 1:{ exact Ebdl. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. }
    1:{ exact Rn. } 1:{ exact Enl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. } 1:{ exact ER. } 1:{ exact OK. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    match goal with E : R = send_tree_loop (S f) _ _ _ _ _ _ _ _ _, O : send_tree_ok _ (S f) _ _ _ _ _ _ _ _ _ |- _ =>
      eapply (IH L s t tfc tdl bfc bdl T N mc R m0); [eassumption| eassumption| eassumption| exact LAY| exact MU| exact WM| exact RDT| exact Etdl| exact RT1| exact RT2
        | exact RmcN| exact RN| exact RDB| exact Ebfc| exact Ebdl| exact RBf| exact RTl| exact RTn| lia| reflexivity| lia| assumption| assumption| assumption| assumption| assumption| assumption
        | exact E| exact O] end.
Qed.

Definition Z_SEND_TREE : Z := 0x1c680.
Definition tsz (t : tree_id) : Z := match t with TL => 573 | TD => 61 | TB => 39 end.

Lemma tree_readable : forall (W : list ivl) (m : mem) (L : dlay) (s : deflate_state) (t : tree_id),
  dlt m L s -> ddt m L s -> dbt m L s -> disjoint_from W (dl_As L + 212) 2692 ->
  ct_readable W m (dl_As L + toff t) (tree_fc s t) (tree_dl s t) (tsz t).
Proof.
  intros W m L s t Glt Gdt Gbt D. destruct t; cbn [toff tree_fc tree_dl tsz].
  - eapply ct_readable_rw; [exact Glt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
  - eapply ct_readable_rw; [exact Gdt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
  - eapply ct_readable_rw; [exact Gbt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
Qed.

Definition send_tree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch (cbW L lo sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DST m' L (send_tree s t mc).

Lemma send_tree_spec : forall (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> dlay_below L lo (bv_unsigned sp) ->
  0 <= mc -> mc + 1 < tsz t ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc s) i < 65536) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get (tree_dl s t) i <= 15) -> (forall i, 0 <= i < tsz t -> 0 <= arr_get (tree_dl s t) i < 65536) ->
  BINV 65536 s -> send_tree_safe 65536 s t mc ->
  a0 = wz (dl_As L) -> a1 = wz (dl_As L + toff t) -> a2 = wz mc ->
  evt psegs (send_tree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s t mc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_SEND_TREE) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST MI STK LO BEL Rmc RmcN RBf RTl RTn BI SAFE -> -> ->. unfold Z_SEND_TREE.
  pose proof BI as (RBV & RBB & RPD).
  pose proof (munch_refl (cbW L lo sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
  open_DST ST. lay_open LAY. below_open BEL. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb.
  assert (RDT : ct_readable (cbW L lo sp) m (dl_As L + toff t) (tree_fc s t) (tree_dl s t) (tsz t)) by (apply tree_readable; [exact Glt| exact Gdt| exact Gbt| cbn [disjoint_from]; lia]).
  assert (RDB : ct_readable (cbW L lo sp) m (dl_As L + 2748) (ds_bl_tree_fc s) (ds_bl_tree_dl s) 39) by (apply (tree_readable _ m L s TB); [exact Glt| exact Gdt| exact Gbt| cbn [disjoint_from]; lia]).
  assert (RtN : tsz t <= 573 /\ 212 <= toff t /\ toff t + 4 * tsz t <= 2904) by (destruct t; cbn [tsz toff]; lia).
  pose proof (RTn 0 ltac:(lia)) as Rnl0.
  unfold send_tree_safe, RefSendTree4.OK, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4.RefSendTree3.cnts0, Len in SAFE. replace (mc + 1 - 0) with (mc + 1) in SAFE by lia.
  carve_frame 80%nat STK.
  zstep. br_false.
  do 10 zstep.
  mv_group dsA_munch GA MUs WM. mv_group dsD_munch GD MUs WM. mv_group dpend_munch Gpend MUs WM. clear MUs.
  lazymatch goal with MIc : mem_inv psegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (RDT mc MU WM MIc 0 ltac:(lia)) as [_ RDl0] end.
  replace (dl_As L + toff t + 4 * 0 + 2) with (dl_As L + toff t + 2) in RDl0 by lia.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH. clear GA GD Gpend.
  assert (HBB : bv_unsigned (wz (ds_bi_buf s)) mod 2^16 = ds_bi_buf s mod 2^16) by apply lo16_unsigned_wz.
  assert (EX0 : upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) = s) by apply upd4_self.
  zs2. zs2. rewrite (zx16_small (arr_get (tree_dl s t) 0)) by lia. zs2. zs2. zs2. zs2.
  zstep. br_cases_s K0.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K0) in SAFE. cbn [fst snd] in SAFE. rewrite K0 in SAFE.
    rewrite K0. change (Z.b2z (0 <? 0)) with 0.
    do 16 zs2.
    destruct (Z.to_nat (mc + 1)) as [|f] eqn:En; [lia|].
    remember (send_tree_loop (S f) s t mc 0 (-1) 0 0 138 3) as R eqn:ER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
      call (st_loop f L s t (tree_fc s t) (tree_dl s t) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (dl_As L + toff t) (tsz t) mc R mcur
                    (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) 0 (-1) 0 0 138 3 (wz (ds_bi_buf s))) end.
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ exact RmcN. } 1:{ lia. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. } 1:{ lia. } 1:{ symmetry; exact K0. } 1:{ lia. }
    1:{ exact RBV. } 1:{ lia. } 1:{ lia. } 1:{ left; reflexivity. } 1:{ left; reflexivity. } 1:{ lia. }
    1:{ rewrite EX0. exact ER. } 1:{ rewrite EX0. exact SAFE. }
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ =>
      assert (EQF : send_tree s t mc = upd4 s pb pd bb bv);
      [ unfold send_tree, Len; rewrite (proj2 (Z.eqb_eq _ _) K0), K0, En; rewrite <- ER; exact E |] end.
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    unfold stR. do 11 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold send_tree_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K0) in SAFE. cbn [fst snd] in SAFE.
    rewrite (proj2 (Z.ltb_lt 0 _)) by lia. change (Z.b2z true) with 1.
    do 17 zs2.
    destruct (Z.to_nat (mc + 1)) as [|f] eqn:En; [lia|].
    remember (send_tree_loop (S f) s t mc 0 (-1) (arr_get (tree_dl s t) 0) 0 7 4) as R eqn:ER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
      call (st_loop f L s t (tree_fc s t) (tree_dl s t) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (dl_As L + toff t) (tsz t) mc R mcur
                    (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) 0 (-1) (arr_get (tree_dl s t) 0) 0 7 4 (wz (ds_bi_buf s))) end.
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ exact RmcN. } 1:{ lia. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. } 1:{ lia. } 1:{ reflexivity. } 1:{ lia. }
    1:{ exact RBV. } 1:{ lia. } 1:{ lia. } 1:{ right; right; reflexivity. } 1:{ right; reflexivity. } 1:{ lia. }
    1:{ rewrite EX0. exact ER. } 1:{ rewrite EX0. exact SAFE. }
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ =>
      assert (EQF : send_tree s t mc = upd4 s pb pd bb bv);
      [ unfold send_tree, Len; rewrite (proj2 (Z.eqb_neq _ _) K0), En; rewrite <- ER; exact E |] end.
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    unfold stR. do 11 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold send_tree_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
Qed.
End Z_tr_st14.

Module Z_tr_fb5.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit Z_tr_cb3 Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition blR (L : dlay) (sp : word) (last bufp mb r BV : Z) (s : deflate_state) (w : word)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz (dl_As L + 2750)) w (wz (ds_l_max_code s)) (wz 14) (wz (Z_BL_ORDER + r)) (wz (Z_BL_ORDER + (mb + 1)))
      (wz 16) (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition tfb_blo_iter_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb r : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 w pcx m',
    ms' = MS (blR L sp last bufp mb (r + 1) BV s w ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1b740 /\ r + 1 <> mb + 1) \/ (pcx = 0x1b7b4 /\ r + 1 = mb + 1)).

Ltac blo_fin MU WM GA GD Gpend LOW SIDE RW :=
  apply evt_done; unfold tfb_blo_iter_post, blR, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV, Z_BL_ORDER; RW; do 6 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LOW|];
  SIDE; split; [reflexivity| lia].

Lemma tfb_blo_iter : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb r V : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bdl (arr_get bl_order_a r) ->
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 -> 0 <= r <= mb -> mb <= 18 ->
  0 <= V < 65536 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) ->
  evt psegs (tfb_blo_iter_post L s sp last bufp mb r (sbF_PB PB PD BB BV V 3) (sbF_PD PD BV 3) (sbF_BB BB BV V 3) (sbF_BV BV 3)
                ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (blR L sp last bufp mb r BV s w ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b740) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV EMH HW MI LAY RDB Rr Rmb RV RBV RPD ROOM. unfold blR, tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (bl_order_bound r) as Ro.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI (arr_get bl_order_a r) ltac:(lia)) as [_ RDl]. rewrite <- EV in RDl.
  pose proof (u8ro_read psegs m Z_BL_ORDER (av8 bl_order_a 19) r _ (wa (Z_BL_ORDER + r)) (rod_bl_order m MI)
                (av8_nth bl_order_a 19 r ltac:(lia)) ltac:(lia) eq_refl) as RDo.
  unfold Z_BL_ORDER in *.
  replace (dl_As L + 2748 + 4 * arr_get bl_order_a r + 2) with (dl_As L + 2750 + arr_get bl_order_a r * 4) in RDl by lia.
  zsb. rewrite (bv8_small (arr_get bl_order_a r)) by lia.
  zs2. shl_norm. zs2. zs2. rewrite (zx16_small V) by lia. clear EV.
  zs2. zs2. sb_or w1 LO BB (exact HW).
  zs2. zstep. br_cases K.
  -
    zs2. zs2. zs2. replace (74720 + r + 1) with (74720 + (r + 1)) by lia.
    zstep. br_cases K2.
    + blo_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
    + blo_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
  -
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. reg_as (BV + -13) (BV + 3 - 16). replace (74720 + r + 1) with (74720 + (r + 1)) by lia.
    zstep. br_cases K2.
    + blo_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
    + blo_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
Qed.

Lemma bl_calls_S : forall s r k, bl_calls s r (S k) = (arr_get (ds_bl_tree_dl s) (arr_get bl_order_a r), 3) :: bl_calls s (r + 1) k.
Proof. reflexivity. Qed.

Definition tfb_blo_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (R : deflate_state)
    (ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 w PB' PD' BB' BV' m',
    ms' = MS (blR L sp last bufp mb (mb + 1) BV' s w ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b7b4) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' w (wz BV') /\ bv_unsigned w mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV' /\ 0 <= BV' <= 16 /\ 0 <= PD'.

Lemma tfb_blo_loop : forall (k : nat) (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb r : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= r -> Z.of_nat (S k) = mb + 1 - r -> mb <= 18 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bdl i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (bl_calls s r (S k)) ->
  R = sbs_run (upd4 s PB PD BB BV) (bl_calls s r (S k)) ->
  evt psegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (blR L sp last bufp mb r BV s w ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b740) fc None m (seg_rom psegs)).
Proof.
  induction k as [|k IH]; intros until m; intros Ebdl EMH HW MI LAY MU WM RDB Rr Ek Rmb RBd RBV RPD HSB ER.
  all: pose proof (bl_order_bound r) as Ro.
  all: rewrite bl_calls_S in HSB, ER; rewrite <- Ebdl in HSB, ER.
  all: apply sbs_ok_cons_flat in HSB; destruct HSB as (_ & ROOM & HSB2); rewrite sbs_run_cons_flat in ER.
  - call (tfb_blo_iter L s bfc bdl sp last bufp mb r (arr_get bdl (arr_get bl_order_a r)) PB PD BB BV wcell w).
    1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ lia. } 1:{ exact Rmb. } 1:{ apply RBd. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM; lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    cbn [bl_calls sbs_run] in ER. replace (r + 1) with (mb + 1) by lia.
    apply evt_done. unfold tfb_blo_post. do 9 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER|]. split; [apply sbF_BV_range; [exact RBV| lia]| pose proof (sbF_PD_range PD BV 3 RPD); lia].
  - call (tfb_blo_iter L s bfc bdl sp last bufp mb r (arr_get bdl (arr_get bl_order_a r)) PB PD BB BV wcell w).
    1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ lia. } 1:{ exact Rmb. } 1:{ apply RBd. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM; lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    match goal with H : EM ?mm _ _ _ _ ?wc _, HB : bv_unsigned ?wc mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s bfc bdl sp last bufp mb (r + 1) R m0); [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| exact Rmb| exact RBd
        | apply sbF_BV_range; [exact RBV| lia]| pose proof (sbF_PD_range PD BV 3 RPD); lia| exact HSB2| exact ER] end.
Qed.
End Z_tr_fb5.

Module Z_tr_fb4.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit Z_tr_cb3 Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition tfb_d1_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z)
    (ra gp tp t0 t1 t2 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a4 a6 wcell w m',
    ms' = MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) a2 w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b57c) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wcell (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma tfb_d1 : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= last <= 1 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) ->
  evt psegs (tfb_d1_post L s sp last len bufp mb (sbF_PB PB PD BB BV (4 + last) 3) (sbF_PD PD BV 3) (sbF_BB BB BV (4 + last) 3) BV (sbF_BV BV 3)
                ra gp tp t0 t1 t2 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 (wz BV) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b4b8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY Rl RBV RPD ROOM. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zs2. reg_as (last + 4) (4 + last). zstep. br_cases K.
  -
    zs2. zs2. zs2. sb_or w LO BB (rewrite lo16_sx16; exact HBB). zs2.
    apply evt_done. unfold tfb_d1_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 6 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| exact LO].
  -
    zs2. zs2. zs2. zs2. zs2. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    sbf_b0 L Gpend PB PD (nbv BB BV (4 + last)) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV (4 + last)) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia.
    zs2. zs2. reg_as (BV + -13) (BV + 3 - 16).
    apply evt_done. unfold tfb_d1_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 6 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

Definition tfb_d2_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a6 a7 wcell w pcx m',
    ms' = MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wcell (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1b5fc /\ BV < 12) \/ (pcx = 0x1b648 /\ 12 <= BV)).

Lemma lmax_eqm : forall lmax, (65535 + lmax - 255) mod 2^16 = (lmax - 256) mod 2^16.
Proof. intros. replace (65535 + lmax - 255) with (lmax - 256 + 1 * 2^16) by lia. apply Z.mod_add. lia. Qed.

Ltac d2_fin MU WM GA GD Gpend LOW SIDE RW :=
  apply evt_done; unfold tfb_d2_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; RW; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LOW|];
  SIDE; split; [reflexivity| lia].

Lemma tfb_d2 : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z) (wcell w : word) (hB1 hB2 hB3 : list byte)
    (ra gp tp t0 t1 t2 a2 a4 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  0 <= ds_l_max_code s < 2^31 -> 0 <= ds_d_max_code s < 2^31 -> 0 <= BV <= 16 -> 0 <= PD -> (11 < BV -> PD + 2 <= 65536) ->
  evt psegs (tfb_d2_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_l_max_code s - 256) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_l_max_code s - 256) 5) (sbF_BV BV 5)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) a2 w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b57c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY GB Rlm Rdm RBV RPD ROOM. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (lmax_eqm (ds_l_max_code s)) as EQV.
  lay_open LAY. open_EM EMH. unfold dsB_cells in GB.
  zs2. zs2. zs2. clear GB. zs2. zs2. zs2. reg_as (65535 + ds_l_max_code s + -255) (65535 + ds_l_max_code s - 255).
  zstep. br_cases K.
  -
    zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV _ _ EQV) in LO.
    zs2. zs2. zs2.
    zstep. br_cases K2.
    + d2_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
    + d2_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
  -
    zs2. zs2. zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV _ _ EQV) in LO.
    sbf_b0 L Gpend PB PD (nbv BB BV (ds_l_max_code s - 256)) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV (ds_l_max_code s - 256)) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia. rewrite (wrap16_eqm16 _ _ EQV).
    zs2. zs2. zs2. reg_as (BV + -11) (BV + 5 - 16).
    zstep. br_cases K2.
    + d2_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
    + d2_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
Qed.

Definition tfb_d3_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a6 wcell w pcx m',
    ms' = MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz (65535 + mb - 2)) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wcell (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1b620 /\ BV < 13) \/ (pcx = 0x1b6b8 /\ 13 <= BV)).

Ltac d3_fin MU WM GA GD Gpend LOW SIDE RW :=
  apply evt_done; unfold tfb_d3_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; RW; do 6 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LOW|];
  SIDE; split; [reflexivity| lia].

Lemma tfb_d3k : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a4 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_d_max_code s < 2^31 -> 0 <= BV < 12 -> 0 <= PD -> 0 <= mb <= 18 ->
  evt psegs (tfb_d3_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_d_max_code s) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_d_max_code s) 5) (sbF_BV BV 5)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b5fc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rdm RBV RPD Rmb. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. sb_or w1 LO BB (exact HW).
  zs2. zs2. zs2. zs2. zs2. zs2. reg_as (65535 + mb + -2) (65535 + mb - 2).
  zstep. br_cases K2.
  - d3_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
  - d3_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
Qed.

Lemma tfb_d3f : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a4 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_d_max_code s < 2^31 -> 12 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= mb <= 18 ->
  evt psegs (tfb_d3_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_d_max_code s) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_d_max_code s) 5) (sbF_BV BV 5)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b648) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rdm RBV RPD ROOM Rmb. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zs2. sb_or w1 LO BB (exact HW).
  sbf_b0 L Gpend PB PD (nbv BB BV (ds_d_max_code s)) LO.
  sbf_b1 L Gpend GD PB PD (nbv BB BV (ds_d_max_code s)) LO.
  zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia.
  zs2. zs2. zs2. zs2. zs2. zs2. reg_as (BV + -11) (BV + 5 - 16). reg_as (65535 + mb + -2) (65535 + mb - 2).
  zstep. br_cases K2.
  - d3_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
  - d3_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
Qed.

Definition tfb_d4_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a3 a4 a6 wcell w m',
    ms' = MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 a0 w (wz (ds_l_max_code s)) a3 a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1b710) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wcell (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma mb_eqm : forall mb, (65535 + mb - 2) mod 2^16 = (mb - 3) mod 2^16.
Proof. intros. replace (65535 + mb - 2) with (mb - 3 + 1 * 2^16) by lia. apply Z.mod_add. lia. Qed.

Lemma tfb_d4k : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a4 a6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= BV < 13 -> 0 <= PD -> 0 <= mb <= 18 ->
  evt psegs (tfb_d4_post L s sp last bufp mb (sbF_PB PB PD BB BV (mb - 3) 4) (sbF_PD PD BV 4) (sbF_BB BB BV (mb - 3) 4) BV (sbF_BV BV 4)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz (65535 + mb - 2)) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b620) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD Rmb. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (mb_eqm mb) as EQV.
  zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV _ _ EQV) in LO.
  zs2. zs2.
  apply evt_done. unfold tfb_d4_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 7 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact EMH| exact LO].
Qed.

Lemma tfb_d4f : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a4 a6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  13 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= mb <= 18 ->
  evt psegs (tfb_d4_post L s sp last bufp mb (sbF_PB PB PD BB BV (mb - 3) 4) (sbF_PD PD BV 4) (sbF_BB BB BV (mb - 3) 4) BV (sbF_BV BV 4)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz (65535 + mb - 2)) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b6b8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD ROOM Rmb. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (mb_eqm mb) as EQV.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV _ _ EQV) in LO.
  sbf_b0 L Gpend PB PD (nbv BB BV (mb - 3)) LO.
  sbf_b1 L Gpend GD PB PD (nbv BB BV (mb - 3)) LO.
  zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia. rewrite (wrap16_eqm16 _ _ EQV).
  zs2. reg_as (BV + -12) (BV + 4 - 16).
  apply evt_done. unfold tfb_d4_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 7 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
End Z_tr_fb4.

Module Z_tr_fb6.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit Z_tr_cb3 Z_tr_st4 Z_tr_st13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_st13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_dyn_hdr2 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV0 BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a0 a3 a4 a6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wcell (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= mb <= 18 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bdl i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (bl_calls s 0 (Z.to_nat (mb + 1))) ->
  R = sbs_run (upd4 s PB PD BB BV) (bl_calls s 0 (Z.to_nat (mb + 1))) ->
  evt psegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 a0 w (wz (ds_l_max_code s)) a3 a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b710) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Ebdl EMH HW MI LAY MU WM RDB Rmb RBd RBV RPD HSB ER. unfold tfR.
  pose proof EMH as EMo. lay_open LAY. open_EM EMo.
  zs2. do 7 zs2.
  destruct (Z.to_nat (mb + 1)) as [|k] eqn:En; [lia|].
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (EM1 : EM mm L s PB PD wcell (wz BV)) by close_EM GA GD Gpend end.
  clear GA GD Gpend.
  replace (wz 74720) with (wz (Z_BL_ORDER + 0)) by reflexivity. change (74720 + (mb + 1)) with (Z_BL_ORDER + (mb + 1)).
  eapply (tfb_blo_loop k L s bfc bdl sp last bufp mb 0 R m0 PB PD BB BV wcell w);
    [exact Ebdl| exact EM1| exact HW| eassumption| assumption| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV| exact RPD| exact HSB| exact ER].
Qed.

Lemma tfb_dyn_hdr : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last len bufp mb : Z) (R : deflate_state)
    (PB : arr) (PD BB BV : Z) (wbb : word) (hB1 hB2 hB3 : list byte)
    (ra gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= last <= 1 -> 0 <= ds_l_max_code s < 2^31 -> 0 <= ds_d_max_code s < 2^31 -> 0 <= mb <= 18 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bdl i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (hd_calls last s mb) ->
  R = sbs_run (upd4 s PB PD BB BV) (hd_calls last s mb) ->
  evt psegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 (wz BV) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b4b8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Ebdl EMH HBB MI LAY GB RDB Rl Rlm Rdm Rmb RBd RBV RPD HSB ER.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb. pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & Rb & _).
  unfold dsB_cells in GB. unfold hd_calls in HSB, ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM1 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM2 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM3 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM4 & HSB). rewrite sbs_run_cons_flat in ER.
  pose proof (sbF_BV_range BV 3 RBV ltac:(lia)) as RBV1. pose proof (sbF_BV_range _ 5 RBV1 ltac:(lia)) as RBV2.
  pose proof (sbF_BV_range _ 5 RBV2 ltac:(lia)) as RBV3. pose proof (sbF_BV_range _ 4 RBV3 ltac:(lia)) as RBV4.
  assert (RPD1 : 0 <= sbF_PD PD BV 3) by (apply sbF_PD_nonneg; exact RPD).
  assert (RPD2 : 0 <= sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) by (apply sbF_PD_nonneg; exact RPD1).
  assert (RPD3 : 0 <= sbF_PD (sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) (sbF_BV (sbF_BV BV 3) 5) 5) by (apply sbF_PD_nonneg; exact RPD2).
  assert (RPD4 : 0 <= sbF_PD (sbF_PD (sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) (sbF_BV (sbF_BV BV 3) 5) 5) (sbF_BV (sbF_BV (sbF_BV BV 3) 5) 5) 4) by (apply sbF_PD_nonneg; exact RPD3).
  call (tfb_d1 L s sp last len bufp mb PB PD BB BV wbb).
  1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM1; lia. }
  match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (tfb_d2 L s sp last len bufp mb pb pd bb bv0 (sbF_BV BV 3) wc wr hB1 hB2 hB3);
    [exact H| exact HB| eassumption| exact LAY| exact GB| exact Rlm| exact Rdm| exact RBV1| lia| intros; apply ROOM2; lia|] end.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X2]|[-> X2]] end.
  -
    match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (tfb_d3k L s sp last bufp mb pb pd bb bv wc wr);
      [exact H| exact HB| eassumption| exact LAY| exact Rdm| lia| lia| exact Rmb|] end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X3]|[-> X3]] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4k L s sp last bufp mb pb pd bb bv wc wr);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| exact Rmb|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 _ wc wr);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| exact Rmb| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4f L s sp last bufp mb pb pd bb bv wc wr);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| apply ROOM4; lia| exact Rmb|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 _ wc wr);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| exact Rmb| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
  -
    match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (tfb_d3f L s sp last bufp mb pb pd bb bv wc wr);
      [exact H| exact HB| eassumption| exact LAY| exact Rdm| lia| lia| apply ROOM3; lia| exact Rmb|] end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X3]|[-> X3]] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4k L s sp last bufp mb pb pd bb bv wc wr);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| exact Rmb|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 _ wc wr);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| exact Rmb| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4f L s sp last bufp mb pb pd bb bv wc wr);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| apply ROOM4; lia| exact Rmb|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 _ wc wr);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| exact Rmb| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
Qed.
End Z_tr_fb6.

Module Z_tr_fb7.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fbpure.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_init OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_st14 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fbtail OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fbpure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel TreeModel FlushBlockModel RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma ct_readable_weaken : forall W m T fc dl n n', ct_readable W m T fc dl n -> n' <= n -> ct_readable W m T fc dl n'.
Proof. intros W m T fc dl n n' H Hn m' MU WM MI i Hi. apply H; [exact MU| exact WM| exact MI| lia]. Qed.

Lemma tfb_arm_dyn : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len bufp mb lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok 65536 last X mb -> RefFlushBlk13.post_ok 65536 last (tfb_emit 1 X mb buf len last) ->
  0 <= last <= 1 -> 0 <= mb <= 18 ->
  Rfin = tfb_fin last (tfb_emit 1 X mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 (wz (ds_bi_valid X)) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b4b8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL DOK (BIY & ROOMY) Rl Rmb ER.
  unfold Z_TRFB_STACK in LO. rewrite (RefFlushBlk13.tfb_emit_1 buf len last X mb Rmb) in ER, BIY, ROOMY. cbv zeta in ER, BIY, ROOMY.
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok in DOK. cbv zeta in DOK.
  destruct DOK as (BI & HOK & (Rlm0 & Rlm1) & (Rdm0 & Rdm1) & (_ & RBd) & RBf & RLl & RLn & RDl & RDn & SAFE1 & SAFE2 & CBOK & RLf & RDf & _ & Rsn & Rlb).
  pose proof BI as (RBV & RBB & RPD).
  pose proof BEL as BEL0. below_open BEL0.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  remember (sbs_run X (hd_calls last X mb)) as X11 eqn:E11.
  assert (T11 : trees8 X11 = trees8 X) by (rewrite E11; apply trees8_sbs_run).
  assert (BI11 : BINV 65536 X11) by (rewrite E11; apply sbs_BINV; assumption).
  remember (send_tree X11 TL (ds_l_max_code X)) as X12 eqn:E12.
  assert (T12 : trees8 X12 = trees8 X) by (rewrite E12, trees8_send_tree; exact T11).
  assert (BI12 : BINV 65536 X12) by (rewrite E12; apply send_tree_BINV; assumption).
  remember (send_tree X12 TD (ds_d_max_code X)) as X13 eqn:E13.
  assert (T13 : trees8 X13 = trees8 X) by (rewrite E13, trees8_send_tree; exact T12).
  assert (ESN : ds_sym_next X13 = ds_sym_next X).
  { rewrite E13, (k_send_tree _ _ _ keeps_sym_next eq_refl), E12, (k_send_tree _ _ _ keeps_sym_next eq_refl), E11. apply (k_sbs_run _ _ _ keeps_sym_next eq_refl). }
  assert (ELB : ds_lit_bufsize X13 = ds_lit_bufsize X).
  { rewrite E13, (k_send_tree _ _ _ keeps_lit_bufsize eq_refl), E12, (k_send_tree _ _ _ keeps_lit_bufsize eq_refl), E11. apply (k_sbs_run _ _ _ keeps_lit_bufsize eq_refl). }
  assert (ES13 : ds_strm X13 = c).
  { rewrite E13, (k_send_tree _ _ _ keeps_strm eq_refl), E12, (k_send_tree _ _ _ keeps_strm eq_refl), E11, (k_sbs_run _ _ _ keeps_strm eq_refl). exact ESTRM. }
  destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.trees8_facts _ _ T11) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.trees8_facts _ _ T12) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.trees8_facts _ _ T13) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof (munch_refl (Wem L) m) as MUw. pose proof (wmono_refl psegs m) as WMw.
  open_DST ST. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb. lay_open LAY.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH.
  destruct GB as (hB1 & hB2 & hB3 & GB). unfold dsB_cells in GB.
  assert (RDB : ct_readable (Wem L) m (dl_As L + 2748) (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39)
    by (eapply ct_readable_rw; [exact Gbt| lia| lia| cbn [disjoint_from]; lia]).
  call (tfb_dyn_hdr L X (ds_bl_tree_fc X) (ds_bl_tree_dl X) sp last len bufp mb X11 (ds_pending_buf X) (ds_pending X) (ds_bi_buf X) (ds_bi_valid X) (wz (ds_bi_buf X)) hB1 hB2 hB3).
  1:{ reflexivity. } 1:{ exact EMH. } 1:{ apply lo16_unsigned_wz. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact GB. } 1:{ exact RDB. }
  1:{ exact Rl. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmb. } 1:{ exact RBd. } 1:{ exact RBV. } 1:{ lia. }
  1:{ rewrite upd4_self. exact HOK. } 1:{ rewrite upd4_self. exact E11. }
  name_mem m1.
  match goal with H : EM m1 _ _ _ _ _ _ |- _ => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
  match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
    destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
  clear GA GD Gpend EMH. tr_groups MUw WMw. clear MUw WMw.
  assert (ST11 : DST m1 L X11).
  { match goal with E : X11 = upd4 _ _ _ _ _ |- _ => rewrite E end.
    constructor; [exact HA| exists hB1, hB2, hB3; exact GB| exact GC| exact HD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact HP| | exact LAY].
    destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]. constructor; unfold upd4; dsred; assumption. }
  clear HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead EMf.
  unfold blR, tfR. do 4 zs2. name_mem m2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
  call (send_tree_spec L X11 TL (ds_l_max_code X) lo).
  1:{ exact ST11. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ lia. } 1:{ cbn [tsz]. lia. } 1:{ rewrite A5. exact RBf. }
  1:{ cbn [tree_dl]. rewrite A2. exact RLl. } 1:{ cbn [tree_dl tsz]. rewrite A2. exact RLn. }
  1:{ exact BI11. } 1:{ exact SAFE1. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST11. rewrite <- E12 in *. name_mem m3.
  do 5 zs2. name_mem m4.
  pose proof (munch_refl (tfWz L lo sp) m4) as MUz. pose proof (wmono_refl psegs m4) as WMz.
  call (send_tree_spec L X12 TD (ds_d_max_code X) lo).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ lia. } 1:{ cbn [tsz]. lia. } 1:{ rewrite B5. exact RBf. }
  1:{ cbn [tree_dl]. rewrite B4. exact RDl. } 1:{ cbn [tree_dl tsz]. rewrite B4. exact RDn. }
  1:{ exact BI12. } 1:{ exact SAFE2. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite <- E13 in *. name_mem m5.
  do 4 zs2. name_mem m6.
  match goal with H : DST m6 L X13 |- _ => pose proof H as ST13; destruct H as [_ _ _ _ Glt Gdt Gbt _ _ _ _ _ _ _ _ _] end.
  assert (DISJ : disjoint_from (cbW L lo (wz (bv_unsigned sp + -64))) (dl_As L + 212) 2692) by (cbn [disjoint_from]; lia).
  pose proof (tree_readable _ m6 L X13 TL Glt Gdt Gbt DISJ) as RDL. cbn [toff tree_fc tree_dl tsz] in RDL. rewrite C1, C2 in RDL.
  pose proof (tree_readable _ m6 L X13 TD Glt Gdt Gbt DISJ) as RDD. cbn [toff tree_fc tree_dl tsz] in RDD. rewrite C3, C4 in RDD.
  clear Glt Gdt Gbt DISJ.
  pose proof (munch_refl (tfWz L lo sp) m6) as MUz. pose proof (wmono_refl psegs m6) as WMz.
  call (compress_block_spec L X13 (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) (ds_dyn_dtree_fc X) (ds_dyn_dtree_dl X) (dl_As L + 212) (dl_As L + 2504) lo).
  1:{ exact ST13. } 1:{ eassumption. } 1:{ eassumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ eapply ct_readable_weaken; [exact RDL| lia]. } 1:{ eapply ct_readable_weaken; [exact RDD| lia]. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RLf. } 1:{ exact RDf. } 1:{ exact CBOK. }
  1:{ rewrite ELB. lia. } 1:{ rewrite ESN. lia. } 1:{ rewrite ESN. lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST13. name_mem m7.
  rewrite C1, C2, C3, C4 in ER, BIY, ROOMY.
  remember (compress_block X13 (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) (ds_dyn_dtree_fc X) (ds_dyn_dtree_dl X)) as Y eqn:EY.
  assert (ESY : ds_strm Y = c) by (rewrite EY, (k_compress_block _ _ _ keeps_strm eq_refl); exact ES13).
  zs2. zs2. name_mem m8.
  pose proof (munch_refl (tfWz L lo sp) m8) as MUz. pose proof (wmono_refl psegs m8) as WMz.
  call (init_block_spec L Y).
  1:{ eassumption. } 1:{ eassumption. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite ESP in *.
  zstep. name_mem m9.
  br_cases_s K.
  - eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1b868 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
  - eapply (tfb_finish L (init_block Y) Rfin c last lo 0x1b7f4 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
Qed.
End Z_tr_fb7.

Module Z_tr_fb8.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel TreeModel FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_emit_ns : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len bufp mb SL OL d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> 0 <= last <= 1 -> 0 <= mb <= 18 -> 0 <= SL < 2^64 -> 0 <= OL < 2^64 ->
  d = (if SL =? OL then 0 else 1) ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok 65536 last X mb | _ => RefFlushBlk13.sto_ok 65536 X buf len last end ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X mb buf len last) ->
  Rfin = tfb_fin last (tfb_emit d X mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz SL) a2 (wz OL) a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b43c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI Rl Rmb RSL ROL Ed SAFE POK ER.
  pose proof BI as (RBV & RBB & RPD).
  pose proof ST as ST'. destruct ST' as [_ _ _ GD _ _ _ _ _ _ _ _ _ _ _ LAY]. lay_open LAY.
  destruct GD as (hD0 & hD1 & hD2 & hD3 & hD4 & GD). unfold dsD_cells in GD.
  unfold tfR. zs2. clear GD. zstep. br_cases K.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in Ed. subst d.
    eapply (tfb_arm_dyn L X Rfin c buf last len bufp mb lo m0); try eassumption.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in Ed. subst d. rewrite tfb_emit_0 in POK, ER.
    eapply (tfb_arm_static L X Rfin c last len bufp lo m0); try eassumption.
Qed.

Lemma tfb_emit_all : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len mb SL OL d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv psegs m ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 -> 0 <= mb <= 18 -> 0 <= SL < 2^64 -> 0 <= OL < 2^64 ->
  d = (if (wrap64 (len + 4) <=? OL) && is_some buf then 2 else if SL =? OL then 0 else 1) ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok 65536 last X mb | _ => RefFlushBlk13.sto_ok 65536 X buf len last end ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X mb buf len last) ->
  Rfin = tfb_fin last (tfb_emit d X mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 (wz mb) (wz SL) a2 (wz OL) a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b40c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI BOK Rlen Rl Rmb RSL ROL Ed SAFE POK ER.
  pose proof BI as (RBV & RBB & RPD).
  assert (LAY : dlay_ok L) by (destruct ST; assumption). lay_open LAY.
  unfold tfR. destruct buf as [off|]; cbn [buf_ptr is_some] in *.
  -
    pose proof BOK as [Roff Roff2].
    zstep. br_false. zs2. zstep. br_cases K.
    +
      rewrite wrap64_id in Ed by lia. rewrite (proj2 (Z.leb_gt _ _)) in Ed by lia. cbn [andb] in Ed.
      eapply (tfb_emit_ns L X Rfin c (Some off) last len (dl_Aw L + off) mb SL OL d lo m0); try eassumption.
    + rewrite wrap64_id in Ed by lia. rewrite (proj2 (Z.leb_le _ _)) in Ed by lia. cbn [andb] in Ed. subst d. rewrite tfb_emit_2 in POK, ER.
      eapply (tfb_arm_stored L X Rfin c (Some off) last len lo m0); try eassumption.
  -
    rewrite Bool.andb_false_r in Ed.
    zstep. br_true.
    eapply (tfb_emit_ns L X Rfin c None last len 0 mb SL OL d lo m0); try eassumption.
Qed.

Definition tfb_SL (X6 : deflate_state) : Z := Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3.
Definition tfb_OL (X6 : deflate_state) : Z :=
  let opt_lenb := Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3 in
  if (tfb_SL X6 <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then tfb_SL X6 else opt_lenb.

Definition tfb_optlen_post (L : dlay) (X5 : deflate_state) (sp : word) (last len bufp mb : Z)
    (ra gp tp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a4 m',
    ms' = MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz (tfb_SL (tfb_X6 X5 mb))) a2 (wz (tfb_OL (tfb_X6 X5 mb))) a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1b40c) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 5912, dl_As L + 5920)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ dsD m' L (tfb_X6 X5 mb).

Lemma tfb_optlen : forall (L : dlay) (X5 : deflate_state) (sp : word) (last len bufp mb : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dsA m L X5 -> dsD m L X5 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_opt_len X5 < 2^63 -> 0 <= ds_static_len X5 < 2^63 -> 0 <= ds_strategy X5 <= 4 -> 0 <= mb <= 18 ->
  evt psegs (tfb_optlen_post L X5 sp last len bufp mb ra gp tp t0 t1 t2 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b3cc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros GA GD MI LAY Rol Rsl Rst Rmb.
  pose proof (munch_refl [(dl_As L + 5912, dl_As L + 5920)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY.
  destruct GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA). unfold dsA_cells in GA.
  destruct GD as (hD0 & hD1 & hD2 & hD3 & hD4 & GD). unfold dsD_cells in GD.
  assert (SHR : forall x, 0 <= x < 2^63 + 200 -> 0 <= Z.shiftr x 3 < 2^63).
  { intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (E6o : ds_opt_len (tfb_X6 X5 mb) = mb * 2 + mb + ds_opt_len X5 + 17).
  { unfold tfb_X6. rewrite RefFlushBlk13.ds_opt_len_set_opt_len, wrap64_id by lia. lia. }
  assert (ESL : tfb_SL (tfb_X6 X5 mb) = Z.shiftr (ds_static_len X5 + 10) 3).
  { unfold tfb_SL. change (ds_static_len (tfb_X6 X5 mb)) with (ds_static_len X5). rewrite wrap64_id by lia. f_equal. lia. }
  assert (EOLb : Z.shiftr (wrap64 (ds_opt_len (tfb_X6 X5 mb) + 3 + 7)) 3 = Z.shiftr (mb * 2 + mb + ds_opt_len X5 + 27) 3).
  { rewrite E6o, wrap64_id by lia. f_equal. lia. }
  pose proof (SHR (ds_static_len X5 + 10) ltac:(lia)) as RSLb. pose proof (SHR (mb * 2 + mb + ds_opt_len X5 + 27) ltac:(lia)) as ROLb.
  unfold tfR. zs2. zs2. zs2. shl_norm. do 7 zs2.
  set (SLb := Z.shiftr (ds_static_len X5 + 10) 3) in *. set (OLb := Z.shiftr (mb * 2 + mb + ds_opt_len X5 + 27) 3) in *.
  zs2. zstep. br_cases K.
  -
    zs2.
    apply evt_done. unfold tfb_optlen_post, tfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
    rewrite (proj2 (Z.leb_le SLb OLb)) by lia. cbn [orb]. do 3 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
  - zs2. zs2. zstep. br_cases K2.
    +
      apply evt_done. unfold tfb_optlen_post, tfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
      rewrite (proj2 (Z.leb_gt SLb OLb)) by lia. change (ds_strategy (tfb_X6 X5 mb)) with (ds_strategy X5). unfold Z_FIXED.
      rewrite (proj2 (Z.eqb_neq _ _) K2). cbn [orb]. do 3 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
    + zs2.
      apply evt_done. unfold tfb_optlen_post, tfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
      change (ds_strategy (tfb_X6 X5 mb)) with (ds_strategy X5). unfold Z_FIXED.
      rewrite (proj2 (Z.eqb_eq _ _) K2), Bool.orb_true_r. do 3 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
Qed.
End Z_tr_fb8.


Module Z_tr_scan2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition scR2 (L : dlay) (T mc : Z) (vt0 vt1 vt2 va1 va3 vt4 : Z) (t4x ra sp gp tp s0 s1 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) :=
  mkR ra sp gp tp (wz vt1) (wz vt2) t3 s0 s1 (wz (dl_As L + 2748)) (wz va1) (wz va3) (wz 4) (wz (T + 4 * (mc + 1) + 6)) (wz 9) a7 (wz vt0)
      s2 s3 s4 s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 (wz vt4) t4x t5 t6.

Definition sd_iter_post (L : dlay) (s1 : deflate_state) (t : tree_id) (T mc n : Z) (dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a7 t3 b' prevlen' count' mx' mn' pcx m',
    ms' = MS (scR2 L T mc mx' mn' count' (arr_get dlT (n + 1)) (T + 4 * (n + 1) + 6) prevlen' t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wbt L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39
    /\ (forall f, scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc n prevlen nextlen count mx mn
                  = scan_tree_loop f (set_bl_tree_fc s1 b') t mc (n + 1) prevlen' (arr_get dlT (n + 1)) count' mx' mn')
    /\ 0 <= count' < mx' /\ (mx' = 138 \/ mx' = 6 \/ mx' = 7) /\ (mn' = 3 \/ mn' = 4) /\ -1 <= prevlen' <= 15
    /\ ((pcx = 0x1b20c /\ n + 1 <= mc) \/ (pcx = 0x1b2c4 /\ n = mc)).

Ltac sd_close T n MU WM ARR MOD :=
  let KE := fresh "KE" in
  zs2; zs2; zs2; zstep; reg_as (T + 4 * n + 10) (T + 4 * (n + 1) + 6); br_cases KE;
  (apply evt_done; unfold sd_iter_post, scR2; do 9 eexists;
   split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
   split; [exact ARR|]; split; [rewrite ?arr_len_set; assumption|]; split; [MOD|];
   split; [destr_ifs; lia|]; split; [destr_ifs; auto|]; split; [destr_ifs; auto|]; split; [lia|];
   first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]]).

Lemma sd_upd : forall (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc n : Z) (dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get dlT n -> 0 <= nextlen <= 15 ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (count + 1 <? mx) && (nextlen =? arr_get dlT (n + 1)) = false ->
  evt psegs (sd_iter_post L s1 t T mc n dlT bdl b prevlen nextlen count mx mn t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (scR2 L T mc mx mn count (arr_get dlT (n + 1)) (T + 4 * n + 6) prevlen t4x ra sp gp tp s0 s1r (wz nextlen) s2 s3 s4 s5 s7 s8 s9 s10 s11 (wz (count + 1)) t5 t6)
          F (wz 0x1b220) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LNB MI LAY RT1 RT2 RNT HL HDL Rn Enl Rcl Rc Rmx Rmn Rpl CND. unfold scR2.
  pose proof (munch_refl (Wbt L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. pose proof (avct_zlength b bdl 39 ltac:(lia)) as LCT.
  pose proof (HDL (n + 1) ltac:(lia)) as Rnl'.
  assert (CND' : mx <= count + 1 \/ nextlen <> arr_get dlT (n + 1)).
  { apply andb_false_iff in CND. destruct CND as [C|C]; [left; apply Z.ltb_ge in C; lia| right; apply Z.eqb_neq in C; exact C]. }
  zstep. br_cases K1.
  -
    zstep. br_cases_s K2.
    +
      zstep. br_cases K3.
      *
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 18) _ (wa (dl_As L + 2748 + 2 * (2 * 18))) ARR (avct_nth_fc b bdl 39 18 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 18 (wrap16 (arr_get b 18 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { zs2. do 3 zs2. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
      *
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 17) _ (wa (dl_As L + 2748 + 2 * (2 * 17))) ARR (avct_nth_fc b bdl 39 17 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 17 (wrap16 (arr_get b 17 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { zs2. do 3 zs2. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
    +
      zstep. br_cases_s K3.
      *
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 16) _ (wa (dl_As L + 2748 + 2 * (2 * 16))) ARR (avct_nth_fc b bdl 39 16 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 16 (wrap16 (arr_get b 16 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { do 3 zs2. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
      *
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * nextlen) _ (wa (dl_As L + 2748 + 2 * (2 * nextlen))) ARR (avct_nth_fc b bdl 39 nextlen ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. shl_norm. zs2. zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) nextlen (wrap16 (arr_get b nextlen + 1)) ltac:(apply le2_add_sx16).
        set (b1 := arr_set b nextlen (wrap16 (arr_get b nextlen + 1))) in *.
        lazymatch type of ARR with u8arr _ ?mc _ _ =>
          pose proof (u16arr_read psegs mc (dl_As L + 2748) (avct b1 bdl 39) (2 * 16) _ (wa (dl_As L + 2748 + 2 * (2 * 16))) ARR (avct_nth_fc b1 bdl 39 16 ltac:(lia)) ltac:(lia) eq_refl) as RD1 end.
        zs2. zs2.
        ct_store_fc ARR b1 bdl 39 (dl_As L + 2748) 16 (wrap16 (arr_get b1 16 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. subst b1. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { do 3 zs2. subst b1. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
  -
    pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * nextlen) _ (wa (dl_As L + 2748 + 2 * (2 * nextlen))) ARR (avct_nth_fc b bdl 39 nextlen ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs2. shl_norm. zs2. zs2. zs2.
    ct_store_fc ARR b bdl 39 (dl_As L + 2748) nextlen (wrap16 (arr_get b nextlen + (count + 1))) ltac:(apply le2_add_sx16).
    zs2. zstep. br_cases K4.
    + do 3 zs2. sd_close T n MU WM ARR ltac:(sc_mod HL CND).
    + do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sd_close T n MU WM ARR ltac:(sc_mod HL CND).
Qed.

Lemma sd_iter : forall (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc n : Z) (fcT dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wbt L) m T fcT dlT NT -> 0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  0 <= n <= mc -> nextlen = arr_get dlT n ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  evt psegs (sd_iter_post L s1 t T mc n dlT bdl b prevlen nextlen count mx mn t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (scR2 L T mc mx mn count nextlen (T + 4 * n + 6) prevlen t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b20c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LNB MI LAY RDT RT1 RT2 RNT HL HDL HLEN Rn Enl Rc Rmx Rmn Rpl.
  pose proof (HLEN n ltac:(lia)) as Rcl. rewrite <- Enl in Rcl.
  pose proof (HDL (n + 1) ltac:(lia)) as Rnl'.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (n + 1) ltac:(lia)) as [_ RDl].
  replace (T + 4 * (n + 1) + 2) with (T + 4 * n + 6) in RDl by lia.
  destruct ((count + 1 <? mx) && (nextlen =? arr_get dlT (n + 1))) eqn:CND.
  -
    apply andb_true_iff in CND. destruct CND as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2.
    pose proof (munch_refl (Wbt L) m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
    unfold scR2. zs2. zs2. rewrite (zx16_small (arr_get dlT (n + 1))) by lia. zs2.
    zstep. br_false. zstep. br_true. zs2.
    sd_close T n MU WM ARR ltac:(intros f0; rewrite scan_loop_S; cbv zeta; rewrite !HL; decide_bools; reflexivity).
  -
    unfold scR2. zs2. zs2. rewrite (zx16_small (arr_get dlT (n + 1))) by lia. zs2.
    zstep. br_cases K1; [| zstep; br_cases_s K2; [exfalso; apply andb_false_iff in CND; destruct CND as [C|C]; [apply Z.ltb_ge in C; lia| apply Z.eqb_neq in C; lia]|]].
    all: eapply (sd_upd L s1 t T NT mc n dlT bdl b prevlen nextlen count mx mn); eassumption.
Qed.

Definition sd_loop_post (L : dlay) (s1 : deflate_state) (T mc : Z) (bdl : arr) (R : deflate_state)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists vt0 vt1 vt2 va1 va3 vt4 a7 t3 b' m',
    ms' = MS (scR2 L T mc vt0 vt1 vt2 va1 va3 vt4 t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b2c4) fc None m' (seg_rom psegs)
    /\ munch (Wbt L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39 /\ R = set_bl_tree_fc s1 b'.

Lemma sd_loop : forall (f : nat) (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc : Z) (fcT dlT bdl : arr) (R : deflate_state) (m0 : mem)
    (n : Z) (b : arr) (prevlen nextlen count mx mn : Z)
    (t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wbt L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wbt L) m0 T fcT dlT NT -> 0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  0 <= n <= mc -> nextlen = arr_get dlT n ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  mc + 1 - n <= Z.of_nat (S f) ->
  R = scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc n prevlen nextlen count mx mn ->
  evt psegs (sd_loop_post L s1 T mc bdl R t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m0)
      (MS (scR2 L T mc mx mn count nextlen (T + 4 * n + 6) prevlen t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b20c) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR LNB MI LAY MU WM RDT RT1 RT2 RNT HL HDL HLEN Rn Enl Rc Rmx Rmn Rpl FUEL ER.
  - call (sd_iter L s1 t T NT mc n fcT dlT bdl b prevlen nextlen count mx mn).
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RNT. } 1:{ exact HL. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Rn. } 1:{ exact Enl. }
    1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. }
    match goal with E : forall f : nat, scan_tree_loop (S f) _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite E in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    rewrite scan_loop_0 in ER.
    apply evt_done. unfold sd_loop_post. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER].
  - call (sd_iter L s1 t T NT mc n fcT dlT bdl b prevlen nextlen count mx mn).
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RNT. } 1:{ exact HL. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Rn. } 1:{ exact Enl. }
    1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. }
    match goal with E : forall f : nat, scan_tree_loop (S f) _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite E in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
    + eapply (IH L s1 t T NT mc fcT dlT bdl R m0 (n + 1)); try eassumption; try lia; reflexivity.
    + rewrite scan_loop_out in ER by lia.
      apply evt_done. unfold sd_loop_post. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER].
Qed.
End Z_tr_scan2.

Module Z_tr_scan3.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_scan2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Ltac regs_eq tac :=
  f_equal; unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | (f_equal; tac)]
  | |- _ = _ => reflexivity
  end.

Definition sc_pre1_post (L : dlay) (s : deflate_state) (mc : Z)
    (ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a7 t3 m',
    ms' = MS (scR L (dl_As L + 212) mc (if arr_get (ds_dyn_ltree_dl s) 0 =? 0 then 138 else 7) (if arr_get (ds_dyn_ltree_dl s) 0 =? 0 then 3 else 4) 0
                  (arr_get (ds_dyn_ltree_dl s) 0) (dl_As L + 212 + 4 * 0 + 6) (-1) ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6)
             F (wz 0x1b0d8) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 212, dl_As L + 2504)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 212) (u16s (avct (ds_dyn_ltree_fc s) (arr_set (ds_dyn_ltree_dl s) (mc + 1) (wrap16 65535)) 573)).

Lemma sc_pre1 : forall (L : dlay) (s : deflate_state) (mc : Z) (hB1 hB2 hB3 : list byte)
    (ra sp gp tp t0 t1 t2 s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 212) (u16s (avct (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573)) -> arr_len (ds_dyn_ltree_dl s) = 573 ->
  rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) -> mem_inv psegs m -> dlay_ok L ->
  mc = ds_l_max_code s -> 0 <= mc -> mc + 1 < 573 -> 0 <= arr_get (ds_dyn_ltree_dl s) 0 < 65536 ->
  evt psegs (sc_pre1_post L s mc ra sp gp tp (wz (dl_As L)) s1r s2 s3 (wz (dl_As L + 2047)) s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (dl_As L + 2047)) s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b054) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LND GB MI LAY Emc Rmc Rmc2 Rnl.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. pose proof (avct_zlength (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ltac:(lia)) as LCT.
  unfold dsB_cells in GB. rewrite <- Emc in GB.
  pose proof (u16arr_read psegs m (dl_As L + 212) (avct (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573) (2 * 0 + 1) _ (wa (dl_As L + 212 + 2 * (2 * 0 + 1))) ARR
                (avct_nth_dl _ _ 573 0 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  set (nl := arr_get (ds_dyn_ltree_dl s) 0) in *.
  zs2. zs2. rewrite (zx16_small nl) by lia. zs2. shl_norm. zs2. zs2.
  ct_store_dl ARR (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 (dl_As L + 212) (mc + 1) (wrap16 65535) ltac:(apply le2_wz_mod; vm_compute; reflexivity).
  zstep. br_false.
  zs2. zs2. rewrite ?Z.mod_small by lia. zs2. zstep. br_cases K.
  -
    do 12 zs2.
    replace (0 <? nl) with false by (symmetry; apply Z.ltb_ge; lia). change (bv_swrap 32 (Z.b2z false + 3)) with 3.
    shl_norm. apply evt_done. unfold sc_pre1_post. fold nl. rewrite (proj2 (Z.eqb_eq nl 0) K). do 3 eexists.
    split; [unfold scR; regs_eq ltac:(lia)|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
  - do 13 zs2.
    replace (0 <? nl) with true by (symmetry; apply Z.ltb_lt; lia). change (bv_swrap 32 (Z.b2z true + 3)) with 4.
    shl_norm. apply evt_done. unfold sc_pre1_post. fold nl. rewrite (proj2 (Z.eqb_neq nl 0) K). do 3 eexists.
    split; [unfold scR; regs_eq ltac:(lia)|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
Qed.

Definition sc_pre2_post (L : dlay) (s : deflate_state) (mc : Z)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a7 t3 m',
    ms' = MS (scR2 L (dl_As L + 2504) mc (if arr_get (ds_dyn_dtree_dl s) 0 =? 0 then 138 else 7) (if arr_get (ds_dyn_dtree_dl s) 0 =? 0 then 3 else 4) 0
                   (arr_get (ds_dyn_dtree_dl s) 0) (dl_As L + 2504 + 4 * 0 + 6) (-1) t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6)
             F (wz 0x1b20c) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 2504, dl_As L + 2748)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2504) (u16s (avct (ds_dyn_dtree_fc s) (arr_set (ds_dyn_dtree_dl s) (mc + 1) (wrap16 65535)) 61)).

Lemma sc_pre2 : forall (L : dlay) (s : deflate_state) (mc : Z) (hB1 hB2 hB3 : list byte)
    (ra sp gp tp t0 t1 t2 s1r a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2504) (u16s (avct (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61)) -> arr_len (ds_dyn_dtree_dl s) = 61 ->
  rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) -> mem_inv psegs m -> dlay_ok L ->
  mc = ds_d_max_code s -> 0 <= mc -> mc + 1 < 61 -> 0 <= arr_get (ds_dyn_dtree_dl s) 0 < 65536 ->
  evt psegs (sc_pre2_post L s mc t4 ra sp gp tp (wz (dl_As L)) s1r s2 s3 (wz (dl_As L + 2047)) s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1r (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (dl_As L + 2047)) s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b190) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LND GB MI LAY Emc Rmc Rmc2 Rnl.
  pose proof (munch_refl [(dl_As L + 2504, dl_As L + 2748)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. pose proof (avct_zlength (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61 ltac:(lia)) as LCT.
  unfold dsB_cells in GB. rewrite <- Emc in GB.
  pose proof (u16arr_read psegs m (dl_As L + 2504) (avct (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61) (2 * 0 + 1) _ (wa (dl_As L + 2504 + 2 * (2 * 0 + 1))) ARR
                (avct_nth_dl _ _ 61 0 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  set (nl := arr_get (ds_dyn_dtree_dl s) 0) in *.
  zs2. zs2. shl_norm. zs2. rewrite (zx16_small nl) by lia. zs2. zs2.
  ct_store_dl ARR (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61 (dl_As L + 2504) (mc + 1) (wrap16 65535) ltac:(apply le2_wz_mod; vm_compute; reflexivity).
  zstep. br_false.
  zs2. zs2. rewrite ?Z.mod_small by lia. zs2. zstep. br_cases K.
  -
    do 13 zs2.
    replace (0 <? nl) with false by (symmetry; apply Z.ltb_ge; lia). change (bv_swrap 32 (Z.b2z false + 3)) with 3.
    shl_norm. apply evt_done. unfold sc_pre2_post. fold nl. rewrite (proj2 (Z.eqb_eq nl 0) K). do 3 eexists.
    split; [unfold scR2; regs_eq ltac:(lia)|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
  - do 14 zs2.
    replace (0 <? nl) with true by (symmetry; apply Z.ltb_lt; lia). change (bv_swrap 32 (Z.b2z true + 3)) with 4.
    shl_norm. apply evt_done. unfold sc_pre2_post. fold nl. rewrite (proj2 (Z.eqb_neq nl 0) K). do 3 eexists.
    split; [unfold scR2; regs_eq ltac:(lia)|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
Qed.


Lemma guard_dl_facts : forall (dl : arr) N mc, arr_len dl = N -> 0 <= mc -> mc + 1 < N ->
  (forall i, 0 <= i < N -> 0 <= arr_get dl i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dl i <= 15) ->
  (forall i, 0 <= i < N -> 0 <= arr_get (arr_set dl (mc + 1) (wrap16 65535)) i < 65536)
  /\ (forall i, 0 <= i <= mc -> 0 <= arr_get (arr_set dl (mc + 1) (wrap16 65535)) i <= 15)
  /\ arr_get (arr_set dl (mc + 1) (wrap16 65535)) 0 = arr_get dl 0.
Proof.
  intros dl N mc LN H0 H1 HA HB.
  assert (G : forall i, arr_get (arr_set dl (mc + 1) (wrap16 65535)) i = if mc + 1 =? i then 65535 else arr_get dl i).
  { intros i. rewrite arr_get_set. unfold arr_inb. rewrite LN. destruct (Z.eqb_spec (mc + 1) i); cbn [andb]; [|reflexivity].
    rewrite (proj2 (Z.leb_le 0 (mc + 1))), (proj2 (Z.ltb_lt (mc + 1) N)) by lia. reflexivity. }
  split; [|split].
  - intros i Hi. rewrite G. destruct (mc + 1 =? i); [lia| apply HA; lia].
  - intros i Hi. rewrite G. destruct (Z.eqb_spec (mc + 1) i); [lia| apply HB; lia].
  - rewrite G. destruct (Z.eqb_spec (mc + 1) 0); [lia| reflexivity].
Qed.

Definition tfb_scan1_post (L : dlay) (s : deflate_state)
    (ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists vt0 vt1 vt2 va1 va3 vt4 a7 t3 m',
    ms' = MS (scR L (dl_As L + 212) (ds_l_max_code s) vt0 vt1 vt2 va1 va3 vt4 ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b190) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 212, dl_As L + 2504); (dl_As L + 2748, dl_As L + 2904)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ dlt m' L (scan_tree s TL (ds_l_max_code s)) /\ dbt m' L (scan_tree s TL (ds_l_max_code s)).

Lemma tfb_scan1 : forall (L : dlay) (s : deflate_state) (hB1 hB2 hB3 : list byte)
    (ra sp gp tp t0 t1 t2 s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dlt m L s -> dbt m L s -> rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  arr_len (ds_dyn_ltree_dl s) = 573 -> arr_len (ds_bl_tree_fc s) = 39 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_l_max_code s -> ds_l_max_code s + 1 < 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_dl s) i < 65536) -> (forall i, 0 <= i <= ds_l_max_code s -> 0 <= arr_get (ds_dyn_ltree_dl s) i <= 15) ->
  evt psegs (tfb_scan1_post L s ra sp gp tp (wz (dl_As L)) s1r s2 s3 (wz (dl_As L + 2047)) s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (dl_As L + 2047)) s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b054) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Glt Gbt GB LND LNB MI LAY Rmc1 Rmc2 HDL HLEN.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504); (dl_As L + 2748, dl_As L + 2904)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof LAY as LAY'. lay_open LAY'.
  unfold dlt, u16arr in Glt. unfold dbt, u16arr in Gbt.
  pose proof (avct_zlength (ds_bl_tree_fc s) (ds_bl_tree_dl s) 39 ltac:(lia)) as LCTb.
  remember (ds_l_max_code s) as mc eqn:Emc.
  destruct (guard_dl_facts (ds_dyn_ltree_dl s) 573 mc LND Rmc1 Rmc2 HDL HLEN) as (HDL' & HLEN' & E0).
  call (sc_pre1 L s mc hB1 hB2 hB3).
  1:{ exact Glt. } 1:{ exact LND. } 1:{ exact GB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Emc. } 1:{ exact Rmc1. } 1:{ exact Rmc2. } 1:{ apply HDL. lia. }
  set (nl := arr_get (ds_dyn_ltree_dl s) 0) in *.
  set (dlT := arr_set (ds_dyn_ltree_dl s) (mc + 1) (wrap16 65535)) in *.
  set (s1 := set_Len s TL (mc + 1) 65535).
  pose proof (avct_zlength (ds_dyn_ltree_fc s) dlT 573 ltac:(lia)) as LCTl.
  remember (scan_tree s TL mc) as R eqn:ER.
  destruct (Z.to_nat (mc + 1)) as [|f] eqn:Ef; [lia|].
  assert (ER' : R = scan_tree_loop (S f) (set_bl_tree_fc s1 (ds_bl_tree_fc s)) TL mc 0 (-1) nl 0 (if nl =? 0 then 138 else 7) (if nl =? 0 then 3 else 4)).
  { rewrite ER. unfold scan_tree. change (Len s TL 0) with nl. rewrite Ef. change (set_Len s TL (mc + 1) 65535) with s1.
    change (ds_bl_tree_fc s) with (ds_bl_tree_fc s1). rewrite (sbf_self s1). destruct (nl =? 0); reflexivity. }
  match goal with H : u8arr _ ?mc0 (dl_As L + 212) _ |- evt _ _ (MS _ _ _ _ _ ?mc0 _) =>
    pose proof (ct_readable_rw (Wbt L) mc0 (dl_As L + 212) (ds_dyn_ltree_fc s) dlT 573 573 H ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; lia)) as RDT;
    call (sc_loop f L s1 TL (dl_As L + 212) 573 mc (ds_dyn_ltree_fc s) dlT (ds_bl_tree_dl s) R mc0 0 (ds_bl_tree_fc s) (-1) nl 0 (if nl =? 0 then 138 else 7) (if nl =? 0 then 3 else 4))
  end.
  1:{ eassumption. } 1:{ exact LNB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RDT. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ intros i. reflexivity. } 1:{ exact HDL'. } 1:{ exact HLEN'. } 1:{ lia. } 1:{ subst dlT. rewrite E0. reflexivity. }
  1:{ destruct (nl =? 0); lia. } 1:{ destruct (nl =? 0); auto. } 1:{ destruct (nl =? 0); auto. } 1:{ lia. } 1:{ lia. } 1:{ exact ER'. }
  subst dlT s1. subst mc. apply evt_done. unfold tfb_scan1_post. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  rewrite <- ER. match goal with E : R = set_bl_tree_fc _ _ |- _ => rewrite E end.
  split; [unfold dlt, u16arr; match goal with H : u8arr _ _ (dl_As L + 212) _ |- _ => exact H end
         | unfold dbt, u16arr; match goal with H : u8arr _ _ (dl_As L + 2748) _ |- _ => exact H end].
Qed.

Definition tfb_scan2_post (L : dlay) (s : deflate_state)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists vt0 vt1 vt2 va1 va3 vt4 a7 t3 m',
    ms' = MS (scR2 L (dl_As L + 2504) (ds_d_max_code s) vt0 vt1 vt2 va1 va3 vt4 t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b2c4) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 2504, dl_As L + 2748); (dl_As L + 2748, dl_As L + 2904)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ ddt m' L (scan_tree s TD (ds_d_max_code s)) /\ dbt m' L (scan_tree s TD (ds_d_max_code s)).

Lemma tfb_scan2 : forall (L : dlay) (s : deflate_state) (hB1 hB2 hB3 : list byte)
    (ra sp gp tp t0 t1 t2 s1r a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ddt m L s -> dbt m L s -> rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  arr_len (ds_dyn_dtree_dl s) = 61 -> arr_len (ds_bl_tree_fc s) = 39 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_d_max_code s -> ds_d_max_code s + 1 < 61 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_dl s) i < 65536) -> (forall i, 0 <= i <= ds_d_max_code s -> 0 <= arr_get (ds_dyn_dtree_dl s) i <= 15) ->
  evt psegs (tfb_scan2_post L s t4 ra sp gp tp (wz (dl_As L)) s1r s2 s3 (wz (dl_As L + 2047)) s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1r (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (dl_As L + 2047)) s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b190) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Gdt Gbt GB LND LNB MI LAY Rmc1 Rmc2 HDL HLEN.
  pose proof (munch_refl [(dl_As L + 2504, dl_As L + 2748); (dl_As L + 2748, dl_As L + 2904)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof LAY as LAY'. lay_open LAY'.
  unfold ddt, u16arr in Gdt. unfold dbt, u16arr in Gbt.
  pose proof (avct_zlength (ds_bl_tree_fc s) (ds_bl_tree_dl s) 39 ltac:(lia)) as LCTb.
  remember (ds_d_max_code s) as mc eqn:Emc.
  destruct (guard_dl_facts (ds_dyn_dtree_dl s) 61 mc LND Rmc1 Rmc2 HDL HLEN) as (HDL' & HLEN' & E0).
  call (sc_pre2 L s mc hB1 hB2 hB3).
  1:{ exact Gdt. } 1:{ exact LND. } 1:{ exact GB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Emc. } 1:{ exact Rmc1. } 1:{ exact Rmc2. } 1:{ apply HDL. lia. }
  set (nl := arr_get (ds_dyn_dtree_dl s) 0) in *.
  set (dlT := arr_set (ds_dyn_dtree_dl s) (mc + 1) (wrap16 65535)) in *.
  set (s1 := set_Len s TD (mc + 1) 65535).
  pose proof (avct_zlength (ds_dyn_dtree_fc s) dlT 61 ltac:(lia)) as LCTl.
  remember (scan_tree s TD mc) as R eqn:ER.
  destruct (Z.to_nat (mc + 1)) as [|f] eqn:Ef; [lia|].
  assert (ER' : R = scan_tree_loop (S f) (set_bl_tree_fc s1 (ds_bl_tree_fc s)) TD mc 0 (-1) nl 0 (if nl =? 0 then 138 else 7) (if nl =? 0 then 3 else 4)).
  { rewrite ER. unfold scan_tree. change (Len s TD 0) with nl. rewrite Ef. change (set_Len s TD (mc + 1) 65535) with s1.
    change (ds_bl_tree_fc s) with (ds_bl_tree_fc s1). rewrite (sbf_self s1). destruct (nl =? 0); reflexivity. }
  match goal with H : u8arr _ ?mc0 (dl_As L + 2504) _ |- evt _ _ (MS _ _ _ _ _ ?mc0 _) =>
    pose proof (ct_readable_rw (Wbt L) mc0 (dl_As L + 2504) (ds_dyn_dtree_fc s) dlT 61 61 H ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; lia)) as RDT;
    call (sd_loop f L s1 TD (dl_As L + 2504) 61 mc (ds_dyn_dtree_fc s) dlT (ds_bl_tree_dl s) R mc0 0 (ds_bl_tree_fc s) (-1) nl 0 (if nl =? 0 then 138 else 7) (if nl =? 0 then 3 else 4))
  end.
  1:{ eassumption. } 1:{ exact LNB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RDT. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ intros i. reflexivity. } 1:{ exact HDL'. } 1:{ exact HLEN'. } 1:{ lia. } 1:{ subst dlT. rewrite E0. reflexivity. }
  1:{ destruct (nl =? 0); lia. } 1:{ destruct (nl =? 0); auto. } 1:{ destruct (nl =? 0); auto. } 1:{ lia. } 1:{ lia. } 1:{ exact ER'. }
  subst dlT s1. subst mc. apply evt_done. unfold tfb_scan2_post. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  rewrite <- ER. match goal with E : R = set_bl_tree_fc _ _ |- _ => rewrite E end.
  split; [unfold ddt, u16arr; match goal with H : u8arr _ _ (dl_As L + 2504) _ |- _ => exact H end
         | unfold dbt, u16arr; match goal with H : u8arr _ _ (dl_As L + 2748) _ |- _ => exact H end].
Qed.
End Z_tr_scan3.

Module Z_tr_fbmid.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require FillWinModel FlushBlockModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma mb_search : forall X (f : nat) mb k, mb - 2 <= Z.of_nat f -> 2 <= k <= mb ->
  (forall j, k < j <= mb -> Len X TB (arr_get bl_order_a j) = 0) -> (k = 2 \/ Len X TB (arr_get bl_order_a k) <> 0) ->
  build_bl_tree_loop f X mb = k.
Proof.
  induction f as [|f IH]; intros mb k Hf Hk HZ HK.
  - cbn [build_bl_tree_loop]. lia.
  - cbn [build_bl_tree_loop]. destruct (Z.leb_spec 3 mb) as [C|C]; [|lia].
    destruct (Z.eq_dec k mb) as [->|NE].
    + destruct HK as [->|HK]; [lia|]. rewrite (proj2 (Z.eqb_neq _ _) HK). reflexivity.
    + rewrite (proj2 (Z.eqb_eq _ _) (HZ mb ltac:(lia))). cbn [negb]. apply IH; [lia| lia| intros j Hj; apply HZ; lia| exact HK].
Qed.


Definition tfb_mbs_post (X : deflate_state)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (tfb_mb X)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b3cc) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Ltac mb_done mb ACC K :=
  let E := fresh "E" in
  assert (E : tfb_mb _ = mb) by (unfold tfb_mb; apply mb_search; [lia| lia| exact ACC| right; exact K]);
  apply evt_done; unfold tfb_mbs_post; rewrite E; eexists; split; [reflexivity|]; split; [apply munch_refl|]; split; [apply wmono_refl| assumption].

Lemma tfb_mbsearch : forall (L : dlay) (X : deflate_state)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39)) -> mem_inv psegs m -> dlay_ok L ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X) i < 65536) ->
  evt psegs (tfb_mbs_post X ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b2d0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR MI LAY HDL. lay_open LAY.
  assert (ACC : forall j, 18 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0) by (intros; lia).
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 15 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 15 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 15 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 15 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 15)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 18 ACC K]; clear RD RV.
  assert (ACC18 : forall j, 18 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 18) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC18 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 1 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 1 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 1 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 1 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 1)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 17 ACC K]; clear RD RV.
  assert (ACC17 : forall j, 17 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 17) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC17 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 14 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 14 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 14 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 14 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 14)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 16 ACC K]; clear RD RV.
  assert (ACC16 : forall j, 16 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 16) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC16 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 2 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 2 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 2 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 2 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 2)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 15 ACC K]; clear RD RV.
  assert (ACC15 : forall j, 15 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 15) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC15 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 13 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 13 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 13 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 13 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 13)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 14 ACC K]; clear RD RV.
  assert (ACC14 : forall j, 14 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 14) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC14 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 3 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 3 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 3 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 3 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 3)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 13 ACC K]; clear RD RV.
  assert (ACC13 : forall j, 13 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 13) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC13 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 12 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 12 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 12 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 12 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 12)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 12 ACC K]; clear RD RV.
  assert (ACC12 : forall j, 12 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 12) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC12 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 4 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 4 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 4 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 4 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 4)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 11 ACC K]; clear RD RV.
  assert (ACC11 : forall j, 11 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 11) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC11 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 11 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 11 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 11 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 11 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 11)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 10 ACC K]; clear RD RV.
  assert (ACC10 : forall j, 10 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 10) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC10 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 5 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 5 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 5 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 5 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 5)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 9 ACC K]; clear RD RV.
  assert (ACC9 : forall j, 9 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 9) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC9 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 10 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 10 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 10 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 10 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 10)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 8 ACC K]; clear RD RV.
  assert (ACC8 : forall j, 8 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 8) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC8 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 6 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 6 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 6 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 6 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 6)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 7 ACC K]; clear RD RV.
  assert (ACC7 : forall j, 7 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 7) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC7 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 9 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 9 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 9 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 9 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 9)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 6 ACC K]; clear RD RV.
  assert (ACC6 : forall j, 6 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 6) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC6 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 7 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 7 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 7 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 7 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 7)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 5 ACC K]; clear RD RV.
  assert (ACC5 : forall j, 5 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 5) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC5 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 8 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 8 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 8 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 8 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 8)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 4 ACC K]; clear RD RV.
  assert (ACC4 : forall j, 4 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 4) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC4 into ACC.
  pose proof (u16arr_read psegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 0 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 0 + 1))) ARR (avct_nth_dl _ _ 39 0 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 0 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 0)) by lia. zs2. zs2.
  destruct (Z.eq_dec (arr_get (ds_bl_tree_dl X) 0) 0) as [K|K].
  - rewrite K. change (Z.lxor (Z.b2z (0 <? 1)) 3) with 2.
    assert (E : tfb_mb X = 2) by (unfold tfb_mb; apply mb_search; [lia| lia| intros j Hj; destruct (Z.eq_dec j 3) as [->|]; [exact K| apply ACC; lia]| left; reflexivity]).
    apply evt_done. unfold tfb_mbs_post. rewrite E. eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| assumption].
  - replace (arr_get (ds_bl_tree_dl X) 0 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). change (Z.lxor (Z.b2z false) 3) with 3.
    mb_done 3 ACC K.
Qed.
End Z_tr_fbmid.

Module Z_tr_fb9.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit Z_tr_fbpure.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fbpure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require FlushBlockModel RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition tfb_detect_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b03c) fc None m' (seg_rom psegs)
    /\ munch [(dl_S L + 88, dl_S L + 92)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ dzs m' L (ds_strm (tfb_X0 s)).

Lemma tfb_X0_strm : forall s, 0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN ->
  ds_strm (tfb_X0 s) = cset_data_type (ds_strm s) (detect_data_type s).
Proof.
  intros s Hl Hd. unfold tfb_X0. rewrite (proj2 (Z.ltb_lt _ _) Hl), Hd. reflexivity.
Qed.

Lemma tfb_dd_store : forall (L : dlay) (s : deflate_state) (v : Z) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = v ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) (wz v) a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b038) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev.
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. destruct DZ as (p1 & p2 & p3 & resv & ZS). unfold zs_call_cells, zs_priv_cells in ZS. cbn [app] in ZS.
  unfold tfR. zs2.
  apply evt_done. unfold tfb_detect_post, tfR. do 5 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  rewrite (tfb_X0_strm s Hl Hd), Ev. exists p1, p2, p3, resv. unfold zs_call_cells, zs_priv_cells. cbn [app].
  close_cells ZS.
Qed.

Lemma tfb_dd_bin : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = Z_BINARY ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b034) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev. unfold tfR. zs2.
  eapply (tfb_dd_store L s 0 sp last len bufp); eassumption.
Qed.
Lemma tfb_dd_text : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = Z_TEXT ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b8a8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev. unfold tfR. zs2. zs2.
  eapply (tfb_dd_store L s 1 sp last len bufp); eassumption.
Qed.

Lemma tfb_dd_loop : forall (j : nat) (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN ->
  ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  (Z.of_nat (S j) <= 224) ->
  ((exists k, 256 - Z.of_nat (S j) <= k < 256 /\ Freq s TL k <> 0) -> detect_data_type s = Z_TEXT) ->
  ((forall k, 256 - Z.of_nat (S j) <= k < 256 -> Freq s TL k = 0) -> detect_data_type s = Z_BINARY) ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 (wz (dl_As L + 212 + 4 * (256 - Z.of_nat (S j)))) (wz (Z.of_nat (S j))) a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b8b8) fc None m (seg_rom psegs)).
Proof.
  induction j as [|j IH]; intros until m; intros DZ MI LAY Hl Hd RDT RF Rj HT HB.
  all: pose proof (dlay_ranges _ LAY) as (Rs & _).
  all: match goal with |- evt _ _ (MS (tfR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?jj) _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
         destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (256 - jj) ltac:(lia)) as [RDf _]; pose proof (RF (256 - jj) ltac:(lia)) as Rf end.
  all: unfold tfR; zs2; rewrite zx16_small by lia; zstep; br_cases_s K.
  - eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply HT. exists (256 - Z.of_nat 1). split; [lia| exact K].
  - rewrite K. zs2. zs2. zstep. br_false. zs2.
    eapply (tfb_dd_store L s 0 sp last len bufp); try eassumption. apply HB. intros k Hk. replace k with (256 - Z.of_nat 1) by lia. exact K.
  - eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply HT. exists (256 - Z.of_nat (S (S j))). split; [lia| exact K].
  - rewrite K. zs2. zs2. zstep. br_true.
    replace (Z.of_nat (S (S j)) + -1) with (Z.of_nat (S j)) by lia.
    replace (dl_As L + 212 + 4 * (256 - Z.of_nat (S (S j))) + 4) with (dl_As L + 212 + 4 * (256 - Z.of_nat (S j))) by lia.
    eapply (IH L s sp last len bufp); try eassumption; try lia.
    + intros (k & Hk & Hf). apply HT. exists k. split; [lia| exact Hf].
    + intros H. apply HB. intros k Hk. destruct (Z.eq_dec k (256 - Z.of_nat (S (S j)))) as [->|NE]; [exact K| apply H; lia].
Qed.

Lemma tfb_detect : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dsA m L s -> dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> - 2^31 <= cs_data_type (ds_strm s) < 2^31 ->
  ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1af6c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros GA DZ MI LAY Hl Rdt RDT RF.
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & _ & RS).
  destruct GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA). unfold dsA_cells in GA.
  pose proof DZ as (p1 & p2 & p3 & resv & ZS). unfold zs_call_cells, zs_priv_cells in ZS. cbn [app] in ZS.
  unfold tfR. zs2. zs2. zs2. clear GA ZS.
  zstep. br_cases_s KDT.
  {
    apply evt_done. unfold tfb_detect_post, tfR. do 5 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold tfb_X0. unfold Z_UNKNOWN. rewrite (proj2 (Z.eqb_neq _ _) KDT), Bool.andb_false_r. exact DZ. }
  assert (Hd : cs_data_type (ds_strm s) = Z_UNKNOWN) by exact KDT.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 0 ltac:(lia)) as [RDb0 _]. replace (dl_As L + 212 + 4 * 0) with (dl_As L + 212) in RDb0 by lia.
  pose proof (RF 0 ltac:(lia)) as Rb0.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K0.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 0); [lia| reflexivity| exact K0]. }
  clear RDb0 Rb0.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 1 ltac:(lia)) as [RDb1 _]. replace (dl_As L + 212 + 4 * 1) with (dl_As L + 216) in RDb1 by lia.
  pose proof (RF 1 ltac:(lia)) as Rb1.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K1.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 1); [lia| reflexivity| exact K1]. }
  clear RDb1 Rb1.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 2 ltac:(lia)) as [RDb2 _]. replace (dl_As L + 212 + 4 * 2) with (dl_As L + 220) in RDb2 by lia.
  pose proof (RF 2 ltac:(lia)) as Rb2.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K2.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 2); [lia| reflexivity| exact K2]. }
  clear RDb2 Rb2.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 3 ltac:(lia)) as [RDb3 _]. replace (dl_As L + 212 + 4 * 3) with (dl_As L + 224) in RDb3 by lia.
  pose proof (RF 3 ltac:(lia)) as Rb3.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K3.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 3); [lia| reflexivity| exact K3]. }
  clear RDb3 Rb3.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 4 ltac:(lia)) as [RDb4 _]. replace (dl_As L + 212 + 4 * 4) with (dl_As L + 228) in RDb4 by lia.
  pose proof (RF 4 ltac:(lia)) as Rb4.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K4.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 4); [lia| reflexivity| exact K4]. }
  clear RDb4 Rb4.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 5 ltac:(lia)) as [RDb5 _]. replace (dl_As L + 212 + 4 * 5) with (dl_As L + 232) in RDb5 by lia.
  pose proof (RF 5 ltac:(lia)) as Rb5.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K5.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 5); [lia| reflexivity| exact K5]. }
  clear RDb5 Rb5.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 6 ltac:(lia)) as [RDb6 _]. replace (dl_As L + 212 + 4 * 6) with (dl_As L + 236) in RDb6 by lia.
  pose proof (RF 6 ltac:(lia)) as Rb6.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K6.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 6); [lia| reflexivity| exact K6]. }
  clear RDb6 Rb6.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 14 ltac:(lia)) as [RDb14 _]. replace (dl_As L + 212 + 4 * 14) with (dl_As L + 268) in RDb14 by lia.
  pose proof (RF 14 ltac:(lia)) as Rb14.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K14.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 14); [lia| reflexivity| exact K14]. }
  clear RDb14 Rb14.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 15 ltac:(lia)) as [RDb15 _]. replace (dl_As L + 212 + 4 * 15) with (dl_As L + 272) in RDb15 by lia.
  pose proof (RF 15 ltac:(lia)) as Rb15.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K15.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 15); [lia| reflexivity| exact K15]. }
  clear RDb15 Rb15.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 16 ltac:(lia)) as [RDb16 _]. replace (dl_As L + 212 + 4 * 16) with (dl_As L + 276) in RDb16 by lia.
  pose proof (RF 16 ltac:(lia)) as Rb16.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K16.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 16); [lia| reflexivity| exact K16]. }
  clear RDb16 Rb16.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 17 ltac:(lia)) as [RDb17 _]. replace (dl_As L + 212 + 4 * 17) with (dl_As L + 280) in RDb17 by lia.
  pose proof (RF 17 ltac:(lia)) as Rb17.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K17.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 17); [lia| reflexivity| exact K17]. }
  clear RDb17 Rb17.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 18 ltac:(lia)) as [RDb18 _]. replace (dl_As L + 212 + 4 * 18) with (dl_As L + 284) in RDb18 by lia.
  pose proof (RF 18 ltac:(lia)) as Rb18.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K18.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 18); [lia| reflexivity| exact K18]. }
  clear RDb18 Rb18.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 19 ltac:(lia)) as [RDb19 _]. replace (dl_As L + 212 + 4 * 19) with (dl_As L + 288) in RDb19 by lia.
  pose proof (RF 19 ltac:(lia)) as Rb19.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K19.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 19); [lia| reflexivity| exact K19]. }
  clear RDb19 Rb19.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 20 ltac:(lia)) as [RDb20 _]. replace (dl_As L + 212 + 4 * 20) with (dl_As L + 292) in RDb20 by lia.
  pose proof (RF 20 ltac:(lia)) as Rb20.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K20.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 20); [lia| reflexivity| exact K20]. }
  clear RDb20 Rb20.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 21 ltac:(lia)) as [RDb21 _]. replace (dl_As L + 212 + 4 * 21) with (dl_As L + 296) in RDb21 by lia.
  pose proof (RF 21 ltac:(lia)) as Rb21.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K21.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 21); [lia| reflexivity| exact K21]. }
  clear RDb21 Rb21.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 22 ltac:(lia)) as [RDb22 _]. replace (dl_As L + 212 + 4 * 22) with (dl_As L + 300) in RDb22 by lia.
  pose proof (RF 22 ltac:(lia)) as Rb22.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K22.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 22); [lia| reflexivity| exact K22]. }
  clear RDb22 Rb22.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 23 ltac:(lia)) as [RDb23 _]. replace (dl_As L + 212 + 4 * 23) with (dl_As L + 304) in RDb23 by lia.
  pose proof (RF 23 ltac:(lia)) as Rb23.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K23.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 23); [lia| reflexivity| exact K23]. }
  clear RDb23 Rb23.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 24 ltac:(lia)) as [RDb24 _]. replace (dl_As L + 212 + 4 * 24) with (dl_As L + 308) in RDb24 by lia.
  pose proof (RF 24 ltac:(lia)) as Rb24.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K24.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 24); [lia| reflexivity| exact K24]. }
  clear RDb24 Rb24.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 25 ltac:(lia)) as [RDb25 _]. replace (dl_As L + 212 + 4 * 25) with (dl_As L + 312) in RDb25 by lia.
  pose proof (RF 25 ltac:(lia)) as Rb25.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K25.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 25); [lia| reflexivity| exact K25]. }
  clear RDb25 Rb25.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 28 ltac:(lia)) as [RDb28 _]. replace (dl_As L + 212 + 4 * 28) with (dl_As L + 324) in RDb28 by lia.
  pose proof (RF 28 ltac:(lia)) as Rb28.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K28.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 28); [lia| reflexivity| exact K28]. }
  clear RDb28 Rb28.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 29 ltac:(lia)) as [RDb29 _]. replace (dl_As L + 212 + 4 * 29) with (dl_As L + 328) in RDb29 by lia.
  pose proof (RF 29 ltac:(lia)) as Rb29.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K29.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 29); [lia| reflexivity| exact K29]. }
  clear RDb29 Rb29.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 30 ltac:(lia)) as [RDb30 _]. replace (dl_As L + 212 + 4 * 30) with (dl_As L + 332) in RDb30 by lia.
  pose proof (RF 30 ltac:(lia)) as Rb30.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K30.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 30); [lia| reflexivity| exact K30]. }
  clear RDb30 Rb30.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 31 ltac:(lia)) as [RDb31 _]. replace (dl_As L + 212 + 4 * 31) with (dl_As L + 336) in RDb31 by lia.
  pose proof (RF 31 ltac:(lia)) as Rb31.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K31.
  2:{ eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 31); [lia| reflexivity| exact K31]. }
  clear RDb31 Rb31.
  assert (H0 : forall k, 0 <= k <= 31 -> Z.testbit DD_MASK k = true -> Freq s TL k = 0).
  { intros k Hk Hb. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    repeat (destruct C as [C|C]; [subst k; first [assumption | discriminate Hb]|]). subst k. first [assumption | discriminate Hb]. }
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 9 ltac:(lia)) as [RDw9 _]. replace (dl_As L + 212 + 4 * 9) with (dl_As L + 248) in RDw9 by lia.
  pose proof (RF 9 ltac:(lia)) as Rw9.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s W9.
  { eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply (ddt_text1 s H0). left. exact W9. }
  clear RDw9 Rw9.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 10 ltac:(lia)) as [RDw10 _]. replace (dl_As L + 212 + 4 * 10) with (dl_As L + 252) in RDw10 by lia.
  pose proof (RF 10 ltac:(lia)) as Rw10.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s W10.
  { eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply (ddt_text1 s H0). right; left. exact W10. }
  clear RDw10 Rw10.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 13 ltac:(lia)) as [RDw13 _]. replace (dl_As L + 212 + 4 * 13) with (dl_As L + 264) in RDw13 by lia.
  pose proof (RF 13 ltac:(lia)) as Rw13.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s W13.
  2:{ eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply (ddt_text1 s H0). right; right. exact W13. }
  clear RDw13 Rw13.
  pose proof (ddt_rest s H0 W9 W10 W13) as ER.
  zs2. zs2.
  replace (wz (dl_As L + 340)) with (wz (dl_As L + 212 + 4 * (256 - Z.of_nat 224))) by (f_equal; lia).
  change (wz 224) with (wz (Z.of_nat 224)).
  eapply (tfb_dd_loop 223 L s sp last len bufp); try eassumption; try lia.
  - intros HE. rewrite ER, (dl2_some 224 s 32); [reflexivity| | lia]. destruct HE as (k & Hk & Hf). exists k. split; [lia| exact Hf].
  - intros HZ. rewrite ER, (dl2_none 224 s 32); [reflexivity|]. intros k Hk. apply HZ. lia.
Qed.
End Z_tr_fb9.

Module Z_tr_fb10.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fbpure.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_scan3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fbmid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fbpure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb8 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require GenBitlenModel FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.ScanModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_SL_range : forall X, 0 <= tfb_SL X < 2^64.
Proof.
  intros X. unfold tfb_SL. pose proof (wrap64_range (ds_static_len X + 3 + 7)) as R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma tfb_OL_range : forall X, 0 <= tfb_OL X < 2^64.
Proof.
  intros X. unfold tfb_OL. cbv zeta. destruct (_ || _); [apply tfb_SL_range|].
  pose proof (wrap64_range (ds_opt_len X + 3 + 7)) as R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma tfb_branch_eq : forall X6 buf len,
  tfb_branch X6 buf len = (if (wrap64 (len + 4) <=? tfb_OL X6) && is_some buf then 2 else if tfb_SL X6 =? tfb_OL X6 then 0 else 1).
Proof. intros. reflexivity. Qed.

Lemma relro_tfW : forall L lo (sp : word) m0 m, relro_clean m0 -> munch (tfW L lo sp) m0 m -> dlay_ok L -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> relro_clean m.
Proof.
  intros L lo sp m0 m RC MU LAY BEL LE. eapply relro_clean_munch; [exact RC| exact MU|].
  pose proof (lo_s _ LAY) as Bs. pose proof (lo_b _ LAY) as Bb. unfold blk_ok in Bs, Bb. unfold dlay_below in BEL. unfold RELRO_LO, RELRO_HI.
  cbn [disjoint_from]. lia.
Qed.

Lemma DST_scanL : forall m L X mc X',
  X' = scan_tree X TL mc ->
  dsA m L X -> dsB m L X -> dsC m L X -> dsD m L X -> ddt m L X -> dblc m L X -> dheap m L X -> ddep m L X ->
  dwin m L X -> dprev m L X -> dhead m L X -> dpend m L X -> dlens X -> dlay_ok L ->
  dlt m L X' -> dbt m L X' -> DST m L X'.
Proof.
  intros m L X mc X' E GA GB GC GD Gdt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY Glt Gbt.
  destruct (scan_tree_flat X TL mc) as (b' & EF & Lb). rewrite <- E in EF. clear E.
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
  constructor; [rewrite EF; exact GA| rewrite EF; exact GB| rewrite EF; exact GC| rewrite EF; exact GD| exact Glt| rewrite EF; exact Gdt| exact Gbt| rewrite EF; exact Gblc
    | rewrite EF; exact Gheap| rewrite EF; exact Gdep| rewrite EF; exact Gwin| rewrite EF; exact Gprev| rewrite EF; exact Ghead| rewrite EF; exact Gpend| | exact LAY].
  rewrite EF; constructor; unfold set_Len, set_Dad, set_tree_dl, tree_dl; dsred; rewrite ?arr_len_set; first [assumption | lia].
Qed.
Lemma DST_scanD : forall m L X mc X',
  X' = scan_tree X TD mc ->
  dsA m L X -> dsB m L X -> dsC m L X -> dsD m L X -> dlt m L X -> dblc m L X -> dheap m L X -> ddep m L X ->
  dwin m L X -> dprev m L X -> dhead m L X -> dpend m L X -> dlens X -> dlay_ok L ->
  ddt m L X' -> dbt m L X' -> DST m L X'.
Proof.
  intros m L X mc X' E GA GB GC GD Glt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY Gdt Gbt.
  destruct (scan_tree_flat X TD mc) as (b' & EF & Lb). rewrite <- E in EF. clear E.
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
  constructor; [rewrite EF; exact GA| rewrite EF; exact GB| rewrite EF; exact GC| rewrite EF; exact GD| rewrite EF; exact Glt| exact Gdt| exact Gbt| rewrite EF; exact Gblc
    | rewrite EF; exact Gheap| rewrite EF; exact Gdep| rewrite EF; exact Gwin| rewrite EF; exact Gprev| rewrite EF; exact Ghead| rewrite EF; exact Gpend| | exact LAY].
  rewrite EF; constructor; unfold set_Len, set_Dad, set_tree_dl, tree_dl; dsred; rewrite ?arr_len_set; first [assumption | lia].
Qed.

Definition hi_body (PBL : Z) (X0 X1 X2 X3 X4 X5 X6 : deflate_state) (mb d : Z) (buf : option Z) (len last : Z) : Prop :=
  bt_safe X0 TL /\ bt_safe X1 TD
  /\ (0 <= ds_l_max_code X2 /\ ds_l_max_code X2 + 1 < 573) /\ (forall i, 0 <= i <= ds_l_max_code X2 -> 0 <= Len X2 TL i <= 15)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X2 TL) i < 65536)
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X2) i < 65536)
  /\ (0 <= ds_d_max_code X3 /\ ds_d_max_code X3 + 1 < 61) /\ (forall i, 0 <= i <= ds_d_max_code X3 -> 0 <= Len X3 TD i <= 15)
  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X3 TD) i < 65536)
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X3) i < 65536)
  /\ bt_safe X4 TB
  /\ ((forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 16)
      /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 65536))
  /\ 0 <= ds_opt_len X5 < 2 ^ 63 /\ 0 <= ds_static_len X5 < 2 ^ 63 /\ 0 <= ds_strategy X5 <= 4
  /\ match d with
     | 0 => RefFlushBlk13.stat_ok PBL last X6
     | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok PBL last X6 mb
     | _ => RefFlushBlk13.sto_ok PBL X6 buf len last
     end.

Section WithBuildTree.
Hypothesis BT : build_tree_stmt.

Lemma tfb_hi2 : forall (L : dlay) (X4 X5 X6 Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len mb d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X4 -> dzs m L c -> ds_strm X4 = c -> mem_inv psegs m -> relro_clean m0 ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe X4 TB -> X5 = build_tree X4 TB -> mb = tfb_mb X5 -> X6 = tfb_X6 X5 mb -> d = tfb_branch X6 buf len ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 65536) ->
  0 <= ds_opt_len X5 < 2^63 -> 0 <= ds_static_len X5 < 2^63 -> 0 <= ds_strategy X5 <= 4 ->
  BINV 65536 X6 ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X6 | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok 65536 last X6 mb | _ => RefFlushBlk13.sto_ok 65536 X6 buf len last end ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X6 mb buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tfb_emit d X6 mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b2c4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI RC MU WM FR STK LO AL BEL BTS E5 Emb E6 Ed RBd Rol Rsl Rst BI6 SAFE POK BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO.
  pose proof BEL as BEL0. below_open BEL0.
  assert (LAY : dlay_ok L) by (destruct ST; assumption).
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  assert (Rmb : 0 <= mb <= 18) by (rewrite Emb; unfold tfb_mb; pose proof (build_bl_tree_loop_range 17 X5 18 ltac:(lia)); lia).
  unfold tfR. do 3 zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl psegs m1) as WMz.
  call (BT L X4 TB lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ eapply relro_tfW; try eassumption; lia. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_BT_STACK. lia. }
  1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. } 1:{ exact BTS. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST. rewrite <- E5 in *. rewrite ESP in *. name_mem m2.
  match goal with H : DST m2 L X5 |- _ => destruct H as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _] end.
  pose proof Gbt as Gbt'. unfold dbt, u16arr in Gbt'.
  pose proof (munch_refl [] m2) as MUm. pose proof (wmono_refl psegs m2) as WMm.
  call (tfb_mbsearch L X5).
  1:{ exact Gbt'. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact RBd. }
  rewrite <- Emb. clear Gbt'. tr_groups MUm WMm. clear MUm WMm. name_mem m3.
  pose proof (munch_refl [(dl_As L + 5912, dl_As L + 5920)] m3) as MUo. pose proof (wmono_refl psegs m3) as WMo.
  call (tfb_optlen L X5 sp last len (buf_ptr L buf) mb).
  1:{ exact GA. } 1:{ exact GD. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact Rol. } 1:{ exact Rsl. } 1:{ exact Rst. } 1:{ exact Rmb. }
  clear GD. tr_groups MUo WMo. clear MUo WMo. rewrite <- E6 in *. name_mem m4.
  assert (ST6 : DST m4 L X6).
  { rewrite E6 in *. constructor; [exact GA| exact GB| exact GC| assumption| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]. constructor; assumption. }
  clear GA GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  eapply (tfb_emit_all L X6 Rfin c buf last len mb (tfb_SL X6) (tfb_OL X6) d lo m0);
    [exact ST6| exact DZ| | eassumption| exact MU| exact WM| exact FR| eassumption| unfold Z_TRFB_STACK; lia| exact BEL| exact BI6| exact BOK| exact Rlen| exact Rl| exact Rmb
    | apply tfb_SL_range| apply tfb_OL_range| rewrite Ed; apply tfb_branch_eq| exact SAFE| exact POK| exact ER].
  rewrite E6, E5. change (ds_strm (tfb_X6 (build_tree X4 TB) mb)) with (ds_strm (build_tree X4 TB)). rewrite (k_build_tree _ _ _ keeps_strm). exact ESTRM.
Qed.

Lemma tfb_hi1 : forall (L : dlay) (s X0 X1 X2 X3 X4 X5 X6 Rfin : deflate_state) (buf : option Z) (last len mb d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> dzs m L (ds_strm s) -> mem_inv psegs m -> relro_clean m0 ->
  munch (tfW L lo sp) m0 m -> wmono psegs m0 m ->
  rw_cells psegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk psegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  0 < ds_level s -> - 2^31 <= cs_data_type (ds_strm s) < 2^31 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  X0 = tfb_X0 s -> X1 = build_tree X0 TL -> X2 = build_tree X1 TD -> X3 = scan_tree X2 TL (ds_l_max_code X2) -> X4 = scan_tree X3 TD (ds_d_max_code X3) ->
  X5 = build_tree X4 TB -> mb = tfb_mb X5 -> X6 = tfb_X6 X5 mb -> d = tfb_branch X6 buf len ->
  hi_body 65536 X0 X1 X2 X3 X4 X5 X6 mb d buf len last -> BINV 65536 X6 ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X6 mb buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tfb_emit d X6 mb buf len last) ->
  evt psegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (tfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1af6c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST DZ MI RC MU WM FR STK LO AL BEL Hlev Rdt RF E0 E1 E2 E3 E4 E5 Emb E6 Ed HI BI6 POK BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO. unfold tf_frame in FR. pose proof BEL as BEL0. below_open BEL0.
  assert (LAY : dlay_ok L) by (destruct ST; assumption).
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  destruct HI as (BTS0 & BTS1 & (Rlm0 & Rlm1) & RLl & RLn & _ & (Rdm0 & Rdm1) & RDl & RDn & _ & BTS4 & (_ & RBd) & Rol & Rsl & Rst & SAFE).
  assert (ES4 : ds_strm X4 = ds_strm X0).
  { rewrite E4, (k_scan_tree _ _ _ keeps_strm), E3, (k_scan_tree _ _ _ keeps_strm), E2, (k_build_tree _ _ _ keeps_strm), E1, (k_build_tree _ _ _ keeps_strm). reflexivity. }
  pose proof (lo_Ss _ LAY) as SEPSs. unfold apart in SEPSs. pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & Rb & RS).
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MUd. pose proof (wmono_refl psegs m) as WMd.
  pose proof ST as ST'. destruct ST' as [GA _ _ _ Glt _ _ _ _ _ _ _ _ _ _ _].
  assert (RDT : ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573)
    by (eapply ct_readable_rw; [exact Glt| lia| lia| cbn [disjoint_from]; lia]).
  call (tfb_detect L s sp last len (buf_ptr L buf)).
  1:{ exact GA. } 1:{ exact DZ. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Hlev. } 1:{ exact Rdt. } 1:{ exact RDT. } 1:{ exact RF. }
  clear GA Glt RDT DZ. rewrite <- E0 in *. name_mem m1.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _].
  tr_groups MUd WMd. clear MUd WMd.
  assert (ST0 : DST m1 L X0).
  { rewrite E0. unfold tfb_X0. destruct (_ && _);
      (constructor; [exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY]);
      destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]; constructor; assumption. }
  clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS.
  unfold tfR. do 3 zs2. name_mem m2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
  call (BT L X0 TL lo).
  1:{ exact ST0. } 1:{ eassumption. } 1:{ eapply relro_tfW; try eassumption; unfold Z_TRFB_STACK in LO; lia. } 1:{ rewrite ESP. exact STK. }
  1:{ rewrite ESP. unfold Z_BT_STACK, Z_TRFB_STACK in *. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BTS0. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST0. rewrite <- E1 in *. rewrite ESP in *. name_mem m3.
  do 3 zs2. name_mem m4.
  pose proof (munch_refl (tfWz L lo sp) m4) as MUz. pose proof (wmono_refl psegs m4) as WMz.
  call (BT L X1 TD lo).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eapply relro_tfW; try eassumption; unfold Z_TRFB_STACK in LO; lia. } 1:{ rewrite ESP. eassumption. }
  1:{ rewrite ESP. unfold Z_BT_STACK, Z_TRFB_STACK in *. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BTS1. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite <- E2 in *. rewrite ESP in *. name_mem m5.
  match goal with H : DST m5 L X2 |- _ => destruct H as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _] end.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504); (dl_As L + 2748, dl_As L + 2904)] m5) as MUs. pose proof (wmono_refl psegs m5) as WMs.
  pose proof GB as (hB1 & hB2 & hB3 & GBr).
  call (tfb_scan1 L X2 hB1 hB2 hB3).
  1:{ exact Glt. } 1:{ exact Gbt. } 1:{ exact GBr. } 1:{ apply (ln_ltd _ LENS). } 1:{ apply (ln_btf _ LENS). } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact Rlm0. } 1:{ exact Rlm1. } 1:{ exact RLn. } 1:{ exact RLl. }
  clear Glt Gbt GBr. tr_groups MUs WMs. clear MUs WMs. rewrite <- E3 in *. name_mem m6.
  match goal with HL : dlt m6 L X3, HB : dbt m6 L X3 |- _ =>
    pose proof (DST_scanL m6 L X2 (ds_l_max_code X2) X3 E3 GA GB GC GD Gdt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY HL HB) as ST3; clear HL HB end.
  clear GA GB GC GD Gdt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS.
  match goal with H : DST m6 L X3 |- _ => destruct H as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _] end.
  pose proof (munch_refl [(dl_As L + 2504, dl_As L + 2748); (dl_As L + 2748, dl_As L + 2904)] m6) as MUs. pose proof (wmono_refl psegs m6) as WMs.
  pose proof GB as (hC1 & hC2 & hC3 & GBr).
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1.scR.
  call (tfb_scan2 L X3 hC1 hC2 hC3).
  1:{ exact Gdt. } 1:{ exact Gbt. } 1:{ exact GBr. } 1:{ apply (ln_dtd _ LENS). } 1:{ apply (ln_btf _ LENS). } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact Rdm0. } 1:{ exact Rdm1. } 1:{ exact RDn. } 1:{ exact RDl. }
  clear Gdt Gbt GBr. tr_groups MUs WMs. clear MUs WMs. rewrite <- E4 in *. name_mem m7.
  match goal with HD : ddt m7 L X4, HB : dbt m7 L X4 |- _ =>
    pose proof (DST_scanD m7 L X3 (ds_d_max_code X3) X4 E4 GA GB GC GD Glt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY HD HB) as ST4; clear HD HB end.
  clear GA GB GC GD Glt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS.
  unfold Z_tr_scan2.scR2.
  match goal with HZ : dzs m7 L (ds_strm X0) |- _ =>
    eapply (tfb_hi2 L X4 X5 X6 Rfin (ds_strm X0) buf last len mb d lo m0);
    [exact ST4| exact HZ| exact ES4| eassumption| exact RC| exact MU| exact WM| exact FR| eassumption| unfold Z_TRFB_STACK; lia| exact AL| exact BEL
    | exact BTS4| exact E5| exact Emb| exact E6| exact Ed| exact RBd| exact Rol| exact Rsl| exact Rst| exact BI6| exact SAFE| exact POK| exact BOK| exact Rlen| exact Rl| exact ER] end.
Qed.

End WithBuildTree.
End Z_tr_fb10.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb8 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11.Z_tr_fb10.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel GenBitlenModel FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_pre_hi : forall s buf len last, 0 < ds_level s ->
  exists X0 X1 X2 X3 X4 X5 X6 mb d,
    X0 = tfb_X0 s /\ X1 = build_tree X0 TL /\ X2 = build_tree X1 TD /\ X3 = scan_tree X2 TL (ds_l_max_code X2) /\ X4 = scan_tree X3 TD (ds_d_max_code X3)
    /\ X5 = build_tree X4 TB /\ mb = tfb_mb X5 /\ X6 = tfb_X6 X5 mb /\ d = tfb_branch X6 buf len
    /\ tfb_pre s buf len last = tfb_emit d X6 mb buf len last
    /\ (RefFlushBlk13.hi_ok 65536 s buf len last -> hi_body 65536 X0 X1 X2 X3 X4 X5 X6 mb d buf len last)
    /\ bits4 X6 = bits4 s.
Proof.
  intros s buf len last Hl. do 9 eexists.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split].
  - unfold tfb_pre. rewrite (proj2 (Z.ltb_lt _ _) Hl). reflexivity.
  - intros H. exact H.
  - exact (RefFlushBlk13.bits4_X6' s).
Qed.

Section WithBuildTree.
Hypothesis BT : build_tree_stmt.

Lemma tr_flush_block_spec : tr_flush_block_stmt.
Proof.
  unfold tr_flush_block_stmt. intros until m. intros DR MI RC STK LO AL BEL BI FBS BOK Rlen Rl -> -> -> ->.
  rewrite tfb_post_gen_eq, tr_flush_block_eq.
  destruct DR as [DZ ST]. unfold Z_TR_FLUSH_BLOCK.
  pose proof BEL as BEL0. below_open BEL0.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY].
  unfold RefFlushBlk13.fb_safe in FBS. cbv zeta in FBS. rewrite (ln_pend _ LENS) in FBS. destruct FBS as (Rlev & Rdt & _ & RF & POK & HILO).
  pose proof (munch_refl (tfW L lo sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl psegs m) as WMs.
  pose proof (dlay_ranges _ LAY) as (Rs & _).
  assert (LO' : lo <= bv_unsigned sp - 512) by exact LO.
  carve_frame 64%nat STK.
  do 9 zstep.
  tr_groups MUs WMs. clear MUs WMs. name_mem m1.
  pose proof GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA'). unfold dsA_cells in GA'.
  do 10 zs2. clear GA'.
  assert (ST : DST m1 L s) by (constructor; assumption).
  clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  zstep. br_cases K.
  -
    rewrite (proj2 (Z.ltb_ge _ _)) in HILO by lia. unfold tfb_pre in POK |- *. rewrite (proj2 (Z.ltb_ge 0 (ds_level s))) in POK |- * by lia.
    do 4 zs2.
    replace (wz (len + 5)) with (wz (wrap64 (len + 5))) by (apply Z_to_bv_eqm; rewrite wrap64_mod, Z.mod_mod by lia; reflexivity).
    eapply (tfb_emit_all L s _ (ds_strm s) buf last len 0 (wrap64 (len + 5)) (wrap64 (len + 5))
              (if (wrap64 (len + 4) <=? wrap64 (len + 5)) && is_some buf then 2 else 0) lo m);
      [exact ST| exact DZ| reflexivity| eassumption| exact MU| exact WM| exact FR| exact STK| exact LO| exact BEL| exact BI| exact BOK| exact Rlen| exact Rl| lia
      | apply wrap64_range| apply wrap64_range| rewrite Z.eqb_refl; reflexivity| | exact POK| reflexivity].
    unfold RefFlushBlk13.lo_ok in HILO. destruct buf as [off|]; cbn [is_some].
    + destruct BOK as [Ro1 Ro2]. rewrite !wrap64_id by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb]. exact HILO.
    + rewrite Bool.andb_false_r. exact HILO.
  -
    assert (Hlev : 0 < ds_level s) by lia.
    rewrite (proj2 (Z.ltb_lt _ _) Hlev) in HILO.
    destruct (tfb_pre_hi s buf len last Hlev) as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & mb & d & E0 & E1 & E2 & E3 & E4 & E5 & Emb & E6 & Ed & EPRE & HIB & B6).
    rewrite EPRE in POK |- *.
    eapply (tfb_hi1 BT L s X0 X1 X2 X3 X4 X5 X6 _ buf last len mb d lo m);
      [exact ST| exact DZ| eassumption| exact RC| exact MU| exact WM| exact FR| exact STK| exact LO| exact AL| exact BEL| exact Hlev| exact Rdt| exact RF
      | exact E0| exact E1| exact E2| exact E3| exact E4| exact E5| exact Emb| exact E6| exact Ed| apply HIB; exact HILO| eapply BINV_bits4; [exact B6| exact BI]
      | exact POK| exact BOK| exact Rlen| exact Rl| reflexivity].
Qed.

End WithBuildTree.
