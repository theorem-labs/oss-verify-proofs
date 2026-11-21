(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_windup.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma lenb3w : forall len, 0 <= len ->
  bv_unsigned (wz (bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lxor len 65535)) 8))) mod 2^8 = wrap8 (Z.shiftr (wrap16 (wrap16 (Z.lnot len))) 8) mod 2^8.
Proof.
  intros len H.
  assert (R1 : 0 <= bv_wrap 32 (Z.lxor len 65535) < 2^32) by (unfold bv_wrap; apply Z.mod_pos_bound; reflexivity).
  assert (R : 0 <= Z.shiftr (bv_wrap 32 (Z.lxor len 65535)) 8 < 2^24).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite Z_dkit.bv_swrap32_id by lia.
  rewrite lo8_unsigned_wz. unfold bv_wrap. change (bv_modulus 32) with (2^32). bits8.
Qed.

Definition tsb_send_post (L : dlay) (s : deflate_state) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 wbb m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (dl_As L + 5936)) a1 a2 a3 a4 a5 a6 a7 s2 (wz 65535) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1bea0) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma tsb_send : forall (L : dlay) (s : deflate_state) (last : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - 3 < BV -> PD + 2 <= 65536) -> 0 <= last <= 1 ->
  evt usegs (tsb_send_post L s (sbF_PB PB PD BB BV last 3) (sbF_PD PD BV 3) (sbF_BB BB BV last 3) (sbF_BV BV 3)
                ra sp gp tp t0 t1 t2 s0 (wz (dl_As L)) a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (wz (dl_As L)) a0 a1 a2 (wz last) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1bda0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY RBV RPD ROOM RL.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  do 3 zstep. zs2. do 3 zstep.
  zstep. br_cases K.
  -
    zstep. gF.
    zs. zs. zs.
      sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zs2.
      apply evt_done. unfold tsb_send_post, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| exact LO].
  -
    zstep. gF. zs2. zstep. zstep.
      rewrite (land16_small last) by lia.
    rewrite shl_guard0 by first [lia | apply (Z.lt_le_trans _ (2^15)); [lia| apply Z.pow_le_mono_r; lia]].
    gF.
    zs. zs. zs. zs. zs.
      sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
      gF. zs2. zs2. zs2. gX. gF.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV last) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
      gF. zs2. zs2. zs2. gX. gF.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV last) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV last)) 8)) ltac:(apply hi8_lo16; exact LO).
    zs2. zstep. zs2. zs2.
      gF. zs2. zstep. gF.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range last (16 - BV) ltac:(lia)) as RSH.
    zs2. zstep.
      zstep. br_true.
    zstep.
      reg_as (BV + -13) (BV + 3 - 16).
    apply evt_done. unfold tsb_send_post, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

Lemma tsb_head_flat : forall s last, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2^16 ->
  wuF_PB (sbF_PB (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) last 3) (sbF_PD (ds_pending s) (ds_bi_valid s) 3)
         (sbF_BB (ds_bi_buf s) (ds_bi_valid s) last 3) (sbF_BV (ds_bi_valid s) 3) = tsb_hA s last
  /\ wuF_PD (sbF_PD (ds_pending s) (ds_bi_valid s) 3) (sbF_BV (ds_bi_valid s) 3) = tsb_hP s.
Proof.
  intros s last H1 H2.
  pose proof (tsb_head_eq s last H1 H2) as E.
  pose proof (send_bits_sbF s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) last 3) as E2.
  rewrite upd4_self in E2. apply (f_equal bi_windup) in E2. rewrite bi_windup_wuF, E in E2.
  split; [apply (f_equal ds_pending_buf) in E2; rewrite !upd4_pending_buf in E2| apply (f_equal ds_pending) in E2; rewrite !upd4_pending in E2];
    symmetry; exact E2.
Qed.

Definition Z_TR_STORED : Z := 0x1bd70.
Definition buf_ptr (L : dlay) (buf : option Z) : Z := match buf with Some off => dl_Aw L + off | None => 0 end.

Definition tr_stored_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (buf : option Z) (len last : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DST m' L (tr_stored_block s buf len last).

Lemma tr_stored_block_spec : forall (L : dlay) (s : deflate_state) (buf : option Z) (len last lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 s -> ds_pending (tr_stored_block s buf len last) <= 65536 -> (len <> 0 -> buf <> None) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  a0 = wz (dl_As L) -> a1 = wz (buf_ptr L buf) -> a2 = wz len -> a3 = wz last ->
  evt usegs (tr_stored_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s buf len last lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_STORED) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST MI STK LO BEL BI ROOM NZ BOK RLEN RL -> -> -> ->. unfold Z_TR_STORED.
  pose proof BI as (RBV & RBB & RPD).
  rewrite tr_stored_block_eq in ROOM by lia. rewrite tsb_tail_pending in ROOM.
  pose proof (tsb_hP_range s) as RHP.
  destruct (tsb_head_flat s last ltac:(lia) ltac:(lia)) as [EhA EhP].
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MUf.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
  open_DST ST. lay_open LAY. below_open BEL. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  carve_frame 48%nat STK.
  do 6 zstep.
  gF. zstep. zs2. al8 (dl_As L). gF. zstep. zstep.
  mv_group dsA_munch GA MUs WM. mv_group dsD_munch GD MUs WM. mv_group dpend_munch Gpend MUs WM. clear MUs.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH. clear GA GD Gpend.
  call (tsb_send L s last (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) (wz (ds_bi_buf s))).
  1:{ exact EMH. } 1:{ apply lo16_unsigned_wz. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ lia. } 1:{ lia. }
  1:{ intros C. unfold tsb_hP in RHP, ROOM. rewrite !(proj2 (Z.leb_gt _ _)) in ROOM by lia. lia. } 1:{ exact RL. }
  clear EMH. rename POST into LO1.
  lazymatch goal with H : EM _ L s _ _ ?w _ |- _ => rename H into EMH; zstep; zstep;
    call (bi_windup_spec L s (sbF_PB (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) last 3) (sbF_PD (ds_pending s) (ds_bi_valid s) 3)
          (sbF_BB (ds_bi_buf s) (ds_bi_valid s) last 3) (sbF_BV (ds_bi_valid s) 3) w) end.
  1:{ exact EMH. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact LO1. }
  1:{ unfold sbF_BV. destruct (Z.ltb_spec (16 - 3) (ds_bi_valid s)); lia. }
  1:{ unfold sbF_PD. destruct (Z.ltb_spec (16 - 3) (ds_bi_valid s)); lia. }
  1:{ rewrite EhP. lia. } 1:{ reflexivity. }
  rewrite EhA, EhP in POST. clear EMH LO1. open_EM POST.
  remember (tsb_hA s last) as A1 eqn:EA1. remember (tsb_hP s) as P1 eqn:EP1.
  assert (LA1 : arr_len A1 = 65536) by (rewrite EA1, tsb_hA_len; exact LNP).
  do 5 zstep. gF. zs2. zs2. zs2. gX. gF.
  pb_store Gpend A1 65536 (dl_Ab L) P1 (wrap8 (Z.land (wrap16 len) 255)) ltac:(apply lenb0).
  do 5 zstep. gF. zs2. zs2. zs2. gX. gF. zstep.
  pb_store Gpend (arr_set A1 P1 (wrap8 (Z.land (wrap16 len) 255))) 65536 (dl_Ab L) (P1 + 1) (wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8)) ltac:(apply lenb1).
  do 5 zstep. gF. zs2. zs2. zs2. gX. gF. zstep.
  pb_store Gpend (arr_set (arr_set A1 P1 (wrap8 (Z.land (wrap16 len) 255))) (P1 + 1) (wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8))) 65536 (dl_Ab L) (P1 + 1 + 1)
           (wrap8 (Z.land (wrap16 (Z.lnot len)) 255)) ltac:(apply lenb2).
  do 5 zstep. gF. zs2. zs2. zs2. gX. gF. zstep.
  pb_store Gpend (arr_set (arr_set (arr_set A1 P1 (wrap8 (Z.land (wrap16 len) 255))) (P1 + 1) (wrap8 (Z.shiftr (wrap16 (wrap16 len)) 8))) (P1 + 1 + 1)
                          (wrap8 (Z.land (wrap16 (Z.lnot len)) 255))) 65536 (dl_Ab L) (P1 + 1 + 1 + 1)
           (wrap8 (Z.shiftr (wrap16 (wrap16 (Z.lnot len))) 8)) ltac:(apply lenb3w; lia).
  fold (tsb_lenA A1 P1 len) in *.
  assert (LA2 : arr_len (tsb_lenA A1 P1 len) = 65536) by (unfold tsb_lenA; rewrite !arr_len_set; exact LA1).
  zstep. br_cases K.
  -
    do 3 zstep. do 7 zstep. release_frame FR STK (bv_unsigned sp).
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
    do 3 zstep. gF. zs2. zs2. zs2. gX. zstep. zstep.
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
    reg_as (P1 + 4 + dl_Ab L) (dl_Ab L + (P1 + 4)). zstep.
    call (memcpy_Z (dl_Ab L + (P1 + 4)) (dl_Aw L + off) len).
    1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    pose proof (u8arr_join3z _ (dl_Ab L) _ _ _ (P1 + 4) len ltac:(lia) ltac:(lia) LO1 O1 PC O3) as Gpend.
    rewrite av8_blit' in Gpend by lia.
    pose proof (av8_zlength (arr_blit (tsb_lenA A1 P1 len) (P1 + 4) (ds_window s) off len) 65536 ltac:(lia)) as LPBf.
    clear O1 O3 PC POST SRC LSRC LO1 LO3.
    do 3 zstep. do 7 zstep. release_frame FR STK (bv_unsigned sp).
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
