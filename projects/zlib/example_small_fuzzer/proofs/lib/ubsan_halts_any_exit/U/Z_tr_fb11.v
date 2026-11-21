(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.

Module Z_tr_stored.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_windup.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
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
             F (wz 0x1ba7c) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned wbb mod 2^16 = BB mod 2^16.

Lemma tsb_send : forall (L : dlay) (s : deflate_state) (last : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= BV <= 16 -> 0 <= PD -> (16 - 3 < BV -> PD + 2 <= 65536) -> 0 <= last <= 1 ->
  evt usegs (tsb_send_post L s (sbF_PB PB PD BB BV last 3) (sbF_PD PD BV 3) (sbF_BB BB BV last 3) (sbF_BV BV 3)
                ra sp gp tp t0 t1 t2 s0 (wz (dl_As L)) a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (wz (dl_As L)) a0 a1 a2 (wz last) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b97c) fc None m (seg_rom usegs)).
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

Definition Z_TR_STORED : Z := 0x1b94c.
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
End Z_tr_stored.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.

Module Z_tr_fb3.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_cb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_windup OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_init OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab CompressModel RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_arm_stored : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv usegs m ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> RefFlushBlk13.sto_ok 65536 X buf len last -> RefFlushBlk13.post_ok 65536 last (tr_stored_block X buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tr_stored_block X buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c290) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI (ROOM & NN) (BIY & ROOMY) BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO.
  pose proof BEL as BEL0. below_open BEL0.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  assert (LAY : dlay_ok L) by (destruct ST; assumption).
  unfold utfR. do 5 zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl usegs m1) as WMz.
  call (tr_stored_block_spec L X buf len last lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BI. } 1:{ exact ROOM. } 1:{ exact NN. } 1:{ exact BOK. } 1:{ exact Rlen. } 1:{ exact Rl. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST. name_mem m2.
  remember (tr_stored_block X buf len last) as Y eqn:EY.
  assert (ESY : ds_strm Y = c).
  { rewrite EY, (k_tr_stored_block _ _ _ keeps_strm eq_refl). exact ESTRM. }
  zs2. zs2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl usegs m2) as WMz.
  call (init_block_spec L Y).
  1:{ eassumption. } 1:{ eassumption. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite ESP in *.
  zstep. name_mem m3.
  br_cases_s K.
  - eapply (tfb_finish L (init_block Y) Rfin c last lo TF_FIN0 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
  - eapply (tfb_finish L (init_block Y) Rfin c last lo TF_FINW m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
Qed.
End Z_tr_fb3.

Module Z_tr_fb4.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_cb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Ltac dsite_fin POSTNAME EX MU WM GA GD Gpend DEC LOW SIDE :=
  apply evt_done; unfold POSTNAME, utfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; DEC; EX;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|];
  first [ split; [LOW|]; SIDE; split; [reflexivity| lia] | LOW ].

Definition tfb_d1_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z)
    (ra gp tp t0 t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a3 a4 a7 w m',
    ms' = MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz BV0) (wz 65535) a3 a4 w (wz BV) a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c504) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma tfb_d1 : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= last <= 1 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) -> 0 <= mb <= 18 ->
  evt usegs (tfb_d1_post L s sp last len bufp mb (sbF_PB PB PD BB BV (4 + last) 3) (sbF_PD PD BV 3) (sbF_BB BB BV (4 + last) 3) BV (sbF_BV BV 3)
                ra gp tp t0 t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz BV) a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c3bc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY Rl RBV RPD ROOM Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zs2. zs2. rewrite slt_lxor by lia. replace (last + 4 <? last) with false by (symmetry; apply Z.ltb_ge; lia). reg_as (last + 4) (4 + last).
 
  zstep. br_cases K.
  -
    ustep TF_TRAP. zs2. ustep TF_TRAP. zs. zs. zs. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    zstep. zs2.
    dsite_fin tfb_d1_post ltac:(do 5 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia) ltac:(exact LO) ltac:(idtac).
  -
    ustep TF_TRAP. zs2. ustep TF_TRAP. zs2. rewrite (land16_small (4 + last)) by lia. zs2. zs2. shl_g0. ustep TF_TRAP.
    zs. zs. zs. zs. zs. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1c42c TF_TRAP. at_pc 0x1c42c.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (4 + last)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1c460 TF_TRAP. at_pc 0x1c460.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (4 + last)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (4 + last))) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1c484 TF_TRAP. at_pc 0x1c484.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range (4 + last) (16 - BV) ltac:(lia)) as RSH.
    zs2. zstep. zstep. br_true. reg_as (BV + -13) (BV + 3 - 16).
    dsite_fin tfb_d1_post ltac:(do 5 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(idtac).
Qed.

Definition tfb_d2_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a3 a7 w pcx m',
    ms' = MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) a3 w (wz 12) (wz BV) a7
                (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1c7c4 /\ BV <= 11) \/ (pcx = 0x1c608 /\ 12 <= BV)).

Lemma tfb_d2 : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z) (w : word) (hB1 hB2 hB3 : list byte)
    (ra gp tp t0 t1 t2 a3 a4 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD w (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  rw_cells usegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  256 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 0 <= BV <= 16 -> 0 <= PD -> (11 < BV -> PD + 2 <= 65536) ->
  evt usegs (tfb_d2_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_l_max_code s - 256) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_l_max_code s - 256) 5) (sbF_BV BV 5)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz BV0) (wz 65535) a3 a4 w (wz BV) a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c504) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY GB Rlm Rdm RBV RPD ROOM. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH. unfold dsB_cells in GB.
  zs2. zs2. zstep. ustep TF_TRAP. zs2. zs2. ustep TF_TRAP. clear GB. zs2. zs2. rewrite slt_lxor by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. zs2. zs2.
  change (Z.lxor (Z.b2z true) 1) with 0. replace (ds_l_max_code s + -256) with (ds_l_max_code s - 256) by lia.
  zstep. br_cases K.
  -
    ustep TF_TRAP. zs2. ustep TF_TRAP. zs. zs. sb_or w1 LO BB (exact HW).
    zstep. zs2. zstep. zs2. zs2. rewrite slt_lxor by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. zs2. zs2. change (Z.lxor (Z.b2z true) 1) with 0.
    reg_as (ds_d_max_code s + 1 + -1) (ds_d_max_code s).
    zstep. br_cases K2.
    + dsite_fin tfb_d2_post ltac:(do 7 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 5) BV)) by lia) ltac:(exact LO) ltac:(right).
    + dsite_fin tfb_d2_post ltac:(do 7 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 5) BV)) by lia) ltac:(exact LO) ltac:(left).
  -
    ustep TF_TRAP. zs2. ustep TF_TRAP. zs2. rewrite (land16_small (ds_l_max_code s - 256)) by lia.
    zs2. zs2. shl_g0. ustep TF_TRAP.
    zs. zs. zs. zs. sb_or w1 LO BB (exact HW).
    zs. zs. zstep. zs.
    uwalk 0x1c588 TF_TRAP. at_pc 0x1c588.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (ds_l_max_code s - 256)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1c5bc TF_TRAP. at_pc 0x1c5bc.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (ds_l_max_code s - 256)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (ds_l_max_code s - 256))) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1c5e0 TF_TRAP. at_pc 0x1c5e0.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range (ds_l_max_code s - 256) (16 - BV) ltac:(lia)) as RSH.
    zs2. zstep. ustep TF_TRAP. zstep. zs2. zs2. rewrite slt_lxor by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. zs2. zs2. change (Z.lxor (Z.b2z true) 1) with 0.
    reg_as (ds_d_max_code s + 1 + -1) (ds_d_max_code s). reg_as (BV + -11) (BV + 5 - 16).
    zstep. br_cases K2.
    + dsite_fin tfb_d2_post ltac:(do 7 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 5) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left).
    + dsite_fin tfb_d2_post ltac:(do 7 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 5) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right).
Qed.
End Z_tr_fb4.

Module Z_tr_fb5.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_cb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition tfb_d3_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a7 w pcx m',
    ms' = MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) w (wz (mb + -3)) (wz 13) (wz BV) a7
                (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1c7f0 /\ BV <= 12) \/ (pcx = 0x1c6d4 /\ 13 <= BV)).

Lemma tfb_d3k : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t0 t1 t2 a3 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 0 <= BV <= 11 -> 0 <= PD -> 0 <= mb <= 18 ->
  evt usegs (tfb_d3_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_d_max_code s) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_d_max_code s) 5) (sbF_BV BV 5)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) a3 w (wz 12) (wz BV) a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1c7c4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rlm Rdm RBV RPD Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep TF_TRAP. zs2. ustep TF_TRAP. zs. zs. sb_or w1 LO BB (exact HW).
  zstep. zs2. zstep. zs2. zs2.
  zstep. br_cases K2.
  - dsite_fin tfb_d3_post ltac:(do 6 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 5) BV)) by lia) ltac:(exact LO) ltac:(right).
  - dsite_fin tfb_d3_post ltac:(do 6 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 5) BV)) by lia) ltac:(exact LO) ltac:(left).
Qed.

Lemma tfb_d3f : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t0 t1 t2 a3 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 12 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= mb <= 18 ->
  evt usegs (tfb_d3_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_d_max_code s) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_d_max_code s) 5) (sbF_BV BV 5)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) a3 w (wz 12) (wz BV) a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1c608) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rlm Rdm RBV RPD ROOM Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep TF_TRAP. zs2. ustep TF_TRAP. zs2. rewrite (land16_small (ds_d_max_code s)) by lia.
  zs2. zs2. shl_g0. ustep TF_TRAP.
  zs. zs. zs. zs. sb_or w1 LO BB (exact HW).
  zs. zs. zstep. zs.
  uwalk 0x1c65c TF_TRAP. at_pc 0x1c65c.
  pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (ds_d_max_code s)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
  zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
  uwalk 0x1c690 TF_TRAP. at_pc 0x1c690.
  pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (ds_d_max_code s)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (ds_d_max_code s))) 8)) ltac:(apply hi8_lo16; exact LO).
  uwalk 0x1c6b4 TF_TRAP. at_pc 0x1c6b4.
  zs2. rewrite srlw_val16 by lia.
  pose proof (shiftr_wrap16_range (ds_d_max_code s) (16 - BV) ltac:(lia)) as RSH.
  zs2. zstep. ustep TF_TRAP. zstep. zs2. zs2. reg_as (BV + -11) (BV + 5 - 16).
  zstep. br_cases K2.
  - dsite_fin tfb_d3_post ltac:(do 6 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 5) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left).
  - dsite_fin tfb_d3_post ltac:(do 6 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 5) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right).
Qed.

Definition tfb_d4_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a3 a4 a5 a6 a7 w m',
    ms' = MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp w (wz BV) t2 (wz (mb + 1)) (wz (ds_l_max_code s + 1)) a2 a3 a4 a5 a6 a7
                (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1c810) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma tfb_d4k : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t0 t1 t2 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 0 <= BV <= 12 -> 0 <= PD -> 3 <= mb <= 18 ->
  evt usegs (tfb_d4_post L s sp last bufp mb (sbF_PB PB PD BB BV (mb - 3) 4) (sbF_PD PD BV 4) (sbF_BB BB BV (mb - 3) 4) (sbF_BV BV 4)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) w (wz (mb + -3)) (wz 13) (wz BV) a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1c7f0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rlm Rdm RBV RPD Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH. replace (mb + -3) with (mb - 3) by lia.
  zs2. ustep TF_TRAP. zs. zs. sb_or w1 LO BB (exact HW).
  zstep. zs2. zs2. zstep.
  dsite_fin tfb_d4_post ltac:(do 8 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 4) BV)) by lia) ltac:(exact LO) ltac:(idtac).
Qed.

Lemma tfb_d4f : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t0 t1 t2 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 13 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 3 <= mb <= 18 ->
  evt usegs (tfb_d4_post L s sp last bufp mb (sbF_PB PB PD BB BV (mb - 3) 4) (sbF_PD PD BV 4) (sbF_BB BB BV (mb - 3) 4) (sbF_BV BV 4)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) w (wz (mb + -3)) (wz 13) (wz BV) a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1c6d4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rlm Rdm RBV RPD ROOM Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH. replace (mb + -3) with (mb - 3) by lia.
  zs2. ustep TF_TRAP. zs2. rewrite (land16_small (mb - 3)) by lia.
  zs2. zs2. shl_g0. ustep TF_TRAP.
  zs. zs. zs. zs. sb_or w1 LO BB (exact HW).
  zs. zs. zstep. zs.
  uwalk 0x1c724 TF_TRAP. at_pc 0x1c724.
  pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (mb - 3)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
  zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
  uwalk 0x1c758 TF_TRAP. at_pc 0x1c758.
  pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (mb - 3)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (mb - 3))) 8)) ltac:(apply hi8_lo16; exact LO).
  uwalk 0x1c77c TF_TRAP. at_pc 0x1c77c.
  zs2. rewrite srlw_val16 by lia.
  pose proof (shiftr_wrap16_range (mb - 3) (16 - BV) ltac:(lia)) as RSH.
  zs2. zstep. zstep. br_true. zs2. zstep. reg_as (BV + -12) (BV + 4 - 16).
  dsite_fin tfb_d4_post ltac:(do 8 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 4) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(idtac).
Qed.
End Z_tr_fb5.

Module Z_tr_fb6.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_cb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma sx16_small : forall v, 0 <= v < 32768 -> sx16 (wz v) = wz v.
Proof.
  intros v Hv. unfold sx16. f_equal. rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo]. rewrite Z.mod_small by lia. lia.
Qed.

Definition ublR (L : dlay) (sp : word) (last bufp mb k r BV : Z) (s : deflate_state) (w : word)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  utfR L sp last (ds_d_max_code s) bufp ra gp tp w (wz BV) t2 (wz k) (wz (ds_l_max_code s + 1)) (wz (dl_As L + 2748)) (wz 14) (wz 31)
       (wz (18446744073709551615 - (dl_As L + 2748))) (wz (Z_BL_ORDER + r)) (wz 16) (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition tfb_blo_iter_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb k r : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4 t5 w pcx m',
    ms' = MS (ublR L sp last bufp mb (k - 1) (r + 1) BV s w ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1c840 /\ k - 1 <> 0) \/ (pcx = 0x1c928 /\ k - 1 = 0)).

Ltac blo_fin MU WM GA GD Gpend DEC LOW SIDE :=
  apply evt_done; unfold tfb_blo_iter_post, ublR, utfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV, Z_BL_ORDER; DEC; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LOW|];
  SIDE; split; [reflexivity| lia].

Lemma tfb_blo_iter : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb k r V : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bdl (arr_get bl_order_a r) ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 -> 0 <= r <= mb -> mb <= 18 -> 1 <= k < 2^31 ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 ->
  0 <= V < 16 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) ->
  evt usegs (tfb_blo_iter_post L s sp last bufp mb k r (sbF_PB PB PD BB BV V 3) (sbF_PD PD BV 3) (sbF_BB BB BV V 3) (sbF_BV BV 3)
                ra gp tp s7 s8 s9 s10 s11 t6 F fc m)
      (MS (ublR L sp last bufp mb k r BV s w ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c840) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV EMH HW MI LAY RDB Rr Rmb Rk Rlm Rdm RV RBV RPD ROOM. unfold ublR, utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bl_order_bound r) as Ro.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI (arr_get bl_order_a r) ltac:(lia)) as [_ RDl]. rewrite <- EV in RDl.
  pose proof (u8ro_read usegs m Z_BL_ORDER (av8 bl_order_a 19) r _ (wa (Z_BL_ORDER + r)) (rod_bl_order m MI)
                (av8_nth bl_order_a 19 r ltac:(lia)) ltac:(lia) eq_refl) as RDo.
  unfold Z_BL_ORDER in *.
  zsb. rewrite (bv8_small (arr_get bl_order_a r)) by lia.
  zs2. shl_norm.
  replace (dl_As L + 2748 + 4 * arr_get bl_order_a r + 2) with (dl_As L + 2748 + arr_get bl_order_a r * 4 + 2) in RDl by lia.
  zstep. br_cases K.
  -
    ustep TF_TRAP. ustep TF_TRAP. zs2. zs. rewrite (sx16_small V) by lia.
    zs. zs. sb_or w1 LO BB (exact HW).
    zstep. zs2. zstep. zstep. zs2. zs2. replace (74720 + r + 1) with (74720 + (r + 1)) by lia. reg_as (k + -1) (k - 1).
    zstep. br_cases_s K2.
    + blo_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia) ltac:(exact LO) ltac:(right).
    + blo_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia) ltac:(exact LO) ltac:(left).
  -
    ustep TF_TRAP. ustep TF_TRAP. zs2. zs. rewrite (zx16_small V) by lia. zs2. zs2. shl_g0. ustep TF_TRAP.
    zs. zs. zs. zs. sb_or w1 LO BB (exact HW).
    zs. zs. zstep. zs.
    uwalk 0x1c8a0 TF_TRAP. at_pc 0x1c8a0.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1c8d4 TF_TRAP. at_pc 0x1c8d4.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1c8f0 TF_TRAP. at_pc 0x1c8f0.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zstep. zstep. br_true. zstep. zs2. zs2. replace (74720 + r + 1) with (74720 + (r + 1)) by lia. reg_as (k + -1) (k - 1). reg_as (BV + -13) (BV + 3 - 16).
   
    zstep. br_cases_s K2.
    + blo_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right).
    + blo_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left).
Qed.

Lemma bl_calls_S : forall s r k, bl_calls s r (S k) = (arr_get (ds_bl_tree_dl s) (arr_get bl_order_a r), 3) :: bl_calls s (r + 1) k.
Proof. reflexivity. Qed.

Definition tfb_blo_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (R : deflate_state)
    (ra gp tp s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4 t5 w PB' PD' BB' BV' m',
    ms' = MS (ublR L sp last bufp mb 0 (mb + 1) BV' s w ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c928) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' w (wz BV') /\ bv_unsigned w mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV' /\ 0 <= BV' <= 16 /\ 0 <= PD'.

Lemma tfb_blo_loop : forall (k : nat) (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb r : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= r -> Z.of_nat (S k) = mb + 1 - r -> mb <= 18 ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bdl i < 16) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (bl_calls s r (S k)) ->
  R = sbs_run (upd4 s PB PD BB BV) (bl_calls s r (S k)) ->
  evt usegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t6 F fc m0)
      (MS (ublR L sp last bufp mb (Z.of_nat (S k)) r BV s w ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c840) fc None m (seg_rom usegs)).
Proof.
  induction k as [|k IH]; intros until m; intros Ebdl EMH HW MI LAY MU WM RDB Rr Ek Rmb Rlm Rdm RBd RBV RPD HSB ER.
  all: pose proof (bl_order_bound r) as Ro.
  all: rewrite bl_calls_S in HSB, ER; rewrite <- Ebdl in HSB, ER.
  all: apply sbs_ok_cons_flat in HSB; destruct HSB as (_ & ROOM & HSB2); rewrite sbs_run_cons_flat in ER.
  - call (tfb_blo_iter L s bfc bdl sp last bufp mb (Z.of_nat 1) r (arr_get bdl (arr_get bl_order_a r)) PB PD BB BV wbb w).
    1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ lia. } 1:{ exact Rmb. } 1:{ lia. } 1:{ exact Rlm. } 1:{ exact Rdm. } 1:{ apply RBd. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM; lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    cbn [bl_calls sbs_run] in ER. replace (r + 1) with (mb + 1) by lia. change (Z.of_nat 1 - 1) with 0.
    apply evt_done. unfold tfb_blo_post. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER|]. split; [apply sbF_BV_range; [exact RBV| lia]| pose proof (sbF_PD_range PD BV 3 RPD); lia].
  - call (tfb_blo_iter L s bfc bdl sp last bufp mb (Z.of_nat (S (S k))) r (arr_get bdl (arr_get bl_order_a r)) PB PD BB BV wbb w).
    1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ lia. } 1:{ exact Rmb. } 1:{ lia. } 1:{ exact Rlm. } 1:{ exact Rdm. } 1:{ apply RBd. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM; lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    replace (Z.of_nat (S (S k)) - 1) with (Z.of_nat (S k)) by lia.
    match goal with H : EM ?mm _ _ _ _ ?wc _, HB : bv_unsigned ?wc mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s bfc bdl sp last bufp mb (r + 1) R m0); [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| exact Rmb| exact Rlm| exact Rdm| exact RBd
        | apply sbF_BV_range; [exact RBV| lia]| pose proof (sbF_PD_range PD BV 3 RPD); lia| exact HSB2| exact ER] end.
Qed.

Lemma tfb_dyn_hdr2 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t2 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= mb <= 18 ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bdl i < 16) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (bl_calls s 0 (Z.to_nat (mb + 1))) ->
  R = sbs_run (upd4 s PB PD BB BV) (bl_calls s 0 (Z.to_nat (mb + 1))) ->
  evt usegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t6 F fc m0)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp w (wz BV) t2 (wz (mb + 1)) (wz (ds_l_max_code s + 1)) a2 a3 a4 a5 a6 a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1c810) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Ebdl EMH HW MI LAY MU WM RDB Rmb Rlm Rdm RBd RBV RPD HSB ER. unfold utfR.
  pose proof LAY as LAY'. lay_open LAY'.
  zs2. reg_as (dl_As L + 2047 + 701) (dl_As L + 2748). do 3 zs2. zs2. rewrite zb_lxor_ones by lia. do 3 zs2.
  destruct (Z.to_nat (mb + 1)) as [|k] eqn:En; [lia|].
  replace (wz 74720) with (wz (Z_BL_ORDER + 0)) by reflexivity. reg_as (mb + 1) (Z.of_nat (S k)).
  eapply (tfb_blo_loop k L s bfc bdl sp last bufp mb 0 R m0 PB PD BB BV wbb w);
    [exact Ebdl| exact EMH| exact HW| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact Rlm| exact Rdm| exact RBd| exact RBV| exact RPD| exact HSB| exact ER].
Qed.

Lemma tfb_dyn_hdr : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last len bufp mb : Z) (R : deflate_state)
    (PB : arr) (PD BB BV : Z) (wbb : word) (hB1 hB2 hB3 : list byte)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  rw_cells usegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= last <= 1 -> 256 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 3 <= mb <= 18 ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bdl i < 16) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (hd_calls last s mb) ->
  R = sbs_run (upd4 s PB PD BB BV) (hd_calls last s mb) ->
  evt usegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz BV) a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c3bc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Ebdl EMH HBB MI LAY GB RDB Rl Rlm Rdm Rmb RBd RBV RPD HSB ER.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
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
  1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM1; lia. } 1:{ lia. }
  match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (tfb_d2 L s sp last len bufp mb pb pd bb bv0 (sbF_BV BV 3) wc hB1 hB2 hB3);
    [exact H| exact HB| eassumption| exact LAY| exact GB| exact Rlm| exact Rdm| exact RBV1| lia| intros; apply ROOM2; lia|] end.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X2]|[-> X2]] end.
  -
    match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (tfb_d3k L s sp last bufp mb pb pd bb bv wc wc);
      [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| lia|] end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X3]|[-> X3]] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4k L s sp last bufp mb pb pd bb bv wc wc);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| lia|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 wc wc);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4f L s sp last bufp mb pb pd bb bv wc wc);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| apply ROOM4; lia| lia|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 wc wc);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
  -
    match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (tfb_d3f L s sp last bufp mb pb pd bb bv wc wc);
      [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| apply ROOM3; lia| lia|] end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X3]|[-> X3]] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4k L s sp last bufp mb pb pd bb bv wc wc);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| lia|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 wc wc);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4f L s sp last bufp mb pb pd bb bv wc wc);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| apply ROOM4; lia| lia|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 wc wc);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
Qed.
End Z_tr_fb6.

Module Z_tr_st8.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_scan1 Z_tr_st7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7.Z_tr_st6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st7 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_cb5.
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


Definition ust_loop_post (L : dlay) (s : deflate_state) (T mc : Z) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists n' nl' x1 x8 x9 x18 x19 x23 x24 x25 x26 x27 wbb PB' PD' BB' BV' m',
    ms' = MS (ustR L T mc n' nl' x1 x8 x9 x18 x19 x23 x24 x25 x26 x27 sp gp tp) F (wz ST_EXIT) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV'.

Lemma st_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (tfc tdl bfc bdl : arr) (T N mc : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV n prevlen nextlen count mx mn : Z) (wbb : word)
    (x8 x9 x18 x19 x23 x25 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 T tfc tdl N -> tdl = tree_dl s t -> 0 < T -> T + 4 * N < 2^62 -> mc + 1 < N -> N <= 573 ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bfc i < 32768) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get tdl i <= 15) -> (forall i, 0 <= i < N -> 0 <= arr_get tdl i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get tdl n -> Z.of_nat (S f) = mc + 1 - n ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (mn = 4 \/ prevlen = nextlen \/ nextlen = 0) ->
  R = send_tree_loop (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  send_tree_ok 65536 (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  evt usegs (ust_loop_post L s T mc R sp gp tp F fc m0)
      (MS (ustR L T mc n nextlen (wz prevlen) x8 x9 x18 x19 x23 (wz count) x25 (wz mx) (wz mn) sp gp tp) F (wz ST_BODY) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros EMH HBB MI LAY MU WM RDT Etdl RT1 RT2 RmcN RN RDB Ebfc Ebdl RBf RTl RTn Rn Enl Ef RBV RPD Rc Rmx Rmn Rpl INV ER OK.
  - call (st_iter L s t tfc tdl bfc bdl T N mc n 0%nat R m PB PD BB BV prevlen nextlen count mx mn wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Etdl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RmcN. } 1:{ exact RN. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Ebfc. } 1:{ exact Ebdl. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. }
    1:{ exact Rn. } 1:{ exact Enl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. } 1:{ exact INV. } 1:{ exact ER. } 1:{ exact OK. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    match goal with E : R = send_tree_loop 0 _ _ _ _ _ _ _ _ _ |- _ => rewrite send_loop_0 in E; rename E into ER' end.
    apply evt_done. unfold ust_loop_post. do 18 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER'].
  - call (st_iter L s t tfc tdl bfc bdl T N mc n (S f) R m PB PD BB BV prevlen nextlen count mx mn wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Etdl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RmcN. } 1:{ exact RN. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Ebfc. } 1:{ exact Ebdl. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. }
    1:{ exact Rn. } 1:{ exact Enl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. } 1:{ exact INV. } 1:{ exact ER. } 1:{ exact OK. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    match goal with E : R = send_tree_loop (S f) _ _ _ _ _ _ _ _ _, O : send_tree_ok _ (S f) _ _ _ _ _ _ _ _ _, I : (_ = 4 \/ _ = _ \/ _ = 0) |- _ =>
      eapply (IH L s t tfc tdl bfc bdl T N mc R m0); [eassumption| eassumption| eassumption| exact LAY| exact MU| exact WM| exact RDT| exact Etdl| exact RT1| exact RT2
        | exact RmcN| exact RN| exact RDB| exact Ebfc| exact Ebdl| exact RBf| exact RTl| exact RTn| lia| reflexivity| lia| assumption| assumption| assumption| assumption| assumption| assumption
        | exact I| exact E| exact O] end.
Qed.

Definition Z_SEND_TREE : Z := 0x1e1dc.
Definition Z_ST_STACK : Z := 112.

Lemma tree_readable : forall (W : list ivl) (m : mem) (L : dlay) (s : deflate_state) (t : tree_id),
  dlt m L s -> ddt m L s -> dbt m L s -> disjoint_from W (dl_As L + 212) 2692 ->
  ct_readable W m (dl_As L + toff t) (tree_fc s t) (tree_dl s t) (tsize t).
Proof.
  intros W m L s t Glt Gdt Gbt D. destruct t; cbn [toff tree_fc tree_dl tsize].
  - eapply ct_readable_rw; [exact Glt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
  - eapply ct_readable_rw; [exact Gdt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
  - eapply ct_readable_rw; [exact Gbt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
Qed.

Definition send_tree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch (cbW L lo sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DST m' L (send_tree s t mc).

Lemma send_tree_spec : forall (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_ST_STACK -> dlay_below L lo (bv_unsigned sp) ->
  0 <= mc -> mc + 1 < tsize t ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_fc s) i < 32768) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get (tree_dl s t) i <= 15) -> (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl s t) i < 65536) ->
  BINV 65536 s -> send_tree_safe 65536 s t mc ->
  a0 = wz (dl_As L) -> a1 = wz (dl_As L + toff t) -> a2 = wz mc ->
  evt usegs (send_tree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s t mc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_SEND_TREE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST MI STK LO BEL Rmc RmcN RBf RTl RTn BI SAFE -> -> ->. unfold Z_SEND_TREE, Z_ST_STACK in *.
  pose proof BI as (RBV & RBB & RPD).
  pose proof (munch_refl (cbW L lo sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
  open_DST ST. lay_open LAY. below_open BEL. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  assert (RDT : ct_readable (cbW L lo sp) m (dl_As L + toff t) (tree_fc s t) (tree_dl s t) (tsize t)) by (apply tree_readable; [exact Glt| exact Gdt| exact Gbt| cbn [disjoint_from]; lia]).
  assert (RDB : ct_readable (cbW L lo sp) m (dl_As L + 2748) (ds_bl_tree_fc s) (ds_bl_tree_dl s) 39) by (apply (tree_readable _ m L s TB); [exact Glt| exact Gdt| exact Gbt| cbn [disjoint_from]; lia]).
  assert (RtN : tsize t <= 573 /\ 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ toff t mod 4 = 0) by (destruct t; cbn [tsize toff]; repeat split; try lia; reflexivity).
  pose proof (RTn 0 ltac:(lia)) as Rnl0.
  unfold send_tree_safe, RefSendTree4.OK, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4.RefSendTree3.cnts0, Len in SAFE. replace (mc + 1 - 0) with (mc + 1) in SAFE by lia.
  carve_frame 112%nat STK.
  do 14 zstep.
  mv_group dsA_munch GA MUs WM. mv_group dsD_munch GD MUs WM. mv_group dpend_munch Gpend MUs WM. clear MUs.
  lazymatch goal with MIc : mem_inv usegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (RDT mc MU WM MIc 0 ltac:(lia)) as [_ RDl0] end.
  replace (dl_As L + toff t + 4 * 0 + 2) with (dl_As L + toff t + 2) in RDl0 by lia.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH. clear GA GD Gpend.
  assert (HBB : bv_unsigned (wz (ds_bi_buf s)) mod 2^16 = ds_bi_buf s mod 2^16) by apply lo16_unsigned_wz.
  assert (EX0 : upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) = s) by apply upd4_self.
  ustep ST_TRAP. ustep ST_TRAP.
  zstep. br_false.
  zs2. zs2. rewrite (zx16_small (arr_get (tree_dl s t) 0)) by lia. zs2. zs2. zs2. zs2.
  zstep. br_cases K0.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K0) in SAFE. cbn [fst snd] in SAFE. rewrite K0 in SAFE.
    rewrite K0. change (Z.b2z (0 <? 0)) with 0.
    zs2. do 5 zs2. zs2. al8 (dl_As L). zs2. reg_as (dl_As L + 2047 + 701) (dl_As L + 2748). do 10 zs2. change (bv_swrap 32 (0 + 3)) with 3.
    destruct (Z.to_nat (mc + 1)) as [|f] eqn:En; [lia|].
    remember (send_tree_loop (S f) s t mc 0 (-1) 0 0 138 3) as R eqn:ER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
      call (st_loop f L s t (tree_fc s t) (tree_dl s t) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (dl_As L + toff t) (tsize t) mc R mcur
                    (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) 0 (-1) 0 0 138 3 (wz (ds_bi_buf s))) end.
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ exact RmcN. } 1:{ lia. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. } 1:{ lia. } 1:{ symmetry; exact K0. } 1:{ lia. }
    1:{ exact RBV. } 1:{ lia. } 1:{ lia. } 1:{ left; reflexivity. } 1:{ left; reflexivity. } 1:{ lia. } 1:{ right; right; reflexivity. }
    1:{ rewrite EX0. exact ER. } 1:{ rewrite EX0. exact SAFE. }
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ =>
      assert (EQF : send_tree s t mc = upd4 s pb pd bb bv);
      [ unfold send_tree, Len; rewrite (proj2 (Z.eqb_eq _ _) K0), K0, En; rewrite <- ER; exact E |] end.
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    unfold ustR. do 15 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold send_tree_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K0) in SAFE. cbn [fst snd] in SAFE.
    rewrite (proj2 (Z.ltb_lt 0 _)) by lia. change (Z.b2z true) with 1.
    zs2. zs2. do 5 zs2. zs2. al8 (dl_As L). zs2. reg_as (dl_As L + 2047 + 701) (dl_As L + 2748). do 10 zs2. change (bv_swrap 32 (1 + 3)) with 4.
    destruct (Z.to_nat (mc + 1)) as [|f] eqn:En; [lia|].
    remember (send_tree_loop (S f) s t mc 0 (-1) (arr_get (tree_dl s t) 0) 0 7 4) as R eqn:ER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
      call (st_loop f L s t (tree_fc s t) (tree_dl s t) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (dl_As L + toff t) (tsize t) mc R mcur
                    (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) 0 (-1) (arr_get (tree_dl s t) 0) 0 7 4 (wz (ds_bi_buf s))) end.
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ exact RmcN. } 1:{ lia. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. } 1:{ lia. } 1:{ reflexivity. } 1:{ lia. }
    1:{ exact RBV. } 1:{ lia. } 1:{ lia. } 1:{ right; right; reflexivity. } 1:{ right; reflexivity. } 1:{ lia. } 1:{ left; reflexivity. }
    1:{ rewrite EX0. exact ER. } 1:{ rewrite EX0. exact SAFE. }
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ =>
      assert (EQF : send_tree s t mc = upd4 s pb pd bb bv);
      [ unfold send_tree, Len; rewrite (proj2 (Z.eqb_neq _ _) K0), En; rewrite <- ER; exact E |] end.
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    unfold ustR. do 15 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold send_tree_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
Qed.
End Z_tr_st8.

Module Z_tr_fb7.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fbpure.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_cb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_st8 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_init OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fbpure.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab TreeModel RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13 CompressModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Lemma ct_readable_weaken : forall W m T fc dl n n', ct_readable W m T fc dl n -> n' <= n -> ct_readable W m T fc dl n'.
Proof. intros W m T fc dl n n' H Hn m' MU WM MI i Hi. apply H; [exact MU| exact WM| exact MI| lia]. Qed.

Lemma tfb_arm_dyn : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len bufp mb lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv usegs m ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok 65536 last X mb -> RefFlushBlk13.post_ok 65536 last (tfb_emit 1 X mb buf len last) ->
  0 <= last <= 1 -> 3 <= mb <= 18 -> 256 <= ds_l_max_code X ->
  c15 (ds_dyn_ltree_fc X) 286 -> c15 (ds_dyn_dtree_fc X) 30 -> (forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_fc X) i < 32768) ->
  Rfin = tfb_fin last (tfb_emit 1 X mb buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_bi_valid X)) a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c3bc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL DOK (BIY & ROOMY) Rl Rmb Rlm256 RLf15 RDf15 RBf15 ER.
  unfold Z_TRFB_STACK in LO. rewrite (RefFlushBlk13.tfb_emit_1 buf len last X mb ltac:(lia)) in ER, BIY, ROOMY. cbv zeta in ER, BIY, ROOMY.
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok in DOK. cbv zeta in DOK.
  destruct DOK as (BI & HOK & (Rlm0 & Rlm1) & (Rdm0 & Rdm1) & (RBd16 & RBd) & RBf & RLl & RLn & RDl & RDn & SAFE1 & SAFE2 & CBOK & RLf & RDf & _ & Rsn & Rlb).
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
  pose proof (munch_refl (Wem L) m) as MUw. pose proof (wmono_refl usegs m) as WMw.
  open_DST ST. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb. pose proof LAY as LAY'. lay_open LAY'.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH.
  destruct GB as (hB1 & hB2 & hB3 & GB). unfold dsB_cells in GB.
  assert (RDB : ct_readable (Wem L) m (dl_As L + 2748) (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39)
    by (eapply ct_readable_rw; [exact Gbt| lia| lia| cbn [disjoint_from]; lia]).
  call (tfb_dyn_hdr L X (ds_bl_tree_fc X) (ds_bl_tree_dl X) sp last len bufp mb X11 (ds_pending_buf X) (ds_pending X) (ds_bi_buf X) (ds_bi_valid X) (wz (ds_bi_buf X)) hB1 hB2 hB3).
  1:{ reflexivity. } 1:{ exact EMH. } 1:{ apply lo16_unsigned_wz. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact GB. } 1:{ exact RDB. }
  1:{ exact Rl. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmb. } 1:{ exact RBd16. } 1:{ exact RBV. } 1:{ lia. }
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
  unfold ublR, utfR. zs2. ustep TF_TRAP. do 3 zs2. reg_as (ds_l_max_code X + 1 + -1) (ds_l_max_code X). zs2. name_mem m2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl usegs m2) as WMz.
  call (send_tree_spec L X11 TL (ds_l_max_code X) lo).
  1:{ exact ST11. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_ST_STACK. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ lia. } 1:{ cbn [tsize]. lia. } 1:{ rewrite A5. exact RBf15. }
  1:{ cbn [tree_dl]. rewrite A2. exact RLl. } 1:{ cbn [tree_dl tsize]. rewrite A2. exact RLn. }
  1:{ exact BI11. } 1:{ exact SAFE1. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST11. rewrite <- E12 in *. name_mem m3.
  ustep TF_TRAP. zs2. reg_as (dl_As L + 2047 + 457) (dl_As L + 2504). do 4 zs2. name_mem m4.
  pose proof (munch_refl (tfWz L lo sp) m4) as MUz. pose proof (wmono_refl usegs m4) as WMz.
  call (send_tree_spec L X12 TD (ds_d_max_code X) lo).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ rewrite ESP. unfold Z_ST_STACK. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ lia. } 1:{ cbn [tsize]. lia. } 1:{ rewrite B5. exact RBf15. }
  1:{ cbn [tree_dl]. rewrite B4. exact RDl. } 1:{ cbn [tree_dl tsize]. rewrite B4. exact RDn. }
  1:{ exact BI12. } 1:{ exact SAFE2. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite <- E13 in *. name_mem m5.
  do 4 zs2. name_mem m6.
  match goal with H : DST m6 L X13 |- _ => pose proof H as ST13; destruct H as [_ _ _ _ Glt Gdt Gbt _ _ _ _ _ _ _ _ _] end.
  assert (DISJ : disjoint_from (cbW L lo (wz (bv_unsigned sp + -64))) (dl_As L + 212) 2692) by (cbn [disjoint_from]; lia).
  pose proof (tree_readable _ m6 L X13 TL Glt Gdt Gbt DISJ) as RDL. cbn [toff tree_fc tree_dl tsize] in RDL. rewrite C1, C2 in RDL.
  pose proof (tree_readable _ m6 L X13 TD Glt Gdt Gbt DISJ) as RDD. cbn [toff tree_fc tree_dl tsize] in RDD. rewrite C3, C4 in RDD.
  clear Glt Gdt Gbt DISJ.
  pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  pose proof (munch_refl (tfWz L lo sp) m6) as MUz. pose proof (wmono_refl usegs m6) as WMz.
  call (compress_block_spec L X13 (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) (ds_dyn_dtree_fc X) (ds_dyn_dtree_dl X) (dl_As L + 212) (dl_As L + 2504) lo).
  1:{ exact ST13. } 1:{ eassumption. } 1:{ eassumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ eapply ct_readable_weaken; [exact RDL| lia]. } 1:{ eapply ct_readable_weaken; [exact RDD| lia]. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ Z.div_mod_to_equations; lia. } 1:{ Z.div_mod_to_equations; lia. }
  1:{ exact RLf15. } 1:{ exact RDf15. } 1:{ exact CBOK. }
  1:{ rewrite ELB. lia. } 1:{ rewrite ESN. lia. } 1:{ rewrite ESN. lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST13. name_mem m7.
  rewrite C1, C2, C3, C4 in ER, BIY, ROOMY.
  remember (compress_block X13 (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) (ds_dyn_dtree_fc X) (ds_dyn_dtree_dl X)) as Y eqn:EY.
  assert (ESY : ds_strm Y = c) by (rewrite EY, (k_compress_block _ _ _ keeps_strm eq_refl); exact ES13).
  zs2. zs2. name_mem m8.
  pose proof (munch_refl (tfWz L lo sp) m8) as MUz. pose proof (wmono_refl usegs m8) as WMz.
  call (init_block_spec L Y).
  1:{ eassumption. } 1:{ eassumption. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite ESP in *.
  zstep. name_mem m9.
  br_cases_s K.
  - eapply (tfb_finish L (init_block Y) Rfin c last lo TF_FINW m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
  - eapply (tfb_finish L (init_block Y) Rfin c last lo TF_FIN0 m0).
    1:{ eassumption. } 1:{ exact DZ. } 1:{ rewrite strm_init_block; exact ESY. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact MU. } 1:{ exact WM. } 1:{ exact FR. } 1:{ eassumption. }
    1:{ lia. } 1:{ exact BEL. } 1:{ apply BINV_init_block; exact BIY. } 1:{ exact ROOMY. } 1:{ exact ER. } 1:{ lia. }
Qed.
End Z_tr_fb7.

Module Z_tr_fb8.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_cb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab TreeModel RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13 CompressModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition ubsan_dyn (X : deflate_state) (mb : Z) : Prop :=
  3 <= mb /\ 256 <= ds_l_max_code X /\ c15 (ds_dyn_ltree_fc X) 286 /\ c15 (ds_dyn_dtree_fc X) 30
  /\ (forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_fc X) i < 32768).

Lemma tfb_emit_ns : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len bufp mb SL OL d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a1 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv usegs m ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> 0 <= last <= 1 -> 0 <= mb <= 18 -> 0 <= SL < 2^64 -> 0 <= OL < 2^64 ->
  d = (if SL =? OL then 0 else 1) ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok 65536 last X mb | _ => RefFlushBlk13.sto_ok 65536 X buf len last end ->
  (d = 1 -> ubsan_dyn X mb) ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X mb buf len last) ->
  Rfin = tfb_fin last (tfb_emit d X mb buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 (wz SL) (wz OL) a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c2dc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI Rl Rmb RSL ROL Ed SAFE UB POK ER.
  pose proof BI as (RBV & RBB & RPD).
  pose proof ST as ST'. destruct ST' as [_ _ _ GD _ _ _ _ _ _ _ _ _ _ _ LAY]. pose proof LAY as LAY'. lay_open LAY'.
  destruct GD as (hD0 & hD1 & hD2 & hD3 & hD4 & GD). unfold dsD_cells in GD.
  unfold utfR. zs2. clear GD. zstep. br_cases K.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in Ed. subst d. destruct (UB eq_refl) as (U1 & U2 & U3 & U4 & U5).
    eapply (tfb_arm_dyn L X Rfin c buf last len bufp mb lo m0); try eassumption. lia.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in Ed. subst d. rewrite tfb_emit_0 in POK, ER.
    eapply (tfb_arm_static L X Rfin c last len bufp lo m0); try eassumption.
Qed.

Lemma tfb_emit_all : forall (L : dlay) (X Rfin : deflate_state) (c : cstrm) (buf : option Z) (last len mb SL OL d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a1 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X -> dzs m L c -> ds_strm X = c -> mem_inv usegs m ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> dlay_below L lo (bv_unsigned sp) ->
  BINV 65536 X -> fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 -> 0 <= mb <= 18 -> 0 <= SL < 2^64 -> 0 <= OL < 2^64 ->
  d = (if (wrap64 (len + 4) <=? OL) && is_some buf then 2 else if SL =? OL then 0 else 1) ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok 65536 last X mb | _ => RefFlushBlk13.sto_ok 65536 X buf len last end ->
  (d = 1 -> ubsan_dyn X mb) ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X mb buf len last) ->
  Rfin = tfb_fin last (tfb_emit d X mb buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 (wz mb) a1 (wz SL) (wz OL) a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c284) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI MU WM FR STK LO BEL BI BOK Rlen Rl Rmb RSL ROL Ed SAFE UB POK ER.
  pose proof BI as (RBV & RBB & RPD).
  assert (LAY : dlay_ok L) by (destruct ST; assumption). pose proof LAY as LAY'. lay_open LAY'.
  unfold utfR. destruct buf as [off|]; cbn [buf_ptr is_some] in *.
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
    (ra gp tp t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a4 m',
    ms' = MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 (wz (tfb_SL (tfb_X6 X5 mb))) (wz (tfb_OL (tfb_X6 X5 mb))) a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1c284) fc None m' (seg_rom usegs)
    /\ munch [(dl_As L + 5912, dl_As L + 5920)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ dsD m' L (tfb_X6 X5 mb).

Lemma tfb_optlen : forall (L : dlay) (X5 : deflate_state) (sp : word) (last len bufp mb : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dsA m L X5 -> dsD m L X5 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_opt_len X5 < 2^63 -> 0 <= ds_static_len X5 < 2^63 -> 0 <= ds_strategy X5 <= 4 -> 0 <= mb <= 18 ->
  evt usegs (tfb_optlen_post L X5 sp last len bufp mb ra gp tp t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c244) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros GA GD MI LAY Rol Rsl Rst Rmb.
  pose proof (munch_refl [(dl_As L + 5912, dl_As L + 5920)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY'. lay_open LAY'.
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
  unfold utfR. zs2. zs2. zs2. shl_norm. do 5 zs2.
  zs2. zs2. reg_as (mb * 2 + mb + ds_opt_len X5 + 17) (mb * 2 + mb + ds_opt_len X5 + 17).
  zstep.
  set (SLb := Z.shiftr (ds_static_len X5 + 10) 3) in *. set (OLb := Z.shiftr (mb * 2 + mb + ds_opt_len X5 + 27) 3) in *.
  zstep. br_cases K.
  -
    zs2.
    apply evt_done. unfold tfb_optlen_post, utfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
    rewrite (proj2 (Z.leb_le SLb OLb)) by lia. cbn [orb]. do 3 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
  - zs2. zs2. zstep. br_cases K2.
    +
      apply evt_done. unfold tfb_optlen_post, utfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
      rewrite (proj2 (Z.leb_gt SLb OLb)) by lia. change (ds_strategy (tfb_X6 X5 mb)) with (ds_strategy X5). unfold Z_FIXED.
      rewrite (proj2 (Z.eqb_neq _ _) K2). cbn [orb]. do 3 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
    + zs2.
      apply evt_done. unfold tfb_optlen_post, utfR. rewrite ESL. unfold tfb_OL. rewrite EOLb, ESL. fold SLb OLb.
      change (ds_strategy (tfb_X6 X5 mb)) with (ds_strategy X5). unfold Z_FIXED.
      rewrite (proj2 (Z.eqb_eq _ _) K2), Bool.orb_true_r. do 3 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      exists hD0, hD1, hD2, hD3, hD4. unfold dsD_cells. rewrite E6o. close_cells GD.
Qed.
End Z_tr_fb8.


Module Z_tr_fb9.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fbpure.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fbpure.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require FillWinModel FlushBlockModel TreesTab RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition tfb_detect_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 m',
    ms' = MS (utfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c05c) fc None m' (seg_rom usegs)
    /\ munch [(dl_S L + 88, dl_S L + 92)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ dzs m' L (ds_strm (tfb_X0 s)).

Lemma tfb_X0_strm : forall s, 0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN ->
  ds_strm (tfb_X0 s) = cset_data_type (ds_strm s) (detect_data_type s).
Proof.
  intros s Hl Hd. unfold tfb_X0. rewrite (proj2 (Z.ltb_lt _ _) Hl), Hd. reflexivity.
Qed.

Lemma tfb_dd_store : forall (L : dlay) (s : deflate_state) (v : Z) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv usegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = v ->
  evt usegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 a2 a3 a4 (wz v) a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c058) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev.
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. destruct DZ as (p1 & p2 & p3 & resv & ZS). unfold zs_call_cells, zs_priv_cells in ZS. cbn [app] in ZS.
  unfold utfR. zs2.
  apply evt_done. unfold tfb_detect_post, utfR. do 8 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  rewrite (tfb_X0_strm s Hl Hd), Ev. exists p1, p2, p3, resv. unfold zs_call_cells, zs_priv_cells. cbn [app].
  close_cells ZS.
Qed.

Lemma tfb_dd_text : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv usegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = Z_TEXT ->
  evt usegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c054) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev. unfold utfR. zs2.
  eapply (tfb_dd_store L s 1 sp last len bufp); eassumption.
Qed.

Lemma tfb_dd_loop : forall (j : nat) (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv usegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN ->
  ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  (Z.of_nat (S j) <= 224) ->
  ((exists k, 256 - Z.of_nat (S j) <= k < 256 /\ Freq s TL k <> 0) -> detect_data_type s = Z_TEXT) ->
  ((forall k, 256 - Z.of_nat (S j) <= k < 256 -> Freq s TL k = 0) -> detect_data_type s = Z_BINARY) ->
  evt usegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) (wz (18446744073709551615 - (dl_As L + 212))) (wz (dl_As L + 212 + 4 * (256 - Z.of_nat (S j))))
               (wz (Z.of_nat (S j))) (wz (4 * (256 - Z.of_nat (S j)))) a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1c128) fc None m (seg_rom usegs)).
Proof.
  induction j as [|j IH]; intros until m; intros DZ MI LAY Hl Hd RDT RF Rj HT HB.
  all: pose proof (dlay_ranges _ LAY) as (Rs & _).
  all: match goal with |- evt _ _ (MS (utfR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?jj) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
         destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (256 - jj) ltac:(lia)) as [RDf _]; pose proof (RF (256 - jj) ltac:(lia)) as Rf end.
  all: unfold utfR; ustep TF_TRAP; zs2; rewrite zx16_small by lia; zstep; br_cases_s K.
  - eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply HT. exists (256 - Z.of_nat 1). split; [lia| exact K].
  - rewrite K. zs2. zs2. zs2. zstep. br_false. zs2.
    eapply (tfb_dd_store L s 0 sp last len bufp); try eassumption. apply HB. intros k Hk. replace k with (256 - Z.of_nat 1) by lia. exact K.
  - eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply HT. exists (256 - Z.of_nat (S (S j))). split; [lia| exact K].
  - rewrite K. zs2. zs2. zs2. zstep. br_true.
    replace (Z.of_nat (S (S j)) + -1) with (Z.of_nat (S j)) by lia.
    replace (dl_As L + 212 + 4 * (256 - Z.of_nat (S (S j))) + 4) with (dl_As L + 212 + 4 * (256 - Z.of_nat (S j))) by lia.
    replace (4 * (256 - Z.of_nat (S (S j))) + 4) with (4 * (256 - Z.of_nat (S j))) by lia.
    eapply (IH L s sp last len bufp); try eassumption; try lia.
    + intros (k & Hk & Hf). apply HT. exists k. split; [lia| exact Hf].
    + intros H. apply HB. intros k Hk. destruct (Z.eq_dec k (256 - Z.of_nat (S (S j)))) as [->|NE]; [exact K| apply H; lia].
Qed.

Ltac dd_bits n RDT RF :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 114724) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ (Z_to_bv 64 114680) _ _ _ _) =>
      zs2; zstep; first [br_true | br_false];
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 114668) _ _ _ _) => zs2; zs2; zstep; first [br_true | br_false]; let n' := eval vm_compute in (n + 1) in dd_bits n' RDT RF
      | |- evt _ _ (MS _ _ (Z_to_bv 64 114688) _ _ ?mc _) =>
          ustep TF_TRAP; zs2;
          let RD := fresh "RDb" in let Rb := fresh "Rb" in let K := fresh "Kb" in
          (lazymatch goal with MI : mem_inv usegs ?mc' |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
             destruct (RDT mc' (munch_refl _ _) (wmono_refl _ _) MI n ltac:(lia)) as [RD _] end);
          pose proof (RF n ltac:(lia)) as Rb;
          zs2; rewrite (zx16_small (arr_get _ n)) by lia; zstep; br_cases_s K;
          [ rewrite ?K; zs2; zs2; zstep; first [br_true | br_false]; clear RD Rb; let n' := eval vm_compute in (n + 1) in dd_bits n' RDT RF
          | zs2; zstep; eapply tfb_dd_store; try eassumption; apply (ddt_binary _ n); [lia| reflexivity| exact K] ]
      end
  end.

Lemma tfb_detect : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dsA m L s -> dzs m L (ds_strm s) -> mem_inv usegs m -> dlay_ok L ->
  0 < ds_level s -> - 2^31 <= cs_data_type (ds_strm s) < 2^31 ->
  ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  evt usegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bfb0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros GA DZ MI LAY Hl Rdt RDT RF.
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & _ & RS). pose proof (lo_S _ LAY) as (_ & ALS & _).
  destruct GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA). unfold dsA_cells in GA.
  pose proof DZ as (p1 & p2 & p3 & resv & ZS). unfold zs_call_cells, zs_priv_cells in ZS. cbn [app] in ZS.
  unfold utfR. zs2. ustep TF_TRAP. ustep TF_TRAP. ustep TF_TRAP. zs2. zs2. clear GA ZS.
  zstep. br_cases_s KDT.
  {
    apply evt_done. unfold tfb_detect_post, utfR. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold tfb_X0. unfold Z_UNKNOWN. rewrite (proj2 (Z.eqb_neq _ _) KDT), Bool.andb_false_r. exact DZ. }
  assert (Hd : cs_data_type (ds_strm s) = Z_UNKNOWN) by exact KDT.
  do 4 zs2. rewrite zb_lxor_ones by lia. do 3 zs2. zstep.
  dd_bits 0 RDT RF.
 
  assert (H0 : forall k, 0 <= k <= 31 -> Z.testbit DD_MASK k = true -> Freq s TL k = 0).
  { intros k Hk Hb. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    repeat (destruct C as [C|C]; [subst k; first [assumption | discriminate Hb]|]). subst k. first [assumption | discriminate Hb]. }
  zs2. ustep TF_TRAP.
  destruct (RDT _ (munch_refl _ _) (wmono_refl _ _) ltac:(eassumption) 9 ltac:(lia)) as [RDw9 _]. pose proof (RF 9 ltac:(lia)) as Rw9.
  zs2. rewrite (zx16_small (arr_get _ 9)) by lia. zstep. br_cases_s W9.
  { eapply tfb_dd_text; try eassumption. apply (ddt_text1 s H0). left. exact W9. }
  clear RDw9 Rw9.
  zs2. ustep TF_TRAP.
  destruct (RDT _ (munch_refl _ _) (wmono_refl _ _) ltac:(eassumption) 10 ltac:(lia)) as [RDw10 _]. pose proof (RF 10 ltac:(lia)) as Rw10.
  zs2. rewrite (zx16_small (arr_get _ 10)) by lia. zstep. br_cases_s W10.
  { eapply tfb_dd_text; try eassumption. apply (ddt_text1 s H0). right; left. exact W10. }
  clear RDw10 Rw10.
  zs2. ustep TF_TRAP.
  destruct (RDT _ (munch_refl _ _) (wmono_refl _ _) ltac:(eassumption) 13 ltac:(lia)) as [RDw13 _]. pose proof (RF 13 ltac:(lia)) as Rw13.
  zs2. rewrite (zx16_small (arr_get _ 13)) by lia. zstep. br_cases_s W13.
  2:{ eapply tfb_dd_text; try eassumption. apply (ddt_text1 s H0). right; right. exact W13. }
  clear RDw13 Rw13.
  pose proof (ddt_rest s H0 W9 W10 W13) as ER.
  zs2. zs2. zs2.
  replace (wz (dl_As L + 340)) with (wz (dl_As L + 212 + 4 * (256 - Z.of_nat 224))) by (f_equal; lia).
  change (wz 224) with (wz (Z.of_nat 224)). change (wz 128) with (wz (4 * (256 - Z.of_nat 224))).
  eapply (tfb_dd_loop 223 L s sp last len bufp); try eassumption; try lia.
  - intros HE. rewrite ER, (dl2_some 224 s 32); [reflexivity| | lia]. destruct HE as (k & Hk & Hf). exists k. split; [lia| exact Hf].
  - intros HZ. rewrite ER, (dl2_none 224 s 32); [reflexivity|]. intros k Hk. apply HZ. lia.
Qed.
End Z_tr_fb9.

Module Z_tr_fbmid.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require FillWinModel FlushBlockModel TreesTab.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab.
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

Lemma ltu_neg_true : forall p a, 0 <= a -> a + Z.pos p < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 (Zneg p)) = true.
Proof.
  intros p a Ha Hp. unfold bv_ltu. rewrite (Z_to_bv_eqm (Zneg p) (2^64 - Z.pos p)).
  2:{ rewrite <- (Z.mod_add (Zneg p) 1 (2^64)) by lia. f_equal. }
  rewrite !unsigned_lit by lia. apply Z.ltb_lt. lia.
Qed.

Definition tfb_mbs_post (L : dlay) (X : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz (tfb_mb X)) a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c244) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Ltac mb_done mb ACC K :=
  let E := fresh "E" in
  assert (E : tfb_mb _ = mb) by (unfold tfb_mb; apply mb_search; [lia| lia| exact ACC| right; exact K]);
  apply evt_done; unfold tfb_mbs_post, utfR; rewrite E; do 2 eexists; split; [reflexivity|]; split; [apply munch_refl|]; split; [apply wmono_refl| assumption].

Lemma tfb_mbsearch : forall (L : dlay) (X : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2748) (u16s (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39)) -> mem_inv usegs m -> dlay_ok L ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X) i < 65536) ->
  evt usegs (tfb_mbs_post L X sp last len bufp ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c0a0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR MI LAY HDL. pose proof LAY as LAY'. lay_open LAY'. unfold utfR.
  pose proof (avct_zlength (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 ltac:(lia)) as LCT.
  assert (ACC : forall j, 18 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0) by (intros; lia).
  zs2. reg_as (dl_As L + 2047 + 701) (dl_As L + 2748). zs2.
  zstep. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| symmetry; rewrite ltu_neg_true by lia; reflexivity] end.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 15 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 15 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 15 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 15 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 15)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 18 ACC K]; clear RD RV.
  assert (ACC18 : forall j, 18 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 18) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC18 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 1 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 1 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 1 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 1 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 1)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 17 ACC K]; clear RD RV.
  assert (ACC17 : forall j, 17 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 17) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC17 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 14 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 14 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 14 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 14 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 14)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 16 ACC K]; clear RD RV.
  assert (ACC16 : forall j, 16 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 16) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC16 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 2 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 2 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 2 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 2 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 2)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 15 ACC K]; clear RD RV.
  assert (ACC15 : forall j, 15 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 15) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC15 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 13 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 13 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 13 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 13 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 13)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 14 ACC K]; clear RD RV.
  assert (ACC14 : forall j, 14 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 14) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC14 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 3 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 3 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 3 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 3 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 3)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 13 ACC K]; clear RD RV.
  assert (ACC13 : forall j, 13 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 13) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC13 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 12 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 12 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 12 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 12 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 12)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 12 ACC K]; clear RD RV.
  assert (ACC12 : forall j, 12 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 12) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC12 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 4 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 4 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 4 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 4 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 4)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 11 ACC K]; clear RD RV.
  assert (ACC11 : forall j, 11 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 11) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC11 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 11 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 11 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 11 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 11 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 11)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 10 ACC K]; clear RD RV.
  assert (ACC10 : forall j, 10 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 10) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC10 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 5 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 5 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 5 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 5 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 5)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 9 ACC K]; clear RD RV.
  assert (ACC9 : forall j, 9 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 9) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC9 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 10 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 10 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 10 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 10 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 10)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 8 ACC K]; clear RD RV.
  assert (ACC8 : forall j, 8 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 8) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC8 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 6 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 6 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 6 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 6 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 6)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 7 ACC K]; clear RD RV.
  assert (ACC7 : forall j, 7 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 7) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC7 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 9 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 9 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 9 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 9 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 9)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 6 ACC K]; clear RD RV.
  assert (ACC6 : forall j, 6 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 6) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC6 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 7 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 7 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 7 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 7 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 7)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 5 ACC K]; clear RD RV.
  assert (ACC5 : forall j, 5 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 5) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC5 into ACC.
  zs2. ustep TF_TRAP.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 8 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 8 + 1))) ARR (avct_nth_dl (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39 8 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 8 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 8)) by lia. zstep. br_cases K; [| zs2; zstep; mb_done 4 ACC K]; clear RD RV.
  assert (ACC4 : forall j, 4 - 1 < j <= 18 -> Len X TB (arr_get bl_order_a j) = 0)
    by (intros j Hj; destruct (Z.eq_dec j 4) as [->|]; [exact K| apply ACC; lia]). clear ACC K. rename ACC4 into ACC.
  pose proof (u16arr_read usegs m (dl_As L + 2748) (avct (ds_bl_tree_fc X) (ds_bl_tree_dl X) 39) (2 * 0 + 1) _ (wa (dl_As L + 2748 + 2 * (2 * 0 + 1))) ARR (avct_nth_dl _ _ 39 0 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  pose proof (HDL 0 ltac:(lia)) as RV.
  zs2. rewrite (zx16_small (arr_get (ds_bl_tree_dl X) 0)) by lia. zs2. zs2.
  destruct (Z.eq_dec (arr_get (ds_bl_tree_dl X) 0) 0) as [K|K].
  - rewrite K. change (Z.lxor (Z.b2z (0 <? 1)) 3) with 2.
    assert (E : tfb_mb X = 2) by (unfold tfb_mb; apply mb_search; [lia| lia| intros j Hj; destruct (Z.eq_dec j 3) as [->|]; [exact K| apply ACC; lia]| left; reflexivity]).
    apply evt_done. unfold tfb_mbs_post, utfR. rewrite E. do 2 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| assumption].
  - replace (arr_get (ds_bl_tree_dl X) 0 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). change (Z.lxor (Z.b2z false) 3) with 3.
    mb_done 3 ACC K.
Qed.
End Z_tr_fbmid.

Module Z_tr_scan2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_fbpure Z_tr_scan1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fbpure OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Definition scan_tree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (dl_As L + 212, dl_As L + 2904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ DST m' L (scan_tree s t mc).

Lemma scan_tree_unfold : forall s t mc f, Z.to_nat (mc + 1) = S f -> (t = TL \/ t = TD) ->
  scan_tree s t mc = scan_tree_loop (S f) (set_bl_tree_fc (set_Len s t (mc + 1) 65535) (ds_bl_tree_fc s)) t mc 0 (-1) (Len s t 0) 0
                       (if Len s t 0 =? 0 then 138 else 7) (if Len s t 0 =? 0 then 3 else 4).
Proof.
  intros s t mc f Ef Ht. unfold scan_tree. rewrite Ef.
  destruct Ht as [-> | ->];
    (change (ds_bl_tree_fc s) with (ds_bl_tree_fc (set_Len s _ (mc + 1) 65535)) at 1 || idtac);
    [ change (ds_bl_tree_fc s) with (ds_bl_tree_fc (set_Len s TL (mc + 1) 65535))
    | change (ds_bl_tree_fc s) with (ds_bl_tree_fc (set_Len s TD (mc + 1) 65535)) ];
    rewrite sbf_self; destruct (_ =? 0); reflexivity.
Qed.

Lemma scan_tree_spec : forall (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_SC_STACK -> dlay_below L lo (bv_unsigned sp) ->
  (t = TL \/ t = TD) -> 0 <= mc -> mc + 1 < tsize t ->
  (forall i, 0 <= i < tsize t -> 0 <= arr_get (tree_dl s t) i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get (tree_dl s t) i <= 15) ->
  a0 = wz (dl_As L) -> a1 = wz (dl_As L + toff t) -> a2 = wz mc ->
  evt usegs (scan_tree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s t mc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_SCAN_TREE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST MI STK LO BEL Ht Rmc RmcN HDL HLEN Ea0 Ea1 Ea2.
  open_DST ST. pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  destruct (Z.to_nat (mc + 1)) as [|f] eqn:Ef; [lia|].
  destruct Ht as [-> | ->]; cbn [toff tsize tree_dl tree_fc] in *.
  -
    unfold dlt, u16arr in Glt. unfold dbt, u16arr in Gbt.
    eapply evt_mono.
    { eapply (scan_tree_body L (dl_As L + 212) 573 mc (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_bl_tree_dl s) (set_Len s TL (mc + 1) 65535) TL (ds_bl_tree_fc s) lo
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Glt. } 1:{ exact (ln_ltd _ LENS). } 1:{ exact Gbt. } 1:{ exact (ln_btf _ LENS). } 1:{ exact MI. } 1:{ exact LAY. }
      1:{ exact STK. } 1:{ exact LO. } 1:{ exact BEL. } 1:{ Z.div_mod_to_equations. lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact RmcN. }
      1:{ intros i. reflexivity. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Ea0. } 1:{ exact Ea1. } 1:{ exact Ea2. } }
    intros ms' P. unfold scan_tree_body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & b' & m' & -> & MU & WM & MI' & STK' & ART & ARB & LNB' & ER).
    tr_groups MU WM.
    unfold scan_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite (scan_tree_unfold s TL mc f Ef ltac:(left; reflexivity)). change (Len s TL 0) with (arr_get (ds_dyn_ltree_dl s) 0). rewrite Ef in ER. rewrite ER.
    constructor; [exact GA| exact GB| exact GC| exact GD| unfold dlt, u16arr; exact ART| exact Gdt| unfold dbt, u16arr; exact ARB| exact Gblc
      | exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    destruct LENS; constructor; cbn -[arr_len Z.add]; rewrite ?arr_len_set; first [assumption| lia].
  -
    unfold ddt, u16arr in Gdt. unfold dbt, u16arr in Gbt.
    eapply evt_mono.
    { eapply (scan_tree_body L (dl_As L + 2504) 61 mc (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_dl s) (set_Len s TD (mc + 1) 65535) TD (ds_bl_tree_fc s) lo
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Gdt. } 1:{ exact (ln_dtd _ LENS). } 1:{ exact Gbt. } 1:{ exact (ln_btf _ LENS). } 1:{ exact MI. } 1:{ exact LAY. }
      1:{ exact STK. } 1:{ exact LO. } 1:{ exact BEL. } 1:{ Z.div_mod_to_equations. lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact RmcN. }
      1:{ intros i. reflexivity. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Ea0. } 1:{ exact Ea1. } 1:{ exact Ea2. } }
    intros ms' P. unfold scan_tree_body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & b' & m' & -> & MU & WM & MI' & STK' & ART & ARB & LNB' & ER).
    tr_groups MU WM.
    unfold scan_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite (scan_tree_unfold s TD mc f Ef ltac:(right; reflexivity)). change (Len s TD 0) with (arr_get (ds_dyn_dtree_dl s) 0). rewrite Ef in ER. rewrite ER.
    constructor; [exact GA| exact GB| exact GC| exact GD| exact Glt| unfold ddt, u16arr; exact ART| unfold dbt, u16arr; exact ARB| exact Gblc
      | exact Gheap| exact Gdep| exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    destruct LENS; constructor; cbn -[arr_len Z.add]; rewrite ?arr_len_set; first [assumption| lia].
Qed.
End Z_tr_scan2.

Module Z_tr_fb10.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_emit Z_ukit Z_tr_cb4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_st4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fbpure.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_cb4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_cb5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_st4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb7 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb8 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb9 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fbmid OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_scan2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fbpure.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab TreeModel RefSendTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13 CompressModel GenBitlenModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreesTab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.CompressModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel.
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
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L X4 -> dzs m L c -> ds_strm X4 = c -> mem_inv usegs m -> relro_clean m0 ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe X4 TB -> X5 = build_tree X4 TB -> mb = tfb_mb X5 -> X6 = tfb_X6 X5 mb -> d = tfb_branch X6 buf len ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 65536) ->
  0 <= ds_opt_len X5 < 2^63 -> 0 <= ds_static_len X5 < 2^63 -> 0 <= ds_strategy X5 <= 4 ->
  BINV 65536 X6 ->
  match d with 0 => RefFlushBlk13.stat_ok 65536 last X6 | 1 => OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk12.dyn_ok 65536 last X6 mb | _ => RefFlushBlk13.sto_ok 65536 X6 buf len last end ->
  (d = 1 -> ubsan_dyn X6 mb) ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X6 mb buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tfb_emit d X6 mb buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c094) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ ESTRM MI RC MU WM FR STK LO AL BEL BTS E5 Emb E6 Ed RBd Rol Rsl Rst BI6 SAFE UB POK BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO.
  pose proof BEL as BEL0. below_open BEL0.
  assert (LAY : dlay_ok L) by (destruct ST; assumption). pose proof LAY as LAY'. lay_open LAY'.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  assert (Rmb : 0 <= mb <= 18) by (rewrite Emb; unfold tfb_mb; pose proof (build_bl_tree_loop_range 17 X5 18 ltac:(lia)); lia).
  unfold utfR. zs2. zs2. zs2. name_mem m1.
  pose proof (munch_refl (tfWz L lo sp) m1) as MUz. pose proof (wmono_refl usegs m1) as WMz.
  call (BT L X4 TB lo).
  1:{ exact ST. } 1:{ exact MI. } 1:{ eapply relro_tfW; try eassumption; lia. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_BT_STACK. lia. }
  1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. } 1:{ exact BTS. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST. rewrite <- E5 in *. rewrite ESP in *. name_mem m2.
  match goal with H : DST m2 L X5 |- _ => destruct H as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS _] end.
  pose proof Gbt as Gbt'. unfold dbt, u16arr in Gbt'.
  pose proof (munch_refl [] m2) as MUm. pose proof (wmono_refl usegs m2) as WMm.
  call (tfb_mbsearch L X5 sp last len (buf_ptr L buf)).
  1:{ exact Gbt'. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact RBd. }
  rewrite <- Emb. clear Gbt'. tr_groups MUm WMm. clear MUm WMm. name_mem m3.
  pose proof (munch_refl [(dl_As L + 5912, dl_As L + 5920)] m3) as MUo. pose proof (wmono_refl usegs m3) as WMo.
  unfold utfR.
  call (tfb_optlen L X5 sp last len (buf_ptr L buf) mb).
  1:{ exact GA. } 1:{ exact GD. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact Rol. } 1:{ exact Rsl. } 1:{ exact Rst. } 1:{ exact Rmb. }
  clear GD. tr_groups MUo WMo. clear MUo WMo. rewrite <- E6 in *. name_mem m4.
  assert (ST6 : DST m4 L X6).
  { rewrite E6 in *. constructor; [exact GA| exact GB| exact GC| assumption| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| | exact LAY].
    destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13]. constructor; assumption. }
  clear GA GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold utfR.
  eapply (tfb_emit_all L X6 Rfin c buf last len mb (tfb_SL X6) (tfb_OL X6) d lo m0);
    [exact ST6| exact DZ| | eassumption| exact MU| exact WM| exact FR| eassumption| unfold Z_TRFB_STACK; lia| exact BEL| exact BI6| exact BOK| exact Rlen| exact Rl| exact Rmb
    | apply tfb_SL_range| apply tfb_OL_range| rewrite Ed; apply tfb_branch_eq| exact SAFE| exact UB| exact POK| exact ER].
  rewrite E6, E5. change (ds_strm (tfb_X6 (build_tree X4 TB) mb)) with (ds_strm (build_tree X4 TB)). rewrite (k_build_tree _ _ _ keeps_strm). exact ESTRM.
Qed.

Lemma tfb_hi1 : forall (L : dlay) (s X0 X1 X2 X3 X4 X5 X6 Rfin : deflate_state) (buf : option Z) (last len mb d lo : Z) (m0 : mem)
    (ra0 s0o s1o s2o s3o s4o s5o s6o sp : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> dzs m L (ds_strm s) -> mem_inv usegs m -> relro_clean m0 ->
  munch (tfW L lo sp) m0 m -> wmono usegs m0 m ->
  rw_cells usegs m (bv_unsigned sp + -64) (tf_frame ra0 s0o s1o s2o s3o s4o s5o s6o) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  0 < ds_level s -> - 2^31 <= cs_data_type (ds_strm s) < 2^31 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  X0 = tfb_X0 s -> X1 = build_tree X0 TL -> X2 = build_tree X1 TD -> X3 = scan_tree X2 TL (ds_l_max_code X2) -> X4 = scan_tree X3 TD (ds_d_max_code X3) ->
  X5 = build_tree X4 TB -> mb = tfb_mb X5 -> X6 = tfb_X6 X5 mb -> d = tfb_branch X6 buf len ->
  hi_body 65536 X0 X1 X2 X3 X4 X5 X6 mb d buf len last -> (d = 1 -> ubsan_dyn X6 mb) -> BINV 65536 X6 ->
  RefFlushBlk13.post_ok 65536 last (tfb_emit d X6 mb buf len last) ->
  fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  Rfin = tfb_fin last (tfb_emit d X6 mb buf len last) ->
  evt usegs (tfb_post_gen ra0 sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc L Rfin lo m0)
      (MS (utfR L sp last len (buf_ptr L buf) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bfb0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST DZ MI RC MU WM FR STK LO AL BEL Hlev Rdt RF E0 E1 E2 E3 E4 E5 Emb E6 Ed HI UB BI6 POK BOK Rlen Rl ER.
  unfold Z_TRFB_STACK in LO. unfold tf_frame in FR. pose proof BEL as BEL0. below_open BEL0.
  assert (LAY : dlay_ok L) by (destruct ST; assumption).
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  destruct HI as (BTS0 & BTS1 & (Rlm0 & Rlm1) & RLl & RLn & _ & (Rdm0 & Rdm1) & RDl & RDn & _ & BTS4 & (_ & RBd) & Rol & Rsl & Rst & SAFE).
  assert (ES4 : ds_strm X4 = ds_strm X0).
  { rewrite E4, (k_scan_tree _ _ _ keeps_strm), E3, (k_scan_tree _ _ _ keeps_strm), E2, (k_build_tree _ _ _ keeps_strm), E1, (k_build_tree _ _ _ keeps_strm). reflexivity. }
  pose proof (lo_Ss _ LAY) as SEPSs. unfold apart in SEPSs. pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & Rb & RS).
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MUd. pose proof (wmono_refl usegs m) as WMd.
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
  unfold utfR. zs2. zs2. zs2. name_mem m2.
  pose proof (munch_refl (tfWz L lo sp) m2) as MUz. pose proof (wmono_refl usegs m2) as WMz.
  call (BT L X0 TL lo).
  1:{ exact ST0. } 1:{ eassumption. } 1:{ eapply relro_tfW; try eassumption; unfold Z_TRFB_STACK in LO; lia. } 1:{ rewrite ESP. exact STK. }
  1:{ rewrite ESP. unfold Z_BT_STACK, Z_TRFB_STACK in *. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BTS0. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST0. rewrite <- E1 in *. rewrite ESP in *. name_mem m3.
  unfold utfR. zs2. zs2. zs2. name_mem m4.
  pose proof (munch_refl (tfWz L lo sp) m4) as MUz. pose proof (wmono_refl usegs m4) as WMz.
  call (BT L X1 TD lo).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eapply relro_tfW; try eassumption; unfold Z_TRFB_STACK in LO; lia. } 1:{ rewrite ESP. eassumption. }
  1:{ rewrite ESP. unfold Z_BT_STACK, Z_TRFB_STACK in *. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ exact BTS1. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz. rewrite <- E2 in *. rewrite ESP in *. name_mem m5.
  match goal with H : DST m5 L X2 |- _ => pose proof H as ST2; destruct H as [_ GB _ _ _ _ _ _ _ _ _ _ _ _ _ _] end.
  pose proof GB as (hB1 & hB2 & hB3 & GBr). unfold dsB_cells in GBr.
  unfold utfR. zs2. clear GB GBr. zs2. zs2. zs2. name_mem m6.
  pose proof (munch_refl (tfWz L lo sp) m6) as MUz. pose proof (wmono_refl usegs m6) as WMz.
  call (scan_tree_spec L X2 TL (ds_l_max_code X2) lo).
  1:{ exact ST2. } 1:{ eassumption. } 1:{ rewrite ESP. eassumption. } 1:{ rewrite ESP. unfold Z_SC_STACK. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ left; reflexivity. } 1:{ exact Rlm0. } 1:{ cbn [tsize]. exact Rlm1. } 1:{ cbn [tsize]. exact RLn. } 1:{ exact RLl. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST2. rewrite <- E3 in *. rewrite ESP in *. name_mem m7.
  match goal with H : DST m7 L X3 |- _ => pose proof H as ST3; destruct H as [_ GB _ _ _ _ _ _ _ _ _ _ _ _ _ _] end.
  pose proof GB as (hC1 & hC2 & hC3 & GBr). unfold dsB_cells in GBr.
  unfold utfR. zs2. clear GB GBr. zs2. zs2. zs2. name_mem m8.
  pose proof (munch_refl (tfWz L lo sp) m8) as MUz. pose proof (wmono_refl usegs m8) as WMz.
  call (scan_tree_spec L X3 TD (ds_d_max_code X3) lo).
  1:{ exact ST3. } 1:{ eassumption. } 1:{ rewrite ESP. eassumption. } 1:{ rewrite ESP. unfold Z_SC_STACK. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
  1:{ right; reflexivity. } 1:{ exact Rdm0. } 1:{ cbn [tsize]. exact Rdm1. } 1:{ cbn [tsize]. exact RDn. } 1:{ exact RDl. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  tr_groups MUz WMz. clear MUz WMz ST3. rewrite <- E4 in *. rewrite ESP in *. name_mem m9.
  unfold utfR.
  match goal with HZ : dzs m9 L (ds_strm X0) |- _ =>
    eapply (tfb_hi2 L X4 X5 X6 Rfin (ds_strm X0) buf last len mb d lo m0);
    [eassumption| exact HZ| exact ES4| eassumption| exact RC| exact MU| exact WM| exact FR| eassumption| unfold Z_TRFB_STACK; lia| exact AL| exact BEL
    | exact BTS4| exact E5| exact Emb| exact E6| exact Ed| exact RBd| exact Rol| exact Rsl| exact Rst| exact BI6| exact SAFE| exact UB| exact POK| exact BOK| exact Rlen| exact Rl| exact ER] end.
Qed.

End WithBuildTree.
End Z_tr_fb10.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_stored OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb2.Z_tr_fb1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb8 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11.Z_tr_fb10.
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


Definition fb_ubsan (s : deflate_state) (buf : option Z) (len last : Z) : Prop :=
  0 < ds_level s ->
  let X0 := tfb_X0 s in
  let X1 := build_tree X0 TL in
  let X2 := build_tree X1 TD in
  let X3 := scan_tree X2 TL (ds_l_max_code X2) in
  let X4 := scan_tree X3 TD (ds_d_max_code X3) in
  let X5 := build_tree X4 TB in
  let mb := tfb_mb X5 in
  let X6 := tfb_X6 X5 mb in
  tfb_branch X6 buf len = 1 -> ubsan_dyn X6 mb.

Definition tr_flush_block_stmtU : Prop :=
  forall (L : dlay) (s : deflate_state) (buf : option Z) (len last lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L s -> mem_inv usegs m -> relro_clean m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) ->
  BINV DS_PEND s -> fb_safe s buf len last -> fb_ubsan s buf len last -> fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  a0 = wz (dl_As L) -> a1 = wz (match buf with Some off => dl_Aw L + off | None => 0 end) -> a2 = wz len -> a3 = wz last ->
  evt usegs (tr_flush_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s buf len last lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_FLUSH_BLOCK) fc None m (seg_rom usegs)).

Lemma tr_flush_block_of_ubsan :
  (forall s buf len last, fb_safe s buf len last -> BINV DS_PEND s -> fb_ubsan s buf len last) ->
  tr_flush_block_stmtU -> tr_flush_block_stmt.
Proof.
  intros HU SU. unfold tr_flush_block_stmt. intros until m. intros DR MI RC STK LO AL BEL BI FBS.
  apply (SU L s buf len last lo); try assumption. apply HU; assumption.
Qed.

Lemma tfb_pre_hi : forall s buf len last, 0 < ds_level s ->
  exists X0 X1 X2 X3 X4 X5 X6 mb d,
    X0 = tfb_X0 s /\ X1 = build_tree X0 TL /\ X2 = build_tree X1 TD /\ X3 = scan_tree X2 TL (ds_l_max_code X2) /\ X4 = scan_tree X3 TD (ds_d_max_code X3)
    /\ X5 = build_tree X4 TB /\ mb = tfb_mb X5 /\ X6 = tfb_X6 X5 mb /\ d = tfb_branch X6 buf len
    /\ tfb_pre s buf len last = tfb_emit d X6 mb buf len last
    /\ (RefFlushBlk13.hi_ok 65536 s buf len last -> hi_body 65536 X0 X1 X2 X3 X4 X5 X6 mb d buf len last)
    /\ (fb_ubsan s buf len last -> d = 1 -> ubsan_dyn X6 mb)
    /\ bits4 X6 = bits4 s.
Proof.
  intros s buf len last Hl. do 9 eexists.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; [|split]].
  - unfold tfb_pre. rewrite (proj2 (Z.ltb_lt _ _) Hl). reflexivity.
  - intros H. exact H.
  - intros H. exact (H Hl).
  - exact (RefFlushBlk13.bits4_X6' s).
Qed.

Section WithBuildTree.
Hypothesis BT : build_tree_stmt.

Lemma tr_flush_block_specU : tr_flush_block_stmtU.
Proof.
  unfold tr_flush_block_stmtU. intros until m. intros DR MI RC STK LO AL BEL BI FBS UBS BOK Rlen Rl -> -> -> ->.
  rewrite tfb_post_gen_eq, tr_flush_block_eq.
  destruct DR as [DZ ST]. unfold Z_TR_FLUSH_BLOCK.
  pose proof BEL as BEL0. below_open BEL0.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY].
  pose proof LAY as LAY'. lay_open LAY'. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  unfold RefFlushBlk13.fb_safe in FBS. cbv zeta in FBS. rewrite (ln_pend _ LENS) in FBS. destruct FBS as (Rlev & Rdt & _ & RF & POK & HILO).
  pose proof (munch_refl (tfW L lo sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl usegs m) as WMs.
  assert (LO' : lo <= bv_unsigned sp - 512) by exact LO.
  carve_frame 64%nat STK.
  do 9 zstep.
  tr_groups MUs WMs. clear MUs WMs. name_mem m1.
  pose proof GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA'). unfold dsA_cells in GA'.
  uwalk 0x1bfac TF_TRAP. at_pc 0x1bfac.
  clear GA'.
  assert (ST : DST m1 L s) by (constructor; assumption).
  clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  zstep. br_cases K.
  -
    rewrite (proj2 (Z.ltb_ge _ _)) in HILO by lia. unfold tfb_pre in POK |- *. rewrite (proj2 (Z.ltb_ge 0 (ds_level s))) in POK |- * by lia.
    do 4 zs2.
    replace (wz (len + 5)) with (wz (wrap64 (len + 5))) by (apply Z_to_bv_eqm; rewrite wrap64_mod, Z.mod_mod by lia; reflexivity).
    unfold utfR in *.
    eapply (tfb_emit_all L s _ (ds_strm s) buf last len 0 (wrap64 (len + 5)) (wrap64 (len + 5))
              (if (wrap64 (len + 4) <=? wrap64 (len + 5)) && is_some buf then 2 else 0) lo m);
      [exact ST| exact DZ| reflexivity| eassumption| exact MU| exact WM| exact FR| exact STK| exact LO| exact BEL| exact BI| exact BOK| exact Rlen| exact Rl| lia
      | apply wrap64_range| apply wrap64_range| rewrite Z.eqb_refl; reflexivity| | destruct (_ && _); intros C; discriminate C| exact POK| reflexivity].
    unfold RefFlushBlk13.lo_ok in HILO. destruct buf as [off|]; cbn [is_some].
    + destruct BOK as [Ro1 Ro2]. rewrite !wrap64_id by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb]. exact HILO.
    + rewrite Bool.andb_false_r. exact HILO.
  -
    assert (Hlev : 0 < ds_level s) by lia.
    rewrite (proj2 (Z.ltb_lt _ _) Hlev) in HILO.
    destruct (tfb_pre_hi s buf len last Hlev) as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & mb & d & E0 & E1 & E2 & E3 & E4 & E5 & Emb & E6 & Ed & EPRE & HIB & UBI & B6).
    rewrite EPRE in POK |- *.
    unfold utfR in *.
    eapply (tfb_hi1 BT L s X0 X1 X2 X3 X4 X5 X6 _ buf last len mb d lo m);
      [exact ST| exact DZ| eassumption| exact RC| exact MU| exact WM| exact FR| exact STK| exact LO| exact AL| exact BEL| exact Hlev| exact Rdt| exact RF
      | exact E0| exact E1| exact E2| exact E3| exact E4| exact E5| exact Emb| exact E6| exact Ed| apply HIB; exact HILO| exact (UBI UBS)| eapply BINV_bits4; [exact B6| exact BI]
      | exact POK| exact BOK| exact Rlen| exact Rl| reflexivity].

Qed.

End WithBuildTree.
