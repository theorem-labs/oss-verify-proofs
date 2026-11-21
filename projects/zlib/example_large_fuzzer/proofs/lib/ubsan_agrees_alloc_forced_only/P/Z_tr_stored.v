(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_emit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition tsb_head_post (L : dlay) (s : deflate_state) (last len : Z)
    (ra sp gp tp t0 t1 t2 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a3 a4 a5 a6 a7 wbb wbv m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz len) (wz (dl_As L)) (wz 65535) a1 (wz (dl_As L + 5936)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1afd8) fc None m' (seg_rom psegs)
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
          F (wz 0x1aed0) fc None m (seg_rom psegs)).
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

Definition Z_TR_STORED : Z := 0x1aec0.

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
