From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import memchr_c memcpy_c fuzz_alloc_live_c
  fuzz_alloc_peak_reset_c SlotDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
Import ListNotations.
Open Scope Z_scope.

Lemma sa_memchr_res : forall p pl, memchr_res p 0 (Z.of_nat (length pl)) pl =
  match find_byte 0 pl with Some i => p + Z.of_nat i | None => 0 end.
Proof. intros p pl. unfold memchr_res. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.

Lemma sa_memchr_ok : forall p pl, memchr_ok p 0 (Z.of_nat (length pl)) pl.
Proof.
  intros p pl. unfold memchr_ok. rewrite Nat2Z.id, firstn_all.
  destruct (find_byte 0 pl); [left|]; lia.
Qed.

Lemma sa_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sa_ro_hi : forall a, 0x55000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
  rewrite (HsKindB.find_segment_above rsegs 0x55000 a 1 HsKindB.rsegs_top) by lia. reflexivity.
Qed.

Lemma sa_rw_rel : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

Lemma sa_stk_norm : forall m lo hi, ro_agree rsegs m -> 0x55000 <= lo ->
  stk rsegs m lo hi -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RA Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw Hr]. pose proof (mem_rel_normalize rsegs m RA) as HR. split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) (wa a) HR (sa_ro_hi a ltac:(lia))). exact Hw.
  - rewrite <- (mrd_rel rsegs m (normalize rsegs m) (wa a) HR). exact Hr.
Qed.

Lemma sa_rel_shape : forall s R F pc fc m0 ro, ms_rel rsegs s (MS R F pc fc None m0 ro) ->
  s = MS R F pc fc None (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [R' F' pc' svc' rv' fc' m' ro'] R F pc fc m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma sa_find_in : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c end.
  - injection H as <-. left. reflexivity.
  - right. eapply IH. exact H.
Qed.

Lemma sa_rd : forall m x, wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x H. unfold mrd. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|].
  unfold wview in H. rewrite E in H.
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:FS; [|exfalso; apply H; reflexivity].
  destruct (seg_writable seg) eqn:W; [|exfalso; apply H; reflexivity].
  assert (C : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg (sa_find_in _ _ _ _ FS)). rewrite W in C. cbn in C. rewrite C.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at _ _) as [b|]; [exists b; reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma sa_rw_sub : forall m a n a' k, wr_at rsegs m a n -> a <= a' -> a' + Z.of_nat k <= a + n ->
  exists junk, rw_cells rsegs m a' [CB k junk].
Proof.
  intros m a n a' k (H1 & H2 & H) Ha Hk.
  assert (S : stk rsegs m a' (a' + Z.of_nat k)).
  { split; [lia|]. split; [lia|]. intros x Hx.
    assert (W : wview rsegs m (wa x) <> None) by (replace x with (a + (x - a)) by lia; apply H; lia).
    split; [exact W | apply sa_rd, W]. }
  destruct (stk_carve rsegs m a' (a' + Z.of_nat k) k S ltac:(lia)) as [_ (junk & J)].
  exists junk. replace (a' + Z.of_nat k - Z.of_nat k) with a' in J by lia. exact J.
Qed.

Lemma sa_le1 : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 (z mod 256)].
Proof.
  intros z Hz. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. f_equal.
  apply Z_to_bv8_mod; rewrite Zmod_mod; reflexivity.
Qed.

Lemma sa_peak_rw : forall i, 0 <= i < 8 -> ro_addr rsegs (wa (0x33458 + i)) = false.
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma sA_inv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (pl : list byte),
  memchr_contract ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> mem_inv rsegs m ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  0 < p -> p + Z.of_nat (length pl) <= lo ->
  bytes_at rsegs m p pl ->
  evt rsegs (fun ms' => exists m',
      munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      ((0x300000 < slot_nn pl /\
        exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom rsegs)) \/
       (slot_nn pl <= 0x300000 /\
        rw_cells rsegs m' (bv_unsigned sp - 48) [C8 (Z_to_bv 64 (2 ^ 64 - 1)); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
        exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          ms' = MS (mkR (Z_to_bv 64 0x1336c) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0' t1' t2' s0
                        (Z_to_bv 64 (slot_nn pl)) (Z_to_bv 64 p) (Z_to_bv 64 (slot_nn pl)) a2' a3' a4' a5' a6' a7'
                        (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x13440) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1331c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p pl
    MEMCHR ST LO MI E0 E1 Hp Hpl PL.
  subst a0 a1.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  unfold slot_nn.
  carve_frame 48%nat ST.
  do 11 zstep.
  call (MEMCHR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pl).
  1: rewrite unsigned_lit by lia; exact PL.
  1: rewrite !unsigned_lit by lia; rewrite Zmod_0_l; apply sa_memchr_ok.
  1: exact MI.
  rewrite (unsigned_lit p), (unsigned_lit (Z.of_nat (length pl))), (unsigned_lit 0) by lia.
  rewrite Zmod_0_l, sa_memchr_res.
  destruct (find_byte 0 pl) as [i|] eqn:FB.
  - destruct (find_byte_Some _ _ _ FB) as (Hi & _).
    zstep. if_cases BZ; zify_cond BZ; [exfalso; Z.div_mod_to_equations; lia|].
    zstep.
    replace (p + Z.of_nat i - p) with (Z.of_nat i) by lia.
    do 4 zstep.
    if_cases BL; zify_cond BL.
    + do 8 zstep.
      apply evt_done. eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      left. split; [lia|]. do 14 eexists. reflexivity.
    + do 3 zstep.
      apply evt_done. eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      right. split; [lia|]. split; [eassumption|]. do 13 eexists. reflexivity.
  - zstep. if_cases BZ; zify_cond BZ; [|exfalso; lia].
    do 4 zstep.
    if_cases BL; zify_cond BL.
    + do 8 zstep.
      apply evt_done. eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      left. split; [lia|]. do 14 eexists. reflexivity.
    + do 3 zstep.
      apply evt_done. eexists. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      right. split; [lia|]. split; [eassumption|]. do 13 eexists. reflexivity.
Qed.

Lemma sA_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (pl : list byte),
  memchr_contract ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> 0x55000 <= lo ->
  ro_agree rsegs m ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  0 < p -> p + Z.of_nat (length pl) <= lo ->
  bytes_at rsegs m p pl ->
  evt rsegs (fun ms' => exists m',
      munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
      ((0x300000 < slot_nn pl /\
        exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom rsegs)) \/
       (slot_nn pl <= 0x300000 /\
        rw_cells rsegs m' (bv_unsigned sp - 48) [C8 (Z_to_bv 64 (2 ^ 64 - 1)); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
        exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          ms' = MS (mkR (Z_to_bv 64 0x1336c) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0' t1' t2' s0
                        (Z_to_bv 64 (slot_nn pl)) (Z_to_bv 64 p) (Z_to_bv 64 (slot_nn pl)) a2' a3' a4' a5' a6' a7'
                        (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 0x13440) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1331c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p pl
    MEMCHR ST LO HL RA E0 E1 Hp Hpl PL.
  pose proof (mem_rel_normalize rsegs m RA) as HR0.
  eapply evt_mono.
  { apply (evt_normalize rsegs); [exact sa_wx | exact RA |].
    eapply sA_inv; [exact MEMCHR | exact (sa_stk_norm m lo _ RA HL ST) | exact LO | apply mem_inv_normalize |
      exact E0 | exact E1 | exact Hp | exact Hpl | exact (bytes_at_normalize rsegs m p pl RA PL)]. }
  intros s (s0' & (m0 & MU & WM & _ & POST) & REL & ROS).
  destruct POST as [(Hc & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & E)
                   |(Hc & FR & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & E)];
    subst s0';
    destruct (sa_rel_shape s _ _ _ _ _ _ REL) as [Es HR];
    exists (ms_mem s);
    (split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS MU)|]);
    (split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS WM)|]);
    (split; [exact (ro_agree_same rsegs m (ms_mem s) RA ROS)|]).
  - left. split; [exact Hc|]. do 14 eexists. exact Es.
  - right. split; [exact Hc|]. split; [exact (sa_rw_rel _ _ _ _ HR FR)|]. do 13 eexists. exact Es.
Qed.

Lemma sC_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text nn : Z) (db j : list byte) (live : word),
  fuzz_alloc_live_contract -> fuzz_alloc_peak_reset_contract ->
  s0 = Z_to_bv 64 text -> s1 = Z_to_bv 64 nn ->
  0 <= nn <= 3 * 2 ^ 20 -> Z.of_nat (length db) = nn ->
  4096 <= text -> text + nn + 1 < 2 ^ 64 -> text + nn + 1 <= 0x33450 \/ 0x33450 + 24 <= text ->
  bytes_at rsegs m text db -> rw_cells rsegs m (text + nn) [CB 1 j] ->
  bytes_at rsegs m 0x33450 (le8 live) -> wr_at rsegs m 0x33458 8 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x133b0) sp gp tp t0' t1' t2' (Z_to_bv 64 text) (Z_to_bv 64 nn) (Z_to_bv 64 text) sp
                    a2' a3' a4' a5' a6' a7' s2 live s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14e90) fc None m' (seg_rom rsegs) /\
      munch [(text + nn, text + nn + 1); (0x33458, 0x33458 + 8)] m m' /\ wmono rsegs m m' /\
      bytes_at rsegs m' text (db ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m' 0x33458 (le8 live))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13390) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    text nn db j live FAL FAPR E0 E1 Hnn Hl Ht Htop Hg BY R1 LV PK.
  subst s0 s1.
  pose proof (munch_refl [(text + nn, text + nn + 1); (0x33458, 0x33458 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep.
  remember (text + nn) as tn eqn:Etn.
  try rewrite <- Etn in R1. try rewrite <- Etn in MU.
  zstep. try (rewrite (sa_le1 0) by lia; mem_after_store).
  destruct R1 as [[_ B1] _]. cbn [cells_bytes cbytes app] in B1.
  zstep.
  eapply evt_cut; [eapply FAL; exact LV|].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x1339c)) with (Z_to_bv 64 0x1339c) by (apply bv_eq; vm_compute; reflexivity).
  zstep. zstep.
  eapply evt_cut; [eapply FAPR; [exact LV | exact PK]|].
  intros ms' (a0' & a1' & m2 & E & PK2 & MUc & WMc).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x133a4)) with (Z_to_bv 64 0x133a4) by (apply bv_eq; vm_compute; reflexivity).
  unfold G_PEAK in MUc, PK2.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m2 MUc WMc end.
  do 3 zstep.
  apply evt_done. do 13 eexists. exists m2. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [apply bytes_at_app; split; [exact BY | rewrite Hl, <- Etn; exact B1] | exact PK2].
Qed.

Lemma sC_inv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text nn p : Z) (db : list byte) (live : word),
  memcpy_contract -> fuzz_alloc_live_contract -> fuzz_alloc_peak_reset_contract ->
  a0 = Z_to_bv 64 text -> s1 = Z_to_bv 64 nn -> s2 = Z_to_bv 64 p ->
  0 <= nn <= 3 * 2 ^ 20 -> Z.of_nat (length db) = nn ->
  4096 <= text -> text + nn + 1 < 2 ^ 64 -> text + nn + 1 <= 0x33450 \/ 0x33450 + 24 <= text ->
  wr_at rsegs m text (nn + 1) ->
  (0 < nn -> 0 <= p /\ bytes_at rsegs m p db /\ (p + nn <= text \/ text + nn + 1 <= p)) ->
  bytes_at rsegs m 0x33450 (le8 live) -> wr_at rsegs m 0x33458 8 ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x133b0) sp gp tp t0' t1' t2' (Z_to_bv 64 text) s1 (Z_to_bv 64 text) sp
                    a2' a3' a4' a5' a6' a7' s2 live s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14e90) fc None m' (seg_rom rsegs) /\
      munch [(text, text + nn + 1); (0x33458, 0x33458 + 8)] m m' /\ wmono rsegs m m' /\
      bytes_at rsegs m' text (db ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m' 0x33458 (le8 live))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13374) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    text nn p db live MEMCPY FAL FAPR E0 E1 E2 Hnn Hl Ht Htop Hg WR HD LV PK MI.
  subst a0 s1 s2.
  zstep. if_cases BZ; zify_cond BZ; [exfalso; lia|].
  zstep.
  zstep. if_cases BN; zify_cond BN.
  - destruct db as [|b db]; [|cbn [length] in Hl; lia].
    destruct (sa_rw_sub m text (nn + 1) (text + nn) 1 WR ltac:(lia) ltac:(lia)) as [j R1].
    eapply evt_mono.
    { eapply sC_tail; [exact FAL | exact FAPR | reflexivity | reflexivity | lia | exact Hl | lia | lia | exact Hg |
        exact (bytes_at_nil rsegs m text ltac:(lia)) | exact R1 | exact LV | exact PK]. }
    intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & m' & E & MU' & WM' & BY' & PK').
    do 13 eexists. exists m'. split; [exact E|].
    split; [eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros x Hx; lia|].
    split; [exact WM'|]. split; [exact BY' | exact PK'].
  - destruct (HD ltac:(lia)) as (Hp0 & DB & DJ).
    pose proof (bytes_at_bound rsegs m p db DB) as Hd.
    destruct (sa_rw_sub m text (nn + 1) text (Z.to_nat nn) WR ltac:(lia) ltac:(lia)) as [j0 R0].
    do 4 zstep.
    eapply evt_cut.
    { eapply MEMCPY with (src := db) (junk := j0).
      - rewrite (unsigned_lit p) by lia. exact DB.
      - rewrite (unsigned_lit nn) by lia. lia.
      - rewrite (unsigned_lit text), (unsigned_lit nn) by lia. exact R0.
      - rewrite (unsigned_lit p), (unsigned_lit text), (unsigned_lit nn) by lia. lia.
      - exact MI. }
    intros ms' POST. unfold memcpy_post in POST.
    destruct POST as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2 &
      E & MUc & WMc & MIc & RVc & DBc).
    subst ms'.
    rewrite (unsigned_lit text), (unsigned_lit nn) in MUc, RVc by lia.
    replace (ret_pc (Z_to_bv 64 0x13390)) with (Z_to_bv 64 0x13390) by (apply bv_eq; vm_compute; reflexivity).
    destruct RVc as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    apply (wr_at_transport rsegs m m2) in WR; [|exact WMc].
    apply (wr_at_transport rsegs m m2) in PK; [|exact WMc].
    apply (bytes_at_transport rsegs [(text, text + nn)] m m2) in LV; [|exact MUc | cbn [disjoint_from]; simpl_sizes; slia].
    destruct (sa_rw_sub m2 text (nn + 1) (text + nn) 1 WR ltac:(lia) ltac:(lia)) as [j1 R1].
    eapply evt_mono.
    { eapply sC_tail; [exact FAL | exact FAPR | reflexivity | reflexivity | lia | exact Hl | lia | lia | exact Hg |
        exact BY | exact R1 | exact LV | exact PK]. }
    intros ms' (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & m' & E' & MU' & WM' & BY' & PK').
    do 13 eexists. exists m'. split; [exact E'|].
    split.
    { apply (munch_trans _ m m2 m').
      - eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - eapply munch_weaken; [|exact MU']. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    split; [exact (wmono_trans rsegs m m2 m' WMc WM')|]. split; [exact BY' | exact PK'].
Qed.

Lemma sC_run : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text nn p : Z) (db : list byte) (live : word),
  memcpy_contract -> fuzz_alloc_live_contract -> fuzz_alloc_peak_reset_contract ->
  a0 = Z_to_bv 64 text -> s1 = Z_to_bv 64 nn -> s2 = Z_to_bv 64 p ->
  0 <= nn <= 3 * 2 ^ 20 -> Z.of_nat (length db) = nn ->
  4096 <= text -> text + nn + 1 <= bv_unsigned sp -> text + nn + 1 <= 0x33450 \/ 0x33450 + 24 <= text ->
  wr_at rsegs m text (nn + 1) ->
  (forall i, 0 <= i < nn + 1 -> ro_addr rsegs (wa (text + i)) = false) ->
  (0 < nn -> 0 <= p /\ bytes_at rsegs m p db /\ (p + nn <= text \/ text + nn + 1 <= p)) ->
  bytes_at rsegs m 0x33450 (le8 live) -> wr_at rsegs m 0x33458 8 ->
  ro_agree rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x133b0) sp gp tp t0' t1' t2' (Z_to_bv 64 text) s1 (Z_to_bv 64 text) sp
                    a2' a3' a4' a5' a6' a7' s2 live s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x14e90) fc None m' (seg_rom rsegs) /\
      munch [(text, text + nn + 1); (0x33458, 0x33458 + 8)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
      bytes_at rsegs m' text (db ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m' 0x33458 (le8 live))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13374) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    text nn p db live MEMCPY FAL FAPR E0 E1 E2 Hnn Hl Ht Hsp Hg WR HRO HD LV PK RA.
  pose proof (mem_rel_normalize rsegs m RA) as HR0.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  eapply evt_mono.
  { apply (evt_normalize rsegs); [exact sa_wx | exact RA |].
    eapply sC_inv; [exact MEMCPY | exact FAL | exact FAPR | exact E0 | exact E1 | exact E2 | exact Hnn | exact Hl |
      exact Ht | lia | exact Hg | exact (wr_at_norm rsegs m (normalize rsegs m) text (nn + 1) HR0 WR HRO) |
      | exact (bytes_at_normalize rsegs m _ _ RA LV) |
      exact (wr_at_norm rsegs m (normalize rsegs m) 0x33458 8 HR0 PK sa_peak_rw) | apply mem_inv_normalize].
    intros Hn0. destruct (HD Hn0) as (Hp0 & DB & DJ).
    split; [exact Hp0|]. split; [exact (bytes_at_normalize rsegs m p db RA DB) | exact DJ]. }
  intros s (s0' & (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & m0 & E & MU & WM & BY & PK') &
    REL & ROS).
  subst s0'.
  destruct (sa_rel_shape s _ _ _ _ _ _ REL) as [Es HR].
  do 13 eexists. exists (ms_mem s). split; [exact Es|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem s) m0 HR0 HR ROS WM)|].
  split; [exact (ro_agree_same rsegs m (ms_mem s) RA ROS)|].
  split; [exact (proj2 (bytes_at_rel rsegs (ms_mem s) m0 _ _ HR) BY) |
          exact (proj2 (bytes_at_rel rsegs (ms_mem s) m0 _ _ HR) PK')].
Qed.
