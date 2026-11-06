From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel CtrlParsed disco_classify_c disco_table_c disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import classify_core_c reac_frame_clean_len_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_classify_on_segment_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_observe_c bcmp_c memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import hunt_c reac_hunt_observe_c HuntObsLib HuntObsFacts.
Import ListNotations.
Open Scope Z_scope.

Lemma ho_rwc_split : forall m A c cs,
  rw_cells rsegs m A (c :: cs) -> rw_cells rsegs m A [c] /\ rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[[Wc Wcs] Hb] (Ha & Hl & Hw)]. cbn [cells_bytes cells_size] in *.
  apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cbytes_length in B2 by exact Wc.
  split; split.
  - split; [cbn; split; [exact Wc|exact I]|]. cbn [cells_bytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [exact Wcs|exact B2].
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma ho_rwc : forall m a bs, bytes_at rsegs m a bs -> wr_at rsegs m a (Z.of_nat (length bs)) ->
  rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m a bs B W. split; [split|].
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma ho_wr_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> a' + n' <= a + n -> wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma ho_rwc_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.


Lemma clean_le : forall n, 0 <= n -> 0 <= reac_frame_clean_len_model n <= n.
Proof.
  intros n Hn. unfold reac_frame_clean_len_model.
  destruct ((54 <=? n) && ((n - 52) mod 36 =? 2)) eqn:E; [|lia].
  apply andb_prop in E. destruct E as [E1 _]. apply Z.leb_le in E1. lia.
Qed.

Lemma clean_50 : forall n, 0 <= n -> 50 <= reac_frame_clean_len_model n -> 50 <= n.
Proof. intros n Hn H. pose proof (clean_le n Hn). lia. Qed.





Lemma bytes_at_cat : forall m a A B, bytes_at rsegs m a A -> bytes_at rsegs m (a + Z.of_nat (length A)) B ->
  bytes_at rsegs m a (A ++ B).
Proof. intros m a A B HA HB. apply bytes_at_app. split; assumption. Qed.

Lemma ho_assemble : forall m h T Lk U12 OP RST,
  length T = 400%nat -> length Lk = 12%nat -> length U12 = 12%nat -> length OP = 8%nat -> length RST = 48%nat ->
  bytes_at rsegs m h T -> bytes_at rsegs m (h + 400) Lk -> bytes_at rsegs m (h + 412) U12 ->
  bytes_at rsegs m (h + 424) OP -> bytes_at rsegs m (h + 432) RST -> wr_at rsegs m h 480 ->
  rw_cells rsegs m h [CB 480 (T ++ Lk ++ U12 ++ OP ++ RST)].
Proof.
  intros m h T Lk U12 OP RST L1 L2 L3 L4 L5 B1 B2 B3 B4 B5 W.
  assert (LL : length (T ++ Lk ++ U12 ++ OP ++ RST) = 480%nat) by (rewrite !app_length; lia).
  rewrite <- LL at 1. apply ho_rwc; [|rewrite LL; exact W].
  apply bytes_at_cat; [exact B1|]. rewrite L1.
  apply bytes_at_cat; [exact B2|]. rewrite L2. replace (h + Z.of_nat 400 + Z.of_nat 12) with (h + 412) by lia.
  apply bytes_at_cat; [exact B3|]. rewrite L3. replace (h + 412 + Z.of_nat 12) with (h + 424) by lia.
  apply bytes_at_cat; [exact B4|]. rewrite L4. replace (h + 424 + Z.of_nat 8) with (h + 432) by lia. exact B5.
Qed.

Lemma h_tail : forall (H : list byte), length H = 480%nat -> skipn 412 H = sub H 412 12 ++ sub H 424 8 ++ sub H 432 48.
Proof.
  intros H LH. transitivity (sub H 412 68); [symmetry; rewrite sub_all by lia; reflexivity|].
  replace 68%nat with (12 + 56)%nat by reflexivity. rewrite sub_split by lia.
  replace 56%nat with (8 + 48)%nat by reflexivity. rewrite sub_split by lia. reflexivity.
Qed.

Lemma h_tail432 : forall (H : list byte), length H = 480%nat -> skipn 432 H = sub H 432 48.
Proof. intros H LH. symmetry. rewrite sub_all by lia. reflexivity. Qed.









Lemma hok_gen : forall H T' Lk' Rest, length H = 480%nat -> hunt_ok H -> length T' = 400%nat -> table_ok T' ->
  length Lk' = 12%nat -> lock_ok Lk' -> length Rest = 68%nat -> sub Rest 28 4 = sub H 440 4 ->
  hunt_ok (T' ++ Lk' ++ Rest).
Proof.
  intros H T' Lk' Rest LH (_ & _ & _ & V) LT TOK LL LOK LR SR. split; [rewrite !app_length; lia|].
  split; [|split].
  - replace (firstn 400 (T' ++ Lk' ++ Rest)) with T'; [exact TOK|]. rewrite <- LT. symmetry. apply firstn_app_exact.
  - replace (firstn 12 (skipn 400 (T' ++ Lk' ++ Rest))) with Lk'; [exact LOK|].
    rewrite <- LT, skipn_app_exact, <- LL. symmetry. apply firstn_app_exact.
  - unfold s32_at, u_at in *. rewrite sub_app_r by lia. rewrite LT. rewrite sub_app_r by lia. rewrite LL.
    replace (440 - Z.of_nat 400 - Z.of_nat 12) with 28 by lia. rewrite SR. exact V.
Qed.


Lemma rwc_len : forall m a n bs, rw_cells rsegs m a [CB n bs] -> length bs = n.
Proof. intros m a n bs [[[X _] _] _]. exact X. Qed.

Lemma ho_post_fail : forall H FR O len now out m' Lk',
  cm_ret (firstn 50 FR) (reac_frame_clean_len_model len) (sub H 412 6) (Some (sub H 400 12)) = -1 ->
  cm_lock (firstn 50 FR) (reac_frame_clean_len_model len) (sub H 412 6) (Some (sub H 400 12)) = Some Lk' ->
  (out <> 0 -> rw_cells rsegs m' out [CB 24 O]) ->
  ho_post H FR O len now out (-1) (sub H 0 400 ++ Lk' ++ skipn 412 H) m'.
Proof.
  intros H FR O len now out m' Lk' R EL RO. unfold ho_post. cbv zeta. rewrite EL. split.
  - intros _. split; [reflexivity|]. split; [reflexivity|]. exact RO.
  - intros X. rewrite R in X. discriminate.
Qed.

Lemma rwc_cells_bytes : forall m a cs, rw_cells rsegs m a cs -> bytes_at rsegs m a (cells_bytes cs).
Proof. intros m a cs [[_ B] _]. exact B. Qed.

Lemma ho_post_ok : forall H FR O len now out m' Lk' T' c,
  cm_ret (firstn 50 FR) (reac_frame_clean_len_model len) (sub H 412 6) (Some (sub H 400 12)) = 0 ->
  cm_lock (firstn 50 FR) (reac_frame_clean_len_model len) (sub H 412 6) (Some (sub H 400 12)) = Some Lk' ->
  observe_model (sub H 0 400) (sight (firstn 50 FR) (reac_frame_clean_len_model len)) 0 now T' c ->
  (out <> 0 -> exists A, ho_answer T' (sight (firstn 50 FR) (reac_frame_clean_len_model len)) A /\
                         rw_cells rsegs m' out [CB 24 A] /\
                         ho_facts H FR (reac_frame_clean_len_model len) (sub H 0 400) A) ->
  ho_post H FR O len now out (if c =? 0 then 0 else 1)
    (T' ++ Lk' ++ sub H 412 12 ++ (if n_of (sub H 0 400) =? 0 then le8 (Z_to_bv 64 now) else sub H 424 8) ++
     skipn 432 H) m'.
Proof.
  intros H FR O len now out m' Lk' T' c R EL OM ANS. unfold ho_post. cbv zeta. rewrite EL. split.
  - intros X. rewrite R in X. contradiction.
  - intros _. exists T', c. split; [exact OM|]. split; [reflexivity|]. split; [reflexivity|]. exact ANS.
Qed.



Lemma stk_mrd_transport : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hc a Ha) as [Ho | Hs]; [|exact Hs].
  exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Ltac ho_tr MUc WMc :=
  lazymatch type of MUc with munch _ ?m1 ?m2 =>
    transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc;
    try match goal with Hm : mem_inv rsegs m1 |- _ => clear Hm end; try clear m1 end.

Theorem reac_hunt_observe_holds :
  reac_frame_clean_len_contract -> reac_disco_classify_on_segment_contract -> reac_disco_table_observe_contract ->
  memcpy_contract -> bcmp_contract -> reac_hunt_observe_contract.
Proof.
  intros CLC CLS OBS MCC BC.
  unfold reac_hunt_observe_contract, REAC_HUNT_OBSERVE, REAC_HUNT_OBSERVE_K.
  unfold reac_disco_classify_on_segment_contract, classify_core_spec, REAC_DISCO_CLASSIFY_ON_SEGMENT in CLS.
  unfold reac_disco_table_observe_contract, REAC_DISCO_TABLE_OBSERVE, REAC_DISCO_TABLE_OBSERVE_K in OBS.
  unfold memcpy_contract in MCC. unfold bcmp_contract, BCMP in BC.
  unfold reac_frame_clean_len_contract, REAC_FRAME_CLEAN_LEN in CLC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo h f len now out H FR O -> -> -> -> -> Hlen Hnow Hout Hh0 Hh8 RH HOK BF LFR Hf0 DF DO Hsp ST LO DH MI KMb KTb.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (rw_cells_bound rsegs m h _ RH) as HB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HB.
  pose proof (bytes_at_bound rsegs m f FR BF) as FB. rewrite LFR in FB. rewrite Z2Nat.id in FB by lia.
  unfold off_window in DH.
  assert (LH : length H = 480%nat) by (destruct HOK as [X _]; exact X).
  assert (RKM : ro_bytes rsegs A_M (le8 (Z_to_bv 64 KM))) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
  assert (RKT : ro_bytes rsegs A_T (le8 (Z_to_bv 64 KT))) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
  clear KMb KTb.
  assert (BFw : bytes_at rsegs m f FR /\ True) by (split; [exact BF|exact I]). clear BF.
  pose proof (ho_rwc_bytes m h 480 H RH) as BH.
  assert (WH : wr_at rsegs m h 480) by (destruct RH as [_ W]; exact W).
  pose proof (bytes_at_sub m h H 0 400 BH ltac:(lia) ltac:(rewrite LH; lia)) as BT. rewrite Z.add_0_r in BT.
  pose proof (bytes_at_sub m h H 400 12 BH ltac:(lia) ltac:(rewrite LH; lia)) as BL.
  pose proof (bytes_at_sub m h H 412 12 BH ltac:(lia) ltac:(rewrite LH; lia)) as BU12.
  pose proof (bytes_at_sub m h H 412 6 BH ltac:(lia) ltac:(rewrite LH; lia)) as BU.
  pose proof (bytes_at_sub m h H 424 8 BH ltac:(lia) ltac:(rewrite LH; lia)) as BO.
  pose proof (bytes_at_sub m h H 432 48 BH ltac:(lia) ltac:(rewrite LH; lia)) as BR.
  clear RH BH.
  set (T := sub H 0 400) in *. set (Lk := sub H 400 12) in *. set (U12 := sub H 412 12) in *.
  set (U := sub H 412 6) in *. set (OP := sub H 424 8) in *. set (RST := sub H 432 48) in *.
  assert (LT : length T = 400%nat) by (apply length_sub; lia).
  assert (LLk : length Lk = 12%nat) by (apply length_sub; lia).
  assert (LU12 : length U12 = 12%nat) by (apply length_sub; lia).
  assert (LU : length U = 6%nat) by (apply length_sub; lia).
  assert (LOP : length OP = 8%nat) by (apply length_sub; lia).
  assert (LRST : length RST = 48%nat) by (apply length_sub; lia).
  pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (h, h + 480)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 64%nat ST.
  do 12 step.
  rename m into mI. rename MU into MU0. rename WM into WM0.
  lazymatch goal with H : rw_cells _ ?mm _ _ |- _ => rename mm into m1; rename H into FR0 end.
  eapply evt_cut.
  { eapply CLC; apply ro_bytes_at; first [exact MI | exact RKM | exact RKT | (unfold A_M, A_T; rewrite ?length_le8; cbn; lia)]. }
  intros ms' (x11 & x12 & x13 & E). subst ms'.
  rewrite (ret_pc_even 89968) by (first [lia | reflexivity]).
  rewrite (unsigned_lit len) by lia.
  set (L := reac_frame_clean_len_model len) in *.
  pose proof (clean_le len ltac:(lia)) as HL. fold L in HL.
  do 6 step.
  pose proof ST as (Hlo0 & _ & _).
  apply ho_rwc_split in FR0. destruct FR0 as [FRs FRr]. cbn [csize] in FRr.
  replace (bv_unsigned sp + -64 + Z.of_nat 24) with (bv_unsigned sp + -40) in FRr by lia.
  assert (BF1 : 0 < len -> bytes_at rsegs m1 f FR).
  { intros Hl0. destruct (DF Hl0) as [DFh DFs]. unfold off_window, disj in DFh, DFs.
    eapply bytes_at_transport; [exact (proj1 BFw) | exact MU0 | ].
    cbn [disjoint_from]. rewrite LFR, Z2Nat.id by lia. lia. }
  assert (RLk : rw_cells rsegs m1 (h + 400) [CB 12 Lk]).
  { rewrite <- LLk. apply ho_rwc; [exact BL|]. rewrite LLk. eapply ho_wr_sub; [exact WH | lia | lia]. }
  eapply evt_cut.
  { eapply CLS with (lo := lo) (lk := h + 400) (f := f mod 2^64) (len := L) (u := h + 412) (o := bv_unsigned sp + -64)
      (FB := firstn 50 (FR ++ repeat (zb 0) 50)) (U := U) (L := Some Lk); try reflexivity.
    { apply bv_eq. rewrite !unsigned_lit_wrap. symmetry. apply Zmod_mod. }
    rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia.
    unfold classify_core_pre, CLASSIFY_CORE_K, disj.
    split; [Z.div_mod_to_equations; lia|].
    split; [exact ST|]. split; [lia|]. split; [lia|].
    split; [pose proof (Z.mod_pos_bound f (2^64)); lia|].
    split; [rewrite length_firstn, length_app, repeat_length; lia|].
    split.
    { intros H50. pose proof (clean_50 len ltac:(lia) H50) as H50'. fold L in H50'.
      destruct (DF ltac:(lia)) as [DFh DFs]. unfold off_window, disj in DFh, DFs.
      rewrite Z.mod_small by lia. rewrite fb0_eq by (rewrite LFR; lia).
      split; [apply Hf0; lia|].
      split; [|lia].
      pose proof (bytes_at_sub m1 f FR 0 50 (BF1 ltac:(lia)) ltac:(lia) ltac:(rewrite LFR; lia)) as X.
      rewrite Z.add_0_r in X. exact X. }
    split; [exact LU|]. split; [exact BU|]. split; [lia|].
    split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact FRs|]. split; [lia|]. split; [lia|].
    split.
    { split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact RLk|].
      split; [lia|]. split; [lia|]. split; [lia|].
      intros H50. pose proof (clean_50 len ltac:(lia) H50) as H50'.
      destruct (DF ltac:(lia)) as [DFh DFs]. unfold off_window, disj in DFh, DFs. lia. }
    exact MI. }
  intros ms' PO. unfold classify_core_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & E & MUc & WMc & MI2 & ST2 & RO & RLK).
  subst ms'. clear ST.
  destruct (cm_pad FR L U (Some Lk) ltac:(intros X; rewrite LFR; lia)) as (CP1 & CP2 & CP3).
  rewrite CP1. rewrite CP2 in RO. rewrite CP3 in RLK. clear CP1 CP2 CP3.
  rewrite (unsigned_lit (bv_unsigned sp + -64)) in MUc, ST2 by lia.
  unfold CLASSIFY_CORE_K in MUc. cbv iota in MUc, RLK.
  ho_tr MUc WMc.
  rewrite (ret_pc_even 89992) by (first [lia | reflexivity]).
  destruct (cm_lock_some (firstn 50 FR) L U Lk) as [Lk' ELk]. rewrite ELk in RLK.
  assert (LLk' : length Lk' = 12%nat) by (destruct RLK as [[[X _] _] _]; exact X).
  pose proof (ho_rwc_bytes _ _ _ _ RLK) as BLk'.
  assert (EPI : forall (m3 : word -> option byte) (r : Z) (H' jk : list byte)
                       (ra' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
    rw_cells rsegs m3 (bv_unsigned sp + -64) [CB 24 jk] ->
    rw_cells rsegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m3 lo (bv_unsigned sp + -64) ->
    munch ((bv_unsigned sp - 256, bv_unsigned sp) :: (h, h + 480) :: (if out =? 0 then [] else [(out, out + 24)])) mI m3 ->
    wmono rsegs mI m3 -> mem_inv rsegs m3 ->
    bytes_at rsegs m3 f FR -> rw_cells rsegs m3 h [CB 480 H'] -> hunt_ok H' -> (r = -1 \/ r = 0 \/ r = 1) ->
    ho_post H FR O len now out r H' m3 ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x15f90) fc None m3 (seg_rom rsegs))).
  { intros m3 r H' jk ra' x5 x6 x7 x8 x9 x10 x11' x12' x13' x14 x15 x16 x17 x19 x28 x29 x30 x31
      FRs3 FRr3 ST3 MU3 WM3 MI3 BF3 RH3 HOK3 R3 POST3.
    do 7 step.
    release_frame FRs3 ST3 (bv_unsigned sp + -40).
    release_frame FRr3 ST3 (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 14 eexists. exists m3, r, H'. split; [reflexivity|].
    repeat (split; [eassumption|]). exact POST3. }
  assert (BFm : bytes_at rsegs m2 f FR).
  { destruct (Z.eq_dec len 0) as [Z0|Z0].
    - assert (FR = []) by (apply length_zero_iff_nil; lia). subst FR. apply bytes_at_nil. lia.
    - destruct (DF ltac:(lia)) as [DFh DFs]. unfold off_window, disj in DFh, DFs.
      eapply bytes_at_transport; [exact (proj1 BFw) | exact MU0 | ].
      cbn [disjoint_from]. rewrite LFR, Z2Nat.id by lia. lia. }
  clear BF1.
  assert (LFB : 50 <= L -> length (firstn 50 FR) = 50%nat) by (intros X; rewrite firstn_length; pose proof (clean_le len); lia).
  assert (LOKk : lock_ok Lk') by (eapply cm_lock_ok; [exact LFB | exact (proj1 (proj2 (proj2 HOK))) | exact ELk]).
  assert (MUg : munch ((bv_unsigned sp - 256, bv_unsigned sp) :: (h, h + 480) :: (if out =? 0 then [] else [(out, out + 24)])) mI m2).
  { eapply munch_weaken; [|exact MU0]. intros x Hx. destruct (out =? 0); cbn [outside] in *; tauto. }
  assert (ROUT : out <> 0 -> rw_cells rsegs m2 out [CB 24 O]).
  { intros Ho. destruct (DO Ho) as (_ & RW & D1 & _ & D2). unfold disj, off_window in D1, D2.
    eapply rw_cells_transport; [exact RW | exact MU0 | exact WM0 | ]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  step.
  destruct (cm_ret_cases (firstn 50 FR) L U (Some Lk)) as [R0|R1].
  2: { rewrite R1. replace (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false by reflexivity. cbv iota.
       step.
       pose proof (cm_lock_fail (firstn 50 FR) L U Lk ltac:(rewrite R1; lia)) as EL. rewrite ELk in EL. injection EL as EL.
       eapply (EPI m2 (-1) (T ++ Lk' ++ skipn 412 H)); try eassumption.
       - rewrite (h_tail H LH). apply ho_assemble; assumption.
       - eapply hok_gen; try eassumption.
         + unfold T. exact (proj1 (proj2 HOK)).
         + rewrite skipn_length. lia.
         + rewrite sub_skipn by lia. reflexivity.
       - left; reflexivity.
       - apply ho_post_fail; assumption. }
  rewrite R0. replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity. cbv iota.
  pose proof (cm_ret0_len _ _ _ _ R0) as L50.
  assert (LFB50 : length (firstn 50 FR) = 50%nat) by (apply LFB; exact L50).
  rewrite (cm_out_ok _ _ _ _ _ R0) in RO.
  set (G := sight (firstn 50 FR) L) in *.
  assert (LG : length G = 24%nat) by (apply sight_len; exact LFB50).
  destruct (sight_ok (firstn 50 FR) L LFB50) as [GS1 GS2]. fold G in GS1, GS2.
  assert (TOK : table_ok T) by exact (proj1 (proj2 HOK)).
  destruct TOK as (TT1 & TT2 & TT3 & TT4).
  pose proof (rd_sub m2 h T 384 4 BT ltac:(lia) ltac:(rewrite LT; lia)) as RN.
  step.
  rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T) in *.
  clear RN. unfold tbl_T1 in TT1.
  clear BU.
  assert (BFend : forall m', munch ((bv_unsigned sp - 256, bv_unsigned sp) :: (h, h + 480) ::
                                    (if out =? 0 then [] else [(out, out + 24)])) mI m' -> bytes_at rsegs m' f FR).
  { intros m' MUx. destruct (Z.eq_dec len 0) as [Z0|Z0].
    - assert (FR = []) by (apply length_zero_iff_nil; lia). subst FR. apply bytes_at_nil. lia.
    - destruct (DF ltac:(lia)) as [DFh DFs]. unfold off_window, disj in DFh, DFs.
      eapply bytes_at_transport; [exact (proj1 BFw) | exact MUx | ].
      rewrite LFR, Z2Nat.id by lia.
      destruct (Z.eqb_spec out 0) as [O0|O0]; cbn [disjoint_from]; [lia|].
      destruct (DO O0) as (_ & _ & _ & D3 & _). specialize (D3 ltac:(lia)). unfold disj in D3. lia. }
  assert (CONT : forall (m3 : word -> option byte) (OP' : list byte)
                        (ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    OP' = (if n_of T =? 0 then le8 (Z_to_bv 64 now) else OP) ->
    rw_cells rsegs m3 (bv_unsigned sp + -64) [CB 24 G] ->
    rw_cells rsegs m3 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m3 lo (bv_unsigned sp + -64) ->
    munch [(bv_unsigned sp - 256, bv_unsigned sp); (h, h + 480)] mI m3 -> wmono rsegs mI m3 -> mem_inv rsegs m3 ->
    bytes_at rsegs m3 h T -> bytes_at rsegs m3 (h + 400) Lk' -> bytes_at rsegs m3 (h + 412) U12 ->
    bytes_at rsegs m3 (h + 424) OP' -> bytes_at rsegs m3 (h + 432) RST -> wr_at rsegs m3 h 480 ->
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 h)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 now) (Z_to_bv 64 f)
                          s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x15fbc) fc None m3 (seg_rom rsegs))).
  { intros m3 OP' ra' x5 x6 x7 x10 x11' x12' x13' x14 x15 x16 x17 x28 x29 x30 x31 EOP
      RG3 FRr3 ST3 MU3 WM3 MI3 BT3 BLk3 BU3 BOP3 BR3 WH3.
    assert (LOP' : length OP' = 8%nat) by (rewrite EOP; destruct (n_of T =? 0); [apply length_le8 | exact LOP]).
    pose proof (ho_rwc_bytes _ _ _ _ RG3) as BG3.
    assert (RT3 : rw_cells rsegs m3 h [CB 400 T]).
    { rewrite <- LT. apply ho_rwc; [exact BT3|]. rewrite LT. eapply ho_wr_sub; [exact WH3 | lia | lia]. }
    do 5 step.
    eapply evt_cut.
    { eapply OBS with (t := h) (s := bv_unsigned sp + -64) (ow := 0) (now := now) (T := T) (G := G) (lo := lo);
        try reflexivity; try lia; try assumption.
      - rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia. exact ST3.
      - rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia. lia.
      - unfold off_window. rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia. lia.
      - unfold off_window. rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia. lia. }
    intros ms' (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & T' & c & E &
                MUc & WMc & MI4 & ST4 & RT4 & BG4 & OM & T1' & T2' & T3' & T4i).
    subst ms'. clear ST3.
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in MUc, ST4 by lia.
    ho_tr MUc WMc.
    rewrite (ret_pc_even 90064) by (first [lia | reflexivity]).
    pose proof (ho_rwc_bytes _ _ _ _ RT4) as BT4. pose proof (rwc_len _ _ _ _ RT4) as LT'. clear RT4.
    pose proof (obs_c01 _ _ _ _ _ _ OM) as C01.
    assert (HOK' : hunt_ok (T' ++ Lk' ++ U12 ++ OP' ++ skipn 432 H)).
    { eapply hok_gen; try eassumption.
      - split; [exact T1'|]. split; [exact T2'|]. split; [exact T3'|]. exact (T4i TT4).
      - rewrite !app_length, skipn_length. lia.
      - rewrite sub_app_r by lia. rewrite sub_app_r by (rewrite LOP'; lia). rewrite sub_skipn by lia.
        rewrite LU12, LOP'. reflexivity. }
    assert (RH4 : forall m5, bytes_at rsegs m5 h T' -> bytes_at rsegs m5 (h + 400) Lk' -> bytes_at rsegs m5 (h + 412) U12 ->
                  bytes_at rsegs m5 (h + 424) OP' -> bytes_at rsegs m5 (h + 432) RST -> wr_at rsegs m5 h 480 ->
                  rw_cells rsegs m5 h [CB 480 (T' ++ Lk' ++ U12 ++ OP' ++ skipn 432 H)]).
    { intros m5 B1 B2 B3 B4 B5 W. rewrite (h_tail432 H LH). apply ho_assemble; assumption. }
    assert (POSTA : forall m5 A, (out <> 0 -> exists r, find_res T' (s_mac G) r /\ A = (if r <? 0 then G else ho_entry T' G r)
                                                   /\ rw_cells rsegs m5 out [CB 24 A]) ->
                    ho_post H FR O len now out (if c =? 0 then 0 else 1) (T' ++ Lk' ++ U12 ++ OP' ++ skipn 432 H) m5).
    { intros m5 A HA. rewrite EOP. apply ho_post_ok; try assumption.
      intros Ho. destruct (HA Ho) as (r & FRr' & EA & RA). exists A. split; [exists r; split; assumption|].
      split; [exact RA|]. rewrite EA. eapply ho_facts_ok; try eassumption. lia. }
    step.
    replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 c)) with (Z_to_bv 64 (if c =? 0 then 0 else 1))
      by (destruct C01 as [C0|C0]; subst c; reflexivity).
    assert (R01 : (if c =? 0 then 0 else 1) = 0 \/ (if c =? 0 then 0 else 1) = 1) by (destruct (c =? 0); auto).
    step.
    rewrite eqb_lit by lia.
    destruct (Z.eqb_spec out 0) as [O0|O0]; cbv iota.
    1: eapply (EPI m4 _ (T' ++ Lk' ++ U12 ++ OP' ++ skipn 432 H)); try eassumption;
      first [ (eapply munch_weaken; [|exact MU3]; intros x Hx; try rewrite O0 in Hx; cbn [outside Z.eqb] in *; tauto)
            | (apply BFend; eapply munch_weaken; [|exact MU3]; intros x Hx; try rewrite O0 in Hx; cbn [outside Z.eqb] in *; tauto)
            | (apply RH4; assumption)
            | (right; exact R01)
            | (apply (POSTA m4 G); intros X; contradiction) ].
    assert (RO4 : rw_cells rsegs m4 out [CB 24 O]) by
          (destruct (DO O0) as (_ & RW & D1 & _ & D2); unfold disj, off_window in D1, D2;
           eapply rw_cells_transport; [exact RW | exact MU3 | exact WM3 | ]; cbn [disjoint_from cells_size csize Nat.add]; lia).
    all: assert (D24 : out + 24 <= h \/ h + 480 <= out) by (destruct (DO O0) as (_ & _ & D1 & _); unfold disj in D1; lia).
    all: assert (D24s : out + 24 <= bv_unsigned sp - 256 \/ bv_unsigned sp <= out)
           by (destruct (DO O0) as (_ & _ & _ & _ & D2); unfold off_window in D2; lia).
    all: assert (MU3' : munch [(bv_unsigned sp - 256, bv_unsigned sp); (h, h + 480); (out, out + 24)] mI m4)
           by (eapply munch_weaken; [|exact MU3]; intros x Hx; cbn [outside] in *; tauto).
    all: clear MU3.
    all: assert (STw : stk rsegs m4 lo (bv_unsigned sp + -64) /\ True) by (split; [exact ST4|exact I]).
    all: do 4 step.
    all: eapply evt_cut;
         [ eapply MCC with (src := G) (junk := O);
           [ rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; exact BG4
           | rewrite LG; reflexivity
           | rewrite (unsigned_lit out) by lia; change (Z.to_nat (bv_unsigned (Z_to_bv 64 24))) with 24%nat; exact RO4
           | rewrite (unsigned_lit out), (unsigned_lit (bv_unsigned sp + -64)), (unsigned_lit 24) by lia; lia
           | exact MI4 ] | ].
    all: intros ms' PO; unfold memcpy_post in PO;
         destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m5 & E &
                         MUc & WMc & MI5 & RO5 & BG5);
         subst ms'.
    all: rewrite (unsigned_lit out), (unsigned_lit 24) in MUc by lia.
    all: rewrite (unsigned_lit out) in RO5 by lia; change (Z.to_nat (bv_unsigned (Z_to_bv 64 24))) with 24%nat in RO5.
    all: rewrite (unsigned_lit (bv_unsigned sp + -64)) in BG5 by lia.
    all: assert (ST5 : stk rsegs m5 lo (bv_unsigned sp + -64)).
    all: [> eapply stk_mrd_transport; [exact (proj1 STw) | exact MUc | exact WMc | ];
           intros x Hx; destruct (Z_le_gt_dec out x) as [X1|X1]; [destruct (Z_lt_ge_dec x (out + 24)) as [X2|X2]|];
           [ right; pose proof (ho_rwc_bytes _ _ _ _ RO5) as (_ & LBo & Bo);
             replace x with (out + Z.of_nat (Z.to_nat (x - out))) by lia; rewrite (Bo (Z.to_nat (x - out))) by lia;
             destruct (nth_error G (Z.to_nat (x - out))) eqn:Ex; [eexists; reflexivity|];
             apply nth_error_None in Ex; lia
           | left; cbn [outside]; lia
           | left; cbn [outside]; lia ] | ].
    all: clear STw.
    all: ho_tr MUc WMc.
    all: rewrite (ret_pc_even 90088) by (first [lia | reflexivity]).
    all: assert (MUg5 : munch ((bv_unsigned sp - 256, bv_unsigned sp) :: (h, h + 480) ::
                               (if out =? 0 then [] else [(out, out + 24)])) mI m5)
           by (replace (out =? 0) with false by (symmetry; apply Z.eqb_neq; exact O0); exact MU3').
    all: pose proof (rd_sub m5 h T' 384 4 BT4 ltac:(lia) ltac:(rewrite LT'; lia)) as RN'.
    all: step.
    all: rewrite lw_val by (apply length_sub; lia).
    all: change (bv_swrap 32 (bytes_le_to_Z (sub T' 384 4))) with (n_of T') in *.
    all: clear RN'. 
    all: unfold tbl_T1 in T1'.
    all: step.
    all: rewrite lts_lit by lia.
    all: pose proof (ho_rwc_bytes _ _ _ _ RG3) as BG3'.
    all: assert (EXIT : forall m6 A (ra' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
             (exists r, find_res T' (s_mac G) r /\ A = (if r <? 0 then G else ho_entry T' G r)) ->
             rw_cells rsegs m6 out [CB 24 A] ->
             rw_cells rsegs m6 (bv_unsigned sp + -64) [CB 24 G] ->
             rw_cells rsegs m6 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
             stk rsegs m6 lo (bv_unsigned sp + -64) ->
             munch [(bv_unsigned sp - 256, bv_unsigned sp); (h, h + 480); (out, out + 24)] mI m6 ->
             wmono rsegs mI m6 -> mem_inv rsegs m6 ->
             bytes_at rsegs m6 h T' -> bytes_at rsegs m6 (h + 400) Lk' -> bytes_at rsegs m6 (h + 412) U12 ->
             bytes_at rsegs m6 (h + 424) OP' -> bytes_at rsegs m6 (h + 432) RST -> wr_at rsegs m6 h 480 ->
             evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 out) x9 x10 x11 x12
                                   x13 x14 x15 x16 x17 (Z_to_bv 64 (if c =? 0 then 0 else 1)) x19 s4 s5 s6 s7 s8 s9
                                   s10 s11 x28 x29 x30 x31)
                              F (Z_to_bv 64 0x15f90) fc None m6 (seg_rom rsegs))).
    { intros m6 A q1 q5 q6 q7 q9 q10 q11 q12 q13 q14 q15 q16 q17 q19 q28 q29 q30 q31 (r & FRr' & EA) RA6
        RG6 FRr6 ST6 MU6 WM6 MI6 BT6 BLk6 BU6 BOP6 BR6 WH6.
      assert (MUg6 : munch ((bv_unsigned sp - 256, bv_unsigned sp) :: (h, h + 480) ::
                            (if out =? 0 then [] else [(out, out + 24)])) mI m6)
        by (replace (out =? 0) with false by (symmetry; apply Z.eqb_neq; exact O0); exact MU6).
      eapply (EPI m6 _ (T' ++ Lk' ++ U12 ++ OP' ++ skipn 432 H)); try eassumption.
      - apply BFend; first [exact MUg6 | exact MU6].
      - apply RH4; assumption.
      - right. exact R01.
      - apply (POSTA m6 A). intros _. exists r. split; [exact FRr'|]. split; [exact EA|exact RA6]. }
    all: destruct (Z.ltb_spec 0 (n_of T')) as [NP0|NP0]; cbv iota.
    2: { apply (EXIT m5 G); [exists (-1); split; [left; split; [reflexivity|intros j Hj; lia]|reflexivity] | assumption ..]. }
    cbn [negb].
    assert (LOOP : forall k i (m6 : word -> option byte) (q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
      Z.of_nat k = n_of T' - i -> 0 <= i < n_of T' ->
      (forall j, 0 <= j < i -> mac_of T' j <> s_mac G) ->
      rw_cells rsegs m6 out [CB 24 G] ->
      rw_cells rsegs m6 (bv_unsigned sp + -64) [CB 24 G] ->
      rw_cells rsegs m6 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk rsegs m6 lo (bv_unsigned sp + -64) ->
      munch [(bv_unsigned sp - 256, bv_unsigned sp); (h, h + 480); (out, out + 24)] mI m6 ->
      wmono rsegs mI m6 -> mem_inv rsegs m6 ->
      bytes_at rsegs m6 h T' -> bytes_at rsegs m6 (h + 400) Lk' -> bytes_at rsegs m6 (h + 412) U12 ->
      bytes_at rsegs m6 (h + 424) OP' -> bytes_at rsegs m6 (h + 432) RST -> wr_at rsegs m6 h 480 ->
      evt rsegs QQ (MS (mkR q1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp q5 q6 q7 (Z_to_bv 64 out) (Z_to_bv 64 (h + 48 * i))
                            q10 q11 q12 q13 q14 q15 q16 q17 (Z_to_bv 64 (if c =? 0 then 0 else 1)) (Z_to_bv 64 (n_of T' - i))
                            s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                       F (Z_to_bv 64 0x15ff0) fc None m6 (seg_rom rsegs))).
    { induction k as [|k IH]; intros i m6 q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31
        Hk Hi NP RO6 RG6 FRr6 ST6 MU6 WM6 MI6 BT6 BLk6 BU6 BOP6 BR6 WH6; [lia|].
      pose proof (ho_rwc_bytes _ _ _ _ RG6) as BG6.
      do 4 step.
      destruct (memcmp6 (mac_of T' i) (s_mac G) ltac:(unfold mac_of; apply length_sub; lia)
                  ltac:(unfold s_mac; apply length_sub; lia)) as (v & Hv & Veq & Vr).
      eapply evt_cut.
      { eapply BC with (ls := mac_of T' i) (rs := s_mac G) (v := v).
        - rewrite unsigned_lit by lia. unfold mac_of. apply bytes_at_sub; [exact BT6 | lia | rewrite LT'; lia].
        - rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia. unfold s_mac.
          pose proof (bytes_at_sub _ _ G 0 6 BG6 ltac:(lia) ltac:(rewrite LG; lia)) as X. rewrite Z.add_0_r in X. exact X.
        - exact Hv.
        - exact MI6. }
      post_call rsegs m6.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
      step.
      rewrite eqb_small by exact Vr.
      destruct (Z.eqb_spec v 0) as [V0|V0].
      - pose proof (rd_sub _ h T' (48 * i + 8) 4 BT6 ltac:(lia) ltac:(rewrite LT'; lia)) as R8. step. rewrite lw_val by (apply length_sub; lia). step.
        pose proof (rd_sub _ h T' (48 * i + 12) 4 BT6 ltac:(lia) ltac:(rewrite LT'; lia)) as R12. step. rewrite lw_val by (apply length_sub; lia). step.
        pose proof (rd_sub _ h T' (48 * i + 16) 1 BT6 ltac:(lia) ltac:(rewrite LT'; lia)) as R16.
        assert (E16 : exists b16, sub T' (48 * i + 16) 1 = [b16]).
        { pose proof (length_sub T' (48 * i + 16) 1 ltac:(lia) ltac:(rewrite LT'; lia)) as X.
          destruct (sub T' (48 * i + 16) 1) as [|b16 [|]]; cbn in X; try lia. exists b16. reflexivity. }
        destruct E16 as [b16 E16]. rewrite E16 in R16.
        step.
        pose proof (rd_sub _ h T' (48 * i + 20) 4 BT6 ltac:(lia) ltac:(rewrite LT'; lia)) as R20. step. rewrite lw_val by (apply length_sub; lia).
        step. replace (le1 (zxb b16)) with [b16] by (symmetry; apply le1_zxb). mem_after_store.
        step. step.
        apply (EXIT m4 (ho_entry T' G i)); [ | | assumption ..].
        + exists i. split; [right; split; [lia|]; split; [apply Veq; exact V0 | exact NP] | ].
          replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        + eapply ho_out_cells; [exact LT' | exact LG | lia | exact E16 | exact RO6].
      - assert (NE : mac_of T' i <> s_mac G) by (intro E; apply V0; apply Veq; exact E).
        step. step. step.
        rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (n_of T' - i + -1) 0) as [Z0|Z0]; cbn [negb].
        + apply (EXIT m7 G); [| assumption ..].
          exists (-1). split; [|reflexivity]. left. split; [reflexivity|].
          intros j Hj. destruct (Z.eq_dec j i) as [->|Ji]; [exact NE|]. apply NP. lia.
        + step.
          replace (h + 48 * i + 48) with (h + 48 * (i + 1)) by lia.
          replace (n_of T' - i + -1) with (n_of T' - (i + 1)) by lia.
          apply (IH (i + 1)); try assumption; try lia.
          intros j Hj. destruct (Z.eq_dec j i) as [->|Ji]; [exact NE|]. apply NP. lia. }
    replace (Z_to_bv 64 h) with (Z_to_bv 64 (h + 48 * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (n_of T')) with (Z_to_bv 64 (n_of T' - 0)) by (f_equal; lia).
    apply (LOOP (Z.to_nat (n_of T')) 0); try assumption; try lia. }
  step.
  rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (n_of T) 0) as [N0|N0]; cbn [negb].
  - pose proof (ho_rwc _ (h + 424) OP BO (ho_wr_sub _ h 480 (h + 424) (Z.of_nat (length OP)) WH ltac:(lia) ltac:(rewrite LOP; lia))) as ROP.
    rewrite LOP in ROP. clear BO.
    step.
    lazymatch goal with H : rw_cells rsegs ?mm (h + 424) _ |- _ => rename H into ROP' end.
    pose proof (rwc_cells_bytes _ _ _ ROP') as BOP'. cbn [cells_bytes cbytes] in BOP'. rewrite app_nil_r in BOP'.
    eapply (CONT _ (le8 (Z_to_bv 64 now))); try eassumption.
    replace (n_of T =? 0) with true by (symmetry; apply Z.eqb_eq; exact N0). reflexivity.
  - eapply (CONT _ OP); try eassumption.
    replace (n_of T =? 0) with false by (symmetry; apply Z.eqb_neq; exact N0). reflexivity.
Qed.
