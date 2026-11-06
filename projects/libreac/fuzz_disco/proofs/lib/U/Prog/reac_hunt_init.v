From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import memset_c memcpy_c reac_disco_table_init_c reac_disco_peer_lock_init_c reac_hunt_init_c.
Import ListNotations.
Open Scope Z_scope.

Lemma hi_rep_sub : forall m a (b : byte) n k n', bytes_at rsegs m a (repeat b n) -> 0 <= k -> Z.of_nat n' + k <= Z.of_nat n ->
  bytes_at rsegs m (a + k) (repeat b n').
Proof.
  intros m a b n k n' (H1 & H2 & H) Hk Hn. unfold bytes_at. rewrite !repeat_length in *. split; [lia|]. split; [lia|].
  intros i Hi. rewrite nth_error_repeat by exact Hi.
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  rewrite H by lia. apply nth_error_repeat. lia.
Qed.

Lemma hi_wr_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> a' + n' <= a + n -> wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma hi_rwc : forall m a bs n, bytes_at rsegs m a bs -> wr_at rsegs m a n -> Z.of_nat (length bs) = n ->
  rw_cells rsegs m a [CB (length bs) bs].
Proof. intros m a bs n B W E. apply rw_cells_of_u8arr. split; [exact B | rewrite E; exact W]. Qed.

Lemma hi_cat : forall m a b bs1 bs2, bytes_at rsegs m a bs1 -> bytes_at rsegs m b bs2 -> b = a + Z.of_nat (length bs1) ->
  bytes_at rsegs m a (bs1 ++ bs2).
Proof. intros m a b bs1 bs2 B1 B2 E. apply bytes_at_app. subst b. split; assumption. Qed.

Lemma hi_bytes_of_rwc : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs H. apply u8arr_of_rw_cells in H. destruct H as [B _]. exact B. Qed.

Lemma hi_piece : forall m h k n, bytes_at rsegs m h (repeat (Z_to_bv 8 0) 480) -> wr_at rsegs m h 480 ->
  0 <= k -> Z.of_nat n + k <= 480 -> rw_cells rsegs m (h + k) [CB n (repeat (Z_to_bv 8 0) n)].
Proof.
  intros m h k n B W Hk Hn.
  pose proof (hi_rep_sub m h _ 480 k n B Hk ltac:(lia)) as B'.
  pose proof (hi_rwc m (h + k) _ (Z.of_nat n) B' (hi_wr_sub m h 480 (h + k) (Z.of_nat n) W ltac:(lia) ltac:(lia))
                ltac:(rewrite repeat_length; reflexivity)) as R.
  rewrite repeat_length in R. exact R.
Qed.

Lemma hi_assemble : forall m h OBx now,
  length OBx = 6%nat ->
  rw_cells rsegs m h [CB 400 zero_table] -> rw_cells rsegs m (h + 400) [CB 12 (repeat (zb 0) 12)] ->
  rw_cells rsegs m (h + 412) [CB 6 OBx] -> rw_cells rsegs m (h + 418) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
  rw_cells rsegs m (h + 424) [C8 (Z_to_bv 64 now)] -> rw_cells rsegs m (h + 432) [CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells rsegs m (h + 440) [C4 (Z_to_bv 64 0)] -> rw_cells rsegs m (h + 444) [CB 36 (repeat (Z_to_bv 8 0) 36)] ->
  bytes_at rsegs m h (hunt_init_bytes OBx now).
Proof.
  intros m h OBx now HL R1 R2 R3 R4 R5 R6 R7 R8.
  apply hi_bytes_of_rwc in R1, R2, R3, R4, R6, R8.
  destruct R5 as [[_ B5] _]. destruct R7 as [[_ B7] _]. cbn [cells_bytes cbytes] in B5, B7. rewrite app_nil_r in B5, B7.
  unfold hunt_init_bytes.
  replace (repeat (Z_to_bv 8 0) 412) with (zero_table ++ repeat (zb 0) 12) by reflexivity.
  replace (repeat (Z_to_bv 8 0) 48) with (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 0) ++ repeat (Z_to_bv 8 0) 36)
    by reflexivity.
  rewrite <- !app_assoc.
  apply (hi_cat m h (h + 400)); [exact R1 | | unfold zero_table; rewrite repeat_length; reflexivity].
  apply (hi_cat m (h + 400) (h + 412)); [exact R2 | | rewrite repeat_length; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply (hi_cat m (h + 412) (h + 418)); [exact R3 | | rewrite HL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply (hi_cat m (h + 418) (h + 424)); [exact R4 | | rewrite repeat_length; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply (hi_cat m (h + 424) (h + 432)); [exact B5 | | rewrite length_le8; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply (hi_cat m (h + 432) (h + 440)); [exact R6 | | rewrite repeat_length; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
  apply (hi_cat m (h + 440) (h + 444)); [exact B7 | exact R8 | rewrite length_le4; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.

Lemma hi_first400 : forall OBx now, firstn 400 (hunt_init_bytes OBx now) = zero_table.
Proof.
  intros OBx now. unfold hunt_init_bytes. rewrite firstn_app, repeat_length.
  change (400 - 412)%nat with 0%nat. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma hi_lock12 : forall OBx now, firstn 12 (skipn 400 (hunt_init_bytes OBx now)) = repeat (zb 0) 12.
Proof.
  intros OBx now. unfold hunt_init_bytes. rewrite skipn_app, repeat_length.
  change (skipn 400 (repeat (Z_to_bv 8 0) 412)) with (repeat (Z_to_bv 8 0) 12).
  change (400 - 412)%nat with 0%nat. cbn [skipn].
  rewrite firstn_app, repeat_length. change (12 - 12)%nat with 0%nat. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Ltac zc HC := unfold bv_eqb, bv_ltu in HC; rewrite ?unsigned_lit_wrap in HC; zify_bool HC; Z.div_mod_to_equations; lia.

Ltac hi_tr MUc WMc :=
  lazymatch type of MUc with munch _ ?m1 ?m2 =>
    transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc;
    try match goal with Hm : mem_inv rsegs m1 |- _ => clear Hm end; try clear m1 end.

Ltac hi_ret n := rewrite (ret_pc_even n) by (first [lia | reflexivity]).

Lemma land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac zcu HC := unfold bv_eqb, bv_ltu in HC; rewrite ?unsigned_lit_wrap in HC; try change (bv_wrap 64 7) with 7 in HC;
  rewrite ?land7 in HC; zify_bool HC; Z.div_mod_to_equations; lia.

Theorem reac_hunt_init_holds :
  memset_contract -> reac_disco_table_init_contract -> reac_disco_peer_lock_init_contract -> memcpy_contract ->
  reac_hunt_init_contract.
Proof.
  intros MSC TIC PLC MCC. unfold reac_hunt_init_contract, REAC_HUNT_INIT.
  unfold memset_contract, MEMSET in MSC. unfold memcpy_contract in MCC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    h our now lo junk ob E0 Hh H8 RH E1 Hour HOB E2 Hnow ST HLO HD MI.
  subst a0 a1 a2.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Hlo & Hhi & _).
  pose proof (rw_cells_bound rsegs m h _ RH) as HB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (h, h + 480)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (Z.eqb_spec our 0) as [O0 | O1].
  - subst our. clear HOB. cbv iota.
    carve_frame 32%nat ST.
    step. step. step. step. step. step. step. step. step. step. step.
    eapply evt_cut.
    { eapply MSC with (junk := junk); [ | eassumption ].
      rewrite (unsigned_lit h) by lia. change (Z.to_nat (bv_unsigned (Z_to_bv 64 480))) with 480%nat. eassumption. }
    intros ms' PO. unfold memset_post in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & Eq & MUc & WMc & MIc & RVc).
    subst ms'.
    rewrite (unsigned_lit h) in MUc, RVc by lia.
    change (bv_unsigned (Z_to_bv 64 480)) with 480 in MUc, RVc.
    change (Z.to_nat 480) with 480%nat in RVc.
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RVc.
    hi_tr MUc WMc.
    apply u8arr_of_rw_cells in RVc. destruct RVc as [BZ WH]. rewrite repeat_length in WH. change (Z.of_nat 480) with 480 in WH.
    pose proof (hi_piece m2 h 0 400 BZ WH ltac:(lia) ltac:(lia)) as R1. rewrite Z.add_0_r in R1.
    pose proof (hi_piece m2 h 412 6 BZ WH ltac:(lia) ltac:(lia)) as R3.
    pose proof (hi_piece m2 h 418 6 BZ WH ltac:(lia) ltac:(lia)) as R4.
    pose proof (hi_piece m2 h 424 8 BZ WH ltac:(lia) ltac:(lia)) as R5.
    pose proof (hi_piece m2 h 432 8 BZ WH ltac:(lia) ltac:(lia)) as R6.
    pose proof (hi_piece m2 h 440 4 BZ WH ltac:(lia) ltac:(lia)) as R7.
    pose proof (hi_piece m2 h 444 36 BZ WH ltac:(lia) ltac:(lia)) as R8.
    clear BZ.
    hi_ret 91296.
    step. if_cases HCa; [exfalso; zcu HCa | ]. step. step. if_cases HCb; [exfalso; zcu HCb | ].
    step. step.
    eapply evt_cut.
    { eapply TIC with (t := h) (junk := repeat (Z_to_bv 8 0) 400); [reflexivity | lia | exact H8 | exact R1 | exact MIc]. }
    intros ms' (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m3 & Eq & MUc & WMc & MI3 & RVt & TOK).
    subst ms'. clear MIc. hi_tr MUc WMc.
    hi_ret 91316.
    step. step.
    eapply evt_cut.
    { eapply PLC with (l := h + 400);
        [reflexivity | Z.div_mod_to_equations; lia | exact (hi_wr_sub m3 h 480 (h + 400) 12 WH ltac:(lia) ltac:(lia)) | exact MI3]. }
    intros ms' (m4 & Eq & MUc & WMc & MI4 & Q2 & LOK).
    subst ms'. clear MI3. hi_tr MUc WMc.
    pose proof (hi_rwc m4 (h + 400) _ 12 Q2 (hi_wr_sub m4 h 480 (h + 400) 12 WH ltac:(lia) ltac:(lia))
                  ltac:(rewrite repeat_length; reflexivity)) as R2.
    rewrite repeat_length in R2. clear Q2.
    hi_ret 91324.
    step.
    if_cases HC.
    2: { exfalso. zc HC. }
    clear HC.
    step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    step.
    apply evt_done. do 16 eexists.
    split; [reflexivity |]. split; [exact MU |]. split; [exact WM |]. split; [eassumption |]. split; [exact ST |].
    split; [ | split; [rewrite hi_first400; exact TOK | rewrite hi_lock12; exact LOK]].
    eapply hi_assemble; [ | eassumption .. ].
    reflexivity.
  - destruct (HOB O1) as (OB & HL & HD1 & HD2). clear HOB.
    cbv iota.
    carve_frame 32%nat ST.
    step. step. step. step. step. step. step. step. step. step. step.
    eapply evt_cut.
    { eapply MSC with (junk := junk); [ | eassumption ].
      rewrite (unsigned_lit h) by lia. change (Z.to_nat (bv_unsigned (Z_to_bv 64 480))) with 480%nat. eassumption. }
    intros ms' PO. unfold memset_post in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & Eq & MUc & WMc & MIc & RVc).
    subst ms'.
    rewrite (unsigned_lit h) in MUc, RVc by lia.
    change (bv_unsigned (Z_to_bv 64 480)) with 480 in MUc, RVc.
    change (Z.to_nat 480) with 480%nat in RVc.
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RVc.
    hi_tr MUc WMc.
    apply u8arr_of_rw_cells in RVc. destruct RVc as [BZ WH]. rewrite repeat_length in WH. change (Z.of_nat 480) with 480 in WH.
    pose proof (hi_piece m2 h 0 400 BZ WH ltac:(lia) ltac:(lia)) as R1. rewrite Z.add_0_r in R1.
    pose proof (hi_piece m2 h 412 6 BZ WH ltac:(lia) ltac:(lia)) as R3.
    pose proof (hi_piece m2 h 418 6 BZ WH ltac:(lia) ltac:(lia)) as R4.
    pose proof (hi_piece m2 h 424 8 BZ WH ltac:(lia) ltac:(lia)) as R5.
    pose proof (hi_piece m2 h 432 8 BZ WH ltac:(lia) ltac:(lia)) as R6.
    pose proof (hi_piece m2 h 440 4 BZ WH ltac:(lia) ltac:(lia)) as R7.
    pose proof (hi_piece m2 h 444 36 BZ WH ltac:(lia) ltac:(lia)) as R8.
    clear BZ.
    hi_ret 91296.
    step. if_cases HCa; [exfalso; zcu HCa | ]. step. step. if_cases HCb; [exfalso; zcu HCb | ].
    step. step.
    eapply evt_cut.
    { eapply TIC with (t := h) (junk := repeat (Z_to_bv 8 0) 400); [reflexivity | lia | exact H8 | exact R1 | exact MIc]. }
    intros ms' (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m3 & Eq & MUc & WMc & MI3 & RVt & TOK).
    subst ms'. clear MIc. hi_tr MUc WMc.
    hi_ret 91316.
    step. step.
    eapply evt_cut.
    { eapply PLC with (l := h + 400);
        [reflexivity | Z.div_mod_to_equations; lia | exact (hi_wr_sub m3 h 480 (h + 400) 12 WH ltac:(lia) ltac:(lia)) | exact MI3]. }
    intros ms' (m4 & Eq & MUc & WMc & MI4 & Q2 & LOK).
    subst ms'. clear MI3. hi_tr MUc WMc.
    pose proof (hi_rwc m4 (h + 400) _ 12 Q2 (hi_wr_sub m4 h 480 (h + 400) 12 WH ltac:(lia) ltac:(lia))
                  ltac:(rewrite repeat_length; reflexivity)) as R2.
    rewrite repeat_length in R2. clear Q2.
    hi_ret 91324.
    step.
    if_cases HC.
    { exfalso. zc HC. }
    clear HC.
    step. step. step. step.
    eapply evt_cut.
    { eapply MCC with (src := ob) (junk := repeat (Z_to_bv 8 0) 6).
      - rewrite (unsigned_lit our) by lia. exact OB.
      - rewrite HL. reflexivity.
      - rewrite (unsigned_lit (h + 412)) by lia. change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat. exact R3.
      - rewrite (unsigned_lit our), (unsigned_lit (h + 412)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6. lia.
      - exact MI4. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m5 & Eq & MUc & WMc & MI5 & RVm & OBm).
    subst ms'. clear MI4.
    rewrite (unsigned_lit (h + 412)) in MUc, RVm by lia. rewrite (unsigned_lit our) in OBm by lia.
    change (bv_unsigned (Z_to_bv 64 6)) with 6 in MUc. change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat in RVm.
    hi_tr MUc WMc.
    hi_ret 91344.
    step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    step.
    apply evt_done. do 16 eexists.
    split; [reflexivity |]. split; [exact MU |]. split; [exact WM |]. split; [eassumption |]. split; [exact ST |].
    split; [ | split; [rewrite hi_first400; exact TOK | rewrite hi_lock12; exact LOK]].
    eapply hi_assemble; [ | eassumption .. ].
    exact HL.
Qed.
