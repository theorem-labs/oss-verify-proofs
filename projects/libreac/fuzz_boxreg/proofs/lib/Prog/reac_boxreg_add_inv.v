From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregUpd lowest_free_base_c
  reac_boxreg_add_c.
Import ListNotations.
Open Scope Z_scope.

Lemma add_row_length : forall M b k, length M = 6%nat -> length (add_row M b k) = 56%nat.
Proof.
  intros M b k HM. unfold add_row. rewrite !length_app, HM, !repeat_length, !length_le4. reflexivity.
Qed.

Lemma add_row_mac : forall M b k, length M = 6%nat -> bsub (add_row M b k) 0 6 = M.
Proof.
  intros M b k HM. unfold add_row. rewrite bsub_app_l by (rewrite ?HM; lia).
  apply bsub_whole. rewrite HM. reflexivity.
Qed.

Lemma add_row_at : forall M b k o w (P : list byte) (rest : list byte),
  length M = 6%nat -> add_row M b k = M ++ P ++ rest -> o = 6 + Z.of_nat (length P) ->
  Z.of_nat (length rest) >= w -> 0 <= w ->
  bsub (add_row M b k) o w = bsub rest 0 w.
Proof.
  intros M b k o w P rest HM E Ho Hr Hw. rewrite E, app_assoc.
  replace o with (Z.of_nat (length (M ++ P)) + 0) by (rewrite length_app, HM; lia).
  apply bsub_app_r; lia.
Qed.

Lemma add_row_base : forall M b k, length M = 6%nat -> bsub (add_row M b k) 8 4 = le4 (Z_to_bv 64 b).
Proof.
  intros M b k HM.
  rewrite (add_row_at M b k 8 4 (repeat (Z_to_bv 8 0) 2)
             (le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0)
                ++ repeat (Z_to_bv 8 0) 32))
    by (first [ exact HM | reflexivity | rewrite ?length_app, ?length_le4, ?repeat_length; cbn; lia ]).
  rewrite bsub_app_l by (try rewrite length_le4; lia). apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma add_row_nch : forall M b k, length M = 6%nat -> bsub (add_row M b k) 12 4 = le4 (Z_to_bv 64 k).
Proof.
  intros M b k HM.
  rewrite (add_row_at M b k 12 4 (repeat (Z_to_bv 8 0) 2 ++ le4 (Z_to_bv 64 b))
             (le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ repeat (Z_to_bv 8 0) 32))
    by (first [ exact HM | unfold add_row; rewrite <- !app_assoc; reflexivity
              | rewrite ?length_app, ?length_le4, ?repeat_length; cbn; lia ]).
  rewrite bsub_app_l by (try rewrite length_le4; lia). apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma add_row_est : forall M b k, length M = 6%nat -> bsub (add_row M b k) 16 4 = le4 (Z_to_bv 64 0).
Proof.
  intros M b k HM.
  rewrite (add_row_at M b k 16 4 (repeat (Z_to_bv 8 0) 2 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k))
             (le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ repeat (Z_to_bv 8 0) 32))
    by (first [ exact HM | unfold add_row; rewrite <- !app_assoc; reflexivity
              | rewrite ?length_app, ?length_le4, ?repeat_length; cbn; lia ]).
  rewrite bsub_app_l by (try rewrite length_le4; lia). apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma add_row_pin : forall M b k, length M = 6%nat -> bsub (add_row M b k) 20 4 = le4 (Z_to_bv 64 0).
Proof.
  intros M b k HM.
  rewrite (add_row_at M b k 20 4
             (repeat (Z_to_bv 8 0) 2 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0))
             (le4 (Z_to_bv 64 0) ++ repeat (Z_to_bv 8 0) 32))
    by (first [ exact HM | unfold add_row; rewrite <- !app_assoc; reflexivity
              | rewrite ?length_app, ?length_le4, ?repeat_length; cbn; lia ]).
  rewrite bsub_app_l by (try rewrite length_le4; lia). apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma add_row_name : forall M b k, length M = 6%nat -> bsub (add_row M b k) 24 32 = repeat (Z_to_bv 8 0) 32.
Proof.
  intros M b k HM.
  rewrite (add_row_at M b k 24 32
             (repeat (Z_to_bv 8 0) 2 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0)
                ++ le4 (Z_to_bv 64 0))
             (repeat (Z_to_bv 8 0) 32))
    by (first [ exact HM | unfold add_row; rewrite <- !app_assoc; reflexivity
              | rewrite ?length_app, ?length_le4, ?repeat_length; cbn; lia ]).
  apply bsub_whole. rewrite repeat_length. reflexivity.
Qed.

Lemma add_new_inv : forall bs M k b,
  boxreg_inv bs -> length M = 6%nat -> M <> zero6 -> add_none_held bs M ->
  add_width_ok k (bx_fabric bs) -> bx_n bs < 5 -> 0 <= b -> lowest_free bs k b ->
  boxreg_inv (add_bytes bs M b k).
Proof.
  intros bs M k b [[HL [H1 [H2 [H3 [H4 [H5 H6]]]]]] H7] HM HZ HNH (Hke & Hk2 & Hkf) Hn5 Hb0 Hlf.
  destruct Hlf as [(E & _) | (_ & Hbk & Hfree & _)]; [lia|].
  unfold boxreg_B1 in H1. unfold boxreg_B2 in H2.
  set (n := bx_n bs) in *.
  assert (Hn : 0 <= n <= 4) by lia.
  set (row := add_row M b k).
  assert (HR : length row = 56%nat) by (apply add_row_length; exact HM).
  pose proof (new_row_length bs row HL Hn HR) as HL'.
  pose proof (new_row_n bs row HL Hn HR) as Hn'.
  pose proof (new_row_fabric bs row HL Hn HR) as Hf'.
  pose proof (new_row_old bs row HL Hn HR) as Hold.
  pose proof (new_row_new bs row HL Hn HR) as Hnew.
  replace (add_bytes bs M b k) with (new_row_bytes bs row) by reflexivity.
  set (bs' := new_row_bytes bs row) in *.
  fold n in Hn', Hnew.
  assert (Ob : forall i, 0 <= i < n -> bx_base bs' i = bx_base bs i)
    by (intros i Hi; unfold bx_base, rd4; rewrite Hold by lia; reflexivity).
  assert (On : forall i, 0 <= i < n -> bx_nch bs' i = bx_nch bs i)
    by (intros i Hi; unfold bx_nch, rd4; rewrite Hold by lia; reflexivity).
  assert (Oe : forall i, 0 <= i < n -> bx_established bs' i = bx_established bs i)
    by (intros i Hi; unfold bx_established, rd4; rewrite Hold by lia; reflexivity).
  assert (Op : forall i, 0 <= i < n -> bx_pinned bs' i = bx_pinned bs i)
    by (intros i Hi; unfold bx_pinned, rd4; rewrite Hold by lia; reflexivity).
  assert (Onm : forall i, 0 <= i < n -> bx_name bs' i = bx_name bs i)
    by (intros i Hi; unfold bx_name; rewrite Hold by lia; reflexivity).
  assert (Om : forall i, 0 <= i < n -> bx_mac bs' i = bx_mac bs i).
  { intros i Hi. unfold bx_mac. replace (56 * i) with (56 * i + 0) by lia. rewrite Hold by lia. reflexivity. }
  assert (Nb : bx_base bs' n = b).
  { apply rd4_le4; [lia|]. rewrite Hnew by lia. apply add_row_base. exact HM. }
  assert (Nn : bx_nch bs' n = k).
  { apply rd4_le4; [lia|]. rewrite Hnew by lia. apply add_row_nch. exact HM. }
  assert (Ne : bx_established bs' n = 0).
  { apply rd4_le4; [lia|]. rewrite Hnew by lia. apply add_row_est. exact HM. }
  assert (Np : bx_pinned bs' n = 0).
  { apply rd4_le4; [lia|]. rewrite Hnew by lia. apply add_row_pin. exact HM. }
  assert (Nnm : bx_name bs' n = repeat (Z_to_bv 8 0) 32).
  { unfold bx_name. rewrite Hnew by lia. apply add_row_name. exact HM. }
  assert (Nm : bx_mac bs' n = M).
  { unfold bx_mac. replace (56 * n) with (56 * n + 0) by lia. rewrite Hnew by lia. apply add_row_mac. exact HM. }
  assert (Split : forall i, 0 <= i < bx_n bs' -> 0 <= i < n \/ i = n) by (intros i Hi; rewrite Hn' in Hi; lia).
  split.
  - split; [exact HL'|].
    split; [unfold boxreg_B1; rewrite Hn'; lia|].
    split; [unfold boxreg_B2; rewrite Hf'; lia|].
    split.
    { unfold boxreg_B3. intros i Hi. rewrite Hf'.
      destruct (Split i Hi) as [Ho | ->].
      - rewrite Ob, On by exact Ho. destruct (H3 i Ho) as (A1 & A2 & A3 & A4 & A5). auto.
      - rewrite Nb, Nn. split; [exact Hke|]. lia. }
    split.
    { unfold boxreg_B4. intros i j Hi Hij Hj. rewrite Hn' in Hj.
      destruct (Z.lt_ge_cases j n) as [Hjn | Hjn].
      - rewrite Ob, On, Ob, On by lia. apply H4; lia.
      - assert (j = n) by lia. subst j. rewrite Ob, On, Nb, Nn by lia.
        intros Hm. apply Hfree. exists i. split; [lia|]. unfold meets in *. lia. }
    split.
    { unfold boxreg_B5. intros i j Hi Hij Hj. rewrite Hn' in Hj.
      destruct (Z.lt_ge_cases j n) as [Hjn | Hjn].
      - rewrite Om, Om by lia. apply H5; lia.
      - assert (j = n) by lia. subst j. rewrite Om, Nm by lia.
        right. apply HNH. lia. }
    { unfold boxreg_B6. intros i Hi. destruct (Split i Hi) as [Ho | ->].
      - rewrite Onm by exact Ho. apply H6. exact Ho.
      - rewrite Nnm. apply In_zero_repeat. lia. }
  - unfold boxreg_B7. intros i Hi. destruct (Split i Hi) as [Ho | ->].
    + rewrite Op, Oe by exact Ho. apply H7. exact Ho.
    + rewrite Np, Ne. split; [left; reflexivity | reflexivity].
Qed.

Lemma add_bind_inv : forall bs M k z,
  boxreg_inv bs -> length M = 6%nat -> M <> zero6 -> add_none_held bs M -> add_unbound bs k z ->
  boxreg_inv (upd_bytes bs (Z.to_nat (56 * z)) M).
Proof.
  intros bs M k z [[HL [H1 [H2 [H3 [H4 [H5 H6]]]]]] H7] HM HZ HNH (Hz & Hzm & Hzk & _).
  unfold boxreg_B1 in H1. unfold boxreg_B2 in H2.
  assert (Hz4 : 0 <= z <= 4) by lia.
  replace (upd_bytes bs (Z.to_nat (56 * z)) M) with (bind_bytes bs M z) by reflexivity.
  pose proof (bind_length bs M z HL Hz4 HM) as HL'.
  pose proof (bind_other bs M z HL Hz4 HM) as Ho.
  pose proof (bind_mac bs M z HL Hz4 HM) as Hm.
  set (bs' := bind_bytes bs M z) in *.
  assert (En : bx_n bs' = bx_n bs) by (unfold bx_n, rd4; rewrite Ho by lia; reflexivity).
  assert (Ef : bx_fabric bs' = bx_fabric bs) by (unfold bx_fabric, rd4; rewrite Ho by lia; reflexivity).
  assert (Eb : forall i, 0 <= i < bx_n bs -> bx_base bs' i = bx_base bs i).
  { intros i Hi. unfold bx_base, rd4. rewrite Ho; [reflexivity | lia | lia | lia |].
    destruct (Z.lt_ge_cases i z); [left | right]; lia. }
  assert (Ek : forall i, 0 <= i < bx_n bs -> bx_nch bs' i = bx_nch bs i).
  { intros i Hi. unfold bx_nch, rd4. rewrite Ho; [reflexivity | lia | lia | lia |].
    destruct (Z.lt_ge_cases i z); [left | right]; lia. }
  assert (Ee : forall i, 0 <= i < bx_n bs -> bx_established bs' i = bx_established bs i).
  { intros i Hi. unfold bx_established, rd4. rewrite Ho; [reflexivity | lia | lia | lia |].
    destruct (Z.lt_ge_cases i z); [left | right]; lia. }
  assert (Ep : forall i, 0 <= i < bx_n bs -> bx_pinned bs' i = bx_pinned bs i).
  { intros i Hi. unfold bx_pinned, rd4. rewrite Ho; [reflexivity | lia | lia | lia |].
    destruct (Z.lt_ge_cases i z); [left | right]; lia. }
  assert (Enm : forall i, 0 <= i < bx_n bs -> bx_name bs' i = bx_name bs i).
  { intros i Hi. unfold bx_name. rewrite Ho; [reflexivity | lia | lia | lia |].
    destruct (Z.lt_ge_cases i z); [left | right]; lia. }
  assert (Em : forall i, 0 <= i < bx_n bs -> i <> z -> bx_mac bs' i = bx_mac bs i).
  { intros i Hi Hne. unfold bx_mac. rewrite Ho; [reflexivity | lia | lia | lia |].
    destruct (Z.lt_ge_cases i z); [left | right]; lia. }
  assert (Mz : bx_mac bs' z = M) by exact Hm.
  split.
  - split; [exact HL'|].
    split; [unfold boxreg_B1; rewrite En; lia|].
    split; [unfold boxreg_B2; rewrite Ef; lia|].
    split.
    { unfold boxreg_B3. intros i Hi. rewrite En in Hi. rewrite Ef, Eb, Ek by exact Hi. apply H3. exact Hi. }
    split.
    { unfold boxreg_B4. intros i j Hi Hij Hj. rewrite En in Hj. rewrite !Eb, !Ek by lia. apply H4; lia. }
    split.
    { unfold boxreg_B5. intros i j Hi Hij Hj. rewrite En in Hj.
      destruct (Z.eq_dec i z) as [-> | Hiz]; [|destruct (Z.eq_dec j z) as [-> | Hjz]].
      - rewrite Mz, Em by lia. right. intros E. apply (HNH j); [lia|]. symmetry. exact E.
      - rewrite Mz, Em by lia.
        destruct (decide (bx_mac bs i = zero6)) as [E | E]; [left; exact E|].
        right. apply HNH. lia.
      - rewrite !Em by lia. apply H5; lia. }
    { unfold boxreg_B6. intros i Hi. rewrite En in Hi. rewrite Enm by exact Hi. apply H6. exact Hi. }
  - unfold boxreg_B7. intros i Hi. rewrite En in Hi. rewrite Ep, Ee by exact Hi. apply H7. exact Hi.
Qed.

Theorem reac_boxreg_add_keeps_inv_holds : reac_boxreg_add_keeps_inv.
Proof.
  unfold reac_boxreg_add_keeps_inv.
  intros bs M bs' k z HI HM HO.
  destruct HO as [(_ & _ & ->) | [(_ & _ & _ & ->) | [(_ & HZ & HNH & HU & ->) | [(_ & _ & _ & _ & _ & _ & ->) |
                  (Hw & HZ & HNH & _ & Hn5 & _ & b & Hb0 & Hlf & ->)]]]].
  - exact HI.
  - exact HI.
  - eapply add_bind_inv; eassumption.
  - exact HI.
  - eapply add_new_inv; eassumption.
Qed.
