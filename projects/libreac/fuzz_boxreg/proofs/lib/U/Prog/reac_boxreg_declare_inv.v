From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregUpd lowest_free_base_c printf_facts_c
  reac_boxreg_declare_c.
Import ListNotations.
Open Scope Z_scope.

Lemma name_field_length : forall s, length (name_field s) = 32%nat.
Proof.
  intros s. unfold name_field, pf_bytes. rewrite length_app, length_map, length_firstn, repeat_length. lia.
Qed.

Lemma name_field_zero : forall s, In (Z_to_bv 8 0) (name_field s).
Proof.
  intros s. unfold name_field. apply in_or_app. right. apply In_zero_repeat. lia.
Qed.

Lemma decl_row_length : forall b k p s, length (decl_row b k p s) = 56%nat.
Proof.
  intros. unfold decl_row. rewrite !length_app, repeat_length, !length_le4, name_field_length. reflexivity.
Qed.

Lemma decl_row_mac : forall b k p s, bsub (decl_row b k p s) 0 6 = zero6.
Proof. intros. reflexivity. Qed.

Lemma decl_row_base : forall b k p s, bsub (decl_row b k p s) 8 4 = le4 (Z_to_bv 64 b).
Proof.
  intros. unfold decl_row.
  replace 8 with (Z.of_nat (length (repeat (Z_to_bv 8 0) 8)) + 0) by reflexivity.
  rewrite bsub_app_r by lia. rewrite bsub_app_l by (try rewrite length_le4; lia).
  apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma decl_row_nch : forall b k p s, bsub (decl_row b k p s) 12 4 = le4 (Z_to_bv 64 k).
Proof.
  intros. unfold decl_row. rewrite app_assoc.
  replace 12 with (Z.of_nat (length (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b))) + 0)
    by (rewrite length_app, repeat_length, length_le4; reflexivity).
  rewrite bsub_app_r by lia. rewrite bsub_app_l by (try rewrite length_le4; lia).
  apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma decl_row_est : forall b k p s, bsub (decl_row b k p s) 16 4 = le4 (Z_to_bv 64 0).
Proof.
  intros. unfold decl_row.
  replace (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0)
             ++ le4 (Z_to_bv 64 p) ++ name_field s)
    with ((repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k))
             ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 p) ++ name_field s) by (rewrite <- !app_assoc; reflexivity).
  replace 16 with (Z.of_nat (length (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k))) + 0)
    by (rewrite !length_app, repeat_length, !length_le4; reflexivity).
  rewrite bsub_app_r by lia. rewrite bsub_app_l by (try rewrite length_le4; lia).
  apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma decl_row_pin : forall b k p s, bsub (decl_row b k p s) 20 4 = le4 (Z_to_bv 64 p).
Proof.
  intros. unfold decl_row.
  replace (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0)
             ++ le4 (Z_to_bv 64 p) ++ name_field s)
    with ((repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0))
             ++ le4 (Z_to_bv 64 p) ++ name_field s) by (rewrite <- !app_assoc; reflexivity).
  replace 20 with (Z.of_nat (length (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k)
                                       ++ le4 (Z_to_bv 64 0))) + 0)
    by (rewrite !length_app, repeat_length, !length_le4; reflexivity).
  rewrite bsub_app_r by lia. rewrite bsub_app_l by (try rewrite length_le4; lia).
  apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma decl_row_name : forall b k p s, bsub (decl_row b k p s) 24 32 = name_field s.
Proof.
  intros. unfold decl_row.
  replace (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0)
             ++ le4 (Z_to_bv 64 p) ++ name_field s)
    with ((repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0)
             ++ le4 (Z_to_bv 64 p)) ++ name_field s) by (rewrite <- !app_assoc; reflexivity).
  replace 24 with (Z.of_nat (length (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k)
                                       ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 p))) + 0)
    by (rewrite !length_app, repeat_length, !length_le4; reflexivity).
  rewrite bsub_app_r by lia.
  apply bsub_whole. rewrite name_field_length. reflexivity.
Qed.

Theorem reac_boxreg_declare_keeps_inv_holds : reac_boxreg_declare_keeps_inv.
Proof.
  unfold reac_boxreg_declare_keeps_inv.
  intros bs s k b0 b p [[HL [H1 [H2 [H3 [H4 [H5 H6]]]]]] H7] [Hw [Hn5 Hc]].
  assert (Hb : 0 <= b /\ b + k <= bx_fabric bs /\ ~ slice_meets bs b k /\ (p = 0 \/ p = 1)).
  { destruct Hc as [(_ & -> & -> & Hr0 & Hr1 & Hr2) | (_ & -> & Hb0 & Hlf)].
    - auto.
    - destruct Hlf as [(E & _) | (_ & Hl1 & Hl2 & _)]; [lia | auto]. }
  destruct Hb as (Hb0 & Hbk & Hfree & Hp).
  destruct Hw as (Hke & Hk2 & Hkf).
  unfold boxreg_B1 in H1. unfold boxreg_B2 in H2.
  set (n := bx_n bs) in *.
  assert (Hn : 0 <= n <= 4) by lia.
  set (row := decl_row b k p s).
  assert (HR : length row = 56%nat) by apply decl_row_length.
  pose proof (new_row_length bs row HL Hn HR) as HL'.
  pose proof (new_row_n bs row HL Hn HR) as Hn'.
  pose proof (new_row_fabric bs row HL Hn HR) as Hf'.
  pose proof (new_row_old bs row HL Hn HR) as Hold.
  pose proof (new_row_new bs row HL Hn HR) as Hnew.
  replace (decl_bytes bs b k p s) with (new_row_bytes bs row) by reflexivity.
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
  { apply rd4_le4; [lia|]. rewrite Hnew by lia. apply decl_row_base. }
  assert (Nn : bx_nch bs' n = k).
  { apply rd4_le4; [lia|]. rewrite Hnew by lia. apply decl_row_nch. }
  assert (Ne : bx_established bs' n = 0).
  { apply rd4_le4; [lia|]. rewrite Hnew by lia. apply decl_row_est. }
  assert (Np : bx_pinned bs' n = p).
  { apply rd4_le4; [lia|]. rewrite Hnew by lia. apply decl_row_pin. }
  assert (Nnm : bx_name bs' n = name_field s).
  { unfold bx_name. rewrite Hnew by lia. apply decl_row_name. }
  assert (Nm : bx_mac bs' n = zero6).
  { unfold bx_mac. replace (56 * n) with (56 * n + 0) by lia. rewrite Hnew by lia. apply decl_row_mac. }
  assert (Split : forall i, 0 <= i < bx_n bs' -> 0 <= i < n \/ i = n) by (intros i Hi; rewrite Hn' in Hi; lia).
  split; [|].
  - split; [exact HL'|].
    split; [unfold boxreg_B1; rewrite Hn'; lia|].
    split; [unfold boxreg_B2; rewrite Hf'; lia|].
    split.
    { unfold boxreg_B3. intros i Hi. rewrite Hf'.
      destruct (Split i Hi) as [Ho | ->].
      - rewrite Ob, On by exact Ho. destruct (H3 i Ho) as (A1 & A2 & A3 & A4 & A5). auto.
      - rewrite Nb, Nn. lia || (split; [exact Hke|]; lia). }
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
        destruct (decide (bx_mac bs i = zero6)) as [E | E]; [left | right]; exact E. }
    { unfold boxreg_B6. intros i Hi. destruct (Split i Hi) as [Ho | ->].
      - rewrite Onm by exact Ho. apply H6. exact Ho.
      - rewrite Nnm. apply name_field_zero. }
  - unfold boxreg_B7. intros i Hi. destruct (Split i Hi) as [Ho | ->].
    + rewrite Op, Oe by exact Ho. apply H7. exact Ho.
    + rewrite Np, Ne. split; [exact Hp | reflexivity].
Qed.
