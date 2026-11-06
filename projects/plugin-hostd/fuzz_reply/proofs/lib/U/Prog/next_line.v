From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memchr_c next_line_c.
Import ListNotations.
Open Scope Z_scope.

Definition keep (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (keep T) in H.

Lemma land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma sltu_pos : forall x : word, 0 < bv_unsigned x -> v_sltu (Z_to_bv 64 0) x = Z_to_bv 64 1.
Proof.
  intros x H. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit 0) by lia.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

Lemma sltiu1_nz : forall z, 1 <= z < 2^64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z H. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  rewrite (proj2 (Z.ltb_ge z 1) ltac:(lia)). reflexivity.
Qed.

Lemma disj_hd : forall lo hi W a n, disjoint_from ((lo, hi) :: W) a n -> disjoint_from [(lo, hi)] a n.
Proof. intros lo hi W a n [H _]. split; [exact H | exact I]. Qed.

Lemma ro_of_bytes8 : forall m A (v : word), bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma byte0_eq : forall b : byte, bv_unsigned b = 0 -> b = Z_to_bv 8 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma first_zero : forall l : list byte, In (Z_to_bv 8 0) l ->
  exists l1 l2, l = l1 ++ Z_to_bv 8 0 :: l2 /\ ~ In (Z_to_bv 8 0) l1.
Proof.
  induction l as [|b l IH]; intros H; [destruct H|].
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E].
  - exists [], l. split; [rewrite (byte0_eq b E); reflexivity | intros []].
  - destruct H as [H|H].
    + exfalso. apply E. rewrite H. reflexivity.
    + destruct (IH H) as (l1 & l2 & -> & N). exists (b :: l1), l2. split; [reflexivity|].
      intros [H'|H']; [apply E; rewrite H'; reflexivity | exact (N H')].
Qed.

Lemma find_first : forall ln rest, ~ In (Z_to_bv 8 0) ln ->
  find_byte 0 (ln ++ Z_to_bv 8 0 :: rest) = Some (length ln).
Proof.
  intros ln rest N. apply find_byte_hit; [|reflexivity].
  intros b Hb E. apply N. rewrite <- (byte0_eq b E). exact Hb.
Qed.

Lemma memchr_line_ok : forall P c n ln rest, c = 0 -> n = Z.of_nat (length (ln ++ Z_to_bv 8 0 :: rest)) ->
  ~ In (Z_to_bv 8 0) ln -> memchr_ok P c n (ln ++ Z_to_bv 8 0 :: rest).
Proof.
  intros P c n ln rest -> -> N. unfold memchr_ok. rewrite Nat2Z.id, firstn_all, (find_first ln rest N). left; lia.
Qed.

Lemma memchr_line_res : forall P c n ln rest, c = 0 -> n = Z.of_nat (length (ln ++ Z_to_bv 8 0 :: rest)) ->
  ~ In (Z_to_bv 8 0) ln -> memchr_res P c n (ln ++ Z_to_bv 8 0 :: rest) = P + Z.of_nat (length ln).
Proof.
  intros P c n ln rest -> -> N. unfold memchr_res. rewrite Nat2Z.id, firstn_all, (find_first ln rest N). reflexivity.
Qed.

Lemma rw_cells_C8_eq : forall m A (v v' : word), rw_cells rsegs m A [C8 v] -> v = v' -> rw_cells rsegs m A [C8 v'].
Proof. intros; subst; assumption. Qed.

Lemma bytes_at_skipn : forall m P (l : list byte) k, bytes_at rsegs m P l -> (k <= length l)%nat ->
  bytes_at rsegs m (P + Z.of_nat k) (skipn k l).
Proof.
  intros m P l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.

Theorem next_line_holds : memchr_contract -> next_line_contract.
Proof.
  intros MCH. unfold next_line_contract, NEXT_LINE, NEXT_LINE_FRAME, G_NOUT, G_OUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo PA PL PN
    at0 nout out jl jn ob.
  cbv zeta.
  intros ST LO MI CA CL CN AA AL AN DA DL DN GN DGN GO DGO OB OL DOB AO HP.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word at0) as Rat. pose proof (zr_word nout) as Rno.
  pose proof (zr_word out) as Rou. unfold inr64 in *.
  pose proof (rw_cells_bound _ _ _ _ CA) as BA. pose proof (rw_cells_bound _ _ _ _ CL) as BL.
  pose proof (rw_cells_bound _ _ _ _ CN) as BN. cbn [cells_size csize Z.of_nat] in BA, BL, BN.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (bytes_at_bound _ _ _ _ OB) as BOB.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (PA, PA + 8); (PL, PL + 8); (PN, PN + 8)] m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MUF.
  pose proof (wmono_refl rsegs m) as WM.
  hide CA. hide CL. hide CN. hide GN. hide GO. hide OB. hide HP.
  carve_frame 48%nat ST.
  step. step. step. step. step. step.
  unfold keep in CA, CL, CN, GN, GO, OB. rewrite <- OL in DOB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_transport rsegs _ m mm _ _ CA MUF WM (disj_hd _ _ _ _ _ DA)) as CA1;
    pose proof (rw_cells_transport rsegs _ m mm _ _ CL MUF WM (disj_hd _ _ _ _ _ DL)) as CL1;
    pose proof (rw_cells_transport rsegs _ m mm _ _ CN MUF WM (disj_hd _ _ _ _ _ DN)) as CN1;
    pose proof (bytes_at_transport rsegs _ m mm _ _ GN MU DGN) as GN1;
    pose proof (bytes_at_transport rsegs _ m mm _ _ GO MU DGO) as GO1;
    pose proof (bytes_at_transport rsegs _ m mm _ _ OB MU DOB) as OB1
  end.
  pose proof (ro_of_bytes8 _ _ _ GN1) as RN1. pose proof (ro_of_bytes8 _ _ _ GO1) as RO1.
  step. step. step. if_cases HT; [exfalso; zify_cond HT; rewrite ?land7 in HT; Z.div_mod_to_equations; lia |]. clear HT.
  step. step. step. step. step. step. step.
  if_cases HB.
  - zify_cond HB. clear MUF.
    unfold keep in HP. destruct (HP ltac:(lia)) as [OUTP INZ]. clear HP.
    destruct (first_zero _ INZ) as (ln & rest & SK & NZ).
    pose proof (bytes_at_skipn _ _ _ (Z.to_nat (bv_unsigned at0)) OB1 ltac:(lia)) as OBA.
    rewrite Z2Nat.id in OBA by lia. rewrite SK in OBA.
    assert (LL : Z.of_nat (length (ln ++ Z_to_bv 8 0 :: rest)) = bv_unsigned nout - bv_unsigned at0).
    { rewrite <- SK, length_skipn. lia. }
    assert (LNB : Z.of_nat (length ln) < bv_unsigned nout - bv_unsigned at0).
    { rewrite <- LL, length_app. cbn [length]. lia. }
    step. step. step. if_cases HT; [exfalso; zify_cond HT; Z.div_mod_to_equations; lia |]. clear HT.
    step. step. step. step.
    rewrite (sltu_pos out) by lia. rewrite (sltiu1_nz (bv_unsigned out + bv_unsigned at0)) by lia.
    if_false.
    step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply MCH with (buf := ln ++ Z_to_bv 8 0 :: rest);
        [ rewrite unsigned_lit by lia; exact OBA
        | apply memchr_line_ok; [reflexivity | rewrite unsigned_lit by lia; lia | exact NZ]
        | exact MI ]
      | post_call rsegs mm ]
    end.
    rewrite (memchr_line_res _ _ _ ln rest) by first [reflexivity | exact NZ | (rewrite unsigned_lit by lia; lia)].
    rewrite (unsigned_lit (bv_unsigned out + bv_unsigned at0)) by lia.
    clear GN1 GO1 RN1 RO1 OB1 OBA.
    cbn [disjoint_from] in DA, DL, DN.
    step. if_cases HZ; zify_cond HZ; [exfalso; Z.div_mod_to_equations; lia |].
    clear POST.
    step. step. if_cases HT; [exfalso; zify_cond HT; rewrite ?land7 in HT; Z.div_mod_to_equations; lia |]. clear HT.
    step. step. step. if_cases HT; [exfalso; zify_cond HT; rewrite ?land7 in HT; Z.div_mod_to_equations; lia |]. clear HT.
    step. step. step. step. step. step. step.
    step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    finish.
    + eapply bytes_at_transport; [exact GN | exact MU | exact DGN].
    + eapply bytes_at_transport; [exact GO | exact MU | exact DGO].
    + eapply bytes_at_transport; [exact OB | exact MU | exact DOB].
    + right. exists ln. split; [lia|]. split; [exists rest; split; [exact SK | exact NZ]|].
      split; [reflexivity|].
      split; [eapply rw_cells_C8_eq; [exact CA1 | rewrite !unsigned_lit by lia; f_equal; lia]|].
      split; [exact CL1|].
      eapply rw_cells_C8_eq; [exact CN1 | rewrite !unsigned_lit by lia; f_equal; lia].
  - zify_cond HB.
    step. step. step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    finish.
    left. split; [lia|]. split; [reflexivity|]. split; [exact CA1|]. split; [exact CL1 | exact CN1].
Qed.
