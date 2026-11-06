From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import next_line_c strlen_c bcmp_c check_shape_done_c check_shape_event_c.
Import ListNotations.
Open Scope Z_scope.

Definition keep (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (keep T) in H.

Lemma ro_of_byte : forall m A (b : byte), bytes_at rsegs m A [b] -> ro_cells rsegs m A [C1 b].
Proof. intros m A b H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. exact H. Qed.

Lemma rw_cells_cut : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma rw_cells_at : forall m A B cs, rw_cells rsegs m A cs -> A = B -> rw_cells rsegs m B cs.
Proof. intros; subst; assumption. Qed.

Lemma line_unique : forall e ln rest : list byte, ~ In (Z_to_bv 8 0) e -> ~ In (Z_to_bv 8 0) ln ->
  e ++ [Z_to_bv 8 0] = ln ++ Z_to_bv 8 0 :: rest -> ln = e.
Proof.
  induction e as [|b e IH]; intros ln rest He Hl H; destruct ln as [|c ln]; cbn in H.
  - reflexivity.
  - injection H as H1 _. subst c. exfalso. apply Hl. left. reflexivity.
  - injection H as H1 _. subst b. exfalso. apply He. left. reflexivity.
  - injection H as H1 H2. subst c. f_equal.
    apply (IH ln rest); [intro X; apply He; right; exact X | intro X; apply Hl; right; exact X | exact H2].
Qed.

Lemma memcmp_refl : forall l : list byte, memcmp_model l l (length l) = Some 0.
Proof. induction l as [|a l IH]; [reflexivity|]. cbn. rewrite Z.eqb_refl. exact IH. Qed.

Ltac dj := cbn [disjoint_from]; rewrite ?unsigned_lit by lia; lia.
Ltac djh D := let D' := fresh in pose proof D as D'; cbn [disjoint_from] in D' |- *; rewrite ?unsigned_lit by lia; lia.

Theorem check_shape_event_holds : next_line_contract -> strlen_contract -> bcmp_contract -> check_shape_done_contract ->
  check_shape_event_contract.
Proof.
  intros NL SLEN BC CSD.
  unfold check_shape_done_contract, CHECK_SHAPE_DONE, check_shape_done_c.G_NOUT in CSD.
  unfold check_shape_event_contract, CHECK_SHAPE_EVENT, CHECK_SHAPE_EVENT_K, G_GONE, next_line_c.G_NOUT, G_OUT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo gone
    nout out e slack ob.
  cbv zeta.
  intros ST LO SA MI EVB NZ PAD DEV GG HG DGG GN DGN GO DGO OB OL DOB OPOS HPROP.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. pose proof (zr_word nout) as Rno.
  pose proof (zr_word out) as Rou. unfold inr64 in *.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (bytes_at_bound _ _ _ _ EVB) as BEV. pose proof (bytes_at_bound _ _ _ _ OB) as BOB.
  rewrite length_app in BEV, DEV. cbn [length] in BEV, DEV.
  rewrite <- OL in DOB.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof DEV as DEV1. cbn [disjoint_from] in DEV1. destruct DEV1 as [DEV1 _].
  pose proof DGG as DGG1. cbn [disjoint_from] in DGG1. destruct DGG1 as [DGG1 _].
  pose proof (ro_of_byte _ _ _ GG) as RG. clear GG.
  hide GN. hide GO. hide OB. hide HPROP. hide OPOS.
  carve_frame 48%nat ST.
  destruct HG as [-> | ->].
  - step. step. step. step. step. step. step. step. step. if_true.
    step. step. step. step.
    destruct (rw_cells_cut _ _ [_] [_; _; _; _] FR) as [FRa FRb]. clear FR.
    destruct (rw_cells_cut _ _ [_] [_; _; _] FRb) as [FAT FRS]. clear FRb.
    apply (rw_cells_split_CB rsegs _ _ [] 16 _ [] [8%nat; 8%nat]) in FRa; [| reflexivity].
    cbn [mk_CB_cells app] in FRa.
    destruct (rw_cells_cut _ _ [_] [_] FRa) as [FLN FLE]. clear FRa.
    apply (rw_cells_at _ _ (bv_unsigned sp + -32)) in FAT; [| cbn [cells_size csize]; lia].
    apply (rw_cells_at _ _ (bv_unsigned sp + -24)) in FRS; [| cbn [cells_size csize]; lia].
    apply (rw_cells_at _ _ (bv_unsigned sp + -40)) in FLE; [| cbn [cells_size csize]; lia].
    unfold keep in GN, GO, OB, OPOS, HPROP. destruct HPROP as [[HC _] | [_ HOB]]; [lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bytes_at_transport rsegs _ m mm _ _ GN MU DGN) as GN1;
      pose proof (bytes_at_transport rsegs _ m mm _ _ GO MU DGO) as GO1;
      pose proof (bytes_at_transport rsegs _ m mm _ _ OB MU DOB) as OB1
    end.
    assert (OE : bv_unsigned nout = Z.of_nat (length e) + 1) by (rewrite <- OL, HOB, length_app; cbn [length]; lia).
    assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    clear RG.
    unfold next_line_contract, NEXT_LINE, NEXT_LINE_FRAME, next_line_c.G_NOUT, G_OUT in NL. cbv zeta in NL.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply NL;
        [ rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | exact MI
        | exact FAT | exact FLN | exact FLE
        | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia
        | dj | dj | dj
        | exact GN1 | djh DGN | exact GO1 | djh DGO | exact OB1 | exact OL | djh DOB
        | rewrite unsigned_lit by lia; lia
        | intros _; split; [apply OPOS; lia | rewrite HOB; apply in_or_app; right; left; reflexivity] ]
      | post_call rsegs mm ]
    end.
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in POST.
    destruct POST as [(HC & _) | (ln & _ & (rest & SK & NZL) & HX2 & CAT & CLN & CLE)]; [lia|].
    cbn [Z.to_nat skipn] in SK. rewrite HOB in SK.
    pose proof (line_unique _ _ _ NZ NZL SK) as ->. subst x2.
    rewrite USP in PC. rename PC into ST.
    rewrite Z.add_0_r in CLN. rewrite Z.add_0_l in CAT.
    clear GN GO OB OPOS.
    step. if_false. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply SLEN with (str := e) (slack := slack); [exact EVB | exact NZ | exact PAD | assumption]
      | post_call rsegs mm ]
    end.
    step. if_false. step. step. step. step.
    pose proof EVB as EB. apply bytes_at_app in EB. destruct EB as [EB _].
    pose proof PC2 as OBE. rewrite HOB in OBE. apply bytes_at_app in OBE. destruct OBE as [OBE _].
    clear POST.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC with (ls := e) (rs := e) (v := 0);
        [ exact OBE | exact EB | rewrite unsigned_lit by lia; rewrite Nat2Z.id; apply memcmp_refl | assumption ]
      | post_call rsegs mm ]
    end.
    clear OBE EB.
    step. if_false. step.
    pose proof (rw_cells_join _ _ _ _ _ CLN CLE ltac:(cbn [cells_size csize]; lia)) as J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 CAT ltac:(cbn [cells_size csize app]; lia)) as J2.
    pose proof (rw_cells_join _ _ _ _ _ J2 FRS ltac:(cbn [cells_size csize app]; lia)) as FR.
    cbn [app] in FR. clear J1 J2 CLN CLE CAT FRS.
    step.
    assert (NE : nout = Z_to_bv 64 (Z.of_nat (length e) + 1)) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
    rewrite NE in PC0.
    eapply evt_cut; [eapply CSD; exact PC0 |].
    intros ms' [a1' ->].
    match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
    step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    finish.
  - step. step. step. step. step. step. step. step. step. if_false.
    unfold keep in HPROP. destruct HPROP as [[_ HO] | [HC _]]; [|lia].
    assert (NZ0 : nout = Z_to_bv 64 0) by (apply bv_eq; rewrite HO; reflexivity).
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    unfold keep in GN, OB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bytes_at_transport rsegs _ m mm _ _ GN MU DGN) as GN1;
      pose proof (bytes_at_transport rsegs _ m mm _ _ OB MU DOB) as OB1
    end.
    rewrite NZ0 in GN1.
    eapply evt_cut; [eapply CSD; exact GN1 |].
    intros ms' [a1' ->].
    finish.
Qed.
