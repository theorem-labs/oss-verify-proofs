From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import bcmp_c list_find_c.
Import ListNotations.
Open Scope Z_scope.

Definition keep (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (keep T) in H.

Lemma lf_memcmp : forall n (L R : list byte) v, length L = n -> length R = n -> memcmp_model L R n = Some v ->
  -255 <= v <= 255 /\ (v = 0 <-> L = R).
Proof.
  induction n as [|n IH]; intros L R v HL HR HM.
  - destruct L, R; cbn in *; try lia. injection HM as <-. split; [lia|]. tauto.
  - destruct L as [|a L], R as [|b R]; cbn in HL, HR; try lia.
    cbn in HM. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH L R v ltac:(lia) ltac:(lia) HM) as [RV IV]. split; [exact RV|].
      rewrite IV. split; intro H.
      * f_equal; [apply bv_eq; exact E | exact H].
      * injection H as _ H. exact H.
    + injection HM as <-. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
      unfold bv_modulus in Ra, Rb. change (Z.of_N 8) with 8 in Ra, Rb.
      split; [lia|]. split; intro H; [lia|]. injection H as H _. subst. contradiction.
Qed.

Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma swrap_inc : forall i, 0 <= i -> i + 1 < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 i) + 1)) = Z_to_bv 64 (i + 1).
Proof.
  intros i H0 H1. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^31) with 2147483648 in H1. Z.div_mod_to_equations. lia.
Qed.

Lemma rd8 : forall m a (v : word) e, bytes_at rsegs m a (le8 v) -> e = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 e) 8 = Some (le8 v).
Proof.
  intros m a v e H ->. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Definition lf_found (recs : list (word * list byte)) (src : list byte) (i : Z) (res : word) : Prop :=
  (exists j r, i <= Z.of_nat j /\ nth_error recs j = Some r /\ snd r = src /\
     (forall k r', i <= Z.of_nat k -> (k < j)%nat -> nth_error recs k = Some r' -> snd r' <> src) /\
     res = Z_to_bv 64 (Z.of_nat j)) \/
  ((forall k r', i <= Z.of_nat k -> nth_error recs k = Some r' -> snd r' <> src) /\ res = Z_to_bv 64 (-1)).

Lemma lf_found_here : forall recs src i r, 0 <= i -> nth_error recs (Z.to_nat i) = Some r -> snd r = src ->
  lf_found recs src i (Z_to_bv 64 i).
Proof.
  intros recs src i r Hi Hn He. left. exists (Z.to_nat i), r. split; [lia|]. split; [exact Hn|]. split; [exact He|].
  split; [intros k r' Hk Hkj; lia | f_equal; lia].
Qed.

Lemma lf_found_next : forall recs src i r res, 0 <= i -> nth_error recs (Z.to_nat i) = Some r -> snd r <> src ->
  lf_found recs src (i + 1) res -> lf_found recs src i res.
Proof.
  intros recs src i r res Hi Hn He [(j & r1 & H1 & H2 & H3 & H4 & H5) | (H1 & H2)].
  - left. exists j, r1. split; [lia|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
    intros k r' Hk Hkj Hr'. destruct (Z.eq_dec (Z.of_nat k) i) as [E|E].
    + assert (k = Z.to_nat i) by lia. subst k. rewrite Hn in Hr'. injection Hr' as <-. exact He.
    + apply (H4 k r'); [lia | exact Hkj | exact Hr'].
  - right. split; [|exact H2]. intros k r' Hk Hr'. destruct (Z.eq_dec (Z.of_nat k) i) as [E|E].
    + assert (k = Z.to_nat i) by lia. subst k. rewrite Hn in Hr'. injection Hr' as <-. exact He.
    + apply (H1 k r'); [lia | exact Hr'].
Qed.

Lemma lf_found_end : forall recs src i r, 0 <= i -> Z.of_nat (length recs) = i + 1 ->
  nth_error recs (Z.to_nat i) = Some r -> snd r <> src -> lf_found recs src i (Z_to_bv 64 (-1)).
Proof.
  intros recs src i r Hi HL Hn He. right. split; [|reflexivity].
  intros k r' Hk Hr'. assert (Hlt : (k < length recs)%nat) by (apply nth_error_Some; rewrite Hr'; discriminate).
  assert (k = Z.to_nat i) by lia. subst k. rewrite Hn in Hr'. injection Hr' as <-. exact He.
Qed.

Lemma list_rec_transport : forall m m' V recs, munch [] m m' ->
  (forall j r, nth_error recs j = Some r -> list_rec m V j r) ->
  (forall j r, nth_error recs j = Some r -> list_rec m' V j r).
Proof.
  intros m m' V recs MU HR j r Hj. destruct (HR j r Hj) as [X Y].
  split; eapply bytes_at_transport; eauto; exact I.
Qed.

Lemma lf_loop : bcmp_contract -> forall (c : nat) (k i A V : Z)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp gp tp s6 s7 s8 s9 s10 s11 nv sv : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (recs : list (word * list byte)) (src : list byte),
  k = Z.of_nat (S c) -> 0 <= i -> i + k = Z.of_nat (length recs) -> i + k < 2^31 -> A = V + 16 * i + 8 ->
  (forall j r, nth_error recs j = Some r -> list_rec m V j r) ->
  bytes_at rsegs m (bv_unsigned sv) src -> bv_unsigned nv = Z.of_nat (length src) -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' t3' t4' t5' t6' : word)
                       (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5'
                     s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x14a68) fc None m' (seg_rom rsegs) /\
       munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ lf_found recs src i s0')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (-1)) nv a0 a1 a2 a3 a4 a5 a6 a7 sv (Z_to_bv 64 k) (Z_to_bv 64 i)
             (Z_to_bv 64 A) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14a34) fc None m (seg_rom rsegs)).
Proof.
  intros BC c. induction c as [|c IH];
    intros k i A V ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp gp tp s6 s7 s8 s9 s10 s11 nv sv F fc m recs src
      Hk Hi HN H31 HA HR HS Hn MI.
  all: destruct (nth_error recs (Z.to_nat i)) as [r|] eqn:Er; [| exfalso; apply nth_error_None in Er; lia].
  all: destruct (HR _ _ Er) as [RB RT].
  all: destruct r as [p e]; cbn [fst snd] in RB, RT.
  all: rewrite Z2Nat.id in RB by lia.
  all: apply bytes_at_app in RB; destruct RB as [RB1 RB2]; rewrite length_le8 in RB2.
  all: pose proof (rd8 m _ _ (A + -8) RB1 ltac:(lia)) as RDp.
  all: pose proof (rd8 m _ _ A RB2 ltac:(lia)) as RDl.
  all: pose proof (bytes_at_bound _ _ _ _ RT) as BT; rewrite length_app in BT; cbn [length] in BT.
  all: apply bytes_at_app in RT; destruct RT as [RT _].
  all: pose proof (zr_word nv) as Rnv; unfold inr64 in Rnv.
  all: pose proof (munch_refl [] m) as MU0; pose proof (wmono_refl rsegs m) as WM0.
  all: hide HR.
  - change (Z.of_nat 1) with 1 in Hk. subst k.
    step. step. if_cases HL.
    + zify_cond HL.
      step. step. step. step. if_false. step.
      apply evt_done. do 22 eexists. exists m. split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|].
      split; [exact MI|]. eapply lf_found_end; [lia | lia | exact Er |]. cbn [snd]. intros ->.
      apply HL. rewrite Hn. first [reflexivity | apply Z.mod_small; lia].
    + zify_cond HL. try rewrite Z.mod_small in HL by lia.
      destruct (memcmp_model_total e src (length src) ltac:(lia) ltac:(lia)) as [v HMv].
      destruct (lf_memcmp (length src) e src v ltac:(lia) eq_refl HMv) as [RV IV].
      step. step. step. step.
      eapply evt_cut.
      { eapply BC with (ls := e) (rs := src) (v := v); [exact RT | exact HS | | exact MI].
        rewrite Hn, Nat2Z.id. exact HMv. }
      post_call rsegs m.
      step. if_cases HV; zify_cond HV.
      * assert (V0 : v = 0) by (Z.div_mod_to_equations; lia). step.
        apply evt_done. do 22 eexists. eexists. split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|].
        split; [assumption|]. apply (lf_found_here _ _ _ (p, e)); [lia | exact Er | apply IV; exact V0].
      * assert (V0 : v <> 0) by (intros ->; apply HV; reflexivity).
        step. step. step. step. if_false. step.
        apply evt_done. do 22 eexists. eexists. split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|].
        split; [assumption|]. eapply lf_found_end; [lia | lia | exact Er |]. cbn [snd]. intros E.
        apply V0. apply IV. exact E.
  - step. step. if_cases HL.
    + zify_cond HL.
      step. step. step. step. if_cases HC; zify_cond HC; [| exfalso; Z.div_mod_to_equations; lia].
      rewrite (swrap_inc i) by lia.
      unfold keep in HR.
      eapply evt_cut.
      { eapply IH with (k := k + -1) (i := i + 1) (A := A + 16) (V := V) (recs := recs) (src := src);
          [lia | lia | lia | lia | lia | exact HR | exact HS | exact Hn | exact MI]. }
      intros ms' PO.
      destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' &
        s4' & s5' & t3' & t4' & t5' & t6' & m'' & -> & MU2 & WM2 & MI2 & LF).
      apply evt_done. do 22 eexists. eexists. split; [reflexivity|]. split; [exact MU2|]. split; [exact WM2|].
      split; [exact MI2|]. eapply lf_found_next; [lia | exact Er | | exact LF]. cbn [snd]. intros ->.
      apply HL. rewrite Hn. first [reflexivity | apply Z.mod_small; lia].
    + zify_cond HL. try rewrite Z.mod_small in HL by lia.
      destruct (memcmp_model_total e src (length src) ltac:(lia) ltac:(lia)) as [v HMv].
      destruct (lf_memcmp (length src) e src v ltac:(lia) eq_refl HMv) as [RV IV].
      step. step. step. step.
      eapply evt_cut.
      { eapply BC with (ls := e) (rs := src) (v := v); [exact RT | exact HS | | exact MI].
        rewrite Hn, Nat2Z.id. exact HMv. }
      post_call rsegs m.
      step. if_cases HV; zify_cond HV.
      * assert (V0 : v = 0) by (Z.div_mod_to_equations; lia). step.
        apply evt_done. do 22 eexists. eexists. split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|].
        split; [assumption|]. apply (lf_found_here _ _ _ (p, e)); [lia | exact Er | apply IV; exact V0].
      * assert (V0 : v <> 0) by (intros ->; apply HV; reflexivity).
        step. step. step. step. if_cases HC; zify_cond HC; [| exfalso; Z.div_mod_to_equations; lia].
        rewrite (swrap_inc i) by lia.
        unfold keep in HR. pose proof (list_rec_transport _ _ _ _ MU0 HR) as HR'.
        eapply evt_cut.
        { eapply IH with (k := k + -1) (i := i + 1) (A := A + 16) (V := V) (recs := recs) (src := src);
            [lia | lia | lia | lia | lia | exact HR' | eassumption | exact Hn | eassumption]. }
        intros ms' PO.
        destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' &
          s4' & s5' & t3' & t4' & t5' & t6' & m'' & -> & MU2 & WM2 & MI2 & LF).
        apply evt_done. do 22 eexists. eexists. split; [reflexivity|].
        split; [exact (munch_trans _ _ _ _ MU0 MU2)|]. split; [exact (wmono_trans _ _ _ _ WM0 WM2)|].
        split; [exact MI2|]. eapply lf_found_next; [lia | exact Er | | exact LF]. cbn [snd]. intros E.
        apply V0. apply IV. exact E.
Qed.

Lemma ro_list : forall m L (v : word) N, bytes_at rsegs m L (le8 v) -> bytes_at rsegs m (L + 8) (le4 (Z_to_bv 64 N)) ->
  bytes_at rsegs m L (le8 v ++ le4 (Z_to_bv 64 N)).
Proof. intros m L v N H1 H2. apply bytes_at_app. split; [exact H1|]. rewrite length_le8. exact H2. Qed.

Theorem list_find_holds : bcmp_contract -> list_find_contract.
Proof.
  intros BC. unfold list_find_contract, LIST_FIND, LIST_FIND_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo N
    v recs src.
  cbv zeta.
  intros ST LO MI HV HNf AL HN HL HVP HR HS Hn DL DV DT DS.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1.
  pose proof (zr_word a2) as Ra2. pose proof (zr_word v) as Rv. unfold inr64 in *.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (ro_list _ _ _ _ HV HNf) as HLO. clear HV HNf.
  pose proof (bytes_at_bound _ _ _ _ HLO) as BLO. rewrite length_app, length_le8, length_le4 in BLO.
  pose proof (bytes_at_bound _ _ _ _ HS) as BS.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  hide HLO. hide HR. hide HS. hide DL. hide DV. hide DT. hide DS. hide HVP.
  carve_frame 64%nat ST.
  step. step. step. step. step. step. step. step.
  unfold keep in HLO, HR, HS, DL, DV, DT, DS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LO1 : ro_cells rsegs mm (bv_unsigned a0) [C8 v; C4 (Z_to_bv 64 N)]);
    [ split; [exact (conj I (conj I I))|]; cbn [cells_bytes cbytes]; rewrite app_nil_r;
      eapply bytes_at_transport;
      [ exact HLO | exact MU | cbn [disjoint_from]; split; [|exact I]; rewrite length_app, length_le8, length_le4; lia ]
    | ];
    assert (HR1 : forall j r, nth_error recs j = Some r -> list_rec mm (bv_unsigned v) j r);
    [ intros j r Hj; pose proof (proj1 (nth_error_Some recs j) ltac:(rewrite Hj; discriminate)) as Hjl;
      destruct (HR j r Hj) as [X Y]; pose proof (DT j r Hj) as D; split;
      [ eapply bytes_at_transport;
        [ exact X | exact MU | cbn [disjoint_from]; split; [|exact I]; rewrite length_app, !length_le8;
          destruct (DV ltac:(lia)); lia ]
      | eapply bytes_at_transport;
        [exact Y | exact MU | cbn [disjoint_from]; split; [|exact I]; rewrite length_app; cbn [length]; lia ] ]
    | ];
    assert (HS1 : bytes_at rsegs mm (bv_unsigned a1) src);
    [ eapply bytes_at_transport; [exact HS | exact MU | cbn [disjoint_from]; split; [|exact I]; lia] | ]
  end.
  clear DL DV DT DS.
  step. rewrite (sx32_lit N) by lia.
  step. step. if_cases HB.
  - zify_cond HB.
    assert (recs = []) by (destruct recs; [reflexivity | cbn [length] in HL; lia]). subst recs.
    step. step. step. step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    finish.
    right. split; [intros k r' Hr'; destruct k; discriminate | reflexivity].
  - zify_cond HB.
    step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (lf_loop BC) with (c := Z.to_nat (N - 1)) (k := N) (i := 0) (A := bv_unsigned v + 8)
          (V := bv_unsigned v) (recs := recs) (src := src);
        [lia | lia | lia | lia | lia | exact HR1 | exact HS1 | exact Hn | exact MI]
      | post_call rsegs mm ]
    end.
    match goal with H : lf_found _ _ _ _ |- _ => rename H into LF end.
    step. step. step. step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    finish.
    destruct LF as [(j & r & _ & Hj & He & Hmin & ->) | (Hall & ->)].
    + left. exists j, r. split; [exact Hj|]. split; [exact He|]. split; [|reflexivity].
      intros k r' Hk Hr'. apply (Hmin k r'); [lia | exact Hk | exact Hr'].
    + right. split; [|reflexivity]. intros k r' Hr'. apply (Hall k r'); [lia | exact Hr'].
Qed.
