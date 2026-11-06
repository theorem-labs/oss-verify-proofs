From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel
  reac_ctrl_build_grant_sweep_c GroupaNeeds_c.
Import ListNotations.
Open Scope Z_scope.

Lemma stk_transport_rd : forall W m m' lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hc a Ha) as [Ho | Hb']; [| exact Hb'].
  exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma rw_cells_rd : forall m A n bs x, rw_cells rsegs m A [CB n bs] -> A <= x < A + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A n bs x [[Hwf (_ & _ & Hb)] _] Hx. cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, Hb.
  destruct Hwf as [Hl _]. rewrite app_nil_r in Hb.
  specialize (Hb (Z.to_nat (x - A)) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
  replace (A + (x - A)) with x in Hb by lia. rewrite Hb.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Theorem sweep_link : reac_ctrl_build_grant_sweep_contract -> reac_ctrl_build_grant_sweep_need.
Proof.
  intros PC.
  unfold reac_ctrl_build_grant_sweep_contract, reac_ctrl_build_grant_sweep_c.REAC_CTRL_BUILD_GRANT_SWEEP,
    reac_ctrl_build_grant_sweep_c.REAC_CTRL_BUILD_GRANT_SWEEP_STACK, REAC_CTRL_BUILD_GRANT_SWEEP_FRAME in PC.
  unfold reac_ctrl_build_grant_sweep_need, GroupaNeeds_c.REAC_CTRL_BUILD_GRANT_SWEEP,
    GroupaNeeds_c.REAC_CTRL_BUILD_GRANT_SWEEP_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m s mx base w V lo vals junk -> -> -> -> -> SP16 Hs Hmx Hb Hw1 Hbw HV HV3 HVB HVL HVLG DV HR ST LO HMI
    HROW DROW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rsp, Hs, HV3.
  pose proof ST as (Hlo0 & _ & _).
  assert (Us : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (UV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  assert (SOK : sweep_ok (Z_to_bv 64 s) (Z_to_bv 64 V) mx base w = (8 + 3 * w <=? mx)).
  { unfold sweep_ok. rewrite Us, UV, (proj2 (Z.eqb_neq s 0)), (proj2 (Z.eqb_neq V 0)) by lia.
    rewrite (proj2 (Z.leb_le 1 w)), (proj2 (Z.leb_le (base + w) 48)) by lia. reflexivity. }
  destruct (stk_split rsegs m lo (bv_unsigned sp - 1888) (bv_unsigned sp) ST ltac:(lia)) as [STL STH].
  eapply evt_mono.
  { eapply PC with (M := mx) (base := base) (w := w) (lo := bv_unsigned sp - 1888) (junk := junk) (vl := vals).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold int32. lia.
    - unfold int32. lia.
    - exact Hb.
    - intros _ _ _. lia.
    - exact HMI.
    - exact STH.
    - lia.
    - exact SP16.
    - exact HROW.
    - unfold IM4_ROW in DROW. unfold CTRL_ROW. lia.
    - intros HOK. rewrite SOK in HOK. apply Z.leb_le in HOK.
      destruct (HR HOK) as (RW & D1 & D2 & D3).
      unfold sweep_pre. rewrite Us, UV.
      split; [exact RW|]. split; [exact HVB|]. split; [exact HVL|]. split; [exact HVLG|].
      split; [exact D1|]. split; [exact DV|]. split; [exact D2|]. exact D3. }
  intros ms' (x1 & x2 & x3 & r & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & m' &
              -> & WM & MI & STH' & HROW' & HIF).
  rewrite SOK, Us in HIF.
  unfold reac_ctrl_build_grant_sweep_c.REAC_CTRL_BUILD_GRANT_SWEEP_STACK, REAC_CTRL_BUILD_GRANT_SWEEP_FRAME in HIF.
  exists x1, x2, x3, r, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m'.
  split; [reflexivity|]. split; [exact WM|]. split; [exact MI|].
  destruct (8 + 3 * w <=? mx) eqn:HOK.
  - destruct HIF as (Hr & MU & RWc).
    split.
    { eapply stk_merge; [| exact STH' | lia].
      eapply stk_transport_rd; [exact STL | exact MU | exact WM |].
      intros x Hx. destruct (Z_lt_le_dec x s) as [L|L]; [left; cbn [outside]; repeat split; try exact I; lia|].
      destruct (Z_lt_le_dec x (s + 34 * (8 + 3 * w))) as [L2|L2];
        [right; eapply rw_cells_rd; [exact RWc | rewrite Z2Nat.id by lia; lia]|].
      left. cbn [outside]. repeat split; try exact I; lia. }
    split; [exact HROW'|].
    split; [exact Hr|]. split; [|exact RWc].
    eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _).
    repeat split; try exact I; lia.
  - destruct HIF as (Hr & MU).
    split.
    { eapply stk_merge; [| exact STH' | lia].
      eapply stk_transport_disjoint; [exact STL | exact MU | exact WM |].
      cbn [disjoint_from]. repeat split; try exact I; lia. }
    split; [exact HROW'|].
    split; [exact Hr|].
    eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x (H1 & _).
    repeat split; try exact I; lia.
Qed.
