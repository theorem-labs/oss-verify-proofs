From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel
  GroupaModel BuildSweepModel GroupaNeeds_c reac_grant_build_sweep_c check_groupa_c
  LLVMFuzzerTestOneInput_c SlotNeeds_c.
Import ListNotations.
Open Scope Z_scope.

Lemma tb_nonneg : forall T i, 0 <= tb T i.
Proof. intros. unfold tb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) T (Z_to_bv 8 0))). lia. Qed.

Lemma I1_set01 : forall T, I1 T -> tx_set01 T.
Proof.
  intros T (H1 & _). intros ch p Hch Hp. pose proof (tb_nonneg T (144 + 3 * ch + p)).
  destruct (H1 (3 * ch + p) ltac:(lia)) as [HS _]. replace (144 + (3 * ch + p)) with (144 + 3 * ch + p) in HS by lia.
  lia.
Qed.

Lemma I1_legal : forall T, I1 T -> tx_legal T.
Proof. intros T (_ & H2 & _). intros ch p Hch Hp H. exact (H2 ch p Hch Hp H). Qed.

Lemma sweep_vals_same : forall T t base w,
  SlotNeeds_c.sweep_vals T t base w = BuildSweepModel.sweep_vals T t base w.
Proof.
  intros. unfold SlotNeeds_c.sweep_vals, BuildSweepModel.sweep_vals. apply map_ext. intros j.
  rewrite Nat2Z.inj_div, Nat2Z.inj_mod. reflexivity.
Qed.

Lemma bs_res_ok : forall s al mx base w,
  bs_res s al mx base w = if bsw_ok s al mx base w then 8 + 3 * w else -1.
Proof.
  intros. unfold bs_res, bsw_ok.
  destruct (s =? 0), (al =? 0), (fits base w); cbn [orb negb andb]; try reflexivity.
  rewrite Z.ltb_antisym. destruct (8 + 3 * w <=? mx); reflexivity.
Qed.

Lemma ctrl_row_same : CTRL_HEADAMP_ROW = IM4_ROW /\ CTRL_HEADAMP_BYTES = IM4_ROW_BYTES.
Proof. split; reflexivity. Qed.

Theorem check_groupa_link : check_groupa_contract -> check_groupa_need.
Proof.
  intros C.
  unfold check_groupa_contract, check_groupa_c.CHECK_GROUPA, CHECK_GROUPA_FRAME in C.
  unfold check_groupa_need, SlotNeeds_c.CHECK_GROUPA, CHECK_GROUPA_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m row ch p t lo T H0 H1 H2 H3 H4 HCH HP Ht HT4 HLT HT HI1 HR SP16 ST LO HMI DR DT.
  eapply evt_mono.
  { eapply C with (row := row) (ch := ch) (p := p) (t := t) (lo := lo) (T := T);
      try eassumption; lia. }
  intros ms' (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & m' &
              -> & MU & WM & MI & ST').
  exists x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m'.
  split; [reflexivity|]. split; [|split; [exact WM | split; [exact MI | exact ST']]].
  eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x (Hx & _).
  split; [lia | exact I].
Qed.

Theorem build_sweep_link : reac_grant_build_sweep_contract -> SlotNeeds_c.reac_grant_build_sweep_need.
Proof.
  intros C.
  unfold reac_grant_build_sweep_contract, reac_grant_build_sweep_c.REAC_GRANT_BUILD_SWEEP,
    REAC_GRANT_BUILD_SWEEP_FRAME in C.
  unfold SlotNeeds_c.reac_grant_build_sweep_need, SlotNeeds_c.REAC_GRANT_BUILD_SWEEP, BUILD_SWEEP_STACK.
  destruct ctrl_row_same as [ER EB]. rewrite ER, EB.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m s mx al t lo base w T junk H0 H1 H2 H3 Hs Hal Hmx SP16 ST LO HMI Hw0 HAL Ht HT4 HLT HT HI1 DT HROW DROW HROWS.
  rewrite bs_res_ok in HROWS.
  eapply evt_mono.
  { eapply C with (s := s) (mx := mx) (al := al) (t := t) (base := base) (w := w) (lo := lo) (T := T) (junk := junk).
    all: try eassumption.
    - intros Hal0. destruct (HAL Hal0) as (Hb & Hw & HB & D). refine (conj Hb (conj Hw (conj HB _))). lia.
    - lia.
    - apply I1_set01; exact HI1.
    - apply I1_legal; exact HI1.
    - lia.
    - intros HOK. rewrite HOK in HROWS. destruct (HROWS eq_refl) as (RW & D1 & _ & _ & D4).
      split; [exact RW | split; [lia | exact D4]]. }
  intros ms' (x1 & x2 & x3 & r & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & m' &
              -> & WM & MI & ST' & HROW' & HIF).
  exists x1, x2, x3, r, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, m'.
  split; [reflexivity|].
  rewrite bs_res_ok. unfold bs_win. rewrite bs_res_ok.
  destruct (bsw_ok s al mx base w) eqn:HOK.
  - destruct HIF as (Hr & MU & RWc).
    apply bsw_ok_spec in HOK.
    rewrite (proj2 (Z.eqb_neq (8 + 3 * w) (-1))) by lia.
    split; [exact Hr|].
    split.
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x (Hx1 & Hx2 & _).
      repeat split; try exact I; lia. }
    split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact HROW'|].
    intros _. rewrite sweep_vals_same. exact RWc.
  - destruct HIF as (Hr & MU).
    rewrite Z.eqb_refl.
    split; [exact Hr|].
    split.
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x (Hx1 & _).
      repeat split; try exact I; lia. }
    split; [exact WM|]. split; [exact MI|]. split; [exact ST'|]. split; [exact HROW'|].
    intros E. exfalso. lia.
Qed.
