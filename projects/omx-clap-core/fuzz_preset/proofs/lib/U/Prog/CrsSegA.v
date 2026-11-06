From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes check_reject_clean_starved_c CrsHash.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require
  fuzz_alloc_live_c fuzz_alloc_count_c fuzz_alloc_fail_c check_reject_clean_c fuzz_alloc_ran_out_c fuzz_alloc_ran_out
  LedgerCells.
Import ListNotations.
Open Scope Z_scope.

(* The walk of check_reject_clean_starved in the #102 ubsan twin 27566683 (entry 0x13c3c, frame 112, saved ra s0-s5).
   CRS_S5 is what `auipc s5, 0x21` at 0x13d00 leaves in s5 (0x13d00 + 0x21000); `lbu a0, 0x550(s5)` reads
   g_own_ran_out at CRS_S5 + 0x550 (crs_s5_own). *)
Definition CRS_S5 : Z := 0x34d00.

Lemma crs_s5_own : CRS_S5 + 0x550 = LedgerCells.GL_OWN_RAN_OUT.
Proof. reflexivity. Qed.

Definition crs_cells (m : word -> option byte) (S : Z) (xra xs0 xs1 xs2 xs3 xs4 xs5 : word) : Prop :=
  bytes_at rsegs m (S - 8) (le8 xra) /\ bytes_at rsegs m (S - 16) (le8 xs0) /\ bytes_at rsegs m (S - 24) (le8 xs1) /\
  bytes_at rsegs m (S - 32) (le8 xs2) /\ bytes_at rsegs m (S - 40) (le8 xs3) /\ bytes_at rsegs m (S - 48) (le8 xs4) /\
  bytes_at rsegs m (S - 56) (le8 xs5).

Lemma crs_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v B.
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 B ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma crs_rd1 : forall m a v, bytes_at rsegs m a (le1 v) -> ov_read_bytes rsegs m (wa a) 1 = Some (le1 v).
Proof.
  intros m a v B.
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le1 v) 0 1 B ltac:(lia)) by (rewrite length_le1; lia).
  reflexivity.
Qed.

(* g_fail_at lies below the stack bound every walk here assumes (strtod_c.STRTOD_GLOBALS_TOP 0x56000, above the end
   0x55e20 of .bss) *)
Lemma crs_fail_lo : fuzz_alloc_fail_c.G_FAIL_AT + 8 <= 0x56000.
Proof. unfold fuzz_alloc_fail_c.G_FAIL_AT. lia. Qed.

Lemma crs_zero8 : bv_unsigned (Z_to_bv 64 0) < 2 ^ 8.
Proof. rewrite unsigned_lit by lia. lia. Qed.

Lemma crs_at : forall m a b bs, bytes_at rsegs m a bs -> a = b -> bytes_at rsegs m b bs.
Proof. intros; subst; assumption. Qed.

Lemma crs_cells_of : forall m A j xra xs0 xs1 xs2 xs3 xs4 xs5,
  rw_cells rsegs m A [CB 56 j; C8 xs5; C8 xs4; C8 xs3; C8 xs2; C8 xs1; C8 xs0; C8 xra] ->
  crs_cells m (A + 112) xra xs0 xs1 xs2 xs3 xs4 xs5.
Proof.
  intros m A j xra xs0 xs1 xs2 xs3 xs4 xs5 [[WF HB] _].
  cbn [cells_wf cell_wf] in WF. destruct WF as [LJ _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [_ HB]. rewrite LJ in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [H5 HB]. rewrite length_le8 in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [H4 HB]. rewrite length_le8 in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [H3 HB]. rewrite length_le8 in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [H2 HB]. rewrite length_le8 in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [H1 HB]. rewrite length_le8 in HB.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [H0 HR]. rewrite length_le8 in HR.
  unfold crs_cells.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); (eapply crs_at; [eassumption | lia]).
Qed.

Lemma crs_mem_inv : forall m m' A, mem_inv rsegs m -> munch [(A, A + 8)] m m' -> wr_at rsegs m A 8 -> mem_inv rsegs m'.
Proof.
  intros m m' A Hi Hm (HA & HB & HW) x b Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [L|L].
  - rewrite (Hm x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (Hi x b Hx).
  - destruct (Z_lt_le_dec (bv_unsigned x) (A + 8)) as [U|U].
    + destruct (m x) as [b'|] eqn:E; [exact (Hi x b' E)|].
      apply (wview_not_ro rsegs m x); [|exact E].
      specialize (HW (bv_unsigned x - A) ltac:(lia)).
      replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in HW by lia.
      unfold wa in HW. rewrite Z_to_bv_lit_self in HW. exact HW.
    + rewrite (Hm x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (Hi x b Hx).
Qed.

Lemma crs_s0_skip : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (live : word),
  fuzz_alloc_live_c.fuzz_alloc_live_contract ->
  0x56000 <= S - 112 -> S <= 2 ^ 63 -> stk rsegs m (S - 112) S ->
  bytes_at rsegs m fuzz_alloc_live_c.G_LIVE (le8 live) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13c70) (Z_to_bv 64 (S - 112)) gp tp t0' t1' t2' live a3 a0' a1' a2' a3' a4' a5' a6' a7'
                     a1 a0 (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x13cfc) fc None m' (seg_rom rsegs) /\
       munch [(S - 112, S)] m m' /\ wmono rsegs m m' /\ crs_cells m' S ra s0 s1 s2 s3 s4 s5)
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S live
    LIVE LO HI ST HL.
  unfold fuzz_alloc_live_c.G_LIVE in HL.
  pose proof (munch_refl [(S - 112, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 112%nat ST.
  do 13 step.
  eapply evt_cut; [eapply LIVE; exact HL|].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x13c70)) with (Z_to_bv 64 0x13c70) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 2 step.
  if_true.
  pose proof (crs_cells_of _ _ _ _ _ _ _ _ _ _ FR) as CC.
  replace (S + -112 + 112) with S in CC by lia.
  finish.
Qed.

Lemma crs_djb2_range : forall l h, 0 <= h < 2 ^ 64 -> 0 <= djb2 h l < 2 ^ 64.
Proof.
  induction l as [|c r IH]; intros h Hh; cbn [djb2]; [exact Hh|].
  apply IH. apply Z.mod_pos_bound. lia.
Qed.

Lemma crs_remu : forall x y, 0 <= x < 2 ^ 64 -> 0 < y < 2 ^ 64 ->
  Sem.mul_div Instr.M_REMU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x mod y).
Proof.
  intros x y Hx Hy. unfold Sem.mul_div.
  rewrite (unsigned_lit y) by lia.
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_modu_unsigned.
  rewrite (unsigned_lit x), (unsigned_lit y), (unsigned_lit (x mod y))
    by (pose proof (Z.mod_pos_bound x y ltac:(lia)); lia).
  reflexivity.
Qed.

Lemma crs_cells_transport : forall m m' S A xra xs0 xs1 xs2 xs3 xs4 xs5,
  crs_cells m S xra xs0 xs1 xs2 xs3 xs4 xs5 -> munch [(A, A + 8)] m m' -> A + 8 <= S - 56 ->
  crs_cells m' S xra xs0 xs1 xs2 xs3 xs4 xs5.
Proof.
  intros m m' S A xra xs0 xs1 xs2 xs3 xs4 xs5 (C0 & C1 & C2 & C3 & C4 & C5 & C6) MU HA.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
    (eapply bytes_at_transport; [eassumption | exact MU | cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I]]).
Qed.

Lemma crsu_snez : forall d, 0 < d < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 d) = Z_to_bv 64 1.
Proof.
  intros d Hd. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  destruct (Z.ltb_spec 0 d); [reflexivity | lia].
Qed.

Ltac crs_parse_tail FAIL FR MU WM M0 SS :=
  let GF := eval cbv in fuzz_alloc_fail_c.G_FAIL_AT in
  step;
  rewrite crs_remu by first [lia | apply crs_djb2_range; lia];
  step;
  eapply evt_cut; [eapply FAIL; eassumption|];
  let ms' := fresh "ms'" in let a1' := fresh "a1'" in let m2 := fresh "m2" in
  let E := fresh "E" in let HF := fresh "HF" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
  intros ms' (a1' & m2 & E & HF & MU2 & WM2); subst ms';
  replace (ret_pc (Z_to_bv 64 0x13cd0)) with (Z_to_bv 64 0x13cd0) by (symmetry; apply ret_pc_even; [lia | reflexivity]);
  do 4 step;
  let CC := fresh "CC" in
  pose proof (crs_cells_of _ _ _ _ _ _ _ _ _ _ FR) as CC;
  replace (SS + -112 + 112) with SS in CC by lia;
  apply (crs_cells_transport _ m2 _ GF) in CC; [| exact MU2 | lia];
  let MUF := fresh "MUF" in
  assert (MUF : munch [(SS + -112, SS); (GF, GF + 8)] M0 m2)
    by (eapply munch_trans; [exact MU|]; refine (munch_weaken _ _ _ _ _ MU2);
        intros x Hx; cbn [outside] in *; tauto);
  let WMF := fresh "WMF" in
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WMF;
  finish.

Lemma crs_s0_parse : forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S data took cnt : Z) (tb : list byte) (live : word),
  fuzz_alloc_live_c.fuzz_alloc_live_contract -> fuzz_alloc_fail_c.fuzz_alloc_fail_contract ->
  0x56000 <= S - 112 -> S <= 2 ^ 63 -> stk rsegs m (S - 112) S ->
  bytes_at rsegs m fuzz_alloc_live_c.G_LIVE (le8 live) ->
  bytes_at rsegs m fuzz_alloc_fail_c.G_COUNT (le8 (Z_to_bv 64 cnt)) -> 0 <= cnt < 2 ^ 64 ->
  wr_at rsegs m fuzz_alloc_fail_c.G_FAIL_AT 8 ->
  bytes_at rsegs m data tb -> data + Z.of_nat (length tb) <= S - 112 ->
  0 < took < 2 ^ 64 -> 0 < data ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13ce0) (Z_to_bv 64 (S - 112)) gp tp t0' t1' t2' live a3
                     (Z_to_bv 64 data) (Z_to_bv 64 (Z.of_nat (length tb))) (Z_to_bv 64 (S - 112)) a3' a4' a5' a6' a7'
                     (Z_to_bv 64 (Z.of_nat (length tb))) (Z_to_bv 64 data) (Z_to_bv 64 took)
                     s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15fb4) fc None m' (seg_rom rsegs) /\
       munch [(S - 112, S); (fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' /\
       wmono rsegs m m' /\ crs_cells m' S ra s0 s1 s2 s3 s4 s5 /\
       bytes_at rsegs m' fuzz_alloc_fail_c.G_FAIL_AT
         (le8 (fuzz_alloc_fail_c.fail_at_of (Z_to_bv 64 cnt) (Z_to_bv 64 (pick (zb tb) took)))))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 data) (Z_to_bv 64 (Z.of_nat (length tb)))
             (Z_to_bv 64 took) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13c3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S data took cnt tb live
    LIVE FAIL LO HI ST HL HC HCB HW HD HDB HT HD0.
  unfold fuzz_alloc_fail_c.fuzz_alloc_fail_contract in FAIL.
  unfold fuzz_alloc_live_c.G_LIVE, fuzz_alloc_fail_c.G_COUNT, fuzz_alloc_fail_c.G_FAIL_AT in *.
  assert (PK : pick (zb tb) took = djb2 5381 (zb tb) mod took)
    by (unfold pick; replace (took =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  rewrite PK. clear PK.
  pose proof (bytes_at_bound rsegs m data tb HD) as DB.
  pose proof (munch_refl [(S - 112, S); (fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m) as MU.
  unfold fuzz_alloc_fail_c.G_FAIL_AT in MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 112%nat ST.
  do 13 step.
  eapply evt_cut; [eapply LIVE; exact HL|].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x13c70)) with (Z_to_bv 64 0x13c70) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 2 step.
  unfold_cond. rewrite (unsigned_lit took) by lia. if_false.
  do 3 step.
  destruct tb as [|c r].
  - change (Z.of_nat (length (@nil byte))) with 0 in *.
    if_true.
    crs_parse_tail FAIL FR MU WM m S.
  - assert (LEN : Z.of_nat (length (c :: r)) = 1 + Z.of_nat (length r)) by (cbn [length]; lia).
    unfold_cond. rewrite (unsigned_lit (Z.of_nat (length (c :: r)))) by lia. if_false.
    do 4 step.
    rewrite (crsu_snez data) by lia.
    eapply evt_cut.
    { eapply crsu_l1 with (D := data) (E := data + Z.of_nat (length (c :: r))) (tl := c :: r) (p := data) (h := 5381);
        [exact HD | discriminate | lia | reflexivity | lia | lia]. }
    intros ms' (a5' & a6' & ->).
    crs_parse_tail FAIL FR MU WM m S.
Qed.

Lemma crs_s1 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S lo rc cnt : Z),
  fuzz_alloc_fail_c.fuzz_alloc_fail_contract -> check_reject_clean_c.check_reject_clean_contract ->
  0x56000 <= lo -> lo + 16 <= S - 112 -> S <= 2 ^ 63 -> stk rsegs m lo (S - 112) -> mem_inv rsegs m ->
  - 2 ^ 31 <= rc < 2 ^ 31 -> rc <> 0 ->
  bytes_at rsegs m (S - 112) (repeat (Z_to_bv 8 0) 56) ->
  bytes_at rsegs m fuzz_alloc_live_c.G_LIVE (le8 s0) ->
  bytes_at rsegs m fuzz_alloc_fail_c.G_COUNT (le8 (Z_to_bv 64 cnt)) -> 0 <= cnt < 2 ^ 64 ->
  wr_at rsegs m fuzz_alloc_fail_c.G_FAIL_AT 8 ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13cfc) (Z_to_bv 64 (S - 112)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 (Z_to_bv 64 rc) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x13cfc) fc None m' (seg_rom rsegs) /\
       munch [(S - 128, S - 112); (fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (S - 112) /\
       bytes_at rsegs m' fuzz_alloc_fail_c.G_FAIL_AT
         (le8 (fuzz_alloc_fail_c.fail_at_of (Z_to_bv 64 cnt) (Z_to_bv 64 (-1)))))
    (MS (mkR ra (Z_to_bv 64 (S - 112)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ce0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S lo rc cnt
    FAIL CRC LO LOS HI ST MI RC NZ HD HL HC HCB HW.
  unfold fuzz_alloc_fail_c.fuzz_alloc_fail_contract in FAIL.
  unfold check_reject_clean_c.check_reject_clean_contract in CRC.
  unfold fuzz_alloc_live_c.G_LIVE, fuzz_alloc_fail_c.G_COUNT in *.
  do 3 step.
  eapply evt_cut; [eapply FAIL; eassumption|].
  intros ms' (a1' & m1 & E & HF & MU1 & WM1). subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13cec)) with (Z_to_bv 64 0x13cec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof crs_fail_lo as GFL.
  apply (bytes_at_transport rsegs [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m1) in HD;
    [|exact MU1 | cbn [disjoint_from]; rewrite repeat_length; split; [lia | exact I]].
  apply (bytes_at_transport rsegs [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m1) in HL;
    [|exact MU1 | cbn [disjoint_from]; rewrite length_le8; split; [unfold fuzz_alloc_fail_c.G_FAIL_AT; lia | exact I]].
  pose proof (stk_transport_disjoint rsegs [(fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m1
                lo (S - 112) ST MU1 WM1 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as ST1.
  pose proof (crs_mem_inv m m1 _ MI MU1 HW) as MI1.
  do 4 step.
  eapply evt_cut.
  { eapply (CRC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rc lo);
      [reflexivity | exact RC | exact NZ | | exact HL | exact MI1 | | | |];
      unfold check_reject_clean_c.CHECK_REJECT_CLEAN_FRAME; rewrite ?unsigned_lit by lia.
    - eapply crs_at; [exact HD | lia].
    - exact ST1.
    - lia.
    - right; lia.
    - left; lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & ST2).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13cfc)) with (Z_to_bv 64 0x13cfc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold check_reject_clean_c.CHECK_REJECT_CLEAN_FRAME in MU2.
  rewrite unsigned_lit in MU2, ST2 by lia.
  apply (bytes_at_transport rsegs [(S - 112 - 16, S - 112)] m1 m2) in HF;
    [|exact MU2 | cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I]].
  assert (MUF : munch [(S - 128, S - 112); (fuzz_alloc_fail_c.G_FAIL_AT, fuzz_alloc_fail_c.G_FAIL_AT + 8)] m m2).
  { eapply munch_trans.
    - refine (munch_weaken _ _ _ _ _ MU1). intros x Hx. cbn [outside] in *. tauto.
    - refine (munch_weaken _ _ _ _ _ MU2). intros x Hx. cbn [outside] in *.
      destruct Hx as (H1 & _ & _). split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM1 WM2) as WMF.
  finish.
Qed.

Lemma crs_epi : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (xra xs0 xs1 xs2 xs3 xs4 xs5 : word),
  0x56000 <= S - 112 -> S <= 2 ^ 63 -> crs_cells m S xra xs0 xs1 xs2 xs3 xs4 xs5 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR xra (Z_to_bv 64 S) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                              xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc xra) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (S - 112)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13de0) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S
    xra xs0 xs1 xs2 xs3 xs4 xs5 LO HI (C0 & C1 & C2 & C3 & C4 & C5 & C6).
  apply crs_rd8 in C0, C1, C2, C3, C4, C5, C6.
  do 9 step.
  replace (S - 112 + 112) with S by lia.
  apply evt_done. reflexivity.
Qed.

Lemma crs_s2_ret : forall (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z) (xra xs0 xs1 xs2 xs3 xs4 xs5 : word),
  0x56000 <= S - 112 -> S <= 2 ^ 63 -> crs_cells m S xra xs0 xs1 xs2 xs3 xs4 xs5 ->
  evt rsegs
    (fun ms' => ms' = MS (mkR xra (Z_to_bv 64 S) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                              xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc xra) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (S - 112)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13cfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S
    xra xs0 xs1 xs2 xs3 xs4 xs5 LO HI CC.
  step. if_true.
  eapply crs_epi; eassumption.
Qed.

(* doc <> 0 at 0x13cfc: `auipc s5`, the two flag tests of out_of_memory() (both read 0), fuzz_alloc_count, and the
   call of the pretty full write pj_write(doc, 1). *)
Lemma crs_s2_write : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cnt : Z),
  fuzz_alloc_count_c.fuzz_alloc_count_contract ->
  bv_unsigned s1 <> 0 ->
  bytes_at rsegs m fuzz_alloc_count_c.G_COUNT (le8 (Z_to_bv 64 cnt)) ->
  bytes_at rsegs m LedgerCells.GL_OWN_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m fuzz_alloc_ran_out_c.G_RAN_OUT (le1 (Z_to_bv 64 0)) ->
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d28) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                              s2 s3 (Z_to_bv 64 cnt) (Z_to_bv 64 CRS_S5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x16838) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13cfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cnt
    CNT NZ HC HO HR.
  pose proof (crs_rd1 m _ _ HO) as RD. unfold LedgerCells.GL_OWN_RAN_OUT in RD.
  step. if_false.
  step. step.
  step. if_false.
  step.
  eapply evt_cut; [eapply fuzz_alloc_ran_out.fuzz_alloc_ran_out_holds; [exact crs_zero8 | exact HR]|].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x13d10)) with (Z_to_bv 64 0x13d10) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. if_false.
  step.
  eapply evt_cut; [eapply CNT; exact HC|].
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x13d18)) with (Z_to_bv 64 0x13d18) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 4 step.
  apply evt_done. reflexivity.
Qed.

Lemma crs_s3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13d2c) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x15ea8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d28) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.

Lemma crs_s6 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13e28) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x15ea8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13e24) fc None m (seg_rom rsegs)).
Proof. intros. step. apply evt_done. reflexivity. Qed.
