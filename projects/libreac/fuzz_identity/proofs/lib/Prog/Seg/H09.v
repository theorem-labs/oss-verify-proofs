From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh2.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H09.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma H9b_wok : forall g nm tk dp regs m, H9b g nm tk dp regs m -> n_wok (g_in g) = true.
Proof. intros g nm tk dp regs m (((((_ & H & _) & _) & _) & _) & _). exact H. Qed.

Lemma step09 : forall t, 0 <= t <= 20 ->
  Hcut B APIf ra (Inv_K139f4 B APIf ra empty) ->
  Hcut B APIf ra (fun g c => Inv_K139cc_at B APIf ra empty g (t + 1) c) ->
  Hcut B APIf ra (fun g c => Inv_K139cc_at B APIf ra empty g t c).
Proof.
  intros t Ht H0 HX g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact HX | exact H0 | | | exact HC | ].
  { intros c' HC'. cbv beta. unfold Inv_K139cc_at. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_K139f4. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (H9 & HT & E12 & E13 & E11 & E10 & HB).
  pose proof H9 as (H9a' & E19).
  pose proof H9a' as (HN1 & E26 & HROW & HNM).
  pose proof HN1 as (HN0 & E8 & HW4 & HQ200 & HQ168).
  pose proof HN0 as ((HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU) & E9 & E18 & HQ16 & HSC).
  pose proof (stem_addr_cases g) as HSA.
  pose proof (n_ln_le (g_in g) HW) as LN. unfold n_ln in LN, HT.
  pose proof (Tac_si.nzb_EXP_NM _ HW) as NZE.
  pose proof E12 as E12'. unfold spk, fsp, SLOT_FRAME in E12'.
  pose proof E13 as E13'. unfold spk, fsp, SLOT_FRAME in E13'.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HB) as HBn. unfold spk, fsp, SLOT_FRAME in HBn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HNM) as HNMn. unfold cstr, spk, fsp, SLOT_FRAME in HNMn.
  set (bs := firstn (Z.to_nat t) (n_EXP_NM (g_in g))) in HBn.
  assert (Lbs : Z.of_nat (length bs) = t) by (unfold bs; rewrite length_firstn; lia).
  set (a := g_S g - 368 + 48 + t).
  assert (Ea : a = g_S g - 368 + 48 + Z.of_nat (length bs)) by (unfold a; lia).
  set (w := RcIdentModel.nthb (n_EXP_NM (g_in g)) (Z.to_nat t)).
  unfold rmk, Frame.mkR. rewrite E2, E10, E11, E12', E13'.
  step. step.
  pose proof (st_ok g (normalize rsegs mem) a 1 HWR0 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO.
  step.
  change (RcIdentModel.bz w) with (bv_unsigned w).
  rewrite le1_byte.
  pose proof (Frame.munch_write [(a, a + 1)] (normalize rsegs mem) (normalize rsegs mem) a [w] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) a [w] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a; lia)) as MUS.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a) [w] (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) a [w] HSTK0
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)) as STK1.
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 368 + 48) bs w HBn ltac:(lia)) as HB1.
  rewrite <- Ea in HB1.
  pose proof (Mem.bytes_at_write_other rsegs (normalize rsegs mem) a [w] (g_S g - 368 + 226) _ HNMn
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(cbn; unfold a; lia)) as HNM1.
  change (Z_to_bv 64 a) with (wa a).
  fold w. remember (write_to_mem (normalize rsegs mem) (wa a) [w]) as m1 eqn:Em1.
  pose proof (Tac_si.cstr_byte m1 (g_S g - 368 + 226) (n_EXP_NM (g_in g)) (Z.to_nat (t + 1)) HNM1 ltac:(lia)) as RD.
  rewrite Z2Nat.id in RD by lia.
  assert (KMm : forall m', mem_rel rsegs m' m1 -> KM [(a, a + 1)] mem m').
  { intros m' HREL. exact (KM_of _ mem m1 m' HRO MU1 HREL). }
  assert (HOk : forall m', mem_rel rsegs m' m1 -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m1 m' HFR HPM MUS HREL HOU). }
  assert (D1 : disjoint_from [(a, a + 1)] (spk g 130) 38) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D2 : disjoint_from [(a, a + 1)] (spk g 40) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D3 : disjoint_from [(a, a + 1)] (spk g 16) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D4 : disjoint_from [(a, a + 1)] (stem_addr g) (zlen (n_stem (g_in g)) + 1))
    by (cbn; unfold zlen, spk, fsp, SLOT_FRAME, a in *; lia).
  assert (D5 : disjoint_from [(a, a + 1)] (spk g 176) 5) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D6 : disjoint_from [(a, a + 1)] (spk g 200) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D7 : disjoint_from [(a, a + 1)] (spk g 168) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D8 : disjoint_from [(a, a + 1)] (spk g 32) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D9 : disjoint_from [(a, a + 1)] (spk g 226) (n_ln (g_in g) + 1))
    by (cbn; unfold n_ln, spk, fsp, SLOT_FRAME, a; lia).
  destruct (Z.eq_dec (t + 1) (Z.of_nat (length (n_EXP_NM (g_in g))))) as [TE|TN].
  - replace (Z.to_nat (t + 1)) with (length (n_EXP_NM (g_in g))) in RD by lia.
    rewrite Tac_si.nthb_snoc_eq in RD.
    step. change (zxb z8) with (Z_to_bv 64 0).
    step. step. step. br_if. step.
    apply (fin_r g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split].
    + split; [|rewrite HG; exact E19].
      apply (H9a_keep g nm tk dp regs mem R' m' _ H9a' (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4 D5 D6 D7 D8 D9);
        rewrite HG; reflexivity.
    + rewrite HG. greg2. unfold n_ln. f_equal; lia.
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME.
      replace (n_EXP_NM (g_in g)) with (bs ++ [w]); [exact HB1|].
      unfold bs, w, RcIdentModel.nthb.
      rewrite <- firstn_snoc by lia. replace (S (Z.to_nat t)) with (length (n_EXP_NM (g_in g))) by lia.
      apply firstn_all.
  - assert (Lq : (Z.to_nat (t + 1) < length (n_EXP_NM (g_in g)))%nat) by lia.
    rewrite Tac_si.nthb_snoc_lt in RD by exact Lq.
    pose proof (Tac_si.nzb_nth _ _ NZE Lq) as NZ.
    pose proof (bz_range (RcIdentModel.nthb (n_EXP_NM (g_in g)) (Z.to_nat (t + 1)))) as BR.
    step. rewrite Tac_si.zxb_bz.
    step. step. step.
    rewrite bv_eqb_lit by lia.
    replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) (Z.to_nat (t + 1))) =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact NZ).
    cbn [negb].
    apply (fin_l g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + split; [|rewrite HG; exact E19].
      apply (H9a_keep g nm tk dp regs mem R' m' _ H9a' (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4 D5 D6 D7 D8 D9);
        rewrite HG; reflexivity.
    + unfold n_ln. lia.
    + rewrite HG. reflexivity.
    + rewrite HG. reflexivity.
    + rewrite HG. greg2. f_equal; lia.
    + rewrite HG. greg2. reflexivity.
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME.
      replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
      rewrite (firstn_snoc (n_EXP_NM (g_in g)) (Z.to_nat t) (RcIdentModel.zb 0)) by lia.
      exact HB1.
Qed.

Lemma seg_H09 : Hcut B APIf ra (Inv_K139f4 B APIf ra empty) -> Hcut B APIf ra (Inv_K139cc B APIf ra empty).
Proof.
  intros H0.
  assert (IND : forall n : nat, Hcut B APIf ra (fun g c => Inv_K139cc_at B APIf ra empty g (21 - Z.of_nat n) c)).
  { induction n as [|n IH].
    - intros g c (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & H9 & HT & _).
      pose proof (n_ln_le (g_in g) (H9b_wok _ _ _ _ _ _ H9)). lia.
    - intros g c HC. destruct (Z_le_dec 0 (21 - Z.of_nat (S n))) as [Hp|Hn].
      + apply (step09 (21 - Z.of_nat (S n))); [| exact H0 | | exact HC].
        * destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & H9 & HT & _). lia.
        * intros g' c' HC'. apply IH. replace (21 - Z.of_nat n) with (21 - Z.of_nat (S n) + 1) by lia. exact HC'.
      + destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & H9 & HT & _). lia. }
  intros g c (t & HC).
  assert (Ht : 0 <= t <= 20).
  { destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & H9 & HT & _).
    pose proof (n_ln_le (g_in g) (H9b_wok _ _ _ _ _ _ H9)). lia. }
  apply (IND (Z.to_nat (21 - t))). replace (21 - Z.of_nat (Z.to_nat (21 - t))) with t by lia. exact HC.
Qed.

End H09.
