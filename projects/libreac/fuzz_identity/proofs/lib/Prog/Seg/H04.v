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

Section H04.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma step04 : forall t, 0 <= t <= 15 ->
  Hcut B APIf ra (Inv_K1390c B APIf ra empty) ->
  Hcut B APIf ra (fun g c => Inv_K138f4_at B APIf ra empty g (t + 1) c) ->
  Hcut B APIf ra (fun g c => Inv_K138f4_at B APIf ra empty g t c).
Proof.
  intros t Ht H0c HX g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact HX | exact H0c | | | exact HC | ].
  { intros c' HC'. cbv beta. unfold Inv_K138f4_at. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_K1390c. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN1 & E19 & HT & E26 & E10 & E12 & E11 & HB).
  pose proof HN1 as (HN0 & E8 & HW4 & HQ200 & HQ168).
  pose proof HN0 as ((HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU) & E9 & E18 & HQ16 & HSC).
  pose proof (stem_addr_cases g) as HSA.
  pose proof (Tac_si.nzb_stem (g_in g)) as NZS.
  pose proof (n_stem_len (g_in g)) as L16.
  unfold zlen in HT, HSA.
  pose proof E10 as E10'. unfold spk, fsp, SLOT_FRAME in E10'.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HB) as HBn. unfold spk, fsp, SLOT_FRAME in HBn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HSC) as HSCn. unfold cstr in HSCn.
  set (bs := firstn (Z.to_nat t) (n_stem (g_in g))) in HBn.
  assert (Lbs : Z.of_nat (length bs) = t) by (unfold bs; rewrite length_firstn; lia).
  set (a := g_S g - 368 + 226 + t).
  assert (Ea : a = g_S g - 368 + 226 + Z.of_nat (length bs)) by (unfold a; lia).
  set (b0 := RcIdentModel.nthb (n_stem (g_in g)) (Z.to_nat t)).
  unfold rmk, Frame.mkR. rewrite E2, E10', E26, E12, E11.
  step.
  pose proof (st_ok g (normalize rsegs mem) a 1 HWR0 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO.
  step.
  change (RcIdentModel.bz b0) with (bv_unsigned b0).
  rewrite le1_byte.
  pose proof (Frame.munch_write [(a, a + 1)] (normalize rsegs mem) (normalize rsegs mem) a [b0] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) a [b0] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a; lia)) as MUS.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a) [b0] (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) a [b0] HSTK0
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)) as STK1.
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 368 + 226) bs b0 HBn ltac:(lia)) as HB1.
  rewrite <- Ea in HB1.
  pose proof (Mem.bytes_at_write_other rsegs (normalize rsegs mem) a [b0] (stem_addr g) _ HSCn
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)
    ltac:(rewrite length_app; cbn [length]; unfold spk, fsp, SLOT_FRAME, a in *; lia)) as HSC1.
  change (Z_to_bv 64 a) with (wa a).
  fold b0. remember (write_to_mem (normalize rsegs mem) (wa a) [b0]) as m1 eqn:Em1.
  pose proof (Tac_si.cstr_byte m1 (stem_addr g) (n_stem (g_in g)) (Z.to_nat (t + 1)) HSC1 ltac:(lia)) as RD.
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
  destruct (Z.eq_dec (t + 1) (Z.of_nat (length (n_stem (g_in g))))) as [TE|TN].
  - replace (Z.to_nat (t + 1)) with (length (n_stem (g_in g))) in RD by lia.
    rewrite Tac_si.nthb_snoc_eq in RD.
    step. change (zxb z8) with (Z_to_bv 64 0).
    step. step. step. br_if.
    apply (fin_r g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split]]].
    + apply (N1_keep g nm tk dp regs mem R' m' _ HN1 (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4 D5 D6 D7);
        rewrite HG; reflexivity.
    + rewrite HG. exact E19.
    + rewrite HG. greg2. unfold zlen. f_equal; lia.
    + rewrite HG. greg2. unfold zlen, spk, fsp, SLOT_FRAME. f_equal; lia.
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME.
      replace (n_stem (g_in g)) with (bs ++ [b0]); [exact HB1|].
      unfold bs, b0, RcIdentModel.nthb.
      rewrite <- firstn_snoc by lia. replace (S (Z.to_nat t)) with (length (n_stem (g_in g))) by lia.
      apply firstn_all.
  - assert (Lq : (Z.to_nat (t + 1) < length (n_stem (g_in g)))%nat) by lia.
    rewrite Tac_si.nthb_snoc_lt in RD by exact Lq.
    pose proof (Tac_si.nzb_nth _ _ NZS Lq) as NZ.
    pose proof (bz_range (RcIdentModel.nthb (n_stem (g_in g)) (Z.to_nat (t + 1)))) as BR.
    step. rewrite Tac_si.zxb_bz.
    step. step. step.
    rewrite bv_eqb_lit by lia.
    replace (RcIdentModel.bz (RcIdentModel.nthb (n_stem (g_in g)) (Z.to_nat (t + 1))) =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact NZ).
    cbn [negb].
    apply (fin_l g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + apply (N1_keep g nm tk dp regs mem R' m' _ HN1 (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4 D5 D6 D7);
        rewrite HG; reflexivity.
    + rewrite HG. exact E19.
    + unfold zlen. lia.
    + rewrite HG. greg2. f_equal; lia.
    + rewrite HG. greg2. unfold spk, fsp, SLOT_FRAME. f_equal; lia.
    + rewrite HG. greg2. reflexivity.
    + rewrite HG. greg2. reflexivity.
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME.
      replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
      rewrite (firstn_snoc (n_stem (g_in g)) (Z.to_nat t) (RcIdentModel.zb 0)) by lia.
      exact HB1.
Qed.

Lemma seg_H04 : Hcut B APIf ra (Inv_K1390c B APIf ra empty) -> Hcut B APIf ra (Inv_K138f4 B APIf ra empty).
Proof.
  intros H0c.
  assert (IND : forall n : nat, Hcut B APIf ra (fun g c => Inv_K138f4_at B APIf ra empty g (16 - Z.of_nat n) c)).
  { induction n as [|n IH].
    - intros g c (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & HT & _).
      pose proof (n_stem_len (g_in g)). unfold zlen in HT. lia.
    - intros g c HC. destruct (Z_le_dec 0 (16 - Z.of_nat (S n))) as [Hp|Hn].
      + apply (step04 (16 - Z.of_nat (S n))); [| exact H0c | | exact HC].
        * destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & HT & _).
          pose proof (n_stem_len (g_in g)). unfold zlen in HT. lia.
        * intros g' c' HC'. apply IH. replace (16 - Z.of_nat n) with (16 - Z.of_nat (S n) + 1) by lia. exact HC'.
      + destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & HT & _). lia. }
  intros g c (t & HC).
  assert (Ht : 0 <= t <= 15).
  { destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & HT & _).
    pose proof (n_stem_len (g_in g)). unfold zlen in HT. lia. }
  apply (IND (Z.to_nat (16 - t))). replace (16 - Z.of_nat (Z.to_nat (16 - t))) with t by lia. exact HC.
Qed.

End H04.
