From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H04.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma step04 : forall t, 0 <= t <= 15 ->
  Hcut B APIf ra (Inv_U13b08 B APIf ra empty) ->
  Hcut B APIf ra (fun g c => Inv_U13ae8_at B APIf ra empty g (t + 1) c) ->
  Hcut B APIf ra (fun g c => Inv_U13ae8_at B APIf ra empty g t c).
Proof.
  intros t Ht H08 HX g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact HX | exact H08 | | | exact HC | ].
  { intros c' HC'. cbv beta. unfold Inv_U13ae8_at. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_U13b08. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN1 & E8 & HT & E15 & E11 & E12 & E13 & E14 & E10 & HB).
  pose proof HN1 as (HNB & E27 & HSTP & HQ216 & HW4).
  pose proof HNB as (HID & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOU).
  pose proof HSTP as (HQ24 & HSC).
  pose proof (stem_addr_cases g) as HSA.
  pose proof (Tac_si.nzb_stem (g_in g)) as NZS.
  pose proof (n_stem_len (g_in g)) as L16.
  unfold zlen in HT, HSA.
  pose proof E14 as E14'. unfold spk, fsp, SLOT_FRAME in E14'.
  pose proof E10 as E10'. unfold spk, fsp, SLOT_FRAME in E10'.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HB) as HBn. unfold spk, fsp, SLOT_FRAME in HBn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HSC) as HSCn. unfold cstr in HSCn.
  set (bs := firstn (Z.to_nat t) (n_stem (g_in g))) in HBn.
  assert (Lbs : Z.of_nat (length bs) = t) by (unfold bs; rewrite length_firstn; lia).
  set (a := g_S g - 384 + 242 + t).
  assert (Ea : a = g_S g - 384 + 242 + Z.of_nat (length bs)) by (unfold a; lia).
  set (b0 := RcIdentModel.nthb (n_stem (g_in g)) (Z.to_nat t)).
  unfold rmk, Frame.mkR. rewrite E2, E15, E13, E10', E12, E14', E11.
  step. rewrite bv_eqb_small by (unfold spk, fsp, SLOT_FRAME in HSA; lia).
  replace (stem_addr g + t =? -1) with false by (symmetry; apply Z.eqb_neq; unfold spk, fsp, SLOT_FRAME in HSA; lia).
  br_if.
  step. rewrite bv_eqb_small by lia.
  replace (g_S g - 384 + 242 =? - t) with false by (symmetry; apply Z.eqb_neq; lia).
  br_if.
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
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 384 + 242) bs b0 HBn ltac:(lia)) as HB1.
  rewrite <- Ea in HB1.
  pose proof (Mem.bytes_at_write_other rsegs (normalize rsegs mem) a [b0] (stem_addr g) _ HSCn
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)
    ltac:(rewrite length_app; cbn [length]; unfold spk, fsp, SLOT_FRAME, a in *; lia)) as HSC1.
  change (Z_to_bv 64 a) with (wa a).
  fold b0. remember (write_to_mem (normalize rsegs mem) (wa a) [b0]) as m1 eqn:Em1.
  pose proof (cstr_byte m1 (stem_addr g) (n_stem (g_in g)) (Z.to_nat (t + 1)) HSC1 ltac:(lia)) as RD.
  rewrite Z2Nat.id in RD by lia.
  assert (KMm : forall m', mem_rel rsegs m' m1 -> KM [(a, a + 1)] mem m').
  { intros m' HREL. exact (KM_of _ mem m1 m' HRO MU1 HREL). }
  assert (HOk : forall m', mem_rel rsegs m' m1 -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m1 m' HFR HPM MUS HREL HOU). }
  assert (D1 : disjoint_from [(a, a + 1)] (spk g 146) 38) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D2 : disjoint_from [(a, a + 1)] (spk g 56) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D3 : disjoint_from [(a, a + 1)] (spk g 48) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D4 : disjoint_from [(a, a + 1)] (spk g 24) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D5 : disjoint_from [(a, a + 1)] (stem_addr g) (zlen (n_stem (g_in g)) + 1))
    by (cbn; unfold zlen, spk, fsp, SLOT_FRAME, a in *; lia).
  assert (D6 : disjoint_from [(a, a + 1)] (spk g 216) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D7 : disjoint_from [(a, a + 1)] (spk g 192) 5) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  destruct (Z.eq_dec (t + 1) (Z.of_nat (length (n_stem (g_in g))))) as [TE|TN].
  - replace (Z.to_nat (t + 1)) with (length (n_stem (g_in g))) in RD by lia.
    rewrite Tac_si.nthb_snoc_eq in RD.
    step. change (zxb z8) with (Z_to_bv 64 0).
    step. step. step. br_if.
    apply (fin_r g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split]]].
    + apply (N1_keep g nm tk dp regs mem R' m' _ HN1 (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4 D5 D6 D7); kr HG.
    + kr HG.
    + rewrite HG. greg2. unfold zlen. f_equal; lia.
    + kr HG.
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
    br_if.
    apply (fin_l g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    + apply (N1_keep g nm tk dp regs mem R' m' _ HN1 (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4 D5 D6 D7); kr HG.
    + kr HG.
    + unfold zlen. lia.
    + rewrite HG. greg2. f_equal; lia.
    + rewrite HG. greg2. reflexivity.
    + rewrite HG. greg2. f_equal; lia.
    + kr HG.
    + rewrite HG. greg2. f_equal; unfold spk, fsp, SLOT_FRAME; lia.
    + kr HG.
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME.
      replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
      rewrite (firstn_snoc (n_stem (g_in g)) (Z.to_nat t) (RcIdentModel.zb 0)) by lia.
      exact HB1.
Qed.

Lemma seg_H04 : Hcut B APIf ra (Inv_U13b08 B APIf ra empty) -> Hcut B APIf ra (Inv_U13ae8 B APIf ra empty).
Proof.
  intros H08.
  assert (IND : forall n : nat, Hcut B APIf ra (fun g c => Inv_U13ae8_at B APIf ra empty g (16 - Z.of_nat n) c)).
  { induction n as [|n IH].
    - intros g c (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & HT & _).
      pose proof (n_stem_len (g_in g)). unfold zlen in HT. lia.
    - intros g c HC. destruct (Z_le_dec 0 (16 - Z.of_nat (S n))) as [Hp|Hn].
      + apply (step04 (16 - Z.of_nat (S n))); [| exact H08 | | exact HC].
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
