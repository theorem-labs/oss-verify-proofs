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

Section H07.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma step07 : forall t, 0 <= t <= 3 ->
  Hcut B APIf ra (Inv_U13be8 B APIf ra empty) ->
  Hcut B APIf ra (fun g c => Inv_U13bc8_at B APIf ra empty g (t + 1) c) ->
  Hcut B APIf ra (fun g c => Inv_U13bc8_at B APIf ra empty g t c).
Proof.
  intros t Ht H0 HX g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact HX | exact H0 | | | exact HC | ].
  { intros c' HC'. cbv beta. unfold Inv_U13bc8_at. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_U13be8. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN1 & E8 & E10 & HE & _ & HB & E11 & E12 & E13 & E14 & E15 & E16).
  pose proof HN1 as (HNB & E27 & HSTP & HQ216 & HW4).
  pose proof HNB as (HID & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOU).
  pose proof (stem_addr_cases g) as HSA.
  pose proof (n_stem_len (g_in g)) as L16.
  destruct (nzb_W4 _ HW) as [NZW LW].
  pose proof E11 as E11'. unfold spk, fsp, SLOT_FRAME in E11'.
  pose proof E15 as E15'. unfold spk, fsp, SLOT_FRAME in E15'.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HB) as HBn. unfold spk, fsp, SLOT_FRAME in HBn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HW4) as HW4n. unfold cstr, spk, fsp, SLOT_FRAME in HW4n.
  set (bs := n_stem (g_in g) ++ [dash] ++ firstn (Z.to_nat t) (n_W4 (g_in g))) in HBn.
  assert (Lbs : Z.of_nat (length bs) = zlen (n_stem (g_in g)) + 1 + t).
  { unfold bs, zlen. rewrite !length_app, length_firstn, LW. cbn [length]. lia. }
  set (a := g_S g - 384 + 242 + Z.of_nat (length bs)).
  set (w := RcIdentModel.nthb (n_W4 (g_in g)) (Z.to_nat t)).
  assert (E14a : getr regs 14 = Z_to_bv 64 a).
  { rewrite E14. unfold a, spk, fsp, SLOT_FRAME. f_equal. lia. }
  unfold rmk, Frame.mkR. rewrite E2, E11', E12, E13, E14a, E15', E16.
  step. eqb_off.
  step. eqb_off.
  step.
  pose proof (st_ok g (normalize rsegs mem) a 1 HWR0 ltac:(unfold a, zlen in *; lia)
    ltac:(unfold a, zlen in *; lia)) as HSO.
  step.
  change (RcIdentModel.bz w) with (bv_unsigned w).
  rewrite le1_byte.
  pose proof (Frame.munch_write [(a, a + 1)] (normalize rsegs mem) (normalize rsegs mem) a [w] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a, zlen in *; lia) ltac:(cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) a [w] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a, zlen in *; lia)
    ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a, zlen in *; lia)) as MUS.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a) [w] (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) a [w] HSTK0
    ltac:(unfold a; lia) ltac:(cbn; unfold a, zlen in *; lia)) as STK1.
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 384 + 242) bs w HBn ltac:(unfold zlen in *; lia)) as HB1.
  fold a in HB1.
  pose proof (Mem.bytes_at_write_other rsegs (normalize rsegs mem) a [w] (g_S g - 384 + 192) _ HW4n
    ltac:(unfold a; lia) ltac:(cbn; unfold a, zlen in *; lia)
    ltac:(rewrite length_app, LW; cbn [length]; unfold a, zlen in *; lia)) as HW41.
  change (Z_to_bv 64 a) with (wa a).
  fold w. remember (write_to_mem (normalize rsegs mem) (wa a) [w]) as m1 eqn:Em1.
  pose proof (cstr_byte m1 (g_S g - 384 + 192) (n_W4 (g_in g)) (Z.to_nat (t + 1)) HW41 ltac:(lia)) as RD.
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
  assert (D7 : disjoint_from [(a, a + 1)] (spk g 192) 5) by (cbn; unfold zlen, spk, fsp, SLOT_FRAME, a in *; lia).
  destruct (Z.eq_dec t 3) as [T3|T3].
  - subst t. change (Z.to_nat (3 + 1)) with 4%nat in RD. rewrite <- LW in RD.
    rewrite Tac_si.nthb_snoc_eq in RD.
    step. change (zxb z8) with (Z_to_bv 64 0).
    step. step. step. br_if.
    apply (fin_r g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split; [|split]]]].
    + apply (N1_keep g nm tk dp regs mem R' m' _ HN1 (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4 D5 D6 D7); kr HG.
    + rg HG.
    + rg HG.
    + exact HE.
    + rg HG.
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME, n_EXP_NM. rewrite HE. cbv iota.
      replace (n_stem (g_in g) ++ [dash] ++ n_W4 (g_in g)) with (bs ++ [w]); [exact HB1|].
      unfold bs, w, RcIdentModel.nthb. rewrite <- !app_assoc. f_equal. f_equal.
      rewrite <- firstn_snoc by lia. replace (S (Z.to_nat 3)) with (length (n_W4 (g_in g))) by lia.
      apply firstn_all.
  - assert (Lq : (Z.to_nat (t + 1) < length (n_W4 (g_in g)))%nat) by lia.
    rewrite Tac_si.nthb_snoc_lt in RD by exact Lq.
    pose proof (Tac_si.nzb_nth _ _ NZW Lq) as NZ.
    pose proof (bz_range (RcIdentModel.nthb (n_W4 (g_in g)) (Z.to_nat (t + 1)))) as BR.
    step. rewrite Tac_si.zxb_bz.
    step. step. step.
    rewrite bv_eqb_lit by lia.
    replace (RcIdentModel.bz (RcIdentModel.nthb (n_W4 (g_in g)) (Z.to_nat (t + 1))) =? 0) with false
      by (symmetry; apply Z.eqb_neq; exact NZ).
    br_if.
    apply (fin_l g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
    + apply (N1_keep g nm tk dp regs mem R' m' _ HN1 (KMm m' HREL) (HOk m' HREL) D1 D2 D3 D4 D5 D6 D7); kr HG.
    + rg HG.
    + rg HG.
    + exact HE.
    + lia.
    + apply (fin_bytes m' m1 _ _ HREL). unfold spk, fsp, SLOT_FRAME.
      replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
      rewrite (firstn_snoc (n_W4 (g_in g)) (Z.to_nat t) (RcIdentModel.zb 0)) by lia.
      rewrite !app_assoc. unfold bs in HB1. rewrite !app_assoc in HB1. exact HB1.
    + rg HG.
    + rg HG.
    + unfold zlen. rg HG.
    + unfold zlen. rg HG.
    + rg HG.
    + rg HG.
Qed.

Lemma seg_H07 : Hcut B APIf ra (Inv_U13be8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13bc8 B APIf ra empty).
Proof.
  intros H0.
  assert (IND : forall n : nat, Hcut B APIf ra (fun g c => Inv_U13bc8_at B APIf ra empty g (4 - Z.of_nat n) c)).
  { induction n as [|n IH].
    - intros g c (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & _ & _ & HT & _). lia.
    - intros g c HC. destruct (Z_le_dec 0 (4 - Z.of_nat (S n))) as [Hp|Hn].
      + apply (step07 (4 - Z.of_nat (S n))); [| exact H0 | | exact HC].
        * destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & _ & _ & HT & _). lia.
        * intros g' c' HC'. apply IH. replace (4 - Z.of_nat n) with (4 - Z.of_nat (S n) + 1) by lia. exact HC'.
      + destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & _ & _ & HT & _). lia. }
  intros g c (t & HC).
  assert (Ht : 0 <= t <= 3)
    by (destruct HC as (nm & tk & dp & L & A & regs & mem & md & _ & _ & _ & _ & _ & _ & _ & HT & _); lia).
  apply (IND (Z.to_nat (4 - t))). replace (4 - Z.of_nat (Z.to_nat (4 - t))) with t by lia. exact HC.
Qed.

End H07.
