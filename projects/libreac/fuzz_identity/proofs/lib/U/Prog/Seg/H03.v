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

Section H03.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_H03 : Hcut B APIf ra (Inv_U13ae8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13b10 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U13aac B APIf ra empty).
Proof.
  intros H8 H10 g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact H8 | exact H10 | | | exact HC | ].
  { intros c' HC'. unfold Inv_U13ae8. exists 0, nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_U13b10. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HNB & E27 & E8 & HSTP & HQ216 & HW4).
  pose proof HNB as (HID & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOU).
  pose proof HSTP as (HQ24 & HSC).
  destruct (wok_chans _ HW) as [Hi Ho].
  pose proof (DEC2_len _ Hi) as Li. pose proof (DEC2_len _ Ho) as Lo.
  assert (LW : length (n_W4 (g_in g)) = 4%nat) by (unfold n_W4; rewrite length_app, Li, Lo; reflexivity).
  pose proof (stem_addr_cases g) as HSA.
  pose proof (Tac_si.nzb_stem (g_in g)) as NZS.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ216)) as R216.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ24)) as R24.
  unfold spk, fsp, SLOT_FRAME in R216, R24.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HSC) as HSCn.
  pose proof (cstr_byte _ _ _ 0 HSCn ltac:(lia)) as RS. rewrite Z.add_0_r in RS.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HW4) as HW4n. unfold spk, fsp, SLOT_FRAME in HW4n.
  pose proof (bz_range (RcIdentModel.nthb (n_stem (g_in g) ++ [z8]) 0)) as BR.
  pose proof E8 as E8'. unfold spk, fsp, SLOT_FRAME in E8'.
  set (a := g_S g - 384 + 192 + 4).
  unfold rmk, Frame.mkR. rewrite E2, E8'.
  step. step. step. if_false.
  step. step.
  rewrite not_lit by lia. rewrite notw_ltu by lia.
  replace (2 ^ 64 - 1 - (g_S g - 384 + 192) <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  br_if.
  step. step. step. step.
  pose proof (st_ok g (normalize rsegs mem) a 1 HWR0 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO.
  step.
  try change (le1 (Z_to_bv 64 0)) with [z8].
  change (Z_to_bv 64 a) with (wa a).
  pose proof (Frame.munch_write [(a, a + 1)] (normalize rsegs mem) (normalize rsegs mem) a [z8] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) a [z8] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a; lia)) as MUS.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a) [z8] (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) a [z8] HSTK0
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)) as STK1.
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 384 + 192) (n_W4 (g_in g)) z8 HW4n
    ltac:(rewrite LW; lia)) as HW41.
  rewrite LW in HW41. change (g_S g - 384 + 192 + Z.of_nat 4) with a in HW41.
  remember (write_to_mem (normalize rsegs mem) (wa a) [z8]) as m1 eqn:Em1.
  assert (D1 : disjoint_from [(a, a + 1)] (spk g 146) 38) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D2 : disjoint_from [(a, a + 1)] (spk g 56) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D3 : disjoint_from [(a, a + 1)] (spk g 48) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D4 : disjoint_from [(a, a + 1)] (spk g 24) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D5 : disjoint_from [(a, a + 1)] (stem_addr g) (zlen (n_stem (g_in g)) + 1))
    by (cbn; unfold spk, fsp, SLOT_FRAME, a in *; lia).
  assert (D6 : disjoint_from [(a, a + 1)] (spk g 216) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (KM1 : forall m', mem_rel rsegs m' m1 -> KM [(a, a + 1)] mem m').
  { intros m' HREL. exact (KM_of _ mem m1 m' HRO MU1 HREL). }
  assert (HOk : forall m', mem_rel rsegs m' m1 -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m1 m' HFR HPM MUS HREL HOU). }
  assert (HN1 : forall R' m', mem_rel rsegs m' m1 ->
    getr R' 9 = getr regs 9 -> getr R' 20 = getr regs 20 -> getr R' 21 = getr regs 21 ->
    getr R' 22 = getr regs 22 -> getr R' 23 = getr regs 23 -> getr R' 24 = getr regs 24 ->
    getr R' 25 = getr regs 25 -> getr R' 19 = getr regs 19 -> getr R' 27 = getr regs 27 ->
    N1 g nm tk dp R' m').
  { intros R' m' HREL F9 F20 F21 F22 F23 F24 F25 F19 F27.
    split; [exact (NB_keep g nm tk dp regs mem R' m' _ HNB (KM1 m' HREL) (HOk m' HREL) D1 D2 D3
      F9 F20 F21 F22 F23 F24 F25 F19)|].
    split; [rewrite F27; exact E27|]. split; [exact (STP_keep g mem m' _ HSTP (KM1 m' HREL) D4 D5)|].
    split; [exact (KM1 m' HREL _ _ ltac:(rewrite length_le8; exact D6) HQ216)|].
    apply (fin_bytes m' m1 _ _ HREL). unfold cstr, spk, fsp, SLOT_FRAME. exact HW41. }
  step. step.
  rewrite Tac_si.zxb_bz. rewrite bv_eqb_lit by lia.
  destruct (Z.eqb_spec (RcIdentModel.bz (RcIdentModel.nthb (n_stem (g_in g) ++ [z8]) 0)) 0) as [Z0|Z0]; br_if.
  - apply (fin_r g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split]].
    + apply (HN1 R' m' HREL); kr HG.
    + kr HG.
    + rewrite HG. greg2. reflexivity.
    + exact (nthb_snoc0 _ Z0).
  - assert (NE : (0 < length (n_stem (g_in g)))%nat).
    { destruct (n_stem (g_in g)) as [|b s] eqn:E; [|cbn; lia]. exfalso. apply Z0. reflexivity. }
    step. step. step.
    apply (fin_l g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    + apply (HN1 R' m' HREL); kr HG.
    + kr HG.
    + unfold zlen. lia.
    + rewrite HG. greg2. f_equal; lia.
    + rewrite HG. greg2. rewrite Tac_si.nthb_snoc_lt by lia. reflexivity.
    + rewrite HG. greg2. reflexivity.
    + rewrite HG. greg2. reflexivity.
    + rewrite HG. greg2. f_equal; unfold spk, fsp, SLOT_FRAME; lia.
    + rewrite HG. greg2. reflexivity.
    + change (firstn (Z.to_nat 0) (n_stem (g_in g))) with (@nil byte). apply bytes_at_nil.
      unfold spk, fsp, SLOT_FRAME. lia.
Qed.

End H03.
