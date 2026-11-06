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

Section H03.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_H03 : Hcut B APIf ra (Inv_K138f4 B APIf ra empty) -> Hcut B APIf ra (Inv_K13968 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K138d0 B APIf ra empty).
Proof.
  intros H4 H68 g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact H4 | exact H68 | | | exact HC | ].
  { intros c' HC'. unfold Inv_K138f4. exists 0, nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_K13968. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN0 & E19 & E8 & HQ200 & HQ168 & HW4).
  pose proof HN0 as ((HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU) & E9 & E18 & HQ16 & HSC).
  destruct (wok_chans _ HW) as [Hi Ho].
  pose proof (DEC2_len _ Hi) as Li. pose proof (DEC2_len _ Ho) as Lo.
  assert (LW : length (n_W4 (g_in g)) = 4%nat) by (unfold n_W4; rewrite length_app, Li, Lo; reflexivity).
  pose proof (stem_addr_cases g) as HSA.
  pose proof (Tac_si.nzb_stem (g_in g)) as NZS.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ200)) as R200.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ16)) as R16.
  unfold spk, fsp, SLOT_FRAME in R200, R16.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HSC) as HSCn.
  pose proof (Tac_si.cstr_byte _ _ _ 0 HSCn ltac:(lia)) as RS. rewrite Z.add_0_r in RS.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HW4) as HW4n. unfold spk, fsp, SLOT_FRAME in HW4n.
  pose proof (bz_range (RcIdentModel.nthb (n_stem (g_in g) ++ [z8]) 0)) as BR.
  set (a := g_S g - 368 + 176 + 4).
  unfold rmk, Frame.mkR. rewrite E2, E8.
  step. step. step. step.
  pose proof (st_ok g (normalize rsegs mem) a 1 HWR0 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO.
  step.
  try change (le1 (Z_to_bv 64 0)) with [z8].
  change (Z_to_bv 64 a) with (wa a).
  pose proof (Mem.mem_inv_store rsegs (normalize rsegs mem) (wa a) [z8] HMI0 HSO) as HMI1.
  pose proof (Frame.munch_write [(a, a + 1)] (normalize rsegs mem) (normalize rsegs mem) a [z8] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) a [z8] (Frame.munch_refl _ _)
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia) ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a; lia)) as MUS.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa a) [z8] (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) a [z8] HSTK0
    ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)) as STK1.
  pose proof (bytes_at_snoc (normalize rsegs mem) (g_S g - 368 + 176) (n_W4 (g_in g)) z8 HW4n
    ltac:(rewrite LW; lia)) as HW41.
  rewrite LW in HW41. change (g_S g - 368 + 176 + Z.of_nat 4) with a in HW41.
  remember (write_to_mem (normalize rsegs mem) (wa a) [z8]) as m1 eqn:Em1.
  assert (D1 : disjoint_from [(a, a + 1)] (spk g 130) 38) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D2 : disjoint_from [(a, a + 1)] (spk g 40) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D3 : disjoint_from [(a, a + 1)] (spk g 16) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D4 : disjoint_from [(a, a + 1)] (stem_addr g) (zlen (n_stem (g_in g)) + 1))
    by (cbn; unfold spk, fsp, SLOT_FRAME, a in *; lia).
  assert (D6 : disjoint_from [(a, a + 1)] (spk g 200) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (D7 : disjoint_from [(a, a + 1)] (spk g 168) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, a; lia).
  assert (KM1 : forall m', mem_rel rsegs m' m1 -> KM [(a, a + 1)] mem m').
  { intros m' HREL. exact (KM_of _ mem m1 m' HRO MU1 HREL). }
  assert (HOk : forall m', mem_rel rsegs m' m1 -> OUTS g nm tk dp m').
  { intros m' HREL. exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m1 m' HFR HPM MUS HREL HOU). }
  assert (HN1 : forall R' m', mem_rel rsegs m' m1 -> YK11.getr R' 8 = Z_to_bv 64 (spk g 176) ->
    YK11.getr R' 20 = YK11.getr regs 20 -> YK11.getr R' 21 = YK11.getr regs 21 ->
    YK11.getr R' 22 = YK11.getr regs 22 -> YK11.getr R' 23 = YK11.getr regs 23 ->
    YK11.getr R' 24 = YK11.getr regs 24 -> YK11.getr R' 25 = YK11.getr regs 25 ->
    YK11.getr R' 9 = YK11.getr regs 9 -> YK11.getr R' 18 = YK11.getr regs 18 -> N1 g nm tk dp R' m').
  { intros R' m' HREL F8 F20 F21 F22 F23 F24 F25 F9 F18. split.
    - exact (N0_keep g nm tk dp regs mem R' m' _ HN0 (KM1 m' HREL) (HOk m' HREL) D1 D2 D3 D4
        F20 F21 F22 F23 F24 F25 F9 F18).
    - split; [exact F8|]. split.
      + apply (fin_bytes m' m1 _ _ HREL). unfold cstr, spk, fsp, SLOT_FRAME. exact HW41.
      + split; [exact (KM1 m' HREL _ _ ltac:(rewrite length_le8; exact D6) HQ200)|].
        exact (KM1 m' HREL _ _ ltac:(rewrite length_le8; exact D7) HQ168). }
  step.
  step.
  rewrite Tac_si.zxb_bz. rewrite bv_eqb_lit by lia.
  destruct (Z.eqb_spec (RcIdentModel.bz (RcIdentModel.nthb (n_stem (g_in g) ++ [z8]) 0)) 0) as [Z0|Z0]; cbn [negb].
  - assert (ES : n_stem (g_in g) = []).
    { destruct (n_stem (g_in g)) as [|b s] eqn:E; [reflexivity|]. exfalso.
      unfold Tac_si.nzb in NZS. cbn [forallb] in NZS. apply andb_prop in NZS as [NB _].
      cbn in Z0. unfold RcIdentModel.nthb in Z0. cbn in Z0. rewrite Z0 in NB. discriminate. }
    apply (fin_r g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split]]].
    + apply (HN1 R' m' HREL); rewrite HG; reflexivity.
    + rewrite HG. exact E19.
    + rewrite HG. rewrite ES. reflexivity.
    + rewrite ES. apply bytes_at_nil. unfold spk, fsp, SLOT_FRAME. lia.
    + unfold n_ends_w4. rewrite ES. reflexivity.
  - assert (NE : (0 < length (n_stem (g_in g)))%nat).
    { destruct (n_stem (g_in g)) as [|b s] eqn:E; [|cbn; lia]. exfalso. apply Z0. reflexivity. }
    step. step.
    apply (fin_l g mem regs _ _ _ _ _ m1 MUS WM1 STK1); [rewrite E2; reflexivity | reflexivity | reflexivity |].
    intros R' m' HG HREL. cbv beta.
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    + apply (HN1 R' m' HREL); rewrite HG; reflexivity.
    + rewrite HG. exact E19.
    + unfold zlen. lia.
    + rewrite HG. reflexivity.
    + rewrite HG. greg2. f_equal; unfold spk, fsp, SLOT_FRAME; lia.
    + rewrite HG. greg2. f_equal; lia.
    + rewrite HG. greg2. rewrite Tac_si.nthb_snoc_lt by lia. reflexivity.
    + change (firstn (Z.to_nat 0) (n_stem (g_in g))) with (@nil byte). apply bytes_at_nil.
      unfold spk, fsp, SLOT_FRAME. lia.
Qed.

End H03.
