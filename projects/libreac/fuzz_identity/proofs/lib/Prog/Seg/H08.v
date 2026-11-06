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

Section H08.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_H08 : Hcut B APIf ra (Inv_K139cc B APIf ra empty) -> Hcut B APIf ra (Inv_K139a4 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_K139cc, Inv_K139cc_at. exists 0, nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HN1 & E19 & E26 & HB).
  pose proof HN1 as (HN0 & E8 & HW4 & HQ200 & HQ168).
  pose proof HN0 as ((HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU) & E9 & E18 & HQ16 & HSC).
  pose proof (stem_addr_cases g) as HSA.
  pose proof (n_ln_le (g_in g) HW) as LN. unfold n_ln in LN.
  pose proof (Tac_si.nzb_EXP_NM _ HW) as NZE.
  pose proof (Tac_si.nzb_nth _ 0 NZE ltac:(lia)) as NZ.
  pose proof (bz_range (RcIdentModel.nthb (n_EXP_NM (g_in g)) 0)) as BR.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HB) as HBn. unfold spk, fsp, SLOT_FRAME in HBn.
  set (p := g_S g - 368 + 32).
  set (a := g_S g - 368 + 226 + Z.of_nat (length (n_EXP_NM (g_in g)))).
  set (W := [(p, p + 8); (a, a + 1)]).
  set (v8 := le8 (Z_to_bv 64 (t_row (g_in g)))).
  assert (L8 : length v8 = 8%nat) by apply length_le8.
  unfold n_ln in E26. unfold rmk, Frame.mkR. rewrite E2, E19, E26.
  pose proof (st_ok g (normalize rsegs mem) p 8 HWR0 ltac:(unfold p; lia) ltac:(unfold p; lia)) as HSO1.
  step.
  change (Z_to_bv 64 p) with (wa p). change (le8 (Z_to_bv 64 (t_row (g_in g)))) with v8.
  pose proof (Frame.munch_write W (normalize rsegs mem) (normalize rsegs mem) p v8 (Frame.munch_refl _ _)
    ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia) ltac:(rewrite L8; unfold W; cbn; lia)) as MU1.
  pose proof (Frame.munch_write (SWIN g) (normalize rsegs mem) (normalize rsegs mem) p v8 (Frame.munch_refl _ _)
    ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia)
    ltac:(rewrite L8; unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold p; lia)) as MUS1.
  pose proof (Frame.wmono_write rsegs _ _ (wa p) v8 (Frame.wmono_refl _ (normalize rsegs mem))) as WM1.
  pose proof (Frame.stk_write rsegs _ _ _ p v8 HSTK0 ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia)) as STK1.
  pose proof (Mem.wr_at_write rsegs _ _ _ (wa p) v8 HWR0) as HWR1.
  pose proof (Mem.bytes_at_write_same rsegs (normalize rsegs mem) p v8 ltac:(unfold p; lia)
    ltac:(rewrite L8; unfold p; lia)) as HQ1.
  pose proof (Mem.bytes_at_write_other rsegs (normalize rsegs mem) p v8 _ _ HBn ltac:(unfold p; lia)
    ltac:(rewrite L8; unfold p; lia) ltac:(rewrite L8; unfold p; lia)) as HB1.
  remember (write_to_mem (normalize rsegs mem) (wa p) v8) as m1 eqn:Em1.
  step. step.
  pose proof (st_ok g m1 a 1 HWR1 ltac:(unfold a; lia) ltac:(unfold a; lia)) as HSO2.
  step.
  try change (le1 (Z_to_bv 64 0)) with [z8].
  change (Z_to_bv 64 a) with (wa a).
  pose proof (Frame.munch_write W _ m1 a [z8] MU1 ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)
    ltac:(unfold W; cbn; lia)) as MU2.
  pose proof (Frame.munch_write (SWIN g) _ m1 a [z8] MUS1 ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)
    ltac:(unfold SWIN, SLOT_K, SLOT_STACK; cbn; unfold a; lia)) as MUS2.
  pose proof (Frame.wmono_write rsegs _ m1 (wa a) [z8] WM1) as WM2.
  pose proof (Frame.stk_write rsegs _ _ _ a [z8] STK1 ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)) as STK2.
  pose proof (Mem.bytes_at_write_other rsegs m1 a [z8] p v8 HQ1 ltac:(unfold a; lia) ltac:(cbn; unfold a; lia)
    ltac:(rewrite L8; cbn; unfold p, a; lia)) as HQ2.
  pose proof (bytes_at_snoc m1 (g_S g - 368 + 226) _ z8 HB1 ltac:(lia)) as HB2. fold a in HB2.
  remember (write_to_mem m1 (wa a) [z8]) as m2 eqn:Em2.
  pose proof (Tac_si.cstr_byte m2 (g_S g - 368 + 226) _ 0 HB2 ltac:(lia)) as RD. rewrite Z.add_0_r in RD.
  rewrite Tac_si.nthb_snoc_lt in RD by lia.
  step. rewrite Tac_si.zxb_bz.
  step.
  rewrite bv_eqb_lit by lia.
  replace (RcIdentModel.bz (RcIdentModel.nthb (n_EXP_NM (g_in g)) 0) =? 0) with false
    by (symmetry; apply Z.eqb_neq; exact NZ).
  br_if.
  step. step. step. step.
  apply (fin_mem g mem regs 0x139cc _ _ m2 MUS2 WM2 STK2); [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM W mem m') by exact (KM_of _ mem m2 m' HRO MU2 HREL).
  assert (HO : OUTS g nm tk dp m')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m2 m' HFR HPM MUS2 HREL HOU).
  assert (D1 : disjoint_from W (spk g 130) 38) by (unfold W; cbn; unfold spk, fsp, SLOT_FRAME, p, a; lia).
  assert (D2 : disjoint_from W (spk g 40) 8) by (unfold W; cbn; unfold spk, fsp, SLOT_FRAME, p, a; lia).
  assert (D3 : disjoint_from W (spk g 16) 8) by (unfold W; cbn; unfold spk, fsp, SLOT_FRAME, p, a; lia).
  assert (D4 : disjoint_from W (stem_addr g) (zlen (n_stem (g_in g)) + 1))
    by (unfold W; cbn; unfold zlen, spk, fsp, SLOT_FRAME, p, a in *; lia).
  assert (D5 : disjoint_from W (spk g 176) 5) by (unfold W; cbn; unfold spk, fsp, SLOT_FRAME, p, a; lia).
  assert (D6 : disjoint_from W (spk g 200) 8) by (unfold W; cbn; unfold spk, fsp, SLOT_FRAME, p, a; lia).
  assert (D7 : disjoint_from W (spk g 168) 8) by (unfold W; cbn; unfold spk, fsp, SLOT_FRAME, p, a; lia).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - split; [split; [|split; [|split]]|].
    + apply (N1_keep g nm tk dp regs mem R' m' _ HN1 KMm HO D1 D2 D3 D4 D5 D6 D7); rewrite HG; reflexivity.
    + rewrite HG. reflexivity.
    + apply (fin_bytes m' m2 _ _ HREL). unfold q64, spk, fsp, SLOT_FRAME. exact HQ2.
    + apply (fin_bytes m' m2 _ _ HREL). unfold cstr, spk, fsp, SLOT_FRAME. exact HB2.
    + rewrite HG. greg2. exact E9.
  - unfold n_ln. lia.
  - rewrite HG. greg2. unfold spk, fsp, SLOT_FRAME. f_equal; lia.
  - rewrite HG. greg2. unfold spk, fsp, SLOT_FRAME. f_equal; lia.
  - rewrite HG. greg2. reflexivity.
  - rewrite HG. greg2. reflexivity.
  - change (firstn (Z.to_nat 0) (n_EXP_NM (g_in g))) with (@nil byte). apply bytes_at_nil.
    unfold spk, fsp, SLOT_FRAME. lia.
Qed.

End H08.
