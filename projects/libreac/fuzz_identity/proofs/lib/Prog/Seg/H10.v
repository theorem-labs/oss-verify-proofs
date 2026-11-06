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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh1 Tac_sh2.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma bytes_head_eq : forall m a b s, bytes_at rsegs m a (b :: s) -> bytes_at rsegs m a [Z_to_bv 8 0] ->
  b = Z_to_bv 8 0.
Proof.
  intros m a b s (_ & _ & H1) (_ & _ & H2). specialize (H1 0%nat ltac:(cbn; lia)).
  specialize (H2 0%nat ltac:(cbn; lia)). rewrite H1 in H2. cbn in H2. injection H2 as E. exact E.
Qed.

Section H10.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_contract.

Lemma H10_ec : Hcut B APIf ra (Inv_K139ec B APIf ra empty).
Proof.
  intros g c (nm & tk & dp & L & A & regs & mem & md & -> & HFR & HPM & (H9 & _ & HB8)).
  exfalso. pose proof H9 as (HN1 & _ & _ & HCS).
  pose proof HN1 as ((HNB & _) & _). pose proof HNB as (_ & HW & _).
  pose proof (n_ln_le (g_in g) HW) as LN. pose proof (Tac_si.nzb_EXP_NM _ HW) as NZ.
  unfold cstr, b8 in *. unfold n_ln in LN.
  destruct (n_EXP_NM (g_in g)) as [|b s]; [cbn in LN; lia|].
  cbn [app] in HCS. pose proof (bytes_head_eq _ _ _ _ HCS HB8) as E.
  unfold Tac_si.nzb in NZ. cbn [forallb] in NZ. rewrite E in NZ. discriminate.
Qed.

Lemma H10_f4 : Hcut B APIf ra (Inv_K13a2c B APIf ra empty) -> Hcut B APIf ra (Inv_K139f4 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_K13a2c. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (s1_frame_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HLO & _ & _ & _ & _ & _ & _).
  unfold fsp, SLOT_FRAME in HLO.
  destruct HP as ((H9 & E19) & E14 & HNMB).
  pose proof H9 as (HN1 & E26 & HROW & HCS).
  pose proof HN1 as (HN0 & E8 & HW4 & HQ200 & HQ168).
  pose proof HN0 as (HNB & E9 & E18 & HQ16 & HSC).
  pose proof HNB as (HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU).
  assert (HNC : NC g nm tk dp regs mem).
  { split; [exact HNB|]. split; [exact E26|]. split; [exact E19|]. split; [exact HROW | exact HCS]. }
  destruct (ld_bounds (g_in g) HW) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (caps_range (g_in g)) as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold zlen in B2, B3, B4, B5. unfold n_ln in B1, B4.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HNMB) as HB0. unfold spk, fsp, SLOT_FRAME in HB0.
  set (q := g_S g - 368 + 48 + Z.of_nat (length (n_EXP_NM (g_in g)))).
  set (p := g_S g - 368 + 168).
  set (WA := [(g_S g - 368 - 64, g_S g - 368); (q, g_S g - 368 + 48 + ld1 (g_in g)); (p, p + 8)]).
  unfold rmk, Frame.mkR. rewrite E2, E14, E19, E18.
  unfold n_ln.
  step. step. step. step. step. step.
  pose proof (st_ok g (normalize rsegs mem) q 1 HWR0 ltac:(unfold q; lia) ltac:(unfold q; lia)) as HSO1.
  step.
  change (le1 (Z_to_bv 64 32)) with [Z_to_bv 8 32].
  change (Z_to_bv 64 q) with (wa q).
  pose proof (Frame.munch_write WA (normalize rsegs mem) (normalize rsegs mem) q [Z_to_bv 8 32]
    (Frame.munch_refl _ _) ltac:(unfold q; lia) ltac:(cbn; unfold q; lia) ltac:(unfold WA; cbn; unfold q; lia)) as MU1.
  pose proof (Frame.wmono_write rsegs _ _ (wa q) [Z_to_bv 8 32] (Frame.wmono_refl _ (normalize rsegs mem))) as WM1.
  pose proof (Frame.stk_write rsegs _ _ _ q [Z_to_bv 8 32] HSTK0 ltac:(unfold q; lia) ltac:(cbn; unfold q; lia))
    as STK1.
  pose proof (Mem.mem_inv_store rsegs _ (wa q) [Z_to_bv 8 32] HMI0 HSO1) as HMI1.
  pose proof (Mem.wr_at_write rsegs _ _ _ (wa q) [Z_to_bv 8 32] HWR0) as HWR1.
  pose proof (bytes_at_snoc _ _ _ (Z_to_bv 8 32) HB0 ltac:(unfold q in *; lia)) as HB1. fold q in HB1.
  remember (write_to_mem (normalize rsegs mem) (wa q) [Z_to_bv 8 32]) as m1 eqn:Em1.
  pose proof (st_ok g m1 (q + 1) 1 HWR1 ltac:(unfold q; lia) ltac:(unfold q; lia)) as HSO2.
  step.
  change (le1 (Z_to_bv 64 40)) with [Z_to_bv 8 40].
  change (Z_to_bv 64 (q + 1)) with (wa (q + 1)).
  pose proof (Frame.munch_write WA _ m1 (q + 1) [Z_to_bv 8 40] MU1 ltac:(unfold q; lia) ltac:(cbn; unfold q; lia)
    ltac:(unfold WA; cbn; unfold q; lia)) as MU2.
  pose proof (Frame.wmono_write rsegs _ m1 (wa (q + 1)) [Z_to_bv 8 40] WM1) as WM2.
  pose proof (Frame.stk_write rsegs _ _ _ (q + 1) [Z_to_bv 8 40] STK1 ltac:(unfold q; lia) ltac:(cbn; unfold q; lia))
    as STK2.
  pose proof (Mem.mem_inv_store rsegs _ (wa (q + 1)) [Z_to_bv 8 40] HMI1 HSO2) as HMI2.
  pose proof (Mem.wr_at_write rsegs _ _ _ (wa (q + 1)) [Z_to_bv 8 40] HWR1) as HWR2.
  pose proof (bytes_at_snoc _ _ _ (Z_to_bv 8 40) HB1 ltac:(rewrite length_app; cbn [length]; unfold q in *; lia))
    as HB2.
  replace (g_S g - 368 + 48 + Z.of_nat (length (n_EXP_NM (g_in g) ++ [Z_to_bv 8 32]))) with (q + 1) in HB2
    by (rewrite length_app; cbn [length]; unfold q; lia).
  remember (write_to_mem m1 (wa (q + 1)) [Z_to_bv 8 40]) as m2 eqn:Em2.
  set (v8 := le8 (Z_to_bv 64 (Z.of_nat (length (n_EXP_NM (g_in g))) + 2))).
  assert (L8 : length v8 = 8%nat) by apply length_le8.
  pose proof (st_ok g m2 p 8 HWR2 ltac:(unfold p; lia) ltac:(unfold p; lia)) as HSO3.
  step.
  change (Z_to_bv 64 p) with (wa p).
  change (le8 (Z_to_bv 64 (Z.of_nat (length (n_EXP_NM (g_in g))) + 2))) with v8.
  pose proof (Frame.munch_write WA _ m2 p v8 MU2 ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia)
    ltac:(rewrite L8; unfold WA; cbn; unfold p; lia)) as MU3.
  pose proof (Frame.wmono_write rsegs _ m2 (wa p) v8 WM2) as WM3.
  pose proof (Frame.stk_write rsegs _ _ _ p v8 STK2 ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia)) as STK3.
  pose proof (Mem.mem_inv_store rsegs _ (wa p) v8 HMI2 ltac:(rewrite L8; exact HSO3)) as HMI3.
  pose proof (Mem.wr_at_write rsegs _ _ _ (wa p) v8 HWR2) as HWR3.
  pose proof (Mem.bytes_at_write_same rsegs m2 p v8 ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia)) as HNp.
  pose proof (Mem.bytes_at_write_other rsegs m2 p v8 _ _ HB2 ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia)
    ltac:(rewrite L8, !length_app; cbn [length]; unfold p, q in *; lia)) as HB3.
  remember (write_to_mem m2 (wa p) v8) as m3 eqn:Em3.
  step. step. step. step. step.
  eapply (pd_call PD) with (lo := g_S g - 16384) (b := g_S g - 368 + 48) (p := p) (v := t_in (g_in g)) (mn := 1)
    (N := Z_to_bv 64 (Z.of_nat (length (n_EXP_NM (g_in g))) + 2));
    rewrite ?(MState.unsigned_lit (Z.of_nat (length (n_EXP_NM (g_in g))) + 2)),
      ?(MState.unsigned_lit (g_S g - 368)) by lia;
    unfold PUT_DEC_FRAME, dec_len in *.
  all: try first
    [ reflexivity
    | exact HNp
    | apply ro_agree_inv; exact HMI3
    | eapply wr_sub; [exact HWR3 | unfold p; lia | unfold p; lia | lia]
    | rewrite MState.unsigned_lit by lia; apply Z.mod_small; lia
    | left; rewrite MState.unsigned_lit by lia; lia
    | unfold p; Z.div_mod_to_equations; lia
    | unfold p; lia
    | right; unfold p; lia
    | destruct (Frame.stk_split rsegs m3 (g_S g - 65536) (g_S g - 368) (g_S g) STK3 ltac:(lia)) as [X _];
      exact (proj2 (Frame.stk_split rsegs m3 (g_S g - 65536) (g_S g - 16384) (g_S g - 368) X ltac:(lia))) ].
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MF4 HRO4 HDEC HN.
  unfold PUT_DEC_FRAME, dec_len in *.
  retpc.
  pose proof MF4 as (MU4 & WM4 & _).
  assert (MUa : Frame.munch WA (normalize rsegs mem) m4).
  { apply (Frame.munch_trans WA _ m3 m4); [exact MU3|].
    eapply Frame.munch_weaken; [|exact MU4]. unfold WA, p, q in *. subfp. }
  assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) WA)
    by (unfold WA, p, q; repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil).
  assert (D1 : disjoint_from WA (spk g 130) 38) by (unfold WA, p, q; cbn; unfold spk, fsp, SLOT_FRAME; lia).
  assert (D2 : disjoint_from WA (spk g 40) 8) by (unfold WA, p, q; cbn; unfold spk, fsp, SLOT_FRAME; lia).
  assert (D3 : disjoint_from WA (spk g 32) 8) by (unfold WA, p, q; cbn; unfold spk, fsp, SLOT_FRAME; lia).
  assert (D4 : disjoint_from WA (spk g 226) (n_ln (g_in g) + 1))
    by (unfold WA, p, q, n_ln; cbn; unfold spk, fsp, SLOT_FRAME; lia).
  pose proof (mfr_bytes _ _ _ _ _ MF4 HB3 ltac:(rewrite !length_app; cbn; unfold p, q in *; lia)) as HB4.
  apply (fin_mem g mem regs 0x13a2c _ _ m4 (munch_SWIN g _ _ _ MUa FW) (Frame.wmono_trans _ _ _ _ WM3 WM4)
    (mfr_stk _ _ _ _ _ MF4 STK3)); [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM WA mem m') by exact (KM_of _ mem m4 m' HRO MUa HREL).
  assert (HO : OUTS g nm tk dp m')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m4 m' HFR HPM (munch_SWIN g _ _ _ MUa FW)
      HREL HOU).
  split; [|split].
  - unfold HAb. split; [|split; [|split; [|split]]].
    + apply (NC_keep g nm tk dp regs mem R' m' _ HNC KMm HO D1 D2 D3 D4); rewrite HG;
        first [reflexivity | rewrite E19; reflexivity | rewrite E14; reflexivity | rewrite E18; reflexivity].
    + rewrite HG. reflexivity.
    + rewrite HG. reflexivity.
    + rewrite HG. reflexivity.
    + apply (fin_bytes m' m4 _ _ HREL). unfold q64, spk, fsp, SLOT_FRAME.
      replace (ld1 (g_in g)) with (Z.of_nat (length (n_EXP_NM (g_in g))) + 2 +
        Z.of_nat (length (DEC (t_in (g_in g)) 1))) by lia.
      exact HN.
  - rewrite HG. reflexivity.
  - apply (fin_bytes m' m4 _ _ HREL). unfold spk, fsp, SLOT_FRAME, dp1.
    replace (n_EXP_NM (g_in g) ++ s_open ++ DEC (t_in (g_in g)) 1) with
      (((n_EXP_NM (g_in g) ++ [Z_to_bv 8 32]) ++ [Z_to_bv 8 40]) ++ DEC (t_in (g_in g)) 1)
      by (rewrite <- !app_assoc; reflexivity).
    apply (proj2 (Mem.bytes_at_app rsegs m4 _ _ _)). split; [exact HB4|].
    rewrite !length_app. cbn [length].
    replace (g_S g - 368 + 48 + Z.of_nat (length (n_EXP_NM (g_in g)) + 1 + 1)) with
      (g_S g - 368 + 48 + (Z.of_nat (length (n_EXP_NM (g_in g))) + 2)) by lia.
    exact HDEC.
Qed.

Lemma seg_H10 : Hcut B APIf ra (Inv_K13a2c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K139ec B APIf ra empty) /\ Hcut B APIf ra (Inv_K139f4 B APIf ra empty).
Proof. intros HX. split; [exact H10_ec | exact (H10_f4 HX)]. Qed.

End H10.
