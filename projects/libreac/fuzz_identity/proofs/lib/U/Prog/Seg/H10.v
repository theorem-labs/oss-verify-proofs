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
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_head_eq : forall m a b s, bytes_at rsegs m a (b :: s) -> bytes_at rsegs m a [Z_to_bv 8 0] ->
  b = Z_to_bv 8 0.
Proof.
  intros m a b s (_ & _ & H1) (_ & _ & H2). specialize (H1 0%nat ltac:(cbn; lia)).
  specialize (H2 0%nat ltac:(cbn; lia)). rewrite H1 in H2. cbn in H2. injection H2 as E. exact E.
Qed.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma open_img : forall m, Mem.mem_inv rsegs m -> bytes_at rsegs m 66487 [Z_to_bv 8 40; Z_to_bv 8 0].
Proof.
  intros m H. apply (ro_bytes_at rsegs m); [exact H | lia | cbn; lia |].
  apply ro_chk_sound. vm_compute. reflexivity.
Qed.

Ltac addr_to q := try lazymatch goal with |- context [write_to_mem ?m0 (Z_to_bv 64 ?x) _] =>
  replace x with q by (unfold q in *; lia) end.

Section H10.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_c.put_dec_contract.

Lemma seg_H10 : Hcut B APIf ra (Inv_U13c98 B APIf ra empty) -> Hcut B APIf ra (Inv_U13c44 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13c98. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (H9a' & E10 & E26 & [(E11 & HNMB) | (_ & HZ)]).
  2: { exfalso. pose proof H9a' as (((_ & HW & _) & _) & _ & HCS).
       pose proof (n_ln_le (g_in g) HW) as LN. pose proof (Tac_si.nzb_EXP_NM _ HW) as NZ.
       unfold cstr, b8 in *. unfold n_ln in LN.
       destruct (n_EXP_NM (g_in g)) as [|b s]; [cbn in LN; lia|].
       cbn [app] in HCS. pose proof (bytes_head_eq _ _ _ _ HCS HZ) as E.
       unfold Tac_si.nzb in NZ. cbn [forallb] in NZ. rewrite E in NZ. discriminate. }
  pose proof H9a' as (HN1 & E8 & HNM).
  pose proof HN1 as (HNB & E27 & HSTP & HQ216 & HW4).
  pose proof HNB as (HID & HW & E9 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HQ56 & HQ48 & HOU).
  destruct (ld_bounds (g_in g) HW) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (caps_range (g_in g)) as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold zlen in B2, B3, B4, B5. unfold n_ln in B1, B4.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HQ56)) as R56. unfold spk, fsp, SLOT_FRAME in R56.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HNMB) as HBe. unfold spk, fsp, SLOT_FRAME in HBe.
  pose proof E10 as E10'. unfold spk, fsp, SLOT_FRAME in E10'.
  pose proof E11 as E11'. unfold n_ln in E11'.
  set (q := g_S g - 384 + 64 + Z.of_nat (length (n_EXP_NM (g_in g)))).
  set (p := g_S g - 384 + 184).
  set (WA := [(g_S g - 384 - 16, g_S g - 384); (q, g_S g - 384 + 64 + ld1 (g_in g)); (p, p + 8)]).
  unfold rmk, Frame.mkR. rewrite E2, E10', E11', E26, E9.
  step. step. step. step. step. step. ltu_off.
  step.
  pose proof (st_ok g (normalize rsegs mem) q 1 HWR0 ltac:(unfold q; lia) ltac:(unfold q; lia)) as HSO1.
  step.
  try change (le1 (Z_to_bv 64 32)) with [Z_to_bv 8 32].
  addr_to q.
  change (Z_to_bv 64 q) with (wa q).
  pose proof (Frame.munch_write WA (normalize rsegs mem) (normalize rsegs mem) q [Z_to_bv 8 32]
    (Frame.munch_refl _ _) ltac:(unfold q; lia) ltac:(cbn; unfold q; lia) ltac:(unfold WA; cbn; unfold q; lia)) as MU1.
  pose proof (Frame.wmono_write rsegs _ _ (wa q) [Z_to_bv 8 32] (Frame.wmono_refl _ (normalize rsegs mem))) as WM1.
  pose proof (Frame.stk_write rsegs _ _ _ q [Z_to_bv 8 32] HSTK0 ltac:(unfold q; lia) ltac:(cbn; unfold q; lia))
    as STK1.
  pose proof (Mem.mem_inv_store rsegs _ (wa q) [Z_to_bv 8 32] HMI0 HSO1) as HMI1.
  pose proof (Mem.wr_at_write rsegs _ _ _ (wa q) [Z_to_bv 8 32] HWR0) as HWR1.
  pose proof (bytes_at_snoc _ _ _ (Z_to_bv 8 32) HBe ltac:(unfold q in *; lia)) as HB1. fold q in HB1.
  remember (write_to_mem (normalize rsegs mem) (wa q) [Z_to_bv 8 32]) as m1 eqn:Em1.
  pose proof (rd1 _ _ _ (bytes_at_one m1 66487 _ 0 (open_img m1 HMI1) ltac:(cbn; lia))) as RO1.
  cbn [nth] in RO1. rewrite Z.add_0_r in RO1.
  step. step. step. step. step. step. eqb_off.
  step. ltu_off.
  step.
  pose proof (st_ok g m1 (q + 1) 1 HWR1 ltac:(unfold q; lia) ltac:(unfold q; lia)) as HSO2.
  step.
  try change (le1 (Z_to_bv 64 40)) with [Z_to_bv 8 40].
  try change (le1 (zxb (Z_to_bv 8 40))) with [Z_to_bv 8 40].
  addr_to (q + 1).
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
  replace (g_S g - 384 + 64 + Z.of_nat (length (n_EXP_NM (g_in g) ++ [Z_to_bv 8 32]))) with (q + 1) in HB2
    by (rewrite length_app; cbn [length]; unfold q; lia).
  remember (write_to_mem m1 (wa (q + 1)) [Z_to_bv 8 40]) as m2 eqn:Em2.
  pose proof (rd1 _ _ _ (bytes_at_one m2 66487 _ 1 (open_img m2 HMI2) ltac:(cbn; lia))) as RO2.
  cbn [nth] in RO2. change (Z.of_nat 1) with 1 in RO2.
  step. step. step. step. step. step. eqb_on.
  pose proof (st_ok g m2 p 8 HWR2 ltac:(unfold p; lia) ltac:(unfold p; lia)) as HSO3.
  step.
  change (Z_to_bv 64 p) with (wa p).
  lazymatch goal with |- context [write_to_mem m2 (wa p) (le8 (Z_to_bv 64 ?x))] =>
    replace x with (Z.of_nat (length (n_EXP_NM (g_in g))) + 2) by (first [lia | zarith]) end.
  set (v8 := le8 (Z_to_bv 64 (Z.of_nat (length (n_EXP_NM (g_in g))) + 2))).
  assert (L8 : length v8 = 8%nat) by apply length_le8.
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
  step. step. step. step. step. step.
  eapply (pd_call PD) with (lo := g_S g - 16384) (b := g_S g - 384 + 64) (p := p) (v := t_in (g_in g)) (mn := 1)
    (N := Z_to_bv 64 (Z.of_nat (length (n_EXP_NM (g_in g))) + 2));
    rewrite ?(MState.unsigned_lit (Z.of_nat (length (n_EXP_NM (g_in g))) + 2)),
      ?(MState.unsigned_lit (g_S g - 384)) by lia;
    unfold put_dec_c.PUT_DEC_FRAME, dec_len in *.
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
    | destruct (Frame.stk_split rsegs m3 (g_S g - 65536) (g_S g - 384) (g_S g) STK3 ltac:(lia)) as [X _];
      exact (proj2 (Frame.stk_split rsegs m3 (g_S g - 65536) (g_S g - 16384) (g_S g - 384) X ltac:(lia))) ].
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MF4 HRO4 HDEC HN.
  unfold put_dec_c.PUT_DEC_FRAME, dec_len in *.
  retpc.
  pose proof MF4 as (MU4 & WM4 & _).
  assert (MUa : Frame.munch WA (normalize rsegs mem) m4).
  { apply (Frame.munch_trans WA _ m3 m4); [exact MU3|].
    eapply Frame.munch_weaken; [|exact MU4]. unfold WA, p, q in *. subfp. }
  assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) WA)
    by (unfold WA, p, q; repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil).
  assert (D1 : disjoint_from WA (spk g 146) 38) by (unfold WA, p, q; cbn; unfold spk, fsp, SLOT_FRAME; lia).
  assert (D2 : disjoint_from WA (spk g 56) 8) by (unfold WA, p, q; cbn; unfold spk, fsp, SLOT_FRAME; lia).
  assert (D3 : disjoint_from WA (spk g 48) 8) by (unfold WA, p, q; cbn; unfold spk, fsp, SLOT_FRAME; lia).
  assert (D4 : disjoint_from WA (spk g 242) (n_ln (g_in g) + 1))
    by (unfold WA, p, q, n_ln; cbn; unfold spk, fsp, SLOT_FRAME; lia).
  pose proof (mfr_bytes _ _ _ _ _ MF4 HB3 ltac:(rewrite !length_app; cbn; unfold p, q in *; lia)) as HB4.
  apply (fin_mem g mem regs 0x13c98 _ _ m4 (munch_SWIN g _ _ _ MUa FW) (Frame.wmono_trans _ _ _ _ WM3 WM4)
    (mfr_stk _ _ _ _ _ MF4 STK3)); [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM WA mem m') by exact (KM_of _ mem m4 m' HRO MUa HREL).
  assert (HO : OUTS g nm tk dp m')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m4 m' HFR HPM (munch_SWIN g _ _ _ MUa FW)
      HREL HOU).
  split; [|split].
  - split; [split; [|split; [|split; [|split]]]|].
    + apply (NB_keep g nm tk dp regs mem R' m' _ HNB KMm HO D1 D2 D3); kr HG.
    + rg HG.
    + rg HG.
    + rg HG.
    + apply KMm; [|exact HNM]. unfold n_ln in D4. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add.
      exact D4.
    + rg HG.
  - apply (fin_bytes m' m4 _ _ HREL). unfold q64, spk, fsp, SLOT_FRAME.
    replace (ld1 (g_in g)) with (Z.of_nat (length (n_EXP_NM (g_in g))) + 2 +
      Z.of_nat (length (DEC (t_in (g_in g)) 1))) by lia.
    exact HN.
  - apply (fin_bytes m' m4 _ _ HREL). unfold spk, fsp, SLOT_FRAME, dp1.
    replace (n_EXP_NM (g_in g) ++ s_open ++ DEC (t_in (g_in g)) 1) with
      (((n_EXP_NM (g_in g) ++ [Z_to_bv 8 32]) ++ [Z_to_bv 8 40]) ++ DEC (t_in (g_in g)) 1)
      by (rewrite <- !app_assoc; reflexivity).
    apply (proj2 (Mem.bytes_at_app rsegs m4 _ _ _)). split; [exact HB4|].
    rewrite !length_app. cbn [length].
    replace (g_S g - 384 + 64 + Z.of_nat (length (n_EXP_NM (g_in g)) + 1 + 1)) with
      (g_S g - 384 + 64 + (Z.of_nat (length (n_EXP_NM (g_in g))) + 2)) by lia.
    exact HDEC.
Qed.

End H10.
