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
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H13.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_contract.

Lemma seg_H13 : Hcut B APIf ra (Inv_K13a74 B APIf ra empty) -> Hcut B APIf ra (Inv_K13a58 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_K13a74. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (s1_frame_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HLO & _ & _ & _ & _ & _ & _).
  unfold fsp, SLOT_FRAME in HLO.
  destruct HP as (HAB & HDP & E12 & E27).
  pose proof HAB as (HNC & E9 & E18 & E8 & HLD).
  pose proof HNC as ((HID & HW & _ & _ & _ & _ & _ & _ & _ & HOU) & _).
  destruct (ld_bounds (g_in g) HW) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (caps_range (g_in g)) as (C1 & C2 & C3 & C4 & C5 & C6).
  unfold zlen in B2, B3, B4, B5.
  assert (LDP : Z.of_nat (length (dp1 (g_in g) ++ s_in)) = ld1 (g_in g) + 6).
  { rewrite length_app. change (length s_in) with 6%nat. unfold ld1, zlen. lia. }
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HDP) as HDPn. unfold spk, fsp, SLOT_FRAME in HDPn.
  set (p := g_S g - 368 + 168).
  set (v8 := le8 (Z_to_bv 64 (ld1 (g_in g) + 6))).
  assert (L8 : length v8 = 8%nat) by apply length_le8.
  unfold rmk, Frame.mkR. rewrite E2, E12, E9.
  pose proof (st_ok g (normalize rsegs mem) p 8 HWR0 ltac:(unfold p; lia) ltac:(unfold p; lia)) as HSO.
  step.
  change (Z_to_bv 64 p) with (wa p).
  change (le8 (Z_to_bv 64 (ld1 (g_in g) + 6))) with v8.
  pose proof (Mem.mem_inv_store rsegs (normalize rsegs mem) (wa p) v8 HMI0 ltac:(rewrite L8; exact HSO)) as HMI1.
  pose proof (Frame.munch_write [(p, p + 8)] (normalize rsegs mem) (normalize rsegs mem) p v8 (Frame.munch_refl _ _)
    ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia) ltac:(rewrite L8; cbn; lia)) as MU1.
  pose proof (Frame.wmono_write rsegs (normalize rsegs mem) (normalize rsegs mem) (wa p) v8 (Frame.wmono_refl _ _))
    as WM1.
  pose proof (Frame.stk_write rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g) p v8 HSTK0
    ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia)) as STK1.
  pose proof (Mem.bytes_at_write_same rsegs (normalize rsegs mem) p v8 ltac:(unfold p; lia)
    ltac:(rewrite L8; unfold p; lia)) as HN0.
  pose proof (Mem.wr_at_write rsegs (normalize rsegs mem) (g_S g - 65536) 65536 (wa p) v8 HWR0) as HWR1.
  pose proof (Mem.bytes_at_write_other rsegs (normalize rsegs mem) p v8 (g_S g - 368 + 48) _ HDPn
    ltac:(unfold p; lia) ltac:(rewrite L8; unfold p; lia) ltac:(rewrite LDP, L8; unfold p; lia)) as HDP1.
  remember (write_to_mem (normalize rsegs mem) (wa p) v8) as m1 eqn:Em1.
  step. step. step. step. step. step.
  eapply (pd_call PD) with (lo := g_S g - 16384) (b := g_S g - 368 + 48) (p := p) (v := t_out (g_in g)) (mn := 1)
    (N := Z_to_bv 64 (ld1 (g_in g) + 6));
    rewrite ?(MState.unsigned_lit (ld1 (g_in g) + 6)), ?(MState.unsigned_lit (g_S g - 368)) by lia;
    unfold PUT_DEC_FRAME, dec_len in *.
  all: try first
    [ reflexivity
    | exact HN0
    | apply ro_agree_inv; exact HMI1
    | eapply wr_sub; [exact HWR1 | unfold p; lia | unfold p; lia | lia]
    | rewrite MState.unsigned_lit by lia; apply Z.mod_small; lia
    | left; rewrite MState.unsigned_lit by lia; lia
    | unfold p; Z.div_mod_to_equations; lia
    | unfold p; lia
    | right; unfold p; lia
    | destruct (Frame.stk_split rsegs m1 (g_S g - 65536) (g_S g - 368) (g_S g) STK1 ltac:(lia)) as [X _];
      exact (proj2 (Frame.stk_split rsegs m1 (g_S g - 65536) (g_S g - 16384) (g_S g - 368) X ltac:(lia))) ].
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MF2 HRO2 HDEC HN.
  unfold PUT_DEC_FRAME, dec_len in *.
  retpc.
  pose proof MF2 as (MU2 & WM2 & _).
  lazymatch type of MU2 with Frame.munch ?W2 _ _ =>
    assert (MUa : Frame.munch W2 (normalize rsegs mem) m2)
      by (apply (Frame.munch_trans W2 _ m1 m2); [apply (Frame.munch_weaken [(p, p + 8)]); [subfp | exact MU1] |
          exact MU2]);
    assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) W2)
      by (repeat (apply Forall_cons; [cbn [fst snd]; unfold p; split; lia|]); apply Forall_nil);
    assert (D1 : disjoint_from W2 (spk g 130) 38) by (cbn; unfold spk, fsp, SLOT_FRAME, p; lia);
    assert (D2 : disjoint_from W2 (spk g 40) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, p; lia);
    assert (D3 : disjoint_from W2 (spk g 32) 8) by (cbn; unfold spk, fsp, SLOT_FRAME, p; lia);
    assert (D4 : disjoint_from W2 (spk g 226) (n_ln (g_in g) + 1)) by (cbn; unfold spk, fsp, SLOT_FRAME, p; lia);
    assert (D5 : disjoint_from W2 (g_S g - 368 + 48) (Z.of_nat (length (dp1 (g_in g) ++ s_in))))
      by (rewrite LDP; cbn; unfold p; lia)
  end.
  pose proof (mfr_bytes _ _ _ _ _ MF2 HDP1 D5) as HDP2.
  apply (fin_mem g mem regs 0x13a74 _ _ m2 (munch_SWIN g _ _ _ MUa FW) (Frame.wmono_trans _ _ _ _ WM1 WM2)
    (mfr_stk _ _ _ _ _ MF2 STK1)); [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM _ mem m') by exact (KM_of _ mem m2 m' HRO MUa HREL).
  assert (HO : OUTS g nm tk dp m')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m2 m' HFR HPM (munch_SWIN g _ _ _ MUa FW)
      HREL HOU).
  split.
  - unfold HBb. split; [|split; [|split]].
    + apply (NC_keep g nm tk dp regs mem R' m' _ HNC KMm HO D1 D2 D3 D4); rewrite HG; reflexivity.
    + rewrite HG. reflexivity.
    + rewrite HG. reflexivity.
    + apply (fin_bytes m' m2 _ _ HREL). unfold q64, spk, fsp, SLOT_FRAME.
      replace (ld2 (g_in g)) with (ld1 (g_in g) + 6 + Z.of_nat (length (DEC (t_out (g_in g)) 1))) by lia.
      exact HN.
  - apply (fin_bytes m' m2 _ _ HREL). unfold spk, fsp, SLOT_FRAME, dp2. rewrite app_assoc.
    apply (proj2 (Mem.bytes_at_app rsegs m2 _ _ _)). split; [exact HDP2|]. rewrite LDP. exact HDEC.
Qed.

End H13.
