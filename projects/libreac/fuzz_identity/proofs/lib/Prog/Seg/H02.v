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

Section H02.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_contract.

Lemma seg_H02 : Hcut B APIf ra (Inv_K138d0 B APIf ra empty) -> Hcut B APIf ra (Inv_K138bc B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_K138d0. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct (s1_frame_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HLO & _ & _ & _ & _ & _ & _).
  unfold fsp, SLOT_FRAME in HLO.
  destruct HP as (HN0 & E19 & E8 & HQ200 & HQ168 & HDEC).
  pose proof HN0 as ((HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU) & E9 & E18 & HQ16 & HCS).
  destruct (wok_chans _ HW) as [Hi Ho].
  pose proof (DEC2_len _ Hi) as Li. pose proof (DEC2_len _ Ho) as Lo.
  pose proof (stem_addr_cases g) as HSA.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HQ200) as HQ200n. unfold q64, spk, fsp, SLOT_FRAME in HQ200n.
  unfold rmk, Frame.mkR. rewrite E2, E18.
  step. step. step. step. step.
  eapply (pd_call PD) with (lo := g_S g - 16384) (b := g_S g - 368 + 176) (p := g_S g - 368 + 200)
    (v := t_out (g_in g)) (mn := 2) (N := Z_to_bv 64 2);
    rewrite ?(MState.unsigned_lit 2), ?(MState.unsigned_lit (g_S g - 368)) by lia;
    unfold PUT_DEC_FRAME, dec_len in *; rewrite ?Lo.
  all: try first
    [ reflexivity
    | exact HQ200n
    | apply ro_agree_inv; exact HMI0
    | eapply wr_sub; [exact HWR0 | lia | lia | lia]
    | rewrite MState.unsigned_lit by lia; apply Z.mod_small; lia
    | left; rewrite MState.unsigned_lit by lia; lia
    | Z.div_mod_to_equations; lia
    | lia
    | right; lia
    | destruct (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 368) (g_S g) HSTK0
        ltac:(lia)) as [X _];
      exact (proj2 (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 16384) (g_S g - 368) X
        ltac:(lia))) ].
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MF2 HRO2 HDEC2 HN.
  unfold PUT_DEC_FRAME, dec_len in *. rewrite ?Lo in *.
  retpc.
  pose proof MF2 as (MU2 & WM2 & _).
  lazymatch type of MU2 with Frame.munch ?W2 _ _ =>
    assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) W2)
      by (repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil);
    assert (D1 : disjoint_from W2 (spk g 130) 38) by (cbn; unfold spk, fsp, SLOT_FRAME; lia);
    assert (D2 : disjoint_from W2 (spk g 40) 8) by (cbn; unfold spk, fsp, SLOT_FRAME; lia);
    assert (D3 : disjoint_from W2 (spk g 16) 8) by (cbn; unfold spk, fsp, SLOT_FRAME; lia);
    assert (D4 : disjoint_from W2 (stem_addr g) (zlen (n_stem (g_in g)) + 1))
      by (cbn; unfold spk, fsp, SLOT_FRAME in *; lia);
    assert (D5 : disjoint_from W2 (spk g 168) 8) by (cbn; unfold spk, fsp, SLOT_FRAME; lia);
    assert (D6 : disjoint_from W2 (spk g 176) (Z.of_nat (length (DEC (t_in (g_in g)) 2))))
      by (rewrite Li; cbn; unfold spk, fsp, SLOT_FRAME; lia)
  end.
  apply (fin_mem g mem regs 0x138d0 _ _ m2 (munch_SWIN g _ _ _ MU2 FW) WM2 (mfr_stk _ _ _ _ _ MF2 HSTK0));
    [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM _ mem m') by exact (KM_of _ mem m2 m' HRO MU2 HREL).
  assert (HO : OUTS g nm tk dp m')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m2 m' HFR HPM (munch_SWIN g _ _ _ MU2 FW)
      HREL HOU).
  split; [|split; [|split; [|split; [|split]]]].
  - apply (N0_keep g nm tk dp regs mem R' m' _ HN0 KMm HO D1 D2 D3 D4); rewrite HG;
      first [reflexivity | rewrite E18; reflexivity].
  - rewrite HG. exact E19.
  - rewrite HG. exact E8.
  - apply (fin_bytes m' m2 _ _ HREL). unfold q64, spk, fsp, SLOT_FRAME. exact HN.
  - unfold q64 in HQ168 |- *. apply (KMm _ _ ltac:(rewrite length_le8; exact D5) HQ168).
  - unfold n_W4. apply (proj2 (Mem.bytes_at_app rsegs m' _ _ _)). split.
    + exact (KMm _ _ D6 HDEC).
    + apply (fin_bytes m' m2 _ _ HREL). rewrite Li. unfold spk, fsp, SLOT_FRAME. exact HDEC2.
Qed.

End H02.
