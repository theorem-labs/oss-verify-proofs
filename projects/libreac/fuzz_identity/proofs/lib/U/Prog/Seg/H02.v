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

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H02.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_c.put_dec_contract.

Lemma seg_H02 : Hcut B APIf ra (Inv_U13aac B APIf ra empty) -> Hcut B APIf ra (Inv_U13a98 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_U13aac. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HNB & E27 & E8 & HSTP & HQ216 & HDEC).
  pose proof HNB as (HID & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOU).
  destruct (wok_chans _ HW) as [Hi Ho].
  pose proof (DEC2_len _ Hi) as Li. pose proof (DEC2_len _ Ho) as Lo.
  pose proof (stem_addr_cases g) as HSA.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HQ216) as HQn. unfold q64, spk, fsp, SLOT_FRAME in HQn.
  unfold rmk, Frame.mkR. rewrite E2, E27.
  step. step. step. step. step.
  eapply (pd_call PD) with (lo := g_S g - 16384) (b := g_S g - 384 + 192) (p := g_S g - 384 + 216)
    (v := t_out (g_in g)) (mn := 2) (N := Z_to_bv 64 2);
    rewrite ?(MState.unsigned_lit 2), ?(MState.unsigned_lit (g_S g - 384)) by lia;
    unfold put_dec_c.PUT_DEC_FRAME, dec_len in *; rewrite ?Lo.
  all: try first
    [ reflexivity
    | exact HQn
    | apply ro_agree_inv; exact HMI0
    | eapply wr_sub; [exact HWR0 | lia | lia | lia]
    | rewrite MState.unsigned_lit by lia; apply Z.mod_small; lia
    | left; rewrite MState.unsigned_lit by lia; lia
    | Z.div_mod_to_equations; lia
    | lia
    | right; lia
    | destruct (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 384) (g_S g) HSTK0
        ltac:(lia)) as [X _];
      exact (proj2 (Frame.stk_split rsegs (normalize rsegs mem) (g_S g - 65536) (g_S g - 16384) (g_S g - 384) X
        ltac:(lia))) ].
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MF2 HRO2 HDEC2 HN.
  unfold put_dec_c.PUT_DEC_FRAME, dec_len in *. rewrite ?Lo in *.
  retpc.
  pose proof MF2 as (MU2 & WM2 & _).
  lazymatch type of MU2 with Frame.munch ?W2 _ _ =>
    assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) W2)
      by (repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil);
    assert (D1 : disjoint_from W2 (spk g 146) 38) by (cbn; unfold spk, fsp, SLOT_FRAME; lia);
    assert (D2 : disjoint_from W2 (spk g 56) 8) by (cbn; unfold spk, fsp, SLOT_FRAME; lia);
    assert (D3 : disjoint_from W2 (spk g 48) 8) by (cbn; unfold spk, fsp, SLOT_FRAME; lia);
    assert (D4 : disjoint_from W2 (spk g 24) 8) by (cbn; unfold spk, fsp, SLOT_FRAME; lia);
    assert (D5 : disjoint_from W2 (stem_addr g) (zlen (n_stem (g_in g)) + 1))
      by (cbn; unfold spk, fsp, SLOT_FRAME in *; lia);
    assert (D6 : disjoint_from W2 (spk g 192) (Z.of_nat (length (DEC (t_in (g_in g)) 2))))
      by (rewrite Li; cbn; unfold spk, fsp, SLOT_FRAME; lia)
  end.
  apply (fin_mem g mem regs 0x13aac _ _ m2 (munch_SWIN g _ _ _ MU2 FW) WM2 (mfr_stk _ _ _ _ _ MF2 HSTK0));
    [rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM _ mem m') by exact (KM_of _ mem m2 m' HRO MU2 HREL).
  assert (HO : OUTS g nm tk dp m')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m2 m' HFR HPM (munch_SWIN g _ _ _ MU2 FW)
      HREL HOU).
  split; [|split; [|split; [|split; [|split]]]].
  - apply (NB_keep g nm tk dp regs mem R' m' _ HNB KMm HO D1 D2 D3); kr HG.
  - kr HG.
  - kr HG.
  - exact (STP_keep g mem m' _ HSTP KMm D4 D5).
  - apply (fin_bytes m' m2 _ _ HREL). unfold q64, spk, fsp, SLOT_FRAME. exact HN.
  - unfold n_W4. apply (proj2 (Mem.bytes_at_app rsegs m' _ _ _)). split.
    + exact (KMm _ _ D6 HDEC).
    + apply (fin_bytes m' m2 _ _ HREL). rewrite Li. unfold spk, fsp, SLOT_FRAME. exact HDEC2.
Qed.

End H02.
