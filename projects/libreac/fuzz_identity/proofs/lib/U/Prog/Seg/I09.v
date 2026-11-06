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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU strlen_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.


Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section I09.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma seg_I09 : Hcut B APIf ra (Inv_U13e08 B APIf ra empty) -> Hcut B APIf ra (Inv_U13dec B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. exists 0%nat, nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM ((HI & R0) & E10).
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  pose proof HI as (HID & E9 & HQ56 & HQ48 & E20 & E21 & E22 & E23 & E24 & E25 & E19 & HO & HE).
  destruct (nmb_in _ _ _ _ _ _ HPM) as (N1 & N2 & N3).
  destruct (FR_parts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (_ & _ & _ & _ & HMR & _).
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N1) as [BN1 BN2].
  pose proof (blk_range B APIf _ _ _ _ _ _ HMR N2) as [BT1 BT2].
  pose proof YM05.alloc_ceiling_value as [AC1 AC2].
  pose proof (Tac_si.caps_range (g_in g)) as CR. unfold bsz in BN2, BT2.
  unfold rmk, Frame.mkR. rewrite E2, E10, E20, E21.
  step. br_if.
  step. step. step. step. step. step.
  rewrite ?not_lit by lia.
  apply fin_nomem; [exact HSTK0 | rewrite E2; reflexivity | reflexivity | reflexivity |].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM [] mem m') by exact (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL).
  assert (HO' : OUTS g nm tk dp m')
    by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM
      (munch_SWIN g [] _ _ (Frame.munch_refl _ _) (Forall_nil _)) HREL HO).
  split; [split; [|exact R0]|].
  - apply (IRb_keep g nm tk dp regs mem R' m' [] HI KMm HO' I I I I I); kr HG.
  - split; [lia|].
    split; [rewrite HG; greg2; unfold dropped; reflexivity|].
    split; [rewrite HG; greg2; reflexivity|].
    split; [rewrite HG; greg2; unfold dropped; reflexivity|].
    split; [rg HG|]. split; [rg HG|]. split; [rg HG|]. rg HG.
Qed.

End I09.
