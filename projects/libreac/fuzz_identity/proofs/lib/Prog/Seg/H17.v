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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sh2 H17x.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H17.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_H17_af4 : Hcut B APIf ra (Inv_K13b18 B APIf ra empty) -> Hcut B APIf ra (Inv_K13af4 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_K13b18. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (H17 & HCN).
  pose proof H17 as (HNC & E9 & E18 & E8 & E27 & HDP).
  pose proof HNC as (HNB & E26 & E19 & HROW & HNM).
  pose proof HNB as (HID & HW & E20 & E21 & E22 & E23 & E24 & E25 & HCD & HOU).
  assert (Hr : n_r (g_in g) = -1).
  { destruct (nr_cases (g_in g)) as [H0|H0]; [|exact H0].
    destruct (nr0_fits (g_in g) H0) as (_ & H1 & _). lia. }
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HROW)) as RROW.
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HCD)) as RCD.
  unfold spk, fsp, SLOT_FRAME in RROW, RCD.
  unfold rmk, Frame.mkR. rewrite E2, E19, E25, Hr.
  step. step. step. step. step. step. step.
  if_true.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [apply Frame.munch_refl|]. split; [apply Frame.wmono_refl|].
  split; [exact HSTK0|].
  split; [rewrite E2; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros R' m' HG HREL. cbv beta.
  assert (KMm : KM [] mem m') by exact (KM_of [] mem (normalize rsegs mem) m' HRO (Frame.munch_refl _ _) HREL).
  assert (HO : OUTS g nm tk dp m').
  { apply (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md (normalize rsegs mem) m' HFR HPM).
    - apply (munch_SWIN g []); [apply Frame.munch_refl | constructor].
    - exact HREL.
    - exact HOU. }
  apply (IRb_mk g nm tk dp regs mem R' m' HNC KMm HO HDP E18); rewrite HG; try reflexivity.
  rewrite Hr. reflexivity.
Qed.

Lemma seg_H17 : Hcut B APIf ra (Inv_K13b18 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13ac8 B APIf ra empty) /\ Hcut B APIf ra (Inv_K13af4 B APIf ra empty).
Proof.
  intros HX. split; [eapply seg_H17_ac8; [exact FF | exact HX] | exact (seg_H17_af4 HX)].
Qed.

End H17.
