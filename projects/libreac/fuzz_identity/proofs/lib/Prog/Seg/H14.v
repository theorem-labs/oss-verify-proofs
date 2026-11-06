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
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Section H14.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_H14 : Hcut B APIf ra (Inv_K13a94 B APIf ra empty) -> Hcut B APIf ra (Inv_K13a74 B APIf ra empty).
Proof.
  intros HX g c (nm & tk & dp & HC).
  eapply (seg_go B APIf ra empty FF); [exact HX | | exact HC | ].
  { intros c' HC'. unfold Inv_K13a94, Inv_K13a94_at. exists 0, nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as (HBB & HDP).
  pose proof HBB as (HNC & E9 & E18 & HLD).
  pose proof (rd8 _ _ _ (bytes_at_normalize rsegs mem _ _ HRO HLD)) as RLD.
  unfold spk, fsp, SLOT_FRAME in RLD.
  pose proof E18 as E18'. unfold spk, fsp, SLOT_FRAME in E18'.
  unfold rmk, Frame.mkR. rewrite E2, E18'.
  step. step. step. step. step. step. step. step.
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
    - destruct HNC as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & HOU) & _). exact HOU. }
  
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - unfold HBb. split; [|split; [|split]].
    + apply (NC_keep g nm tk dp regs mem R' m' [] HNC KMm HO I I I I); rewrite HG; reflexivity.
    + rewrite HG. exact E9.
    + rewrite HG. unfold spk, fsp, SLOT_FRAME. reflexivity.
    + apply KMm; [exact I | exact HLD].
  - lia.
  - change (firstn (Z.to_nat 0) s_out) with (@nil byte). rewrite app_nil_r. apply KMm; [exact I | exact HDP].
  - rewrite HG; reflexivity.
  - rewrite HG; reflexivity.
  - rewrite HG; reflexivity.
  - rewrite HG; unfold spk, fsp, SLOT_FRAME; f_equal; lia.
  - rewrite HG; reflexivity.
  - rewrite HG; reflexivity.
Qed.

End H14.
