From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
Import ListNotations.
Open Scope Z_scope.

Section Seg.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : lib.Reusable.YM05.RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.

Hypothesis sB01 : forall i, Hrec B APIf ra (Inv_U130fc_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13058_at B APIf ra empty) i.
Hypothesis sB02 : forall i, Hrec B APIf ra (Inv_U13124_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U130fc_at B APIf ra empty) i.
Hypothesis sB03 : forall i, Hrec B APIf ra (Inv_U13134_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13124_at B APIf ra empty) i.
Hypothesis sB04 : forall i, Hrec B APIf ra (Inv_U13148_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13134_at B APIf ra empty) i.
Hypothesis sB05 : forall i, Hrec B APIf ra (Inv_U1315c_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13148_at B APIf ra empty) i.
Hypothesis sB06 : forall i, Hrec B APIf ra (Inv_U13174_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U1315c_at B APIf ra empty) i.
Hypothesis sB07 : forall i, Hrec B APIf ra (Inv_U13198_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13174_at B APIf ra empty) i.
Hypothesis sB08 : forall i, Hrec B APIf ra (Inv_U131ac_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13198_at B APIf ra empty) i.
Hypothesis sB09 : forall i, Hrec B APIf ra (Inv_U131b8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U131ac_at B APIf ra empty) i.
Hypothesis sB10 : forall i, Hrec B APIf ra (Inv_U131ec_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U131b8_at B APIf ra empty) i.
Hypothesis sB11 : forall i, Hrec B APIf ra (Inv_U13230_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U131ec_at B APIf ra empty) i.
Hypothesis sB12 : forall i, Hrec B APIf ra (Inv_U133ac_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U135c0_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U1341c_at B APIf ra empty) i -> Hrec B APIf ra (fun g i c => Inv_U13270_at B APIf ra empty g i 0 c) i -> Hrec B APIf ra (Inv_U13230_at B APIf ra empty) i.
Hypothesis sB13 : forall i t, Hrec B APIf ra (Inv_U132a4_at B APIf ra empty) i -> Hrec B APIf ra (fun g i c => Inv_U13270_at B APIf ra empty g i t c) i.
Hypothesis sB14 : forall i, Hrec B APIf ra (Inv_U13304_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U132a4_at B APIf ra empty) i.
Hypothesis sB15 : forall i, Hrec B APIf ra (Inv_U13314_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13304_at B APIf ra empty) i.
Hypothesis sB16 : forall i, Hrec B APIf ra (Inv_U13660_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13314_at B APIf ra empty) i.
Hypothesis sB17 : forall i, Hrec B APIf ra (Inv_U133bc_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U133ac_at B APIf ra empty) i.
Hypothesis sB18 : forall i, Hrec B APIf ra (Inv_U13660_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U133bc_at B APIf ra empty) i.
Hypothesis sB19 : forall i, Hrec B APIf ra (Inv_U13438_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U1341c_at B APIf ra empty) i.
Hypothesis sB20 : forall i, Hrec B APIf ra (Inv_U134b4_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13438_at B APIf ra empty) i.
Hypothesis sB21 : forall i, Hrec B APIf ra (Inv_U134f4_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U134b4_at B APIf ra empty) i.
Hypothesis sB22 : forall i, Hrec B APIf ra (Inv_U13508_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U134f4_at B APIf ra empty) i.
Hypothesis sB23 : forall i, Hrec B APIf ra (Inv_U13540_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13508_at B APIf ra empty) i.
Hypothesis sB24 : forall i, Hrec B APIf ra (Inv_U13558_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13540_at B APIf ra empty) i.
Hypothesis sB25 : forall i, Hrec B APIf ra (Inv_U13660_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13558_at B APIf ra empty) i.
Hypothesis sB26 : forall i, Hrec B APIf ra (Inv_U135d0_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U135c0_at B APIf ra empty) i.
Hypothesis sB27 : forall i, Hrec B APIf ra (Inv_U13604_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U135d0_at B APIf ra empty) i.
Hypothesis sB28 : forall i, Hrec B APIf ra (Inv_U13660_at B APIf ra empty) i -> Hrec B APIf ra (Inv_U13604_at B APIf ra empty) i.
Hypothesis sB29 : forall i, Hrec B APIf ra (Inv_U13058_at B APIf ra empty) (S i) -> Hcut B APIf ra (Inv_U136a0 B APIf ra empty) -> Hrec B APIf ra (Inv_U13660_at B APIf ra empty) i.
Lemma b00_body : forall i,
  Hcut B APIf ra (Inv_U136a0 B APIf ra empty) ->
  Hrec B APIf ra (Inv_U13058_at B APIf ra empty) (S i) ->
  Hrec B APIf ra (Inv_U13058_at B APIf ra empty) i.
Proof.
  intros i HE HS.
  pose proof (sB29 i HS HE) as r1.
  pose proof (sB16 i r1) as r2.
  pose proof (sB18 i r1) as r3.
  pose proof (sB25 i r1) as r4.
  pose proof (sB28 i r1) as r5.
  pose proof (sB15 i r2) as r6.
  pose proof (sB17 i r3) as r7.
  pose proof (sB24 i r4) as r8.
  pose proof (sB27 i r5) as r9.
  pose proof (sB14 i r6) as r10.
  pose proof (sB23 i r8) as r11.
  pose proof (sB26 i r9) as r12.
  pose proof (sB13 i 0 r10) as r13.
  pose proof (sB22 i r11) as r14.
  pose proof (sB21 i r14) as r15.
  pose proof (sB20 i r15) as r16.
  pose proof (sB19 i r16) as r17.
  pose proof (sB12 i r7 r12 r17 r13) as r18.
  pose proof (sB11 i r18) as r19.
  pose proof (sB10 i r19) as r20.
  pose proof (sB09 i r20) as r21.
  pose proof (sB08 i r21) as r22.
  pose proof (sB07 i r22) as r23.
  pose proof (sB06 i r23) as r24.
  pose proof (sB05 i r24) as r25.
  pose proof (sB04 i r25) as r26.
  pose proof (sB03 i r26) as r27.
  pose proof (sB02 i r27) as r28.
  pose proof (sB01 i r28) as r29.
  exact r29.
Qed.

Lemma b00_rec_lt : forall g i c, Inv_U13058_at B APIf ra empty g i c -> Z.of_nat i < NR g.
Proof.
  intros g i c (L & A & regs & mem & md & _ & _ & _ & (HREC & _)).
  destruct HREC as [H _]. exact H.
Qed.

Lemma loop_records : Hcut B APIf ra (Inv_U136a0 B APIf ra empty) ->
  forall i, Hrec B APIf ra (Inv_U13058_at B APIf ra empty) i.
Proof.
  intros HE.
  assert (IND : forall k i, (64 - i <= k)%nat -> Hrec B APIf ra (Inv_U13058_at B APIf ra empty) i).
  { induction k as [|k IH]; intros i Hk.
    - intros g c Hc. exfalso. pose proof (b00_rec_lt g i c Hc) as Hlt.
      pose proof (nrec_range (g_in g)) as Hr. unfold NR in Hlt. lia.
    - destruct (Nat.le_gt_cases 64 i) as [Hi|Hi].
      + intros g c Hc. exfalso. pose proof (b00_rec_lt g i c Hc) as Hlt.
        pose proof (nrec_range (g_in g)) as Hr. unfold NR in Hlt. lia.
      + apply b00_body; [exact HE|]. apply IH. lia. }
  intro i. apply (IND (64 - i)%nat i). lia.
Qed.

End Seg.
