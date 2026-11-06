From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
Import ListNotations.
Open Scope Z_scope.

Section Seg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.

Hypothesis sB01 : forall i,
  Hrec B APIf ra (Inv_K13068_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) i.
Hypothesis sB02 : forall i,
  Hrec B APIf ra (Inv_K13088_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13068_at B APIf ra empty) i.
Hypothesis sB03 : forall i,
  Hrec B APIf ra (Inv_K13098_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13088_at B APIf ra empty) i.
Hypothesis sB04 : forall i,
  Hrec B APIf ra (Inv_K130ac_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13098_at B APIf ra empty) i.
Hypothesis sB05 : forall i,
  Hrec B APIf ra (Inv_K130bc_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K130ac_at B APIf ra empty) i.
Hypothesis sB06 : forall i,
  Hrec B APIf ra (Inv_K130dc_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K130bc_at B APIf ra empty) i.
Hypothesis sB07 : forall i,
  Hrec B APIf ra (Inv_K130f8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K130dc_at B APIf ra empty) i.
Hypothesis sB08 : forall i,
  Hrec B APIf ra (Inv_K1310c_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K130f8_at B APIf ra empty) i.
Hypothesis sB09 : forall i,
  Hrec B APIf ra (Inv_K13118_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K1310c_at B APIf ra empty) i.
Hypothesis sB10 : forall i,
  Hrec B APIf ra (Inv_K13144_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13118_at B APIf ra empty) i.
Hypothesis sB11 : forall i,
  Hrec B APIf ra (Inv_K13188_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13144_at B APIf ra empty) i.
Hypothesis sB12 : forall i,
  Hrec B APIf ra (Inv_K1328c_at B APIf ra empty) i ->
  Hrec B APIf ra (Inv_K13440_at B APIf ra empty) i ->
  Hrec B APIf ra (Inv_K132d8_at B APIf ra empty) i ->
  Hrec B APIf ra (fun g i c => Inv_K131c8_at B APIf ra empty g i 0 c) i ->
  Hrec B APIf ra (Inv_K13188_at B APIf ra empty) i.
Hypothesis sB13 : forall i t,
  Hrec B APIf ra (Inv_K131dc_at B APIf ra empty) i ->
  Hrec B APIf ra (fun g i c => Inv_K131c8_at B APIf ra empty g i t c) i.
Hypothesis sB14 : forall i,
  Hrec B APIf ra (Inv_K13220_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K131dc_at B APIf ra empty) i.
Hypothesis sB15 : forall i,
  Hrec B APIf ra (Inv_K13230_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13220_at B APIf ra empty) i.
Hypothesis sB16 : forall i,
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13230_at B APIf ra empty) i.
Hypothesis sB17 : forall i,
  Hrec B APIf ra (Inv_K1329c_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K1328c_at B APIf ra empty) i.
Hypothesis sB18 : forall i,
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K1329c_at B APIf ra empty) i.
Hypothesis sB19 : forall i,
  Hrec B APIf ra (Inv_K132f4_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K132d8_at B APIf ra empty) i.
Hypothesis sB20 : forall i,
  Hrec B APIf ra (Inv_K1334c_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K132f4_at B APIf ra empty) i.
Hypothesis sB21 : forall i,
  Hrec B APIf ra (Inv_K1337c_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K1334c_at B APIf ra empty) i.
Hypothesis sB22 : forall i,
  Hrec B APIf ra (Inv_K13390_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K1337c_at B APIf ra empty) i.
Hypothesis sB23 : forall i,
  Hrec B APIf ra (Inv_K133b4_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13390_at B APIf ra empty) i.
Hypothesis sB24 : forall i,
  Hrec B APIf ra (Inv_K133d0_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K133b4_at B APIf ra empty) i.
Hypothesis sB25 : forall i,
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K133d0_at B APIf ra empty) i.
Hypothesis sB26 : forall i,
  Hrec B APIf ra (Inv_K13454_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13440_at B APIf ra empty) i.
Hypothesis sB27 : forall i,
  Hrec B APIf ra (Inv_K13480_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13454_at B APIf ra empty) i.
Hypothesis sB28 : forall i,
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i -> Hrec B APIf ra (Inv_K13480_at B APIf ra empty) i.
Hypothesis sB29 : forall i,
  Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) (S i) -> Hcut B APIf ra (Inv_K134e4 B APIf ra empty) ->
  Hrec B APIf ra (Inv_K134c8_at B APIf ra empty) i.

Lemma b00_rec_lt : forall g i c, Inv_K12fc4_at B APIf ra empty g i c -> Z.of_nat i < NR g.
Proof.
  intros g i c (L & A & regs & mem & md & _ & _ & _ & (HREC & _)).
  destruct HREC as [H _]. exact H.
Qed.

Lemma b00_body : forall i,
  Hcut B APIf ra (Inv_K134e4 B APIf ra empty) ->
  Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) (S i) ->
  Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) i.
Proof.
  intros i HE HS.
  pose proof (sB29 i HS HE) as h134c8.
  pose proof (sB28 i h134c8) as h13480.
  pose proof (sB27 i h13480) as h13454.
  pose proof (sB26 i h13454) as h13440.
  pose proof (sB25 i h134c8) as h133d0.
  pose proof (sB24 i h133d0) as h133b4.
  pose proof (sB23 i h133b4) as h13390.
  pose proof (sB22 i h13390) as h1337c.
  pose proof (sB21 i h1337c) as h1334c.
  pose proof (sB20 i h1334c) as h132f4.
  pose proof (sB19 i h132f4) as h132d8.
  pose proof (sB18 i h134c8) as h1329c.
  pose proof (sB17 i h1329c) as h1328c.
  pose proof (sB16 i h134c8) as h13230.
  pose proof (sB15 i h13230) as h13220.
  pose proof (sB14 i h13220) as h131dc.
  pose proof (sB13 i 0 h131dc) as h131c8.
  pose proof (sB12 i h1328c h13440 h132d8 h131c8) as h13188.
  pose proof (sB11 i h13188) as h13144.
  pose proof (sB10 i h13144) as h13118.
  pose proof (sB09 i h13118) as h1310c.
  pose proof (sB08 i h1310c) as h130f8.
  pose proof (sB07 i h130f8) as h130dc.
  pose proof (sB06 i h130dc) as h130bc.
  pose proof (sB05 i h130bc) as h130ac.
  pose proof (sB04 i h130ac) as h13098.
  pose proof (sB03 i h13098) as h13088.
  pose proof (sB02 i h13088) as h13068.
  exact (sB01 i h13068).
Qed.

Lemma loop_records : Hcut B APIf ra (Inv_K134e4 B APIf ra empty) ->
  forall i, Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) i.
Proof.
  intros HE.
  assert (IND : forall k i, (64 - i <= k)%nat -> Hrec B APIf ra (Inv_K12fc4_at B APIf ra empty) i).
  { induction k as [|k IH]; intros i Hk.
    - intros g c Hc. exfalso. pose proof (b00_rec_lt g i c Hc) as Hlt.
      pose proof (nrec_range (g_in g)) as Hr. unfold NR in Hlt. lia.
    - destruct (Nat.le_gt_cases 64 i) as [Hi|Hi].
      + intros g c Hc. exfalso. pose proof (b00_rec_lt g i c Hc) as Hlt.
        pose proof (nrec_range (g_in g)) as Hr. unfold NR in Hlt. lia.
      + apply b00_body; [exact HE|]. apply IH. lia. }
  intro i. apply (IND (64 - i)%nat i). lia.
Qed.

Lemma seg_B00 : Hcut B APIf ra (Inv_K134e4 B APIf ra empty) -> Hcut B APIf ra (Inv_K12fc4 B APIf ra empty).
Proof.
  intros HE g c [i Hc]. exact (loop_records HE i g c Hc).
Qed.

End Seg.
