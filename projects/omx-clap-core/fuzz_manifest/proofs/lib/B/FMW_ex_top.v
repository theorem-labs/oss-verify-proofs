(* G4, IMAGE B: expected_spec from the segments of lib/B/FMW_ex_base.v (B twin of lib/A/FMW_ex_top.v, 06d82004dc3): the scan's head by strong induction on |text| - i (fm plain
   expected_ml.v:983), then the entry. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YI04 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SEG_HEAD : ex_seg_head B.
Hypothesis SEG_P : ex_seg_P B.
Hypothesis SEG_ENTRY : ex_seg_entry B.

Theorem ex_seg_L_holds : ex_seg_L B.
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 H.
  remember (length (cx_tb cx) - i)%nat as m eqn:Hm.
  revert i d f ly3 S3 W3 regs3 mem3 md3 Hm H.
  induction m as [m IH] using lt_wf_ind.
  intros i d f ly3 S3 W3 regs3 mem3 md3 Hm H.
  pose proof H as (_ & _ & _ & _ & _ & (Hi & _) & _).
  apply (SEG_HEAD cx i d f ly3 S3 W3 regs3 mem3 md3); [|exact SEG_P|exact H].
  intros i' d' f' ly4 S4 W4 regs4 mem4 md4 Hlt H'.
  pose proof H' as (_ & _ & _ & _ & _ & (Hi' & _) & _).
  apply (IH (length (cx_tb cx) - i')%nat ltac:(lia) i' d' f' ly4 S4 W4 regs4 mem4 md4 eq_refl H').
Qed.

Theorem expected_spec_of_segs : expected_spec tfibsegs B.
Proof.
  unfold expected_spec.
  intros ly S W regs mem md ch t u tb ub live peak cnt fail HPRE HGL Ht Hu HCt HCu HKt HKu Hlen Hmax.
  set (cx := mkECX ly S W regs mem md ch t u tb ub live peak cnt fail).
  change (SRr tfibsegs (cx_W cx) (cfg_at tfibsegs A_expected (cx_regs cx) (cx_mem cx) (cx_md cx)) (ex_post B cx)).
  apply SEG_ENTRY.
  - exact (conj HPRE (conj HGL (conj Ht (conj Hu (conj HCt (conj HCu (conj HKt (conj HKu (conj Hlen Hmax))))))))).
  - intros ly3 S3 W3 regs3 mem3 md3 H. exact (ex_seg_L_holds cx 0%nat 0%nat _ ly3 S3 W3 regs3 mem3 md3 H).
Qed.
End W.

Print Assumptions expected_spec_of_segs.
