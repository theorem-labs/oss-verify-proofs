(* Walk of check_parse_refusal (fuzz/fuzz_frame.c:34-63 at 835f336c) in fuzz_frame.plain,
   0x12ea4..0x12eec. r (a0) and w->code (the word at a1) are both fr_code b, one of 0, -2, -3,
   -4 (DgnSpec.fr_code_cases). For each of the four values the eight tests at
   0x12eb4..0x12ed8 are closed terms, and none of them branches to abort at 0x12ee8.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import check_parse_refusal_c.
Import ListNotations.
Open Scope Z_scope.

(* Decide a branch whose condition is a closed term. *)
Ltac brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

Theorem check_parse_refusal_holds : check_parse_refusal_contract.
Proof.
  unfold check_parse_refusal_contract, CHECK_PARSE_REFUSAL, CPR_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m w lo b
    RO DW ST LO MI.
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  destruct (fr_code_cases b) as [E|[E|[E|E]]]; rewrite E in *.
  all: do 3 step.
  all: repeat first [ brc | step ].
  all: release_frame FR ST (bv_unsigned sp).
  all: apply evt_done; do 16 eexists; split; [reflexivity|].
  all: refine (conj _ (conj _ (conj _ _))); eassumption.
Qed.
