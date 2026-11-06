(* The slot's 48-operation loop, composed from its pieces at the SR level: the entry run (to the loop head of
   operation 0, to the exit, or straight to the end), one arm per operation (from the loop head of operation i
   to that of i + 1 or to the exit), and the exit run (to the end). Generic in the cut predicates, so the
   pieces' glue (LFr and the arm files) plugs in unchanged. The measure is 48 - i: an arm leaves the loop
   after operation 47 (`bltu s5, s11` with s5 = 46 at each arm's end). *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM06.
Local Open Scope Z_scope.

Section L.
Variable segs : list Segment.
Variables (ENT EX FIN : config -> Prop) (LH : Z -> config -> Prop).

Hypothesis ENTRY_OK : forall c, ENT c -> SR segs c (fun c' => LH 0 c' \/ EX c' \/ FIN c').
Hypothesis ARM_OK : forall i c, 0 <= i <= 47 -> LH i c ->
  SR segs c (fun c' => (i < 47 /\ LH (i + 1) c') \/ EX c').
Hypothesis EXIT_OK : forall c, EX c -> SR segs c FIN.

Lemma loop_to_exit : forall i c, 0 <= i <= 47 -> LH i c -> SR segs c EX.
Proof.
  intros i c Hi HL.
  refine (SR_loopZ segs Z (fun w => 48 - w) (fun w c => 0 <= w <= 47 /\ LH w c) EX _ i c (conj Hi HL)).
  intros w c0 [Hw HW]. eapply SR_mono; [exact (ARM_OK w c0 Hw HW)|].
  intros c' [[Hlt HN] | HX]; [right; exists (w + 1); split; [lia | split; [lia | exact HN]] | left; exact HX].
Qed.

Theorem slot_runs : forall c, ENT c -> SR segs c FIN.
Proof.
  intros c HE. eapply SR_bind; [exact (ENTRY_OK c HE)|].
  intros c' [HL | [HX | HF]].
  - eapply SR_bind; [exact (loop_to_exit 0 c' ltac:(lia) HL)|]. exact EXIT_OK.
  - exact (EXIT_OK c' HX).
  - exact (SR_ret segs c' FIN HF).
Qed.

End L.
