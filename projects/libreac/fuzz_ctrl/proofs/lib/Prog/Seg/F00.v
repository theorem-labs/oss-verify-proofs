(* Composition F00 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): the frame loop, by induction on 256 - j.
   loop_frames : H(K13db4) -> (the turn F01 .. C05 from K13694 to K13d98) -> H(K13694) for every j; C06 closes each
   turn. b8_tail composes batch b8's part of the turn: C05, C04, W00, W01 from H(K13d98).
   libreac v1.9.0: no instruction of its own; the cut names follow lib/Prog/SlotInv.v's renames (K1368c -> K13694,
   K13d80 -> K13db4, K13d68 -> K13d98, K13d5c -> K13d8c, K13d50 -> K13d80, K13d4c -> K13d7c, K13d1c -> K13d4c,
   K13d08 -> K13d38); the statements keep their v1.8 shape on the renamed cuts. rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv declaration_of_c bcmp_ro_c
  reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import C06 C05 C04 W00 W01.
Import ListNotations.
Open Scope Z_scope.

Section F00.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* K13694 holds only for j <= 255. *)
Lemma f00_out : forall j, (255 < j)%nat -> Hat B APIf ra (Inv_K13694_at B APIf ra empty) j.
Proof.
  intros j Hj g c (L & A & regs & mem & md & _ & _ & _ & (Hle & _)). lia.
Qed.

Lemma loop_frames : Hcut B APIf ra (Inv_K13db4 B APIf ra empty) ->
  (forall j : nat, Hat B APIf ra (Inv_K13d98_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13694_at B APIf ra empty) j) ->
  forall j : nat, Hat B APIf ra (Inv_K13694_at B APIf ra empty) j.
Proof.
  intros Hdb4 TURN.
  assert (K : forall k j, (256 - j <= k)%nat -> Hat B APIf ra (Inv_K13694_at B APIf ra empty) j).
  { induction k as [|k IH]; intros j Hk.
    - apply f00_out. lia.
    - destruct (Nat.le_gt_cases j 255) as [Hj|Hj]; [|apply f00_out; lia].
      apply TURN. exact (seg_C06 B APIf ra empty FF j (IH (S j) ltac:(lia)) Hdb4). }
  intros j. exact (K (256 - j)%nat j ltac:(lia)).
Qed.

Hypothesis FREE : free_contract B (APIf rc).
Hypothesis MATCH : reac_box_catalogue_match_contract.
Hypothesis DECL : declaration_of_contract.
Hypothesis BCMPC : bcmp_ro_contract.

Lemma b8_tail : forall j : nat, Hat B APIf ra (Inv_K13d98_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13d8c_at B APIf ra empty) j /\ Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j /\
  Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j /\
  (forall i : nat, Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i) /\
  Hat B APIf ra (Inv_K13d38_at B APIf ra empty) j.
Proof.
  intros j Hd98.
  pose proof (seg_C05 B APIf ra empty FF FREE j Hd98) as Hd8c.
  destruct (seg_C04 B APIf ra empty FF MATCH j Hd8c) as [Hd7c Hd80].
  pose proof (loop_rows B APIf ra empty FF DECL BCMPC j Hd80 Hd7c) as Hd4c.
  split; [exact Hd8c|]. split; [exact Hd80|]. split; [exact Hd7c|]. split; [exact Hd4c|].
  exact (seg_W01 B APIf ra empty FF j (Hd4c 0%nat) Hd80).
Qed.

End F00.
