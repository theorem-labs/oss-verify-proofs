(* Composition W00 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): the row_of_block loop (W02 .. W04), by induction on
   11 - i. loop_rows : H(K13d80) -> H(K13d7c) -> H(K13d4c) for every row i.
   libreac v1.9.0: no instruction of its own; the cut names follow lib/Prog/SlotInv.v's renames (K13d50 -> K13d80,
   K13d4c -> K13d7c, K13d1c -> K13d4c, K13d3c -> K13d6c, K13d40 -> K13d70); the statements keep their v1.8 shape on
   the renamed cuts. rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv declaration_of_c bcmp_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import W02 W03 W04.
Import ListNotations.
Open Scope Z_scope.

Section W00.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis DECL : declaration_of_contract.
Hypothesis BCMPC : bcmp_ro_contract.

(* K13d4c holds only for i <= 10. *)
Lemma w00_out : forall j i, (10 < i)%nat -> Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i.
Proof.
  intros j i Hi g c (phi & L & A & regs & mem & md & _ & _ & _ & (_ & Hle & _)). lia.
Qed.

Lemma loop_rows : forall j : nat,
  Hat B APIf ra (Inv_K13d80_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13d7c_at B APIf ra empty) j ->
  forall i, Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i.
Proof.
  intros j Hd80 Hd7c.
  assert (K : forall k i, (11 - i <= k)%nat -> Hat2 B APIf ra (Inv_K13d4c_at B APIf ra empty) j i).
  { induction k as [|k IH]; intros i Hk.
    - apply w00_out. lia.
    - destruct (Nat.le_gt_cases i 10) as [Hi|Hi]; [|apply w00_out; lia].
      destruct (seg_W04 B APIf ra empty FF j i Hd80 (IH (S i) ltac:(lia)) Hd7c) as [Hd6c Hd70].
      exact (seg_W02 B APIf ra empty FF DECL j i (seg_W03 B APIf ra empty FF BCMPC j i Hd6c Hd70)). }
  intros i. exact (K (11 - i)%nat i ltac:(lia)).
Qed.

End W00.
