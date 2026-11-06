(* Segment R12 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13420, 0x13424], K13420 -> K13514
   (#11 not taken: the ingest returned 1; break to the free). libreac v1.9.0: 0x13420 `bne a0,s8` (the 1 of RT
   in s8; v1.8 s9). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

Lemma r12_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 1 -> s8 = Z_to_bv 64 1 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13514) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13420) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m -> ->.
  step. if_false. step.
  apply evt_done. reflexivity.
Qed.

Section R12.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R12 : forall b, Hat B APIf ra (Inv_K13514_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_K13420_at B APIf ra empty) b.
Proof.
  intros b H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & Hb & H10).
  pose proof HRF as ((HRB & Hnz & H20 & HF) & H22).
  pose proof HRB as (_ & _ & _ & (_ & _ & _ & _ & H24 & _) & _).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  destruct (b1_RS_len (g_in g) (S b)) as (LI & LF).
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of. apply r12_evt; [exact H10 | exact H24].
  - intros ms ->. do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x _ O. exfalso. apply O. exact I.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    injection HQ; intros; subst.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (KR : b1_kr regs' regs).
    { unfold b1_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    split; [exact (b1_RB_keep g b _ _ regs regs' mem (normalize rsegs mem) m' [] HMI (munch_refl _ _) Hrel
                     LI LF I KR HRB)|].
    split; [exact Hnz|]. unfold rg in *. rewrite (sl_getr_eqv _ _ _ Hx). exact H20.
Qed.

End R12.
