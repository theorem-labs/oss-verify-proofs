From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg Require Import SInv STac SGlue SCut.
Import ListNotations.
Open Scope Z_scope.

(* Segment F: 0x15340 `mv a0,s1; jal free` frees body (ra 0x15348). *)

Section KA.
Context {fx : YK11.FPState}.

Lemma F_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = Frame.mkR (Z_to_bv 64 0x15348) x2 x3 x4 x5 x6 x7 x8 x9 x9 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 /\
       pc' = Z_to_bv 64 0x16558 /\ m' = m)
    (MS (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        fp_regs (Z_to_bv 64 0x15340) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m.
  step. step.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

End KA.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FREE : free_contract B (APIf rc).

Lemma seg_F : Hcut B APIf ra (Inv_K15348 B APIf ra empty) -> Hcut B APIf ra (Inv_K15340 B APIf ra empty).
Proof.
  intros HX g c (body & km & HC).
  eapply (cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP H9.
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ HF)) as [Hh Hl].
  eapply (ss_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x15340) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of. apply F_x. }
  intros R pc' m' regs1 (-> & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by ss_kp XR regs.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x15348) by (rewrite (ss_getr_x _ _ 1 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 body).
  { transitivity (getr regs 9); [|exact H9].
    rewrite (ss_getr_x _ _ 10 XR) by reflexivity. rewrite (ss_getr_reg regs 9) by reflexivity. reflexivity. }
  assert (HF1 : FR B APIf ra empty g km [(body, nbG g)] L A regs1 mem md).
  { apply (ss_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply ss_wmono_eq. intros w. reflexivity. }
  rewrite <- (ss_free_pc B APIf ra empty FF).
  apply (ss_free_step B APIf ra empty FF FREE g km [] body (nbG g) [] L A regs1 mem md _ HF1 HP).
  - pose proof (nbG_range g). unfold MMAP_THRESHOLD. lia.
  - rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
  - exact G10.
  - intros L' A' regs2 mem2 md2 HF2 HP2 RP2 FRM2.
    rewrite G1. apply HX. exists km, L', A', regs2, mem2, md2. split; [reflexivity|].
    split; [exact HF2|]. split; [exact HP2 | exact I].
Qed.

End F.
