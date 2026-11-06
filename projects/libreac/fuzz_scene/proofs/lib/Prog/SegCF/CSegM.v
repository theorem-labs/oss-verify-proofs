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
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.SegCF Require Import CInv CTac.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog.Seg Require Import SInv STac SGlue SCut.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* Segment M: 0x151dc `mv a0,s2; jal malloc` allocates before (nb bytes, ra 0x151e4). *)

Section KA.
Context {fx : YK11.FPState}.

Lemma M_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = Frame.mkR (Z_to_bv 64 0x151e4) x2 x3 x4 x5 x6 x7 x8 x9 x18 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 /\
       pc' = Z_to_bv 64 0x16698 /\ m' = m)
    (MS (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
             x27 x28 x29 x30 x31)
        fp_regs (Z_to_bv 64 0x151dc) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m.
  step. step.
  apply evt_done. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

End KA.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MALLOC : malloc_contract_cf B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).

Lemma seg_M_cf : Hcut_cf B APIf ra (Inv_K151e4 B APIf ra empty) -> Hcut_cf B APIf ra (Inv_K151dc B APIf ra empty).
Proof.
  intros HX g c HCAP (body & km & Hkm & HC).
  eapply (cut_open_cf B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (H9 & H18 & H24 & HB & HM).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ HF)) as [Hh Hl].
  pose proof (ss_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (_ & _ & _ & HfS & _ & HS47 & _ & Hsp).
  pose proof (nbG_range g) as Hnb.
  eapply (ss_kA_run0_cf B APIf ra empty FF regs (Z_to_bv 64 0x151dc) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of. apply M_x. }
  intros R pc' m' regs1 (-> & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by ss_kp XR regs.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x151e4) by (rewrite (ss_getr_x _ _ 1 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (nbG g)).
  { transitivity (getr regs 18); [|exact H18].
    rewrite (ss_getr_x _ _ 10 XR) by reflexivity. rewrite (ss_getr_reg regs 18) by reflexivity. reflexivity. }
  assert (HF1 : FR B APIf ra empty g km [(body, nbG g)] L A regs1 mem md).
  { apply (ss_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply ss_wmono_eq. intros w. reflexivity. }
  rewrite <- (ss_malloc_pc B APIf ra empty FF).
  apply (ss_malloc_step_cf B APIf ra empty FF MALLOC LIMLAW g HCAP km [(body, nbG g)] L A regs1 mem md (nbG g) _ HF1 HP).
  - cbn. lia.
  - unfold hb_bytes. cbn. lia.
  - lia.
  - rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
  - exact G10.
  - intros L' A' regs2 mem2 md2 res HF2 HP2 RP2 R10 Hr0 FRM2 HBM2.
    rewrite G1. apply HX; [exact HCAP|]. exists body, res, (km + 1). split; [lia|].
    exists L', A', regs2, mem2, md2. split; [reflexivity|]. split; [exact HF2|]. split; [exact HP2|].
    assert (CS : CSeq regs regs2) by (apply (ss_CSeq_trans _ regs1); [exact (ss_KP_CSeq regs regs1 KP1) | exact RP2]).
    split; [exact R10|].
    split; [ss_cs CS 9; exact H9|].
    split; [ss_cs CS 24; exact H24|].
    split.
    + destruct HB as (bb & Hbb & HBB). exists bb. split; [exact Hbb|].
      apply (ss_bytes_mbyte rsegs mem mem2); [|exact HBB].
      intros i Hi. rewrite <- (ss_segs B APIf ra empty FF). apply (HBM2 body (nbG g) i); [left; reflexivity | lia].
    + destruct HM as (macb & Hlen & HMB). exists macb. split; [exact Hlen|].
      apply (ss_bytes_mbyte rsegs mem mem2); [|exact HMB].
      intros i Hi. rewrite <- (ss_segs B APIf ra empty FF). apply FRM2.
      rewrite Hlen in Hi. unfold fsp, SLOT_FRAME. lia.
Qed.

End M.
