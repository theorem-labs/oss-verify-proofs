(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2004 of its 2120 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F30.v, with its module paths, module names and addresses changed; 91 of its 111 lines of code are new or changed and 2100 lines of the source are left out. *)
(* Segment R13 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): S_R13, Inv_A81924_at -> Inv_A81734_at, on the
   official cuts of aslot push 13 (Inv_A81734_at carries PRO, RXS and X81734: a0 = 1, s8 = phi, RB at the
   turn-(S b) records).
   0x81734 `li a1,1` and 0x81738 `beq a0,a1,8191c`: a0 is the reac_identity_ingest result 1, so the branch is taken
   and 0x8173c (`j 82bf4`, the abort pair) is NOT reached. At 0x8191c `mv a0,s8 ; jal wrapper_free` releases the
   harness buffer (phi, rnb g b): that run, the free contract and the rebuild of the official exit cut
   Inv_A81924_at (hb = []) are R15.r_free_cont (a working branch 7f03eba472d), which R15 / R16 /
   R20 use for the same call; RXS and PRO reach it by R15.r15_rxs_keep / R15.r15_pro_keep (the li / beq write
   only a1). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
Import ListNotations.
Open Scope Z_scope.

(* 0x81734 li a1,1 ; 0x81738 beq a0,a1,8191c (a0 = 1, so taken; only a1 changes). *)
Lemma r13_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 1 ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81734) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ->.
  step. step. if_true. apply evt_done. eexists. reflexivity.
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require BzBridge KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_rt_b2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R15.
(* Qualified, as in R15.v: `Require BzBridge KindBGlue` loads the image-independent lib/Reusable/YK11. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.

Section R13.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The li / beq run to 0x8191c (memory and the FRA / RB / spill registers unchanged), then R15.r_free_cont. *)
Lemma seg_R13 : forall b : nat,
  Hat B APIf ra (Inv_A81924_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A81734_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b Hexit g c HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hb6 & HHB & Hr23 & Hour & Hout & Hcur & Hs112 & Hs128 & HPRO & Hs104 & Hs96 & Hs64 & Hs144 & Hs208 &
     HRWid & HRWjk & Hs280 & Hs240 & HRWjy & HRWj32 & Hs152 & Hr21 & HAid & HRXS & Ha0 & Hr24 & HRB)).
  subst c.
  pose proof (proj1 FF) as SEGS.
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x81734) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x8191c /\ mem' = mem /\
       getr R 1 = getr regs 1 /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  { pose proof HFRA as HF2.
    destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _). exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    - apply r13_evt. exact Ha0.
    - intros ms' (a1' & ->). do 3 eexists. repeat (split; [reflexivity|]). reflexivity. }
  intros R pc' mem' regs'' md1
    (Hpc & Hmem & K1 & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26)
    Hreg Hmat.
  subst pc' mem'.
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
  assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
  assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem md1)
    by exact (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs regs'' mem md md1 HFRA E2 E3 E4 E8 E9 E19 E26 Hmat).
  assert (HENT'' : ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem md1).
  { eapply ent_mat; [exact HENT | exact Hmat]. }
  assert (HRB'' : RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs'' mem).
  { destruct HRB as (Rb6 & Rcur & Rour & Rr23 & Ridb & Rfgb).
    split; [exact Rb6|].
    split.
    { destruct Rcur as (Rc0 & Rc22 & Rc25). unfold CUR, rg in *.
      split; [exact Rc0|]. split; [rewrite E22; exact Rc22 | rewrite E25; exact Rc25]. }
    split; [exact Rour|].
    split; [unfold rg in *; rewrite E23; exact Rr23|].
    split; [exact Ridb | exact Rfgb]. }
  assert (Hr24'' : rg regs'' 24 phi) by (unfold rg in *; rewrite E24; exact Hr24).
  assert (KSP'' : forall off w, spill regs mem off w -> spill regs'' mem off w).
  { intros off w (A0 & HA0 & HQ). exists A0. split; [unfold rg in *; rewrite E9; exact HA0 | exact HQ]. }
  assert (Hr21'' : rg regs'' 21 (fr + 2176)) by (unfold rg in *; rewrite E21; exact Hr21).
  rewrite <- SEGS.
  exact (R15.r_free_cont B APIf ra empty FF b Hexit g regs'' mem md1 fr phi HFRA'' HENT'' Hgn HRB'' Hr24'' Hout
           (KSP'' 128 _ Hs128)
           (R15.r15_pro_keep g fr regs regs'' mem mem (fun off v _ H => KSP'' off v H) (fun H => H)
              (fun _ H => H) (fun _ H => H) HPRO)
           (KSP'' 104 _ Hs104) (KSP'' 96 _ Hs96) (KSP'' 64 _ Hs64)
           Hr21'' (KSP'' 112 _ Hs112) (KSP'' 144 _ Hs144) (KSP'' 192 _ Hs208) HRWid HRWjk
           (KSP'' 280 _ Hs280) (KSP'' 240 _ Hs240) HRWjy HRWj32 (KSP'' 152 _ Hs152)
           HAid
           (R15.r15_rxs_keep g fr regs regs'' mem mem (fun off v _ H => KSP'' off v H) (fun H => H) HRXS)).
Qed.

End R13.
