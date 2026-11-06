From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sef.
Import ListNotations.
Open Scope Z_scope.

Section KA.
Context {fx : YK11.FPState}.

Lemma E07_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (cap : Z),
  x21 = Z_to_bv 64 cap -> 0 <= cap < 32 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = mkR (Z_to_bv 64 0x135fc) x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (bsz cap)) x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 /\
       pc' = Z_to_bv 64 0x15580 /\ m' = m)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x135f0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m cap E21 Hc.
  subst x21.
  step. step. step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [|split; reflexivity]. rewrite sf_bsz_seqz by lia. reflexivity.
Qed.

End KA.

Section E07.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_E07 : Hcut B APIf ra (Inv_K135fc B APIf ra empty) -> Hcut B APIf ra (Inv_K135f0 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HD).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & _).
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HD as (HTID & HTL & H21 & H20).
  assert (Hcap : 0 <= t_cap_ver (g_in g) < 32) by (unfold t_cap_ver; apply Z.mod_pos_bound; lia).
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x135f0) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of. apply E07_x; [rewrite <- (sf_getr_reg regs 21) by reflexivity; exact H21 | exact Hcap]. }
  intros R pc' m' regs1 (-> & -> & ->) XR.
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by sf_kp XR regs.
  pose proof (sf_KP_CSeq regs regs1 KP1) as CS1.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x135fc) by (rewrite (sf_getr_x _ _ 1 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (bsz (t_cap_ver (g_in g))))
    by (rewrite (sf_getr_x _ _ 10 XR) by reflexivity; reflexivity).
  assert (HF1 : FR B APIf ra empty g (2 * NR g + 1) [] L A regs1 mem md).
  { apply (sf_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply sf_wmono_eq. intros w. reflexivity. }
  rewrite <- (sf_malloc_pc B APIf ra empty FF).
  apply (sf_malloc_step B APIf ra empty FF g (2 * NR g + 1) [] L A regs1 mem md (bsz (t_cap_ver (g_in g))) _
    HF1 HP).
  - cbn [Datatypes.length]. lia.
  - unfold hb_bytes. cbn. lia.
  - unfold bsz. lia.
  - rewrite G1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
  - exact G10.
  - intros L' A' regs2 mem2 md2 res HF2 HP2 RP2 R10 Hr0 FRM2 _.
    rewrite G1.
    replace (2 * NR g + 1 + 1) with (2 * NR g + 2) in HF2 by lia.
    apply HX. exists res, L', A', regs2, mem2, md2. split; [reflexivity|].
    split; [exact HF2|]. split; [exact HP2|].
    assert (CS : CSeq regs regs2) by (apply (sf_CSeq_trans _ regs1); [exact CS1 | exact RP2]).
    assert (FRe : FReq g mem mem2) by (intros x Hx; rewrite <- SEG; exact (FRM2 x Hx)).
    split; [|exact R10].
    split; [exact (sf_TID_tr g mem mem2 FRe HTID)|].
    split; [exact (sf_TL_tr g regs regs2 mem mem2 CS FRe HTL)|].
    split; [sf_cs CS 21; exact H21 | sf_cs CS 20; exact H20].
Qed.

End E07.
