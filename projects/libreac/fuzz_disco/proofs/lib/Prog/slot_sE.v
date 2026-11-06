From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0o YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_norm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_exit slot_R0_R3 slot_seg slot_preds.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_cells.
Import ListNotations.
Open Scope Z_scope.

Definition W_E1 (X : Z) : list (Z * Z) := [(X + 2488, X + 2592); (X + 914, X + 920)].

Lemma seg_E1 : forall X d pl regs0, xok X -> dok X d pl ->
  seg_ev ENTRY_PC (W_E1 X) (fun R m => P_ENT X d pl regs0 R m /\ fenv X [] m)
    (fun q R m => (q = MALLOC_AT /\ P_MAL0 X d pl regs0 R m) \/
                  (q = bv_unsigned (ret_pc (getr regs0 1)) /\ P_RET regs0 R m)).
Proof.
  intros X d pl regs0 HX HD fx' regs m0 Hf HI ((EQ & E02 & E010 & E011 & E04 & BD) & (STK & _)).
  pose proof (mem_inv_of_cj m0 HI) as MI.
  unfold xok, dok, LO, SLOT_FRAME, SLOT_STACK, IMG_HI in *.
  destruct HX as (HX0 & HX16 & HX1 & HXlo). destruct HD as (Hd0 & Hd1 & Hd2 & _).
  set (n := Z.of_nat (length pl)) in *.
  assert (G2 : getr regs 2 = Z_to_bv 64 (X + 2592)) by (rewrite EQ; exact E02).
  assert (G10 : getr regs 10 = Z_to_bv 64 d) by (rewrite EQ; exact E010).
  assert (G11 : getr regs 11 = Z_to_bv 64 n) by (rewrite EQ; exact E011).
  destruct (stk_cb m0 _ _ (X + 2488) 104 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jsv SV0].
  destruct (stk_cb m0 _ _ (X + 914) 6 STK ltac:(unfold IMG_HI; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [jour OU0].
  pose proof (munch_refl (W_E1 X) m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold W_E1 in MU.
  clear STK.
  unfold rmk. eapply evt_cut.
  { eapply (slot_R0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 X n jsv G2 G11);
      [lia | lia | lia | exact SV0 | exact MI]. }
  intros ms (m1 & -> & MU1 & WM1 & MI1 & SV1).
  transport_after_call rsegs m0 m1 MU1 WM1. clear MU1 WM1.
  destruct (Z.ltb_spec n (2 ^ 26)) as [Hn|Hn].
  - eapply evt_cut.
    { eapply (slot_R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 X d n pl jour);
        [reflexivity | exact G10 | exact G11 | lia | lia | lia | reflexivity | lia | lia | lia | eassumption |
         eassumption | exact MI1]. }
    intros ms (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & MU2 & WM2 & MI2 & OU2 & BD2).
    transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2.
    apply evt_done. do 2 eexists. exists MALLOC_AT. do 2 eexists.
    split; [reflexivity|]. split; [exact Hf|]. split; [unfold W_E1; exact MU|]. split; [exact WM|].
    left. split; [reflexivity|]. unfold P_MAL0.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact (EQ _)|].
    split; [exact (eq_trans (EQ _) E04)|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold saved_of; rewrite <- !EQ; exact SV1|]. split; eassumption.
  - eapply evt_mono.
    { eapply (slot_R29_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 X);
        [reflexivity | lia | lia | exact SV1]. }
    intros ms ->. do 2 eexists. exists (bv_unsigned (ret_pc (getr regs0 1))). do 2 eexists.
    split; [rewrite Z_to_bv_bv_unsigned, <- EQ; reflexivity|].
    split; [exact Hf|]. split; [unfold W_E1; exact MU|]. split; [exact WM|].
    right. split; [reflexivity|]. split; [|reflexivity].
    intros r Hr. unfold callee_saved in Hr.
    destruct Hr as [->|[->|[->|[->|[->|Hr]]]]];
      [symmetry; exact E02 | exact (EQ _) | exact (EQ _) | exact (EQ _) | exact (EQ _) |].
    assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; exact (EQ _).
Qed.
