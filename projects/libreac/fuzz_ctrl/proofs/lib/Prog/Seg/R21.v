(* Segment R21 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13514, 0x13518], K13514 -> K1351c (turn b):
   free of the round trip's frame block (Kind B, malloc/free from frame_facts' frame_allocator). libreac v1.9.0:
   free at 0x1635c (frame_facts ms_free). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b3.
Import ListNotations.
Open Scope Z_scope.

Lemma r21_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1351c) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x1635c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13514) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. step. apply evt_done. reflexivity.
Qed.

Section R21.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_R21 : forall b, Hat B APIf ra (Inv_K1351c_at B APIf ra empty) b ->
  Hat B APIf ra (Inv_K13514_at B APIf ra empty) b.
Proof.
  intros b H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRB & Hn & H20).
  pose proof (b3_rnb_pos g b Hn) as Hn1.
  pose proof (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (_ & _ & HSK & HS47 & _).
  assert (Hin : In (phi, rnb g b) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b3_in_blocks L A _ _ Hin) as (p & Hp & Ep).
  eapply (b3_mid B APIf ra empty FF g (hb1 phi (rnb g b)) L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (b3_fp g _ x _ Hx O). apply Forall_nil.
  - rewrite sl_mkR_of. apply r21_evt.
  - intros ms ->.
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs_c m1 HQ Hx Hrel MU' HFR'.
    injection HQ as E1 E2 E3. subst R pc' m0'.
    apply (b3_free_call B APIf ra empty FF g [] [] L A regs_c m1 md regs_c p (rnb g b)).
    + rewrite Ep. exact HFR'.
    + rewrite Ep. exact HP.
    + exact Hp.
    + exact Hn1.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite (sl_getr_eqv _ _ _ Hx). apply YK0s.ret_ok_even. vm_compute. reflexivity.
    + rewrite (sl_getr_eqv _ _ _ Hx). rewrite Ep. exact H20.
    + intros L' A' regs' mem' md' HF' HP' RP' HK.
      replace (getr regs_c 1) with (Z_to_bv 64 0x1351c) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      apply H. exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact HF'|]. split; [exact HP'|].
      destruct (b3_RB_bytes g b _ _ regs mem m1 [] HRB MU' I I I) as (B1 & B2 & B3).
      unfold spk, fsp, SLOT_FRAME in B1, B2, B3.
      apply (b3_RB g b _ _ regs mem regs' mem' HRB);
        [ b3_rp RP' Hx 8 | b3_rp RP' Hx 9 | b3_rp RP' Hx 18 | b3_rp RP' Hx 19 | b3_rp RP' Hx 21 | b3_rp RP' Hx 23
        | b3_rp RP' Hx 24 | b3_rp RP' Hx 25 | b3_rp RP' Hx 26 | b3_rp RP' Hx 27 | | | ];
        unfold spk, fsp, SLOT_FRAME; (eapply b3_ba_hi; [eassumption | | exact HK]); lia.
Qed.

End R21.
