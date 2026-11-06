(* Segment I02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13a14, 0x13a24], U13a14 -> U13a28
   (T23 on blk = Φ + 18 (s8; v1.8 s7) not taken by HBR; record_sum_closes (0x143a8) (blk + 16 = Φ + 34, pll_r + 5)
   on IR's record bytes Φ[34 .. 39 + pll_r): its premises a0 != 0 and a0 + a1 <= 2^64 from HBR; no stack, no
   memory written). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF record_sum_closes_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u4 Tac_u5.
Import ListNotations.
Open Scope Z_scope.

Lemma i02_evt : record_sum_closes_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi pll : Z) (bs : list byte),
    s8 = Z_to_bv 64 (phi + 18) -> a1 = Z_to_bv 64 pll ->
    4096 <= phi -> phi + 50 <= 2 ^ 63 -> 1 <= pll <= 10 ->
    length bs = Z.to_nat (pll + 5) -> bytes_at rsegs m (phi + 34) bs ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' a4' a5' a6' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13a28) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (if recsum bs =? 0 then 1 else 0)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13a28) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a14) fc None m (seg_rom rsegs)).
Proof.
  intros RSC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi pll bs Hs8 Ha1 Hphi Hphi50 Hpll Hlen HB.
  subst s8 a1.
  step. step. u5_br false.
  step. step. step.
  eapply evt_cut.
  { eapply RSC with (bs := bs).
    - u5_ul. match goal with |- length bs = Z.to_nat ?x => replace x with (pll + 5) by lia end. exact Hlen.
    - right. u5_ul. split; [lia|]. split; [lia|].
      match goal with |- bytes_at _ _ ?a _ => replace a with (phi + 34) by lia end. exact HB. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & E). subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13a28)) with (Z_to_bv 64 0x13a28)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists a1', a2', a3', a4', a5', a6'. reflexivity.
Qed.

Section I02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis RSC : record_sum_closes_contract.

Lemma seg_I02 : forall j : nat, Hat B APIf ra (Inv_U13a28_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13a14_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & Hir & HRPS & H11).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof HFB as ((HLK & (HS24 & H21 & H22) & H23 & Hphi & H18) & (H25 & H19 & H27 & H20 & (H24 & _ & _))).
  destruct (u5_ir_facts _ _ Hir) as (H50 & Hbig & Hsok & Hpll & _).
  pose proof (u4_phi_g _ _ _ _ (u5_norm mem phi _ HMI Hphi) H50) as HG.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ []);
    [exact HFR | exact HP | intros x Hx O; exfalso; apply O; exact I | | |].
  - rewrite sl_mkR_of.
    apply (i02_evt RSC) with (phi := phi) (pll := r_pll (t_g (g_in g) j))
      (bs := RcFrag.bsl (t_g (g_in g) j) 34 (r_pll (t_g (g_in g) j) + 5));
      [ | exact H11 | lia | lia | exact Hpll | | ].
    + unfold rg in H24. rewrite H24, Hbig. reflexivity.
    + apply u5_bsl_len; [lia | lia | rewrite u4_tg_len; lia].
    + apply (u5_ba_bsl _ phi _ 34 _ HG); [lia | lia | rewrite u4_tg_len; lia].
  - intros ms (? & ? & ? & ? & ? & ? & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & HE).
    injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj|].
    split; [apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj|].
    split; [exact Hir|].
    split; [apply (u5_RPS_keep g j phi mem m' _ HRPS MU'); u4_dj|].
    unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End I02.
