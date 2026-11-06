(* Segment G05 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13af0, 0x13b00], U13af0 (v1.8
   U13af8, a Theorem Labs lane's table section 8 anchor) -> U13b04 (v1.8 U13b10) (T27 `li a0,-8; bltu a0,s0` on
   buf = s0 = sp+128 not taken by SR (v1.8 recomputed buf = sp+90 in a0); record_sum_closes (0x143a8) (buf + 7 =
   sp+135, pll_f + 5) on the CLOSE record's bytes frag[15 .. 20 + pll_f) (FRAG C1.8: pll_f + 2 <= 53), its premises
   a0 != 0 and a0 + a1 <= 2^64 from SR; no stack, no memory written). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv record_sum_closes_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4 Tac_u5.
Import ListNotations.
Open Scope Z_scope.

Lemma g05_evt : record_sum_closes_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv pll : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> a1 = Z_to_bv 64 pll -> s0 = Z_to_bv 64 (spv + 128) ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> 1 <= pll <= 51 ->
    length bs = Z.to_nat (pll + 5) -> bytes_at rsegs m (spv + 135) bs ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' a4' a5' a6' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13b04) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (if recsum bs =? 0 then 1 else 0)) a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13b04) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13af0) fc None m (seg_rom rsegs)).
Proof.
  intros RSC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv pll bs Hsp Ha1 Hs0 Hlo Hhi Hpll Hlen HB.
  subst sp a1 s0.
  step. step. u5_br false.
  step. step. step.
  eapply evt_cut.
  { eapply RSC with (bs := bs).
    - u5_ul. match goal with |- length bs = Z.to_nat ?x => replace x with (pll + 5) by lia end. exact Hlen.
    - right. u5_ul. split; [lia|]. split; [lia|].
      match goal with |- bytes_at _ _ ?a _ => replace a with (spv + 135) by lia end. exact HB. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & E). subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13b04)) with (Z_to_bv 64 0x13b04)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists a1', a2', a3', a4', a5', a6'. reflexivity.
Qed.

Section G05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis RSC : record_sum_closes_contract.

Lemma seg_G05 : forall j : nat, Hat B APIf ra (Inv_U13b04_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13af0_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H26 & Hrf & H11).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof HGF as (((HLK & _) & _) & _ & HG & _).
  pose proof (u4_LK_s0 g j regs mem HLK) as H8.
  destruct (u5_close_facts (g_in g) j Hrf) as (HT & _).
  assert (Hpll : 1 <= f_pll (t_FG (g_in g) j) (t_g (g_in g) j) <= 51) by (unfold f_pll; lia).
  pose proof (u5_ba_bsl _ _ _ 15 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j) + 5) (u5_norm mem _ _ HMI (proj1 HG))
                ltac:(lia) ltac:(lia) ltac:(rewrite u4_tFGf_len; lia)) as HBS.
  unfold spk, SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  replace (g_S g - 1936 + 120 + 15) with (g_S g - 1936 + 135) in HBS by lia.
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ []);
    [exact HFR | exact HP | intros x Hx O; exfalso; apply O; exact I | | |].
  - rewrite sl_mkR_of.
    apply (g05_evt RSC) with (spv := g_S g - 1936) (pll := f_pll (t_FG (g_in g) j) (t_g (g_in g) j))
      (bs := RcFrag.bsl (t_FGf (g_in g) j) 15 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j) + 5));
      [exact Hsp | exact H11 | exact H8 | lia | lia | exact Hpll | | exact HBS].
    apply u5_bsl_len; [lia | lia | rewrite u4_tFGf_len; lia].
  - intros ms (? & ? & ? & ? & ? & ? & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & HE).
    injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [apply (u5_GF_keep g j phi regs regs' mem m' _ HGF HKP MU'); u4_dj|].
    split; [unfold rg in *; rewrite (sl_getr_eqv _ _ _ Hx); exact H26|].
    split; [exact Hrf|].
    unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End G05.
