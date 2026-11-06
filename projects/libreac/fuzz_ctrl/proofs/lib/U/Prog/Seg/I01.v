(* Segment I01 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x139bc, 0x13a10], U139bc -> U13a14
   (r = 1: P4a, P4b and P4c not taken; the UBSan checks T20-T22 on blk = Φ + 18 not taken by HBR), U13a68 (r = 0).
   No call. v1.9 registers: the r = 1 test against s2 = 1 (v1.8 s0 = 1), sum_ok s11, Φ s7, len s6, blk s8 (v1.8 s10,
   s6, s5, s7). Port of the plain seg_I01 (a working branch lib/Prog/Seg/I01.v). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4 Tac_u5.
Import ListNotations.
Open Scope Z_scope.

Lemma i01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len pll r : Z) (b26 : byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 r -> s2 = Z_to_bv 64 1 -> s7 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 len ->
    r = 0 \/ r = 1 ->
    (r = 1 -> s11 = Z_to_bv 64 1 /\ s8 = Z_to_bv 64 (phi + 18) /\
       ov_read_bytes rsegs m (wa (spv + 1736)) 8 = Some (le8 (Z_to_bv 64 (phi + 38))) /\
       ov_read_bytes rsegs m (wa (spv + 1728)) 8 = Some (le8 (Z_to_bv 64 pll)) /\
       ov_read_bytes rsegs m (wa (phi + 26)) 1 = Some [b26] /\
       50 <= len < 2 ^ 64 /\ 1 <= pll <= 10 /\ bv_unsigned b26 = pll + 13 /\ 4096 <= phi /\
       phi + 50 <= 2 ^ 63) ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    evt rsegs
      (fun ms' =>
         (r = 1 /\ exists a0' a2' a3' : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 pll) a2' a3' a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13a14) fc None m (seg_rom rsegs)) \/
         (r = 0 /\
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13a68) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x139bc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len pll r b26 Hsp Ha0 Hs2 Hs7 Hs6 Hr H1 Hlo Hhi.
  subst sp a0 s2 s7 s6.
  destruct Hr as [-> | ->].
  - step. u5_br false. step. u5_br true.
    apply evt_done. right. split; reflexivity.
  - destruct (H1 eq_refl) as (Hs11 & Hs8 & R1736 & R1728 & R26 & Hlen & Hpll & Hb26 & Hphi & Hphi50).
    subst s11 s8.
    step. u5_br false. step. u5_br false. step. u5_br false.
    step. step. u5_br false.
    step. step. u5_br false.
    step. step. step. step. u5_br false.
    step. u5_br false.
    step. step. u5_br false.
    step. step. u5_br false.
    step. step. step. u5_br false.
    step. step. step. u5_br false.
    apply evt_done. left. split; [reflexivity|]. do 3 eexists. reflexivity.
Qed.

Section I01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_I01 : forall j : nat, Hat B APIf ra (Inv_U13a14_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13a68_at B APIf ra empty) j -> Hat B APIf ra (Inv_U139bc_at B APIf ra empty) j.
Proof.
  intros j H1 H0 g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & H10 & HRPS).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof (proj1 HFR) as (Hn & _).
  pose proof HFB as ((HLK & (HS24 & H21 & H22) & H23 & Hphi & _) & (H25 & H19 & H27 & H20 & (H24 & _ & _))).
  pose proof (u4_LK_s2 g j regs mem HLK) as H18.
  unfold g_n in Hn.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ []);
    [exact HFR | exact HP | intros x Hx O; exfalso; apply O; exact I | | |].
  - rewrite sl_mkR_of.
    apply i01_evt with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j)
      (pll := r_pll (t_g (g_in g) j)) (r := t_r (g_in g) j) (b26 := nth 26 (t_g (g_in g) j) (Z_to_bv 8 0));
      [exact Hsp | exact H10 | exact H18 | exact H23 | exact H22 | | | lia | lia].
    + unfold t_r, rp_r. destruct (ir _ _); [right | left]; reflexivity.
    + intros Hr1.
      assert (Hir : t_ir (g_in g) j = true).
      { unfold t_r, rp_r in Hr1. unfold t_ir. destruct (ir _ _); [reflexivity | discriminate]. }
      destruct (u5_ir_facts _ _ Hir) as (H50 & Hbig & Hsok & Hpll & _).
      destruct HRPS as (HR1 & _). destruct (HR1 Hir) as (Ra & Rb & Rc).
      unfold spk, fsp, SLOT_FRAME in Ra, Rb, Rc.
      pose proof (u4_phi_g _ _ _ _ (u5_norm mem phi _ HMI Hphi) H50) as HG.
      split; [unfold V0, rg in H27; rewrite H27, Hsok; reflexivity|].
      split; [unfold rg in H24; rewrite H24, Hbig; reflexivity|].
      split; [exact (u5_q64_read _ _ _ (u5_q64_norm mem _ _ HMI Rb))|].
      split; [exact (u5_q64_read _ _ _ (u5_q64_norm mem _ _ HMI Rc))|].
      split.
      { pose proof (u5_byte_read _ phi _ 26 HG ltac:(rewrite u4_tg_len; lia)) as R.
        change (Z.of_nat 26) with 26 in R. exact R. }
      split; [lia|]. split; [exact Hpll|].
      split; [unfold r_pll, ir_s, cp_v, cp_b, cp_z; lia|].
      lia.
  - intros ms [(? & ? & ? & ? & ->) | (? & ->)];
      do 3 eexists; (split; [reflexivity|]); (split; [apply munch_refl|]); (split; [apply wmono_refl|]);
      (split; [reflexivity|]); split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as [(Hr1 & ? & ? & ? & HE) | (Hr0 & HE)]; injection HE; intros; subst;
      (assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity)).
    + assert (Hir : t_ir (g_in g) j = true).
      { unfold t_r, rp_r in Hr1. unfold t_ir. destruct (ir _ _); [reflexivity | discriminate]. }
      apply H1. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj|].
      split; [apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj|].
      split; [exact Hir|].
      split; [apply (u5_RPS_keep g j phi mem m' _ HRPS MU'); u4_dj|].
      unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + assert (Hir : t_ir (g_in g) j = false).
      { unfold t_r, rp_r in Hr0. unfold t_ir. destruct (ir _ _); [discriminate | reflexivity]. }
      destruct (u5_ir_false _ _ Hir) as (_ & EID).
      pose proof (u4_IFS_keep g j mem m' _ HIFS MU' ltac:(u4_dj) ltac:(u4_dj) ltac:(u4_dj)) as (HI' & HG' & HS').
      apply H0. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj|].
      split; [unfold IDj in HI'; rewrite EID; exact HI'|].
      split; [exact HG' | exact HS'].
Qed.

End I01.
