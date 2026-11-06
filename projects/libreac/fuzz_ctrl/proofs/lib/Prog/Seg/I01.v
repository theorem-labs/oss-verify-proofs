(* Segment I01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13830, 0x13870], K13830 -> K13874 (r = 1: P4a,
   P4b and P4c not taken); K138c8 (r = 0). No call.
   libreac v1.9.0 (table 5a S_I01, CHANGED: register): sum_ok is s1 (0x1383c `beqz s1`; v1.8 s0), the reply
   outputs pl / pll at sp+1736 / sp+1728 (v1.8 1720 / 1712), the frame 1936 bytes; the instructions are v1.8's
   otherwise. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcParse RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
Open Scope Z_scope.

Lemma i01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len pll r : Z) (b26 : byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 r -> s5 = Z_to_bv 64 phi -> s4 = Z_to_bv 64 len ->
    r = 0 \/ r = 1 ->
    (r = 1 -> s1 = Z_to_bv 64 1 /\ s6 = Z_to_bv 64 (phi + 18) /\
       ov_read_bytes rsegs m (wa (spv + 1736)) 8 = Some (le8 (Z_to_bv 64 (phi + 38))) /\
       ov_read_bytes rsegs m (wa (spv + 1728)) 8 = Some (le8 (Z_to_bv 64 pll)) /\
       ov_read_bytes rsegs m (wa (phi + 26)) 1 = Some [b26] /\
       50 <= len < 2 ^ 64 /\ 1 <= pll <= 10 /\ bv_unsigned b26 = pll + 13 /\ 0 < phi /\ phi + 50 <= 2 ^ 64) ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    evt rsegs
      (fun ms' =>
         (r = 1 /\ exists a0' a1' : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 pll) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13874) fc None m (seg_rom rsegs)) \/
         (r = 0 /\ exists a1' : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x138c8) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13830) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len pll r b26 Hsp Ha0 Hs5 Hs4 Hr H1 Hlo Hhi.
  subst sp a0 s5 s4.
  destruct Hr as [-> | ->].
  - step. b5_br false. step. step. b5_br true.
    apply evt_done. right. split; [reflexivity|]. eexists. reflexivity.
  - destruct (H1 eq_refl) as (Hs1 & Hs6 & R20 & R12 & R26 & Hlen & Hpll & Hb26 & Hphi & Hphi50).
    subst s1 s6.
    step. b5_br false. step. step. b5_br false. step. b5_br false.
    step. step. b5_br false. step. step. b5_br false.
    step. step. step. step. b5_br false.
    step. step. b5_br false.
    step. step. step. b5_br false.
    apply evt_done. left. split; [reflexivity|]. do 2 eexists. reflexivity.
Qed.

Section I01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_I01 : forall j, Hat B APIf ra (Inv_K13874_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K138c8_at B APIf ra empty) j -> Hat B APIf ra (Inv_K13830_at B APIf ra empty) j.
Proof.
  intros j H1 H0 g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & H10 & HRPS).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (b5_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (b5_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof (proj1 HFR) as (Hn & _).
  pose proof HFB as ((Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & _) & (H23 & H25 & H9 & H18 & (H8 & H22 & _))).
  unfold g_n in Hn.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  eapply (b5_mid B APIf ra empty FF g _ L A regs mem md _ []);
    [exact HFR | exact HP | intros x Hx O; exfalso; apply O; exact I | | |].
  - rewrite sl_mkR_of.
    apply i01_evt with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j)
      (pll := r_pll (t_g (g_in g) j)) (r := t_r (g_in g) j) (b26 := nth 26 (t_g (g_in g) j) (Z_to_bv 8 0));
      [exact Hsp | exact H10 | exact H21 | exact H20 | | | lia | lia].
    + unfold t_r, rp_r. destruct (ir _ _); [right | left]; reflexivity.
    + intros Hr1.
      assert (Hir : t_ir (g_in g) j = true).
      { unfold t_r, rp_r in Hr1. unfold t_ir. destruct (ir _ _); [reflexivity | discriminate]. }
      destruct (b5_ir_facts _ _ Hir) as (H50 & Hbig & Hsok & Hpll & _).
      destruct HRPS as (HR1 & _). destruct (HR1 Hir) as (Ra & Rb & Rc).
      unfold spk, fsp, SLOT_FRAME in Ra, Rb, Rc.
      pose proof (b5_phi_g _ _ _ _ (bytes_at_normalize rsegs mem phi _ HMI Hphi) H50) as HG.
      split; [unfold rg in H9; rewrite H9, Hsok; reflexivity|].
      split; [unfold rg in H22; rewrite H22, Hbig; reflexivity|].
      split; [exact (b5_q64_read _ _ _ (bytes_at_normalize rsegs mem _ _ HMI Rb))|].
      split; [exact (b5_q64_read _ _ _ (bytes_at_normalize rsegs mem _ _ HMI Rc))|].
      split.
      { assert (L26 : (Z.to_nat 26 + 1 <= length (t_g (g_in g) j))%nat) by (rewrite b5_tg_len; cbn; lia).
        rewrite (bytes_at_read rsegs _ phi _ 26 1 HG ltac:(lia) L26). f_equal.
        change (Z.to_nat 26) with 26%nat. apply b5_first1. rewrite b5_tg_len. lia. }
      split; [lia|]. split; [exact Hpll|].
      split; [unfold r_pll, ir_s, cp_v, cp_b, cp_z; lia|].
      lia.
  - intros ms [(? & ? & ? & ->) | (? & ? & ->)];
      do 3 eexists; (split; [reflexivity|]); (split; [apply munch_refl|]); (split; [apply wmono_refl|]);
      (split; [reflexivity|]); split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as [(Hr1 & ? & ? & HE) | (Hr0 & ? & HE)]; injection HE; intros; subst;
      (assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity)).
    + assert (Hir : t_ir (g_in g) j = true).
      { unfold t_r, rp_r in Hr1. unfold t_ir. destruct (ir _ _); [reflexivity | discriminate]. }
      apply H1. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [apply (b5_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); b5_dj|].
      split; [apply (b5_IFS_keep g j regs regs' mem m' _ HIFS HKP MU'); b5_dj|].
      split; [exact Hir|].
      split; [apply (b5_RPS_keep g j phi mem m' _ HRPS MU'); b5_dj|].
      split; unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.
    + assert (Hir : t_ir (g_in g) j = false).
      { unfold t_r, rp_r in Hr0. unfold t_ir. destruct (ir _ _); [discriminate | reflexivity]. }
      destruct (b5_ir_false _ _ Hir) as (_ & EID).
      pose proof (b5_IFS_keep g j regs regs' mem m' _ HIFS HKP MU' ltac:(b5_dj) ltac:(b5_dj) ltac:(b5_dj)
                    ltac:(b5_dj)) as (HI' & HG' & HS').
      apply H0. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [apply (b5_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); b5_dj|].
      split; [unfold IDj in HI'; rewrite EID; exact HI'|].
      split; [exact HG' | exact HS'].
Qed.

End I01.
