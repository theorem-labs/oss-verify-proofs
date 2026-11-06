(* Segment C01 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13f98, 0x13fb4], ev = -1 at sp+1684, then
   reac_ctrl_classify_box_frame(Φ = s7, len = s6, our = sp+114, out = sp+1688, ev = sp+1684) (CLS; window 128).
   U13f98 -> U13fb8. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv
  reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Lemma c01_evt : reac_ctrl_classify_box_frame_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len : Z) (fr us junk jv : list byte),
    sp = Z_to_bv 64 spv -> 65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    s7 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 len -> 4096 <= phi -> phi + 50 <= spv - 128 -> 0 <= len < 2 ^ 64 ->
    stk rsegs m (spv - 128) spv -> length fr = 50%nat -> (50 <= len -> bytes_at rsegs m phi fr) ->
    length us = 6%nat -> bytes_at rsegs m (spv + 114) us ->
    rw_cells rsegs m (spv + 1688) [CB 36 junk] -> rw_cells rsegs m (spv + 1684) [CB 4 jv] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13fb8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r (classify len fr us)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13fb8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1684, spv + 1724); (spv - 128, spv)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (spv + 1688) [CB 36 (snd (ctrlparse len fr))] /\
         rw_cells rsegs m' (spv + 1684)
           [CB 4 (reac_ctrl_classify_box_frame_ev (classify len fr us) (le4 (Z_to_bv 64 (-1))))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13f98) fc None m (seg_rom rsegs)).
Proof.
  intros CL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len fr us junk jv -> Hs0 Hs1 H16 -> -> Hp0 Hp1 Hl ST Hfl Hfr Hul HU HO HV MI.
  pose proof (munch_refl [(spv + 1684, spv + 1724); (spv - 128, spv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HF0 : 50 <= len -> bytes_at rsegs m phi fr) by exact Hfr. clear Hfr.
  destruct (Z_lt_le_dec len 50) as [Hs|Hb]; [clear HF0 | specialize (HF0 Hb)].
  all: pose proof (conj HU I) as HUp; clear HU.
  2: pose proof (conj HF0 I) as HFp; clear HF0.
  all: step. all: step. all: step. all: step.
  all: step. all: step. all: step. all: step.
  all: pose proof (u8_ba _ _ _ _ _ (proj1 HUp) MU
         ltac:(rewrite Hul; cbn [disjoint_from]; repeat split; try exact I; lia)) as HU.
  2: pose proof (u8_ba _ _ _ _ _ (proj1 HFp) MU
         ltac:(rewrite Hfl; cbn [disjoint_from]; repeat split; try exact I; lia)) as HF0.
  all: eapply evt_cut.
  1, 3: (eapply CL with (f := phi) (n := len) (u := spv + 114) (o := spv + 1688) (v := spv + 1684) (S := spv)
       (fr := fr) (us := us) (junk := junk) (vb := le4 (Z_to_bv 64 (-1)));
     unfold REAC_CTRL_CLASSIFY_BOX_FRAME_K;
     first [ reflexivity | (rewrite ?MState.unsigned_lit by lia; reflexivity) | lia | exact ST | exact Hfl
           | exact Hul | exact HU | exact HO | exact HV | exact MI
           | (intros ?; exfalso; lia)
           | (intros ?; split; [lia|]; split; [lia|]; split; [exact HF0 | lia])
           | (intros ?; split; [lia|]; split; [exact HU | lia])
           | (match goal with H : rw_cells _ _ _ [C4 _] |- _ => exact (u8_rw_c4 _ _ _ H) end) ]).
  all: (intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                 E & MUc & WMc & MI' & ST' & HOc & HVc);
     subst ms';
     replace (ret_pc (Z_to_bv 64 0x13fb8)) with (Z_to_bv 64 0x13fb8)
       by (symmetry; apply ret_pc_even; [lia | reflexivity]);
     apply evt_done; exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m';
     split; [reflexivity|];
     split; [apply (munch_trans _ _ _ _ MU); eapply munch_weaken; [|exact MUc];
             intros x Hx; destruct Hx as (H1 & H2 & _); unfold REAC_CTRL_CLASSIFY_BOX_FRAME_K;
             split; [lia|]; split; [lia|]; split; [lia | exact I]|];
     split; [exact (wmono_trans rsegs _ _ _ WM WMc)|];
     split; [exact HOc | exact HVc]).
Qed.

Section C01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CLS : reac_ctrl_classify_box_frame_contract.

Lemma seg_C01 : forall j : nat, Hat B APIf ra (Inv_U13fb8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13f98_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HCC).
  pose proof HCC as ((HFT & HVC & HIFS) & H20 & H25).
  pose proof HFT as ((Hj & H9 & HOUR & HM7 & HOVF & HS2) & (H24 & H21 & H22) & H23 & Hphi & H18).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u8_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u8_t_facts (g_in g) j) as (Rc & EL & Rh & _ & HL & _).
  pose proof (u8_p_range B APIf ra empty FF g (proj1 HFR)) as (_ & _ & Hn).
  unfold g_n in Hn.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1688) 36 ST ltac:(lia) ltac:(lia)) as (junk & HO).
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1684) 4 ST ltac:(lia) ltac:(lia)) as (jv & HV).
  eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _
            [(g_S g - 1936 + 1684, g_S g - 1936 + 1724); (g_S g - 1936 - 128, g_S g - 1936)]);
    [exact HFR | exact HP | u8_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (c01_evt CLS) with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j) (fr := t_g (g_in g) j)
      (us := OUR (g_in g)) (junk := junk) (jv := jv);
      [exact Hsp | lia | lia | exact H16 | exact H23 | exact H22 | lia | lia | lia | | apply u8_tg_len | |
       apply OUR_length | | exact HO | exact HV | exact (mem_inv_normalize rsegs mem)].
    + apply (u8_stk_sub _ _ _ _ _ ST); lia.
    + intros Hb. rewrite (u8_g_bytes _ _ Hb).
      pose proof (u8_at_slice _ phi _ 0 50 (bytes_at_normalize rsegs mem phi _ HMI Hphi)) as E.
      cbn [Z.of_nat skipn] in E. rewrite Z.add_0_r in E. apply E. rewrite u8_phi_length. lia.
    + unfold OURb, spk, fsp, SLOT_FRAME in HOUR. exact (bytes_at_normalize rsegs mem _ _ HMI HOUR).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HOc & HVc).
    injection HE; intros; subst.
    apply (H g). exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
    split; [|split; [split|]].
    + apply (u8_CC_keep g j phi regs regs' mem m' _ HCC HK (eq_trans (HG _) eq_refl) (eq_trans (HG _) eq_refl) MU');
        u8_dj.
    + apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). unfold spk, fsp, SLOT_FRAME.
      exact (u8_c_bytes _ _ _ HOc).
    + apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). unfold spk, fsp, SLOT_FRAME.
      exact (u8_c_bytes _ _ _ HVc).
    + unfold rg. rewrite HG. reflexivity.
Qed.

End C01.
