(* Segment C01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13ca0, 0x13cbc], ev = -1 at sp+1684, then
   reac_ctrl_classify_box_frame(Φ, len, our = sp+76, q = sp+1688, &ev = sp+1684). K13ca0 -> K13cc0.
   libreac v1.9.0 (table 5a S_C01: IDENTICAL-RENUMBER, OLD 0x13c70 .. 0x13c8c): pcs, the frame offsets
   (ev 1668 -> 1684, our 60 -> 76, q 1672 -> 1688) and the frame size 1920 -> 1936 move; cuts K13c70 -> K13ca0
   and K13c90 -> K13cc0 (SlotInv.v's renames), so seg_C01 is stated on the renamed cuts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify SlotModel SlotInv
  reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m Tac_b8c.
Import ListNotations.
Open Scope Z_scope.

Lemma kC01 : reac_ctrl_classify_box_frame_contract -> forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
    x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (sp0 lo phi n : Z) (fr us junk ob : list byte),
  x2 = Z_to_bv 64 sp0 -> x21 = Z_to_bv 64 phi -> x20 = Z_to_bv 64 n ->
  0 <= lo -> lo <= sp0 - 128 -> sp0 mod 16 = 0 -> sp0 + 1936 < 2 ^ 64 ->
  0 < phi -> phi + 50 <= sp0 - 128 -> 0 <= n < 2 ^ 64 ->
  stk rsegs m lo sp0 -> length fr = 50%nat -> (50 <= n -> bytes_at rsegs m phi fr) ->
  length us = 6%nat -> bytes_at rsegs m (sp0 + 76) us ->
  rw_cells rsegs m (sp0 + 1688) [CB 36 junk] -> rw_cells rsegs m (sp0 + 1684) [CB 4 ob] -> mem_inv rsegs m ->
  Exec.evt rsegs
    (fun ms' => exists R m', ms' = MS R F (Z_to_bv 64 0x13cc0) fc None m' (seg_rom rsegs) /\
       (getr R 10 = Z_to_bv 64 (cl_r (classify n fr us)) /\ getr R 2 = Z_to_bv 64 sp0 /\ getr R 3 = x3 /\
        getr R 4 = x4 /\ getr R 9 = x9 /\ getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\
        getr R 21 = x21 /\ getr R 22 = x22 /\ getr R 23 = x23 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
        munch [(sp0 - 128, sp0); (sp0 + 1684, sp0 + 1724)] m m' /\ wmono rsegs m m' /\
        bytes_at rsegs m' (sp0 + 1688) (snd (ctrlparse n fr)) /\
        bytes_at rsegs m' (sp0 + 1684)
          (reac_ctrl_classify_box_frame_ev (classify n fr us) (le4 (Z_to_bv 64 (-1))))))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13ca0) fc None m (seg_rom rsegs)).
Proof.
  intros CLSF x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m sp0 lo phi n fr us junk ob E2 E21 E20 Hlo0 Hlo1 H16 H1 Hp0 Hp1 Hn ST Hfl Hfr Hul Hu
    HO HV HMI.
  subst x2 x21 x20.
  pose proof (munch_refl [(sp0 - 128, sp0); (sp0 + 1684, sp0 + 1724)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  match goal with H : rw_cells rsegs ?mm (sp0 + 1684) [C4 ?v] |- _ =>
    replace v with (Z_to_bv 64 (-1)) in H by (first [reflexivity | apply bv_eq; vm_compute; reflexivity]);
    pose proof (b8c_c4_cb _ _ _ H) as HV'
  end.
  match goal with MU0 : munch _ m ?m0 |- _ =>
    assert (Hfr0 : 50 <= n -> bytes_at rsegs m0 phi fr)
      by (intros Hb; apply (b8_ba_keepW _ m m0 _ _ (Hfr Hb) MU0); rewrite Hfl; intros x Hx; b8c_out)
  end.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply CLSF with (f := phi) (n := n) (u := sp0 + 76) (o := sp0 + 1688) (v := sp0 + 1684) (S := sp0)
      (fr := fr) (us := us) (junk := junk) (vb := le4 (Z_to_bv 64 (-1)));
    unfold REAC_CTRL_CLASSIFY_BOX_FRAME_K;
    first [ reflexivity | (f_equal; lia) | assumption | lia | (Z.div_mod_to_equations; lia)
          | (apply (b8_stk_sub _ _ _ _ _ _ ST); lia)
          | (intros Hb'; split; [lia | split; [lia | split; [exact (Hfr0 Hb') | lia]]])
          | (intros _; split; [lia | split; [assumption | lia]])
          | (intros _; lia) ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & STc & RWo & RWv).
  subst ms'. unfold REAC_CTRL_CLASSIFY_BOX_FRAME_K in MUc. rewrite (b8_ret_pc 0x13cc0) by lia.
  apply evt_done. eexists _, _. split; [reflexivity|].
  repeat (split; [reflexivity|]).
  match goal with MU0 : munch _ m ?m0, WM0 : wmono rsegs m ?m0 |- _ =>
    split; [eapply munch_trans; [exact MU0 | eapply munch_weaken; [|exact MUc]]; b8c_sub|];
    split; [exact (wmono_trans _ _ _ _ WM0 WMc)|]
  end.
  split; [exact (sl_rw_bytes _ _ _ _ RWo) | exact (sl_rw_bytes _ _ _ _ RWv)].
Qed.

Section C01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CLSF : reac_ctrl_classify_box_frame_contract.

Lemma seg_C01 : forall j : nat, Hat B APIf ra (Inv_K13cc0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13ca0_at B APIf ra empty) j.
Proof.
  intros j H1 g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP HCC.
  pose proof HCC as ((HFT & H18 & HVC & HI) & H23).
  pose proof HFT as (Hj & H26 & (H27 & H32 & H20) & H21 & HBphi & HO & HM7).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof (sl_fr_stk B APIf ra empty FF g _ L A regs mem md HF) as HST.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _).
  pose proof alloc_ceiling_value as HAC.
  pose proof (b8_p_range B APIf ra empty FF g _ L A regs mem md HF HP) as (Hp0 & Hpn & Hn).
  pose proof (b8_t_facts (g_in g) j) as (Rc & EL & Rh & Eh & Rl & _).
  unfold g_n in *. unfold SLOT_K, SLOT_STACK in *.
  unfold MI in HMI. rewrite (b8_segs B APIf ra empty FF) in HMI.
  assert (Hin : In (phi, t_len (g_in g) j) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_block_pos B APIf ra empty g _ L A regs mem md _ _ HF Hin) as [Hph1 Hph2].
  assert (Hfr : 50 <= t_len (g_in g) j -> bytes_at rsegs (normalize rsegs mem) phi (t_g (g_in g) j)).
  { intros Hb. rewrite (b8_g_bytes _ _ Hb).
    pose proof (b8_ba_sub rsegs _ phi _ 0 50 (MemNorm.bytes_at_normalize rsegs mem _ _ HMI HBphi)) as X.
    rewrite Z.add_0_r, skipn_O in X. apply X. rewrite b8_phi_length. lia. }
  assert (Hu : bytes_at rsegs (normalize rsegs mem) (g_S g - 1936 + 76) (OUR (g_in g))).
  { replace (g_S g - 1936 + 76) with (spk g 76) by (unfold spk, fsp, SLOT_FRAME; lia).
    exact (MemNorm.bytes_at_normalize rsegs mem _ _ HMI HO). }
  destruct (sl_rw_of_stk (normalize rsegs mem) (g_S g - 65536) (g_S g) (g_S g - 1936 + 1688) 36 HST
              ltac:(lia) ltac:(lia)) as (junk & HOJ).
  destruct (sl_rw_of_stk (normalize rsegs mem) (g_S g - 65536) (g_S g) (g_S g - 1936 + 1684) 4 HST
              ltac:(lia) ltac:(lia)) as (ob & HOV).
  eapply (b8_mid B APIf ra empty FF g _ L A regs mem md (Z_to_bv 64 0x13ca0)
            [(g_S g - 1936 - 128, g_S g - 1936); (g_S g - 1936 + 1684, g_S g - 1936 + 1724)]).
  - exact HF.
  - exact HP.
  - intros x Hx O. unfold SLOT_K, SLOT_STACK.
    destruct (Z_le_dec (g_S g - 1936 - 128) x); destruct (Z_lt_dec x (g_S g - 1936));
      destruct (Z_le_dec (g_S g - 1936 + 1684) x); destruct (Z_lt_dec x (g_S g - 1936 + 1724)); try lia;
      exfalso; apply O; b8c_out.
  - rewrite sl_mkR_of.
    eapply (kC01 CLSF) with (sp0 := g_S g - 1936) (lo := g_S g - 65536) (phi := phi) (n := t_len (g_in g) j)
      (fr := t_g (g_in g) j) (us := OUR (g_in g)) (junk := junk) (ob := ob).
    + exact Hsp.
    + exact H21.
    + exact H20.
    + lia.
    + lia.
    + exact H16.
    + lia.
    + lia.
    + lia.
    + lia.
    + apply (b8_stk_sub _ _ _ _ _ _ HST); lia.
    + apply fr50_length.
    + exact Hfr.
    + apply OUR_length.
    + exact Hu.
    + exact HOJ.
    + exact HOV.
    + exact (MemNorm.mem_inv_normalize rsegs mem).
  - intros ms (R & m' & -> & (H10 & E2 & E3 & E4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _)).
    exists R, (Z_to_bv 64 0x13cc0), m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [rewrite E2; symmetry; exact Hsp|]. split; [exact E3 | exact E4].
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HF'.
    destruct HQ as (R1 & m1 & E & (H10 & E2 & E3 & E4 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E26 & E27 &
                    MU & WM & BA1 & BA2)).
    injection E; intros; subst.
    apply H1. exists phi. apply (b8_cut_close B APIf ra empty _ _ _ _ L A); [exact HF' | exact HP |].
    assert (G : forall r0, getr regs' r0 = getr R1 r0) by (intros r0; apply sl_getr_eqv; exact Hx).
    split; [|split; [split|]].
    + split.
      * apply (b8_CC7_munch g j phi regs' mem m'
                 [(g_S g - 1936 - 128, g_S g - 1936); (g_S g - 1936 + 1684, g_S g - 1936 + 1724)]);
          [| exact MU' |].
        -- apply (b8_CC7_regs _ _ _ regs); [exact (proj1 HCC) | rewrite G; assumption ..].
        -- intros x Hx'. unfold spk, fsp, SLOT_FRAME in Hx'. b8c_out.
      * unfold V7, rg in *. rewrite G, E23. exact H23.
    + replace (spk g 1688) with (g_S g - 1936 + 1688) by (unfold spk, fsp, SLOT_FRAME; lia).
      exact (proj2 (bytes_at_rel rsegs m' m1 _ _ Hrel) BA1).
    + replace (spk g 1684) with (g_S g - 1936 + 1684) by (unfold spk, fsp, SLOT_FRAME; lia).
      exact (proj2 (bytes_at_rel rsegs m' m1 _ _ Hrel) BA2).
    + unfold rg. rewrite G, H10. reflexivity.
Qed.

End C01.
