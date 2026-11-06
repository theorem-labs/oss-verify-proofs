(* Segment G02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13a78, 0x13a90], U13a78 -> U13a94
   (reac_ctrl_identity_fragment (0x152bc) (frag = sp+120, Φ (s7), len (s6), sp+1750, sp+1736, sp+1728; v1.8 frag
   sp+82, Φ s6, len s5); pp = frag + 19 = sp+139; the WIP U contract, frame 96). Port of the plain seg_G02
   (a working branch lib/Prog/Seg/G02.v). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4 Tac_u5.
Import ListNotations.
Open Scope Z_scope.

Lemma g02_fcls : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  fg_class f fr pa pp pn len st g = fcls len st g.
Proof.
  intros f fr pa pp pn len st g H1 H2 H3 H4 H5. unfold fcls, fg_class.
  rewrite (proj2 (Z.eqb_neq f 0) H1), (proj2 (Z.eqb_neq fr 0) H2), (proj2 (Z.eqb_neq pa 0) H3),
    (proj2 (Z.eqb_neq pp 0) H4), (proj2 (Z.eqb_neq pn 0) H5).
  reflexivity.
Qed.

Ltac g02_mw MUc :=
  eapply munch_weaken; [|exact MUc]; intros x (O1 & O2 & O3 & _); cbn [Frame.outside];
  repeat split; try exact I; lia.

Lemma g02_evt : reac_ctrl_identity_fragment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len : Z) (st g : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 len ->
    spv mod 16 = 0 -> 96 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 < phi -> phi + 50 <= spv - 96 -> 0 <= len < 2 ^ 64 ->
    stk rsegs m (spv - 96) (spv + 1832) -> mem_inv rsegs m -> length st = 72%nat -> length g = 50%nat ->
    (50 <= len -> bytes_at rsegs m phi g) -> rw_cells rsegs m (spv + 120) [CB 72 st] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13a94) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_rf len st g))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13a94) fc None m' (seg_rom rsegs) /\
         munch [(spv - 96, spv); (spv + 120, spv + 192); (spv + 1728, spv + 1752)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 120) (fg_st len st g) /\
         (fg_rf len st g = 1 -> u16 m' (spv + 1750) (fg_addr st g) /\ q64 m' (spv + 1736) (spv + 139) /\
                                q64 m' (spv + 1728) (f_pll st g)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a78) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len st g Hsp Hs7 Hs6 H16 H96 Hhi Hphi Hpb Hlen ST MI Hst Hg Hg50 Hrw.
  subst sp s7 s6.
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply FRAG with (f := spv + 120) (fr := phi) (len := len) (pa := spv + 1750) (pp := spv + 1736)
      (pn := spv + 1728) (st := st) (g := g);
      [ first [reflexivity | u5_weq] | first [reflexivity | u5_weq] | first [reflexivity | u5_weq]
      | first [reflexivity | u5_weq] | first [reflexivity | u5_weq] | first [reflexivity | u5_weq]
      | lia | lia | lia | lia | lia | lia
      | u5_ul; exact H16
      | unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME; u5_ul; apply (u4_stk_sub _ _ _ _ _ ST); lia
      | exact Hg | exact Hst | intros _ _ _ _ _ H50; exact (Hg50 H50) | | exact MI ].
    intros _ _ _ _ _. unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME. u5_ul.
    split; [exact Hrw|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply (u5_wr_of_stk _ _ _ _ _ ST); lia|].
    split; [apply (u5_wr_of_stk _ _ _ _ _ ST); lia|].
    split; [apply (u5_wr_of_stk _ _ _ _ _ ST); lia|].
    cbn [all_dj dj_from]. repeat split; lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _ & Hfm).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13a94)) with (Z_to_bv 64 0x13a94)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (MState.unsigned_lit spv) in MUc by lia.
  rewrite (g02_fcls (spv + 120) phi (spv + 1750) (spv + 1736) (spv + 1728) len st g) in MUc, Hfm |- * by lia.
  unfold fg_rf, fg_st.
  pose proof (u5_nref len st g) as NR.
  pose proof (sl_rw_bytes _ _ _ _ Hrw) as Hst0.
  apply evt_done. do 14 eexists. exists m'. split; [reflexivity|].
  destruct (fcls len st g); [exfalso; exact (NR eq_refl) | | | | |];
    cbn [fg_next fg_ret fg_fp fg_mem] in MUc, Hfm |- *; unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME in MUc.
  - split; [g02_mw MUc|]. split; [exact WMc|]. split; [|intros C; discriminate].
    apply (bytes_at_transport rsegs _ m m' _ _ Hst0 MUc). cbn [disjoint_from]. rewrite Hst.
    repeat split; try exact I; lia.
  - split; [g02_mw MUc|]. split; [exact WMc|]. split; [exact Hfm | intros C; discriminate].
  - split; [g02_mw MUc|]. split; [exact WMc|]. split; [exact Hfm | intros C; discriminate].
  - split; [g02_mw MUc|]. split; [exact WMc|]. split; [exact Hfm | intros C; discriminate].
  - destruct Hfm as (F1 & F2 & F3 & F4).
    split; [g02_mw MUc|]. split; [exact WMc|]. split; [exact F1|].
    intros _. split; [exact F2|]. split; [|exact F4].
    unfold q64. replace (spv + 139) with (spv + 120 + 19) by lia. exact F3.
Qed.

Section G02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FRAG : reac_ctrl_identity_fragment_contract.

Lemma seg_G02 : forall j : nat, Hat B APIf ra (Inv_U13a94_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13a78_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HFB & HI & HG & HS) & H192).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof (proj1 HFR) as (Hn & _).
  pose proof HFB as ((HLK & (HS24 & H21 & H22) & H23 & Hphi & H18) & _).
  unfold g_n in Hn.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 120) 72 ST ltac:(lia) ltac:(lia)) as (jk & Hjk).
  pose proof (u5_rw_ba _ _ _ _ _ Hjk (u5_norm mem _ _ HMI (proj1 HG)) (u4_tFG_len _ _)) as Hrw.
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _
            [(g_S g - 1936 - 96, g_S g - 1936); (g_S g - 1936 + 120, g_S g - 1936 + 192);
             (g_S g - 1936 + 1728, g_S g - 1936 + 1752)]);
    [exact HFR | exact HP | u4_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (g02_evt FRAG) with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j)
      (st := t_FG (g_in g) j) (g := t_g (g_in g) j);
      [exact Hsp | exact H23 | exact H22 | exact H16 | lia | lia | lia | lia | unfold nlen in Hbl; lia
      | apply (u4_stk_sub _ _ _ _ _ ST); lia | exact (mem_inv_normalize rsegs mem) | apply u4_tFG_len
      | apply u4_tg_len | intros Hb; exact (u4_phi_g _ _ _ _ (u5_norm mem phi _ HMI Hphi) Hb)
      | exact Hrw].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & Hfg & Hcl).
    injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [|split; [|split; [|split; [|split]]]]|].
    + apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj.
    + exact (u4_IDb_keep g _ mem m' _ (u4_tIDr_len _ _) HI MU' ltac:(u4_dj)).
    + split.
      * unfold FGB, t_FGf, spk, fsp, SLOT_FRAME. apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). exact Hfg.
      * exact (proj2 (proj2 (u5_lens (g_in g) j))).
    + exact (u4_FSj_keep g j mem m' _ HS MU' ltac:(u4_dj)).
    + apply (u4_ba _ mem m' _ _ H192 MU'). rewrite u4_tFG_len. u4_dj.
    + intros Hrf. destruct (Hcl Hrf) as (C1 & C2 & C3). unfold u16, q64, spk, fsp, SLOT_FRAME in *.
      split; [|split]; apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)); assumption.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End G02.
