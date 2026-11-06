(* Segment G02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x138d8, 0x138f0], K138d8 -> K138f4
   (reac_ctrl_identity_fragment(sp+82, Φ, len, sp+1750, sp+1736, sp+1728): frag = FGf, rf = fg_rf).
   libreac v1.9.0 (table 5a S_G02, IDENTICAL-RENUMBER): pcs + 0xc, frag sp+82 (v1.8 66), the fragment outputs
   addr / pl / pll at sp+1750 / 1736 / 1728 (v1.8 1734 / 1720 / 1712), pl = &frag + 19 = sp+101 (v1.8 85), the
   frame 1936 bytes (saved registers at sp+1832). rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcFrag
  reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b5.
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

(* frag_ok (struct.reac_identity_frag FG2) of each new reassembly state. *)
Lemma g02_clear_ok : forall st, (6 <= length st)%nat -> frag_ok (fg_clear st).
Proof.
  intros st H. assert (E : bat (fg_clear st) 6 = 0).
  { unfold bat, fg_clear. rewrite app_nth2 by (rewrite length_firstn; lia).
    rewrite length_firstn. replace (Z.to_nat 6 - Nat.min 6 (length st))%nat with 0%nat by lia. reflexivity. }
  unfold frag_ok. rewrite E. split; [left; reflexivity | intros C; discriminate].
Qed.

Lemma g02_first_ok : forall st g, length g = 50%nat -> 1 <= fg_n g <= 22 -> frag_ok (fg_first st g).
Proof.
  intros st g Hg Hn.
  assert (L6 : length (bsl g 6 6) = 6%nat) by (unfold bsl; rewrite length_firstn, length_skipn, Hg; reflexivity).
  assert (E6 : bat (fg_first st g) 6 = 1).
  { unfold bat, fg_first. rewrite app_nth2 by (rewrite L6; lia). rewrite L6. reflexivity. }
  assert (E7 : bat (fg_first st g) 7 = fg_n g).
  { unfold bat, fg_first. rewrite app_nth2 by (rewrite L6; lia). rewrite L6. reflexivity. }
  unfold frag_ok. rewrite E6, E7. split; [right; reflexivity | intros _; exact Hn].
Qed.

Lemma g02_fgst_ok : forall len st g, length st = 72%nat -> length g = 50%nat -> frag_ok st ->
  frag_ok (fg_st len st g).
Proof.
  intros len st g Hs Hg Hok. pose proof (b5_bat_nn st 7) as H7.
  unfold fg_st, fg_next, fcls, fg_class. cbn [Z.eqb orb].
  destruct (fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hok].
  pose proof (b5_fgfr_n len g Efr) as Hn.
  destruct (bat g 19 =? 1); cbn [negb]; [apply g02_first_ok; assumption|].
  destruct (fg_keep st g); cbn [negb]; [|apply g02_clear_ok; lia].
  destruct (fg_close st g); cbn [negb]; apply g02_clear_ok;
    unfold fg_join, fg_lf; rewrite !length_app, length_firstn; lia.
Qed.

Ltac g02_mw MUc :=
  eapply munch_weaken; [|exact MUc]; intros x (O1 & O2 & O3 & _); cbn [Frame.outside];
  repeat split; try exact I; lia.

Lemma g02_evt : reac_ctrl_identity_fragment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len : Z) (st g : list byte),
    sp = Z_to_bv 64 spv -> s5 = Z_to_bv 64 phi -> s4 = Z_to_bv 64 len ->
    spv mod 16 = 0 -> 160 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 < phi -> phi + 50 <= spv - 80 -> 0 <= len < 2 ^ 64 ->
    stk rsegs m (spv - 80) (spv + 1832) -> mem_inv rsegs m -> length st = 72%nat -> length g = 50%nat ->
    (50 <= len -> bytes_at rsegs m phi g) -> rw_cells rsegs m (spv + 82) [CB 72 st] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x138f4) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fg_rf len st g))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x138f4) fc None m' (seg_rom rsegs) /\
         munch [(spv - 80, spv); (spv + 82, spv + 154); (spv + 1728, spv + 1752)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 82) (fg_st len st g) /\
         (fg_rf len st g = 1 -> u16 m' (spv + 1750) (fg_addr st g) /\ q64 m' (spv + 1736) (spv + 101) /\
                                q64 m' (spv + 1728) (f_pll st g)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138d8) fc None m (seg_rom rsegs)).
Proof.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len st g Hsp Hs5 Hs4 H16 H160 Hhi Hphi Hpb Hlen ST MI Hst Hg Hg50 Hrw.
  subst sp s5 s4.
  step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply FRAG with (f := spv + 82) (fr := phi) (len := len) (pa := spv + 1750) (pp := spv + 1736)
      (pn := spv + 1728) (st := st) (g := g);
      [ first [reflexivity | b5_weq] | first [reflexivity | b5_weq] | first [reflexivity | b5_weq]
      | first [reflexivity | b5_weq] | first [reflexivity | b5_weq] | first [reflexivity | b5_weq]
      | lia | lia | lia | lia | lia | lia
      | b5_ul; exact H16
      | unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME; b5_ul; apply (b5_stk_sub _ _ _ _ _ ST); lia
      | exact Hg | exact Hst | intros _ _ _ _ _ H50; exact (Hg50 H50) | | exact MI ].
    intros _ _ _ _ _. unfold REAC_CTRL_IDENTITY_FRAGMENT_FRAME. b5_ul.
    split; [exact Hrw|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply (b5_wr_of_stk _ _ _ _ _ ST); lia|].
    split; [apply (b5_wr_of_stk _ _ _ _ _ ST); lia|].
    split; [apply (b5_wr_of_stk _ _ _ _ _ ST); lia|].
    cbn [all_dj dj_from]. repeat split; lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _ & Hfm).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x138f4)) with (Z_to_bv 64 0x138f4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (MState.unsigned_lit spv) in MUc by lia.
  rewrite (g02_fcls (spv + 82) phi (spv + 1750) (spv + 1736) (spv + 1728) len st g) in MUc, Hfm |- * by lia.
  unfold fg_rf, fg_st.
  pose proof (b5_nref len st g) as NR.
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
    unfold q64. replace (spv + 101) with (spv + 82 + 19) by lia. exact F3.
Qed.

Section G02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FRAG : reac_ctrl_identity_fragment_contract.

Lemma seg_G02 : forall j, Hat B APIf ra (Inv_K138f4_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K138d8_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HFB & HI & HG & HS) & H192).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (b5_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (b5_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof (b5_nb_range (g_in g) j) as Hnb.
  pose proof (proj1 HFR) as (Hn & _).
  pose proof HFB as ((Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & _) & _).
  unfold g_n in Hn.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 82) 72 ST ltac:(lia) ltac:(lia)) as (jk & Hjk).
  pose proof (b5_rw_ba _ _ _ _ _ Hjk (bytes_at_normalize rsegs mem _ _ HMI (proj1 HG)) (b5_tFG_len _ _)) as Hrw.
  eapply (b5_mid B APIf ra empty FF g _ L A regs mem md _
            [(g_S g - 1936 - 80, g_S g - 1936); (g_S g - 1936 + 82, g_S g - 1936 + 154);
             (g_S g - 1936 + 1728, g_S g - 1936 + 1752)]);
    [exact HFR | exact HP | b5_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (g02_evt FRAG) with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j)
      (st := t_FG (g_in g) j) (g := t_g (g_in g) j);
      [exact Hsp | exact H21 | exact H20 | exact H16 | lia | lia | lia | lia | unfold nlen in Hbl; lia
      | apply (b5_stk_sub _ _ _ _ _ ST); lia | exact (mem_inv_normalize rsegs mem) | apply b5_tFG_len
      | apply b5_tg_len | intros Hb; exact (b5_phi_g _ _ _ _ (bytes_at_normalize rsegs mem phi _ HMI Hphi) Hb)
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
    + apply (b5_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); b5_dj.
    + exact (b5_IDb_keep g _ mem m' _ (b5_tIDr_len _ _) HI MU' ltac:(b5_dj)).
    + split.
      * unfold FGB, t_FGf, spk, fsp, SLOT_FRAME. apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). exact Hfg.
      * apply g02_fgst_ok; [apply b5_tFG_len | apply b5_tg_len | exact (proj2 HG)].
    + exact (b5_FSb_keep g _ _ regs regs' mem m' _ HS (proj1 (proj2 (proj2 (proj2 HKP)))) MU' ltac:(b5_dj)
               ltac:(b5_dj)).
    + apply (b5_ba _ mem m' _ _ H192 MU'). rewrite b5_tFG_len. b5_dj.
    + intros Hrf. destruct (Hcl Hrf) as (C1 & C2 & C3). unfold u16, q64, spk, fsp, SLOT_FRAME in *.
      split; [|split]; apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)); assumption.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End G02.
