(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec RefLayout ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxSubst FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChain FxWvC FxChMain FxChEntM.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChAllow OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanStartCert OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanStartAll OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanFinAB OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanFinEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcConvG AcSubst AcFam.

Module AsanStartAg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxImg FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart FxChain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan AsanStart.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Strategy opaque [TBLd IMGd mk_tbl_ranges check check_chain startup_res some_nonempty list_of].
Strategy expand [startup_ok_c FINALS_c].

Section ThmAg.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Variables (sp brk0 mb : word) (draw : EntryDraw) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hid : valid_id (in_uid inp).
Variables (olo ohi xlo : Z).
Hypothesis HC : olo <= OFS sp <= ohi.
Hypothesis Hxlo : 0 <= olo /\ 64 * xlo <= 200 + olo.

Let mdl := model0 sp brk0 mb LIM inp.
Let mem := m0 sp draw inp.

(* [comment removed for export] *)
#[using="Hoff Hsp Hbrk Hfit Hva Hve Hid HC Hxlo"] Theorem asan_startup_cls_ag : startup_ok_c olo ohi xlo = true -> forall T,
  (forall S' M' E' ms' model', In (S', M') (FINALS_c olo ohi xlo) -> DEN ASEGS LIM mdl mem E' S' M' ms' model' ->
     agree 17 (E0 sp brk0 draw inp) E' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mb draw LIM inp) T.
Proof. LiaFast.lf_pins (fun (Hoff Hsp Hbrk Hfit Hva Hve Hid HC Hxlo : LiaFast.U) => LiaFast.u0).
  intros Hcert T Hk.
  change (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mb draw LIM inp) with (mkCfg (ms0 sp draw inp) mdl).
  pose proof (den_entry sp brk0 mb draw LIM inp Hsp Hbrk Hfit Hva Hve Hid olo ohi xlo HC Hxlo ltac:(clear; unfold LIM; lia)) as Hd0.
  unfold startup_ok_c, FINALS_c in *.
  destruct (startup_res (S0c olo ohi xlo) TBLd IMGd) as [finals|] eqn:HS; [|cbn in Hcert; discriminate Hcert]. cbn [list_of] in Hk.
  destruct (startup_res_inv (S0c olo ohi xlo) TBLd IMGd finals HS) as (Hbi0 & Henv & Hpnt & L1 & HR0 & HL1 & Hbi1 & L2 & HR1 & HL2 & rgs' & Hpr & HCH).
  (* [comment removed for export] *)
  apply (den_seg ASEGS cfg LIM mdl mem A_wx TBLd IMGd (pos_below 17) 20 PLAN0 (S0c olo ohi xlo) [L1] (E0 sp brk0 draw inp) M0 (ms0 sp draw inp) mdl T
           TBLd_ok IMGd_ok HR0 Hd0 Hbi0 (pos_below_In 17)).
  intros L E1 ms1 mdl1 HL Hd1 Ha1. destruct HL as [<-|[]].
  (* [comment removed for export] *)
  pose proof (usp_b sp inp Hsp Hfit Hva Hve) as (U1 & U2).
  pose proof (rel_rp sp draw inp Hsp Hfit Hva Hve) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  pose proof (blk_top sp draw inp Hsp Hfit Hva Hve) as Bt.
  assert (HuE : forall E' l, agree 17 (E0 sp brk0 draw inp) E' -> lwf 17 l = true -> uE E' l = bv_unsigned (lden (E0 sp brk0 draw inp) l)).
  { intros E' l Ha Hl. unfold uE. rewrite (lden_agree 17 (E0 sp brk0 draw inp) E' l Hl Ha). reflexivity. }
  assert (Hw_ENVP : lwf 17 ENVP = true) by (vm_compute; reflexivity).
  assert (Hw_AUXV : lwf 17 AUXV = true) by (vm_compute; reflexivity).
  assert (Hw_ESZ : lwf 17 (laddc (lscale 8 ENVC) 8) = true) by (vm_compute; reflexivity).
  pose proof (u_ENVP sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uENVP. pose proof (u_AUXV sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uAUXV.
  pose proof (u_ESZ sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uESZ.
  unfold L1_ok in HL1. apply andb_prop in HL1 as [HL1 Hn1]. apply Pos.leb_le in Hn1.
  apply andb_prop in HL1 as [HL1 HwA]. apply andb_prop in HL1 as [Hpc1 HS1]. apply Z.eqb_eq in Hpc1. apply lin_eqb_eq in HS1.
  unfold env_tbl_ok in Henv. apply andb_prop in Henv as [Henv T3]. apply andb_prop in Henv as [T1 T2].
  (* [comment removed for export] *)
  apply (den_envp ASEGS cfg LIM mdl mem A_wx TBLd TBLd_ok envp_pc E1 L1 M0 ms1 mdl1 T ENVP AUXV (length (in_envp inp))).
  - unfold envp_pc. clear. lia.
  - unfold envp_pc, two64. clear. lia.
  - exact (tl_ld_ok _ _ _ _ _ _ _ T1).
  - exact (tl_addi_ok _ _ _ _ _ T2).
  - exact (tl_br_ok _ _ _ _ _ _ T3).
  - exact Hd1.
  - exact Hpc1.
  - exact HS1.
  - rewrite (HuE E1 ENVP Ha1 Hw_ENVP), uENVP. unfold two64, EC in *. clear - U1 R7 R8. lia.
  - intros w Hw. exists (ENVP, laddc (lscale 8 ENVC) 8). split; [left; reflexivity|]. cbn [fst snd].
    rewrite (HuE E1 ENVP Ha1 Hw_ENVP) in *. rewrite (HuE E1 _ Ha1 Hw_ESZ), uESZ. rewrite uENVP in *. unfold EC in *. clear - Hw R8. lia.
  - intros i Hi. rewrite (HuE E1 ENVP Ha1 Hw_ENVP), uENVP. exact (envp_words sp draw inp Hsp Hfit Hva Hve i Hi).
  - rewrite (HuE E1 ENVP Ha1 Hw_ENVP), uENVP. pose proof (envp_null sp draw inp Hsp Hfit Hva Hve) as X. unfold EC in X. exact X.
  - apply bv_eq. rewrite <- (lden_agree 17 (E0 sp brk0 draw inp) E1 AUXV Hw_AUXV Ha1), uAUXV. rewrite (HuE E1 ENVP Ha1 Hw_ENVP), uENVP.
    rewrite u_small64 by (unfold two64, EC in *; clear - U1 R7 R8; lia). unfold EC in *. clear - R8. lia.
  - exact HwA.
  - intros E2 ms2 mdl2 Hd2 Ha2.
    assert (Ha12 : agree 17 (E0 sp brk0 draw inp) E2) by (apply (agree_trans 17 _ E1 _ Ha1); exact (agree_mono 17 _ E1 E2 Hn1 Ha2)).
    (* [comment removed for export] *)
    set (S1 := envp_post L1 (envp_pc + 12) AUXV) in *.
    apply (den_seg ASEGS cfg LIM mdl mem A_wx TBLd IMGd (pos_below (s_next S1)) 20 PLAN1 S1 [L2] E2 M0 ms2 mdl2 T
             TBLd_ok IMGd_ok HR1 Hd2 Hbi1 (pos_below_In (s_next S1))).
    intros L E3 ms3 mdl3 HL Hd3 Ha3. destruct HL as [<-|[]].
    assert (Ha13 : agree 17 (E0 sp brk0 draw inp) E3) by (apply (agree_trans 17 _ E2 _ Ha12); exact (agree_mono 17 _ E2 E3 Hn1 Ha3)).
    (* [comment removed for export] *)
    unfold L2_ok in HL2. apply andb_prop in HL2 as [HL2 Hn2]. apply Pos.leb_le in Hn2. apply andb_prop in HL2 as [HL2 HwP].
    apply andb_prop in HL2 as [HL2 HA1]. apply andb_prop in HL2 as [HL2 HA0]. apply andb_prop in HL2 as [HL2 HS0].
    apply andb_prop in HL2 as [Hpc2 Hrv]. apply Z.eqb_eq in Hpc2. apply lin_eqb_eq in HS0, HA0, HA1.
    assert (Hrv' : s_resv L2 = RNone) by (destruct (s_resv L2); [reflexivity | discriminate Hrv | discriminate Hrv]).
    unfold pn_tbl_ok in Hpnt.
    apply andb_prop in Hpnt as [Hpnt P8]. apply andb_prop in Hpnt as [Hpnt P7]. apply andb_prop in Hpnt as [Hpnt P6].
    apply andb_prop in Hpnt as [Hpnt P5]. apply andb_prop in Hpnt as [Hpnt P4]. apply andb_prop in Hpnt as [Hpnt P3].
    apply andb_prop in Hpnt as [P1 P2].
    assert (Hw_P0 : lwf 17 P0 = true) by (vm_compute; reflexivity).
    assert (Hw_STR : lwf 17 (lsub RANDP P0) = true) by (vm_compute; reflexivity).
    assert (Hw_PN : lwf 17 PN_L1 = true) by (vm_compute; reflexivity).
    pose proof (u_P0 sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uP0. pose proof (u_STR sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uSTR.
    pose proof (u_PNL1 sp brk0 draw inp Hsp Hfit Hva Hve olo ohi HC) as uPN.
    pose proof (rp_str sp draw inp Hsp Hfit Hva Hve) as Hrs. pose proof (argv0_top sp draw inp Hfit Hva) as Atop.
    set (n0 := Z.of_nat (length (nth 0 (in_argv inp) []))).
    assert (HuP0 : uE E3 P0 = usp sp + 8 * AC inp + 8 * EC inp + 184) by (rewrite (HuE E3 P0 Ha13 Hw_P0); exact uP0).
    assert (Hn0 : 0 <= n0 <= 131071).
    { clear - Hva R7. unfold n0. pose proof (valid_argv_str_len (in_argv inp) 0 Hva ltac:(clear - R7; unfold AC in *; lia)). lia. }
    apply (den_pn ASEGS cfg LIM mdl mem A_wx TBLd TBLd_ok pn_pc E3 L2 M0 ms3 mdl3 T PNG P0 PN_L1 rgs' n0
             (fun i => nth (Z.to_nat i) (nth 0 (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
    + unfold pn_pc. clear. lia.
    + unfold pn_pc, two64. clear. lia.
    + exact (tl_st_ok _ _ _ _ _ _ P1).
    + exact (tl_addi_ok _ _ _ _ _ P2).
    + exact (tl_jal_ok _ _ _ _ _ P3).
    + exact (tl_st_ok _ _ _ _ _ _ P4).
    + exact (tl_addi_ok _ _ _ _ _ P5).
    + exact (tl_ld_ok _ _ _ _ _ _ _ P6).
    + exact (tl_br_ok _ _ _ _ _ _ P7).
    + exact (tl_br_ok _ _ _ _ _ _ P8).
    + exact Hd3.
    + exact Hpc2.
    + exact Hrv'.
    + exact HS0.
    + exact HA0.
    + rewrite HA1, lden_laddc. reflexivity.
    + exact Hpr.
    + rewrite HuP0. clear - U1 R7 R8. unfold AC, EC in *. lia.
    + rewrite HuP0. unfold two64. clear - U1 R7 R8 Hn0 Atop. unfold AC, EC, n0 in *. lia.
    + exact (proj1 Hn0).
    + unfold PNG. clear. lia.
    + unfold PNG, two64. clear. lia.
    + left. rewrite HuP0. unfold PNG. clear - U1 R7 R8. unfold AC, EC in *. lia.
    + intros w Hw. exists (P0, lsub RANDP P0). split; [right; left; reflexivity|]. cbn [fst snd].
      rewrite HuP0 in *. rewrite (HuE E3 _ Ha13 Hw_STR), uSTR. clear - Hw Hrs Hn0. unfold n0, AC, EC in *. lia.
    + intros i Hi. rewrite HuP0. split.
      * pose proof (argv0_byte sp draw inp Hsp Hfit Hva Hve (Z.to_nat i) ltac:(clear - Hi; unfold n0 in *; lia)) as X.
        rewrite Z2Nat.id in X by (clear - Hi; lia). exact X.
      * apply (argv0_nz inp Hva (Z.to_nat i)). clear - Hi. unfold n0 in *. lia.
    + rewrite HuP0. pose proof (argv0_byte sp draw inp Hsp Hfit Hva Hve (length (nth 0 (in_argv inp) [])) ltac:(clear; lia)) as X.
      rewrite (argv0_nul inp) in X. exact X.
    + apply bv_eq. rewrite <- (lden_agree 17 (E0 sp brk0 draw inp) E3 PN_L1 Hw_PN Ha13). unfold PN_L1. rewrite uPN.
      rewrite HuP0. rewrite u_small64 by (unfold two64; clear - U1 R7 R8 Hn0 Atop; unfold AC, EC, n0 in *; lia).
      clear. unfold n0, L0. lia.
    + exact HwP.
    + intros E4 ms4 mdl4 Hd4 Ha4.
      assert (Ha14 : agree 17 (E0 sp brk0 draw inp) E4) by (apply (agree_trans 17 _ E3 _ Ha13); exact (agree_mono 17 _ E3 E4 Hn2 Ha4)).
      apply (chain_sound_ag ASEGS cfg LIM mdl mem TBLd IMGd A_wx A_segb Hoff A_respos A_reswf TBLd_ok IMGd_ok TBLd_ecall
               CH1 (pn_post L2 (pn_pc + 32) PN_L1 rgs') M0 finals HCH E4 ms4 mdl4 T Hd4).
      intros S' M' E' ms' model' Hin Hd' Ha'. apply (Hk S' M' E' ms' model' Hin Hd').
      apply (agree_trans 17 _ E4 _ Ha14). apply (agree_mono 17 (s_next (pn_post L2 (pn_pc + 32) PN_L1 rgs')) E4 E'); [|exact Ha']. cbn [pn_post s_next]. lia.
Qed.
End ThmAg.
(* [comment removed for export] *)
End AsanStartAg.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTBridge.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTop0.AsanStartAg OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTBridge.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition FRZ0 : list (lin * lin) := Eval vm_compute in sm_frz M1x.
Definition frz_keep (E : valu) (m m' : word -> option byte) : Prop :=
  forall p, In p FRZ0 -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> m' (Z_to_bv 64 w) = m (Z_to_bv 64 w).

Fixpoint frz_eqb (x y : list (lin * lin)) : bool :=
  match x, y with
  | [], [] => true
  | (a, b) :: x', (a', b') :: y' => (lin_eqb a a' && lin_eqb b b' && frz_eqb x' y')%bool
  | _, _ => false
  end.
Lemma frz_eqb_eq : forall x y, frz_eqb x y = true -> x = y.
Proof.
  induction x as [|[a b] x IH]; intros [|[a' b'] y] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1, H2. subst. f_equal. exact (IH y H3).
Qed.
(* [comment removed for export] *)
Lemma fins_ok : forallb (fun F => (Pos.leb 17 (s_next (fst F)) && frz_eqb (sm_frz (snd F)) FRZ0)%bool) (FINC ++ FINA ++ FINB) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma FRZ0_wf : forallb (fun p => (lwf 17 (fst p) && lwf 17 (snd p))%bool) FRZ0 = true. Proof. vm_compute. reflexivity. Qed.

Lemma frz_agree : forall E E' (m m' : word -> option byte), agree 17 E E' ->
  (forall p, In p FRZ0 -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> m' (Z_to_bv 64 w) = m (Z_to_bv 64 w)) ->
  frz_keep E' m m'.
Proof.
  intros E E' m m' Ha H p Hp w Hw. apply (H p Hp w).
  pose proof FRZ0_wf as X. rewrite forallb_forall in X. pose proof (X p Hp) as Xp. apply andb_prop in Xp as [W1 W2].
  unfold uE in *. rewrite (lden_agree 17 E E' _ W1 Ha), (lden_agree 17 E E' _ W2 Ha). exact Hw.
Qed.

Section Top0.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.

(* [comment removed for export] *)
Definition main_ok (sp brk0 mb : word) (draw : EntryDraw) (inp : ProcInput) (T : TSet) : Prop :=
  forall mem0 E ms model, agree 17 (E0 sp brk0 draw inp) E ->
  DEN ASEGS LIM (model0 sp brk0 mb LIM inp) mem0 E TMAIN MMAIN ms model -> HA E MMAIN AMAIN mem0 ->
  frz_keep E (m0 sp draw inp) mem0 -> realizes_cfg ASEGS cfg (mkCfg ms model) T.

#[using="Hoff"] Theorem asan_from_main : forall (sp brk0 mb : word) (draw : EntryDraw) (inp : ProcInput) T,
  valid_sp sp -> valid_brk ASEGS brk0 -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_argv (in_argv inp) ->
  valid_envp (in_envp inp) -> valid_id (in_uid inp) ->
  main_ok sp brk0 mb draw inp T ->
  realizes_cfg ASEGS cfg (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mb draw LIM inp) T.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0).
  intros sp brk0 mb draw inp T Hsp Hbrk Hfit Hva Hve Hid Hmain.
  (* [comment removed for export] *)
  assert (K : forall S' M' E' ms' model', In (S', M') FINALS_ALL ->
            DEN ASEGS LIM (model0 sp brk0 mb LIM inp) (m0 sp draw inp) E' S' M' ms' model' -> agree 17 (E0 sp brk0 draw inp) E' ->
            realizes_cfg ASEGS cfg (mkCfg ms' model') T).
  { intros S' M' E' ms' model' Hin Hd Hag. rewrite finals_all_eq in Hin.
    pose proof bridge_all as Hb. rewrite forallb_forall in Hb. specialize (Hb (S', M') Hin).
    pose proof fins_ok as Hf. rewrite forallb_forall in Hf. specialize (Hf (S', M') Hin). apply andb_prop in Hf as [H17 Hfz].
    apply Pos.leb_le in H17. apply frz_eqb_eq in Hfz. cbn [fst snd] in H17, Hfz.
    apply (tm_handoff cfg (model0 sp brk0 mb LIM inp) (S', M') Hb (m0 sp draw inp) E' ms' model' T Hd H17).
    intros E'' mem0' ms'' model'' Ha2 Hfs Hd'' HA''.
    apply (Hmain mem0' E'' ms'' model''); [exact (agree_trans 17 _ E' _ Hag Ha2) | exact Hd'' | exact HA'' |].
    apply (frz_agree E' E'' (m0 sp draw inp) mem0' Ha2). intros p Hp w Hw. cbn [snd] in Hfs. apply (Hfs p); [rewrite Hfz; exact Hp | exact Hw]. }
  pose proof (ofs_b sp inp Hsp Hfit Hva Hve) as (O1 & O2 & O3 & O4 & O5).
  unfold FINALS_ALL in K.
  assert (Hq : OFS sp = 16 * (OFS sp / 16)) by (pose proof (Z.div_mod (OFS sp) 16 ltac:(lia)); lia).
  destruct (Z_le_gt_dec (OFS sp) 4080) as [Hc|Hc]; [|destruct (Z_le_gt_dec (OFS sp) 4176) as [Hc'|Hc']].
  - apply (asan_startup_cls_ag cfg Hoff sp brk0 mb draw inp Hsp Hbrk Hfit Hva Hve Hid 176 4080 5 ltac:(clear - O4 Hc; lia) ltac:(clear; lia)
             startup_ok_C T).
    intros S' M' E' ms' model' Hin Hd Hag. apply (K S' M' E' ms' model'); [|exact Hd | exact Hag]. apply in_or_app. left. exact Hin.
  - apply (asan_startup_cls_ag cfg Hoff sp brk0 mb draw inp Hsp Hbrk Hfit Hva Hve Hid 4096 4176 67 ltac:(clear - O4 Hc Hc' Hq; lia) ltac:(clear; lia)
             startup_ok_A T).
    intros S' M' E' ms' model' Hin Hd Hag. apply (K S' M' E' ms' model'); [|exact Hd | exact Hag]. apply in_or_app. right. apply in_or_app. left. exact Hin.
  - apply (asan_startup_cls_ag cfg Hoff sp brk0 mb draw inp Hsp Hbrk Hfit Hva Hve Hid 4192 4256 68 ltac:(clear - O4 Hc Hc' Hq; lia) ltac:(clear; lia)
             startup_ok_B T).
    intros S' M' E' ms' model' Hin Hd Hag. apply (K S' M' E' ms' model'); [|exact Hd | exact Hag]. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.
End Top0.
(* [comment removed for export] *)
