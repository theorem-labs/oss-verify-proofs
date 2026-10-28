(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_HStKit LbB_VecT LbB_HEmpS LbB_HEmpD LbB_HEmpI LbB_HEmpR LbB_HEmpNd
  LbB_HRehK LbB_HRehD LbB_HRehL LbB_HRehE LbB_HRehB.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_TopKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition srRA : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition KN_GOTR : list kentry := [KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE)].
Definition KNRA : list kentry :=
  KN_GOTR ++ [KWr (SA (EVar 34) (-64)) (ELit 64); KRange (EVar 33) 1 (2 ^ 28); KRange (EVar 34) (2 ^ 45) (2 ^ 47)].
Definition SCR_RA := SCR [] [] [].
Definition runRA :=
  Eval vm_compute in (sym_exec ASEGS 40 true [AOPNEW] SCR_RA (SS (reh_entry EMP_U32) srRA [] (kn_fix 20 [AOPNEW] SCR_RA (reh_entry EMP_U32) srRA KNRA 50) 50) []).
Definition srRA' : list expr := Eval cbv in (let '(ss, _, _) := runRA in s_regs ss).
Definition lgRA : list sentry := Eval cbv in (let '(ss, _, _) := runRA in s_log ss).
Definition tlRA : list expr := [EVar 21; EVar 20; EVar 19; EVar 18; EVar 9; EVar 8; EVar 1].
Lemma lgRA_c8 : lgRA = c8log (EVar 34) (-56) tlRA.
Proof. reflexivity. Qed.

Section RehA.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.

  Theorem reh_specA : reh_stmt H EMP_U32.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LB0 LBm LF
      obj bl bc ents lo B shi errv
      VIS FRZ Ha0 Ha1 U SH PE PM AD WR LFO OCE OBL BCL RH KR AL0 RS RC RL RICM TRK RA SPB BR SP16 ST ACL LOR ERR MI TPV RAE AC RF S0 SHI OWN.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr. fold spz in Hspr. clearbody spz.
    subst a0 a1 sp.
    set (n := bseq_next bc) in *.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold AREH_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    assert (SPHI : spz <= 2 ^ 47) by (destruct S0 as (g & _ & Hg & _); unfold AAPP_HI in Hg; lia).
    assert (SPL : 2 ^ 45 <= spz - 64) by (clear - ACF1 ACL LOR'; lia).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoal.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    destruct (bseq_next_factsE bc (u_bseq U) BCL) as (HnB & Hbcn & Hn28 & _). fold n in HnB, Hbcn, Hn28.
    assert (Hn0 : 0 < n) by (clear - BCR Hbcn; lia).
    pose proof (ACONST_shbase m AC) as [CG CS].
    pose proof (obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    remember (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).

    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 n; Z_to_bv 64 spz]).
    assert (HR : regs_ok E srRA R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (KG1 : kentry_ok asegs E m (KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL))).
    { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL)));
        [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
    assert (KG2 : kentry_ok asegs E m (KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE))).
    { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE)));
        [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
    assert (KW : kentry_ok asegs E m (KWr (SA (EVar 34) (-64)) (ELit 64))).
    { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; clear - ACL LOR' ACF1; lia
                         | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    assert (KQ1 : kentry_ok asegs E m (KRange (EVar 33) 1 (2 ^ 28))) by (cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - Hn0 Hn28; lia).
    assert (KQ2 : kentry_ok asegs E m (KRange (EVar 34) (2 ^ 45) (2 ^ 47))) by (cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPHI; lia).
    assert (HK : know_ok asegs E m (kn_fix 20 [AOPNEW] SCR_RA (reh_entry EMP_U32) srRA KNRA 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [exact KG1|]. apply Forall_cons; [exact KG2|]. apply Forall_cons; [exact KW|].
      apply Forall_cons; [exact KQ1|]. apply Forall_cons; [exact KQ2|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R (reh_entry EMP_U32) m (seg_rom asegs) HR HK 40%nat [AOPNEW] SCR_RA 50%N.
    { split_scs. }
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) => change mm with (mem_denot E m lgRA) in Hms end.
    change (log_flat E lgRA) in Hlf.
    set (M1 := mem_denot E m lgRA) in Hms.

    assert (MU1 : munch [(spz - 64, spz)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|]. unfold lgRA. clear - SPL SPHI Hspr.
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (CE : map (fun v => C8 (edenot E v)) tlRA = [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (unfold E, tlRA; subst R; reflexivity).
    assert (FR1 : RFRAME ra s0 s1 s2 s3 s4 s5 spz M1).
    { unfold RFRAME. rewrite <- CE.
      subst M1. rewrite lgRA_c8. rewrite lgRA_c8 in Hlf.
      apply rw_cells_c8log; [exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia |].
      destruct ST as (STa & STb & STc). cbn [tlRA length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul].
      split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (STc (spz - 56 + i) ltac:(lia))). }

    assert (W1 : aclient_write_ok H LB (spz - 64, spz)) by (left; cbn; lia).
    assert (W2 : afs_write_ok H LF (spz - 64, spz)).
    { left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. clear - FB1 FB2 ACL LOR' ACF1. unfold AIMG_TOP in FB1. lia. }
    assert (W3 : aconst_ok (spz - 64, spz)).
    { apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; clear - SPL; lia | right; left; clear - SPL; lia]. }
    assert (W4 : stack0_ok (spz - 64, spz)) by (left; cbn; unfold AHI_LO; clear - SPL; lia).
    destruct (client_frame H HH s LB LF B [(spz - 64, spz)] m M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
      as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]).
    assert (ST1 : stk asegs M1 lo spz) by (eapply LbB_TopKit.stk_wmono; [exact ST | exact WM1 | clear - ACL ACF1; lia]).
    assert (EA : errno_addr tp = 7100340) by (subst tp; unfold errno_addr; rewrite u64_of_Z by (unfold ATP; lia); reflexivity).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { rewrite EA in ERR |- *. eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; clear - SPL; lia]. }
    assert (XP1 : xpres H LB spz [] m M1).
    { eapply (xpres_munch_mixed H HH s LB LB [] spz [] [(spz - 64, spz)] m m M1);
        [apply xpres_refl | exact RH | rewrite app_nil_r; apply Permutation_refl | lia | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
    assert (OWN1 : lb_own LBm M1) by exact (lb_own_wmono _ _ _ OWN WM1).

    pose proof (msteps_full asegs _ _ Hms FHF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 19%bv G19.
    rewrite (w_addm spz (-64)) in G2 by lia. replace (spz + -64) with (spz - 64) in G2 by lia.
    rewrite (w_mul 8 n) in G10 by lia.
    change (getr R' 19 = Z_to_bv 64 SHBASE) in G19.
    rewrite G1, G2, G8, G9, G10, G19 in HRe.
    eapply (sr_blk_eqR H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    assert (AOK : as_alloc_ok H s LB (8 * n)) by exact (rt_bp_live H HHB s LB M1 (8 * n) RH1 ltac:(lia) RS RC RL).
    assert (CM : as_Cm H (8 * n) <= as_AL H s) by (rewrite (proj2 (rt_bp_cost H HHB) (8 * n)); exact RICM).
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 8 * n) (LB := LB) (lo := lo) (B := B) (errv := errv);
        [ exact VIS1 | exact RH1 | exact KR1 | exact AOK | exact CM | exact RA1
        | rewrite u64_of_Z by lia; lia
        | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs M1 lo (spz - 64) spz ST1 ltac:(lia)))
        | exact ACL | rewrite u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | exact ERR1 | exact MI1 | exact TPV | rewrite u64_of_Z by lia; Z.div_mod_to_equations; lia
        | exact AC1 | reflexivity | lia ]. }
    intros [msF2 mo2] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & p & junk & pid & s'
                      & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    first [rewrite (ret_pc_even R_NEWRET ltac:(unfold R_NEWRET; lia) eq_refl) in VIS2 | rewrite (ret_pc_even 1027308 ltac:(lia) eq_refl) in VIS2].
    rewrite u64_of_Z in AP2, ST2 by lia.
    rewrite (proj2 (rt_bp_cost H HHB) (8 * n)) in AL2.
    assert (NI : ~ In pid (map blk_id LB)).
    { pose proof (ah_nodup H HH _ _ _ RH2) as ND. cbn [map blk_id Datatypes.fst] in ND. inversion ND; subst. assumption. }

    assert (XP12 : xpres H LB (spz - 64) [] M1 m2) by exact (xpres_of_apres H _ _ [] _ _ AP2).
    assert (XP02 : xpres H LB spz [] m m2).
    { eapply xpres_trans; [exact XP1|]. eapply (xpres_weaken H); [exact XP12 | lia | intros b Hb; exact Hb | intros a Ha; destruct Ha]. }
    assert (FR2 : RFRAME ra s0 s1 s2 s3 s4 s5 spz m2) by (unfold RFRAME in FR1 |- *; eapply (apres_rw_cells H); [exact AP2 | exact FR1 | left; lia]).
    assert (ST2' : stk asegs m2 lo spz).
    { apply (stk_merge asegs m2 lo (spz - 64) spz); [exact ST2 | | clear - ACL LOR'; lia].
      eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs M1 lo (spz - 64) spz ST1 ltac:(clear - ACL LOR'; lia))) | lia]. }
    assert (RF2 : as_RFS H LF m2) by exact (RFS_via_apres H HH LF LB _ M1 m2 RF1 AP2).
    assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact XP12 | exact S01 | apply Forall_nil]).
    assert (OWN2 : lb_own LBm m2).
    { eapply (lb_own_apres H); [exact OWN1 | exact AP2 | intros b Hb; apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact Hb]. }

    assert (HOX : forall i, 0 <= i < 40 -> xclient H LB spz [] (obj + i)).
    { intros i Hi. split; [|intros K; exact K]. right; right; right; right; left. unfold AFS_SIZE in *. lia. }
    assert (INm : forall q k, In (q, k) (umap_blocks 24 bl bc ents) -> In (q, k) (lbl LBm)).
    { intros q k Hq. apply (Permutation_in _ (Permutation_sym PM)). exact Hq. }
    assert (INL : forall q k, In (q, k) (lbl LBm) -> In (q, k) (lbl LB)).
    { intros q k Hq. destruct (lbl_in_inv _ _ _ Hq) as (qi & Qi). unfold lbl. apply in_map_iff. exists (qi, q, k). split; [reflexivity|].
      apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. exact Qi. }
    assert (U2 : umapx MI_A 24 (nval24 ASEGS) (lbl LB) m2 obj bl bc ents).
    { eapply (umapx_xp H 24 Z (nval24 ASEGS) LB spz [] LB LB m m2 obj); [exact (nval24_agree ASEGS) | lia | exact XP02 | exact U | exact HOX |].
      apply (blkx_intro H). intros q k Hq. split; [exact (INL q k (INm q k Hq))|]. split; [exact (INL q k (INm q k Hq))|]. intros a _ K. exact K. }
    assert (SH2 : umap_sh m2 24 (bl, bc, ents)).
    { eapply (umap_sh_xp H); [exact XP02 | exact SH |]. apply (blksh_intro H). intros q k Hq. split; [exact (INL q k (INm q k Hq)) | intros a _ K; exact K]. }
    assert (AD2 : addressable m2 obj 40).
    { eapply (addressable_xp H); [exact XP02 | exact AD |]. intros a Ha. split; [|intros K; exact K].
      right; right; right; right; right; left.
      unfold sh, nsh in Ha |- *. clear - Ha OB1 OB2 Hoal Ho0. Z.div_mod_to_equations. lia. }
    assert (WR2 : wr_at asegs m2 obj 40).
    { eapply xpres_wr_at; [exact XP02 | exact WR |]. split; [right; right; right; right; left; unfold AFS_SIZE in *; lia | apply Forall_nil]. }
    assert (HDR : agree_on m m2 obj 40) by (eapply (agree_xp H); [exact XP02 | exact HOX | lia | lia]).
    assert (NODES : forall e, In e ents -> agree_on m m2 (HRehashModel.addr Z e) 24).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U He) as (He0 & He1 & _).
      assert (INe : In (HRehashModel.addr Z e, 24) (lbl LB)).
      { apply INL. apply INm. unfold umap_blocks. apply in_or_app. right. apply in_map_iff. exists e. split; [destruct e as [q [k v]]; reflexivity | exact He]. }
      destruct (lbl_in_inv _ _ _ INe) as (qe & Qe).
      eapply (agree_xp H); [exact XP02 | | lia | lia].
      intros i Hi. split; [|intros K; exact K]. right; right; left. exists (qe, HRehashModel.addr Z e, 24). split; [exact Qe | cbn; lia]. }
    destruct SH2 as [SHb SHn]. unfold t3a, t3b, t3c in SHb, SHn. cbn [fst snd] in SHb, SHn.
    eapply (stage_b H HHB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz s LB0 LF obj bl bc ents lo B shi m mo LB
              U BCL RICM OCE LFO ACL LOR TPV SPB
              s' msF2 mo2 m2 F fc t0' t1' t2' _ a2' a3' a4' a5' a6' a7' s2 s4 s5 t3' t4' t5' t6' errv2 LB LBm pid p junk);
      [ exact VIS2 | exact FRZ | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]
      | exact FR2 | exact SP16 | exact SPL | exact SPHI | exact RAE | exact MI2 | exact ST2' | exact ERR2 | exact RA2
      | exact NODES | exact HDR
      | intros Hb; exact (SHb Hb) | exact AD2 | intros [q [k v]] He; exact (SHn q k v He) | exact WR2
      | exact RH2 | exact NI | exact PE | exact PM | exact OWN2 | exact CB2 | exact ADDR
      | eapply (xpres_weaken H); [exact XP02 | lia | intros b Hb; apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb | intros a Ha; destruct Ha]
      | exact RF2 | exact AC2 | exact S02 | subst n; clear - AL2; lia | exact TRK ].
  Qed.
End RehA.
