(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_VecT LbB_HEmpS LbB_HEmpK LbB_HEmpD LbB_HEmpI LbB_HEmpI2
  LbB_HEmpI3 LbB_HEmpI4 LbB_HEmpX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_RC : Z := 0xfaaa0.
Definition srRC : list expr :=
  srs sr_id [(2%bv, EVar 34); (8%bv, EVar 32); (9%bv, ELit SHBASE); (10%bv, EVar 32); (11%bv, EVar 33)].
Definition KNRC : list kentry :=
  [KWord (SA (EVar 34) 0) 8 (EVar 36); KWord (SA (EVar 34) 8) 8 (EVar 37); KWord (SA (EVar 34) 16) 8 (EVar 32);
   KWord (SA (EVar 34) 24) 8 (ELit E_IDX)].

Lemma inZ_bseq : forall x, existsb (Z.eqb x) BSEQ = true -> In x BSEQ.
Proof.
  intros x Hx. apply existsb_exists in Hx. destruct Hx as (y & Hy & E). apply Z.eqb_eq in E. subst y. exact Hy.
Qed.

Lemma bseq_next_factsE : forall bc, In bc BSEQ -> bc <> BSEQ_LAST ->
  In (bseq_next bc) BSEQ /\ bc < bseq_next bc /\ 8 * bseq_next bc <= 2 ^ 28
  /\ ((bc = 0 /\ bseq_next bc = 2) \/ (3 <= bseq_next bc /\ Z.land (bseq_next bc) (bseq_next bc - 1) <> 0)).
Proof.
  intros bc Hin Hlast. unfold BSEQ in Hin. unfold BSEQ_LAST in Hlast.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | match goal with |- context [bseq_next ?b] => let v := eval vm_compute in (bseq_next b) in change (bseq_next b) with v end;
              split; [apply inZ_bseq; vm_compute; reflexivity | split; [lia | split; [lia | first [left; split; reflexivity | right; split; [lia | vm_compute; discriminate]]]]] ] |]).
  destruct Hin.
Qed.

Lemma lbl_split : forall (LBm : list block) p n L, Permutation (lbl LBm) ((p, n) :: L) ->
  exists q LBr, Permutation LBm ((q, p, n) :: LBr) /\ Permutation (lbl LBr) L.
Proof.
  intros LBm p n L PM.
  destruct (lbl_in_inv LBm p n (Permutation_in _ (Permutation_sym PM) (or_introl eq_refl))) as (q & Q).
  destruct (in_split _ _ Q) as (l1 & l2 & ->). exists q, (l1 ++ l2). split; [apply Permutation_sym, Permutation_middle|].
  apply (Permutation_cons_inv (a := (p, n))). eapply perm_trans; [|exact PM].
  unfold lbl. rewrite !map_app. cbn [map]. cbn [fst snd]. apply Permutation_middle.
Qed.

Section EmpR.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis REH : reh_stmt H EMP_U32.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation QIx := (QI H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).

  Lemma xpres_SHADE : forall LBx SP X m m' A sbs,
    xpres H LBx SP X m m' -> SHAD m A sbs -> xclient_range H LBx SP X (sh A) (Z.of_nat (length sbs)) -> SHAD m' A sbs.
  Proof.
    intros LBx SP X m m' A sbs XP (A0 & A8 & [UB UW]) XC. split; [exact A0|]. split; [exact A8|].
    split; [eapply xpres_bytes_at; eauto| eapply xpres_wr_at; eauto].
  Qed.
  Lemma xpres_addressableE : forall LBx SP X m m' A n,
    xpres H LBx SP X m m' -> addressable m A n -> xclient_range H LBx SP X (sh A) (nsh n) -> addressable m' A n.
  Proof.
    intros LBx SP X m m' A n XP [Hn SH] XC. split; [exact Hn|]. eapply xpres_SHADE; eauto. rewrite shadow_of_length by lia. exact XC.
  Qed.

  Definition GPRE (s : as_St H) (mo : Model) (m : mem) (errv' : word) (LB' LBm : list block) (p : Z) : Prop :=
    as_MPRES H mo0 mo
    /\ FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz m /\ spz mod 16 = 0 /\ 2 ^ 45 <= spf spz /\ spz <= 2 ^ 47
    /\ bv_unsigned ra mod 2 = 0
    /\ mem_inv asegs m /\ stk asegs m lo spz /\ rw_cells asegs m (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m B
    /\ tp = Z_to_bv 64 ATP /\ aceil <= spf spz /\ aceil <= lo /\ lo <= spf spz - AREH_STACK /\ spz <= shi /\ spz <= B /\ B < 2 ^ 64
    /\ map_live_frame LF obj /\ obj + 40 <= aceil
    /\ umapx MI_A 24 (nval24 ASEGS) (lbl LB') m obj bl bc ents /\ umap_sh m 24 (bl, bc, ents)
    /\ (bc = 0 \/ Zlength ents = bc) /\ bc <> BSEQ_LAST /\ Zlength ents + 1 < 2 ^ 24 /\ 0 <= key < 2 ^ 32
    /\ addressable m obj 40 /\ wr_at asegs m obj 40
    /\ (forall b, In b LB' -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj)
    /\ 0 < p /\ p + 24 <= 2 ^ 47 /\ p mod 16 = 0 /\ apart p 24 obj 40
    /\ (forall q n, In (q, n) (umap_blocks 24 bl bc ents) -> apart p 24 q n)
    /\ rw_cells asegs m p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0)] /\ addressable m p 24
    /\ as_RHEAP H s LB' m /\ Permutation LB' (LB0 ++ LBm)
    /\ Permutation (lbl LBm) ((p, 24) :: umap_blocks 24 bl bc ents)
    /\ lb_own LBm m
    /\ xpres H LB0 spz [(obj, obj + 40)] m0 m
    /\ as_RFS H LF m /\ ACONST m /\ stack0 m lo shi
    /\ as_AL H s >= as_AL H sk0 /\ 0 <= as_AL H s
    /\ lb_small LB' + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX /\ Z.of_nat (length LB') + 1 <= RT_CNT_MAX
    /\ nlarge LB' + nlg (8 * bseq_next bc) <= RT_LARGE_MAX /\ ICM (8 * bseq_next bc) <= as_AL H s
    /\ trace_ok (as_TR H) APC0_FREE [emp_del_ra EMP_U32].

  Lemma stage_rcall : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz - 32)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 SHBASE) (Z_to_bv 64 obj)
                             (Z_to_bv 64 (bseq_next bc)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20
                             (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p)
                             (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_RC) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    GPRE s mo m errv' LB' LBm p ->
    rw_cells asegs m (spf spz - 32) [C8 (Z_to_bv 64 (obj + 24)); C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 E_IDX)] ->
    as_SR H QIx (mkCfg msF mo).
  Proof using All.
    intros s msF mo m F fc y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR GP HF.
    destruct GP as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACS & ACL & LOR & SHI & SPB & BR & LFO & OCE
                    & U & SH & GROW & BCL & SZR & KR32 & AD & WR & OBL & P0 & P1 & P16 & PO & PA & NC & ADP
                    & RH & PE & PM & OWN & XP & RF & AC & S0 & AL & AL0 & RS & RC & RL & RICM & TRK).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof LOR as LOR'. unfold AREH_STACK, AOPNEW_STACK, AMALLOC_STACK, spf in LOR'.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    destruct (bseq_next_factsE bc (u_bseq U) BCL) as (HnB & Hbcn & Hn28 & _).
    destruct (u_hdr U) as [_ Cbc _ _ _ _].
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    pose proof (obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).

    destruct (lbl_split LBm p 24 _ PM) as (qp & LBmr & PMs & PMr).
    set (LB0r := LB0 ++ [(qp, p, 24)]).
    assert (PEr : Permutation LB' (LB0r ++ LBmr)).
    { eapply perm_trans; [exact PE|]. unfold LB0r. rewrite <- app_assoc. cbn [app]. apply Permutation_app_head. exact PMs. }
    assert (QPL : In (qp, p, 24) LB') by (apply (Permutation_in _ (Permutation_sym PEr)); apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (ah_blocks H HH _ _ _ _ RH QPL) as (_ & _ & _ & PIM & PCE & _ & PAPP).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in PIM, PCE, PAPP. unfold AIMG_TOP in PIM.
    assert (OWNr : lb_own LBmr m) by (eapply lb_own_incl; [|exact OWN]; intros b Hb; apply (Permutation_in _ (Permutation_sym PMs)); right; exact Hb).
    assert (WRP : wr_at asegs m p 24).
    { pose proof (lb_own_In LBm m _ OWN (Permutation_in _ (Permutation_sym PMs) (or_introl eq_refl))) as W. exact W. }
    unfold FRAME, spf in FR. unfold spf in *.

    remember (mkR y1 (Z_to_bv 64 (spz - 96 - 32)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 SHBASE) (Z_to_bv 64 obj)
                  (Z_to_bv 64 (bseq_next bc)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20
                  (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p)
                  (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 (bseq_next bc); Z_to_bv 64 (spz - 96 - 32); Z_to_bv 64 bc;
                        Z_to_bv 64 (obj + 24); Z_to_bv 64 (obj + 8)]).
    assert (HR : regs_ok E srRC R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]).
      apply Forall_nil. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    assert (HK : know_ok asegs E m (kn_fix 20 [reh_entry EMP_U32] (SCR [false] [EVar 35] []) E_RC srRC KNRC 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell HF 0%nat (C8 (Z_to_bv 64 (obj + 24)))|].
      apply Forall_cons; [kword_cell HF 8%nat (C8 (Z_to_bv 64 (obj + 8)))|].
      apply Forall_cons; [kword_cell HF 16%nat (C8 (Z_to_bv 64 obj))|].
      apply Forall_cons; [kword_cell HF 24%nat (C8 (Z_to_bv 64 E_IDX))|].
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R E_RC m (seg_rom asegs) HR HK 40%nat [reh_entry EMP_U32] (SCR [false] [EVar 35] []) 50%N.
    { clear - E Cbc GZO Ho0 Ho1 BCR Hbcn Hn28 SPL SPH. split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 18%bv G18.
    assert (G1' : getr R' 1 = Z_to_bv 64 E_IDX) by (rewrite G1; reflexivity).
    assert (G2' : getr R' 2 = Z_to_bv 64 (spz - 96)) by (rewrite G2, w_add by lia; f_equal; lia).
    rewrite G1', G2', G8, G9, G10, G11, G18 in HRe. clear G1 G2.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    eapply (ah_seq H HH).
    { eapply (REH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF1 m mo1 s LB' LB0r LBmr LF obj bl bc ents lo B shi errv');
        [ exact VIS1 | exact FRZ | reflexivity | reflexivity | exact U | exact SH | exact PEr | exact PMr | exact AD | exact WR | exact LFO
        | exact OCE | exact OBL | exact BCL | exact RH | exact KR1 | exact AL0 | exact RS | exact RC | exact RL | exact RICM | exact TRK
        | exact RA | rewrite u64_of_Z by lia; lia | exact BR
        | rewrite u64_of_Z by lia; replace (spz - 96) with (spz + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact SP16
        | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs m lo (spz - 96) spz ST ltac:(lia)))
        | exact ACL | rewrite u64_of_Z by lia; exact LOR | exact ERR | exact MI | exact TPV | unfold E_IDX; rewrite u64_of_Z by lia; reflexivity
        | exact AC | exact RF | exact S0 | rewrite u64_of_Z by lia; lia | exact OWNr ]. }
    intros [msF2 mo2] POST2.
    destruct POST2 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & s2'
                       & LB2 & LBm2 & F2 & fc2 & bl2 & ents2 & VIS2 & FRZ2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & U2 & SH2 & PERM2
                       & AD2 & WR2 & RH2 & PE2 & PM2 & OWN2 & XP2 & RF2 & AC2 & S02 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite u64_of_Z in ST2, XP2 by lia.
    rewrite (ret_pc_even E_IDX ltac:(unfold E_IDX; lia) eq_refl) in VIS2.

    assert (XPr : xpres H LB0r (spz - 96) [(obj, obj + 40)] m m2) by exact XP2.
    assert (QPL2 : In (qp, p, 24) LB2) by (apply (Permutation_in _ (Permutation_sym PE2)); apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (XCP : forall a n, p <= a -> a + n <= p + 24 -> 0 <= n -> xclient_range H LB0r (spz - 96) [(obj, obj + 40)] a n).
    { intros a n Ha Han Hn. split.
      - right; right; left. exists (qp, p, 24). split; [unfold LB0r; apply in_or_app; right; left; reflexivity | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; lia].
      - apply Forall_cons; [cbn [Datatypes.fst Datatypes.snd]; unfold apart in PO; lia | apply Forall_nil]. }
    assert (NC2 : rw_cells asegs m2 p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0)])
      by (eapply xpres_rw_cells; [exact XPr | exact NC | apply XCP; cbn; lia]).
    assert (ADP2 : addressable m2 p 24).
    { eapply xpres_addressableE; [exact XPr | exact ADP |]. split.
      - right; right; right; left. exists (qp, p, 24). split; [unfold LB0r; apply in_or_app; right; left; reflexivity | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; lia].
      - apply Forall_cons; [|apply Forall_nil]. cbn [Datatypes.fst Datatypes.snd].
        pose proof (sh_nsh_high p 24 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SN.
        assert (ASHADOW_BASE <= sh p) by (unfold sh; pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia).
        unfold aapp, aapp_lo, aapp_hi in VA. unfold ASHADOW_BASE, AHI_LO, ALOWSH_LO in *. lia. }
    assert (WRP2 : wr_at asegs m2 p 24) by (eapply xpres_wr_at; [exact XPr | exact WRP | apply XCP; lia]).
    assert (FR2 : rw_cells asegs m2 (spz - 96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply xpres_rw_cells; [exact XPr | exact FR |]. split; [left; lia|].
      apply Forall_cons; [|apply Forall_nil]. cbn [Datatypes.fst Datatypes.snd cells_size csize Z.of_nat]. unfold AFS_SIZE in *. lia. }
    assert (ST2' : stk asegs m2 lo spz).
    { pose proof (stk_release asegs m2 lo (spz - 96) _ ST2 FR2 ltac:(lia)) as X.
      replace (spz - 96 + Z.of_nat (cells_size _)) with spz in X by (cbn [cells_size csize]; lia). exact X. }

    assert (PA2 : forall q n, In (q, n) (umap_blocks 24 bl2 (bseq_next bc) ents2) -> apart p 24 q n).
    { intros q n Hq. destruct (lbl_in_inv LBm2 q n (Permutation_in _ (Permutation_sym PM2) Hq)) as (qi & Qi).
      assert (QiL : In (qi, q, n) LB2) by (apply (Permutation_in _ (Permutation_sym PE2)); apply in_or_app; right; exact Qi).
      assert (Hne : qi <> qp).
      { intros ->. pose proof (ah_nodup H HH _ _ _ RH2) as ND.
        pose proof (Stdlib.Sorting.Permutation.Permutation_NoDup (Permutation_map blk_id PE2) ND) as ND'. rewrite map_app in ND'.
        apply (nodup_app_disj _ _ _ qp ND').
        - apply in_map_iff. exists (qp, p, 24). split; [reflexivity | unfold LB0r; apply in_or_app; right; left; reflexivity].
        - apply in_map_iff. exists (qp, q, n). split; [reflexivity | exact Qi]. }
      pose proof (ah_disj H HH _ _ _ _ _ RH2 QPL2 QiL (not_eq_sym Hne)) as D. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in D.
      unfold apart. lia. }
    eapply (stage_idx H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
              s2' msF2 mo2 m2 F2 fc2) with (LB' := LB2) (LBm' := (qp, p, 24) :: LBm2) (p := p) (bl2 := bl2) (bc2 := bseq_next bc)
            (ents2 := ents2) (rehashed := true) (errv' := errv2); [exact VIS2 | exact FRZ2 | exact KR2 |].

    unfold IPRE.
    split; [eapply (ah_mpres_trans H HH); [exact MP | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]]|].
    split; [unfold FRAME, spf; exact FR2|].
    split; [exact SP16|]. split; [unfold spf; lia|]. split; [exact SPH|]. split; [exact RAE|].
    split; [exact MI2|]. split; [exact ST2'|]. split; [exact ERR2|]. split; [exact RA2|].
    split; [exact TPV|]. split; [unfold spf; lia|]. split; [exact LFO|].
    split; [exact U2|]. split; [exact SH2|]. split; [exact PERM2|].
    split; [lia|]. split; [pose proof (u_load U) as ULD; lia|]. split; [exact KR32|].
    split; [exact AD2|]. split; [exact WR2|].
    split; [exact P0|]. split; [exact P1|]. split; [exact P16|]. split; [exact PO|]. split; [exact PA2|].
    split; [exact NC2|]. split; [exact ADP2|].
    split; [intros X; discriminate X|]. split; [intros _; split; [exact GROW | reflexivity]|].
    split; [exact RH2|].
    split; [eapply perm_trans; [exact PE2|]; unfold LB0r; rewrite <- app_assoc; cbn [app]; apply Permutation_refl|].
    split; [cbn [lbl map]; cbn [Datatypes.fst Datatypes.snd]; apply perm_skip; exact PM2|].
    split; [apply lb_own_cons; [exact WRP2 | exact OWN2]|].
    split; [eapply xpres_trans; [exact XP | eapply (xpres_weaken H); [exact XPr | lia | intros b Hb; unfold LB0r; apply in_or_app; left; exact Hb | intros a Ha; exact Ha]]|].
    split; [exact RF2|]. split; [exact AC2|]. split; [exact S02|].
    cbv beta iota. lia.
  Qed.
End EmpR.
