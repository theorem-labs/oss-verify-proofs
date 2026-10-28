(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel HFpu HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_HStKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtRK LbB_NtD LbB_NtI LbB_NtI4
  LbB_NtRL LbB_NtRE LbB_NtRB LbB_NtF LbB_NtG.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_TopKit LbB_HEmpD LbB_HEmpI LbB_HEmpS LbB_HEmpR LbB_HEmpL LbB_HEmpN
  LbB_HEmpNd LbB_HEmpI2 LbB_HEmpI3 LbB_RGl.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


Definition E_NF : Z := 0xf53e0.
Definition E_NEWRET : Z := 0xf53ec.

Lemma zero12_cells : forall m A, rw_cells asegs m A [CB 12 (poison_bytes 12 0)] ->
  rw_cells asegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros m A [[Hwf Hb] Hw]. split; [split|].
  - cbn. tauto.
  - assert (E : cells_bytes [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] = cells_bytes [CB 12 (poison_bytes 12 0)])
      by (vm_compute; reflexivity).
    rewrite E. exact Hb.
  - exact Hw.
Qed.

Lemma cells6_join : forall m A c1 c2 c3 c4 c5 c6,
  rw_cells asegs m A [C8 c1] -> rw_cells asegs m (A + 8) [C8 c2] -> rw_cells asegs m (A + 16) [C4 c3] ->
  rw_cells asegs m (A + 20) [C4 c4; C4 c5; C4 c6] ->
  rw_cells asegs m A [C8 c1; C8 c2; C4 c3; C4 c4; C4 c5; C4 c6].
Proof.
  intros m A c1 c2 c3 c4 c5 c6 H1 H2 H3 H4.
  apply rw_cells_cons8_c; [exact H1|].
  apply rw_cells_cons8_c; [exact H2|].
  change [C4 c3; C4 c4; C4 c5; C4 c6] with ([C4 c3] ++ [C4 c4; C4 c5; C4 c6]).
  apply rw_cells_app. split.
  - eapply rw_cells_addr; [exact H3 | lia].
  - eapply rw_cells_addr; [exact H4 | cbn [cells_size csize Z.of_nat Pos.of_succ_nat]; lia].
Qed.

Definition srND : list expr := srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (10%bv, EVar 33); (21%bv, EVar 34); (18%bv, EVar 35)].
Definition KN_ND : list kentry :=
  [KWord (SA (EVar 32) 616) 8 (ELit SHBASE); KWr (SA (EVar 33) 0) (ELit 32); KWr (SA (EVar 32) 592) (ELit 8);
   KRange (EVar 33) AIMG_TOP (2 ^ 47 - 32); KAlign (EVar 33) 16; KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 34) 0 (2 ^ 47 - 8)].
Definition SCR_ND := SCR [] [EVar 36] [].

Section NtNd.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key keyp v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).
  Variable (CH : list (Z * Z)).
  #[local] Notation n := (bseq_next bc).

  Hypothesis BSQ : In bc BSEQ.
  Hypothesis Hlast : bc <> BSEQ_LAST.
  Hypothesis OCE : obj + 40 <= aceil.
  Hypothesis LFO : map_live_frame LF obj.
  Hypothesis ACL : aceil <= lo.
  Hypothesis LOS : lo <= S1.
  Hypothesis LOR : lo <= S1 - ANT_STACK.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis KR32 : 0 <= key < 2 ^ 32.
  Hypothesis ZLEN : Zlength ents + 1 < 2 ^ 24.
  Hypothesis SP16 : S1 mod 16 = 0.
  Hypothesis SPB : S1 + 672 <= B.
  Hypothesis BR : B < 2 ^ 64.
  Hypothesis SHI : S1 + 672 <= shi.
  Hypothesis TRK : trace_ok (as_TR H) APC0_FREE (R_DRET :: map snd CH).
  Hypothesis CHH : forall fp ra, In (fp, ra) CH -> S1 + 688 <= fp.
  Hypothesis K0 : 0 <= keyp.
  Hypothesis KCE : keyp + 4 <= aceil.
  Hypothesis K4 : keyp mod 4 = 0.
  #[local] Opaque bseq_next.
  Abbreviation QIx := (QI H gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).

  Definition NPRE (s : as_St H) (mo : Model) (m : mem) (errv : word) (LB LBm : list block) (j584 j592 : word) : Prop :=
    as_MPRES H mo0 mo
    /\ WSLOTS ty enc S1 obj m j584 j592 /\ nt_slots m S1 obj v408 v576 v624
    /\ 2 ^ 45 <= S1 /\ S1 + 672 <= 2 ^ 47 /\ (0 <= v408 < 2 ^ 64 /\ 0 <= v576 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64)
    /\ mem_inv asegs m /\ stk asegs m lo (S1 + 672) /\ rw_cells asegs m (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m B
    /\ umapx MI_A 32 (nval32 ASEGS) (lbl LB) m obj bl bc ents /\ umap_sh m 32 (bl, bc, ents)
    /\ addressable m obj 40 /\ wr_at asegs m obj 40
    /\ fldA m keyp 4 key /\ emp_src H LB0 S1 obj keyp 4
    /\ as_RHEAP H s LB m /\ Permutation LB (LB0 ++ LBm) /\ Permutation (lbl LBm) (umap_blocks 32 bl bc ents) /\ lb_own LBm m
    /\ xpres H LB0 S1 (nt_X S1 obj) m0 m /\ as_RFS H LF m /\ ACONST m /\ stack0 m lo shi
    /\ as_AL H s >= as_AL H sk0 /\ 0 <= as_AL H s
    /\ lb_small LB + 32 + nsmall (8 * n) <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + nlg (8 * n) <= RT_LARGE_MAX
    /\ ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * n) <= as_AL H s)
    /\ as_chain H m (bv_unsigned s0) CH.

  #[local] Ltac trm X MU WM := eapply rw_cells_transport; [exact X | exact MU | exact WM | cbn [disjoint_from cells_size csize]; lia].
  #[local] Ltac tra AP X := eapply (apres_rw_cells H); [exact AP | exact X | left; lia].

  Lemma stage_node : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y25 y26 y28 y29 y30 y31 : word) (errv : word) (LB LBm : list block)
      (j584 j592 : word),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 key) y19 s4 (Z_to_bv 64 keyp) y22 y23 wd y25 y26 (Z_to_bv 64 bc) y28 y29 y30 y31)
                        F (Z_to_bv 64 E_NF) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> NPRE s mo m errv LB LBm j584 j592 ->
    (bc <> 0 -> y22 = Z_to_bv 64 (hmod key bc)) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y22 y23 y25 y26 y28 y29 y30 y31 errv LB LBm j584 j592
      VIS FRZ KR NP IDX.
    destruct NP as (MP & WS & RS & SPL & SPH & V64 & MI & ST & ERR & RA & U & SH & ADH & WRH & FK & ES
                    & RH & PE & PM & OWN & XP & RF & AC & S0 & AL & AL0 & RSM & RCN & RLG & RICM & CHN).
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold ANT_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoal.
    pose proof (LbB_HFind.BSEQ_boundA bc BSQ) as BCR.
    destruct (LbB_HEmpR.bseq_next_factsE bc BSQ Hlast) as (HnB & Hbcn & Hn28 & _).
    assert (Hn0 : 0 < n) by (clear - BCR Hbcn; lia).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    assert (EA : errno_addr tp = ATP - 164) by (rewrite TPV, u64_of_Z by (unfold ATP; lia); lia).
    rewrite EA in ERR.

    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 key) y19 s4 (Z_to_bv 64 keyp) y22 y23 wd y25 y26 (Z_to_bv 64 bc) y28 y29 y30 y31) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by apply regs_ok_seed.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R E_NF m (seg_rom asegs) HR HK 10%nat [AOPNEW] (SCR [] [] []) 40%N.
    { apply Forall_nil. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 10%bv G10. rreg HR' 25%bv G25.
    assert (G1' : getr R' 1 = Z_to_bv 64 E_NEWRET) by (rewrite G1; reflexivity).
    assert (G25' : getr R' 25 = wd) by (rewrite G25, HR0; reflexivity).
    rewrite G1', G10, G25' in HRe. clear G1 G25.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    clear Hms HRe VIS KR.

    assert (NSm : 0 <= nsmall (8 * n)) by (apply nsmall_bounds; lia).
    assert (NLg : 0 <= nlg (8 * n)) by (unfold nlg; destruct (_ <? _); lia).
    assert (AOK : as_alloc_ok H s LB 32).
    { apply (rt_bp_live H HHB s LB m 32 RH ltac:(lia)); [change (nsmall 32) with 32 | | change (nlg 32) with 0]; lia. }
    assert (CM : as_Cm H 32 <= as_AL H s) by (rewrite (proj2 (rt_bp_cost H HHB) 32), ICM_small by lia; lia).
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 32) (LB := LB) (lo := lo) (B := B) (errv := errv);
        [ exact VIS1 | exact RH | exact KR1 | exact AOK | exact CM | exact RA
        | rewrite u64_of_Z by lia; lia
        | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs m lo S1 (S1 + 672) ST ltac:(lia)))
        | exact ACL | rewrite u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | rewrite EA; exact ERR | exact MI | exact TPV | rewrite u64_of_Z by lia; exact SP16
        | exact AC | reflexivity | lia ]. }
    intros [msF2 mo2] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & p & junk & pid & s1
                      & VIS2 & KR2 & MP2 & MI1 & ST1 & ERR1 & RA1 & AP1 & ABR & RH1 & CB1 & ADP1 & AC1 & AL1).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite (ret_pc_even E_NEWRET ltac:(unfold E_NEWRET; lia) eq_refl) in VIS2.
    rewrite u64_of_Z in AP1, ST1 by lia.
    rewrite (proj2 (rt_bp_cost H HHB) 32), ICM_small in AL1 by lia.
    rewrite EA in ERR1.
    destruct ABR as (Hp0 & Hp16 & _ & HpI & HpC & HpF & HpA).
    unfold AIMG_TOP in HpI.
    pose proof HpA as HpA'. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in HpA'.
    assert (HpS : p + 32 <= S1) by lia.
    pose proof (ah_nodup H HH _ _ _ RH1) as ND. cbn [map] in ND. apply NoDup_cons_iff in ND as (NIN & _).
    cbn [blk_id fst] in NIN.
    clear Hlf G10 G1' G25' HR' R'.
    assert (CRK : aclient_range H LB S1 keyp 4).
    { destruct ES as (ER & _ & _). eapply (LbB_HEmpNd.acr_mono H); [exact ER | | lia].
      intros b Hb. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb. }
    assert (APK : apart keyp 4 p 32).
    { eapply (LbB_HEmpNd.aclient_range_apart_fresh H HH); [exact RH1 | exact NIN | exact HpS | lia | exact CRK]. }
    unfold apart in APK.
    assert (CK1 : cell4 ASEGS m1 keyp key).
    { eapply cellw_agree; [split; [change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | exact FK] | | lia | cbn; lia].
      intros i Hi. cbn [Z.of_N] in Hi.
      destruct (AP1 (keyp + i) ltac:(lia) (aclient_range_addr H _ _ _ _ (keyp + i) CRK ltac:(lia))) as [Ek _]. exact Ek. }
    assert (GZp : gz m1 p 32) by (apply LbB_HEmpI.gzA; [exact ADP1 | reflexivity]).
    assert (WRp : wr_at asegs m1 p 32) by exact (proj2 CB1).
    destruct WS as (W584 & W600 & W632 & W656).
    destruct RS as (R408 & R576 & R616 & R624 & R648).
    assert (W584a : rw_cells asegs m1 (S1 + 584) [C8 j584; C8 j592]) by tra AP1 W584.
    assert (W600a : rw_cells asegs m1 (S1 + 600) [C8 enc; C8 ty]) by tra AP1 W600.
    assert (W632a : rw_cells asegs m1 (S1 + 632) [C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 (obj / 8))]) by tra AP1 W632.
    assert (W656a : rw_cells asegs m1 (S1 + 656) [C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 (sh (obj + 8)))]) by tra AP1 W656.
    assert (R408a : rw_cells asegs m1 (S1 + 408) [C8 (Z_to_bv 64 v408)]) by tra AP1 R408.
    assert (R576a : rw_cells asegs m1 (S1 + 576) [C8 (Z_to_bv 64 v576)]) by tra AP1 R576.
    assert (R616a : rw_cells asegs m1 (S1 + 616) [C8 (Z_to_bv 64 SHBASE)]) by tra AP1 R616.
    assert (R624a : rw_cells asegs m1 (S1 + 624) [C8 (Z_to_bv 64 v624)]) by tra AP1 R624.
    assert (R648a : rw_cells asegs m1 (S1 + 648) [C8 (Z_to_bv 64 (obj - 136))]) by tra AP1 R648.
    clear W584 W600 W632 W656 R408 R576 R616 R624 R648.
    assert (ST1f : stk asegs m1 S1 (S1 + 672)).
    { eapply (apres_stk H); [exact AP1 | exact (proj2 (stk_split asegs m lo S1 (S1 + 672) ST ltac:(lia))) | lia]. }
    assert (ST1a : stk asegs m1 lo (S1 + 672)) by (apply (stk_merge asegs m1 lo S1 (S1 + 672)); [exact ST1 | exact ST1f | lia]).
    assert (XP12 : xpres H LB S1 [] m m1) by exact (xpres_of_apres H _ _ [] _ _ AP1).
    assert (RF1 : as_RFS H LF m1) by exact (RFS_via_apres H HH LF LB _ m m1 RF AP1).
    assert (S01 : stack0 m1 lo shi) by (eapply (stack0_xpres H); [exact XP12 | exact S0 | apply Forall_nil]).
    assert (OWN1 : lb_own LBm m1).
    { eapply (lb_own_apres H); [exact OWN | exact AP1 |]. intros b Hb. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. exact Hb. }
    assert (XP1 : xpres H LB0 S1 (nt_X S1 obj) m0 m1).
    { eapply xpres_trans; [exact XP|]. eapply (xpres_weaken H); [exact XP12 | lia | | intros a Ha; destruct Ha].
      intros b Hb. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb. }
    assert (XPa1 : xpres H LB (S1 + 672) [] m m1) by (eapply (xpres_weaken H); [exact XP12 | lia | intros b Hb; exact Hb | intros a Ha; exact Ha]).

    lazymatch type of VIS2 with _ = MS ?RR _ _ _ _ _ _ => remember RR as R2 eqn:HR20 end.
    assert (FHF2 : rfull R2) by (rewrite HR20; apply rfull_mkR).
    pose (E2 := Eseed R2 [Z_to_bv 64 S1; Z_to_bv 64 p; Z_to_bv 64 keyp; Z_to_bv 64 key; sxw key]).
    assert (HR2 : regs_ok E2 srND R2).
    { unfold srND. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R2; evs; reflexivity] |]). apply Forall_nil. }
    assert (HK2 : know_ok asegs E2 m1 (kn_fix 20 [AASAN_MEMSET] SCR_ND E_NEWRET srND KN_ND 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell R616a 0%nat (C8 (Z_to_bv 64 SHBASE))|].
      apply Forall_cons; [eapply (kwr_of_wr_at asegs E2 m1 p 32); [exact WRp | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]|].
      apply Forall_cons; [eapply (kwr_of_stk asegs E2 m1 lo (S1 + 672)); [exact ST1a | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; split; [lia | exact Hp16]|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      clear - GZp Hp0 HpC ACF2. know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R2 E_NEWRET m1 (seg_rom asegs) HR2 HK2 60%nat [AASAN_MEMSET] SCR_ND 50%N.
    { split_scs.
      - clear - E2 APK Hp0 HpC ACF2 K0 KCE. sc_dj.
      - clear - E2 APK Hp0 HpC ACF2 K0 KCE. sc_dj.
      - clear - E2 Hp0 HpC ACF2 K0 KCE ACL LOS SPL SPH. sc_dj.
      - eapply sc_read_cell4_sx; [exact CK1 | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity].
      - clear - E2 Hp0 HpC HpA' ACF2. sc_shdj.
      - clear - E2 Hp0 HpC HpA' ACF2. sc_shdj.
      - clear - E2 Hp0 HpC HpA' ACF2. sc_shdj. }
    rename R' into R2'. rename HR' into HR2'.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E2 m1 lg) in Hms; set (M2 := mem_denot E2 m1 lg) in Hms end end.
    assert (MU2 : munch [(p, p + 20); (S1 + 592, S1 + 600)] m1 M2).
    { subst M2. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM2 : wmono asegs m1 M2) by (subst M2; apply wmono_mem_denot).
    assert (MI2 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms MI1).
    assert (ST2 : stk asegs M2 lo (S1 + 672)) by (subst M2; apply stk_mem_denot; exact ST1a).
    assert (W592 : wr_at asegs m1 (S1 + 592) 8) by (eapply LbB_HEmpD.wr_at_subE; [exact (proj2 W584a) | lia | cbn [cells_size csize]; lia | lia]).
    assert (C592 : rw_cells asegs M2 (S1 + 592) [C8 (Z_to_bv 64 (p / 8 + SHBASE))]).
    { subst M2. rwc_newT Hlf W592 ltac:(evs; rewrite sh_word by lia; reflexivity). }
    assert (WRp0 : wr_at asegs m1 p 8) by (eapply LbB_HEmpD.wr_at_subE; [exact WRp | lia | lia | lia]).
    assert (WRp8 : wr_at asegs m1 (p + 8) 8) by (eapply LbB_HEmpD.wr_at_subE; [exact WRp | lia | lia | lia]).
    assert (WRp16 : wr_at asegs m1 (p + 16) 4) by (eapply LbB_HEmpD.wr_at_subE; [exact WRp | lia | lia | lia]).
    assert (N0 : rw_cells asegs M2 p [C8 (Z_to_bv 64 0)]) by (subst M2; rwc_new Hlf WRp0).
    assert (N8 : rw_cells asegs M2 (p + 8) [C8 (Z_to_bv 64 key)]) by (subst M2; rwc_new Hlf WRp8).
    assert (N16 : rw_cells asegs M2 (p + 16) [C4 (Z_to_bv 64 key)]).
    { subst M2. rwc_newT Hlf WRp16 ltac:(evs; exact (eq_sym (word_to_le_bytes_swrap 4 key ltac:(lia)))). }
    destruct (rw_cells_CB_split asegs m1 p (Z.to_nat 32) 20 junk CB1 ltac:(cbn; lia)) as (_ & CBb).
    assert (CB12a : rw_cells asegs m1 (p + 20) [CB 12 (skipn 20 junk)]) by (eapply rw_cells_addr; [exact CBb | reflexivity]).
    assert (CB12 : rw_cells asegs M2 (p + 20) [CB 12 (skipn 20 junk)]) by trm CB12a MU2 WM2.
    change [C8 j584; C8 j592] with ([C8 j584] ++ [C8 j592]) in W584a. apply rw_cells_app in W584a as (W584b & _).
    assert (W584c : rw_cells asegs M2 (S1 + 584) [C8 j584]) by trm W584b MU2 WM2.
    assert (W600c : rw_cells asegs M2 (S1 + 600) [C8 enc; C8 ty]) by trm W600a MU2 WM2.
    assert (W632c : rw_cells asegs M2 (S1 + 632) [C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 (obj / 8))]) by trm W632a MU2 WM2.
    assert (W656c : rw_cells asegs M2 (S1 + 656) [C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 (sh (obj + 8)))]) by trm W656a MU2 WM2.
    assert (R408c : rw_cells asegs M2 (S1 + 408) [C8 (Z_to_bv 64 v408)]) by trm R408a MU2 WM2.
    assert (R576c : rw_cells asegs M2 (S1 + 576) [C8 (Z_to_bv 64 v576)]) by trm R576a MU2 WM2.
    assert (R616c : rw_cells asegs M2 (S1 + 616) [C8 (Z_to_bv 64 SHBASE)]) by trm R616a MU2 WM2.
    assert (R624c : rw_cells asegs M2 (S1 + 624) [C8 (Z_to_bv 64 v624)]) by trm R624a MU2 WM2.
    assert (R648c : rw_cells asegs M2 (S1 + 648) [C8 (Z_to_bv 64 (obj - 136))]) by trm R648a MU2 WM2.
    assert (ERR2 : rw_cells asegs M2 (ATP - 164) [C4 errv1]) by (eapply rw_cells_transport; [exact ERR1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; unfold ATP in *; lia]).
    clear CB12a CBb W584b W600a W632a W656a R408a R576a R616a R624a R648a.
    assert (INP : In (pid, p, 32) ((pid, p, 32) :: LB)) by (left; reflexivity).
    destruct (LbB_HEmpI.blk_win H HH LF s1 ((pid, p, 32) :: LB) m1 pid p 32 p (p + 20) RH1 INP ltac:(lia) ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    assert (WA : aclient_write_ok H ((pid, p, 32) :: LB) (S1 + 592, S1 + 600) /\ afs_write_ok H LF (S1 + 592, S1 + 600)
                 /\ aconst_ok (S1 + 592, S1 + 600) /\ stack0_ok (S1 + 592, S1 + 600)).
    { split; [left; cbn; lia|].
      split; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; clear - FB1 FB2 ACL LOS ACF1; unfold AIMG_TOP in FB1; lia|].
      split; [apply aconst_ok_high; [assert (SHT : sh AIMG_TOP < 2 ^ 45) by (vm_compute; reflexivity); clear - SPL SHT; lia | right; left; clear - SPL; lia]|].
      left. cbn. unfold AHI_LO. clear - SPL. lia. }
    destruct WA as (WA1 & WA2 & WA3 & WA4).
    destruct (client_frame H HH s1 ((pid, p, 32) :: LB) LF B _ m1 M2 RH1 RF1 AC1 RA1 MU2 WM2
               (Forall_cons _ _ _ Q1 (Forall_cons _ _ _ WA1 (Forall_nil _)))
               (Forall_cons _ _ _ Q2 (Forall_cons _ _ _ WA2 (Forall_nil _)))
               (Forall_cons _ _ _ Q3 (Forall_cons _ _ _ WA3 (Forall_nil _)))) as (RH2 & RF2 & AC2 & RA2).
    assert (S02 : stack0 M2 lo shi) by (eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 | exact (Forall_cons _ _ _ Q4 (Forall_cons _ _ _ WA4 (Forall_nil _)))]).
    assert (DSH2 : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from [(p, p + 20); (S1 + 592, S1 + 600)] (sh A) (nsh k)).
    { intros A k HA Hk HAk. apply LbB_HEmpI.dsh_app; [| exact HA | exact Hk | exact HAk].
      apply Forall_cons; [cbn [fst snd]; clear - Q5; lia|]. apply Forall_cons; [cbn [fst snd]; unfold AHI_LO; clear - SPL; lia | apply Forall_nil]. }
    assert (ADP2 : addressable M2 p 32) by (eapply addressable_transport; [exact ADP1 | exact MU2 | exact WM2 | apply DSH2; lia]).
    assert (WRp2 : wr_at asegs M2 p 32) by exact (wr_at_wmono _ _ _ _ WRp WM2).
    assert (OWN2 : lb_own LBm M2) by exact (lb_own_wmono _ _ _ OWN1 WM2).
    assert (PE2 : Permutation ((pid, p, 32) :: LB) (LB0 ++ (pid, p, 32) :: LBm))
      by (eapply perm_trans; [apply perm_skip; exact PE | apply Permutation_middle]).
    assert (XP2 : xpres H LB0 S1 (nt_X S1 obj) m0 M2).
    { eapply (xpres_munch_mixed H HH s1 ((pid, p, 32) :: LB) LB0 ((pid, p, 32) :: LBm) S1 (nt_X S1 obj) _ m0 m1 M2);
        [exact XP1 | exact RH1 | exact PE2 | lia | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; right; exists pid, p, 32; split; [left; reflexivity | cbn; lia]|].
      apply Forall_cons; [right; left; intros a Ha; unfold nt_X; cbn [rin_ivs fst snd] in *; right; left; lia | apply Forall_nil]. }
    assert (XPa2 : xpres H LB (S1 + 672) [] m M2).
    { eapply (xpres_munch_mixed H HH s1 ((pid, p, 32) :: LB) LB [(pid, p, 32)] (S1 + 672) [] _ m m1 M2);
        [exact XPa1 | exact RH1 | apply Permutation_cons_append | lia | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; right; exists pid, p, 32; split; [left; reflexivity | cbn; lia]|].
      apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }

    readback HR2' (msteps_full asegs _ _ Hms FHF2) HR20 HRe2.
    rreg HR2' 1%bv G1. rreg HR2' 2%bv G2. rreg HR2' 9%bv G9. rreg HR2' 10%bv G10. rreg HR2' 11%bv G11. rreg HR2' 12%bv G12.
    rreg HR2' 18%bv G18. rreg HR2' 21%bv G21. rreg HR2' 23%bv G23. rreg HR2' 24%bv G24.
    assert (G1' : getr R2' 1 = Z_to_bv 64 E_LF) by (rewrite G1; reflexivity).
    change (getr R2' 24 = Z_to_bv 64 SHBASE) in G24.
    rewrite (w_add p 20) in G10 by lia.
    rewrite G1', G2, G9, G10, G11, G12, G18, G21, G23, G24 in HRe2. clear G1.
    eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact FHF2 | exact Hms | exact HRe2 |].
    intros msF3 mo3 KR3 MP3 VIS3.
    clear Hms HRe2 VIS2 KR2.
    assert (AIS : 0 <= AINTRIN_STACK /\ lo <= S1 - AINTRIN_STACK) by (unfold AINTRIN_STACK; clear - LOR'; lia).
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ RH2 INP) as SVP.
    destruct (LbB_HEmpI.blk_win H HH LF s1 ((pid, p, 32) :: LB) M2 pid p 32 (p + 20) (p + 32) RH2 INP ltac:(lia) ltac:(lia))
      as (P1 & P2 & P3 & P4 & P5).
    eapply (ahh_evt_then H HH (amemset_post (Z_to_bv 64 E_LF) (Z_to_bv 64 S1) gp tp s0 (Z_to_bv 64 S1) (Z_to_bv 64 key) y19 s4
              (Z_to_bv 64 keyp) y22 (Z_to_bv 64 p) (Z_to_bv 64 SHBASE) wd y26 (Z_to_bv 64 bc)
              F fc (Z_to_bv 64 (p + 20)) (Z_to_bv 64 12) 0 lo M2)); [exact KR3 | exact VIS3 | |].
    { eapply (ah_memset H HH); [reflexivity | lia | | | | | exact ACL | | exact MI2 | exact AC2 | | | |];
        rewrite ?u64_of_Z by lia.
      - exact CB12.
      - eapply addressable_accessible; [exact ADP2 | lia | lia | unfold AAPP_HI in *; lia].
      - eapply shvis_sub; [exact SVP | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs M2 lo S1 (S1 + 672) ST2 ltac:(lia))).
      - lia.
      - lia.
      - unfold in_app_mem. rewrite ASHADOW_BASE_val. unfold ALOWSH_LO, AHI_LO, AAPP_HI in *. clear - HpA' HpC ACF2 Hp0. lia.
      - replace (p + 20 + 12) with (p + 32) by lia. exact P3.
      - left. clear - HpC ACL. lia. }
    intros msF4 mo4 KR4 MP4 POST.
    destruct POST as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & M3
                      & VIS4 & MU3 & WM3 & MI3 & ST3 & ZER & AC3).
    assert (U64a : bv_unsigned (Z_to_bv 64 (p + 20)) = p + 20) by (apply u64_of_Z; lia).
    assert (U64b : bv_unsigned (Z_to_bv 64 12) = 12) by (apply u64_of_Z; lia).
    assert (U64c : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply u64_of_Z; lia).
    rewrite U64a, U64b, U64c in MU3. rewrite U64c in ST3. rewrite U64a, U64b in ZER.
    rewrite (ret_pc_even E_LF ltac:(unfold E_LF; lia) eq_refl) in VIS4.
    pose proof (zero12_cells M3 (p + 20) ZER) as Z12. clear ZER U64a U64b U64c.
    replace (p + 20 + 12) with (p + 32) in MU3 by lia.
    assert (N0' : rw_cells asegs M3 p [C8 (Z_to_bv 64 0)]) by trm N0 MU3 WM3.
    assert (N8' : rw_cells asegs M3 (p + 8) [C8 (Z_to_bv 64 key)]) by trm N8 MU3 WM3.
    assert (N16' : rw_cells asegs M3 (p + 16) [C4 (Z_to_bv 64 key)]) by trm N16 MU3 WM3.
    pose proof (cells6_join M3 p _ _ _ _ _ _ N0' N8' N16' Z12) as NODE.
    assert (W584d : rw_cells asegs M3 (S1 + 584) [C8 j584]) by trm W584c MU3 WM3.
    assert (C592d : rw_cells asegs M3 (S1 + 592) [C8 (Z_to_bv 64 (p / 8 + SHBASE))]) by trm C592 MU3 WM3.
    assert (W600d : rw_cells asegs M3 (S1 + 600) [C8 enc; C8 ty]) by trm W600c MU3 WM3.
    assert (W632d : rw_cells asegs M3 (S1 + 632) [C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 (obj / 8))]) by trm W632c MU3 WM3.
    assert (W656d : rw_cells asegs M3 (S1 + 656) [C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 (sh (obj + 8)))]) by trm W656c MU3 WM3.
    assert (R408d : rw_cells asegs M3 (S1 + 408) [C8 (Z_to_bv 64 v408)]) by trm R408c MU3 WM3.
    assert (R576d : rw_cells asegs M3 (S1 + 576) [C8 (Z_to_bv 64 v576)]) by trm R576c MU3 WM3.
    assert (R616d : rw_cells asegs M3 (S1 + 616) [C8 (Z_to_bv 64 SHBASE)]) by trm R616c MU3 WM3.
    assert (R624d : rw_cells asegs M3 (S1 + 624) [C8 (Z_to_bv 64 v624)]) by trm R624c MU3 WM3.
    assert (R648d : rw_cells asegs M3 (S1 + 648) [C8 (Z_to_bv 64 (obj - 136))]) by trm R648c MU3 WM3.
    assert (ERR3 : rw_cells asegs M3 (ATP - 164) [C4 errv1]).
    { eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; unfold ATP in *; lia]. }
    assert (J3 : exists j, rw_cells asegs M3 (S1 + 584) [C8 j; C8 (Z_to_bv 64 (p / 8 + SHBASE))]).
    { exists j584. apply rw_cells_cons8_c; [exact W584d|]. replace (S1 + 584 + 8) with (S1 + 592) by lia. exact C592d. }
    clear N0 N8 N16 W584c C592 W600c W632c W656c R408c R576c R616c R624c R648c ERR2.
    assert (ST3a : stk asegs M3 lo (S1 + 672)).
    { apply (stk_merge asegs M3 lo S1 (S1 + 672)); [exact ST3 | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs M2 lo S1 (S1 + 672) ST2 ltac:(lia))) | exact MU3 | exact WM3 |].
      cbn [disjoint_from]. lia. }
    assert (XP3 : xpres H LB0 S1 (nt_X S1 obj) m0 M3).
    { eapply (xpres_munch_mixed H HH s1 ((pid, p, 32) :: LB) LB0 ((pid, p, 32) :: LBm) S1 (nt_X S1 obj) _ m0 M2 M3);
        [exact XP2 | exact RH2 | exact PE2 | lia | exact MU3 | exact WM3 |].
      apply Forall_cons; [right; right; exists pid, p, 32; split; [left; reflexivity | cbn; lia]|].
      apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
    assert (XPa3 : xpres H LB (S1 + 672) [] m M3).
    { eapply (xpres_munch_mixed H HH s1 ((pid, p, 32) :: LB) LB [(pid, p, 32)] (S1 + 672) [] _ m M2 M3);
        [exact XPa2 | exact RH2 | apply Permutation_cons_append | lia | exact MU3 | exact WM3 |].
      apply Forall_cons; [right; right; exists pid, p, 32; split; [left; reflexivity | cbn; lia]|].
      apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
    assert (WB : aclient_write_ok H ((pid, p, 32) :: LB) (S1 - AINTRIN_STACK, S1) /\ afs_write_ok H LF (S1 - AINTRIN_STACK, S1)
                 /\ aconst_ok (S1 - AINTRIN_STACK, S1) /\ stack0_ok (S1 - AINTRIN_STACK, S1)).
    { split; [left; cbn; lia|].
      split; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; clear - FB1 FB2 ACL LOS ACF1 AIS; unfold AIMG_TOP in FB1; lia|].
      split; [apply aconst_ok_high; [assert (SHT : sh AIMG_TOP < 2 ^ 40) by (vm_compute; reflexivity); unfold AINTRIN_STACK in *; clear - SPL SHT; lia
                                   | right; left; unfold AINTRIN_STACK; clear - SPL; lia]|].
      left. cbn. unfold AHI_LO, AINTRIN_STACK. clear - SPL. lia. }
    destruct WB as (WB1 & WB2 & WB3 & WB4).
    destruct (client_frame H HH s1 ((pid, p, 32) :: LB) LF B _ M2 M3 RH2 RF2 AC2 RA2 MU3 WM3
               (Forall_cons _ _ _ P1 (Forall_cons _ _ _ WB1 (Forall_nil _)))
               (Forall_cons _ _ _ P2 (Forall_cons _ _ _ WB2 (Forall_nil _)))
               (Forall_cons _ _ _ P3 (Forall_cons _ _ _ WB3 (Forall_nil _)))) as (RH3 & RF3 & _ & RA3).
    assert (S03 : stack0 M3 lo shi).
    { eapply stack0_transport; [exact S02 | exact MU3 | exact WM3 | exact (Forall_cons _ _ _ P4 (Forall_cons _ _ _ WB4 (Forall_nil _)))]. }
    assert (DSH3 : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 ->
                   disjoint_from [(p + 20, p + 32); (S1 - AINTRIN_STACK, S1)] (sh A) (nsh k)).
    { intros A k HA Hk HAk. apply LbB_HEmpI.dsh_app; [| exact HA | exact Hk | exact HAk].
      apply Forall_cons; [cbn [fst snd]; clear - P5; lia|].
      apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, AINTRIN_STACK; clear - SPL; lia | apply Forall_nil]. }
    assert (ADP3 : addressable M3 p 32) by (eapply addressable_transport; [exact ADP2 | exact MU3 | exact WM3 | apply DSH3; lia]).
    assert (OWN3 : lb_own ((pid, p, 32) :: LBm) M3).
    { apply (lb_own_wmono _ M2 M3); [|exact WM3]. unfold lb_own. apply Forall_cons; [exact WRp2 | exact OWN2]. }
    assert (CHN3 : as_chain H M3 (bv_unsigned s0) CH).
    { eapply (ah_chain_ext H HH); [exact CHN|]. intros fp ra a IN Ha.
      pose proof (ah_chain_range H HH _ _ _ _ _ CHN IN) as (CR1 & CR2 & CR3). pose proof (CHH _ _ IN) as CF.
      assert (XC : xclient H LB (S1 + 672) [] a) by (split; [left; lia | intros K; exact K]).
      exact (proj1 (XPa3 a ltac:(lia) XC)). }
    assert (HOX : forall i, 0 <= i < 40 -> xclient H LB (S1 + 672) [] (obj + i)).
    { intros i Hi. split; [|intros K; exact K]. right; right; right; right; left. unfold AFS_SIZE in *. lia. }
    assert (INm : forall q k0, In (q, k0) (umap_blocks 32 bl bc ents) -> In (q, k0) (lbl LBm)).
    { intros q k0 Hq. apply (Permutation_in _ (Permutation_sym PM)). exact Hq. }
    assert (INL : forall q k0, In (q, k0) (lbl LBm) -> In (q, k0) (lbl LB)).
    { intros q k0 Hq. destruct (lbl_in_inv _ _ _ Hq) as (qi & Qi). unfold lbl. apply in_map_iff. exists (qi, q, k0).
      split; [reflexivity|]. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. exact Qi. }
    assert (U3 : umapx MI_A 32 (nval32 ASEGS) (lbl ((pid, p, 32) :: LB)) M3 obj bl bc ents).
    { eapply (umapx_xp H 32 _ (nval32 ASEGS) LB (S1 + 672) [] LB ((pid, p, 32) :: LB) m M3 obj);
        [exact (nval32_agree ASEGS) | lia | exact XPa3 | exact U | exact HOX |].
      apply (blkx_intro H). intros q k0 Hq. split; [exact (INL q k0 (INm q k0 Hq))|].
      split; [right; exact (INL q k0 (INm q k0 Hq)) | intros a _ K; exact K]. }
    assert (SH3 : umap_sh M3 32 (bl, bc, ents)).
    { eapply (umap_sh_xp H); [exact XPa3 | exact SH |]. apply (blksh_intro H). intros q k0 Hq.
      split; [exact (INL q k0 (INm q k0 Hq)) | intros a _ K; exact K]. }
    assert (AD3 : addressable M3 obj 40).
    { eapply (addressable_xp H); [exact XPa3 | exact ADH |]. intros a Ha. split; [|intros K; exact K].
      right; right; right; right; right; left.
      unfold sh, nsh in Ha |- *. clear - Ha OB1 OB2 Hoal Ho0. Z.div_mod_to_equations. lia. }
    assert (WR3 : wr_at asegs M3 obj 40).
    { eapply xpres_wr_at; [exact XPa3 | exact WRH |].
      split; [right; right; right; right; left; unfold AFS_SIZE in *; lia | apply Forall_nil]. }
    assert (APU : forall q k, In (q, k) (umap_blocks 32 bl bc ents) -> apart p 32 q k).
    { intros q k0 Hq. destruct (lbl_in_inv _ _ _ (INL q k0 (INm q k0 Hq))) as (qi & Qi).
      assert (NE : pid <> qi).
      { intros E0. apply NIN. apply in_map_iff. exists (qi, q, k0). split; [cbn; symmetry; exact E0 | exact Qi]. }
      pose proof (ah_disj H HH s1 ((pid, p, 32) :: LB) M2 (pid, p, 32) (qi, q, k0) RH2 (or_introl eq_refl) (or_intror Qi) NE) as D.
      cbn in D. unfold apart. lia. }
    eapply LbB_NtG.stage_lf with (s := s1) (m := M3) (errv' := errv1) (LB' := (pid, p, 32) :: LB) (LBm := (pid, p, 32) :: LBm) (p := p).
    all: try (first [exact VIS4 | exact FRZ | exact KR4 | exact IDX | eassumption]).
    unfold LbB_NtG.LPRE.
    split; [eapply (ah_mpres_trans H HH); [exact MP | eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH);
              [exact MP2 | eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4]]]]|].
    split; [exact J3|].
    split; [exact (conj W600d (conj W632d W656d))|].
    split; [exact (conj R408d (conj R576d (conj R616d (conj R624d R648d))))|].
    split; [exact SPL|]. split; [exact SPH|]. split; [exact V64|].
    split; [exact MI3|]. split; [exact ST3a|]. split; [rewrite EA; exact ERR3|]. split; [exact RA3|].
    split; [exact U3|]. split; [exact SH3|]. split; [exact AD3|]. split; [exact WR3|].
    split; [exact Hp0|]. split; [lia|]. split; [exact Hp16|]. split; [unfold apart; clear - HpF OB1 OB2; lia|].
    split; [exact APU|]. split; [exact NODE|]. split; [exact ADP3|]. split; [exact RH3|]. split; [exact PE2|].
    split; [change (lbl ((pid, p, 32) :: LBm)) with ((p, 32) :: lbl LBm); apply perm_skip; exact PM|].
    split; [exact OWN3|]. split; [exact XP3|]. split; [exact RF3|]. split; [exact AC3|]. split; [exact S03|].
    split; [lia|]. split; [lia|].
    split; [change (lb_small ((pid, p, 32) :: LB)) with (nsmall 32 + lb_small LB); change (nsmall 32) with 32; lia|].
    split; [cbn [length]; lia|].
    split; [change (nlarge ((pid, p, 32) :: LB)) with (nlg 32 + nlarge LB); change (nlg 32) with 0; lia|].
    split; [intros G; pose proof (RICM G); lia|].
    exact CHN3.
  Qed.
End NtNd.
