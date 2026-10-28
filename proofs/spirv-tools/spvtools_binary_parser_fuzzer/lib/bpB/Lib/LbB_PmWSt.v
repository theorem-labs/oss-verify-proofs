(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmVops LbB_PmVup LbB_TablStmt LbB_PmU2K LbB_HEmpStmt LbB_PmWM.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RT_SW : list (reg * expr) := [(10%bv, EVar 41)].

Definition KN_SW : list kentry := [KWr (SA (EVar 41) 0) (ELit 4)].

Lemma wr_at_subS {HCEIL : HeapCeil} : forall m a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

Section WSt.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  #[local] Notation ent := (Z * (Z * Z))%type (only parsing).

  Lemma HHs : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_sw_f17f8 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl msF R F fc (bl bc : Z) (l1 l2 : list ent) (q k v v' : Z)
                              (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo (set_m1A c (bl, bc, l1 ++ (q, (k, v)) :: l2)) ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf3aec) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 10%bv = Z_to_bv 64 (q + 20) -> PropExec.getr R 19%bv = Z_to_bv 64 (sx32A v') -> 0 <= v' < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf3af0) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 (set_m1A c (bl, bc, l1 ++ (q, (k, v')) :: l2)) ins tbl ftbl ->
       (forall r, PropExec.getr R1 r = PropExec.getr R r) ->
       (forall kk cs, 0 <= kk -> kk + Z.of_nat (cells_size cs) <= 16384 -> rw_cells asegs m (wa_ff w + kk) cs -> rw_cells asegs m1 (wa_ff w + kk) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl msF R F fc bl bc l1 l2 q k v v' Q OK X Hknn Hfk KR VIS RF G10 G19 Hv' K.
    pose proof HHs as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    set (c0 := set_m1A c (bl, bc, l1 ++ (q, (k, v)) :: l2)) in *.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as LBO.

    assert (Hinp : In (q, (k, v)) (l1 ++ (q, (k, v)) :: l2)) by (apply in_app_iff; right; left; reflexivity).
    assert (XBc : In (q, 24) (c_blocks c0)).
    { apply (Permutation_in _ (Permutation_sym (cbk_m1 c0))). apply in_or_app; left. unfold mblk1, c0, set_m1A. cbn [c_m1 c_m2 c_m3 t3a t3b t3c fst snd].
      unfold umap_blocks. apply in_or_app; right. apply in_map_iff. exists (q, (k, v)). split; [reflexivity | exact Hinp]. }
    destruct (xb_facts H HH w s LB LBs [] m c0 (q, 24) OK RH OWN1 OWN2 XBc) as (pid & XB1 & XB2 & XB3 & XBR). cbn [fst snd] in XB1, XB2, XB3, XBR.
    pose proof XBR as (R0 & R16 & Rn & RI & RC & RF' & RAPP).
    assert (WQ : wr_at asegs m q 24) by exact (proj1 (Forall_forall _ _) LBO _ XB1).

    set (Xv := [Z_to_bv 64 (q + 20)]).
    assert (HTv : regs_tblX w Xv R RT_SW).
    { unfold regs_tblX, RT_SW. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. rewrite G10. reflexivity. }
    assert (HE : env_world H w (Eseed R (wenv_vals w ++ Xv))) by apply env_world_seed.
    assert (E41 : edenot (Eseed R (wenv_vals w ++ Xv)) (EVar 41) = Z_to_bv 64 (q + 20)) by reflexivity.
    assert (HK0 : know_ok asegs (Eseed R (wenv_vals w ++ Xv)) m KN_SW).
    { unfold KN_SW, know_ok. apply Forall_cons; [| apply Forall_nil].
      eapply (kwr_of_wr_at _ _ m q 24); [exact WQ | | |]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?E41; cbn [edenot];
        rewrite ?unsigned_lit by lia; lia. }
    pm_goR HH OK X KR VIS RF HTv Xv KN_SW HK0 10%nat [0xf3af0] (@nil bool) 42%N (@nil (reg * expr)).
    { split_scs. eapply (sc_flat_lit asegs _ _ _ _ (q + 20 + 0) 4); [apply (estart_var _ 41 0 (q + 20) E41); lia | apply elit_u; lia | lia | lia | lia]. }
    intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1 HR1 Hlf1.
    lazymatch type of VIS1 with _ = MS _ _ _ _ _ ?mm _ => set (M1 := mm) in * end.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ Xv)) m _ [(EVar 41, 0, 4)] Hlf1 ltac:(vm_compute; reflexivity)) as MU1.
    cbn [num_wins map] in MU1. rewrite E41, unsigned_lit in MU1 by lia. rewrite Z.add_0_r in MU1.
    replace (q + 20 + 4) with (q + 24) in MU1 by lia.
    assert (RW1 : rw_cells asegs M1 (q + 20) [C4 (Z_to_bv 64 v')]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat (EVar 41%N) 0 4 (EVar 19));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite E41, u64_of_Z by lia; lia
        | exact (wr_at_subS m q 24 (q + 20) 4 WQ ltac:(lia) ltac:(lia) ltac:(lia))
        | reflexivity | exact Logic.I
        | cbn [cbytes]; change (edenot (Eseed R (wenv_vals w ++ Xv)) (EVar 19)) with (PropExec.getr R 19%bv); rewrite G19; apply w2lb4_sx32A; exact Hv' ]. }
    assert (X1 : PMXA H LINV w s LB LBs M1 mo1 (set_m1A c (bl, bc, l1 ++ (q, (k, v')) :: l2)) ins tbl ftbl).
    { apply (pmxa_mpres H HH LINV w _ _ _ _ mo mo1); [| exact MP1].
      eapply (pm_m1_setval H HHbp LINV LINV_cl w s LB LBs m mo c ins tbl ftbl M1 bl bc l1 l2 q k v v' OK X Hknn Hfk MU1);
        [apply wmono_mem_denot | intros x Hx; apply mem_denot_defined; exact Hx | exact MI1 | exact RW1 | exact Hv']. }
    replace (s_pc SSr) with 0xf3af0 in VIS1 by reflexivity.
    eapply (K msF1 mo1 M1 R1 KR1 VIS1 RF1 X1).
    - intros r. rewrite (HR1 r).
      pose proof (regs_ok_of_tbl w R RT_SW Xv (xbound Xv) HTv ltac:(vm_compute; reflexivity)) as HR0.
      replace (s_regs SSr) with (srs sr_id RT_SW) by (vm_compute; reflexivity). symmetry. apply HR0.
    - intros kk cs Hkk Hcs C. eapply rw_cells_transport; [exact C | exact MU1 | apply wmono_mem_denot |].
      cbn [disjoint_from]. split; [| exact I].
      pose proof (blk_apart_ff H HH w s LB m _ OK RH XB2) as BF. cbn [blk_addr blk_size fst snd] in BF. lia.
  Qed.
End WSt.
