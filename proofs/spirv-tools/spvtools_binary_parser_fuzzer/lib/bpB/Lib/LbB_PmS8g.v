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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_ContStmt LbB_PmLH LbB_PmVops LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_PmWXK LbB_PmS8K.

Definition RT_PM_S8G_1 : list (reg * expr) := [(1%bv, ELit 997252); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551612); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8G_3 : list (reg * expr) := [(1%bv, ELit 997272); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (11%bv, ELit 150176); (12%bv, ELit 30); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8G_5 : list (reg * expr) := [(1%bv, ELit 997284); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (11%bv, ELit 65535); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8G_7 : list (reg * expr) := [(1%bv, ELit 997304); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (11%bv, ELit 150240); (12%bv, ELit 8); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8G_9 : list (reg * expr) := [(1%bv, ELit 997316); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8G_11 : list (reg * expr) := [(1%bv, ELit 997336); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (11%bv, ELit 150272); (12%bv, ELit 11); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8G_13 : list (reg * expr) := [(1%bv, ELit 997348); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6000)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8G_15 : list (reg * expr) := [(1%bv, ELit 997348); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Ltac s8g_acc :=
  lazymatch goal with |- forall _, ACONST _ -> accessible _ ?p ?n =>
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p);
      [ eapply (ACONST_global_addressable M' p _ _ ACM'); [unfold aglobals; repeat (first [left; reflexivity | right]) | lia]
      | lia | lia | unfold AAPP_HI; lia ]
  end.
Ltac s8g_bytes :=
  lazymatch goal with |- exists bs, length bs = Z.to_nat ?n /\ forall _, mem_inv asegs _ -> bytes_at asegs _ ?p bs =>
    let nn := eval vm_compute in (Z.to_nat n) in
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) nn) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (img_lit M' p nn bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end
  end.
Ltac s8g_pc VIS pc :=
  lazymatch type of VIS with context [s_pc ?ss] => replace (s_pc ss) with pc in VIS by reflexivity end.

Lemma s8g_fk {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) (m m1 : mem) (dso : Z),
  (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
     (wa_ff w + k + Z.of_nat (cells_size cs) <= wa_ff w + dso \/ wa_ff w + dso + DS_SIZE <= wa_ff w + k) ->
     rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
  ffkeepX w [(dso, DS_SIZE)] m m1.
Proof.
  intros w m m1 dso FR k cs Hk Hn F C. apply (FR k cs Hk Hn); [| exact C].
  apply Forall_inv in F. cbn [fst snd] in F. lia.
Qed.

Lemma s8g_cb8 : forall m A (bs : list byte), length bs = 8%nat -> rw_cells asegs m A [CB 8 bs] ->
  rw_cells asegs m A [C8 (Z_to_bv 64 (bytes_le_to_Z bs))] /\ 0 <= bytes_le_to_Z bs < 2 ^ 64.
Proof.
  intros m A bs L RW. pose proof (BW_MallocBase.bytes_le_to_Z_range8 bs L) as R. split; [| exact R].
  destruct RW as [[WF BA] WR]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. cbn [cells_size csize] in WR.
  split; [split|].
  - cbn. split; exact Logic.I.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. unfold le8, word_to_le_bytes. rewrite u64_of_Z by lia.
    rewrite <- L. rewrite BW_MallocBase.Z_to_le_bytes_to_Z. exact BA.
  - cbn [cells_size csize]. exact WR.
Qed.

Section S8g.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HU16 : put_u16_stmtA H LINV ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV ds_repA.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

  Lemma s8g_rf8 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k,
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> pmw_okA H w -> 0 <= k -> k + 8 <= 832 ->
    exists x, 0 <= x < 2 ^ 64 /\ rw_cells asegs m (wa_s1 w + k) [C8 (Z_to_bv 64 x)].
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k X OK Hk Hk8.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    pose proof (wr_at_of_stk asegs m (wa_lo w) (wa_sp0 w) STK) as W. destruct W as (W0 & W1 & W2).
    assert (WR : wr_at asegs m (wa_s1 w + k) 8).
    { split; [lia|]. split; [lia|]. intros i Hi. replace (wa_s1 w + k + i) with (wa_lo w + (wa_s1 w + k + i - wa_lo w)) by lia. apply W2. lia. }
    destruct (rw_cells_of_wr_hi m (wa_s1 w + k) 8 WR ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(lia)) as (bs & RB).
    change (Z.to_nat 8) with 8%nat in RB.
    assert (L : length bs = 8%nat).
    { destruct RB as [[WF _] _]. destruct WF as [C _]. cbn in C. exact C. }
    destruct (s8g_cb8 m _ bs L RB) as [C R]. exists (bytes_le_to_Z bs). split; [exact R | exact C].
  Qed.

  Lemma pm_s8g : forall (w : pmwA H) s LB LBs m mo c msF R F fc (nw b0 cp dp ty : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf36a4) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 21%bv = Z_to_bv 64 nw ->
    0 <= nw < 2 ^ 64 ->
    pm_bud (wa_n w) c ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] ->
    rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    (forall (s1 : as_St H) (LB1 LBs1 : list block) msF1 mo1 m1 R1 F1 fc1 tbl1 (spal1 : Z), as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xf4164) fc1 None m1 (seg_rom asegs) -> rfull R1 -> frm_zero fc1 -> PMXAT H LINV w s1 LB1 LBs1 m1 mo1 c S_STR tbl1 [] [] spal1 -> incl TBL_EEF44 tbl1 -> 0 <= spal1 <= 2 ^ 20 -> regs_tbl w R1 RT_S8D0 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A (2 ^ 32 - 4)) -> rw_cells asegs m1 (wa_ff w + 5936) [C1 (b8 b0)] -> rw_cells asegs m1 (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] -> rw_cells asegs m1 (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame DSL HCSEQ HDTOR HU16 HU64 HPDIAG0.
    intros w s LB LBs m mo c msF R F fc nw b0 cp dp ty Q OK X0 _ Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 GNW HNW BUD
           HB0 HCP HDP HTY K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word) (@nil kentry) 400%nat [APDIAG] (@nil bool) 41%N
          [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8G_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    s8g_pc VIS1 APDIAG.
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (_ & TEB1 & _).
    pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m _ [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928); (EVar WV_S1, 24, 32)]
                  Hlf1 ltac:(vm_compute; reflexivity)) as TMU1.
    cbn [num_wins map] in TMU1. rewrite (srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU1.
    rewrite (ev_s1 H w _ OK (env_world_seed H w R (@nil word))) in TMU1.
    assert (FK1 : ffkeepX w [(6000, DS_SIZE)] m M1).
    { apply (ffkeepX_mono w []); [| intros ? []].
      apply (ffkeepX_munch w _ _ _ _ TMU1 (wmono_mem_denot _ _ _)).
      apply Forall_cons; [cbn [fst snd]; destruct Q6 as [Q6'|Q6']; [left | right; left]; rewrite Q13 in Q6'; unfold SHBASE in *; lia |].
      apply Forall_cons; [cbn [fst snd]; left; lia | apply Forall_nil]. }
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c
              [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] 0 msF1 R1 F fc 6000 _ (-4) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | reflexivity
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    subst TB2.
    pose proof (regs_keep w _ R1 R2 RT_PM_S8G_1 HTx1 KEEP2) as HT2.
    pose proof (ffkeepX_trans w [(6000, DS_SIZE)] [(6000, DS_SIZE)] [(6000, DS_SIZE)] m M1 m2 FK1 (s8g_fk w M1 m2 6000 FR2) (fun _ h => h) (fun _ h => h)) as FK2.
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8G_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    s8g_pc VIS3 APUT_CSEQ.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ _ _ _ _ 6000 (-4) 0 OK X2
                  (env_world_seed H w R2 []) Hlf3
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS2) as DS3.
    assert (FK3 : ffkeepX w [(6000, DS_SIZE)] m M3) by exact FK2.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M3 mo3 c
              [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF3 R3 F2 fc2 6000 _ 150176 30 (-4) 0 Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HTx3 | reflexivity | lia | rtf HTx3 | rtf HTx3 | exact G4_3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | s8g_acc
      | s8g_bytes
      | exact DS3
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 (DS4 & HR10_4) FR4.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w _ R3 R4 RT_PM_S8G_3 HTx3 KEEP4) as HT4.
    pose proof (ffkeepX_trans w [(6000, DS_SIZE)] [(6000, DS_SIZE)] [(6000, DS_SIZE)] m M3 m4 FK3 (s8g_fk w M3 m4 6000 FR4) (fun _ h => h) (fun _ h => h)) as FK4.
    pm_go HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 (@nil word) (@nil kentry) 100%nat [APUT_U16] (@nil bool) 41%N
          [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8G_5.
    { split_scs. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    s8g_pc VIS5 APUT_U16.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs m4 mo4 c _ _ _ _ _ _ _ 6000 (-4) (0 + 30) OK X4
                  (env_world_seed H w R4 []) Hlf5
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS4) as DS5.
    assert (FK5 : ffkeepX w [(6000, DS_SIZE)] m M5) by exact FK4.
    eapply (pm_put_num H HHbp LINV ds_repA DSL _ _ _ _ HU16 w s4 LB4 LBs M5 mo5 c
              [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF5 R5 F4 fc4 6000 _ 65535 (-4) (0 + 30) Q);
      [ exact OK | exact X5 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR5 | exact VIS5 | exact RF5 | exact FZ4
      | rtf HTx5 | reflexivity | lia | rtf HTx5 | rtf HTx5 | exact G4_5 | rtf HTx5 | rtf HTx5 | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | exact DS5
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF6 mo6 R6 F6 fc6 s6 LB6 m6 TB6 KR6 VIS6 RF6 FZ6 X6 KEEP6 (DS6 & HR10_6) FR6.
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    pose proof (regs_keep w _ R5 R6 RT_PM_S8G_5 HTx5 KEEP6) as HT6.
    pose proof (ffkeepX_trans w [(6000, DS_SIZE)] [(6000, DS_SIZE)] [(6000, DS_SIZE)] m M5 m6 FK5 (s8g_fk w M5 m6 6000 FR6) (fun _ h => h) (fun _ h => h)) as FK6.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8G_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    s8g_pc VIS7 APUT_CSEQ.
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s6 LB6 LBs m6 mo6 c _ _ _ _ _ _ _ 6000 (-4) (0 + 30 + 24) OK X6
                  (env_world_seed H w R6 []) Hlf7
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS6) as DS7.
    assert (FK7 : ffkeepX w [(6000, DS_SIZE)] m M7) by exact FK6.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s6 LB6 LBs M7 mo7 c
              [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF7 R7 F6 fc6 6000 _ 150240 8 (-4) (0 + 30 + 24) Q);
      [ exact OK | exact X7 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR7 | exact VIS7 | exact RF7 | exact FZ6
      | rtf HTx7 | reflexivity | lia | rtf HTx7 | rtf HTx7 | exact G4_7 | rtf HTx7 | rtf HTx7 | rtf HTx7
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | s8g_acc
      | s8g_bytes
      | exact DS7
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF8 mo8 R8 F8 fc8 s8 LB8 m8 TB8 KR8 VIS8 RF8 FZ8 X8 KEEP8 (DS8 & HR10_8) FR8.
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (transitivity (PropExec.getr R7 4%bv); [apply KEEP8; cbn; tauto | exact G4_7]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (transitivity (PropExec.getr R7 3%bv); [apply KEEP8; cbn; tauto | exact G3_7]).
    pose proof (regs_keep w _ R7 R8 RT_PM_S8G_7 HTx7 KEEP8) as HT8.
    pose proof (ffkeepX_trans w [(6000, DS_SIZE)] [(6000, DS_SIZE)] [(6000, DS_SIZE)] m M7 m8 FK7 (s8g_fk w M7 m8 6000 FR8) (fun _ h => h) (fun _ h => h)) as FK8.
    destruct (s8g_rf8 w _ _ _ _ _ _ _ _ _ _ _ 24 X8 OK ltac:(lia) ltac:(lia)) as (xj & Hxj & Cj).
    assert (HK9 : know_ok asegs (Eseed R8 (wenv_vals w ++ [Z_to_bv 64 xj])) m8 [KWord (SA (EVar WV_S1) 24) 8 (EVar 41)]).
    { pose proof (ev_s1 H w (Eseed R8 (wenv_vals w ++ [Z_to_bv 64 xj])) OK (env_world_seed H w R8 [Z_to_bv 64 xj])) as ES.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m8 (wa_s1 w + 24) _ 0%nat (C8 (Z_to_bv 64 xj)));
        [ exact Cj | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite ES; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity ]. }
    pm_goX HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 [Z_to_bv 64 xj]
          [KWord (SA (EVar WV_S1) 24) 8 (EVar 41)] HK9 100%nat [APUT_U64] (@nil bool) 42%N
          [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8G_9.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    s8g_pc VIS9 APUT_U64.
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s8 LB8 LBs m8 mo8 c _ _ _ _ _ _ _ 6000 (-4) (0 + 30 + 24 + 8) OK X8
                  (env_world_seed H w R8 [Z_to_bv 64 xj]) Hlf9
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS8) as DS9.
    assert (FK9 : ffkeepX w [(6000, DS_SIZE)] m M9) by exact FK8.
    eapply (pm_put_num H HHbp LINV ds_repA DSL _ _ _ _ HU64 w s8 LB8 LBs M9 mo9 c
              [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF9 R9 F8 fc8 6000 _ xj (-4) (0 + 30 + 24 + 8) Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ8
      | rtf HTx9 | reflexivity | lia | rtf HTx9 | rtf HTx9 | exact G4_9 | rtf HTx9 | rewrite (HR9 11%bv); reflexivity | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | exact DS9
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 (DS10 & HR10_10) FR10.
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (transitivity (PropExec.getr R9 4%bv); [apply KEEP10; cbn; tauto | exact G4_9]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (transitivity (PropExec.getr R9 3%bv); [apply KEEP10; cbn; tauto | exact G3_9]).
    pose proof (regs_tbl_restrict w [] _ R10 (rt_keep RT_PM_S8G_9) (regs_keep w _ R9 R10 RT_PM_S8G_9 HTx9 KEEP10) ltac:(vm_compute; reflexivity)) as HT10.
    pose proof (ffkeepX_trans w [(6000, DS_SIZE)] [(6000, DS_SIZE)] [(6000, DS_SIZE)] m M9 m10 FK9 (s8g_fk w M9 m10 6000 FR10) (fun _ h => h) (fun _ h => h)) as FK10.
    pm_go HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8G_11.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HTx11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M11 := mm) in * end.
    s8g_pc VIS11 APUT_CSEQ.
    assert (G4_11 : PropExec.getr R11 4%bv = wa_tp w) by (rewrite (HR11 4%bv); exact G4_10).
    assert (G3_11 : PropExec.getr R11 3%bv = wa_gp w) by (rewrite (HR11 3%bv); exact G3_10).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s10 LB10 LBs m10 mo10 c _ _ _ _ _ _ _ 6000 (-4) (0 + 30 + 24 + 8 + 24) OK X10
                  (env_world_seed H w R10 []) Hlf11
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS10) as DS11.
    assert (FK11 : ffkeepX w [(6000, DS_SIZE)] m M11) by exact FK10.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s10 LB10 LBs M11 mo11 c
              [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] _ _ msF11 R11 F10 fc10 6000 _ 150272 11 (-4) (0 + 30 + 24 + 8 + 24) Q);
      [ exact OK | exact X11 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR11 | exact VIS11 | exact RF11 | exact FZ10
      | rtf HTx11 | reflexivity | lia | rtf HTx11 | rtf HTx11 | exact G4_11 | rtf HTx11 | rtf HTx11 | rtf HTx11
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | s8g_acc
      | s8g_bytes
      | exact DS11
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF12 mo12 R12 F12 fc12 s12 LB12 m12 TB12 KR12 VIS12 RF12 FZ12 X12 KEEP12 (DS12 & HR10_12) FR12.
    assert (G4_12 : PropExec.getr R12 4%bv = wa_tp w) by (transitivity (PropExec.getr R11 4%bv); [apply KEEP12; cbn; tauto | exact G4_11]).
    assert (G3_12 : PropExec.getr R12 3%bv = wa_gp w) by (transitivity (PropExec.getr R11 3%bv); [apply KEEP12; cbn; tauto | exact G3_11]).
    pose proof (regs_keep w _ R11 R12 RT_PM_S8G_11 HTx11 KEEP12) as HT12.
    pose proof (ffkeepX_trans w [(6000, DS_SIZE)] [(6000, DS_SIZE)] [(6000, DS_SIZE)] m M11 m12 FK11 (s8g_fk w M11 m12 6000 FR12) (fun _ h => h) (fun _ h => h)) as FK12.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS12) as ERR12.
    assert (HK13 : know_ok asegs (Eseed R12 (wenv_vals w ++ [])) m12 [KWord (SA (EVar WV_FF) 6360) 4 (ELit 4294967292)]).
    { pose proof (ev_ff H w (Eseed R12 (wenv_vals w ++ [])) OK (env_world_seed H w R12 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m12 (wa_ff w + 6000 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-4) mod 2 ^ 32))));
        [exact ERR12 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X12 KR12 VIS12 RF12 HT12 (@nil word)
          [KWord (SA (EVar WV_FF) 6360) 4 (ELit 4294967292)] HK13 100%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8G_13.
    { split_scs. }
    intros msF13 mo13 R13 KR13 VIS13 RF13 X13 HTx13 HR13 Hlf13.
    lazymatch type of X13 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M13 := mm) in * end.
    s8g_pc VIS13 ADS_DTOR.
    assert (G4_13 : PropExec.getr R13 4%bv = wa_tp w) by (rewrite (HR13 4%bv); exact G4_12).
    assert (G3_13 : PropExec.getr R13 3%bv = wa_gp w) by (rewrite (HR13 3%bv); exact G3_12).
    assert (FK13 : ffkeepX w [(6000, DS_SIZE)] m M13) by exact FK12.
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s12 LB12 LBs M13 mo13 c
              [3; 4; 24; 25; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB12 _ msF13 R13 F12 fc12 6000 _ (-4) (0 + 30 + 24 + 8 + 24 + 11) Q);
      [ exact OK | exact X13 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR13 | exact VIS13 | exact RF13 | exact FZ12
      | rtf HTx13 | reflexivity | lia | rtf HTx13 | rtf HTx13 | exact G4_13 | rtf HTx13
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s12 LB12 LBs m12 mo12 c _ _ _ _ _ _ _ 6000 (-4) (0 + 30 + 24 + 8 + 24 + 11) OK X12
                  (env_world_seed H w R12 []) Hlf13);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS12]
      | cbn; tauto
      | ].
    intros msF14 mo14 R14 F14 fc14 s14 LB14 m14 TB14 KR14 VIS14 RF14 FZ14 X14 KEEP14 (TB14e & ADDR14) FR14.
    assert (G4_14 : PropExec.getr R14 4%bv = wa_tp w) by (transitivity (PropExec.getr R13 4%bv); [apply KEEP14; cbn; tauto | exact G4_13]).
    assert (G3_14 : PropExec.getr R14 3%bv = wa_gp w) by (transitivity (PropExec.getr R13 3%bv); [apply KEEP14; cbn; tauto | exact G3_13]).
    subst TB14.
    pose proof (regs_keep w _ R13 R14 RT_PM_S8G_13 HTx13 KEEP14) as HT14.
    pose proof (ffkeepX_trans w [(6000, DS_SIZE)] [(6000, DS_SIZE)] [(6000, DS_SIZE)] m M13 m14 FK13 (s8g_fk w M13 m14 6000 FR14) (fun _ h => h) (fun _ h => h)) as FK14.
    pm_go HHm LINV_frame OK X14 KR14 VIS14 RF14 HT14 (@nil word) (@nil kentry) 300%nat [0xf4164] (@nil bool) 41%N
          [3; 4; 24; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8G_15.
    { split_scs. }
    intros msF15 mo15 R15 KR15 VIS15 RF15 X15 HTx15 HR15 Hlf15.
    lazymatch type of X15 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M15 := mm) in * end.
    s8g_pc VIS15 0xf4164.
    destruct (ev_world_all H w _ (env_world_seed H w R14 (@nil word))) as (_ & TEB15 & _).
    pose proof (munch_sym (Eseed R14 (wenv_vals w ++ (@nil word))) m14 _ [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)]
                  Hlf15 ltac:(vm_compute; reflexivity)) as TMU15.
    cbn [num_wins map] in TMU15. rewrite (srl3_val _ (EVar 33) (wa_ff w) TEB15 ltac:(lia)) in TMU15.
    assert (FK15 : ffkeepX w [(6000, DS_SIZE)] m M15).
    { apply (ffkeepX_trans w _ [] _ m m14 M15 FK14); [| intros ? h; exact h | intros ? []].
      apply (ffkeepX_munch w _ _ _ _ TMU15 (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      destruct Q6 as [Q6'|Q6']; [left | right; left]; rewrite Q13 in Q6'; unfold SHBASE in *; lia. }
    eapply (K s14 LB14 LBs msF15 mo15 M15 R15 F14 fc14 TBL_EEF44 _ KR15 VIS15 RF15 FZ14 X15 (fun _ h => h));
      [ unfold ds_cost; lia
      | exact (regs_tbl_sub w [] R15 RT_PM_S8G_15 RT_S8D0 HTx15 ltac:(vm_compute; reflexivity))
      | rewrite (HR15 3%bv); exact G3_14
      | rewrite (HR15 4%bv); exact G4_14
      | rtf HTx15
      | exact (ffkeepX_cell w _ m M15 5936 _ FK15 HB0 ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
      | exact (ffkeepX_cell w _ m M15 5936 _ FK15 HCP ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
      | exact (ffkeepX_cell w _ m M15 5952 _ FK15 HDP ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
      | exact (ffkeepX_cell w _ m M15 116 _ FK15 HTY ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) ].
  Qed.

End S8g.
