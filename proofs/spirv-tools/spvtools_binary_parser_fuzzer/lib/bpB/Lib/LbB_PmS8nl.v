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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_ContStmt LbB_PmLH LbB_PmVops LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_PmWXK LbB_PmS8K LbB_PmStrX.

Definition RT_PM_S8N_L_1 : list (reg * expr) := [(1%bv, ELit 998916); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551612); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8N_L_3 : list (reg * expr) := [(1%bv, ELit 998936); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (11%bv, ELit 150304); (12%bv, ELit 37); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8N_L_5 : list (reg * expr) := [(1%bv, ELit 999544); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (11%bv, EVar 43); (12%bv, EVar 42); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8N_L_7 : list (reg * expr) := [(1%bv, ELit 999564); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (11%bv, ELit 150400); (12%bv, ELit 1); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8N_L_9 : list (reg * expr) := [(1%bv, ELit 999576); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 6464)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_S8N_L_11 : list (reg * expr) := [(1%bv, ELit 999576); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 0); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Ltac s8nl_acc :=
  lazymatch goal with |- forall _, ACONST _ -> accessible _ ?p ?n =>
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p);
      [ eapply (ACONST_global_addressable M' p _ _ ACM'); [unfold aglobals; repeat (first [left; reflexivity | right]) | lia]
      | lia | lia | unfold AAPP_HI; lia ]
  end.
Ltac s8nl_bytes :=
  lazymatch goal with |- exists bs, length bs = Z.to_nat ?n /\ forall _, mem_inv asegs _ -> bytes_at asegs _ ?p bs =>
    let nn := eval vm_compute in (Z.to_nat n) in
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) nn) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (img_lit M' p nn bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end
  end.
Ltac s8nl_pc VIS pc :=
  lazymatch type of VIS with context [s_pc ?ss] => replace (s_pc ss) with pc in VIS by reflexivity end.

Lemma s8nl_fk {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) (m m1 : mem) (dso : Z),
  (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
     (wa_ff w + k + Z.of_nat (cells_size cs) <= wa_ff w + dso \/ wa_ff w + dso + DS_SIZE <= wa_ff w + k) ->
     rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
  ffkeepX w [(dso, DS_SIZE)] m m1.
Proof.
  intros w m m1 dso FR k cs Hk Hn F C. apply (FR k cs Hk Hn); [| exact C].
  apply Forall_inv in F. cbn [fst snd] in F. lia.
Qed.

Section S8nl.
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
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

  Lemma pm_s8n_l : forall (w : pmwA H) s LB LBs m mo c msF R F fc (b0 sz cp dp ty asz : Z) (pid : bptr) (bs : list byte) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 24; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> True ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf31d8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S8C0 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    pm_bud (wa_n w) c ->
    rw_cells asegs m (wa_ff w + 5936) [C1 (b8 b0)] ->
    0 <= b0 < 256 /\ b0 mod 2 = 1 ->
    rw_cells asegs m (wa_ff w + 5944) [C8 (Z_to_bv 64 sz)] ->
    0 <= sz < 262140 ->
    rw_cells asegs m (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] ->
    rw_cells asegs m (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] ->
    0 <= dp < 2 ^ 64 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] ->
    In (pid, dp, asz) LBs ->
    sz <= asz ->
    length bs = Z.to_nat sz ->
    bytes_at asegs m dp bs ->
    SHAD m dp (shadow_of asz) ->
    (forall (s1 : as_St H) (LB1 LBs1 : list block) msF1 mo1 m1 R1 F1 fc1 tbl1 (spal1 : Z), as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 0xf4164) fc1 None m1 (seg_rom asegs) -> rfull R1 -> frm_zero fc1 -> PMXAT H LINV w s1 LB1 LBs1 m1 mo1 c S_STR tbl1 [] [] spal1 -> incl TBL_EEF44 tbl1 -> 0 <= spal1 <= 2 ^ 24 -> regs_tbl w R1 RT_S8D0 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A (2 ^ 32 - 4)) -> rw_cells asegs m1 (wa_ff w + 5936) [C1 (b8 b0)] -> rw_cells asegs m1 (wa_ff w + 5936) [C8 (Z_to_bv 64 cp)] -> rw_cells asegs m1 (wa_ff w + 5952) [C8 (Z_to_bv 64 dp)] -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 ty)] -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame DSL HCSEQ HDTOR HPDIAG0.
    intros w s LB LBs m mo c msF R F fc b0 sz cp dp ty asz pid bs Q OK X0 _ Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD
           HB0 HB0R HSZ HSZR HCP HDP HDPR HTY HIN HASZ HBL HBY HSH K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    destruct HB0R as [HB0a HB0b].
    assert (HBL' : Z.of_nat (length bs) <= asz) by (rewrite HBL, Z2Nat.id by lia; lia).
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word) (@nil kentry) 400%nat [APDIAG] (@nil bool) 41%N
          [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8N_L_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    s8nl_pc VIS1 APDIAG.
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    destruct (ev_world_all H w _ (env_world_seed H w R (@nil word))) as (_ & TEB1 & _).
    pose proof (munch_sym (Eseed R (wenv_vals w ++ (@nil word))) m _ [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)]
                  Hlf1 ltac:(vm_compute; reflexivity)) as TMU1.
    cbn [num_wins map] in TMU1. rewrite (srl3_val _ (EVar 33) (wa_ff w) TEB1 ltac:(lia)) in TMU1.
    assert (FK1 : ffkeepX w [(6464, DS_SIZE)] m M1).
    { apply (ffkeepX_mono w []); [| intros ? []].
      apply (ffkeepX_munch w _ _ _ _ TMU1 (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      destruct Q6 as [Q6'|Q6']; [left | right; left]; rewrite Q13 in Q6'; unfold SHBASE in *; lia. }
    destruct (blk_keep_fsh H HHbp LINV w s LB LBs m mo c _ _ _ _ _ M1 pid dp asz bs OK X0 HIN TMU1 (wmono_mem_denot _ _ _) HBY HBL' HSH)
      as (BY1 & SH1).
    eapply (pm_pdiagX H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c
              [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] 0 msF1 R1 F fc 6464 0xf3e04 (-4) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | reflexivity
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 XS2 LBk2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2 RFS2 FSX2 XP2 LBK2. subst TB2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    pose proof (regs_keep w _ R1 R2 RT_PM_S8N_L_1 HTx1 KEEP2) as HT2.
    pose proof (ffkeepX_trans w [(6464, DS_SIZE)] [(6464, DS_SIZE)] [(6464, DS_SIZE)] m M1 m2 FK1 (s8nl_fk w M1 m2 6464 FR2) (fun _ h => h) (fun _ h => h)) as FK2.
    destruct (blk_keep_xpres H HHbp LINV w s LB LBs M1 mo1 c _ _ _ _ _ m2 XS2 LBk2 6464 pid dp asz bs OK X1 HIN LBK2
                ltac:(lia) ltac:(unfold DS_SIZE; lia) ltac:(apply Forall_nil) RFS2 FSX2 XP2 BY1 HBL' SH1) as (BY2 & SH2).
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8N_L_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    s8nl_pc VIS3 APUT_CSEQ.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ _ _ _ _ 6464 (-4) 0 OK X2 (env_world_seed H w R2 []) Hlf3
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS2) as DS3.
    assert (FK3 : ffkeepX w [(6464, DS_SIZE)] m M3) by exact FK2.
    assert (BY3 : bytes_at asegs M3 dp bs) by exact BY2.
    assert (SH3 : SHAD M3 dp (shadow_of asz)) by exact SH2.
    eapply (pm_put_cseq_imgX H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M3 mo3 c
              [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] [] 0 msF3 R3 F2 fc2 6464 0xf3e18 150304 37 (-4) 0 Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HTx3 | reflexivity | lia | rtf HTx3 | rtf HTx3 | exact G4_3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | s8nl_acc
      | s8nl_bytes
      | exact DS3
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 XS4 LBk4 KR4 VIS4 RF4 FZ4 X4 KEEP4 (DS4 & HR10_4) FR4 RFS4 FSX4 XP4 LBK4.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w _ R3 R4 RT_PM_S8N_L_3 HTx3 KEEP4) as HT4.
    pose proof (ffkeepX_trans w [(6464, DS_SIZE)] [(6464, DS_SIZE)] [(6464, DS_SIZE)] m M3 m4 FK3 (s8nl_fk w M3 m4 6464 FR4) (fun _ h => h) (fun _ h => h)) as FK4.
    destruct (blk_keep_xpres H HHbp LINV w s2 LB2 LBs M3 mo3 c _ _ _ _ _ m4 XS4 LBk4 6464 pid dp asz bs OK X3 HIN LBK4
                ltac:(lia) ltac:(unfold DS_SIZE; lia) ltac:(apply Forall_nil) RFS4 FSX4 XP4 BY3 HBL' SH3) as (BY4 & SH4).
    pose proof (ffkeepX_cell w _ m m4 5936 _ FK4 HB0 ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as HB0_4.
    pose proof (ffkeepX_cell w _ m m4 5944 _ FK4 HSZ ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as HSZ_4.
    pose proof (ffkeepX_cell w _ m m4 5952 _ FK4 HDP ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as HDP_4.
    pose proof (ev_ff H w _ OK (env_world_seed H w R4 [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 dp])) as EF4.
    assert (E41 : edenot (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 dp])) (EVar 41) = Z_to_bv 64 b0) by reflexivity.
    assert (E42 : edenot (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 dp])) (EVar 42) = Z_to_bv 64 sz) by reflexivity.
    assert (E43 : edenot (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 dp])) (EVar 43) = Z_to_bv 64 dp) by reflexivity.
    assert (HK5 : know_ok asegs (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 dp])) m4
                    [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42); KWord (SA (EVar WV_FF) 5952) 8 (EVar 43)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
      - eapply (kword_of_rw_cells asegs _ m4 (wa_ff w + 5936) _ 0%nat (C1 (b8 b0)));
          [exact HB0_4 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF4; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; symmetry; apply w1_b8; lia].
      - eapply (kword_of_rw_cells asegs _ m4 (wa_ff w + 5944) _ 0%nat (C8 (Z_to_bv 64 sz)));
          [exact HSZ_4 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF4; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E42; reflexivity].
      - eapply (kword_of_rw_cells asegs _ m4 (wa_ff w + 5952) _ 0%nat (C8 (Z_to_bv 64 dp)));
          [exact HDP_4 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF4; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E43; reflexivity]. }
    pm_goX HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 dp]
          [KWord (SA (EVar WV_FF) 5936) 1 (EVar 41); KWord (SA (EVar WV_FF) 5944) 8 (EVar 42); KWord (SA (EVar WV_FF) 5952) 8 (EVar 43)] HK5
          60%nat [APUT_CSEQ] [true] 44%N
          [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8N_L_5.
    { split_scs. cbn [sc_denot]. rewrite (sc_b0_long_ne _ 41 b0 E41 HB0a), HB0b. reflexivity. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    s8nl_pc VIS5 APUT_CSEQ.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs m4 mo4 c _ _ _ _ _ _ _ 6464 (-4) (0 + 37) OK X4
                  (env_world_seed H w R4 [Z_to_bv 64 b0; Z_to_bv 64 sz; Z_to_bv 64 dp]) Hlf5
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS4) as DS5.
    assert (FK5 : ffkeepX w [(6464, DS_SIZE)] m M5) by exact FK4.
    assert (BY5 : bytes_at asegs M5 dp bs) by exact BY4.
    assert (SH5 : SHAD M5 dp (shadow_of asz)) by exact SH4.
    eapply (pm_put_cseq_blk H HHbp LINV ds_repA DSL HCSEQ w s4 LB4 LBs M5 mo5 c
              [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB4 (0 + ds_cost (0 + 37)) msF5 R5 F4 fc4 6464 0xf4078 dp sz (-4) (0 + 37) Q);
      [ exact OK | exact X5 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR5 | exact VIS5 | exact RF5 | exact FZ4
      | rtf HTx5 | reflexivity | lia | rtf HTx5 | rtf HTx5 | exact G4_5 | rtf HTx5 | rtf HTx5 | rtf HTx5
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | unfold blk_src; split; [lia|]; split; [lia|]; exists pid, asz, bs; refine (conj HIN (conj _ (conj HBL (conj BY5 SH5)))); lia
      | exact DS5
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF6 mo6 R6 F6 fc6 s6 LB6 m6 TB6 KR6 VIS6 RF6 FZ6 X6 KEEP6 (DS6 & HR10_6) FR6.
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    pose proof (regs_tbl_restrict w [] _ R6 (rt_keep RT_PM_S8N_L_5) (regs_keep w _ R5 R6 RT_PM_S8N_L_5 HTx5 KEEP6) ltac:(vm_compute; reflexivity)) as HT6.
    pose proof (ffkeepX_trans w [(6464, DS_SIZE)] [(6464, DS_SIZE)] [(6464, DS_SIZE)] m M5 m6 FK5 (s8nl_fk w M5 m6 6464 FR6) (fun _ h => h) (fun _ h => h)) as FK6.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8N_L_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    s8nl_pc VIS7 APUT_CSEQ.
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s6 LB6 LBs m6 mo6 c _ _ _ _ _ _ _ 6464 (-4) (0 + 37 + sz) OK X6 (env_world_seed H w R6 []) Hlf7
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS6) as DS7.
    assert (FK7 : ffkeepX w [(6464, DS_SIZE)] m M7) by exact FK6.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s6 LB6 LBs M7 mo7 c
              [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB6 (0 + ds_cost (0 + 37) + ds_cost (0 + 37 + sz)) msF7 R7 F6 fc6
              6464 0xf408c 150400 1 (-4) (0 + 37 + sz) Q);
      [ exact OK | exact X7 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR7 | exact VIS7 | exact RF7 | exact FZ6
      | rtf HTx7 | reflexivity | lia | rtf HTx7 | rtf HTx7 | exact G4_7 | rtf HTx7 | rtf HTx7 | rtf HTx7
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | s8nl_acc
      | s8nl_bytes
      | exact DS7
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF8 mo8 R8 F8 fc8 s8 LB8 m8 TB8 KR8 VIS8 RF8 FZ8 X8 KEEP8 (DS8 & HR10_8) FR8.
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (transitivity (PropExec.getr R7 4%bv); [apply KEEP8; cbn; tauto | exact G4_7]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (transitivity (PropExec.getr R7 3%bv); [apply KEEP8; cbn; tauto | exact G3_7]).
    pose proof (regs_keep w _ R7 R8 RT_PM_S8N_L_7 HTx7 KEEP8) as HT8.
    pose proof (ffkeepX_trans w [(6464, DS_SIZE)] [(6464, DS_SIZE)] [(6464, DS_SIZE)] m M7 m8 FK7 (s8nl_fk w M7 m8 6464 FR8) (fun _ h => h) (fun _ h => h)) as FK8.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS8) as ERR8.
    assert (HK9 : know_ok asegs (Eseed R8 (wenv_vals w ++ [])) m8 [KWord (SA (EVar WV_FF) 6824) 4 (ELit 4294967292)]).
    { pose proof (ev_ff H w (Eseed R8 (wenv_vals w ++ [])) OK (env_world_seed H w R8 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m8 (wa_ff w + 6464 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-4) mod 2 ^ 32))));
        [exact ERR8 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word)
          [KWord (SA (EVar WV_FF) 6824) 4 (ELit 4294967292)] HK9 100%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8N_L_9.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    s8nl_pc VIS9 ADS_DTOR.
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    assert (FK9 : ffkeepX w [(6464, DS_SIZE)] m M9) by exact FK8.
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s8 LB8 LBs M9 mo9 c
              [3; 4; 24; 26; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] TB8 _ msF9 R9 F8 fc8 6464 0xf4098 (-4) (0 + 37 + sz + 1) Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ8
      | rtf HTx9 | reflexivity | lia | rtf HTx9 | rtf HTx9 | exact G4_9 | rtf HTx9
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s8 LB8 LBs m8 mo8 c _ _ _ _ _ _ _ 6464 (-4) (0 + 37 + sz + 1) OK X8
                  (env_world_seed H w R8 []) Hlf9);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS8]
      | cbn; tauto
      | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 (TB10e & ADDR10) FR10. subst TB10.
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (transitivity (PropExec.getr R9 4%bv); [apply KEEP10; cbn; tauto | exact G4_9]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (transitivity (PropExec.getr R9 3%bv); [apply KEEP10; cbn; tauto | exact G3_9]).
    pose proof (regs_keep w _ R9 R10 RT_PM_S8N_L_9 HTx9 KEEP10) as HT10.
    pose proof (ffkeepX_trans w [(6464, DS_SIZE)] [(6464, DS_SIZE)] [(6464, DS_SIZE)] m M9 m10 FK9 (s8nl_fk w M9 m10 6464 FR10) (fun _ h => h) (fun _ h => h)) as FK10.
    pm_go HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word) (@nil kentry) 300%nat [0xf4164] (@nil bool) 41%N
          [3; 4; 24; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_S8N_L_11.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HTx11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M11 := mm) in * end.
    s8nl_pc VIS11 0xf4164.
    destruct (ev_world_all H w _ (env_world_seed H w R10 (@nil word))) as (_ & TEB11 & _).
    pose proof (munch_sym (Eseed R10 (wenv_vals w ++ (@nil word))) m10 _ [(EAlu ALU_SRL (EVar 33) (ELit 3), 2147450880, 2147452928)]
                  Hlf11 ltac:(vm_compute; reflexivity)) as TMU11.
    cbn [num_wins map] in TMU11. rewrite (srl3_val _ (EVar 33) (wa_ff w) TEB11 ltac:(lia)) in TMU11.
    assert (FK11 : ffkeepX w [(6464, DS_SIZE)] m M11).
    { apply (ffkeepX_trans w _ [] _ m m10 M11 FK10); [| intros ? h; exact h | intros ? []].
      apply (ffkeepX_munch w _ _ _ _ TMU11 (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      destruct Q6 as [Q6'|Q6']; [left | right; left]; rewrite Q13 in Q6'; unfold SHBASE in *; lia. }
    eapply (K s10 LB10 LBs msF11 mo11 M11 R11 F10 fc10 TBL_EEF44 _ KR11 VIS11 RF11 FZ10 X11 (fun _ h => h));
      [ unfold ds_cost; lia
      | exact (regs_tbl_sub w [] R11 RT_PM_S8N_L_11 RT_S8D0 HTx11 ltac:(vm_compute; reflexivity))
      | rewrite (HR11 3%bv); exact G3_10
      | rewrite (HR11 4%bv); exact G4_10
      | rtf HTx11
      | exact (ffkeepX_cell w _ m M11 5936 _ FK11 HB0 ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
      | exact (ffkeepX_cell w _ m M11 5936 _ FK11 HCP ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
      | exact (ffkeepX_cell w _ m M11 5952 _ FK11 HDP ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity))
      | exact (ffkeepX_cell w _ m M11 116 _ FK11 HTY ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) ].
  Qed.

End S8nl.
