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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmFin LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_PmU7a.

Definition RT_PM_U7_DB_1 : list (reg * expr) := [(1%bv, ELit 997808); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 4032)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551615); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 4032)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 4000)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U7_DB_3 : list (reg * expr) := [(1%bv, ELit 997828); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 4032)); (11%bv, ELit 149856); (12%bv, ELit 39); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 4032)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 4000)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U7_DB_5 : list (reg * expr) := [(1%bv, ELit 997840); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 4032)); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 4032)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 4000)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, ELit 18446744073709551615); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U7_DB_7 : list (reg * expr) := [(1%bv, ELit 997840); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 4032)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, ELit 18446744073709551615); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_S7DB : list (reg * expr) := rt_keep RT_PM_U7_2_1.

Ltac lit_acc :=
  lazymatch goal with |- forall _, ACONST _ -> accessible _ ?p ?n =>
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p);
      [ eapply (ACONST_global_addressable M' p _ _ ACM'); [unfold aglobals; repeat (first [left; reflexivity | right]) | lia]
      | lia | lia | unfold AAPP_HI; lia ]
  end.
Ltac lit_bytes :=
  lazymatch goal with |- exists bs, length bs = Z.to_nat ?n /\ forall _, mem_inv asegs _ -> bytes_at asegs _ ?p bs =>
    let nn := eval vm_compute in (Z.to_nat n) in
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) nn) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (img_lit M' p nn bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end
  end.
Section U7db.
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
  Hypothesis HPDIAGE : pdiagE_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTbAPmU7db_0 : list (Z * expr) := [(32, EAlu ALU_ADD (EVar 33) (ELit 5472)); (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032)); (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008)); (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (104, ELit 65535); (112, EAlu ALU_ADD (EVar 33) (ELit 6000)); (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024)); (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120)); (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (176, ELit 262140); (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512)); (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576)); (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488)); (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (272, EAlu ALU_ADD (EVar 32) (ELit 96)); (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512)); (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928)); (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216)); (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (432, EAlu ALU_ADD (EVar 32) (ELit 232)); (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224)); (456, EAlu ALU_ADD (EVar 33) (ELit 64)); (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88)); (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48)); (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952); (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240)); (568, EVar 33); (576, EVar 33); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880); (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (632, EAlu ALU_ADD (EVar 32) (ELit 264)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32); (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72)); (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32); (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].
  Lemma pm_u7_db : forall (w : pmwA H) s LB LBs m mo c msF R F fc (r : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 17; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 997584) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S7DB -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 r ->
    r <> 0 /\ - 2 ^ 31 <= r < 2 ^ 31 ->
    pm_bud (wa_n w) c ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc r Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HR10 HRr BUD K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [])) m [KRange (EVar 10) 1 (2 ^ 64)]).
    { apply Forall_cons; [| apply Forall_nil].
      cbn [kentry_ok].
      change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 10)) with (PropExec.getr R 10%bv).
      rewrite HR10, Z_to_bv_unsigned, bv_wrap64_mod. destruct HRr as [Hr0 Hrr].
      pose proof (Z.mod_pos_bound r (2 ^ 64) ltac:(lia)) as MB.
      assert (r mod 2 ^ 64 <> 0) by (intro E0; apply Z.mod_divide in E0; [destruct E0 as [k Hk]; nia | lia]). lia. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 10) 1 (2 ^ 64)] HK1 400%nat [APDIAG_E] (@nil bool) 41%N
          [3; 4; 17; 18; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU7db_0 (@nil (Z * expr)) RT_PM_U7_DB_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    replace (s_pc SSr) with APDIAG_E in VIS1 by reflexivity.
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG_E true HPDIAGE w s LB LBs M1 mo1 c
              [3; 4; 17; 18; 39; 40; 41; 43; 45]%nat HTbAPmU7db_0 [] 0 msF1 R1 F fc 4032 _ (-1) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2. subst TB2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    pose proof (regs_keep w _ R1 R2 RT_PM_U7_DB_1 HTx1 KEEP2) as HT2.
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry) 200%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 17; 18; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU7db_0 (@nil (Z * expr)) RT_PM_U7_DB_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    replace (s_pc SSr0) with APUT_CSEQ in VIS3 by reflexivity.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M3 mo3 c
              [3; 4; 17; 18; 39; 40; 41; 43; 45]%nat HTbAPmU7db_0 [] [] 0 msF3 R3 F2 fc2 4032 _ _ _ (-1) 0 Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HTx3 | reflexivity | lia | rtf HTx3 | rtf HTx3 | exact G4_3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc
      | lit_bytes
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ [] 0 _ _ 4032 (-1) 0 OK X2 (env_world_seed H w R2 []) Hlf3);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS2]
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 (DS4 & HR10_4) FR4.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w _ R3 R4 RT_PM_U7_DB_3 HTx3 KEEP4) as HT4.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS4) as ERR4.
    assert (HK4 : know_ok asegs (Eseed R4 (wenv_vals w ++ [])) m4 [KWord (SA (EVar WV_FF) 4392) 4 (ELit 4294967295)]).
    { pose proof (ev_ff H w (Eseed R4 (wenv_vals w ++ [])) OK (env_world_seed H w R4 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m4 (wa_ff w + 4032 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-1) mod 2 ^ 32))));
        [exact ERR4 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 (@nil word)
          [KWord (SA (EVar WV_FF) 4392) 4 (ELit 4294967295)] HK4 200%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 17; 18; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU7db_0 (@nil (Z * expr)) RT_PM_U7_DB_5.
    { split_scs. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    replace (s_pc SSr1) with ADS_DTOR in VIS5 by reflexivity.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s4 LB4 LBs M5 mo5 c
              [3; 4; 17; 18; 39; 40; 41; 43; 45]%nat HTbAPmU7db_0 [] TB4 _ msF5 R5 F4 fc4 4032 _ (-1) (0 + 39) Q);
      [ exact OK | exact X5 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR5 | exact VIS5 | exact RF5 | exact FZ4
      | rtf HTx5 | reflexivity | lia | rtf HTx5 | rtf HTx5 | exact G4_5 | rtf HTx5
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs m4 mo4 c _ _ _ _ _ _ _ 4032 (-1) (0 + 39) OK X4 (env_world_seed H w R4 []) Hlf5);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS4]
      | cbn; tauto
      | ].
    intros msF6 mo6 R6 F6 fc6 s6 LB6 m6 TB6 KR6 VIS6 RF6 FZ6 X6 KEEP6 (TB6e & ADDR6) FR6. subst TB6.
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    pose proof (regs_keep w _ R5 R6 RT_PM_U7_DB_5 HTx5 KEEP6) as HT6.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word) (@nil kentry) 400%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU7db_0 (@nil (Z * expr)) RT_PM_U7_DB_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    replace (s_pc SSr2) with OL_CHECK in VIS7 by reflexivity.
    eapply (K s6 LB6 LBs M7 mo7 c msF7 R7 F6 fc6 HTbAPmU7db_0 _ 4294967295);
      [ exact X7 | apply tbl_incl; vm_compute; reflexivity | exact Htr | exact BUD | exact Hbsz | exact KR7 | exact VIS7 | exact RF7
      | exact FZ6 | exact (regs_tbl_sub w [] R7 RT_PM_U7_DB_7 RT_CHECK HTx7 ltac:(vm_compute; reflexivity))
      | rewrite (HR7 3%bv); exact G3_6 | rewrite (HR7 4%bv); exact G4_6 | rtf HTx7 | lia ].
  Qed.

End U7db.
