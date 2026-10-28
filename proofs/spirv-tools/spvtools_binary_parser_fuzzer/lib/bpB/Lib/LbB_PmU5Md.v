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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_PmU5K LbB_RwKit.

Definition RT_PM_U5M_D_1 : list (reg * expr) := [(1%bv, ELit 990336); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551612); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_3 : list (reg * expr) := [(1%bv, ELit 990356); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (11%bv, ELit 149792); (12%bv, ELit 8); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_5 : list (reg * expr) := [(1%bv, ELit 990368); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_7 : list (reg * expr) := [(1%bv, ELit 990376); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_9 : list (reg * expr) := [(1%bv, ELit 990396); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_11 : list (reg * expr) := [(1%bv, ELit 990416); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (11%bv, ELit 150432); (12%bv, ELit 10); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_13 : list (reg * expr) := [(1%bv, ELit 990432); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_15 : list (reg * expr) := [(1%bv, ELit 990452); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (11%bv, ELit 150656); (12%bv, ELit 28); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_17 : list (reg * expr) := [(1%bv, ELit 990464); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_19 : list (reg * expr) := [(1%bv, ELit 990476); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 8016)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U5M_D_21 : list (reg * expr) := [(1%bv, ELit 990476); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Ltac lit_acc5 :=
  lazymatch goal with |- forall _, ACONST _ -> accessible _ ?p ?n =>
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p);
      [ eapply (ACONST_global_addressable M' p _ _ ACM'); [unfold aglobals; repeat (first [left; reflexivity | right]) | lia]
      | lia | lia | unfold AAPP_HI; lia ]
  end.
Ltac lit_bytes5 :=
  lazymatch goal with |- exists bs, length bs = Z.to_nat ?n /\ forall _, mem_inv asegs _ -> bytes_at asegs _ ?p bs =>
    let nn := eval vm_compute in (Z.to_nat n) in
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) nn) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (img_lit M' p nn bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end
  end.
Ltac fixpc5 VIS pc :=
  lazymatch type of VIS with context [s_pc ?ss] => replace (s_pc ss) with pc in VIS by reflexivity end.
Ltac stk5 := first [ lia | unfold TL_STACK, AINTRIN_STACK; lia | vm_compute; split; discriminate ].
Section U5Md.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTbAPmU5Md_0 : list (Z * expr) := [(32, EAlu ALU_ADD (EVar 33) (ELit 5472)); (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032)); (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008)); (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (104, ELit 65535); (112, EAlu ALU_ADD (EVar 33) (ELit 6000)); (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024)); (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120)); (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (176, ELit 262140); (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512)); (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576)); (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488)); (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (272, EAlu ALU_ADD (EVar 32) (ELit 96)); (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512)); (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928)); (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216)); (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (432, EAlu ALU_ADD (EVar 32) (ELit 232)); (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224)); (456, EAlu ALU_ADD (EVar 33) (ELit 64)); (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88)); (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48)); (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952); (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240)); (568, EVar 33); (576, EVar 33); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880); (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (632, EAlu ALU_ADD (EVar 32) (ELit 264)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32); (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72)); (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32); (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].
  Lemma pm_u5m_d : forall (w : pmwA H) s LB LBs m mo c msF R F fc (r et j : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 33; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf188c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ML -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 r ->
    r <> 0 /\ - 2 ^ 31 <= r < 2 ^ 31 ->
    PropExec.getr R 23%bv = Z_to_bv 64 (sx32A (2 ^ j)) ->
    0 <= j <= 31 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 et)] ->
    0 <= et < 2 ^ 31 ->
    pm_bud (wa_n w) c ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame DSL HCSEQ HDTOR HU32 HTL LINV_relro HPDIAG0.
    intros w s LB LBs m mo c msF R F fc r et j Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 A0 (Hr0 & Hr1) G23_0 Hj Cet Het BUD K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (p_range H w OK) as [PR1 PR2].
    assert (HK0 : know_ok asegs (Eseed R (wenv_vals w ++ [])) m
                    [KRange (EVar 10) 1 (2 ^ 64); KWord (SA (EVar WV_P) 40) 1 (ELit 0)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - assert (EA : edenot (Eseed R (wenv_vals w ++ [])) (EVar 10) = Z_to_bv 64 r) by exact A0.
        cbn [kentry_ok]. rewrite EA, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
        split; Z.div_mod_to_equations; lia.
      - eapply (kword_of_fld _ m (wa_p w + 40) 1 0);
          [ exact (xa_hunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia
          | exact (estart_p H w _ 40 OK (env_world_seed H w R []))
          | unfold AIMG_TOP in *; lia | unfold AIMG_TOP, PARSER_SIZE in *; lia | reflexivity ]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 10) 1 (2 ^ 64); KWord (SA (EVar WV_P) 40) 1 (ELit 0)] HK0 400%nat [APDIAG] (@nil bool) 41%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    fixpc5 VIS1 APDIAG.
    pose proof (ev_world_all H w (Eseed R (wenv_vals w ++ [])) (env_world_seed H w R [])) as (_ & EV33 & _).
    assert (UFS : bv_unsigned (edenot (Eseed R (wenv_vals w ++ [])) FSHB) = wa_ff w / 8)
      by (unfold FSHB; apply srl3_val; [exact EV33 | lia]).
    assert (FK1 : ffkeepX w [] m M1).
    { pose proof (munch_sym _ m (s_log SSr) [(FSHB, SHBASE, SHBASE + PM_NSH)] Hlf1
                    ltac:(vm_compute; reflexivity)) as MU.
      cbn [num_wins map] in MU. rewrite UFS in MU.
      apply (ffkeepX_munch w _ _ _ _ MU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_nil]; cbn [fst snd].
      unfold PM_NSH. destruct Q6 as [D|D]; [left | right; left]; lia. }
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G23_1 : PropExec.getr R1 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (HR1 23%bv); exact G23_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c
              [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat HTbAPmU5Md_0 [] 0 msF1 R1 F fc 8016 _ (-4) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | first [reflexivity | cbn; reflexivity]
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G23_2 : PropExec.getr R2 23%bv = Z_to_bv 64 (sx32A (2 ^ j)))
      by (transitivity (PropExec.getr R1 23%bv); [apply KEEP2; cbn; tauto | exact G23_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    subst TB2.
    pose proof (regs_keep w _ R1 R2 RT_PM_U5M_D_1 HTx1 KEEP2) as HT2.
    assert (Cet2 : rw_cells asegs m2 (wa_ff w + 116) [C4 (Z_to_bv 64 et)]).
    { apply (FR2 116 _); [lia | cbn; lia | left; cbn; lia |].
      apply (FK1 116 _); [lia | cbn; lia | apply Forall_nil | exact Cet]. }
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word)
          (@nil kentry) 200%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    fixpc5 VIS3 APUT_CSEQ.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G23_3 : PropExec.getr R3 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (HR3 23%bv); exact G23_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    assert (Cet3 : rw_cells asegs M3 (wa_ff w + 116) [C4 (Z_to_bv 64 et)]).
    { pose proof (munch_sym _ m2 (s_log SSr0) [] Hlf3 ltac:(vm_compute; reflexivity)) as MU.
      cbn [num_wins map] in MU.
      apply (ffkeepX_munch w [] _ m2 M3 MU (wmono_mem_denot _ _ _) ltac:(apply Forall_nil) 116 _);
        [lia | cbn; lia | apply Forall_nil | exact Cet2]. }
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M3 mo3 c
              [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat HTbAPmU5Md_0 [] [] 0 msF3 R3 F2 fc2 8016 _ _ _ (-4) (0) Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HTx3 | reflexivity | lia | rtf HTx3 | rtf HTx3 | exact G4_3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc5
      | lit_bytes5
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ [] 0 _ _ 8016 (-4) (0) OK X2 (env_world_seed H w R2 []) Hlf3);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS2]
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 (DS4 & HR10_4) FR4.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G23_4 : PropExec.getr R4 23%bv = Z_to_bv 64 (sx32A (2 ^ j)))
      by (transitivity (PropExec.getr R3 23%bv); [apply KEEP4; cbn; tauto | exact G23_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w _ R3 R4 RT_PM_U5M_D_3 HTx3 KEEP4) as HT4.
    assert (Cet4 : rw_cells asegs m4 (wa_ff w + 116) [C4 (Z_to_bv 64 et)])
      by (apply (FR4 116 _); [lia | cbn; lia | left; cbn; lia | exact Cet3]).
    assert (HK4 : know_ok asegs (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 et])) m4 [KWord (SA (EVar WV_FF) 116) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 et])) OK (env_world_seed H w R4 [Z_to_bv 64 et])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m4 (wa_ff w + 116) _ 0%nat (C4 (Z_to_bv 64 et)));
        [ exact Cet4 | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity ]. }
    assert (EV41 : edenot (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 et])) (EExt true 0 4 (EVar 41)) = Z_to_bv 64 et).
    { transitivity (Z_to_bv 64 (sx32A et));
        [exact (edenot_sext32 (Eseed R4 (wenv_vals w ++ [Z_to_bv 64 et])) 41 et eq_refl ltac:(lia)) |].
      f_equal. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec et (2 ^ 31)); lia. }
    pm_goX HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 [Z_to_bv 64 et]
          [KWord (SA (EVar WV_FF) 116) 4 (EVar 41)] HK4 200%nat [AT_OPERAND_TYPE_STR] [false] 42%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_5.
    { split_scs. cbn [sc_denot]. rewrite EV41. cbn [edenot].
      rewrite br_ltB by lia. apply Z.ltb_ge. lia. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    fixpc5 VIS5 AT_OPERAND_TYPE_STR.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G23_5 : PropExec.getr R5 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (HR5 23%bv); exact G23_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    assert (E10_5 : PropExec.getr R5 10%bv = Z_to_bv 64 et) by (rewrite (HR5 10%bv); exact EV41).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs m4 mo4 c _ _ _ _ _ _ _ 8016 (-4) (0 + 8) OK X4
                  (env_world_seed H w R4 [Z_to_bv 64 et]) Hlf5
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS4) as DS5.
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_OPERAND_TYPE_STR _ _ _ _ (tla_operand_type_str HTL) et w _ _ _ _ _ c _ _ _ _ _
              msF5 R5 F4 fc4 _ _);
      [ exact OK | exact X5 | exact KR5 | exact VIS5 | exact RF5 | rtf HTx5 | rtf HTx5 | reflexivity | lia | stk5 | reflexivity
      | cbn beta iota; split; [lia|]; split; [exact E10_5 | exact (LINV_relro _ (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5))]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF6 mo6 M6 R6 KR6 VIS6 RF6 X6 KEEP6 MU6 WM6 (tp & tn & CS6 & Er6 & _).
    pose proof CS6 as (CP1 & CN & _).
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G23_6 : PropExec.getr R6 23%bv = Z_to_bv 64 (sx32A (2 ^ j)))
      by (transitivity (PropExec.getr R5 23%bv); [apply KEEP6; cbn; tauto | exact G23_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    pose proof (regs_tbl_restrict w [] _ R6 (rt_keep RT_PM_U5M_D_5) (regs_keep w _ R5 R6 RT_PM_U5M_D_5 HTx5 KEEP6)
                  ltac:(vm_compute; reflexivity)) as HT6.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w s4 LB4 LBs M5 mo5 c _ _ _ _ _ M6 _ 8016 (-4) (0 + 8) OK X5 MU6
                  ltac:(stk5) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS5) as DS6.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word)
          (@nil kentry) 200%nat [ASTRLEN_STUB] (@nil bool) 41%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    fixpc5 VIS7 ASTRLEN_STUB.
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (G23_7 : PropExec.getr R7 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (HR7 23%bv); exact G23_6).
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    assert (E10_7 : PropExec.getr R7 10%bv = Z_to_bv 64 tp) by (rewrite (HR7 10%bv); exact Er6).
    assert (E18_7 : PropExec.getr R7 18%bv = Z_to_bv 64 tp) by (rewrite (HR7 18%bv); exact Er6).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs M6 mo6 c _ _ _ _ _ _ _ 8016 (-4) (0 + 8) OK X6
                  (env_world_seed H w R6 []) Hlf7
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS6) as DS7.
    eapply (pm_leafS H HHm LINV LINV_frame ASTRLEN_STUB _ _ _ _ (strlen_cstr_tleaf (ah_strlen H HHm)) (tp, tn) w _ _ _ _ _ c _ _ _ _ _
              msF7 R7 F4 fc4 _ _);
      [ exact OK | exact X7 | exact KR7 | exact VIS7 | exact RF7 | rtf HTx7 | rtf HTx7 | reflexivity | lia | stk5 | reflexivity
      | cbn beta iota; split; [exact CS6 | exact E10_7]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF8 mo8 M8 R8 KR8 VIS8 RF8 X8 KEEP8 MU8 WM8 SL8. cbn [snd] in SL8.
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (transitivity (PropExec.getr R7 4%bv); [apply KEEP8; cbn; tauto | exact G4_7]).
    assert (G23_8 : PropExec.getr R8 23%bv = Z_to_bv 64 (sx32A (2 ^ j)))
      by (transitivity (PropExec.getr R7 23%bv); [apply KEEP8; cbn; tauto | exact G23_7]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (transitivity (PropExec.getr R7 3%bv); [apply KEEP8; cbn; tauto | exact G3_7]).
    assert (E18_8 : PropExec.getr R8 18%bv = Z_to_bv 64 tp)
      by (transitivity (PropExec.getr R7 18%bv); [apply KEEP8; cbn; tauto | exact E18_7]).
    pose proof (regs_keep w [] R7 R8 RT_PM_U5M_D_7 HTx7 KEEP8) as HT8.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w s4 LB4 LBs M7 mo7 c _ _ _ _ _ M8 _ 8016 (-4) (0 + 8) OK X7 MU8
                  ltac:(stk5) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS7) as DS8.
    pm_go HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word)
          (@nil kentry) 200%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_9.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    fixpc5 VIS9 APUT_CSEQ.
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    assert (G23_9 : PropExec.getr R9 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (HR9 23%bv); exact G23_8).
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    eapply (pm_put_cseq_cstr H HHbp LINV ds_repA DSL HCSEQ w s4 LB4 LBs M9 mo9 c
              [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat HTbAPmU5Md_0 [] TB4 _ msF9 R9 F4 fc4 8016 _ tp tn (-4) (0 + 8) Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ4
      | rtf HTx9 | reflexivity | lia | rtf HTx9 | rtf HTx9 | exact G4_9 | rtf HTx9
      | rewrite (HR9 11%bv); exact E18_8 | rewrite (HR9 12%bv); exact SL8
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | exact CS6
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs M8 mo8 c _ _ _ TB4 _ _ _ 8016 (-4) (0 + 8) OK X8
                  (env_world_seed H w R8 []) Hlf9);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS8]
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 (DS10 & HR10_10) FR10.
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (transitivity (PropExec.getr R9 4%bv); [apply KEEP10; cbn; tauto | exact G4_9]).
    assert (G23_10 : PropExec.getr R10 23%bv = Z_to_bv 64 (sx32A (2 ^ j)))
      by (transitivity (PropExec.getr R9 23%bv); [apply KEEP10; cbn; tauto | exact G23_9]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (transitivity (PropExec.getr R9 3%bv); [apply KEEP10; cbn; tauto | exact G3_9]).
    pose proof (regs_keep w _ R9 R10 RT_PM_U5M_D_9 HTx9 KEEP10) as HT10.
    pm_go HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word)
          (@nil kentry) 200%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_11.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HTx11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M11 := mm) in * end.
    fixpc5 VIS11 APUT_CSEQ.
    assert (G4_11 : PropExec.getr R11 4%bv = wa_tp w) by (rewrite (HR11 4%bv); exact G4_10).
    assert (G23_11 : PropExec.getr R11 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (HR11 23%bv); exact G23_10).
    assert (G3_11 : PropExec.getr R11 3%bv = wa_gp w) by (rewrite (HR11 3%bv); exact G3_10).
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s10 LB10 LBs M11 mo11 c
              [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat HTbAPmU5Md_0 [] TB10 _ msF11 R11 F10 fc10 8016 _ _ _ (-4) (0 + 8 + tn) Q);
      [ exact OK | exact X11 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR11 | exact VIS11 | exact RF11 | exact FZ10
      | rtf HTx11 | reflexivity | lia | rtf HTx11 | rtf HTx11 | exact G4_11 | rtf HTx11 | rtf HTx11 | rtf HTx11
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc5
      | lit_bytes5
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s10 LB10 LBs m10 mo10 c _ _ _ TB10 _ _ _ 8016 (-4) (0 + 8 + tn) OK X10
                  (env_world_seed H w R10 []) Hlf11);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS10]
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF12 mo12 R12 F12 fc12 s12 LB12 m12 TB12 KR12 VIS12 RF12 FZ12 X12 KEEP12 (DS12 & HR10_12) FR12.
    assert (G4_12 : PropExec.getr R12 4%bv = wa_tp w) by (transitivity (PropExec.getr R11 4%bv); [apply KEEP12; cbn; tauto | exact G4_11]).
    assert (G23_12 : PropExec.getr R12 23%bv = Z_to_bv 64 (sx32A (2 ^ j)))
      by (transitivity (PropExec.getr R11 23%bv); [apply KEEP12; cbn; tauto | exact G23_11]).
    assert (G3_12 : PropExec.getr R12 3%bv = wa_gp w) by (transitivity (PropExec.getr R11 3%bv); [apply KEEP12; cbn; tauto | exact G3_11]).
    pose proof (regs_keep w _ R11 R12 RT_PM_U5M_D_11 HTx11 KEEP12) as HT12.
    destruct (ff_junk H LINV w s12 LB12 LBs m12 mo12 c _ _ _ _ _ 176 4 X12 ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(lia)
                ltac:(lia) ltac:(lia)) as (bs & RB).
    change (Z.to_nat 4) with 4%nat in RB.
    assert (L : length bs = 4%nat) by (destruct RB as [[WF _] _]; destruct WF as [C _]; cbn in C; exact C).
    destruct (cb4_as_c4 m12 _ bs L RB) as [Cx Hx]. revert Cx Hx. generalize (bytes_le_to_Z bs). intros x Cx Hx.
    assert (HK12 : know_ok asegs (Eseed R12 (wenv_vals w ++ [Z_to_bv 64 x])) m12 [KWord (SA (EVar WV_FF) 176) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R12 (wenv_vals w ++ [Z_to_bv 64 x])) OK (env_world_seed H w R12 [Z_to_bv 64 x])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m12 (wa_ff w + 176) _ 0%nat (C4 (Z_to_bv 64 x)));
        [ exact Cx | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity ]. }
    pm_goX HHm LINV_frame OK X12 KR12 VIS12 RF12 HT12 [Z_to_bv 64 x]
          [KWord (SA (EVar WV_FF) 176) 4 (EVar 41)] HK12 200%nat [APUT_U32] (@nil bool) 42%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_13.
    { split_scs. }
    intros msF13 mo13 R13 KR13 VIS13 RF13 X13 HTx13 HR13 Hlf13.
    lazymatch type of X13 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M13 := mm) in * end.
    fixpc5 VIS13 APUT_U32.
    assert (G4_13 : PropExec.getr R13 4%bv = wa_tp w) by (rewrite (HR13 4%bv); exact G4_12).
    assert (G23_13 : PropExec.getr R13 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (HR13 23%bv); exact G23_12).
    assert (G3_13 : PropExec.getr R13 3%bv = wa_gp w) by (rewrite (HR13 3%bv); exact G3_12).
    assert (G11_13 : PropExec.getr R13 11%bv = Z_to_bv 64 (sx32 x)).
    { rewrite (HR13 11%bv).
      transitivity (Z_to_bv 64 (sx32A x)); [exact (edenot_sext32 (Eseed R12 (wenv_vals w ++ [Z_to_bv 64 x])) 41 x eq_refl Hx) |].
      f_equal. unfold sx32A, PrsGrammar.sx32, sx32. change (2 ^ 31) with 2147483648. destruct (x <? 2147483648); lia. }
    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_U32 0 (2 ^ 32) sx32 HU32 w s12 LB12 LBs M13 mo13 c
              [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat HTbAPmU5Md_0 [] TB12 _ msF13 R13 F12 fc12 8016 _ x (-4) (0 + 8 + tn + 10) Q);
      [ exact OK | exact X13 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR13 | exact VIS13 | exact RF13 | exact FZ12
      | rtf HTx13 | reflexivity | lia | rtf HTx13 | rtf HTx13 | exact G4_13 | rtf HTx13 | exact G11_13 | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s12 LB12 LBs m12 mo12 c _ _ _ TB12 _ _ _ 8016 (-4) (0 + 8 + tn + 10) OK X12
                  (env_world_seed H w R12 [Z_to_bv 64 x]) Hlf13);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS12]
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF14 mo14 R14 F14 fc14 s14 LB14 m14 TB14 KR14 VIS14 RF14 FZ14 X14 KEEP14 (DS14 & HR10_14) FR14.
    assert (G4_14 : PropExec.getr R14 4%bv = wa_tp w) by (transitivity (PropExec.getr R13 4%bv); [apply KEEP14; cbn; tauto | exact G4_13]).
    assert (G23_14 : PropExec.getr R14 23%bv = Z_to_bv 64 (sx32A (2 ^ j)))
      by (transitivity (PropExec.getr R13 23%bv); [apply KEEP14; cbn; tauto | exact G23_13]).
    assert (G3_14 : PropExec.getr R14 3%bv = wa_gp w) by (transitivity (PropExec.getr R13 3%bv); [apply KEEP14; cbn; tauto | exact G3_13]).
    pose proof (regs_tbl_restrict w [] _ R14 (rt_keep RT_PM_U5M_D_13) (regs_keep w _ R13 R14 RT_PM_U5M_D_13 HTx13 KEEP14)
                  ltac:(vm_compute; reflexivity)) as HT14.
    pm_go HHm LINV_frame OK X14 KR14 VIS14 RF14 HT14 (@nil word)
          (@nil kentry) 200%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_15.
    { split_scs. }
    intros msF15 mo15 R15 KR15 VIS15 RF15 X15 HTx15 HR15 Hlf15.
    lazymatch type of X15 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M15 := mm) in * end.
    fixpc5 VIS15 APUT_CSEQ.
    assert (G4_15 : PropExec.getr R15 4%bv = wa_tp w) by (rewrite (HR15 4%bv); exact G4_14).
    assert (G3_15 : PropExec.getr R15 3%bv = wa_gp w) by (rewrite (HR15 3%bv); exact G3_14).
    assert (G23_15 : PropExec.getr R15 23%bv = Z_to_bv 64 (sx32A (2 ^ j))) by (rewrite (HR15 23%bv); exact G23_14).
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s14 LB14 LBs M15 mo15 c
              [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat HTbAPmU5Md_0 [] TB14 _ msF15 R15 F14 fc14 8016 _ _ _ (-4) (0 + 8 + tn + 10 + 24) Q);
      [ exact OK | exact X15 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR15 | exact VIS15 | exact RF15 | exact FZ14
      | rtf HTx15 | reflexivity | lia | rtf HTx15 | rtf HTx15 | exact G4_15 | rtf HTx15 | rtf HTx15 | rtf HTx15
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | lit_acc5
      | lit_bytes5
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s14 LB14 LBs m14 mo14 c _ _ _ TB14 _ _ _ 8016 (-4) (0 + 8 + tn + 10 + 24) OK X14
                  (env_world_seed H w R14 []) Hlf15);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS14]
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF16 mo16 R16 F16 fc16 s16 LB16 m16 TB16 KR16 VIS16 RF16 FZ16 X16 KEEP16 (DS16 & HR10_16) FR16.
    assert (G4_16 : PropExec.getr R16 4%bv = wa_tp w) by (transitivity (PropExec.getr R15 4%bv); [apply KEEP16; cbn; tauto | exact G4_15]).
    assert (G3_16 : PropExec.getr R16 3%bv = wa_gp w) by (transitivity (PropExec.getr R15 3%bv); [apply KEEP16; cbn; tauto | exact G3_15]).
    assert (G23_16 : PropExec.getr R16 23%bv = Z_to_bv 64 (sx32A (2 ^ j)))
      by (transitivity (PropExec.getr R15 23%bv); [apply KEEP16; cbn; tauto | exact G23_15]).
    pose proof (regs_keep w _ R15 R16 RT_PM_U5M_D_15 HTx15 KEEP16) as HT16.
    pm_go HHm LINV_frame OK X16 KR16 VIS16 RF16 HT16 (@nil word)
          (@nil kentry) 200%nat [APUT_U32] (@nil bool) 41%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_17.
    { split_scs. }
    intros msF17 mo17 R17 KR17 VIS17 RF17 X17 HTx17 HR17 Hlf17.
    lazymatch type of X17 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M17 := mm) in * end.
    fixpc5 VIS17 APUT_U32.
    assert (G4_17 : PropExec.getr R17 4%bv = wa_tp w) by (rewrite (HR17 4%bv); exact G4_16).
    assert (G3_17 : PropExec.getr R17 3%bv = wa_gp w) by (rewrite (HR17 3%bv); exact G3_16).
    pose proof (pow2_range32A j Hj) as PJ.
    assert (G11_17 : PropExec.getr R17 11%bv = Z_to_bv 64 (sx32 (2 ^ j))).
    { rewrite (HR17 11%bv). transitivity (PropExec.getr R16 23%bv); [reflexivity |]. rewrite G23_16.
      f_equal. unfold sx32A, PrsGrammar.sx32, sx32. change (2 ^ 31) with 2147483648. destruct (2 ^ j <? 2147483648); lia. }
    eapply (pm_put_num H HHbp LINV ds_repA DSL APUT_U32 0 (2 ^ 32) sx32 HU32 w s16 LB16 LBs M17 mo17 c
              [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat HTbAPmU5Md_0 [] TB16 _ msF17 R17 F16 fc16 8016 _ (2 ^ j) (-4) (0 + 8 + tn + 10 + 24 + 28) Q);
      [ exact OK | exact X17 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR17 | exact VIS17 | exact RF17 | exact FZ16
      | rtf HTx17 | reflexivity | lia | rtf HTx17 | rtf HTx17 | exact G4_17 | rtf HTx17 | exact G11_17 | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s16 LB16 LBs m16 mo16 c _ _ _ TB16 _ _ _ 8016 (-4) (0 + 8 + tn + 10 + 24 + 28) OK X16
                  (env_world_seed H w R16 []) Hlf17);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS16]
      | unfold DS_MAXLEN; lia | unfold ds_cost, PM_RESERVE; lia | ].
    intros msF18 mo18 R18 F18 fc18 s18 LB18 m18 TB18 KR18 VIS18 RF18 FZ18 X18 KEEP18 (DS18 & HR10_18) FR18.
    assert (G4_18 : PropExec.getr R18 4%bv = wa_tp w) by (transitivity (PropExec.getr R17 4%bv); [apply KEEP18; cbn; tauto | exact G4_17]).
    assert (G3_18 : PropExec.getr R18 3%bv = wa_gp w) by (transitivity (PropExec.getr R17 3%bv); [apply KEEP18; cbn; tauto | exact G3_17]).
    pose proof (regs_keep w _ R17 R18 RT_PM_U5M_D_17 HTx17 KEEP18) as HT18.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS18) as ERR18.
    assert (HK18 : know_ok asegs (Eseed R18 (wenv_vals w ++ [])) m18 [KWord (SA (EVar WV_FF) 8376) 4 (ELit 4294967292)]).
    { pose proof (ev_ff H w (Eseed R18 (wenv_vals w ++ [])) OK (env_world_seed H w R18 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m18 (wa_ff w + 8016 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-4) mod 2 ^ 32))));
        [exact ERR18 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X18 KR18 VIS18 RF18 HT18 (@nil word)
          [KWord (SA (EVar WV_FF) 8376) 4 (ELit 4294967292)] HK18 200%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_19.
    { split_scs. }
    intros msF19 mo19 R19 KR19 VIS19 RF19 X19 HTx19 HR19 Hlf19.
    lazymatch type of X19 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M19 := mm) in * end.
    fixpc5 VIS19 ADS_DTOR.
    assert (G4_19 : PropExec.getr R19 4%bv = wa_tp w) by (rewrite (HR19 4%bv); exact G4_18).
    assert (G3_19 : PropExec.getr R19 3%bv = wa_gp w) by (rewrite (HR19 3%bv); exact G3_18).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s18 LB18 LBs M19 mo19 c
              [3; 4; 33; 34; 39; 40; 41; 43; 45]%nat HTbAPmU5Md_0 [] TB18 _ msF19 R19 F18 fc18 8016 _ (-4) (0 + 8 + tn + 10 + 24 + 28 + 24) Q);
      [ exact OK | exact X19 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR19 | exact VIS19 | exact RF19 | exact FZ18
      | rtf HTx19 | reflexivity | lia | rtf HTx19 | rtf HTx19 | exact G4_19 | rtf HTx19
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s18 LB18 LBs m18 mo18 c _ _ _ _ _ _ _ 8016 (-4) (0 + 8 + tn + 10 + 24 + 28 + 24) OK X18
                  (env_world_seed H w R18 []) Hlf19);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS18]
      | cbn; tauto
      | ].
    intros msF20 mo20 R20 F20 fc20 s20 LB20 m20 TB20 KR20 VIS20 RF20 FZ20 X20 KEEP20 (TB20e & ADDR20) FR20.
    assert (G4_20 : PropExec.getr R20 4%bv = wa_tp w) by (transitivity (PropExec.getr R19 4%bv); [apply KEEP20; cbn; tauto | exact G4_19]).
    assert (G3_20 : PropExec.getr R20 3%bv = wa_gp w) by (transitivity (PropExec.getr R19 3%bv); [apply KEEP20; cbn; tauto | exact G3_19]).
    subst TB20.
    pose proof (regs_keep w _ R19 R20 RT_PM_U5M_D_19 HTx19 KEEP20) as HT20.
    pm_go HHm LINV_frame OK X20 KR20 VIS20 RF20 HT20 (@nil word)
          (@nil kentry) 400%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU5Md_0 (@nil (Z * expr)) RT_PM_U5M_D_21.
    { split_scs. }
    intros msF21 mo21 R21 KR21 VIS21 RF21 X21 HTx21 HR21 Hlf21.
    lazymatch type of X21 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M21 := mm) in * end.
    fixpc5 VIS21 OL_CHECK.
    eapply (K s20 LB20 LBs M21 mo21 c msF21 R21 F20 fc20 HTbAPmU5Md_0 _ 4294967292);
      [ exact X21 | apply tbl_incl; vm_compute; reflexivity | exact Htr | exact BUD | exact Hbsz | exact KR21 | exact VIS21 | exact RF21
      | exact FZ20 | exact (regs_tbl_sub w [] R21 RT_PM_U5M_D_21 RT_CHECK HTx21 ltac:(vm_compute; reflexivity))
      | rewrite (HR21 3%bv); exact G3_20 | rewrite (HR21 4%bv); exact G4_20 | rtf HTx21 | lia ].
  Qed.

End U5Md.
