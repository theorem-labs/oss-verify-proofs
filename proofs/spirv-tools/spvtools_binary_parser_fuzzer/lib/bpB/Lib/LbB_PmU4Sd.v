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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_PmU4Sa.

Definition RT_PM_U4S_D_1 : list (reg * expr) := [(1%bv, ELit 993956); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (11%bv, EVar 32); (12%bv, ELit 18446744073709551612); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7456)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_3 : list (reg * expr) := [(1%bv, ELit 993976); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (11%bv, ELit 149792); (12%bv, ELit 8); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7456)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_5 : list (reg * expr) := [(1%bv, ELit 993992); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 12); (18%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7456)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_7 : list (reg * expr) := [(1%bv, ELit 994000); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7456)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_9 : list (reg * expr) := [(1%bv, ELit 994020); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_11 : list (reg * expr) := [(1%bv, ELit 994040); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (11%bv, ELit 150432); (12%bv, ELit 10); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_13 : list (reg * expr) := [(1%bv, ELit 994056); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (11%bv, EExt true 0 4 (EVar 41)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_15 : list (reg * expr) := [(1%bv, ELit 994076); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (11%bv, ELit 150464); (12%bv, ELit 130); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_17 : list (reg * expr) := [(1%bv, ELit 994088); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7488)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U4S_D_19 : list (reg * expr) := [(1%bv, ELit 994088); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (23%bv, ELit 18446744073709551612); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Ltac u4s_acc :=
  lazymatch goal with |- forall _, ACONST _ -> accessible _ ?p ?n =>
    let M' := fresh "M'" in let ACM' := fresh "ACM'" in
    intros M' ACM'; eapply (addressable_accessible M' p);
      [ eapply (ACONST_global_addressable M' p _ _ ACM'); [unfold aglobals; repeat (first [left; reflexivity | right]) | lia]
      | lia | lia | unfold AAPP_HI; lia ]
  end.
Ltac u4s_bytes :=
  lazymatch goal with |- exists bs, length bs = Z.to_nat ?n /\ forall _, mem_inv asegs _ -> bytes_at asegs _ ?p bs =>
    let nn := eval vm_compute in (Z.to_nat n) in
    let r := eval vm_compute in (PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 p) nn) in
    lazymatch r with Some ?bs => exists bs; split; [reflexivity |
      let M' := fresh "M'" in let MIM' := fresh "MIM'" in let B' := fresh "B'" in
      intros M' MIM'; edestruct (img_lit M' p nn bs MIM') as [B' _]; [lia | cbn; lia | vm_compute; reflexivity | exact B']] end
  end.
Ltac u4s_pc VIS pc :=
  lazymatch type of VIS with context [s_pc ?ss] => replace (s_pc ss) with pc in VIS by reflexivity end.
Ltac u4s_stk := first [ lia | unfold TL_STACK, AINTRIN_STACK; lia | vm_compute; split; discriminate ].
Section U4Sd.
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
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTbAPmU4Sd_0 : list (Z * expr) := [(32, EAlu ALU_ADD (EVar 33) (ELit 5472)); (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032)); (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008)); (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (104, ELit 65535); (112, EAlu ALU_ADD (EVar 33) (ELit 6000)); (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024)); (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120)); (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (176, ELit 262140); (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512)); (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576)); (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488)); (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (272, EAlu ALU_ADD (EVar 32) (ELit 96)); (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512)); (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928)); (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216)); (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (432, EAlu ALU_ADD (EVar 32) (ELit 232)); (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224)); (456, EAlu ALU_ADD (EVar 33) (ELit 64)); (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88)); (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48)); (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952); (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240)); (568, EVar 33); (576, EVar 33); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880); (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (632, EAlu ALU_ADD (EVar 32) (ELit 264)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32); (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72)); (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32); (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].
  Lemma pm_u4s_d : forall (w : pmwA H) s LB LBs m mo c msF R F fc (r : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 30; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf296c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S1 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 r ->
    r <> 0 /\ - 2 ^ 31 <= r < 2 ^ 31 ->
    rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 12)] ->
    pm_bud (wa_n w) c ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal : Z) (e : Z), PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' -> (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) -> as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w -> PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame DSL HCSEQ HDTOR HU32 HTL LINV_relro HPDIAG0.
    intros w s LB LBs m mo c msF R F fc r Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HR10 HRr HTY BUD K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (p_range H w OK) as [PR1 PR2].
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [])) m [KRange (EVar 10) 1 (2 ^ 64); KWord (SA (EVar WV_P) 40) 1 (ELit 0)]).
    { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - cbn [kentry_ok].
        change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 10)) with (PropExec.getr R 10%bv).
        rewrite HR10, Z_to_bv_unsigned, bv_wrap64_mod. destruct HRr as [Hr0 Hrr].
        pose proof (Z.mod_pos_bound r (2 ^ 64) ltac:(lia)) as MB.
        assert (r mod 2 ^ 64 <> 0) by (intro E0; apply Z.mod_divide in E0; [destruct E0 as [k Hk]; nia | lia]). lia.
      - eapply (kword_of_fld _ m (wa_p w + 40) 1 0);
          [ exact (xa_hunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia
          | exact (estart_p H w _ 40 OK (env_world_seed H w R []))
          | unfold AIMG_TOP in *; lia | unfold AIMG_TOP, PARSER_SIZE in *; lia | reflexivity ]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word)
          [KRange (EVar 10) 1 (2 ^ 64); KWord (SA (EVar WV_P) 40) 1 (ELit 0)] HK1 300%nat [APDIAG] (@nil bool) 41%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    u4s_pc VIS1 APDIAG.
    pose proof (ev_world_all H w (Eseed R (wenv_vals w ++ [])) (env_world_seed H w R [])) as (_ & EV33 & _).
    assert (UFS : bv_unsigned (edenot (Eseed R (wenv_vals w ++ [])) FSHB) = wa_ff w / 8)
      by (unfold FSHB; apply srl3_val; [exact EV33 | lia]).
    assert (FK1 : ffkeepX w [] m M1).
    { pose proof (munch_sym _ m _ [(FSHB, SHBASE, SHBASE + PM_NSH)] Hlf1 ltac:(vm_compute; reflexivity)) as MU1.
      cbn [num_wins map] in MU1. rewrite UFS in MU1.
      apply (ffkeepX_munch w _ _ _ _ MU1 (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_nil]; cbn [fst snd].
      unfold PM_NSH. destruct Q6 as [D|D]; [left | right; left]; lia. }
    assert (TY1 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 12)]).
    { apply (FK1 116 _); [lia | cbn; lia | apply Forall_nil | exact HTY]. }
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    eapply (pm_pdiag H HHbp LINV ds_repA APDIAG false HPDIAG0 w s LB LBs M1 mo1 c
              [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat HTbAPmU4Sd_0 [] 0 msF1 R1 F fc 7488 _ (-4) Q);
      [ exact OK | exact X1 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR1 | exact VIS1 | exact RF1 | exact FZ0
      | rtf HTx1 | reflexivity | lia | rtf HTx1 | rtf HTx1 | exact G4_1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | first [reflexivity | cbn; reflexivity]
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil | ].
    intros msF2 mo2 R2 F2 fc2 s2 LB2 m2 TB2 KR2 VIS2 RF2 FZ2 X2 KEEP2 (TB2e & DS2) FR2. subst TB2.
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (transitivity (PropExec.getr R1 4%bv); [apply KEEP2; cbn; tauto | exact G4_1]).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (transitivity (PropExec.getr R1 3%bv); [apply KEEP2; cbn; tauto | exact G3_1]).
    pose proof (regs_keep w _ R1 R2 RT_PM_U4S_D_1 HTx1 KEEP2) as HT2.
    assert (TY2 : rw_cells asegs m2 (wa_ff w + 116) [C4 (Z_to_bv 64 12)]).
    { apply (FR2 116 _); [lia | cbn; lia | left; cbn; lia | exact TY1]. }
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_3.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    u4s_pc VIS3 APUT_CSEQ.
    assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
    assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
    assert (TY3 : rw_cells asegs M3 (wa_ff w + 116) [C4 (Z_to_bv 64 12)]).
    { pose proof (munch_sym _ m2 _ [] Hlf3 ltac:(vm_compute; reflexivity)) as MU3.
      cbn [num_wins map] in MU3.
      apply (ffkeepX_munch w [] _ m2 M3 MU3 (wmono_mem_denot _ _ _) ltac:(apply Forall_nil) 116 _);
        [lia | cbn; lia | apply Forall_nil | exact TY2]. }
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s2 LB2 LBs m2 mo2 c _ _ _ _ _ _ _ 7488 (-4) 0 OK X2 (env_world_seed H w R2 []) Hlf3
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS2) as DS3.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s2 LB2 LBs M3 mo3 c
              [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat HTbAPmU4Sd_0 [] [] 0 msF3 R3 F2 fc2 7488 _ _ _ (-4) 0 Q);
      [ exact OK | exact X3 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR3 | exact VIS3 | exact RF3 | exact FZ2
      | rtf HTx3 | reflexivity | lia | rtf HTx3 | rtf HTx3 | exact G4_3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | u4s_acc
      | u4s_bytes
      | exact DS3
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF4 mo4 R4 F4 fc4 s4 LB4 m4 TB4 KR4 VIS4 RF4 FZ4 X4 KEEP4 (DS4 & HR10_4) FR4.
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (transitivity (PropExec.getr R3 4%bv); [apply KEEP4; cbn; tauto | exact G4_3]).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (transitivity (PropExec.getr R3 3%bv); [apply KEEP4; cbn; tauto | exact G3_3]).
    pose proof (regs_keep w _ R3 R4 RT_PM_U4S_D_3 HTx3 KEEP4) as HT4.
    assert (TY4 : rw_cells asegs m4 (wa_ff w + 116) [C4 (Z_to_bv 64 12)]).
    { apply (FR4 116 _); [lia | cbn; lia | left; cbn; lia | exact TY3]. }
    assert (HK4 : know_ok asegs (Eseed R4 (wenv_vals w ++ [])) m4 [KWord (SA (EVar WV_FF) 116) 4 (ELit 12)]).
    { pose proof (ev_ff H w (Eseed R4 (wenv_vals w ++ [])) OK (env_world_seed H w R4 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m4 (wa_ff w + 116) _ 0%nat (C4 (Z_to_bv 64 12)));
        [ exact TY4 | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity ]. }
    pm_goX HHm LINV_frame OK X4 KR4 VIS4 RF4 HT4 (@nil word)
          [KWord (SA (EVar WV_FF) 116) 4 (ELit 12)] HK4 60%nat [AT_OPERAND_TYPE_STR] (@nil bool) 41%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_5.
    { split_scs. }
    intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
    lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M5 := mm) in * end.
    u4s_pc VIS5 AT_OPERAND_TYPE_STR.
    assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
    assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs m4 mo4 c _ _ _ _ _ _ _ 7488 (-4) _ OK X4 (env_world_seed H w R4 []) Hlf5
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS4) as DS5.
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_OPERAND_TYPE_STR _ _ _ _ (tla_operand_type_str HTL) 12 w _ _ _ _ _ c _ _ _ _ _ msF5 R5 F4 fc4 _ _);
      [ exact OK | exact X5 | exact KR5 | exact VIS5 | exact RF5 | rtf HTx5 | rtf HTx5 | reflexivity | lia | u4s_stk | reflexivity
      | cbn beta iota; split; [lia|]; split; [rtf HTx5 | exact (LINV_relro _ (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5))]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF6 mo6 M6 R6 KR6 VIS6 RF6 X6 KEEP6 MU6 WM6 (p & n & CS6 & Er6 & Hpn).
    vm_compute in Hpn. apply pair_equal_spec in Hpn as [Ep En].
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (transitivity (PropExec.getr R5 4%bv); [apply KEEP6; cbn; tauto | exact G4_5]).
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (transitivity (PropExec.getr R5 3%bv); [apply KEEP6; cbn; tauto | exact G3_5]).
    pose proof (regs_keep w [] R5 R6 RT_PM_U4S_D_5 HTx5 KEEP6) as HT6.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w s4 LB4 LBs M5 mo5 c _ _ _ _ _ M6 _ 7488 (-4) _ OK X5 MU6
                  ltac:(u4s_stk) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS5) as DS6.
    pm_go HHm LINV_frame OK X6 KR6 VIS6 RF6 HT6 (@nil word) (@nil kentry) 100%nat [ASTRLEN_STUB] (@nil bool) 41%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_7.
    { split_scs. }
    intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
    lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M7 := mm) in * end.
    u4s_pc VIS7 ASTRLEN_STUB.
    assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
    assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
    assert (E10_7 : PropExec.getr R7 10%bv = Z_to_bv 64 p) by (rewrite (HR7 10%bv); exact Er6).
    assert (E18_7 : PropExec.getr R7 18%bv = Z_to_bv 64 p) by (rewrite (HR7 18%bv); exact Er6).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs M6 mo6 c _ _ _ _ _ _ _ 7488 (-4) _ OK X6 (env_world_seed H w R6 []) Hlf7
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS6) as DS7.
    eapply (pm_leafS H HHm LINV LINV_frame ASTRLEN_STUB _ _ _ _ (strlen_cstr_tleaf (ah_strlen H HHm)) (p, n) w _ _ _ _ _ c _ _ _ _ _ msF7 R7 F4 fc4 _ _);
      [ exact OK | exact X7 | exact KR7 | exact VIS7 | exact RF7 | rtf HTx7 | rtf HTx7 | reflexivity | lia | u4s_stk | reflexivity
      | cbn beta iota; split; [exact CS6 | exact E10_7]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF8 mo8 M8 R8 KR8 VIS8 RF8 X8 KEEP8 MU8 WM8 SL8. cbn [snd] in SL8.
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (transitivity (PropExec.getr R7 4%bv); [apply KEEP8; cbn; tauto | exact G4_7]).
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (transitivity (PropExec.getr R7 3%bv); [apply KEEP8; cbn; tauto | exact G3_7]).
    assert (E18_8 : PropExec.getr R8 18%bv = Z_to_bv 64 p) by (transitivity (PropExec.getr R7 18%bv); [apply KEEP8; cbn; tauto | exact E18_7]).
    pose proof (regs_keep w [] R7 R8 RT_PM_U4S_D_7 HTx7 KEEP8) as HT8.
    pose proof (ds_rep_leaf H HHbp LINV ds_repA DSL w s4 LB4 LBs M7 mo7 c _ _ _ _ _ M8 _ 7488 (-4) _ OK X7 MU8
                  ltac:(u4s_stk) ltac:(lia) ltac:(unfold DS_SIZE; lia) DS7) as DS8.
    subst p n.
    pm_go HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_9.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    u4s_pc VIS9 APUT_CSEQ.
    assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).
    assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s4 LB4 LBs M8 mo8 c _ _ _ _ _ _ _ 7488 (-4) _ OK X8 (env_world_seed H w R8 []) Hlf9
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS8) as DS9.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s4 LB4 LBs M9 mo9 c
              [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat HTbAPmU4Sd_0 [] _ _ msF9 R9 F4 fc4 7488 _ _ _ (-4) _ Q);
      [ exact OK | exact X9 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR9 | exact VIS9 | exact RF9 | exact FZ4
      | rtf HTx9 | reflexivity | lia | rtf HTx9 | rtf HTx9 | exact G4_9 | rtf HTx9
      | rewrite (HR9 11%bv); exact E18_8 | rewrite (HR9 12%bv); exact SL8
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | u4s_acc
      | u4s_bytes
      | exact DS9
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF10 mo10 R10 F10 fc10 s10 LB10 m10 TB10 KR10 VIS10 RF10 FZ10 X10 KEEP10 (DS10 & HR10_10) FR10.
    assert (G4_10 : PropExec.getr R10 4%bv = wa_tp w) by (transitivity (PropExec.getr R9 4%bv); [apply KEEP10; cbn; tauto | exact G4_9]).
    assert (G3_10 : PropExec.getr R10 3%bv = wa_gp w) by (transitivity (PropExec.getr R9 3%bv); [apply KEEP10; cbn; tauto | exact G3_9]).
    pose proof (regs_keep w _ R9 R10 RT_PM_U4S_D_9 HTx9 KEEP10) as HT10.
    pm_go HHm LINV_frame OK X10 KR10 VIS10 RF10 HT10 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_11.
    { split_scs. }
    intros msF11 mo11 R11 KR11 VIS11 RF11 X11 HTx11 HR11 Hlf11.
    lazymatch type of X11 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M11 := mm) in * end.
    u4s_pc VIS11 APUT_CSEQ.
    assert (G4_11 : PropExec.getr R11 4%bv = wa_tp w) by (rewrite (HR11 4%bv); exact G4_10).
    assert (G3_11 : PropExec.getr R11 3%bv = wa_gp w) by (rewrite (HR11 3%bv); exact G3_10).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s10 LB10 LBs m10 mo10 c _ _ _ _ _ _ _ 7488 (-4) _ OK X10 (env_world_seed H w R10 []) Hlf11
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS10) as DS11.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s10 LB10 LBs M11 mo11 c
              [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat HTbAPmU4Sd_0 [] _ _ msF11 R11 F10 fc10 7488 _ _ _ (-4) _ Q);
      [ exact OK | exact X11 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR11 | exact VIS11 | exact RF11 | exact FZ10
      | rtf HTx11 | reflexivity | lia | rtf HTx11 | rtf HTx11 | exact G4_11 | rtf HTx11 | rtf HTx11 | rtf HTx11
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | u4s_acc
      | u4s_bytes
      | exact DS11
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF12 mo12 R12 F12 fc12 s12 LB12 m12 TB12 KR12 VIS12 RF12 FZ12 X12 KEEP12 (DS12 & HR10_12) FR12.
    assert (G4_12 : PropExec.getr R12 4%bv = wa_tp w) by (transitivity (PropExec.getr R11 4%bv); [apply KEEP12; cbn; tauto | exact G4_11]).
    assert (G3_12 : PropExec.getr R12 3%bv = wa_gp w) by (transitivity (PropExec.getr R11 3%bv); [apply KEEP12; cbn; tauto | exact G3_11]).
    pose proof (regs_keep w _ R11 R12 RT_PM_U4S_D_11 HTx11 KEEP12) as HT12.
    destruct (ff_junk H LINV w _ _ _ _ _ _ _ _ _ _ _ 176 4 X12 ltac:(unfold AFS_HDR in Q4; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (bj & CBj).
    assert (LBj : length bj = 4%nat) by (destruct CBj as [[Hwf _] _]; cbn in Hwf; tauto).
    destruct (cb4_as_c4 m12 _ bj LBj CBj) as (Cj & Hxj).
    set (xj := bytes_le_to_Z bj) in *.
    assert (HK12 : know_ok asegs (Eseed R12 (wenv_vals w ++ [Z_to_bv 64 xj])) m12 [KWord (SA (EVar WV_FF) 176) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R12 (wenv_vals w ++ [Z_to_bv 64 xj])) OK (env_world_seed H w R12 [Z_to_bv 64 xj])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m12 (wa_ff w + 176) _ 0%nat (C4 (Z_to_bv 64 xj)));
        [ exact Cj | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity ]. }
    pm_goX HHm LINV_frame OK X12 KR12 VIS12 RF12 HT12 [Z_to_bv 64 xj]
          [KWord (SA (EVar WV_FF) 176) 4 (EVar 41)] HK12 100%nat [APUT_U32] (@nil bool) 42%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_13.
    { split_scs. }
    intros msF13 mo13 R13 KR13 VIS13 RF13 X13 HTx13 HR13 Hlf13.
    lazymatch type of X13 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M13 := mm) in * end.
    u4s_pc VIS13 APUT_U32.
    assert (G4_13 : PropExec.getr R13 4%bv = wa_tp w) by (rewrite (HR13 4%bv); exact G4_12).
    assert (G3_13 : PropExec.getr R13 3%bv = wa_gp w) by (rewrite (HR13 3%bv); exact G3_12).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s12 LB12 LBs m12 mo12 c _ _ _ _ _ _ _ 7488 (-4) _ OK X12
                  (env_world_seed H w R12 [Z_to_bv 64 xj]) Hlf13
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS12) as DS13.
    eapply (pm_put_num H HHbp LINV ds_repA DSL _ _ _ _ HU32 w s12 LB12 LBs M13 mo13 c
              [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat HTbAPmU4Sd_0 [] _ _ msF13 R13 F12 fc12 7488 _ xj (-4) _ Q);
      [ exact OK | exact X13 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR13 | exact VIS13 | exact RF13 | exact FZ12
      | rtf HTx13 | reflexivity | lia | rtf HTx13 | rtf HTx13 | exact G4_13 | rtf HTx13
      | rewrite (HR13 11%bv); transitivity (Z_to_bv 64 (sx32A xj));
          [ exact (edenot_sext32 (Eseed R12 (wenv_vals w ++ [Z_to_bv 64 xj])) 41 xj eq_refl Hxj)
          | f_equal; unfold sx32A, PrsGrammar.sx32, LbB_DiagStmt.sx32; destruct (xj <? 2 ^ 31); cbn beta iota; lia ] | lia
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | exact DS13
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF14 mo14 R14 F14 fc14 s14 LB14 m14 TB14 KR14 VIS14 RF14 FZ14 X14 KEEP14 (DS14 & HR10_14) FR14.
    assert (G4_14 : PropExec.getr R14 4%bv = wa_tp w) by (transitivity (PropExec.getr R13 4%bv); [apply KEEP14; cbn; tauto | exact G4_13]).
    assert (G3_14 : PropExec.getr R14 3%bv = wa_gp w) by (transitivity (PropExec.getr R13 3%bv); [apply KEEP14; cbn; tauto | exact G3_13]).
    pose proof (regs_tbl_restrict w [] _ R14 (rt_keep RT_PM_U4S_D_13) (regs_keep w _ R13 R14 RT_PM_U4S_D_13 HTx13 KEEP14) ltac:(vm_compute; reflexivity)) as HT14.
    pm_go HHm LINV_frame OK X14 KR14 VIS14 RF14 HT14 (@nil word) (@nil kentry) 100%nat [APUT_CSEQ] (@nil bool) 41%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_15.
    { split_scs. }
    intros msF15 mo15 R15 KR15 VIS15 RF15 X15 HTx15 HR15 Hlf15.
    lazymatch type of X15 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M15 := mm) in * end.
    u4s_pc VIS15 APUT_CSEQ.
    assert (G4_15 : PropExec.getr R15 4%bv = wa_tp w) by (rewrite (HR15 4%bv); exact G4_14).
    assert (G3_15 : PropExec.getr R15 3%bv = wa_gp w) by (rewrite (HR15 3%bv); exact G3_14).
    pose proof (ds_rep_run H HHbp LINV ds_repA DSL w s14 LB14 LBs m14 mo14 c _ _ _ _ _ _ _ 7488 (-4) _ OK X14 (env_world_seed H w R14 []) Hlf15
                  ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold DS_SIZE; lia) eq_refl DS14) as DS15.
    eapply (pm_put_cseq_img H HHbp LINV ds_repA DSL HCSEQ w s14 LB14 LBs M15 mo15 c
              [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat HTbAPmU4Sd_0 [] _ _ msF15 R15 F14 fc14 7488 _ _ _ (-4) _ Q);
      [ exact OK | exact X15 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR15 | exact VIS15 | exact RF15 | exact FZ14
      | rtf HTx15 | reflexivity | lia | rtf HTx15 | rtf HTx15 | exact G4_15 | rtf HTx15 | rtf HTx15 | rtf HTx15
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | lia | unfold AIMG_LO; lia | unfold AIMG_TOP; lia
      | u4s_acc
      | u4s_bytes
      | exact DS15
      | unfold DS_MAXLEN; lia | vm_compute; congruence | ].
    intros msF16 mo16 R16 F16 fc16 s16 LB16 m16 TB16 KR16 VIS16 RF16 FZ16 X16 KEEP16 (DS16 & HR10_16) FR16.
    assert (G4_16 : PropExec.getr R16 4%bv = wa_tp w) by (transitivity (PropExec.getr R15 4%bv); [apply KEEP16; cbn; tauto | exact G4_15]).
    assert (G3_16 : PropExec.getr R16 3%bv = wa_gp w) by (transitivity (PropExec.getr R15 3%bv); [apply KEEP16; cbn; tauto | exact G3_15]).
    pose proof (regs_keep w _ R15 R16 RT_PM_U4S_D_15 HTx15 KEEP16) as HT16.
    pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS16) as ERR16.
    assert (HK16 : know_ok asegs (Eseed R16 (wenv_vals w ++ [])) m16 [KWord (SA (EVar WV_FF) 7848) 4 (ELit 4294967292)]).
    { pose proof (ev_ff H w (Eseed R16 (wenv_vals w ++ [])) OK (env_world_seed H w R16 [])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m16 (wa_ff w + 7488 + DS_ERR_OFF) _ 0%nat (C4 (Z_to_bv 64 ((-4) mod 2 ^ 32))));
        [exact ERR16 | reflexivity | reflexivity | lia | unfold estart, DS_ERR_OFF; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | unfold DS_ERR_OFF; cbn [Z.of_nat]; lia | reflexivity]. }
    pm_goX HHm LINV_frame OK X16 KR16 VIS16 RF16 HT16 (@nil word)
          [KWord (SA (EVar WV_FF) 7848) 4 (ELit 4294967292)] HK16 100%nat [ADS_DTOR] (@nil bool) 41%N
          [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_17.
    { split_scs. }
    intros msF17 mo17 R17 KR17 VIS17 RF17 X17 HTx17 HR17 Hlf17.
    lazymatch type of X17 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M17 := mm) in * end.
    u4s_pc VIS17 ADS_DTOR.
    assert (G4_17 : PropExec.getr R17 4%bv = wa_tp w) by (rewrite (HR17 4%bv); exact G4_16).
    assert (G3_17 : PropExec.getr R17 3%bv = wa_gp w) by (rewrite (HR17 3%bv); exact G3_16).
    eapply (pm_ds_dtor H HHbp LINV ds_repA HDTOR w s16 LB16 LBs M17 mo17 c
              [3; 4; 30; 31; 39; 40; 41; 43; 45]%nat HTbAPmU4Sd_0 [] TB16 _ msF17 R17 F16 fc16 7488 _ (-4) _ Q);
      [ exact OK | exact X17 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR17 | exact VIS17 | exact RF17 | exact FZ16
      | rtf HTx17 | reflexivity | lia | rtf HTx17 | rtf HTx17 | exact G4_17 | rtf HTx17
      | vm_compute; reflexivity | lia | unfold DS_SIZE; lia | apply Forall_nil
      | eapply (ds_rep_run H HHbp LINV ds_repA DSL w s16 LB16 LBs m16 mo16 c _ _ _ _ _ _ _ 7488 (-4) _ OK X16
                  (env_world_seed H w R16 []) Hlf17);
          [vm_compute; reflexivity | lia | unfold DS_SIZE; lia | reflexivity | exact DS16]
      | cbn; tauto
      | ].
    intros msF18 mo18 R18 F18 fc18 s18 LB18 m18 TB18 KR18 VIS18 RF18 FZ18 X18 KEEP18 (TB18e & ADDR18) FR18. subst TB18.
    assert (G4_18 : PropExec.getr R18 4%bv = wa_tp w) by (transitivity (PropExec.getr R17 4%bv); [apply KEEP18; cbn; tauto | exact G4_17]).
    assert (G3_18 : PropExec.getr R18 3%bv = wa_gp w) by (transitivity (PropExec.getr R17 3%bv); [apply KEEP18; cbn; tauto | exact G3_17]).
    pose proof (regs_keep w _ R17 R18 RT_PM_U4S_D_17 HTx17 KEEP18) as HT18.
    pm_go HHm LINV_frame OK X18 KR18 VIS18 RF18 HT18 (@nil word) (@nil kentry) 400%nat [OL_CHECK] (@nil bool) 41%N
          [3; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU4Sd_0 (@nil (Z * expr)) RT_PM_U4S_D_19.
    { split_scs. }
    intros msF19 mo19 R19 KR19 VIS19 RF19 X19 HTx19 HR19 Hlf19.
    lazymatch type of X19 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M19 := mm) in * end.
    u4s_pc VIS19 OL_CHECK.
    eapply (K s18 LB18 LBs M19 mo19 c msF19 R19 F18 fc18 HTbAPmU4Sd_0 _ (2 ^ 32 - 4));
      [ exact X19 | apply tbl_incl; vm_compute; reflexivity | exact Htr | exact BUD | exact Hbsz | exact KR19 | exact VIS19 | exact RF19
      | exact FZ18 | exact (regs_tbl_sub w [] R19 RT_PM_U4S_D_19 RT_CHECK HTx19 ltac:(vm_compute; reflexivity))
      | rewrite (HR19 3%bv); exact G3_18 | rewrite (HR19 4%bv); exact G4_18 | rtf HTx19 | lia ].
  Qed.

End U4Sd.
