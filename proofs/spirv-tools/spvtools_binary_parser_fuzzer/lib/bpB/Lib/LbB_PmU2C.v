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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmLeaf LbB_PmLeafW LbB_PmVops LbB_PmU2K LbB_PmOL.

Definition RT_F0A20 : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (19%bv, EVar WV_P);
   (20%bv, SH_FF);
   (21%bv, EAlu ALU_ADD (EVar WV_P) (ELit 248));
   (22%bv, EAlu ALU_ADD (EVar WV_P) (ELit 224));
   (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 224)) (ELit 3)) (ELit SHBASE));
   (24%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   (25%bv, ELit SHBASE);
   (26%bv, EAlu ALU_ADD (EVar WV_P) (ELit 216));
   (27%bv, EAlu ALU_ADD (EVar WV_P) (ELit 48))].
Definition TBL_F0A20 : list (Z * expr) :=
  [(416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 216)) (ELit 3)) (ELit SHBASE));
   (432, EAlu ALU_ADD (EVar WV_P) (ELit 232));
   (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 232)) (ELit 3)) (ELit SHBASE));
   (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 240)) (ELit 3)) (ELit SHBASE));
   (512, EAlu ALU_ADD (EVar WV_P) (ELit 88));
   (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 88)) (ELit 3)) (ELit SHBASE));
   (528, EAlu ALU_ADD (EVar WV_P) (ELit 48));
   (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 48)) (ELit 3)) (ELit SHBASE));
   (544, ELit (2 ^ 61));
   (560, EAlu ALU_ADD (EVar WV_P) (ELit 240));
   (568, EVar WV_FF);
   (576, EVar WV_FF);
   (624, EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   (640, EAlu ALU_ADD (EVar WV_FF) (ELit 9136));
   (648, EVar WV_P);
   (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 72)) (ELit 3)) (ELit SHBASE));
   (664, EAlu ALU_ADD (EVar WV_P) (ELit 72));
   (680, EVar WV_FF)].
Definition RT_F0A44 : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (19%bv, EVar WV_P);
   (20%bv, SH_FF);
   (21%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9050));
   (22%bv, EAlu ALU_ADD (EVar WV_P) (ELit 224));
   (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 224)) (ELit 3)) (ELit SHBASE));
   (24%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   (25%bv, ELit SHBASE);
   (26%bv, EAlu ALU_ADD (EVar WV_P) (ELit 216));
   (27%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9136))].
Definition TBL_F0A44 : list (Z * expr) := TBL_F0A20.
Definition RT_F0A6C : list (reg * expr) := RT_F0A44.
Definition TBL_F0A6C : list (Z * expr) :=
  [(400, EAlu ALU_ADD (EVar WV_FF) (ELit 9616));
   (408, EAlu ALU_ADD (EVar WV_P) (ELit 216));
   (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 216)) (ELit 3)) (ELit SHBASE));
   (432, EAlu ALU_ADD (EVar WV_P) (ELit 232));
   (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 232)) (ELit 3)) (ELit SHBASE));
   (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 240)) (ELit 3)) (ELit SHBASE));
   (512, EAlu ALU_ADD (EVar WV_P) (ELit 88));
   (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 88)) (ELit 3)) (ELit SHBASE));
   (528, EAlu ALU_ADD (EVar WV_P) (ELit 48));
   (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 48)) (ELit 3)) (ELit SHBASE));
   (544, ELit (2 ^ 61));
   (560, EAlu ALU_ADD (EVar WV_P) (ELit 240));
   (568, EVar WV_FF);
   (576, EVar WV_FF);
   (608, EAlu ALU_ADD (EVar WV_FF) (ELit 9050));
   (624, EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   (640, EAlu ALU_ADD (EVar WV_FF) (ELit 9136));
   (648, EVar WV_P);
   (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 72)) (ELit 3)) (ELit SHBASE));
   (664, EAlu ALU_ADD (EVar WV_P) (ELit 72));
   (680, EVar WV_FF)].

Lemma estart_of_ev : forall E e off v, edenot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> estart E (SA e off) = v + off.
Proof. intros E e off v He Hv. unfold estart. cbn [a_base a_off]. rewrite He, u64_of_Z by lia. reflexivity. Qed.

Ltac sreg_rw HR r :=
  rewrite (HR r);
  lazymatch goal with |- context [sr_get ?regs ?r'] =>
    let e := eval vm_compute in (sr_get regs r') in
    let S := fresh "S" in
    assert (S : sr_get regs r' = e) by (vm_compute; reflexivity); rewrite S; clear S
  end.

Section U2C.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Record HS_F0A44 (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
              (msF : machine_state) (R F : bvmap 5 word) (fc : bv 32) (fw : Z) : Prop := MKHS_F0A44 {
    h44_x   : PMXA H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD; OB_INST_WC] TBL_F0A44 [];
    h44_tr  : c_tr c = [];
    h44_bsz : forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40;
    h44_bud : pm_bud (wa_n w) c;
    h44_v1  : t3b (c_v1 c) = 0;
    h44_kr  : as_AKREL H s (mkCfg msF mo);
    h44_vis : as_VIS H s msF = MS R F (Z_to_bv 64 0xf0a44) fc None m (seg_rom asegs);
    h44_rf  : rfull R;
    h44_fz  : frm_zero fc;
    h44_rt  : regs_tbl w R RT_F0A44;
    h44_gp  : PropExec.getr R 3%bv = wa_gp w;
    h44_tp  : PropExec.getr R 4%bv = wa_tp w;
    h44_fwr : 0 <= fw < 2 ^ 32;
    h44_fw  : rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 fw)];
    h44_wc  : rw_cells asegs m (wa_ff w + 9136) [C2 (Z_to_bv 64 (fw / 2 ^ 16))];
    h44_op  : rw_cells asegs m (wa_ff w + 9050) [C2 (Z_to_bv 64 (fw mod 2 ^ 16))]
  }.

  Record HS_F0A6C (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
              (msF : machine_state) (R F : bvmap 5 word) (fc : bv 32) (fw r : Z) : Prop := MKHS_F0A6C {
    h6c_x   : PMXA H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC] TBL_F0A6C [];
    h6c_tr  : c_tr c = [];
    h6c_bsz : forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40;
    h6c_bud : pm_bud (wa_n w) c;
    h6c_v1  : t3b (c_v1 c) = 0;
    h6c_kr  : as_AKREL H s (mkCfg msF mo);
    h6c_vis : as_VIS H s msF = MS R F (Z_to_bv 64 0xf0a6c) fc None m (seg_rom asegs);
    h6c_rf  : rfull R;
    h6c_fz  : frm_zero fc;
    h6c_rt  : regs_tbl w R RT_F0A6C;
    h6c_gp  : PropExec.getr R 3%bv = wa_gp w;
    h6c_tp  : PropExec.getr R 4%bv = wa_tp w;
    h6c_fwr : 0 <= fw < 2 ^ 32;
    h6c_wc0 : fw / 2 ^ 16 <> 0;
    h6c_fw  : rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 fw)];
    h6c_wc  : rw_cells asegs m (wa_ff w + 9136) [C2 (Z_to_bv 64 (fw / 2 ^ 16))];
    h6c_op  : rw_cells asegs m (wa_ff w + 9050) [C2 (Z_to_bv 64 (fw mod 2 ^ 16))];
    h6c_a0  : PropExec.getr R 10%bv = Z_to_bv 64 r;
    h6c_r   : - 2 ^ 31 <= r < 2 ^ 31;
    h6c_fnd : r = 0 <-> exists l, g_op TG (fw mod 2 ^ 16) = Some l;
    h6c_d   : r = 0 -> exists d, rw_cells asegs m (wa_ff w + 9616) [C8 (Z_to_bv 64 d)] /\ idescA d (fw mod 2 ^ 16);
    h6c_d0  : r <> 0 -> rw_cells asegs m (wa_ff w + 9616) [C8 (Z_to_bv 64 0)]
  }.

  Lemma pm_u2c : forall (w : pmwA H) s LB LBs m mo c msF R F fc (fw : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [OB_INST; OB_FIRST_WORD] TBL_F0A20 [] ->
    c_tr c = [] -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud (wa_n w) c -> t3b (c_v1 c) = 0 ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0a20) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_F0A20 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    0 <= fw < 2 ^ 32 -> rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 (sx32A fw))] ->
    (forall msF1 mo1 m1 R1, HS_F0A44 w s LB LBs m1 mo1 c msF1 R1 F fc fw -> ffkeepX w [(9136, 2); (9050, 2)] m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc fw Q OK X0 Htr Hbsz Hbud Hv1 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Hfw CF K.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 (bv_swrap 32 fw)] (@nil kentry) 100%nat [AT_OPCODE_SPLIT]
          (@nil bool) 41%N [OB_INST; OB_FIRST_WORD; OB_INST_WC] (@nil Z) (@nil Z) TBL_F0A20 (@nil (Z * expr)) RT_F0A44.
    { split_scs.
      pose proof (rw_cells_C4_sx32A m _ fw Hfw CF) as CF'.
      pose proof (rw_cells_read asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 fw)] 0 (C4 (Z_to_bv 64 fw)) CF' eq_refl) as RD.
      cbn [csize cbytes] in RD. rewrite Z.add_0_r in RD. unfold wa in RD. rewrite LbB_Conv.rdn_of_ov in RD. unfold le4 in RD.
      pose proof (ev_world_all H w _ (env_world_seed H w R [Z_to_bv 64 (bv_swrap 32 fw)])) as (_ & EV33 & _).
      eapply (sc_read_cell4_sx asegs _ _ _ (wa_ff w + 9120) fw).
      - split; [lia | exact RD].
      - apply adenot_of_estart; [apply estart_of_ev; [exact EV33 | lia] | lia].
      - reflexivity. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    set (E1 := Eseed R (wenv_vals w ++ [Z_to_bv 64 (bv_swrap 32 fw)])) in *.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_F0A44 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    pose proof (ev_world_all H w E1 (env_world_seed H w R _)) as (_ & EV33 & _).
    assert (U33 : bv_unsigned (edenot E1 (EVar WV_FF)) = wa_ff w).
    { change (EVar WV_FF) with (EVar 33). rewrite EV33. apply u64_of_Z. lia. }
    assert (UFS : bv_unsigned (edenot E1 FSHB) = wa_ff w / 8) by (unfold FSHB; apply srl3_val; [exact EV33 | lia]).
    assert (FK1 : ffkeepX w [(9136, 2); (9050, 2)] m M1).
    { pose proof (munch_sym E1 m (s_log SSr) [(EVar WV_FF, 9136, 9138); (FSHB, SHBASE, SHBASE + PM_NSH)] Hlf1
                    ltac:(vm_compute; reflexivity)) as MU.
      cbn [num_wins map] in MU. rewrite U33, UFS in MU.
      apply (ffkeepX_munch w _ _ _ _ MU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
      - right; right. apply Exists_cons_hd. cbn [fst snd]. lia.
      - unfold PM_NSH. destruct Q6 as [D|D]; [left | right; left]; lia. }
    assert (G2_1 : PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w)) by rtf HT1.
    assert (G1_1 : PropExec.getr R1 1%bv = Z_to_bv 64 0xf0a44) by (sreg_rw HR1 (1%bv : reg); reflexivity).
    assert (G10_1 : PropExec.getr R1 10%bv = Z_to_bv 64 (sx32A fw)).
    { sreg_rw HR1 (10%bv : reg). rewrite <- (swrap32_sx32A fw Hfw). reflexivity. }
    assert (G11_1 : PropExec.getr R1 11%bv = Z_to_bv 64 (wa_ff w + 9136)).
    by (sreg_rw HR1 (11%bv : reg); apply ev_add; [exact EV33 | lia | lia]).
    assert (G12_1 : PropExec.getr R1 12%bv = Z_to_bv 64 (wa_ff w + 9050)).
    by (sreg_rw HR1 (12%bv : reg); apply ev_add; [exact EV33 | lia | lia]).
    eapply (pm_opcode_split H HHm LINV LINV_frame (tla_opcode_split HTL) fw 9136 9050 w s LB LBs M1 mo1 c
              [OB_INST; OB_FIRST_WORD; OB_INST_WC] TBL_F0A20 [] [] 0 msF1 R1 F fc 0xf0a44 Q []
              OK X1 KR1 VIS1 RF1 G2_1 G1_1 ltac:(reflexivity) ltac:(lia) G10_1 Hfw G11_1 G12_1
              ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (incl_refl _) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)).
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEPT MU WM QW QO.
    assert (FK2 : ffkeepX w [(9136, 2); (9050, 2)] M1 m2).
    { apply (ffkeepX_munch w _ _ _ _ MU WM). cbn [offs_wins map fst snd].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
      - left. unfold TL_STACK. lia.
      - right; right. apply Exists_cons_hd. cbn [fst snd]. lia.
      - right; right. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd]. lia. }
    pose proof (ffkeepX_trans w _ _ _ m M1 m2 FK1 FK2 (incl_refl _) (incl_refl _)) as FK.
    pose proof (rw_cells_C4_sx32A m _ fw Hfw CF) as CF'.
    assert (CF2 : rw_cells asegs m2 (wa_ff w + 9120) [C4 (Z_to_bv 64 fw)]).
    { apply (FK 9120 _); [lia | cbn; lia | | exact CF'].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd cells_size csize]; lia. }
    pose proof (regs_keep w [] R1 R2 RT_F0A44 HT1 KEPT) as HT2. change (rt_keep RT_F0A44) with RT_F0A44 in HT2.
    apply (K msF2 mo2 m2 R2); [constructor | exact FK].
    - exact X2.
    - exact Htr.
    - exact Hbsz.
    - exact Hbud.
    - exact Hv1.
    - exact KR2.
    - exact VIS2.
    - exact RF2.
    - exact FZ0.
    - exact HT2.
    - rewrite (KEPT 3%bv ltac:(inb)), (HR1 3%bv). exact G3_0.
    - rewrite (KEPT 4%bv ltac:(inb)), (HR1 4%bv). exact G4_0.
    - exact Hfw.
    - exact CF2.
    - exact QW.
    - exact QO.
  Qed.
End U2C.
