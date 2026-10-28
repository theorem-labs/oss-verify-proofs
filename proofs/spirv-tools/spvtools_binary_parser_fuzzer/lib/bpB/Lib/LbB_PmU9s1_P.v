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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_PmHex LbB_DStat LbB_TablStmt LbB_PmLeaf LbB_PmLH LbB_PmWords LbB_PmCells LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_PmOL LbB_PmU3XK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord.

Ltac u9_sc A w E33 EFu EB EA RD0 F H E HE :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCReadBase (SA (EVar 32) _) 4 true _) => sc_fld4 H w E HE F
  | |- sc_denot _ _ _ (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL _ _) _) 4) 4 true _) =>
      eapply sc_rd_w4s; [rewrite (adenot_of_estart _ _ A); [reflexivity | unfold estart; cbn [a_base a_off]; rewrite EB, u64_of_Z by lia; lia | lia] | exact RD0 | reflexivity]
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL _ _) _) 4) (ELit ?l)) =>
      eapply (sc_flat_lit asegs _ _ _ _ A l); [unfold estart; cbn [a_base a_off]; rewrite EB, u64_of_Z by lia; lia | apply elit_u; lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL _ _) _) (ELit 4)) (ELit 3)) _) (ELit ?l)) =>
      eapply (sc_flat_lit asegs _ _ _ _ (A / 8 + SHBASE) l); [apply (estart_sh _ _ A EA); lia | apply elit_u; lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_ADD (EMd M_MUL _ _) _) 4) (ELit ?l1) (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) ?o2) (ELit ?l2)) =>
      eapply (sc_disj_lit asegs _ _ _ _ _ _ A l1 (wa_ff w / 8 + o2) l2);
      [unfold estart; cbn [a_base a_off]; rewrite EB, u64_of_Z by lia; lia | apply elit_u; lia
      | unfold estart; cbn [a_base a_off]; rewrite (srl3_val _ (EVar 33) (wa_ff w) E33) by lia; lia | apply elit_u; lia
      | lia | lia | lia | lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_ADD (EMd M_MUL _ _) _) 4) (ELit ?l1) (SA (EVar 33) ?o2) (ELit ?l2)) =>
      eapply (sc_disj_lit asegs _ _ _ _ _ _ A l1 (wa_ff w + o2) l2);
      [unfold estart; cbn [a_base a_off]; rewrite EB, u64_of_Z by lia; lia | apply elit_u; lia
      | unfold estart; cbn [a_base a_off]; rewrite EFu; lia | apply elit_u; lia
      | lia | lia | lia | lia | lia | lia | lia]
  | |- _ => idtac
  end.

Lemma ev_idx4p4 : forall E (r n : N) (x y : Z), edenot E (EVar r) = Z_to_bv 64 x -> edenot E (EVar n) = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> y + 4 * x + 4 < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar r)) (EVar n)) (ELit 4)) = Z_to_bv 64 (y + 4 * (x + 1)).
Proof.
  intros E r n x y Hx Hy H0 H1 H2. cbn [edenot]. change (ev E r) with (edenot E (EVar r)). change (ev E n) with (edenot E (EVar n)).
  rewrite Hx, Hy. rewrite w_mul_litA. cbn [alu64 alu]. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (4 * x) (2 ^ 64)) by lia. rewrite (Z.mod_small y (2 ^ 64)) by lia.
  rewrite (Z.mod_small (4 * x + y) (2 ^ 64)) by lia. rewrite (Z.mod_small 4 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (4 * x + y + 4) (2 ^ 64)) by lia. rewrite (Z.mod_small (y + 4 * (x + 1)) (2 ^ 64)) by lia. lia.
Qed.

Lemma ev_idx4 : forall E (r n : N) (x y : Z), edenot E (EVar r) = Z_to_bv 64 x -> edenot E (EVar n) = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> y + 4 * x < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar r)) (EVar n)) = Z_to_bv 64 (y + 4 * x).
Proof.
  intros E r n x y Hx Hy H0 H1 H2. cbn [edenot]. change (ev E r) with (edenot E (EVar r)). change (ev E n) with (edenot E (EVar n)).
  rewrite Hx, Hy. rewrite w_mul_litA. cbn [alu64 alu]. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (4 * x) (2 ^ 64)) by lia. rewrite (Z.mod_small y (2 ^ 64)) by lia.
  rewrite (Z.mod_small (4 * x + y) (2 ^ 64)) by lia. rewrite (Z.mod_small (y + 4 * x) (2 ^ 64)) by lia. lia.
Qed.

Lemma u9_ck_null : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 < a < 2 ^ 64 ->
  sc_denot SEGS M E (SCBr false BC_EQ e (ELit 0)).
Proof.
  intros SEGS M E e a He Ha. cbn [sc_denot]. rewrite He. cbn [edenot]. rewrite br_eq by lia.
  apply Z.eqb_neq. lia.
Qed.

Lemma u9_ck_wrap : forall (SEGS : list Segment) M E e1 e2 a k, edenot E e1 = Z_to_bv 64 (a + k) -> edenot E e2 = Z_to_bv 64 a ->
  0 <= a -> 0 <= k -> a + k < 2 ^ 64 -> sc_denot SEGS M E (SCBr false BC_LTU e1 e2).
Proof.
  intros SEGS M E e1 e2 a k H1 H2 Ha Hk Hak. cbn [sc_denot]. rewrite H1, H2, br_ltu by lia.
  apply Z.ltb_ge. lia.
Qed.

Lemma u9_ck_pos : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 < a < 2 ^ 64 ->
  sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_SLTU (ELit 0) e) (ELit 0)).
Proof.
  intros SEGS M E e a He Ha. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite w_sltu by lia.
  replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma u9_ck_part : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 8 = 0 ->
  sc_denot SEGS M E (SCBr true BC_LT (EAlu ALU_ADD (EAlu ALU_AND e (ELit 7)) (ELit 3)) (ELit 4)).
Proof.
  intros SEGS M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite w_and by lia.
  replace (Z.land a 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
  vm_compute. reflexivity.
Qed.

Definition RT_PM_U9_S1_P_1 : list (reg * expr) := [(1%bv, ELit 991668); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EVar 42); (11%bv, EVar 41); (12%bv, ELit 4); (14%bv, EVar 36); (15%bv, ELit 2305843009213693952); (16%bv, ELit 0); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section U9s1.
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

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

Definition WA4 : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 25)) (EVar 36)) (ELit 4).
Definition WSH : saddr := SA (EAlu ALU_SRL WA4 (ELit 3)) SHBASE.
Definition WAD : saddr := SA (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 25)) (EVar 36)) 4.
Definition U9_WK : list kentry :=
  [KWord WSH 1 (ELit 4);
   KDisj WSH (ELit 1) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO));
   KDisj WSH (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH);
   KDisj WSH (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384)].
Definition U9_WD : list kentry :=
  [KDisj WAD (ELit 4) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO));
   KDisj WAD (ELit 4) (SA FSHB SHBASE) (ELit PM_NSH);
   KDisj WAD (ELit 4) (SA (EVar WV_FF) 0) (ELit 16384)].
Definition U9_A : list kentry := [KRange (EVar 22) 251 251; KRange (EVar 25) 0 (2 ^ 24); KRange (EVar 41) 0 1; KAlign (EVar 36) 16;
  KWord (SA (EVar WV_P) 88) 4 (EVar 41)].
  Lemma pm_u9_s1_P : forall (w : pmwA H) s LB LBs m mo c msF R F fc (io : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2190) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 22%bv = Z_to_bv 64 251 ->
    PropExec.getr R 25%bv = Z_to_bv 64 io ->
    0 <= io ->
    io + 1 < wa_n w ->
    wa_words w <> 0 ->
    c_endian c = 0 \/ c_endian c = 1 ->
    4 * (io + 1) = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4 ->
    (forall msF1 mo1 m1 R1 (x0 : Z), as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_FIXWORD) fc None m1 (seg_rom asegs) -> rfull R1 ->
      PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 20; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ARM -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1
      4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf21b4 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> 0 <= x0 < 2 ^ 32 -> PropExec.getr R1 10%bv =
      Z_to_bv 64 (sx32A x0) -> PropExec.getr R1 11%bv = Z_to_bv 64 (c_endian c) -> rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 9)] -> ffkeepX w [(116, 4)] m m1
      -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame.
    intros w s LB LBs m mo c msF R F fc io Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 R22 R25 Hio0 Hio1 HW0 HEND HGR K.
    destruct HGR as [HGR1 HGR2].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X0) as (_ & _ & PAW). specialize (PAW HW0).
    assert (HinLB : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)))). apply in_app_iff. left. exact Hin. }
    pose proof (ah_blocks H HHm _ _ _ _ (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) HinLB) as (_ & _ & _ & _ & _ & _ & RAPP).
    cbn [blk_addr blk_size fst snd] in RAPP.
    pose proof (aapp_bounds _ _ RAPP ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5).
    pose proof (aapp_disjoint_sh (wa_words w) k (wa_ff w) 16384 RAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DSH.
    rewrite Q13 in DSH. change (nsh 16384) with 2048 in DSH.
    destruct (words_rd4 H LINV w _ _ _ _ _ _ _ _ _ _ _ (io + 1) OK X0 HW0 ltac:(lia)) as (bs & RD0 & BL).
    pose proof (bytes_le_to_Z_range4 bs BL) as BR.
    set (A := wa_words w + 4 * (io + 1)) in *.
    assert (HA : A = wa_words w + 4 * (io + 1)) by reflexivity.
    set (XS := [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs))]).
    pose proof (env_world_seed H w R XS) as HE.
    pose proof (ev_ff H w _ OK HE) as EFw. pose proof EFw as EFu. change (EVar WV_FF) with (EVar 33%N) in EFu.
    destruct (ev_world_all H w _ HE) as (E32 & E33 & _ & E35 & E36 & _).
    assert (U35 : bv_unsigned (edenot (Eseed R (wenv_vals w ++ XS)) (EVar WV_S1)) = wa_s1 w).
    { change (EVar WV_S1) with (EVar 35). rewrite E35. apply u64_of_Z. lia. }
    assert (UFS : bv_unsigned (edenot (Eseed R (wenv_vals w ++ XS)) FSHB) = wa_ff w / 8)
      by (unfold FSHB; change (EVar WV_FF) with (EVar 33); apply srl3_val; [exact E33 | lia]).
    assert (E41 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 41) = Z_to_bv 64 (c_endian c)) by reflexivity.
    assert (E42 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 42) = Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs))) by reflexivity.
    assert (E22 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 22) = Z_to_bv 64 251) by (cbn [edenot]; rewrite Eseed_reg by lia; exact R22).
    assert (E25 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 25) = Z_to_bv 64 io) by (cbn [edenot]; rewrite Eseed_reg by lia; exact R25).
    assert (EB : edenot (Eseed R (wenv_vals w ++ XS)) (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 25)) (EVar 36)) = Z_to_bv 64 (wa_words w + 4 * io))
      by (apply ev_idx4; [exact E25 | exact E36 | lia | lia | lia]).
    assert (EA : edenot (Eseed R (wenv_vals w ++ XS)) WA4 = Z_to_bv 64 A)
      by (rewrite HA; unfold WA4; apply ev_idx4p4; [exact E25 | exact E36 | lia | lia | lia]).
    assert (HK : know_ok asegs (Eseed R (wenv_vals w ++ XS)) m (U9_A ++ U9_WD ++ U9_WK)).
    { unfold U9_A, U9_WD, U9_WK, WSH, WAD. cbn [app].
      apply Forall_cons. { apply krange_intro. rewrite E22, u64_of_Z by lia. lia. }
      apply Forall_cons. { apply krange_intro. rewrite E25, u64_of_Z by lia. lia. }
      apply Forall_cons. { apply krange_intro. rewrite E41, u64_of_Z by lia. lia. }
      apply Forall_cons. { apply kalign_intro; [lia|]. rewrite E36, u64_of_Z by lia. exact W16. }
      apply Forall_cons. { eapply pmk_scal_endian with (1 := OK) (2 := X0) (3 := HE). exact E41. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite EB, U35, !elit_u, !u64_of_Z by (unfold PM_RF_LO; lia).
        unfold PM_RF_LO. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite EB, UFS, !elit_u, !u64_of_Z by (unfold PM_NSH; lia).
        unfold PM_NSH. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite EB, EFw, !elit_u, !u64_of_Z by lia. lia. }
      apply Forall_cons.
      { first [eapply pmk_sh_wordsE_part with (1 := HHm) (2 := OK) (3 := X0) (4 := HW0) | eapply pmk_sh_wordsE_part with (1 := OK) (2 := X0) (3 := HW0)];
          [exact EA | exact HGR1 | exact HGR2]. }
      apply Forall_cons.
      { first [eapply pmk_sh_s1disj with (1 := HHm) (2 := OK) (3 := X0) (4 := HE) | eapply pmk_sh_s1disj with (1 := OK) (2 := X0) (3 := HE)];
          [exact EA | lia | lia]. }
      apply Forall_cons.
      { first [eapply pmk_sh_fshdisj with (1 := HHm) (2 := OK) (3 := X0) (4 := HE) | eapply pmk_sh_fshdisj with (1 := OK) (2 := X0) (3 := HE)];
          [exact EA | lia | lia | lia]. }
      apply Forall_cons.
      { first [eapply pmk_sh_ffdisj with (1 := HHm) (2 := OK) (3 := X0) (4 := HE) | eapply pmk_sh_ffdisj with (1 := OK) (2 := X0) (3 := HE)];
          [exact EA | lia | lia]. }
      apply Forall_nil. }
    assert (AM8 : A mod 8 = 0).
    { rewrite HA, HGR1. pose proof (Z_div_exact_full_2 (wa_words w) 16 ltac:(lia) W16) as WQ.
      rewrite WQ. replace (16 * (wa_words w / 16) + 8 * (4 * wa_n w / 8)) with ((2 * (wa_words w / 16) + 4 * wa_n w / 8) * 8) by ring.
      apply Z.mod_mul. lia. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 XS (U9_A ++ U9_WD ++ U9_WK) HK 100%nat [AT_FIXWORD] [false; false; false; true] 42%N
      [3; 4; 20; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U9_S1_P_1.
    { split_scs.
      all: first
        [ eapply sc_rd_w4s;
            [ rewrite (adenot_of_estart _ _ A); [reflexivity | unfold estart; cbn [a_base a_off]; rewrite EB, u64_of_Z by lia; lia | lia]
            | exact RD0 | exact E42 ]
        | eapply u9_ck_null; [exact E36 | lia]
        | eapply (u9_ck_wrap _ _ _ _ _ (wa_words w) (4 * (io + 1))); [exact EA | exact E36 | lia | lia | lia]
        | eapply u9_ck_pos; [exact E36 | lia]
        | eapply u9_ck_part; [exact EA | lia | exact AM8] ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    lazymatch type of VIS1 with context [s_pc ?ss] => replace (s_pc ss) with AT_FIXWORD in VIS1 by reflexivity end.
    pose proof (regs_tbl_restrict w [] XS R1 RT_ARM (regs_tbl_sub w XS R1 RT_PM_U9_S1_P_1 RT_ARM HTx1 ltac:(vm_compute; reflexivity))
                  ltac:(vm_compute; reflexivity)) as HT1.
    assert (WSF : forall a n, wa_ff w + 112 <= a -> a + n <= wa_ff w + 132 -> wr_at asegs m a n).
    { intros a n Y1 Y2. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (W1 & W2 & W).
      change (fsz PM_FCLASS) with 16384 in W2, W. split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (wa_ff w + (a - wa_ff w + i)) by lia. apply W. lia. }
    assert (C116 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 9)]).
    { subst M1. eapply (rw_cells_log_nth _ _ _ 2%nat (SA (EVar 33) 116) 4%nat (ELit 9));
        [ exact Hlf1 | reflexivity
        | lazymatch goal with |- Forall _ (firstn 2 ?lg) =>
            let l := eval vm_compute in (firstn 2 lg) in replace (firstn 2 lg) with l by (vm_compute; reflexivity) end;
          apply Forall_cons;
          [ cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite EFu; change (EVar 35) with (EVar WV_S1); rewrite U35; cbn [Z.of_nat]; lia |];
          apply Forall_cons;
          [ cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite EFu;
            change (EAlu ALU_SRL (EVar 33) (ELit 3)) with FSHB; rewrite UFS; cbn [Z.of_nat]; unfold SHBASE in *; lia |];
          apply Forall_nil
        | unfold estart; cbn [a_base a_off]; rewrite EFu; reflexivity
        | apply WSF; lia | reflexivity | exact I | reflexivity ]. }
    assert (TFK1 : ffkeepX w [(116, 4)] m M1).
    { pose proof (munch_sym (Eseed R (wenv_vals w ++ XS)) m (s_log SSr)
        [(EVar 33, 116, 120); (FSHB, SHBASE, SHBASE + PM_NSH); (EVar WV_S1, -16, 0)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU.
      cbn [num_wins map] in TMU. rewrite UFS, EFu, U35 in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [cbn [fst snd]; right; right; apply Exists_cons_hd; cbn [fst snd]; lia |].
      apply Forall_cons; [cbn [fst snd]; unfold PM_NSH; destruct Q6 as [Q6'|Q6']; [left | right; left]; lia |].
      apply Forall_cons; [cbn [fst snd]; left; lia |].
      apply Forall_nil. }
    eapply (K msF1 mo1 M1 R1 (bytes_le_to_Z bs)); [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact HT1
      | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0
      | rewrite (HR1 1%bv); reflexivity
      | rewrite (HR1 2%bv); exact E35
      | exact BR
      | rewrite (HR1 10%bv); transitivity (Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs))); [reflexivity | apply swrap32_sx32A; exact BR]
      | rewrite (HR1 11%bv); exact E41
      | exact C116
      | exact TFK1
      | intros rr Hrr; destruct Hrr as [<-|[<-|[<-|[]]]]; rewrite (HR1 _); reflexivity ].
  Qed.

End U9s1.
