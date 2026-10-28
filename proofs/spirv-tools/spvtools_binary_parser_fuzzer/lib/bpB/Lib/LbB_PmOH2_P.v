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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_PmHex LbB_TablStmt LbB_PmLeaf LbB_PmLH LbB_PmWords LbB_PmCells LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_PmOL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmOHK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord.

Ltac oh_sc A w E33 EFu EA RD0 F H E HE :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCReadBase (SA (EVar 32) _) 4 true _) => sc_fld4 H w E HE F
  | |- sc_denot _ _ _ (SCReadBase (SA (EAlu ALU_ADD (EVar 36) _) 0) 4 true _) =>
      eapply sc_rd_w4s; [rewrite (adenot_of_estart _ _ A); [reflexivity | unfold estart; cbn [a_base a_off]; rewrite EA, u64_of_Z by lia; lia | lia] | exact RD0 | reflexivity]
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_ADD (EVar 36) _) 0) (ELit ?l)) =>
      eapply (sc_flat_lit asegs _ _ _ _ A l); [unfold estart; cbn [a_base a_off]; rewrite EA, u64_of_Z by lia; lia | apply elit_u; lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 36) _) (ELit 3)) _) (ELit ?l)) =>
      eapply (sc_flat_lit asegs _ _ _ _ (A / 8 + SHBASE) l); [apply (estart_sh _ _ A EA); lia | apply elit_u; lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_ADD (EVar 36) _) 0) (ELit ?l1) (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) ?o2) (ELit ?l2)) =>
      eapply (sc_disj_lit asegs _ _ _ _ _ _ A l1 (wa_ff w / 8 + o2) l2);
      [unfold estart; cbn [a_base a_off]; rewrite EA, u64_of_Z by lia; lia | apply elit_u; lia
      | unfold estart; cbn [a_base a_off]; rewrite (srl3_val _ (EVar 33) (wa_ff w) E33) by lia; lia | apply elit_u; lia
      | lia | lia | lia | lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_ADD (EVar 36) _) 0) (ELit ?l1) (SA (EVar 33) ?o2) (ELit ?l2)) =>
      eapply (sc_disj_lit asegs _ _ _ _ _ _ A l1 (wa_ff w + o2) l2);
      [unfold estart; cbn [a_base a_off]; rewrite EA, u64_of_Z by lia; lia | apply elit_u; lia
      | unfold estart; cbn [a_base a_off]; rewrite EFu; lia | apply elit_u; lia
      | lia | lia | lia | lia | lia | lia | lia]
  | |- _ => idtac
  end.

Lemma sc_ck_lt0 : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 63 ->
  sc_denot SEGS M E (SCBr false BC_LT e (ELit 0)).
Proof.
  intros SEGS M E e a He Ha. cbn [sc_denot]. rewrite He. cbn [edenot].
  rewrite br_lts_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma sc_ck_geu : forall (SEGS : list Segment) M E e1 e2 a b, edenot E e1 = Z_to_bv 64 a -> edenot E e2 = Z_to_bv 64 b ->
  0 <= a < b -> b < 2 ^ 64 -> sc_denot SEGS M E (SCBr false BC_GEU e1 e2).
Proof.
  intros SEGS M E e1 e2 a b H1 H2 Hab Hb. cbn [sc_denot]. rewrite H1, H2, br_geu by lia.
  replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma sc_ck_nz2 : forall (SEGS : list Segment) M E e1 e2 a b, edenot E e1 = Z_to_bv 64 a -> edenot E e2 = Z_to_bv 64 b ->
  0 < a < 2 ^ 64 -> 1 <= b < 2 ^ 64 ->
  sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_SLTU (ELit 0) e1) (EAlu ALU_SLTU e2 (ELit 1))).
Proof.
  intros SEGS M E e1 e2 a b H1 H2 Ha Hb. cbn [sc_denot]. cbn [edenot]. rewrite H1, H2.
  rewrite !w_sltu by lia.
  replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma sc_ck_al4 : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 4 = 0 ->
  sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND e (ELit 3)) (ELit 0)).
Proof.
  intros SEGS M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite w_and by lia.
  replace (Z.land a 3) with (a mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
  rewrite Hal. reflexivity.
Qed.

Lemma sc_ck_null : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 < a < 2 ^ 64 ->
  sc_denot SEGS M E (SCBr false BC_EQ e (ELit 0)).
Proof.
  intros SEGS M E e a He Ha. cbn [sc_denot]. rewrite He. cbn [edenot]. rewrite br_eq by lia.
  apply Z.eqb_neq. lia.
Qed.

Lemma sc_ck_wrap : forall (SEGS : list Segment) M E e1 e2 a k, edenot E e1 = Z_to_bv 64 (a + k) -> edenot E e2 = Z_to_bv 64 a ->
  0 <= a -> 0 <= k -> a + k < 2 ^ 64 -> sc_denot SEGS M E (SCBr false BC_LTU e1 e2).
Proof.
  intros SEGS M E e1 e2 a k H1 H2 Ha Hk Hak. cbn [sc_denot]. rewrite H1, H2, br_ltu by lia.
  apply Z.ltb_ge. lia.
Qed.

Lemma sc_ck_srl62 : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 62 ->
  sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_SRL e (ELit 62)) (ELit 0)).
Proof.
  intros SEGS M E e a He Ha. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite w_srl by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma sc_ck_part4 : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 8 = 0 ->
  sc_denot SEGS M E (SCBr false BC_GE (EAlu ALU_ADD (EAlu ALU_AND e (ELit 7)) (ELit 3)) (ELit 4)).
Proof.
  intros SEGS M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite (and7_add3_w a Ha Hal). reflexivity.
Qed.

Section OH2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Lemma pm_oh2_P : forall (w : pmwA H) s LB LBs m mo c msF R F fc (io iwc op t : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf136c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EEFB0 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 t ->
    0 <= t < 2 ^ 31 ->
    0 <= io <= c_widx c ->
    0 <= iwc < 2 ^ 16 ->
    c_widx c < io + iwc ->
    0 <= op < 2 ^ 16 ->
    wa_words w <> 0 ->
    c_widx c < wa_n w ->
    c_endian c = 0 \/ c_endian c = 1 ->
    4 * c_widx c = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4 ->
    rw_cells asegs m (wa_ff w + 10112) [C8 (Z_to_bv 64 io)] ->
    rw_cells asegs m (wa_ff w + 9050) [C2 (Z_to_bv 64 op)] ->
    (forall msF1 mo1 m1 R1 (x0 : Z), as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_FIXWORD) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_EF07Cc ->
       PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       0 <= x0 < 2 ^ 32 -> PropExec.getr R1 10%bv = Z_to_bv 64 (sx32A x0) -> PropExec.getr R1 11%bv = Z_to_bv 64 (c_endian c) ->
       PropExec.getr R1 18%bv = Z_to_bv 64 t -> PropExec.getr R1 22%bv = Z_to_bv 64 op -> PropExec.getr R1 25%bv = Z_to_bv 64 io ->
       popndA H w m1 (c_widx c - io) t ->
       rw_cells asegs m1 (wa_ff w + 10112) [C8 (Z_to_bv 64 io)] -> rw_cells asegs m1 (wa_ff w + 9050) [C2 (Z_to_bv 64 op)] ->
       ffkeepX w [(128, 4); (124, 4); (120, 4); (116, 4); (114, 2); (112, 2)] m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame.
    intros w s LB LBs m mo c msF R F fc io iwc op t Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 T10 Ht Hio Hiwc HLT Hop
           HW0 HWN HEND HGR CIO COP K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X0) as (_ & _ & PAW). specialize (PAW HW0).
    assert (HinLB : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)))). apply in_app_iff. left. exact Hin. }
    pose proof (ah_blocks H HHm _ _ _ _ (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) HinLB) as (_ & _ & _ & _ & _ & _ & RAPP).
    cbn [blk_addr blk_size fst snd] in RAPP.
    pose proof (aapp_disjoint_sh (wa_words w) k (wa_ff w) 16384 RAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DSH.
    rewrite Q13 in DSH. change (nsh 16384) with 2048 in DSH.
    assert (SHV : SHBASE = 0x7fff8000) by reflexivity.
    destruct (words_rd4 H LINV w _ _ _ _ _ _ _ _ _ _ _ (c_widx c) OK X0 HW0 ltac:(lia)) as (bs & RD0 & BL).
    pose proof (bytes_le_to_Z_range4 bs BL) as BR.
    set (A := wa_words w + 4 * c_widx c) in *.
    set (XS := [Z_to_bv 64 io; Z_to_bv 64 (c_widx c); Z_to_bv 64 op; Z_to_bv 64 (c_endian c);
                Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs))]).
    pose proof (env_world_seed H w R XS) as HE.
    pose proof (ev_ff H w _ OK HE) as EFw. pose proof EFw as EFu. change (EVar WV_FF) with (EVar 33%N) in EFu.
    destruct (ev_world_all H w _ HE) as (E32 & E33 & _ & _ & E36 & E37 & _).
    assert (E41 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 41) = Z_to_bv 64 io) by reflexivity.
    assert (E42 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 42) = Z_to_bv 64 (c_widx c)) by reflexivity.
    assert (E43 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 43) = Z_to_bv 64 op) by reflexivity.
    assert (E44 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 44) = Z_to_bv 64 (c_endian c)) by reflexivity.
    assert (E10 : edenot (Eseed R (wenv_vals w ++ XS)) (EVar 10) = Z_to_bv 64 t) by (cbn [edenot]; rewrite Eseed_reg by lia; exact T10).
    assert (EA : edenot (Eseed R (wenv_vals w ++ XS)) (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 42))) = Z_to_bv 64 A)
      by (apply ev_idx4b; [exact E36 | exact E42 | lia | lia | lia]).
    assert (A8 : 0 <= A / 8 < 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ XS)) m
      [KWord (SA (EVar WV_FF) 10112) 8 (EVar 41); KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 42);
       KWord (SA (EVar WV_FF) 9050) 2 (EVar 43);
       KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 42))) (ELit 3)) SHBASE) 1 (ELit 4);
       KDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 42))) (ELit 3)) SHBASE) (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH);
       KDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 42))) (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384)]).
    { apply Forall_cons.
      { eapply (kword_of_rw_cells asegs _ m (wa_ff w + 10112) _ 0%nat (C8 (Z_to_bv 64 io)));
          [exact CIO | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EFw; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity]. }
      apply Forall_cons.
      { eapply pmk_scal_widx with (1 := OK) (2 := X0) (3 := HE); exact E42. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs _ m (wa_ff w + 9050) _ 0%nat (C2 (Z_to_bv 64 op)));
          [exact COP | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EFw; cbn [Z.of_nat]; lia
          | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E43; reflexivity]. }
      apply Forall_cons.
      { first [eapply pmk_sh_wordsE_part with (1 := HHm) (2 := OK) (3 := X0) (4 := HW0) | eapply pmk_sh_wordsE_part with (1 := OK) (2 := X0) (3 := HW0)];
          [exact EA | lia | lia]. }
      apply Forall_cons.
      { first [eapply pmk_sh_fshdisj with (1 := HHm) (2 := OK) (3 := X0) (4 := HE) | eapply pmk_sh_fshdisj with (1 := OK) (2 := X0) (3 := HE)];
          [exact EA | lia | lia | lia]. }
      apply Forall_cons.
      { first [eapply pmk_sh_ffdisj with (1 := HHm) (2 := OK) (3 := X0) (4 := HE) | eapply pmk_sh_ffdisj with (1 := OK) (2 := X0) (3 := HE)];
          [exact EA | lia | lia]. }
      apply Forall_nil. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 XS
      [KWord (SA (EVar WV_FF) 10112) 8 (EVar 41); KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 42);
       KWord (SA (EVar WV_FF) 9050) 2 (EVar 43);
       KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 42))) (ELit 3)) SHBASE) 1 (ELit 4);
       KDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 42))) (ELit 3)) SHBASE) (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH);
       KDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 42))) (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384)]
      HK1 300%nat [AT_FIXWORD] [false; false; false; false; false; false; false; false; false] 44%N
      S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_EF07Cc.
    { split_scs.
      all: first
        [ eapply sc_ck_lt0; [exact E10 | lia]
        | eapply sc_ck_lt0; [exact E44 | lia]
        | eapply sc_ck_geu; [exact E42 | exact E37 | lia | lia]
        | eapply sc_ck_nz2; [exact E36 | exact EA | lia | lia]
        | eapply sc_ck_srl62; [eapply ev_add; [exact E42 | lia | lia] | lia]
        | eapply (sc_ck_wrap _ _ _ _ _ (wa_words w) (4 * c_widx c)); [exact EA | exact E36 | lia | lia | lia]
        | eapply sc_ck_null; [exact E36 | lia]
        | eapply sc_ck_al4; [exact EA | lia | unfold A; Z.div_mod_to_equations; lia]
        | eapply sc_ck_part4; [exact EA | lia | unfold A; destruct HGR as [HG1 _]; rewrite HG1; Z.div_mod_to_equations; lia]
        | solve [oh_sc A w E33 EFu EA RD0 (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) H (Eseed R (wenv_vals w ++ XS)) HE] ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    replace (s_pc SSr) with AT_FIXWORD in VIS1 by reflexivity.
    pose proof (regs_tbl_restrict w [] _ R1 RT_EF07Cc HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    assert (ESR : bv_unsigned (edenot (Eseed R (wenv_vals w ++ XS)) (EAlu ALU_SRL (EVar 33) (ELit 3))) = wa_ff w / 8)
      by (apply (srl3_val _ (EVar 33) (wa_ff w) E33); lia).
    assert (WSF : forall a n, wa_ff w + 112 <= a -> a + n <= wa_ff w + 132 -> wr_at asegs m a n).
    { intros a n Y1 Y2. pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (W1 & W2 & W).
      change (fsz PM_FCLASS) with 16384 in W2, W. split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (wa_ff w + (a - wa_ff w + i)) by lia. apply W. lia. }
    assert (C112 : rw_cells asegs M1 (wa_ff w + 112) [C2 (Z_to_bv 64 (c_widx c - io))]).
    { subst M1. eapply (rw_cells_log_nth_2b _ _ _ 6%nat _ (EAlu ALU_SRL (EVar 33) (ELit 3)) _ _ _ SHBASE (SHBASE + 2048));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFu; lia | rewrite ESR; lia | apply WSF; lia | reflexivity | exact I
        | cbn [cbytes]; rewrite (ev_subw_small _ 42 41 (c_widx c) io E42 E41) by lia; reflexivity]. }
    assert (C114 : rw_cells asegs M1 (wa_ff w + 114) [C2 (Z_to_bv 64 1)]).
    { subst M1. eapply (rw_cells_log_nth_2b _ _ _ 5%nat _ (EAlu ALU_SRL (EVar 33) (ELit 3)) _ _ _ SHBASE (SHBASE + 2048));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFu; lia | rewrite ESR; lia | apply WSF; lia | reflexivity | exact I
        | reflexivity]. }
    assert (C116 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 t)]).
    { subst M1. eapply (rw_cells_log_nth_2b _ _ _ 4%nat _ (EAlu ALU_SRL (EVar 33) (ELit 3)) _ _ _ SHBASE (SHBASE + 2048));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFu; lia | rewrite ESR; lia | apply WSF; lia | reflexivity | exact I
        | cbn [cbytes]; rewrite E10; reflexivity]. }
    assert (C120 : rw_cells asegs M1 (wa_ff w + 120) [C4 (Z_to_bv 64 0)]).
    { subst M1. eapply (rw_cells_log_nth_2b _ _ _ 3%nat _ (EAlu ALU_SRL (EVar 33) (ELit 3)) _ _ _ SHBASE (SHBASE + 2048));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFu; lia | rewrite ESR; lia | apply WSF; lia | reflexivity | exact I
        | reflexivity]. }
    assert (C124 : rw_cells asegs M1 (wa_ff w + 124) [C4 (Z_to_bv 64 0)]).
    { subst M1. eapply (rw_cells_log_nth_2b _ _ _ 2%nat _ (EAlu ALU_SRL (EVar 33) (ELit 3)) _ _ _ SHBASE (SHBASE + 2048));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFu; lia | rewrite ESR; lia | apply WSF; lia | reflexivity | exact I
        | reflexivity]. }
    assert (C128 : rw_cells asegs M1 (wa_ff w + 128) [C4 (Z_to_bv 64 0)]).
    { subst M1. eapply (rw_cells_log_nth_2b _ _ _ 1%nat _ (EAlu ALU_SRL (EVar 33) (ELit 3)) _ _ _ SHBASE (SHBASE + 2048));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFu; lia | rewrite ESR; lia | apply WSF; lia | reflexivity | exact I
        | reflexivity]. }
    assert (TFK1 : ffkeepX w [(128, 4); (124, 4); (120, 4); (116, 4); (114, 2); (112, 2)] m M1).
    { pose proof (munch_sym (Eseed R (wenv_vals w ++ XS)) m (s_log SSr)
        [(EVar 33, 112, 114); (EVar 33, 114, 116); (EVar 33, 116, 120); (EVar 33, 120, 124); (EVar 33, 124, 128);
         (EVar 33, 128, 132); (EAlu ALU_SRL (EVar 33) (ELit 3), SHBASE, SHBASE + 2048)] Hlf1 ltac:(vm_compute; reflexivity)) as TMU.
      cbn [num_wins map] in TMU. rewrite ?ESR, ?EFu in TMU.
      apply (ffkeepX_munch w _ _ _ _ TMU (wmono_mem_denot _ _ _)).
      repeat (apply Forall_cons; [cbn [fst snd]; first [left; lia | right; left; lia
        | (destruct Q6 as [Q6'|Q6']; [left | right; left]; lia)
        | right; right; solve [repeat (first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl])]] |]).
      apply Forall_nil. }
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    eapply (K msF1 mo1 M1 R1 (bytes_le_to_Z bs)); [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact HT1 | exact G3_1 | exact G4_1
      | exact BR
      | rewrite (HR1 10%bv); transitivity (Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs))); [reflexivity | apply swrap32_sx32A; exact BR]
      | rewrite (HR1 11%bv); exact E44
      | rewrite (HR1 18%bv); exact E10
      | rewrite (HR1 22%bv); exact (edenot_zext16 _ 43 op E43 ltac:(lia))
      | rewrite (HR1 25%bv); exact E41
      | exact (conj C112 (conj C114 (conj C116 (conj C120 (conj C124 C128)))))
      | apply (ffkeepX_cell w _ _ _ _ _ TFK1 CIO); [lia | cbn; lia | reflexivity]
      | apply (ffkeepX_cell w _ _ _ _ _ TFK1 COP); [lia | cbn; lia | reflexivity]
      | exact TFK1 ].
  Qed.

End OH2.
