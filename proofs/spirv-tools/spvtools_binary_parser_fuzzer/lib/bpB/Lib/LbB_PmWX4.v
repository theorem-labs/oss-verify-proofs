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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmHex LbB_PmDS LbB_PmExit2 LbB_PmLH LbB_PmOL LbB_TablStmt LbB_TablImg LbB_PmLeaf LbB_PmLeafW LbB_PmWords LbB_PmU2K LbB_PmWC1 LbB_PmWX1 LbB_PmWX2 LbB_PmWX5 LbB_PmWX3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition EW8 : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 8).
Definition EW12b : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 12).

Definition S_DESC : list nat := 0%nat :: S_INSTR.

Definition RT_X4A : list (reg * expr) :=
  [(1%bv, ELit 0xf4ebc); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (19%bv, WADD WV_FF 9040); (20%bv, SH_FF);
   (22%bv, WADD WV_P 88); (23%bv, EVar WV_P); (24%bv, WADD WV_FF 7984); (25%bv, WADD WV_P 48); (26%bv, WADD WV_P 216);
   (27%bv, EVar WV_FF)].

Definition RT_X4T : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, ELit SHBASE); (19%bv, WADD WV_FF 32); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 9060); (22%bv, WADD WV_P 88); (23%bv, EVar WV_P); (25%bv, WADD WV_P 48); (26%bv, ELit 3); (27%bv, EVar WV_FF)].

Definition RT_X4B : list (reg * expr) := (1%bv, ELit 0xf4f74) :: RT_X4T.
Definition RT_X4D : list (reg * expr) := (1%bv, ELit 0xf4f84) :: RT_X4T.
Definition RT_X4C : list (reg * expr) := (10%bv, ELit 34) :: (12%bv, WADD WV_FF 32) :: RT_X4D.
Definition RT_X4E : list (reg * expr) := (1%bv, ELit 0xf511c) :: RT_X4T.

Lemma x4_bne : forall r, - 2 ^ 31 <= r < 2 ^ 31 -> r <> 0 -> branch_taken BC_EQ (Z_to_bv 64 r) (Z_to_bv 64 0) = false.
Proof.
  intros r Hr Hn.
  replace (Z_to_bv 64 r) with (Z_to_bv 64 (r mod 2 ^ 64)).
  - rewrite br_eq by (Z.div_mod_to_equations; lia). apply Z.eqb_neq. Z.div_mod_to_equations; lia.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Section TX4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHx4 : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Ltac tlx4_rd a bs RD YB YA :=
    first
      [ eapply (sc_rd_w4s _ _ _ a bs _);
          [ apply (adenot_of_estart _ _ a); [unfold estart; cbn [a_base a_off]; rewrite YB, u64_of_Z by lia; lia | lia]
          | exact RD | ev_xs; reflexivity ]
      | eapply (sc_flat_lit asegs _ _ _ _ a 4);
          [unfold estart; cbn [a_base a_off]; rewrite YB, u64_of_Z by lia; lia | apply elit_u; lia | lia | lia | lia]
      | eapply (sc_flat_lit asegs _ _ _ _ (a / 8 + SHBASE) 1);
          [apply (estart_sh _ _ a YA); lia | apply elit_u; lia
          | unfold SHBASE; Z.div_mod_to_equations; lia | lia | unfold SHBASE; Z.div_mod_to_equations; lia] ].

  Ltac x4_br :=
    cbn [sc_denot];
    first
      [ eapply x3_sltu; [eassumption | eassumption | lia | lia]
      | repeat match goal with
               | Y : edenot ?E ?e = _ |- context [edenot ?E ?e] => rewrite Y
               end;
        rewrite ?x3_lit; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ge_small, ?br_lts_small by lia; bool_lia ].

  Lemma x4_fksh : forall (w : pmwA H) E m m1 lg, pmw_okA H w -> ffkeepX w X3_FFX m m1 ->
    edenot E (EVar 33) = Z_to_bv 64 (wa_ff w) -> log_flat E lg ->
    forallb (sym_inside [(EVar WV_FF, 32, 40); (EAlu ALU_SRL (EVar WV_FF) (ELit 3), SHBASE + 4, SHBASE + 5)]) lg = true ->
    ffkeepX w X3_FFX m (mem_denot E m1 lg).
  Proof.
    intros w E m m1 lg OK K E33 Hf Hb. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (munch_sym _ m1 _ _ Hf Hb) as MU. cbn [num_wins map] in MU. unfold WV_FF in MU.
    rewrite (srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)) in MU. rewrite E33, u64_of_Z in MU by lia.
    apply (x3_fk H w m m1 _ _ K MU (wmono_mem_denot _ _ _)).
    apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia|].
    apply Forall_cons; [destruct Q6 as [Q6 | Q6]; [left | right; left]; cbn [fst snd]; lia | apply Forall_nil].
  Qed.

  Lemma tl_x4 : forall (w : pmwA H) s LB LBs m mo (c : pmc) msF R F fc (io iwc : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4e1c) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_X3F -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 21%bv = Z_to_bv 64 io ->
    rw_cells asegs m (wa_ff w + 9048) [C2 (Z_to_bv 64 iwc)] ->
    0 <= io -> 3 <= iwc < 2 ^ 16 -> io + iwc <= wa_n w -> wa_words w <> 0 ->
    c_endian c = 0 \/ c_endian c = 1 ->
    K3234 H LINV w s LB LBs m c F fc Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc io iwc Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 G21 Ciwc Hio Hiwc Hn Hw Hend KK.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmw_apart_ff H HHx4 LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] [] 0 OK X0) as (_ & _ & APW).
    specialize (APW Hw).
    destruct (wk_words H w OK) as [[E0 _]|(pw & kw & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    assert (WAPP : wa_words w + kw <= ALOWSH_LO \/ AHI_LO <= wa_words w).
    { pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (PERM & _).
      assert (HinL : In (pw, wa_words w, kw) LB)
        by (eapply Permutation_in; [apply Permutation_sym; exact PERM | apply in_or_app; left; exact Hin]).
      pose proof (ah_blocks H HHx4 _ _ _ _ (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) HinL) as (_ & _ & _ & _ & _ & _ & APP).
      cbn [blk_addr blk_size fst snd] in APP. destruct APP as [[A1 A2] | [A1 A2]]; [left; exact A2 | right; exact A1]. }
    unfold ALOWSH_LO, AHI_LO in WAPP.
    destruct (words_rd4 H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] [] 0 (io + 2) OK X0 Hw ltac:(lia)) as (bs2 & RD2 & L2).
    pose proof (bytes_le_to_Z_range4 bs2 L2) as Rg2.
    replace (wa_words w + 4 * (io + 2)) with (wa_words w + 4 * io + 8) in RD2 by lia.

    assert (CONTA : forall msF1 mo1 R1,
              as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_FIXWORD) fc None m (seg_rom asegs) -> rfull R1 ->
              PMXA H LINV w s LB LBs m mo1 c S_INSTR TBL_EEF44 [] ->
              regs_tbl w R1 RT_X4A -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
              PropExec.getr R1 21%bv = Z_to_bv 64 io -> PropExec.getr R1 18%bv = Z_to_bv 64 (io + 2 ^ 61) ->
              PropExec.getr R1 10%bv = Z_to_bv 64 (sx32A (bytes_le_to_Z bs2)) -> PropExec.getr R1 11%bv = Z_to_bv 64 (c_endian c) ->
              as_SR H Q (mkCfg msF1 mo1)).
    { intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G21_1 G18_1 G10_1 G11_1.
      eapply (pm_leafW H HHx4 LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) (bytes_le_to_Z bs2, c_endian c) []
                w s LB LBs m mo1 c S_INSTR TBL_EEF44 [] [] 0 msF1 R1 F fc 0xf4ebc Q []);
        [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | rtf HT1 | rtf HT1 | reflexivity | lia | lia | reflexivity | reflexivity
        | cbn beta iota; split; [lia|]; split; [exact G10_1|]; split; [lia | exact G11_1]
        | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
        | intros r0 r1 m9 k9 n9 a9 _ Hin9; destruct Hin9
        | ].
      intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 (r2 & Hr2 & Er2).
      pose proof (regs_keep w [] R1 R2 RT_X4A HT1 KEEP2) as HT2. change (rt_keep RT_X4A) with RT_X4A in HT2.
      assert (FK2 : ffkeepX w X3_FFX m m2) by exact (x3_fkleaf H w m m m2 0 OK ltac:(lia) (ffkeepX_refl w X3_FFX m) MU2 WM2).
      assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inb)); exact G3_1).
      assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inb)); exact G4_1).
      assert (Ciwc2 : rw_cells asegs m2 (wa_ff w + 9048) [C2 (Z_to_bv 64 iwc)])
        by exact (ffkeepX_cell w X3_FFX m m2 9048 _ FK2 Ciwc ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)).
      pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2.
      destruct (Z_le_gt_dec iwc 3) as [I3 | I4].
      - set (Xs := [Z_to_bv 64 iwc]).
        pose proof (env_world_seed H w R2 Xs) as HE.
        pose proof (ev_world_all H w _ HE) as (_ & E33 & _).
        assert (Y41 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
        assert (YIW : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EExt false 0 2 (EVar 41)) = Z_to_bv 64 iwc)
          by (apply edenot_zext16; [exact Y41 | lia]).
        assert (HKX : know_ok asegs (Eseed R2 (wenv_vals w ++ Xs)) m2 [KWord (SA (EVar 33) 9048) 2 (EVar 41)]).
        { apply Forall_cons; [| apply Forall_nil].
          eapply (kword_of_rw_cells asegs _ m2 (wa_ff w + 9048) _ 0 (C2 (Z_to_bv 64 iwc))); [exact Ciwc2 | reflexivity | reflexivity | lia
            | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
            | rewrite Y41; reflexivity]. }
        pm_goX HHx4 LINV_frame OK X2 KR2 VIS2 RF2 HT2 Xs [KWord (SA (EVar 33) 9048) 2 (EVar 41)] HKX
              40%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] [true] 42%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44
              (@nil (Z * expr)) RT_X3K.
        { split_scs. all: first [x4_br | match goal with |- ?g => idtac "SCLEFT" g end]. }
        intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
        lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m2 in X3 end.
        change (mem_denot _ m2 _) with m2 in VIS3.
        eapply (KK msF3 mo3 m2 R3 3 (sx32A r2) 0 KR3 VIS3 RF3 X3);
          [ exact (regs_tbl_restrict w [] _ R3 RT_X3K HTx3 ltac:(vm_compute; reflexivity))
          | rewrite (HR3 3%bv); exact G3_2 | rewrite (HR3 4%bv); exact G4_2
          | rewrite (HR3 26%bv); reflexivity | lia | rewrite (HR3 24%bv); exact (x3_ereg R2 _ 10 _ ltac:(lia) Er2) | apply x3_sxr; lia
          | rewrite (HR3 15%bv); reflexivity | lia | exact FK2 ].
      - assert (WR32 : wr_at asegs m2 (wa_ff w + 32) 8).
        { split; [lia|]. split; [lia|]. intros i Hi. replace (wa_ff w + 32 + i) with (wa_ff w + (32 + i)) by lia. apply FW2. lia. }
        destruct (words_rd4 H LINV w s LB LBs m2 mo2 c S_INSTR TBL_EEF44 [] [] 0 (io + 3) OK X2 Hw ltac:(lia)) as (bs3 & RD3 & L3).
        pose proof (bytes_le_to_Z_range4 bs3 L3) as Rg3.
        replace (wa_words w + 4 * (io + 3)) with (wa_words w + 4 * io + 12) in RD3 by lia.

        assert (CONTB : forall msF3 mo3 m3 R3,
                  as_AKREL H s (mkCfg msF3 mo3) -> as_VIS H s msF3 = MS R3 F (Z_to_bv 64 AT_FIXWORD) fc None m3 (seg_rom asegs) -> rfull R3 ->
                  PMXA H LINV w s LB LBs m3 mo3 c S_DESC TBL_EEF44 [] ->
                  regs_tbl w R3 RT_X4B -> PropExec.getr R3 3%bv = wa_gp w -> PropExec.getr R3 4%bv = wa_tp w ->
                  PropExec.getr R3 24%bv = Z_to_bv 64 (sx32A r2) ->
                  PropExec.getr R3 10%bv = Z_to_bv 64 (sx32A (bytes_le_to_Z bs3)) -> PropExec.getr R3 11%bv = Z_to_bv 64 (c_endian c) ->
                  rw_cells asegs m3 (wa_ff w + 32) [C8 (Z_to_bv 64 0)] -> ffkeepX w X3_FFX m m3 ->
                  as_SR H Q (mkCfg msF3 mo3)).
        { intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 G24_3 G10_3 G11_3 C32 FK3.
          eapply (pm_leafW H HHx4 LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) (bytes_le_to_Z bs3, c_endian c) []
                    w s LB LBs m3 mo3 c S_DESC TBL_EEF44 [] [] 0 msF3 R3 F fc 0xf4f74 Q []);
            [ exact OK | exact X3 | exact KR3 | exact VIS3 | exact RF3 | rtf HT3 | rtf HT3 | reflexivity | lia | lia | reflexivity | reflexivity
            | cbn beta iota; split; [lia|]; split; [exact G10_3|]; split; [lia | exact G11_3]
            | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
            | intros r0 r1 m9 k9 n9 a9 _ Hin9; destruct Hin9
            | ].
          intros msF4 mo4 m4 R4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 (r3 & Hr3 & Er3).
          pose proof (regs_keep w [] R3 R4 RT_X4B HT3 KEEP4) as HT4. change (rt_keep RT_X4B) with RT_X4B in HT4.
          assert (FK4 : ffkeepX w X3_FFX m m4) by exact (x3_fkleaf H w m m3 m4 0 OK ltac:(lia) FK3 MU4 WM4).
          assert (C32_4 : rw_cells asegs m4 (wa_ff w + 32) [C8 (Z_to_bv 64 0)]).
          { apply (ffkeep_munch w _ m3 m4 MU4 WM4); [| lia | cbn; lia | exact C32].
            apply Forall_cons; [left; cbn [fst]; lia | apply Forall_nil]. }
          assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv ltac:(inb)); exact G3_3).
          assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv ltac:(inb)); exact G4_3).
          assert (G24_4 : PropExec.getr R4 24%bv = Z_to_bv 64 (sx32A r2)) by (rewrite (KEEP4 24%bv ltac:(inb)); exact G24_3).
          set (Xs4 := @nil word).
          pose proof (env_world_seed H w R4 Xs4) as HE4.
          pose proof (ev_world_all H w _ HE4) as (_ & E33_4 & _).
          assert (HKN4 : know_ok asegs (Eseed R4 (wenv_vals w ++ Xs4)) m4 []) by apply Forall_nil.
          pm_goX HHx4 LINV_frame OK X4 KR4 VIS4 RF4 HT4 Xs4 (@nil kentry) HKN4
                40%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] (@nil bool) 41%N S_DESC (@nil Z) (@nil Z) TBL_EEF44
                (@nil (Z * expr)) RT_X4C.
          { split_scs. }
          intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
          lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m4 in X5 end.
          change (mem_denot _ m4 _) with m4 in VIS5.
          pose proof (regs_tbl_restrict w [] _ R5 RT_X4C HTx5 ltac:(vm_compute; reflexivity)) as HT5.
          assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (HR5 3%bv); exact G3_4).
          assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (HR5 4%bv); exact G4_4).
          assert (G24_5 : PropExec.getr R5 24%bv = Z_to_bv 64 (sx32A r2))
            by (rewrite (HR5 24%bv); exact (x3_ereg R4 _ 24 _ ltac:(lia) G24_4)).
          assert (G2_5 : PropExec.getr R5 2%bv = Z_to_bv 64 (wa_s1 w)) by rtf HT5.
          assert (Gra5 : PropExec.getr R5 1%bv = Z_to_bv 64 0xf4f84) by rtf HT5.
          assert (G10_5 : PropExec.getr R5 10%bv = Z_to_bv 64 34) by rtf HT5.
          assert (G12_5 : PropExec.getr R5 12%bv = Z_to_bv 64 (wa_ff w + 32)) by rtf HT5.
          assert (G11_5 : PropExec.getr R5 11%bv = Z_to_bv 64 (sx32A r3))
            by (rewrite (HR5 11%bv); exact (x3_ereg R4 _ 10 _ ltac:(lia) Er3)).
          assert (MD : mdef m4 (wa_ff w + 32) 8) by exact (mdef_of_rw_cells m4 _ _ C32_4 ltac:(unfold AIMG_TOP, AFS_HDR in *; lia)).
          eapply (pm_lookup H HHx4 LINV LINV_frame _ _ _ _ (tla_lookup_operand HTL) 34 r3 32 w s LB LBs m4 mo5 c S_DESC TBL_EEF44 [] [] 0
                    msF5 R5 F fc 0xf4f84 Q [] OK X5 KR5 VIS5 RF5 G2_5 Gra5 eq_refl ltac:(lia) G10_5 ltac:(lia)
                    ltac:(intros Hn2; discriminate Hn2) ltac:(intros _; exact (conj G11_5 (conj Hr3 G12_5))) eq_refl);
            [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
            | exact MD |].
          intros msF6 mo6 m6 R6 r KR6 VIS6 RF6 X6 KEEP6 MU6 WM6 Gr Hr Hiff Hfound Hmiss.
          pose proof (regs_keep w [] R5 R6 RT_X4C HT5 KEEP6) as HT6. change (rt_keep RT_X4C) with RT_X4D in HT6.
          assert (FK6 : ffkeepX w X3_FFX m m6).
          { apply (x3_fk H w m m4 m6 _ FK4 MU6 WM6). apply Forall_cons; [left; cbn [fst]; unfold TL_STACK; lia|].
            cbn [offs_wins map]. apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
          assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (rewrite (KEEP6 3%bv ltac:(inb)); exact G3_5).
          assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (rewrite (KEEP6 4%bv ltac:(inb)); exact G4_5).
          assert (G24_6 : PropExec.getr R6 24%bv = Z_to_bv 64 (sx32A r2)) by (rewrite (KEEP6 24%bv ltac:(inb)); exact G24_5).
          assert (G26_6 : PropExec.getr R6 26%bv = Z_to_bv 64 3) by rtf HT6.
          destruct (Z.eq_dec r 0) as [R0 | RN0].
          + destruct (Hfound R0) as (d & CDd & HOD). subst r.
            destruct (odescA_facts d 34 r3 HOD) as (rr & Hfi & Htg & Hv & Dlo & Dhi & D4 & D52 & FL & _).
            destruct (FL m6 (conj (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6) (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6)))
              as (F0 & _ & _ & GZ).
            set (Xs := [Z_to_bv 64 d; Z_to_bv 64 r3]).
            pose proof (env_world_seed H w R6 Xs) as HE.
            pose proof (ev_world_all H w _ HE) as (_ & E33 & _).
            assert (Y41 : edenot (Eseed R6 (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 d) by (ev_xs; reflexivity).
            assert (Y42 : edenot (Eseed R6 (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 r3) by (ev_xs; reflexivity).
            assert (Y10 : edenot (Eseed R6 (wenv_vals w ++ Xs)) (EVar 10) = Z_to_bv 64 0) by (apply x3_ereg; [lia | exact Gr]).
            assert (YAND : edenot (Eseed R6 (wenv_vals w ++ Xs)) (EAlu ALU_AND (EVar 41) (ELit 3)) = Z_to_bv 64 0)
              by (apply (x3_and3 _ _ d Y41); lia).
            assert (HKX : know_ok asegs (Eseed R6 (wenv_vals w ++ Xs)) m6
                            [KWord (SA (EVar 33) 32) 8 (EVar 41); KWord (SA (EAlu ALU_SRL (EVar 41) (ELit 3)) SHBASE) 1 (ELit 0);
                             KWord (SA (EVar 41) 0) 4 (EVar 42)]).
            { apply Forall_cons.
              { eapply (kword_of_rw_cells asegs _ m6 (wa_ff w + 32) _ 0 (C8 (Z_to_bv 64 d))); [exact CDd | reflexivity | reflexivity | lia
                  | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
                  | rewrite Y41; reflexivity]. }
              apply Forall_cons.
              { apply (kshadow0 _ m6 (EVar 41) d Y41 ltac:(lia)). pose proof (gz_at m6 d 12 0 GZ ltac:(lia)) as S0.
                rewrite Z.add_0_r in S0. exact S0. }
              apply Forall_cons; [| apply Forall_nil].
              apply (kword_of_fld _ m6 d 4 r3 (SA (EVar 41) 0) (EVar 42) F0); [lia | | lia | lia | exact Y42].
              unfold estart; cbn [a_base a_off]. rewrite Y41, u64_of_Z by lia. lia. }
            pm_goX HHx4 LINV_frame OK X6 KR6 VIS6 RF6 HT6 Xs
                  [KWord (SA (EVar 33) 32) 8 (EVar 41); KWord (SA (EAlu ALU_SRL (EVar 41) (ELit 3)) SHBASE) 1 (ELit 0);
                   KWord (SA (EVar 41) 0) 4 (EVar 42)] HKX
                  40%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] [true; true; true] 43%N S_DESC (@nil Z) (@nil Z) TBL_EEF44
                  (@nil (Z * expr)) RT_X4E.
            { split_scs. all: first [ tlx4_rd d I Y41 Y41 Y41 | x4_br | match goal with |- ?g => idtac "SCLEFT" g end ]. }
            intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
            lazymatch type of X7 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m6 in X7 end.
            change (mem_denot _ m6 _) with m6 in VIS7.
            pose proof (regs_tbl_restrict w [] _ R7 RT_X4E HTx7 ltac:(vm_compute; reflexivity)) as HT7.
            assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (HR7 3%bv); exact G3_6).
            assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (HR7 4%bv); exact G4_6).
            assert (G24_7 : PropExec.getr R7 24%bv = Z_to_bv 64 (sx32A r2))
              by (rewrite (HR7 24%bv); exact (x3_ereg R6 _ 24 _ ltac:(lia) G24_6)).
            eapply (pm_leafW H HHx4 LINV LINV_frame AT_FPENC 0 _ _ _ (tla_fpenc HTL) tt []
                      w s LB LBs m6 mo7 c S_DESC TBL_EEF44 [] [] 0 msF7 R7 F fc 0xf511c Q []);
              [ exact OK | exact X7 | exact KR7 | exact VIS7 | exact RF7 | rtf HT7 | rtf HT7 | reflexivity | lia | lia | reflexivity | reflexivity
              | exact I
              | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
              | intros r0 r1 m9 k9 n9 a9 _ Hin9; destruct Hin9
              | ].
            intros msF8 mo8 m8 R8 KR8 VIS8 RF8 X8 KEEP8 MU8 WM8 (re & Hre & Ere).
            pose proof (regs_keep w [] R7 R8 RT_X4E HT7 KEEP8) as HT8. change (rt_keep RT_X4E) with RT_X4E in HT8.
            assert (FK8 : ffkeepX w X3_FFX m m8) by exact (x3_fkleaf H w m m6 m8 0 OK ltac:(lia) FK6 MU8 WM8).
            assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv ltac:(inb)); exact G3_7).
            assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv ltac:(inb)); exact G4_7).
            assert (G24_8 : PropExec.getr R8 24%bv = Z_to_bv 64 (sx32A r2)) by (rewrite (KEEP8 24%bv ltac:(inb)); exact G24_7).
            assert (G26_8 : PropExec.getr R8 26%bv = Z_to_bv 64 3) by rtf HT8.
            set (Xs8 := @nil word).
            pose proof (env_world_seed H w R8 Xs8) as HE8.
            pose proof (ev_world_all H w _ HE8) as (_ & E33_8 & _).
            assert (HKN8 : know_ok asegs (Eseed R8 (wenv_vals w ++ Xs8)) m8 []) by apply Forall_nil.
            pm_goX HHx4 LINV_frame OK X8 KR8 VIS8 RF8 HT8 Xs8 (@nil kentry) HKN8
                  40%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] (@nil bool) 41%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44
                  (@nil (Z * expr)) RT_X3K.
            { split_scs. }
            intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
            eapply (KK msF9 mo9 _ R9 3 (sx32A r2) re KR9 VIS9 RF9 X9);
              [ exact (regs_tbl_restrict w [] _ R9 RT_X3K HTx9 ltac:(vm_compute; reflexivity))
              | rewrite (HR9 3%bv); exact G3_8 | rewrite (HR9 4%bv); exact G4_8
              | rewrite (HR9 26%bv); reflexivity | lia
              | rewrite (HR9 24%bv); exact (x3_ereg R8 _ 24 _ ltac:(lia) G24_8) | apply x3_sxr; lia
              | rewrite (HR9 15%bv); exact (x3_ereg R8 _ 10 _ ltac:(lia) Ere) | lia
              | apply (x4_fksh w _ m m8 _ OK FK8 E33_8 Hlf9); vm_compute; reflexivity ].
          + set (Xs := @nil word).
            pose proof (env_world_seed H w R6 Xs) as HE.
            pose proof (ev_world_all H w _ HE) as (_ & E33 & _).
            assert (Y10 : edenot (Eseed R6 (wenv_vals w ++ Xs)) (EVar 10) = Z_to_bv 64 r) by (apply x3_ereg; [lia | exact Gr]).
            assert (HKN : know_ok asegs (Eseed R6 (wenv_vals w ++ Xs)) m6 []) by apply Forall_nil.
            pm_goX HHx4 LINV_frame OK X6 KR6 VIS6 RF6 HT6 Xs (@nil kentry) HKN
                  40%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] [false] 41%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44
                  (@nil (Z * expr)) RT_X3K.
            { split_scs. cbn [sc_denot]. rewrite Y10, x3_lit. apply x4_bne; lia. }
            intros msF7 mo7 R7 KR7 VIS7 RF7 X7 HTx7 HR7 Hlf7.
            eapply (KK msF7 mo7 _ R7 3 (sx32A r2) 0 KR7 VIS7 RF7 X7);
              [ exact (regs_tbl_restrict w [] _ R7 RT_X3K HTx7 ltac:(vm_compute; reflexivity))
              | rewrite (HR7 3%bv); exact G3_6 | rewrite (HR7 4%bv); exact G4_6
              | rewrite (HR7 26%bv); reflexivity | lia
              | rewrite (HR7 24%bv); exact (x3_ereg R6 _ 24 _ ltac:(lia) G24_6) | apply x3_sxr; lia
              | rewrite (HR7 15%bv); reflexivity | lia
              | apply (x4_fksh w _ m m6 _ OK FK6 E33 Hlf7); vm_compute; reflexivity ]. }

        assert (Y21x : forall Xs, edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 21) = Z_to_bv 64 io)
          by (intros Xs; apply x3_ereg; [lia | transitivity (PropExec.getr R1 21%bv); [exact (KEEP2 21%bv ltac:(inb)) | exact G21_1]]).
        assert (Y18x : forall Xs, edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 18) = Z_to_bv 64 (io + 2 ^ 61))
          by (intros Xs; apply x3_ereg; [lia | transitivity (PropExec.getr R1 18%bv); [exact (KEEP2 18%bv ltac:(inb)) | exact G18_1]]).
        assert (Y10x : forall Xs, edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 10) = Z_to_bv 64 (sx32A r2))
          by (intros Xs; apply x3_ereg; [lia | exact Er2]).
        destruct (Z_le_gt_dec (4 * (io + 3) + 4) (8 * ((4 * wa_n w) / 8))) as [FULL | PART].
        + set (Xs := [Z_to_bv 64 iwc; Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs3))]).
          pose proof (env_world_seed H w R2 Xs) as HE.
          pose proof (ev_world_all H w _ HE) as (_ & E33 & _ & _ & E36 & _).
          pose proof (Y21x Xs) as Y21. pose proof (Y18x Xs) as Y18. pose proof (Y10x Xs) as Y10.
          assert (Y41 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
          assert (Y42 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (c_endian c)) by (ev_xs; reflexivity).
          assert (Y43 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 43) = Z_to_bv 64 (sx32A (bytes_le_to_Z bs3)))
            by (ev_xs; apply swrap32_sx32A; lia).
          assert (YIW : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EExt false 0 2 (EVar 41)) = Z_to_bv 64 iwc)
            by (apply edenot_zext16; [exact Y41 | lia]).
          destruct (x3_ew (Eseed R2 (wenv_vals w ++ Xs)) io (wa_words w) 12 Y21 E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (YB & YA).
          assert (YEN : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EExt true 0 4 (EVar 42)) = Z_to_bv 64 (c_endian c))
            by (apply x3_endv; [exact Y42 | exact Hend]).
          assert (YAND : edenot (Eseed R2 (wenv_vals w ++ Xs))
                           (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 12)) (ELit 3)) = Z_to_bv 64 0)
            by (apply (x3_and3 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
          assert (YSRL : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 18) (ELit 3)) (ELit 62)) = Z_to_bv 64 0)
            by (apply (x3_srl _ _ (io + 2 ^ 61)); [exact Y18 | lia | lia | lia]).
          assert (HKX : know_ok asegs (Eseed R2 (wenv_vals w ++ Xs)) m2
                          [KWord (SA (EVar 33) 9048) 2 (EVar 41); KWord (SA (EVar 32) 88) 4 (EVar 42);
                           KWord (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) 1 (ELit 0);
                           KDisj (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384);
                           KDisj (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH)]).
          { apply Forall_cons.
            { eapply (kword_of_rw_cells asegs _ m2 (wa_ff w + 9048) _ 0 (C2 (Z_to_bv 64 iwc))); [exact Ciwc2 | reflexivity | reflexivity | lia
                | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
                | rewrite Y41; reflexivity]. }
            apply Forall_cons; [eapply pmk_scal_endian with (1 := OK) (2 := X2) (3 := HE); exact Y42|].
            apply Forall_cons.
            { apply (pmk_sh_wordsE H HHx4 LINV w s LB LBs m2 mo2 c S_INSTR TBL_EEF44 [] [] 0 _ EW12b (io + 3) OK X2 Hw);
                [unfold EW12b; rewrite YA; f_equal; lia | lia | exact FULL]. }
            apply Forall_cons.
            { eapply pmk_sh_ffdisj with (1 := OK) (2 := X2) (3 := HE); [exact YA | lia | lia]. }
            apply Forall_cons; [| apply Forall_nil].
            eapply pmk_sh_fshdisj with (1 := OK) (2 := X2) (3 := HE); [exact YA | lia | lia | lia]. }
          pm_goX HHx4 LINV_frame OK X2 KR2 VIS2 RF2 HT2 Xs
                [KWord (SA (EVar 33) 9048) 2 (EVar 41); KWord (SA (EVar 32) 88) 4 (EVar 42);
                 KWord (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) 1 (ELit 0);
                 KDisj (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384);
                 KDisj (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH)] HKX
                200%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] [false; true; true; true; true; true; true] 43%N S_DESC
                (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X4B.
          { split_scs. all: first
              [ tlx4_rd (wa_words w + 4 * io + 12) bs3 RD3 YB YA
              | eapply (sc_disj_lit asegs _ _ _ _ _ _ (wa_words w + 4 * io + 12) 4 (wa_ff w + 32) 8);
                  [ unfold estart; cbn [a_base a_off]; rewrite YB, u64_of_Z by lia; lia | apply elit_u; lia
                  | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; lia | apply elit_u; lia
                  | lia | lia | lia | lia | lia | lia | lia ]
              | eapply (sc_disj_lit asegs _ _ _ _ _ _ (wa_words w + 4 * io + 12) 4 (wa_ff w / 8 + 2147450884) 1);
                  [ unfold estart; cbn [a_base a_off]; rewrite YB, u64_of_Z by lia; lia | apply elit_u; lia
                  | unfold estart; cbn [a_base a_off]; rewrite (srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)); lia | apply elit_u; lia
                  | lia | lia | lia | Z.div_mod_to_equations; lia | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
              | x4_br
              | match goal with |- ?g => idtac "SCLEFT" g end ]. }
          intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
          lazymatch type of Hlf3 with log_flat _ ?lg =>
            change lg with [SE (SA (EVar 33) 32) 8 (ELit 0); SE (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) 2147450884) 1 (ELit 0)] in Hlf3, VIS3, X3 end.
          eapply (CONTB msF3 mo3 _ R3 KR3 VIS3 RF3 X3);
            [ exact (regs_tbl_restrict w [] _ R3 RT_X4B HTx3 ltac:(vm_compute; reflexivity))
            | rewrite (HR3 3%bv); exact G3_2 | rewrite (HR3 4%bv); exact G4_2
            | rewrite (HR3 24%bv); exact Y10 | rewrite (HR3 10%bv); exact Y43 | rewrite (HR3 11%bv); exact YEN
            | apply (rw_cells_mem_denot_w _ m2 [] (SA (EVar 33) 32) 8 (ELit 0) _ (wa_ff w + 32) (C8 (Z_to_bv 64 0)));
                [exact Hlf3 | apply Forall_nil | rewrite (estart_var _ 33 32 _ E33) by lia; lia | exact WR32 | reflexivity | exact I
                | reflexivity]
            | apply (x4_fksh w _ m m2 _ OK FK2 E33 Hlf3); vm_compute; reflexivity ].
        + assert (Hp : 4 * (io + 3) = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4) by (Z.div_mod_to_equations; lia).
          set (Xs := [Z_to_bv 64 iwc; Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs3))]).
          pose proof (env_world_seed H w R2 Xs) as HE.
          pose proof (ev_world_all H w _ HE) as (_ & E33 & _ & _ & E36 & _).
          pose proof (Y21x Xs) as Y21. pose proof (Y18x Xs) as Y18. pose proof (Y10x Xs) as Y10.
          assert (Y41 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
          assert (Y42 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (c_endian c)) by (ev_xs; reflexivity).
          assert (Y43 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 43) = Z_to_bv 64 (sx32A (bytes_le_to_Z bs3)))
            by (ev_xs; apply swrap32_sx32A; lia).
          assert (YIW : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EExt false 0 2 (EVar 41)) = Z_to_bv 64 iwc)
            by (apply edenot_zext16; [exact Y41 | lia]).
          destruct (x3_ew (Eseed R2 (wenv_vals w ++ Xs)) io (wa_words w) 12 Y21 E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (YB & YA).
          assert (YEN : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EExt true 0 4 (EVar 42)) = Z_to_bv 64 (c_endian c))
            by (apply x3_endv; [exact Y42 | exact Hend]).
          assert (YAND : edenot (Eseed R2 (wenv_vals w ++ Xs))
                           (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 12)) (ELit 3)) = Z_to_bv 64 0)
            by (apply (x3_and3 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
          assert (Y7 : edenot (Eseed R2 (wenv_vals w ++ Xs))
                         (EAlu ALU_ADD (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 12)) (ELit 7)) (ELit 3))
                       = Z_to_bv 64 3)
            by (apply (x3_and7 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
          assert (YSRL : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 18) (ELit 3)) (ELit 62)) = Z_to_bv 64 0)
            by (apply (x3_srl _ _ (io + 2 ^ 61)); [exact Y18 | lia | lia | lia]).
          assert (HKX : know_ok asegs (Eseed R2 (wenv_vals w ++ Xs)) m2
                          [KWord (SA (EVar 33) 9048) 2 (EVar 41); KWord (SA (EVar 32) 88) 4 (EVar 42);
                           KWord (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) 1 (ELit 4);
                           KDisj (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384);
                           KDisj (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH)]).
          { apply Forall_cons.
            { eapply (kword_of_rw_cells asegs _ m2 (wa_ff w + 9048) _ 0 (C2 (Z_to_bv 64 iwc))); [exact Ciwc2 | reflexivity | reflexivity | lia
                | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
                | rewrite Y41; reflexivity]. }
            apply Forall_cons; [eapply pmk_scal_endian with (1 := OK) (2 := X2) (3 := HE); exact Y42|].
            apply Forall_cons.
            { apply (pmk_sh_wordsE_part H HHx4 LINV w s LB LBs m2 mo2 c S_INSTR TBL_EEF44 [] [] 0 _ EW12b (io + 3) OK X2 Hw);
                [unfold EW12b; rewrite YA; f_equal; lia | exact (proj1 Hp) | exact (proj2 Hp)]. }
            apply Forall_cons.
            { eapply pmk_sh_ffdisj with (1 := OK) (2 := X2) (3 := HE); [exact YA | lia | lia]. }
            apply Forall_cons; [| apply Forall_nil].
            eapply pmk_sh_fshdisj with (1 := OK) (2 := X2) (3 := HE); [exact YA | lia | lia | lia]. }
          pm_goX HHx4 LINV_frame OK X2 KR2 VIS2 RF2 HT2 Xs
                [KWord (SA (EVar 33) 9048) 2 (EVar 41); KWord (SA (EVar 32) 88) 4 (EVar 42);
                 KWord (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) 1 (ELit 4);
                 KDisj (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_FF) 0) (ELit 16384);
                 KDisj (SA (EAlu ALU_SRL EW12b (ELit 3)) SHBASE) (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH)] HKX
                200%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] [false; true; true; true; true; true; true; false] 43%N S_DESC
                (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X4B.
          { split_scs. all: first
              [ tlx4_rd (wa_words w + 4 * io + 12) bs3 RD3 YB YA
              | eapply (sc_disj_lit asegs _ _ _ _ _ _ (wa_words w + 4 * io + 12) 4 (wa_ff w + 32) 8);
                  [ unfold estart; cbn [a_base a_off]; rewrite YB, u64_of_Z by lia; lia | apply elit_u; lia
                  | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; lia | apply elit_u; lia
                  | lia | lia | lia | lia | lia | lia | lia ]
              | eapply (sc_disj_lit asegs _ _ _ _ _ _ (wa_words w + 4 * io + 12) 4 (wa_ff w / 8 + 2147450884) 1);
                  [ unfold estart; cbn [a_base a_off]; rewrite YB, u64_of_Z by lia; lia | apply elit_u; lia
                  | unfold estart; cbn [a_base a_off]; rewrite (srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)); lia | apply elit_u; lia
                  | lia | lia | lia | Z.div_mod_to_equations; lia | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
              | x4_br
              | match goal with |- ?g => idtac "SCLEFT" g end ]. }
          intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
          lazymatch type of Hlf3 with log_flat _ ?lg =>
            change lg with [SE (SA (EVar 33) 32) 8 (ELit 0); SE (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) 2147450884) 1 (ELit 0)] in Hlf3, VIS3, X3 end.
          eapply (CONTB msF3 mo3 _ R3 KR3 VIS3 RF3 X3);
            [ exact (regs_tbl_restrict w [] _ R3 RT_X4B HTx3 ltac:(vm_compute; reflexivity))
            | rewrite (HR3 3%bv); exact G3_2 | rewrite (HR3 4%bv); exact G4_2
            | rewrite (HR3 24%bv); exact Y10 | rewrite (HR3 10%bv); exact Y43 | rewrite (HR3 11%bv); exact YEN
            | apply (rw_cells_mem_denot_w _ m2 [] (SA (EVar 33) 32) 8 (ELit 0) _ (wa_ff w + 32) (C8 (Z_to_bv 64 0)));
                [exact Hlf3 | apply Forall_nil | rewrite (estart_var _ 33 32 _ E33) by lia; lia | exact WR32 | reflexivity | exact I
                | reflexivity]
            | apply (x4_fksh w _ m m2 _ OK FK2 E33 Hlf3); vm_compute; reflexivity ]. }

    assert (Y21 : forall Xs, edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 21) = Z_to_bv 64 io)
      by (intros Xs; apply x3_ereg; [lia | exact G21]).
    destruct (Z_le_gt_dec (4 * (io + 2) + 4) (8 * ((4 * wa_n w) / 8))) as [FULL | PART].
    - set (Xs := [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs2))]).
      pose proof (env_world_seed H w R Xs) as HE.
      pose proof (ev_world_all H w _ HE) as (_ & _ & _ & _ & E36 & _).
      pose proof (Y21 Xs) as Y21x.
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 (c_endian c)) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (sx32A (bytes_le_to_Z bs2)))
        by (ev_xs; apply swrap32_sx32A; lia).
      destruct (x3_ew (Eseed R (wenv_vals w ++ Xs)) io (wa_words w) 8 Y21x E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (YB & YA).
      assert (YEN : edenot (Eseed R (wenv_vals w ++ Xs)) (EExt true 0 4 (EVar 41)) = Z_to_bv 64 (c_endian c))
        by (apply x3_endv; [exact Y41 | exact Hend]).
      assert (YAND : edenot (Eseed R (wenv_vals w ++ Xs))
                       (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 8)) (ELit 3)) = Z_to_bv 64 0)
        by (apply (x3_and3 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
      assert (YSRL : edenot (Eseed R (wenv_vals w ++ Xs))
                       (EAlu ALU_SRL (EAlu ALU_ADD (EVar 21) (ELit 2305843009213693954)) (ELit 62)) = Z_to_bv 64 0)
        by (apply (x3_srl _ _ io); [exact Y21x | lia | lia | lia]).
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m
                      [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW8 (ELit 3)) SHBASE) 1 (ELit 0)]).
      { apply Forall_cons; [eapply pmk_scal_endian with (1 := OK) (2 := X0) (3 := HE); exact Y41|].
        apply Forall_cons; [| apply Forall_nil].
        apply (pmk_sh_wordsE H HHx4 LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] [] 0 _ EW8 (io + 2) OK X0 Hw);
          [unfold EW8; rewrite YA; f_equal; lia | lia | exact FULL]. }
      pm_goX HHx4 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW8 (ELit 3)) SHBASE) 1 (ELit 0)] HKX
            200%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] [true; true; true; true; true; true] 42%N S_INSTR
            (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X4A.
      { split_scs. all: first [ tlx4_rd (wa_words w + 4 * io + 8) bs2 RD2 YB YA | x4_br
                              | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      eapply (CONTA msF1 mo1 R1 KR1 VIS1 RF1 X1);
        [ exact (regs_tbl_restrict w [] _ R1 RT_X4A HTx1 ltac:(vm_compute; reflexivity))
        | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rewrite (HR1 21%bv); exact Y21x
        | rewrite (HR1 18%bv); exact (ev_add _ 21 io (2 ^ 61) Y21x ltac:(lia) ltac:(lia))
        | rewrite (HR1 10%bv); exact Y42 | rewrite (HR1 11%bv); exact YEN ].
    - assert (Hp : 4 * (io + 2) = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4) by (Z.div_mod_to_equations; lia).
      set (Xs := [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs2))]).
      pose proof (env_world_seed H w R Xs) as HE.
      pose proof (ev_world_all H w _ HE) as (_ & _ & _ & _ & E36 & _).
      pose proof (Y21 Xs) as Y21x.
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 (c_endian c)) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (sx32A (bytes_le_to_Z bs2)))
        by (ev_xs; apply swrap32_sx32A; lia).
      destruct (x3_ew (Eseed R (wenv_vals w ++ Xs)) io (wa_words w) 8 Y21x E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (YB & YA).
      assert (YEN : edenot (Eseed R (wenv_vals w ++ Xs)) (EExt true 0 4 (EVar 41)) = Z_to_bv 64 (c_endian c))
        by (apply x3_endv; [exact Y41 | exact Hend]).
      assert (YAND : edenot (Eseed R (wenv_vals w ++ Xs))
                       (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 8)) (ELit 3)) = Z_to_bv 64 0)
        by (apply (x3_and3 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
      assert (Y7 : edenot (Eseed R (wenv_vals w ++ Xs))
                     (EAlu ALU_ADD (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 8)) (ELit 7)) (ELit 3))
                   = Z_to_bv 64 3)
        by (apply (x3_and7 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
      assert (YSRL : edenot (Eseed R (wenv_vals w ++ Xs))
                       (EAlu ALU_SRL (EAlu ALU_ADD (EVar 21) (ELit 2305843009213693954)) (ELit 62)) = Z_to_bv 64 0)
        by (apply (x3_srl _ _ io); [exact Y21x | lia | lia | lia]).
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m
                      [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW8 (ELit 3)) SHBASE) 1 (ELit 4)]).
      { apply Forall_cons; [eapply pmk_scal_endian with (1 := OK) (2 := X0) (3 := HE); exact Y41|].
        apply Forall_cons; [| apply Forall_nil].
        apply (pmk_sh_wordsE_part H HHx4 LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] [] 0 _ EW8 (io + 2) OK X0 Hw);
          [unfold EW8; rewrite YA; f_equal; lia | exact (proj1 Hp) | exact (proj2 Hp)]. }
      pm_goX HHx4 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW8 (ELit 3)) SHBASE) 1 (ELit 4)] HKX
            200%nat [0xf5128; AT_FIXWORD; AT_LOOKUP_OPERAND; AT_FPENC] [true; true; true; true; true; true; false] 42%N S_INSTR
            (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X4A.
      { split_scs. all: first [ tlx4_rd (wa_words w + 4 * io + 8) bs2 RD2 YB YA | x4_br
                              | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      eapply (CONTA msF1 mo1 R1 KR1 VIS1 RF1 X1);
        [ exact (regs_tbl_restrict w [] _ R1 RT_X4A HTx1 ltac:(vm_compute; reflexivity))
        | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rewrite (HR1 21%bv); exact Y21x
        | rewrite (HR1 18%bv); exact (ev_add _ 21 io (2 ^ 61) Y21x ltac:(lia) ltac:(lia))
        | rewrite (HR1 10%bv); exact Y42 | rewrite (HR1 11%bv); exact YEN ].
  Qed.
End TX4.
