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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmHex LbB_PmDS LbB_PmExit2 LbB_PmLH LbB_PmOL LbB_TablStmt LbB_PmLeaf LbB_PmLeafW LbB_PmWords LbB_PmU2K LbB_PmWX1 LbB_PmWXK.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord.
Definition X2_FFX : list (Z * Z) := [(9040, 10)].

Definition RT_3054 : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (19%bv, WADD WV_FF 9040);
   (20%bv, SH_FF);
   (22%bv, WADD WV_FF 10112);
   (23%bv, EVar WV_P);
   (24%bv, WADD WV_FF 7984);
   (25%bv, WADD WV_P 48);
   (26%bv, WADD WV_P 216);
   (27%bv, EVar WV_FF)].
Definition RT_X2G : list (reg * expr) := (1%bv, ELit 0xf4e04) :: RT_3054.

Definition RT_2978 : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (10%bv, WADD WV_FF 9136);
   (13%bv, ELit SHBASE);
   (20%bv, SH_FF);
   (22%bv, WADD WV_FF 10112);
   (23%bv, EVar WV_P);
   (24%bv, WADD WV_FF 7984);
   (25%bv, WADD WV_P 264);
   (26%bv, WADD WV_FF 112);
   (27%bv, EVar WV_FF)].

Section TX2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHx2 : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTLbAPmWX2_0 : list kentry := [KWord (SA (EVar 33) 10112) 8 (EVar 41); KWord (SA (EVar 33) 9136) 2 (EVar 42); KWord (SA (EVar 32) 72) 8 (EVar 43)].
  Lemma tl_x2 : forall (w : pmwA H) s LB LBs m mo (c : pmc) msF R F fc (io iwc op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf453c) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_255C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 10112) [C8 (Z_to_bv 64 io)] -> rw_cells asegs m (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)] ->
    rw_cells asegs m (wa_ff w + 9050) [C2 (Z_to_bv 64 op)] ->
    0 <= io -> 0 <= iwc < 2 ^ 16 -> 0 <= op < 2 ^ 16 -> io + iwc <= c_widx c ->
    c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1) ->

    (forall msF1 mo1 R1,
       as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf48a4) fc None m (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m mo1 c S_INSTR TBL_EEF44 [] ->
       regs_tbl w R1 RT_2978 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 21%bv = Z_to_bv 64 io -> c_widx c <> io + iwc ->
       as_SR H Q (mkCfg msF1 mo1)) ->

    (forall msF1 mo1 m1 R1 (bg : bool),
       as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf4e04) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 c S_INSTR TBL_EEF44 [] ->
       regs_tbl w R1 RT_3054 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 21%bv = Z_to_bv 64 io -> PropExec.getr R1 18%bv = Z_to_bv 64 op ->
       PropExec.getr R1 10%bv = Z_to_bv 64 (if bg then 1 else 0) -> (bg = true -> tg_generates_type op = true) ->
       c_widx c = io + iwc -> ffkeepX w X2_FFX m m1 -> rw_cells asegs m1 (wa_ff w + 9048) [C2 (Z_to_bv 64 iwc)] ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc io iwc op Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 Cio Ciwc Cop Hio Hiwc Hop Hexit [Hend Hend01] KD K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND. pose proof (wk_n H w OK) as WN.
    pose proof (wk_words H w OK) as WW.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).

    assert (KC8 : forall Xs k v (e : expr), let E := Eseed R (wenv_vals w ++ Xs) in
              rw_cells asegs m (wa_ff w + k) [C8 (Z_to_bv 64 v)] -> 0 <= k -> k + 8 <= 16384 ->
              edenot E e = Z_to_bv 64 v -> kentry_ok ASEGS E m (KWord (SA (EVar 33) k) 8 e)).
    { intros Xs k v e. lazy zeta. intros C Hk Hk2 He. pose proof (ev_world_all H w _ (env_world_seed H w R Xs)) as (_ & E33 & _).
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + k) _ 0 (C8 (Z_to_bv 64 v))); [exact C | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
        | rewrite He; reflexivity]. }
    assert (KC2 : forall Xs k v (e : expr), let E := Eseed R (wenv_vals w ++ Xs) in
              rw_cells asegs m (wa_ff w + k) [C2 (Z_to_bv 64 v)] -> 0 <= k -> k + 2 <= 16384 ->
              edenot E e = Z_to_bv 64 v -> kentry_ok ASEGS E m (KWord (SA (EVar 33) k) 2 e)).
    { intros Xs k v e. lazy zeta. intros C Hk Hk2 He. pose proof (ev_world_all H w _ (env_world_seed H w R Xs)) as (_ & E33 & _).
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + k) _ 0 (C2 (Z_to_bv 64 v))); [exact C | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite E33, u64_of_Z by lia; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia
        | rewrite He; reflexivity]. }
    assert (KWI : forall Xs (e : expr), let E := Eseed R (wenv_vals w ++ Xs) in
              edenot E e = Z_to_bv 64 (c_widx c) -> kentry_ok ASEGS E m (KWord (SA (EVar 32) 72) 8 e)).
    { intros Xs e. lazy zeta. intros He. pose proof (ev_world_all H w _ (env_world_seed H w R Xs)) as (E32 & _).
      apply (kword_of_fld _ m (wa_p w + O_WIDX) 8 (c_widx c)); [exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | | | | exact He];
        [unfold estart; cbn [a_base a_off]; rewrite E32, u64_of_Z by lia; unfold O_WIDX; lia | unfold O_WIDX, PARSER_SIZE in *; lia
        | unfold O_WIDX, PARSER_SIZE in *; cbn; lia]. }
    assert (KFL : forall Xs, let E := Eseed R (wenv_vals w ++ Xs) in kentry_ok ASEGS E m (KWord (SA (EVar 32) 92) 1 (ELit (c_reqconv c)))).
    { intros Xs. lazy zeta. pose proof (ev_world_all H w _ (env_world_seed H w R Xs)) as (E32 & _).
      apply (kword_of_fld _ m (wa_p w + O_FLAGS) 1 (c_reqconv c)); [exact (xa_flags _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | | | |];
        [unfold estart; cbn [a_base a_off]; rewrite E32, u64_of_Z by lia; unfold O_FLAGS; lia | unfold O_FLAGS, PARSER_SIZE in *; lia
        | unfold O_FLAGS, PARSER_SIZE in *; cbn; lia | cbn [edenot]; rewrite <- Hend; destruct Hend01 as [-> | ->]; reflexivity]. }
    assert (EVALS : forall Xs, let E := Eseed R (wenv_vals w ++ Xs) in
              edenot E (EVar 41) = Z_to_bv 64 io -> edenot E (EVar 42) = Z_to_bv 64 iwc -> edenot E (EVar 43) = Z_to_bv 64 op ->
              edenot E (EExt false 0 2 (EVar 42)) = Z_to_bv 64 iwc
              /\ edenot E (EAlu ALU_ADD (EVar 41) (EExt false 0 2 (EVar 42))) = Z_to_bv 64 (io + iwc)
              /\ edenot E (EExt false 0 2 (EVar 43)) = Z_to_bv 64 op
              /\ edenot E (EAlu ALU_ADD (EVar 36) (EMd M_MUL (ELit 4) (EVar 41))) = Z_to_bv 64 (wa_words w + 4 * io)).
    { intros Xs. lazy zeta. intros H41 H42 H43. pose proof (ev_world_all H w _ (env_world_seed H w R Xs)) as (_ & _ & _ & _ & E36 & _).
      assert (Z42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EExt false 0 2 (EVar 42)) = Z_to_bv 64 iwc) by (apply edenot_zext16; [exact H42 | lia]).
      split; [exact Z42|]. split; [apply ev_add2; [exact H41 | exact Z42 | lia | lia | lia]|].
      split; [apply edenot_zext16; [exact H43 | lia]|]. apply ev_add2; [exact E36 | apply ev_mul4_0; [exact H41 | lia] | lia | lia | lia]. }
    destruct (Z.eq_dec (c_widx c) (io + iwc)) as [EQW | NEW].
    2: {
      set (Xs := [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 (c_widx c)]).
      pose proof (env_world_seed H w R Xs) as HE.
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 io) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
      assert (Y43 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 43) = Z_to_bv 64 (c_widx c)) by (ev_xs; reflexivity).
      assert (Z42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EExt false 0 2 (EVar 42)) = Z_to_bv 64 iwc) by (apply edenot_zext16; [exact Y42 | lia]).
      assert (YIO : edenot (Eseed R (wenv_vals w ++ Xs)) (EAlu ALU_ADD (EVar 41) (EExt false 0 2 (EVar 42))) = Z_to_bv 64 (io + iwc))
        by (apply ev_add2; [exact Y41 | exact Z42 | lia | lia | lia]).
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m
                      HTLbAPmWX2_0).
      { apply Forall_cons; [apply (KC8 Xs 10112 io); [exact Cio | lia | lia | exact Y41]|].
        apply Forall_cons; [apply (KC2 Xs 9136 iwc); [exact Ciwc | lia | lia | exact Y42]|].
        apply Forall_cons; [apply KWI; exact Y43 | apply Forall_nil]. }
      pm_goX HHx2 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            HTLbAPmWX2_0 HKX
            200%nat [AT_GENERATES_TYPE; 0xf48a4] [true] 44%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_2978.
      { split_scs. all: first [ cbn [sc_denot]; rewrite ?YIO, ?Y43, ?ev_lit0; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia
                              | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      eapply (KD msF1 mo1 R1 KR1 VIS1 RF1 X1);
        [exact (regs_tbl_restrict w [] _ R1 RT_2978 HTx1 ltac:(vm_compute; reflexivity))
        | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rewrite (HR1 21%bv); exact Y41 | exact NEW]. }

    pose proof (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (_ & _ & _ & _ & Hb2 & F20 & _). unfold O_V2 in F20.
    assert (Rb2 : 0 <= t3a (c_v2 c) < 2 ^ 64) by (destruct Hb2 as [[Bz Cz]|(Bp & B16 & Cp & Bq4 & _)]; lia).

    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (W0 & W1 & W2). change (fsz PM_FCLASS) with 16384 in W2.
    assert (WR424 : wr_at asegs m (wa_ff w + 9048) 2).
    { split; [lia|]. split; [lia|]. intros i Hi. replace (wa_ff w + 9048 + i) with (wa_ff w + (9048 + i)) by lia. apply W2. unfold AFS_HDR. lia. }
    assert (CONT : forall msF1 mo1 R1 (LOG' : list sentry) Xs,
              let E := Eseed R (wenv_vals w ++ Xs) in
              let LOG := SE (SA (EVar 33) 9048) 2 (EExt false 0 2 (EVar 42)) :: LOG' in
              edenot E (EVar 42) = Z_to_bv 64 iwc ->
              as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_GENERATES_TYPE) fc None (mem_denot E m LOG) (seg_rom asegs) ->
              rfull R1 -> PMXA H LINV w s LB LBs (mem_denot E m LOG) mo1 c S_INSTR TBL_EEF44 [] ->
              log_flat E LOG -> forallb (sym_inside [(EVar WV_FF, 9040, 9050)]) LOG = true ->
              regs_tbl w R1 RT_X2G -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
              PropExec.getr R1 21%bv = Z_to_bv 64 io -> PropExec.getr R1 18%bv = Z_to_bv 64 op -> PropExec.getr R1 10%bv = Z_to_bv 64 op ->
              as_SR H Q (mkCfg msF1 mo1)).
    { intros msF1 mo1 R1 LOG' Xs E LOG Y42 KR1 VIS1 RF1 X1 Hlf1 Hins HT1 G3_1 G4_1 G21_1 G18_1 G10_1.
      pose proof (ev_world_all H w _ (env_world_seed H w R Xs)) as (_ & E33 & _).
      assert (C424 : rw_cells asegs (mem_denot E m LOG) (wa_ff w + 9048) [C2 (Z_to_bv 64 iwc)]).
      { subst LOG. apply (rw_cells_mem_denot_w _ m [] (SA (EVar 33) 9048) 2 _ LOG' (wa_ff w + 9048) (C2 (Z_to_bv 64 iwc)));
          [exact Hlf1 | apply Forall_nil | subst E; rewrite (estart_var _ 33 9048 _ E33); lia | exact WR424 | reflexivity | exact I
          | subst E; rewrite (edenot_zext16 _ 42 iwc Y42 ltac:(lia)); reflexivity]. }
      assert (FK1 : ffkeepX w X2_FFX m (mem_denot E m LOG)).
      { pose proof (munch_sym _ m _ [(EVar WV_FF, 9040, 9050)] Hlf1 Hins) as MU.
        cbn [num_wins map] in MU. unfold WV_FF in MU. subst E. rewrite E33, u64_of_Z in MU by lia.
        apply (ffkeepX_munch w _ _ _ _ MU (wmono_mem_denot _ _ _)).
        apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right. apply Exists_cons_hd. cbn [fst snd]. lia. }
      eapply (pm_leafW H HHx2 LINV LINV_frame AT_GENERATES_TYPE 0 _ _ _ (tla_generates_type HTL) op [] w s LB LBs _ mo1 c S_INSTR TBL_EEF44 [] [] 0 msF1 R1 F fc 0xf4e04 Q []);
        [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | rtf HT1 | rtf HT1 | reflexivity | lia | lia | reflexivity | reflexivity
        | cbn beta iota; split; [lia | exact G10_1]
        | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
        | intros r0 r1 m9 k9 n9 a9 _ Hin9; destruct Hin9
        | ].
      intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 (bg & Ebg & Pbg).
      eapply (K msF2 mo2 m2 R2 bg KR2 VIS2 RF2 X2).
      - exact (regs_tbl_restrict w [] _ R2 RT_3054 (regs_tbl_sub w _ _ _ RT_3054 (regs_keep w [] _ _ RT_X2G HT1 KEEP2) ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity)).
      - rewrite (KEEP2 3%bv ltac:(inb)). exact G3_1. - rewrite (KEEP2 4%bv ltac:(inb)). exact G4_1.
      - rewrite (KEEP2 21%bv ltac:(inb)). exact G21_1. - rewrite (KEEP2 18%bv ltac:(inb)). exact G18_1.
      - exact Ebg. - exact Pbg. - exact EQW.
      - eapply (ffkeepX_trans w _ [] _ _ _ _ FK1); [| apply incl_refl | intros x9 Hx9; destruct Hx9].
        apply ffkeepX_nil. apply (ffkeep_munch w _ _ _ MU2 WM2). apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
      - apply (ffkeep_munch w _ _ _ MU2 WM2); [apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil] | lia | cbn; lia | exact C424]. }
    destruct (Z.eq_dec (c_reqconv c) 0) as [RC0 | RC1].
    -
      set (Xs := [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 op]).
      pose proof (env_world_seed H w R Xs) as HE.
      pose proof (ev_world_all H w _ HE) as (_ & _ & _ & _ & E36 & _).
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 io) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
      assert (Y43 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 43) = Z_to_bv 64 op) by (ev_xs; reflexivity).
      destruct (EVALS Xs Y41 Y42 Y43) as (Z42 & YIO & Z43 & YSRC).
      assert (Y41S : edenot (Eseed R (wenv_vals w ++ Xs)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 41) (ELit 2305843009213693952)) (ELit 62)) = Z_to_bv 64 0).
      { cbn [edenot]. change (ev (Eseed R (wenv_vals w ++ Xs)) 41) with (edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41)). rewrite Y41.
        rewrite (w_add io 2305843009213693952) by lia. rewrite w_srl by lia. f_equal. apply Z.div_small. lia. }
      assert (WNZ : wa_words w = 0 /\ io = 0 \/ 0 < wa_words w).
      { destruct WW as [[W0' N0'] | (pw & kk & _ & _ & Wp & _)]; [left; split; [exact W0' | lia] | right; exact Wp]. }
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m
                      [KWord (SA (EVar 33) 10112) 8 (EVar 41); KWord (SA (EVar 33) 9136) 2 (EVar 42);
                       KWord (SA (EVar 32) 72) 8 (EAlu ALU_ADD (EVar 41) (EExt false 0 2 (EVar 42))); KWord (SA (EVar 32) 92) 1 (ELit 0);
                       KWord (SA (EVar 33) 9050) 2 (EVar 43)]).
      { apply Forall_cons; [apply (KC8 Xs 10112 io); [exact Cio | lia | lia | exact Y41]|].
        apply Forall_cons; [apply (KC2 Xs 9136 iwc); [exact Ciwc | lia | lia | exact Y42]|].
        apply Forall_cons; [apply KWI; rewrite EQW; exact YIO|].
        apply Forall_cons; [rewrite <- RC0; apply KFL|].
        apply Forall_cons; [apply (KC2 Xs 9050 op); [exact Cop | lia | lia | exact Y43] | apply Forall_nil]. }
      pm_goX HHx2 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            [KWord (SA (EVar 33) 10112) 8 (EVar 41); KWord (SA (EVar 33) 9136) 2 (EVar 42);
             KWord (SA (EVar 32) 72) 8 (EAlu ALU_ADD (EVar 41) (EExt false 0 2 (EVar 42))); KWord (SA (EVar 32) 92) 1 (ELit 0);
             KWord (SA (EVar 33) 9050) 2 (EVar 43)] HKX
            200%nat [AT_GENERATES_TYPE; 0xf48a4] [true; true; true] 44%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X2G.
      { split_scs.
        - cbn [sc_denot]. rewrite YSRC, E36. rewrite br_geu by lia. apply Bool.negb_true_iff, Z.ltb_ge. lia.
        - cbn [sc_denot]. rewrite Y41S, ev_lit0. rewrite br_eq by lia. reflexivity.
        - cbn [sc_denot].
          assert (EA : forall E0 a b, edenot E0 (EAlu ALU_SLTU a b) = alu64 ALU_SLTU (edenot E0 a) (edenot E0 b)) by reflexivity.
          rewrite !EA, YSRC, E36, !ev_lit0. rewrite !w_sltu by lia. rewrite br_ne by (destruct (_ <? _); lia).
          destruct WNZ as [[W0' I0] | WP].
          + rewrite W0', I0. reflexivity.
          + replace (0 <? wa_words w) with true by (symmetry; apply Z.ltb_lt; lia).
            replace (wa_words w + 4 * io <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      eapply (CONT msF1 mo1 R1 _ Xs Y42 KR1 VIS1 RF1 X1 Hlf1);
        [vm_compute; reflexivity
        | exact (regs_tbl_restrict w [] _ R1 RT_X2G HTx1 ltac:(vm_compute; reflexivity))
        | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0
        | rewrite (HR1 21%bv); exact Y41 | rewrite (HR1 18%bv); exact Z43 | rewrite (HR1 10%bv); exact Z43].
    -
      assert (RC : c_reqconv c = 1) by lia.
      set (Xs := [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 op; Z_to_bv 64 (t3a (c_v2 c))]).
      pose proof (env_world_seed H w R Xs) as HE.
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 io) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 iwc) by (ev_xs; reflexivity).
      assert (Y43 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 43) = Z_to_bv 64 op) by (ev_xs; reflexivity).
      destruct (EVALS Xs Y41 Y42 Y43) as (Z42 & YIO & Z43 & YSRC).
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m
                      [KWord (SA (EVar 33) 10112) 8 (EVar 41); KWord (SA (EVar 33) 9136) 2 (EVar 42);
                       KWord (SA (EVar 32) 72) 8 (EAlu ALU_ADD (EVar 41) (EExt false 0 2 (EVar 42))); KWord (SA (EVar 32) 92) 1 (ELit 1);
                       KWord (SA (EVar 33) 9050) 2 (EVar 43)]).
      { apply Forall_cons; [apply (KC8 Xs 10112 io); [exact Cio | lia | lia | exact Y41]|].
        apply Forall_cons; [apply (KC2 Xs 9136 iwc); [exact Ciwc | lia | lia | exact Y42]|].
        apply Forall_cons; [apply KWI; rewrite EQW; exact YIO|].
        apply Forall_cons; [rewrite <- RC; apply KFL|].
        apply Forall_cons; [apply (KC2 Xs 9050 op); [exact Cop | lia | lia | exact Y43] | apply Forall_nil]. }
      pm_goX HHx2 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            [KWord (SA (EVar 33) 10112) 8 (EVar 41); KWord (SA (EVar 33) 9136) 2 (EVar 42);
             KWord (SA (EVar 32) 72) 8 (EAlu ALU_ADD (EVar 41) (EExt false 0 2 (EVar 42))); KWord (SA (EVar 32) 92) 1 (ELit 1);
             KWord (SA (EVar 33) 9050) 2 (EVar 43)] HKX
            200%nat [AT_GENERATES_TYPE; 0xf48a4] (@nil bool) 44%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X2G.
      { split_scs. all: first
          [ eapply (sc_rd_fld8 _ _ _ _ _ _ F20); [rewrite (adenot_of_estart _ _ (wa_p w + 240)); [reflexivity | rewrite (estart_p H w _ _ OK HE); lia | lia] | ev_xs; reflexivity]
          | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      eapply (CONT msF1 mo1 R1 _ Xs Y42 KR1 VIS1 RF1 X1 Hlf1);
        [vm_compute; reflexivity
        | exact (regs_tbl_restrict w [] _ R1 RT_X2G HTx1 ltac:(vm_compute; reflexivity))
        | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0
        | rewrite (HR1 21%bv); exact Y41 | rewrite (HR1 18%bv); exact Z43 | rewrite (HR1 10%bv); exact Z43].
  Qed.
End TX2.
