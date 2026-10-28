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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVup LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmHex LbB_PmDS LbB_PmLH LbB_PmOL LbB_TablStmt LbB_PmLeaf LbB_PmLeafW LbB_PmVS LbB_ContStmt LbB_PmWKit LbB_PmWG LbB_PmWP2b LbB_PmWords LbB_PmU2K LbB_PmWT1 LbB_PmWT2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmOLX LbB_BiW32S.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition S_WORD : list nat := (2 :: 1 :: S_OPER)%nat.

Lemma regs_keepV {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R R' RT KL,
  regs_tblX w X R RT -> (forall r, In r KL -> PropExec.getr R' r = PropExec.getr R r) ->
  forallb (fun re => existsb (fun x => bv_eqb (fst re) x) KL) RT = true -> regs_tblX w X R' RT.
Proof.
  intros w X R R' RT KL HT HK HB. unfold regs_tblX in *. apply Forall_forall. intros [r e] Hin.
  pose proof (proj1 (forallb_forall _ _) HB (r, e) Hin) as Hk. cbn [fst snd] in *.
  rewrite (HK r (LbB_Call.inb_In r KL Hk)). exact (proj1 (Forall_forall _ _) HT (r, e) Hin).
Qed.

Lemma bud_set_v2 : forall n c b' xs' cap', pm_bud n c -> 0 <= 4 * cap' <= 2 ^ 20 -> pm_bud n (set_v2A c (b', xs', cap')).
Proof.
  intros n c b' xs' cap' B Hc. unfold pm_bud, set_v2A in *. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3c snd] in *. tauto.
Qed.
Lemma bsz_set_v2 : forall c b' xs' cap',
  (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> 4 * cap' <= 2 ^ 40 ->
  forall q k, In (q, k) (c_blocks (set_v2A c (b', xs', cap'))) -> k <= 2 ^ 40.
Proof.
  intros c b' xs' cap' Hb Hc q k Hin. rewrite cblocks_set_v2, !in_app_iff in Hin.
  destruct Hin as [Hin | [Hin | Hin]].
  - apply (Hb q k). rewrite (cblocks_v2 c), !in_app_iff. left. exact Hin.
  - destruct (b' =? 0); [destruct Hin | destruct Hin as [E | []]; injection E as E1 E2; lia].
  - apply (Hb q k). rewrite (cblocks_v2 c), !in_app_iff. right. right. exact Hin.
Qed.

Definition RT_FXE : list (reg * expr) :=
  [(1%bv, ELit 0xf1e10); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF);
   (24%bv, WADD WV_FF 7984); (25%bv, ELit SHBASE); (26%bv, WADD WV_FF 112); (27%bv, ELit 18446744073709551608)].
Definition RT_LOOPW : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF); (24%bv, WADD WV_FF 7984);
   (25%bv, ELit SHBASE); (26%bv, WADD WV_FF 112); (27%bv, ELit 18446744073709551608)].
Definition RT_V4E : list (reg * expr) :=
  [(1%bv, ELit 0xf1e20); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (10%bv, WADD WV_FF 64);
   (11%bv, WADD WV_FF 96); (20%bv, SH_FF); (24%bv, WADD WV_FF 7984); (25%bv, ELit SHBASE); (26%bv, WADD WV_FF 112);
   (27%bv, ELit 18446744073709551608)].

Section TLC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.
  Hypothesis HFC : biw32_stmt H.
  Hypothesis HFW : fixword_stmtA.

  Lemma HHm3 : asan_rt_hyps H.
  Proof. exact (rt_bp_base H HHbp). Qed.



  Ltac tlw_sc w i E21 E23 RD0 :=
    first
      [ eapply (sc_rd_w4s _ _ _ (wa_words w + 4 * i) _ _);
          [ apply (adenot_of_estart _ _ (wa_words w + 4 * i)); [rewrite (estart_var _ 23 0 _ E23); lia | lia] | exact RD0 | ev_xs; reflexivity ]
      | eapply (sc_flat_lit asegs _ _ _ _ (wa_words w + 4 * i) 4); [rewrite (estart_var _ 23 0 _ E23); lia | apply elit_u; lia | lia | lia | lia]
      | eapply (sc_flat_lit asegs _ _ _ _ ((wa_words w + 4 * i) / 8 + SHBASE) 1);
          [apply (estart_sh _ (EVar 21) (wa_words w + 4 * i) E21); lia | apply elit_u; lia
          | unfold SHBASE; Z.div_mod_to_equations; lia | lia | unfold SHBASE; Z.div_mod_to_equations; lia]
      | match goal with |- ?g => idtac "SCLEFT" g end ].



  Lemma tl_wA : forall (spal : Z) (w : pmwA H) s LB LBs m mo (cj : pmc) msF R F fc (i en : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo cj S_WORD TBL_EEF44 [] [] spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1df4) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_LOOPC -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_words w + 4 * i) -> PropExec.getr R 23%bv = Z_to_bv 64 (wa_words w + 4 * i) ->
    PropExec.getr R 18%bv = Z_to_bv 64 en -> 0 <= en < 2 ^ 32 ->
    wa_words w <> 0 -> 0 <= i < wa_n w ->
    (forall msF1 mo1 m1 R1 (r : Z),
       as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf1e10) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 cj S_WORD TBL_EEF44 [] [] spal ->
       regs_tbl w R1 RT_LOOPW -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 18%bv = PropExec.getr R 18%bv -> PropExec.getr R1 19%bv = PropExec.getr R 19%bv ->
       PropExec.getr R1 21%bv = PropExec.getr R 21%bv -> PropExec.getr R1 22%bv = PropExec.getr R 22%bv ->
       PropExec.getr R1 23%bv = PropExec.getr R 23%bv ->
       0 <= r < 2 ^ 32 -> PropExec.getr R1 10%bv = Z_to_bv 64 (sx32A r) ->
       ffkeep w m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros spal w s LB LBs m mo cj msF R F fc i en Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 G21 G23 G18 Hen Hw Hi K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    destruct (wk_words H w OK) as [[W0 _] | WOK]; [contradiction|].
    destruct WOK as (pw & kw & INw & Kw1 & Wpos & Wal & Wtop & _).
    pose proof (xa_wbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0 Hw) as MD.
    destruct (rdn4_of_mdef m (wa_words w + 4 * i)) as (bs & RD0 & LB4).
    { intros j Hj. replace (wa_words w + 4 * i + j) with (wa_words w + (4 * i + j)) by lia. apply MD. lia. }
    { lia. }
    { lia. }
    set (x0 := bytes_le_to_Z bs).
    assert (XR0 : 0 <= x0 < 2 ^ 32) by (apply bytes_le_to_Z_range4; exact LB4).
    set (Xs := [Z_to_bv 64 (bv_swrap 32 x0)]).
    pose proof (env_world_seed H w R Xs) as HE.
    pose proof (ev_world_all H w _ HE) as (E32 & E33 & _).
    assert (E21 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 21) = Z_to_bv 64 (wa_words w + 4 * i))
      by (cbn [edenot]; rewrite Eseed_reg by lia; exact G21).
    assert (E23 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 23) = Z_to_bv 64 (wa_words w + 4 * i))
      by (cbn [edenot]; rewrite Eseed_reg by lia; exact G23).
    assert (CONT : forall msF1 mo1 R1,
              as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_FIXWORD) fc None m (seg_rom asegs) -> rfull R1 ->
              PMXAT H LINV w s LB LBs m mo1 cj S_WORD TBL_EEF44 [] [] spal ->
              regs_tbl w R1 RT_FXE -> PropExec.getr R1 10%bv = Z_to_bv 64 (sx32A x0) -> PropExec.getr R1 11%bv = Z_to_bv 64 en ->
              (forall r, In r [3; 4; 18; 19; 21; 22; 23]%bv -> PropExec.getr R1 r = PropExec.getr R r) ->
              as_SR H Q (mkCfg msF1 mo1)).
    { intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 G10_1 G11_1 GK1.
      eapply (pm_leafW H HHm3 LINV LINV_frame AT_FIXWORD 0 _ _ _ HFW (x0, en) [] w s LB LBs m mo1 cj S_WORD TBL_EEF44 [] [] spal msF1 R1 F fc 0xf1e10 Q []);
        [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | rtf HT1 | rtf HT1 | reflexivity | lia | lia | reflexivity | reflexivity
        | cbn beta iota; split; [exact XR0|]; split; [exact G10_1|]; split; [exact Hen | exact G11_1]
        | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
        | intros r0 r1 m9 k9 n9 a9 _ Hin9; destruct Hin9
        | ].
      intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 (r & Hr & Er).
      eapply (K msF2 mo2 m2 R2 r KR2 VIS2 RF2 X2);
        [ exact (regs_tbl_sub w _ _ _ RT_LOOPW (regs_keep w [] _ _ RT_FXE HT1 KEEP2) ltac:(vm_compute; reflexivity))
        | rewrite (KEEP2 3%bv ltac:(inb)), (GK1 3%bv ltac:(inb)); exact G3_0
        | rewrite (KEEP2 4%bv ltac:(inb)), (GK1 4%bv ltac:(inb)); exact G4_0
        | rewrite (KEEP2 18%bv ltac:(inb)); exact (GK1 18%bv ltac:(inb))
        | rewrite (KEEP2 19%bv ltac:(inb)); exact (GK1 19%bv ltac:(inb))
        | rewrite (KEEP2 21%bv ltac:(inb)); exact (GK1 21%bv ltac:(inb))
        | rewrite (KEEP2 22%bv ltac:(inb)); exact (GK1 22%bv ltac:(inb))
        | rewrite (KEEP2 23%bv ltac:(inb)); exact (GK1 23%bv ltac:(inb))
        | exact Hr | exact Er
        | apply (ffkeep_munch w _ _ _ MU2 WM2); apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil] ]. }
    destruct (Z_le_gt_dec (4 * i + 4) (8 * ((4 * wa_n w) / 8))) as [FULL | PART].
    - assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m [KWord (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SHBASE) 1 (ELit 0)]).
      { apply Forall_cons; [| apply Forall_nil].
        eapply pmk_sh_wordsE with (w := w) (i := i); first [exact HHm3 | exact OK | exact X0 | exact Hw | exact E21 | lia]. }
      pm_goX HHm3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            [KWord (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SHBASE) 1 (ELit 0)] HKX
            40%nat [AT_FIXWORD] (@nil bool) 41%N S_WORD (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_FXE.
      { split_scs. all: tlw_sc w i E21 E23 RD0. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      apply (CONT msF1 mo1 R1 KR1 VIS1 RF1 X1 (regs_tbl_restrict w [] _ R1 RT_FXE HTx1 ltac:(vm_compute; reflexivity))).
      + rewrite (HR1 10%bv). etransitivity; [| exact (swrap32_sx32A x0 XR0)]. ev_xs. reflexivity.
      + rewrite (HR1 11%bv). exact G18.
      + intros r Hr. repeat (destruct Hr as [<-|Hr]; [rewrite (HR1 _); reflexivity |]). destruct Hr.
    - assert (Hlast : 4 * i = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4) by (Z.div_mod_to_equations; lia).
      destruct Hlast as [HL1 HL2].
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m [KWord (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SHBASE) 1 (ELit 4)]).
      { apply Forall_cons; [| apply Forall_nil].
        eapply pmk_sh_wordsE_part with (w := w) (i := i); first [exact HHm3 | exact OK | exact X0 | exact Hw | exact E21 | exact HL1 | exact HL2]. }
      assert (YA : edenot (Eseed R (wenv_vals w ++ Xs)) (EAlu ALU_ADD (EAlu ALU_AND (EVar 21) (ELit 7)) (ELit 3)) = Z_to_bv 64 3).
      { change (edenot (Eseed R (wenv_vals w ++ Xs)) (EAlu ALU_ADD (EAlu ALU_AND (EVar 21) (ELit 7)) (ELit 3)))
          with (alu64 ALU_ADD (alu64 ALU_AND (edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 21)) (Z_to_bv 64 7)) (Z_to_bv 64 3)).
        rewrite E21, w_and by lia.
        replace (Z.land (wa_words w + 4 * i) 7) with 0; [rewrite w_add by lia; reflexivity |].
        change 7 with (Z.ones 3). rewrite Z.land_ones by lia. Z.div_mod_to_equations. lia. }
      pm_goX HHm3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            [KWord (SA (EAlu ALU_SRL (EVar 21) (ELit 3)) SHBASE) 1 (ELit 4)] HKX
            40%nat [AT_FIXWORD] [true] 41%N S_WORD (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_FXE.
      { split_scs. all: first [ cbn [sc_denot]; rewrite YA; vm_compute; reflexivity | tlw_sc w i E21 E23 RD0 ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      apply (CONT msF1 mo1 R1 KR1 VIS1 RF1 X1 (regs_tbl_restrict w [] _ R1 RT_FXE HTx1 ltac:(vm_compute; reflexivity))).
      + rewrite (HR1 10%bv). etransitivity; [| exact (swrap32_sx32A x0 XR0)]. ev_xs. reflexivity.
      + rewrite (HR1 11%bv). exact G18.
      + intros r Hr. repeat (destruct Hr as [<-|Hr]; [rewrite (HR1 _); reflexivity |]). destruct Hr.
  Qed.




  Lemma tl_wB : forall (spal : Z) (w : pmwA H) s LB LBs m mo (cj : pmc) msF R F fc (r : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo cj S_WORD TBL_EEF44 [] [] spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1e10) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_LOOPW -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (sx32A r) -> 0 <= r < 2 ^ 32 ->
    rw_cells asegs m (wa_ff w + 64) [C8 (Z_to_bv 64 (wa_p w + 240))] ->
    Zlen (t3b (c_v2 cj)) + 1 <= 2 ^ 17 -> pm_bud (wa_n w) cj -> (forall q k, In (q, k) (c_blocks cj) -> k <= 2 ^ 40) ->
    (forall s' LB' LBs' m' mo' msF' R' (b' cap' : Z),
       as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F (Z_to_bv 64 0xf1e20) fc None m' (seg_rom asegs) -> rfull R' ->
       PMXAT H LINV w s' LB' LBs' m' mo' (set_v2A cj (b', t3b (c_v2 cj) ++ [r], cap')) S_WORD TBL_EEF44 [] [] spal ->
       regs_tbl w R' RT_LOOPW -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
       PropExec.getr R' 18%bv = PropExec.getr R 18%bv -> PropExec.getr R' 19%bv = PropExec.getr R 19%bv ->
       PropExec.getr R' 21%bv = PropExec.getr R 21%bv -> PropExec.getr R' 22%bv = PropExec.getr R 22%bv ->
       PropExec.getr R' 23%bv = PropExec.getr R 23%bv ->
       pm_bud (wa_n w) (set_v2A cj (b', t3b (c_v2 cj) ++ [r], cap')) ->
       (forall q k, In (q, k) (c_blocks (set_v2A cj (b', t3b (c_v2 cj) ++ [r], cap'))) -> k <= 2 ^ 40) ->
       rw_cells asegs m' (wa_ff w + 64) [C8 (Z_to_bv 64 (wa_p w + 240))] ->
       ffkeepX w TL_FFX m m' ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros spal w s LB LBs m mo cj msF R F fc r Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 G10 Hr RW64 Hlen BUD BSZ K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmw_frame_facts H w OK) as (FR1 & FR2 & FR3 & _).
    assert (FSZ : 100 <= fsz PM_FCLASS) by (vm_compute; discriminate).
    set (Xs := @nil word).
    pose proof (env_world_seed H w R Xs) as HE.
    pose proof (ev_world_all H w _ HE) as (E32 & E33 & _).
    assert (HKN : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m []) by apply Forall_nil.
    pm_goX HHm3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs (@nil kentry) HKN
          40%nat [BIW32_ENTRY] (@nil bool) 41%N S_WORD (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_V4E.
    { split_scs. all: match goal with |- ?g => idtac "SCLEFT" g end. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (HT1 : regs_tbl w R1 RT_V4E) by exact HTx1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (m1 := mm) in X1, VIS1 end.
    pose proof (munch_sym (Eseed R (wenv_vals w ++ Xs)) m _ [(EVar WV_FF, 96, 100)] Hlf1 ltac:(vm_compute; reflexivity)) as MU.
    cbn [num_wins map] in MU. unfold WV_FF in MU. rewrite E33, u64_of_Z in MU by lia.
    assert (FKX : ffkeepX w [(96, 4)] m m1).
    { apply (ffkeepX_munch w _ _ m m1 MU (wmono_mem_denot _ _ _)).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right. right. apply Exists_cons_hd. cbn [fst snd]. lia. }
    assert (RW64' : rw_cells asegs m1 (wa_ff w + 64) [C8 (Z_to_bv 64 (wa_p w + 240))]).
    { apply (FKX 64 [C8 (Z_to_bv 64 (wa_p w + 240))] ltac:(lia) ltac:(cbn; lia)); [| exact RW64]. apply Forall_cons; [cbn; lia | apply Forall_nil]. }
    assert (RW96 : rw_cells asegs m1 (wa_ff w + 96) [C4 (Z_to_bv 64 r)]).
    { apply (rw_cells_C4_sx32A m1 (wa_ff w + 96) r Hr).
      eapply (rw_cells_mem_denot_w _ _ [] _ 4 _ []);
        [ exact Hlf1 | apply Forall_nil
        | first [apply (estart_var _ 33 96 (wa_ff w) E33); lia | match goal with |- ?g => idtac "ESTART" g end]
        | apply (wr_at_sub asegs m (wa_ff w) (fsz PM_FCLASS)); [exact (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | lia | lia | lia]
        | reflexivity
        | first [exact I | cbn; lia | match goal with |- ?g => idtac "CELLWF" g end]
        | transitivity (word_to_le_bytes 4 (PropExec.getr R 10%bv));
            [rewrite G10; reflexivity | cbn [edenot]; rewrite Eseed_reg by lia; reflexivity] ]. }
    eapply (pm_vpush2b H HHbp LINV LINV_cl HOWN HFC w s LB LBs m1 mo1 cj S_WORD TBL_EEF44 [] [] spal msF1 R1 F fc 0xf1e20 r Q
              OK X1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KR1 VIS1 RF1);
      [ rtf HT1 | reflexivity | lia | rtf HT1 | rewrite (HR1 4%bv); exact G4_0 | rtf HT1 | rtf HT1
      | vm_compute; reflexivity | vm_compute; reflexivity | exact RW64' | exact RW96 | exact Hr | exact BUD
      | intros XSL b'' xs''; apply bud_set_v2; [exact BUD | unfold vgrow, Zlen in *; lia]
      | ].
    intros msF2 mo2 m2 R2 s2 LB2 LBs2 b' cap' KR2 VIS2 RF2 X2 KEEP2 BUD2 CASES FK2.
    eapply (K s2 LB2 LBs2 m2 mo2 msF2 R2 b' cap' KR2 VIS2 RF2 X2).
    - exact (regs_keepV w [] R1 R2 RT_LOOPW V4_KEPT (regs_tbl_sub w [] R1 RT_V4E RT_LOOPW HT1 ltac:(vm_compute; reflexivity)) KEEP2
               ltac:(vm_compute; reflexivity)).
    - rewrite (KEEP2 3%bv ltac:(inb)), (HR1 3%bv). exact G3_0.
    - rewrite (KEEP2 4%bv ltac:(inb)), (HR1 4%bv). exact G4_0.
    - rewrite (KEEP2 18%bv ltac:(inb)), (HR1 18%bv). reflexivity.
    - rewrite (KEEP2 19%bv ltac:(inb)), (HR1 19%bv). reflexivity.
    - rewrite (KEEP2 21%bv ltac:(inb)), (HR1 21%bv). reflexivity.
    - rewrite (KEEP2 22%bv ltac:(inb)), (HR1 22%bv). reflexivity.
    - rewrite (KEEP2 23%bv ltac:(inb)), (HR1 23%bv). reflexivity.
    - exact BUD2.
    - apply bsz_set_v2; [exact BSZ |]. pose proof BUD2 as (_ & _ & _ & _ & _ & Bv2 & _). cbn [set_v2A c_v2 t3a t3b t3c fst snd] in Bv2. lia.
    - exact (FK2 64 [C8 (Z_to_bv 64 (wa_p w + 240))] ltac:(lia) ltac:(cbn; lia) RW64').
    - eapply (ffkeepX_trans w [(96, 4)] [] TL_FFX m m1 m2 FKX (ffkeepX_nil w m1 m2 FK2));
        [intros x Hx; destruct Hx as [<- | []]; right; left; reflexivity | intros x Hx; destruct Hx].
  Qed.

  Lemma tl_next : forall (spal : Z) (w : pmwA H) s LB LBs m mo (cj : pmc) msF R F fc (src e : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo cj S_WORD TBL_EEF44 [] [] spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1e20) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_LOOPW -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 21%bv = Z_to_bv 64 src -> PropExec.getr R 23%bv = Z_to_bv 64 src ->
    PropExec.getr R 22%bv = Z_to_bv 64 e -> 0 <= src -> src + 4 <= e -> e <= 2 ^ 47 ->
    (src + 4 < e -> forall msF1 mo1 m1 R1,
       as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf1df4) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 cj S_WORD TBL_EEF44 [] [] spal ->
       regs_tbl w R1 RT_LOOPC -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 21%bv = Z_to_bv 64 (src + 4) -> PropExec.getr R1 23%bv = Z_to_bv 64 (src + 4) ->
       PropExec.getr R1 18%bv = PropExec.getr R 18%bv -> PropExec.getr R1 19%bv = PropExec.getr R 19%bv ->
       PropExec.getr R1 22%bv = PropExec.getr R 22%bv ->
       ffkeep w m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    (src + 4 = e -> forall msF1 mo1 m1 R1,
       as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf1ab4) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 cj S_OPER TBL_EEF44 [] [] spal ->
       regs_tbl w R1 RT_FIN -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 19%bv = PropExec.getr R 19%bv ->
       ffkeep w m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros spal w s LB LBs m mo cj msF R F fc src e Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 G21 G23 G22 Hs0 Hse He K1 K2.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    set (Xs := @nil word).
    pose proof (env_world_seed H w R Xs) as HE.
    pose proof (ev_world_all H w _ HE) as (E32 & E33 & _).
    assert (HKN : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m []) by apply Forall_nil.
    assert (Y21 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 21) = Z_to_bv 64 src) by (cbn [edenot]; rewrite Eseed_reg by lia; exact G21).
    assert (Y23 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 23) = Z_to_bv 64 src) by (cbn [edenot]; rewrite Eseed_reg by lia; exact G23).
    assert (Y22 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 22) = Z_to_bv 64 e) by (cbn [edenot]; rewrite Eseed_reg by lia; exact G22).
    assert (Y21' : edenot (Eseed R (wenv_vals w ++ Xs)) (EAlu ALU_ADD (EVar 21) (ELit 4)) = Z_to_bv 64 (src + 4))
      by (apply ev_add; [exact Y21 | lia | lia]).
    assert (Y23' : edenot (Eseed R (wenv_vals w ++ Xs)) (EAlu ALU_ADD (EVar 23) (ELit 4)) = Z_to_bv 64 (src + 4))
      by (apply ev_add; [exact Y23 | lia | lia]).
    assert (YL : edenot (Eseed R (wenv_vals w ++ Xs)) (ELit 18446744073709551611) = Z_to_bv 64 18446744073709551611) by reflexivity.
    assert (YL0 : edenot (Eseed R (wenv_vals w ++ Xs)) (ELit 0) = Z_to_bv 64 0) by reflexivity.
    destruct (Z.eq_dec (src + 4) e) as [EQ | NE].
    - pm_goX HHm3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs (@nil kentry) HKN
            40%nat [0xf1ab4] [true; true] 41%N S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_FIN.
      { split_scs. all: first
          [ cbn [sc_denot]; rewrite ?Y21, ?Y23, ?Y22, ?Y21', ?Y23', ?YL, ?YL0; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia;
            first [bool_lia | apply Z.leb_le; lia]
          | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      pose proof (munch_sym (Eseed R (wenv_vals w ++ Xs)) m _ [(FSHB, SHBASE + 8, SHBASE + 9); (FSHB, SHBASE + 12, SHBASE + 13)] Hlf1
                    ltac:(vm_compute; reflexivity)) as MU.
      cbn [num_wins map] in MU. unfold FSHB, WV_FF in MU.
      rewrite (srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)) in MU.
      apply (K2 EQ msF1 mo1 _ R1 KR1 VIS1 RF1 X1 HTx1).
      + rewrite (HR1 3%bv). exact G3_0.
      + rewrite (HR1 4%bv). exact G4_0.
      + rewrite (HR1 19%bv). reflexivity.
      + apply (ffkeep_munch w _ _ _ MU (wmono_mem_denot _ _ _)).
        rewrite Q13 in Q6. unfold SHBASE in *.
        apply Forall_cons; [cbn [fst snd]; destruct Q6 as [Q6|Q6]; [left | right]; lia |].
        apply Forall_cons; [cbn [fst snd]; destruct Q6 as [Q6|Q6]; [left | right]; lia | apply Forall_nil].
    - pm_goX HHm3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs (@nil kentry) HKN
            40%nat [0xf1df4] [true; false; false] 41%N S_WORD (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_LOOPC.
      { split_scs. all: first
          [ cbn [sc_denot]; rewrite ?Y21, ?Y23, ?Y22, ?Y21', ?Y23', ?YL, ?YL0; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia;
            first [bool_lia | apply Z.leb_le; lia]
          | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      pose proof (munch_sym (Eseed R (wenv_vals w ++ Xs)) m _ [(FSHB, SHBASE + 12, SHBASE + 13)] Hlf1
                    ltac:(vm_compute; reflexivity)) as MU.
      cbn [num_wins map] in MU. unfold FSHB, WV_FF in MU.
      rewrite (srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)) in MU.
      apply (K1 ltac:(lia) msF1 mo1 _ R1 KR1 VIS1 RF1 X1 HTx1).
      + rewrite (HR1 3%bv). exact G3_0.
      + rewrite (HR1 4%bv). exact G4_0.
      + rewrite (HR1 21%bv). exact Y21'.
      + rewrite (HR1 23%bv). exact Y23'.
      + rewrite (HR1 18%bv). reflexivity.
      + rewrite (HR1 19%bv). reflexivity.
      + rewrite (HR1 22%bv). reflexivity.
      + apply (ffkeep_munch w _ _ _ MU (wmono_mem_denot _ _ _)).
        rewrite Q13 in Q6. unfold SHBASE in *.
        apply Forall_cons; [cbn [fst snd]; destruct Q6 as [Q6|Q6]; [left | right]; lia | apply Forall_nil].
  Qed.

  Lemma tl_loop : forall (k : nat) (spal : Z) (w : pmwA H) s LB LBs (m0 m : mem) mo (c1 : pmc) (v2j : Z * list Z * Z) msF R F fc (ia en : Z) (Q : config -> Prop),
    pmw_okA H w -> (0 < k)%nat ->
    PMXAT H LINV w s LB LBs m mo (set_v2A c1 v2j) S_WORD TBL_EEF44 [] [] spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1df4) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_LOOPC -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 18%bv = Z_to_bv 64 en -> 0 <= en < 2 ^ 32 ->
    PropExec.getr R 19%bv = Z_to_bv 64 ia ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_words w + 4 * (ia - Z.of_nat k)) ->
    PropExec.getr R 23%bv = Z_to_bv 64 (wa_words w + 4 * (ia - Z.of_nat k)) ->
    PropExec.getr R 22%bv = Z_to_bv 64 (wa_words w + 4 * ia) ->
    rw_cells asegs m (wa_ff w + 64) [C8 (Z_to_bv 64 (wa_p w + 240))] ->
    wa_words w <> 0 -> Z.of_nat k <= ia <= wa_n w ->
    Zlen (t3b v2j) + Z.of_nat k <= 2 ^ 17 ->
    pm_bud (wa_n w) (set_v2A c1 v2j) -> (forall q kk, In (q, kk) (c_blocks (set_v2A c1 v2j)) -> kk <= 2 ^ 40) ->
    ffkeepX w TL_FFX m0 m ->
    (forall s' LB' LBs' m' mo' msF' R' (v2' : Z * list Z * Z),
       as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F (Z_to_bv 64 0xf1ab4) fc None m' (seg_rom asegs) -> rfull R' ->
       PMXAT H LINV w s' LB' LBs' m' mo' (set_v2A c1 v2') S_OPER TBL_EEF44 [] [] spal ->
       regs_tbl w R' RT_FIN -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
       PropExec.getr R' 19%bv = Z_to_bv 64 ia ->
       Zlen (t3b v2') = Zlen (t3b v2j) + Z.of_nat k ->
       pm_bud (wa_n w) (set_v2A c1 v2') -> (forall q kk, In (q, kk) (c_blocks (set_v2A c1 v2')) -> kk <= 2 ^ 40) ->
       ffkeepX w TL_FFX m0 m' ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    induction k as [|k IH];
      intros spal w s LB LBs m0 m mo c1 v2j msF R F fc ia en Q OK Hk X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 G18 Hen G19 G21 G23 G22 RW0 Hw Hia Hlen
             BUD BSZ FK0 K; [lia |].
    pose proof (pmw_bounds H w OK) as BND.
    eapply (tl_wA spal w s LB LBs m mo (set_v2A c1 v2j) msF R F fc (ia - Z.of_nat (S k)) en Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0
              G21 G23 G18 Hen Hw ltac:(lia)).
    intros msF1 mo1 m1 R1 r KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 E18 E19 E21 E22 E23 Hr G10 FK1.
    eapply (tl_wB spal w s LB LBs m1 mo1 (set_v2A c1 v2j) msF1 R1 F fc r Q OK X1 KR1 VIS1 RF1 HT1 G3_1 G4_1 G10 Hr
              (FK1 64 [C8 (Z_to_bv 64 (wa_p w + 240))] ltac:(lia) ltac:(cbn; lia) RW0) ltac:(cbn [set_v2A c_v2]; lia) BUD BSZ).
    intros s2 LB2 LBs2 m2 mo2 msF2 R2 b' cap' KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 F18 F19 F21 F22 F23 BUD2 BSZ2 RW2 FK2.
    assert (FK02 : ffkeepX w TL_FFX m0 m2).
    { eapply (ffkeepX_trans w TL_FFX TL_FFX TL_FFX m0 m1 m2); [| exact FK2 | apply incl_refl | apply incl_refl].
      eapply (ffkeepX_trans w TL_FFX [] TL_FFX m0 m m1 FK0 (ffkeepX_nil w m m1 FK1)); [apply incl_refl | intros x Hx; destruct Hx]. }
    eapply (tl_next spal w s2 LB2 LBs2 m2 mo2 _ msF2 R2 F fc (wa_words w + 4 * (ia - Z.of_nat (S k))) (wa_words w + 4 * ia) Q
              OK X2 KR2 VIS2 RF2 HT2 G3_2 G4_2).
    - rewrite F21, E21. exact G21.
    - rewrite F23, E23. exact G23.
    - rewrite F22, E22. exact G22.
    - lia.
    - lia.
    - lia.
    - intros LT msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 H21 H23 H18 H19 H22 FK3.
      assert (FK03 : ffkeepX w TL_FFX m0 m3)
        by (eapply (ffkeepX_trans w TL_FFX [] TL_FFX m0 m2 m3 FK02 (ffkeepX_nil w m2 m3 FK3)); [apply incl_refl | intros x Hx; destruct Hx]).
      eapply (IH spal w s2 LB2 LBs2 m0 m3 mo3 c1 (b', t3b v2j ++ [r], cap') msF3 R3 F fc ia en Q OK ltac:(lia) X3 KR3 VIS3 RF3 HT3
                G3_3 G4_3).
      + rewrite H18, F18, E18. exact G18.
      + exact Hen.
      + rewrite H19, F19, E19. exact G19.
      + rewrite H21. f_equal. lia.
      + rewrite H23. f_equal. lia.
      + rewrite H22, F22, E22. exact G22.
      + exact (FK3 64 [C8 (Z_to_bv 64 (wa_p w + 240))] ltac:(lia) ltac:(cbn; lia) RW2).
      + exact Hw.
      + lia.
      + cbn [t3b fst snd]. rewrite Zlen_app1. lia.
      + exact BUD2.
      + exact BSZ2.
      + exact FK03.
      + intros s' LB' LBs' m' mo' msF' R' v2' KR' VIS' RF' X' HT' G3' G4' G19' HL' BUD' BSZ' FK'.
        apply (K s' LB' LBs' m' mo' msF' R' v2' KR' VIS' RF' X' HT' G3' G4' G19'); [| exact BUD' | exact BSZ' | exact FK'].
        rewrite HL'. cbn [t3b fst snd]. rewrite Zlen_app1. lia.
    - intros EQ msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 H19 FK3.
      apply (K s2 LB2 LBs2 m3 mo3 msF3 R3 (b', t3b v2j ++ [r], cap') KR3 VIS3 RF3 X3 HT3 G3_3 G4_3).
      + rewrite H19, F19, E19. exact G19.
      + cbn [t3b fst snd]. rewrite Zlen_app1. lia.
      + exact BUD2.
      + exact BSZ2.
      + eapply (ffkeepX_trans w TL_FFX [] TL_FFX m0 m2 m3 FK02 (ffkeepX_nil w m2 m3 FK3)); [apply incl_refl | intros x Hx; destruct Hx].
  Qed.
End TLC.
