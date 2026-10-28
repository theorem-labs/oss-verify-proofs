(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_PmOwn LbB_PmCut
  LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmVops LbB_PmDS LbB_WoGen LbB_ContStmt LbB_PmWKit LbB_PmWG
  LbB_HEmpStmt LbB_HEmpR LbB_HRehB LbB_HKit LbB_PmWM LbB_PmWM3 LbB_PmEmh LbB_PmEmhOk LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HEmp.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section EMHB.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.

  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.

  Hypothesis HOWN : rt_own H.
  #[local] Notation ent := (Z * (Z * Z))%type.

  Lemma emhb3_pmxa : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl s' m' mo' (LB' LBm LBr LBm' : list block)
      (bl bc : Z) (ents : list ent) (bl' bc' : Z) (ents' : list ent) (rehashed : bool) (errv' : word) (XS : list (Z * Z)),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    c_m3 c = (bl, bc, ents) ->
    Permutation LBs (LBm ++ LBr) -> lbl LBr = rest_m3 c ->
    pm_bud (wa_n w) (set_m3A c (bl', bc', ents')) ->
    (rehashed = false -> bl' = bl /\ bc' = bc) -> (rehashed = true -> bc' = bseq_next bc) -> In bc BSEQ -> bc <> BSEQ_LAST ->

    as_RHEAP H s' LB' m' -> Permutation LB' ((wa_LB0 w ++ LBr) ++ LBm') -> Permutation (lbl LBm') (umap_blocks 24 bl' bc' ents') ->
    as_MPRES H mo mo' -> mem_inv asegs m' ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv'] -> as_rauxv_ok H m' (wa_B w) ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H (wa_LB0 w ++ LBr) (wa_s1 w) (mx3 H w ++ XS) m m' ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M3) bl' bc' ents' -> umap_sh m' 24 (bl', bc', ents') ->
    wr_at asegs m' (wa_p w + O_M3) 40 ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    as_AL H s' >= as_AL H s - (if rehashed then ICM (8 * bc') else 0) ->
    PMXA H LINV w s' LB' (LBm' ++ LBr) m' mo' (set_m3A c (bl', bc', ents')) ins tbl ftbl.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl s' m' mo' LB' LBm LBr LBm' bl bc ents bl' bc' ents' rehashed errv' XS
           OK X0 Hknn Hfk Em3 PS ELr BUD' NRH RH Hbs Hlast RH' PE' PM' MP' MI' STK' ERR' RA' FXS XP U1k SH1' WR' RFS' AC' S0' AL'.
    pose proof (proj1 HHbp) as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH0.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    set (LBk := wa_LB0 w ++ LBr) in *.
    set (c' := set_m3A c (bl', bc', ents')) in *.
    set (LBs' := LBm' ++ LBr).

    assert (INr : forall b, In b LBr -> In b LBs) by (intros b Hb; apply (Permutation_in _ (Permutation_sym PS)); apply in_or_app; right; exact Hb).
    assert (LBk1 : forall b, In b LBk -> In b LB).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym OWN1)). unfold LBk in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - apply in_or_app; left; exact Hb.
      - apply in_or_app; right; apply in_or_app; left. exact (INr b Hb). }
    assert (LBk0 : forall b, In b (wa_LB0 w) -> In b LBk) by (intros b Hb; unfold LBk; apply in_or_app; left; exact Hb).
    assert (INr' : forall b, In b LBr -> In b LB') by (intros b Hb; apply (Permutation_in _ (Permutation_sym PE')); apply in_or_app; left; unfold LBk; apply in_or_app; right; exact Hb).
    assert (P1 : Permutation LB' (wa_LB0 w ++ LBs' ++ [])).
    { rewrite app_nil_r. unfold LBs'. eapply perm_trans; [exact PE'|]. unfold LBk. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
    assert (P2 : Permutation (lbl LBs') (c_blocks c')).
    { unfold LBs'. replace (lbl (LBm' ++ LBr)) with (lbl LBm' ++ lbl LBr) by (unfold lbl; rewrite map_app; reflexivity). rewrite ELr.
      eapply perm_trans; [| apply Permutation_sym; exact (cbk_m3' c (bl', bc', ents'))]. cbn [t3a t3b t3c fst snd]. apply Permutation_app_tail. exact PM'. }
    pose proof (HOWN s' LB' m' RH') as OWNall.
    assert (OWN3 : lb_own LBs' m').
    { eapply lb_own_incl; [| exact OWNall]. intros b Hb. apply (Permutation_in _ (Permutation_sym P1)). apply in_or_app; right. rewrite app_nil_r. exact Hb. }
    assert (MEAS' : pm_meas_ok (wa_n w) LBs') by (apply (pm_meas_of_bud (wa_n w) c' LBs'); [lia | exact BUD' | exact P2]).
    assert (RESV' : pm_cap c' + PM_RESERVE <= po_cost (wa_n w)) by (apply pm_resv_of_bud; [exact WN | exact BUD']).
    assert (AL1 : as_AL H s' >= as_AL H (wa_s0 w) - pm_phi c' - 0).
    { destruct rehashed.
      - pose proof (RH eq_refl) as Ebc'. pose proof (phi_rehash_m3 c bl bc ents bl' ents' Em3 Hbs Hlast) as PG.
        subst bc'. fold c' in PG. clear - A1 AL' PG. lia.
      - destruct (NRH eq_refl) as [-> ->]. pose proof (phi_same_m3 c bl bc ents ents' Em3) as PG. fold c' in PG. clear - A1 AL' PG. lia. }

    assert (FXI : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) (mx3 H w ++ XS))
      by (apply Forall_app; split; [unfold mx3; apply Forall_cons; [cbn [fst]; unfold O_M3; lia | apply Forall_nil] | exact (scratch_img H HHbp w m' XS RFS' FXS)]).
    assert (LI' : LINV m') by (apply (LINV_cl m m' (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)); eapply (xpres_img H); [exact XP | exact FXI]).
    assert (FX : Forall (xv_ok4 H w LBs ftbl) (mx3 H w)).
    { unfold mx3. apply Forall_cons; [| apply Forall_nil]. right; left. cbn [fst snd]. unfold O_M1, O_M3, PARSER_SIZE. lia. }
    assert (FXW : Forall (fun iv : Z * Z => (snd iv <= wa_ff w + 24 \/ wa_ff w + 16376 <= fst iv) \/ wr_at asegs m' (fst iv) (snd iv - fst iv)) (mx3 H w)).
    { unfold mx3. apply Forall_cons; [| apply Forall_nil]. right. cbn [fst snd]. replace (wa_p w + O_M3 + 40 - (wa_p w + O_M3)) with 40 by lia. exact WR'. }

    assert (Hp_fs : as_FSB H <= wa_p w /\ wa_p w + PARSER_SIZE <= as_FSB H + AFS_SIZE) by (unfold AFS_HDR in *; lia).
    assert (FOp : fsobj H (PMLF H w) (wa_p w) PARSER_SIZE) by (right; exists fp0; split; [right; exact Hfp0 | lia]).
    pose proof (xp_scr_obj H HH w m' XS (wa_p w) PARSER_SIZE OK RFS' FXS FOp ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(unfold AAPP_HI, PARSER_SIZE in *; lia) PA) as [SXp SXps].
    assert (HEQ : forall a, wa_p w + O_M1 <= a < wa_p w + PARSER_SIZE -> (a < wa_p w + O_M3 \/ wa_p w + O_V1 <= a) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha Ho. apply (XP a); [unfold O_M1, PARSER_SIZE in *; lia|]. split.
      - right; right; right; right; left. unfold O_M1, PARSER_SIZE in *. lia.
      - intros RR. apply rin_ivs_app in RR as [RR|RR]; [unfold mx3 in RR; cbn [rin_ivs fst snd] in RR; unfold O_M3, O_V1 in *; lia|].
        destruct (rin_ivs_In XS a RR) as (iv & Hiv & RR1 & RR2). pose proof (proj1 (Forall_forall _ _) SXp iv Hiv) as DD. cbn beta in DD. unfold O_M1, PARSER_SIZE in *. lia. }
    assert (BLKr : forall A n, In (A, n) (rest_m3 c) -> exists q, In (q, A, n) LBr /\ In (q, A, n) LBk /\ In (q, A, n) LB /\ ablock_range H A n).
    { intros A n Hin. rewrite <- ELr in Hin. destruct (lbl_in_inv _ _ _ Hin) as (q & Hq). exists q.
      assert (Hk : In (q, A, n) LBk) by (unfold LBk; apply in_or_app; right; exact Hq).
      split; [exact Hq|]. split; [exact Hk|]. split; [exact (LBk1 _ Hk)|]. exact (ah_blocks H HH _ _ _ _ RH0 (LBk1 _ Hk)). }
    assert (BEQ : forall A n a, In (A, n) (rest_m3 c) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros A n a Hin Ha. destruct (BLKr A n Hin) as (q & Hq & Hk & HL & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      apply (XP a); [lia|]. split.
      - right; right; left. exists (q, A, n). split; [exact Hk | cbn; lia].
      - pose proof (xp_scr_obj H HH w m' XS A n OK RFS' FXS (fsobj_block H HH _ _ _ (PMLF H w) q A n RH0 HL) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) RAPP) as [SXb _].
        intros RR. apply rin_ivs_app in RR as [RR|RR]; [unfold mx3 in RR; cbn [rin_ivs fst snd] in RR; unfold AFS_HDR, O_M3, PARSER_SIZE in *; lia|].
        destruct (rin_ivs_In XS a RR) as (iv & Hiv & RR1 & RR2). pose proof (proj1 (Forall_forall _ _) SXb iv Hiv) as DD. cbn beta in DD. lia. }
    assert (SEQ : forall A n sbs, In (A, n) (rest_m3 c) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs).
    { intros A n sbs Hin Hlen SH. destruct (BLKr A n Hin) as (q & Hq & Hk & HL & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      eapply (xpres_SHAD H); [exact XP | exact SH |]. split.
      - right; right; right; left. exists (q, A, n). split; [exact Hk | cbn; lia].
      - pose proof (xp_scr_obj H HH w m' XS A n OK RFS' FXS (fsobj_block H HH _ _ _ (PMLF H w) q A n RH0 HL) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) RAPP) as [_ SXb].
        apply Forall_app. split; [| eapply Forall_impl; [| exact SXb]; intros iv Hiv; cbn beta in *; lia].
        unfold mx3. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE A n PA ltac:(lia) ltac:(pose proof (aapp_bounds _ _ RAPP Rn); lia) Rn) as D.
        unfold O_M3, PARSER_SIZE in *. destruct D; lia. }
    assert (LIVE : forall b, In b (rest_m3 c) -> In b (lbl LB) -> In b (lbl LB')).
    { intros [A n] Hin _. destruct (BLKr A n Hin) as (q & Hq & _). exact (lbl_in LB' q A n (INr' _ Hq)). }
    pose proof (pmc_keep_m3 (wa_p w) (lbl LB) (lbl LB') m m' c
                  (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                  (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                  (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) HEQ BEQ SEQ LIVE)
      as (U1' & U2' & SH1k & SH2' & V1' & VS1' & V2' & VS2' & V3' & VS3').
    assert (SHc' : pmc_sh m' c').
    { unfold pmc_sh. unfold c', set_m3A. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3].
      split; [exact SH1k|]. split; [exact SH2'|]. split; [exact SH1'|]. split; [exact VS1'|]. split; [exact VS2' | exact VS3']. }
    assert (MDh : mdef m' (wa_p w + O_M1) (PARSER_SIZE - O_M1)).
    { eapply mdef_hdrs; [exact U1' | exact U2' | exact U1k | exact V1' | exact V2' | exact V3']. }

    eapply (pmxa_xv4 H HH LINV w s LB LBs m mo c ins tbl ftbl [] 0 s' LB' LBs' m' mo' c' [] 0 LBk (mx3 H w) XS);
      [exact OK | exact X0 | exact Hknn | exact RH' | exact MP' | exact MI' | exact STK' | exists errv'; exact ERR' | exact RA' | exact RFS' | exact AC' | exact S0'
      | exact LI' | exact FXS | exact XP | exact FX | exact FXW | exact MDh | exact Hfk
      | exact LBk1 | exact LBk0
      | exact P1 | exact P2 | exact OWN3 | exact MEAS' | apply lb_own_nil | cbn; lia
      | exact AL1 | exact RESV' | exact A4
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact U1' | exact U2' | exact U1k | exact V1' | exact V2' | exact V3' | exact SHc' ].
  Qed.
  Lemma pm_emh_m3 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl msF R F fc (ret sok key : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 (emh_entry EMH_EXT)) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_p w + O_M3) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w + sok) ->

    accessible m (wa_ff w + sok) 4 -> 24 <= sok -> sok + 4 <= 15616 -> sok mod 4 = 0 ->
    rw_cells asegs m (wa_ff w + sok) [C4 (Z_to_bv 64 key)] -> 0 <= key < 2 ^ 32 ->

    pm_bud (wa_n w) c -> 3 * (Zlength (t3c (c_m3 c)) + 1) <= wa_n w + 3 ->
    (forall msF1 mo1 m1 (s1 : as_St H) (LB1 LBs1 : list block) (F1 : bvmap 5 word) (fc1 : bv 32)
            (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (p v : Z) (t : Z * Z * list ent) (inserted : bool),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS (mkR (Z_to_bv 64 ret) (PropExec.getr R 2%bv) (PropExec.getr R 3%bv) (PropExec.getr R 4%bv) t0 t1 t2
                                   (PropExec.getr R 8%bv) (PropExec.getr R 9%bv) (Z_to_bv 64 (p + 20)) a1 a2 a3 a4 a5 a6 a7
                                   (PropExec.getr R 18%bv) (PropExec.getr R 19%bv) (PropExec.getr R 20%bv) (PropExec.getr R 21%bv)
                                   (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) (PropExec.getr R 24%bv) (PropExec.getr R 25%bv)
                                   (PropExec.getr R 26%bv) (PropExec.getr R 27%bv) t3 t4 t5 t6)
                              F1 (Z_to_bv 64 ret) fc1 None m1 (seg_rom asegs) ->
       frm_zero fc1 ->
       PMXA H LINV w s1 LB1 LBs1 m1 mo1 (set_m3A c t) ins tbl ftbl ->
       In (p, (key, v)) (t3c t) -> 0 <= v < 2 ^ 32 ->
       Zlength (t3c (c_m3 c)) <= Zlength (t3c t) <= Zlength (t3c (c_m3 c)) + 1 ->
       (inserted = false -> t3c t = t3c (c_m3 c)) ->
       (inserted = true -> v = 0 /\ Permutation (t3c t) ((p, (key, 0)) :: t3c (c_m3 c))) ->
       pm_bud (wa_n w) (set_m3A c t) ->

       (t3b t = t3b (c_m3 c) \/ ((t3b (c_m3 c) = 0 \/ Zlength (t3c (c_m3 c)) = t3b (c_m3 c)) /\ t3b t = bseq_next (t3b (c_m3 c)))) ->
       In (t3b (c_m3 c)) BSEQ -> t3b (c_m3 c) <> BSEQ_LAST ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 -> rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_cl LINV_relro HOWN.
    intros w s LB LBs m mo c ins tbl ftbl msF R F fc ret sok key Q OK X Hknn Hfk KR VIS RF FRZ
           G1 Hr2 Hr G2 G4 G10 G11 Hokk Hk1 Hk2 Hk4 RWk Hkey BUD ACC K.
    pose proof (proj1 HHbp) as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (wk_s1 H w OK) as [T1 T2].
    pose proof (wk_n H w OK) as WN. pose proof (wk_B64 H w OK) as B64.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4).
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SHc & ADp & _).
    pose proof (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FSH.
    destruct (c_m3 c) as [[bl bc] ents] eqn:Em3. cbn [t3a t3b t3c fst snd] in *.
    pose proof (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as U. rewrite Em3 in U. cbn [t3a t3b t3c fst snd] in U.
    pose proof SHc as (_ & _ & SH1 & _). rewrite Em3 in SH1.
    pose proof (u_bseq U) as Hbs. pose proof (LbB_HFind.BSEQ_boundA bc Hbs) as B0.
    pose proof BUD as BUDc. unfold pm_bud in BUDc. rewrite Em3 in BUDc. cbn [t3a t3b t3c fst snd] in BUDc.
    destruct BUDc as ((_ & _ & C1a) & _ & _ & C2 & _).
    assert (Hlast : bc <> BSEQ_LAST) by (unfold BSEQ_LAST; clear - C2 WN; lia).
    pose proof (bseq_next_le2' bc Hbs Hlast) as LE2.
    destruct (bseq_next_factsE bc Hbs Hlast) as (_ & Hbcn & Hn28 & _).

    pose proof OWN2 as OWN2'. rewrite <- (app_nil_r (c_blocks c)) in OWN2'.
    destruct (lbl_perm_splitR LBs (mblk3 c) (rest_m3 c) ltac:(eapply perm_trans; [exact OWN2 | exact (cbk_m3 c)])) as (LBm & LBr & PS & ELm & ELr).
    unfold mblk3 in ELm. rewrite Em3 in ELm. cbn [t3a t3b t3c fst snd] in ELm.
    set (LBk := wa_LB0 w ++ LBr).
    assert (PE : Permutation LB (LBk ++ LBm)).
    { eapply perm_trans; [exact OWN1|]. rewrite app_nil_r. unfold LBk. rewrite <- app_assoc. apply Permutation_app_head.
      eapply perm_trans; [exact PS | apply Permutation_app_comm]. }
    assert (OWNm : lb_own LBm m).
    { eapply lb_own_incl; [| exact (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)]. intros b Hb. apply (Permutation_in _ (Permutation_sym PS)). apply in_or_app; left; exact Hb. }

    assert (TRd : trace_ok (as_TR H) APC0_FREE [emp_del_ra EMP_EXT]).
    { pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR. exact (proj1 (Forall_forall _ _) TR 0xfc020 ltac:(cbn; tauto)). }

    change (fsz PM_FCLASS) with 16384 in *.
    assert (AKk : accessible m (wa_ff w + sok) 4) by exact Hokk.
    assert (FKk : fldA m (wa_ff w + sok) 4 key).
    { pose proof (fld_of_cell4 m (wa_ff w + sok) (Z_to_bv 64 key) RWk ltac:(lia)) as FL. rewrite HLib.u64_of_Z in FL by lia. exact FL. }
    assert (ESRC : forall so n, 0 <= so -> so + n <= 15616 -> 0 <= n <= 8 -> emp_src H LBk (wa_s1 w) (wa_p w + O_M3) (wa_ff w + so) n).
    { intros so n Hso Hson Hn. split; [| split].
      - right; right; right; right; left. clear - F1 F2 Hso Hson Hn. unfold AFS_HDR in *. lia.
      - right; right; right; right; right; left. split; [apply sh_mono; clear - F1 Hso; unfold AFS_HDR in *; lia|].
        assert (sh (wa_ff w + so) + nsh n <= sh (wa_ff w + so + 16)) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
        assert (sh (wa_ff w + so + 16) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; clear - F2 Hson Hn; lia). lia.
      - unfold apart. unfold O_M3, PARSER_SIZE in *. clear - PFF Hso Hson Hn. lia. }

    pose proof (pm_phi_le_cap c) as PCc.
    assert (AL0 : 0 <= as_AL H s) by (unfold PM_RESERVE in *; clear - A1 A2 A3 PCc; lia).
    assert (RICM : (bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s).
    { intros CASE.
      pose proof (bud_emp_m3 (wa_n w) c bl bc ents 1 (bseq_next bc) ((1, (key, 0)) :: ents) BUD Em3 Hbs Hlast ACC
                    ltac:(unfold Zlength; cbn [length]; lia) (or_intror (conj CASE eq_refl))) as BUDg.
      pose proof (pm_resv_of_bud (wa_n w) _ WN BUDg) as RESVg.
      pose proof (phi_rehash_m3 c bl bc ents 1 ((1, (key, 0)) :: ents) Em3 Hbs Hlast) as PG.
      match type of RESVg with pm_cap ?cc + _ <= _ => pose proof (pm_phi_le_cap cc) as PCg end.
      clear - A1 A3 RESVg PG PCg. unfold PM_RESERVE in *. lia. }
    pose proof (pmxa_meas_LB H LINV w s LB LBs m mo c ins tbl ftbl [] 0 OK X) as (M1 & M2 & M3).
    pose proof (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl [] 0 OK X) as (M4 & M5).
    pose proof (nsmall_bounds (8 * bseq_next bc) ltac:(lia)) as NSB. pose proof (nlg_bounds (8 * bseq_next bc)) as NLB.

    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H HH).
    { eapply (emh_ext_ok H HHbp) with (obj := wa_p w + O_M3) (keyp := wa_ff w + sok)
        (key := key) (bl := bl) (bc := bc) (ents := ents) (LB := LB) (LB0 := LBk) (LBm := LBm) (LF := PMLF H w)
        (lo := wa_lo w) (B := wa_B w) (shi := wa_shi w) (errv := errv) (s := s) (m := m) (mo := mo);
      [ exact VIS | exact FRZ | exact G10 | exact G11
      | exact U | exact SH1 | exact PE | rewrite ELm; apply Permutation_refl
      | apply (pw_addr_sub8 m (wa_p w) PARSER_SIZE O_M3 40 ADp); unfold O_M3, PARSER_SIZE; try reflexivity; lia
      | apply (wr_at_of_mdef m (wa_p w) PARSER_SIZE O_M3 40 (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)); unfold O_M3, PARSER_SIZE; lia
      | exists fp0; split; [right; exact Hfp0 | unfold O_M3, PARSER_SIZE in *; lia]
      | unfold O_M3, PARSER_SIZE in *; lia
      | intros b Hb; pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (_ & _ & _ & _ & _ & RFb & _); unfold AFS_HDR, O_M3, PARSER_SIZE in *; clear - RFb PF1 PF2 PF3 PF4; lia
      | exact FKk | exact AKk | rewrite G2, u64_of_Z by lia; apply ESRC; lia
      | exists (PM_FCLASS, wa_ff w, wa_fp w); split; [left; reflexivity | unfold ff_addr, ff_class; cbn [fst snd]; change (fsz PM_FCLASS) with 16384; lia]
      | clear - Q2 Hk4; Z.div_mod_to_equations; lia
      | exact Hkey
      | clear - ACC WN; unfold Zlength in *; lia | exact Hlast
      | exact RH | exact KR | exact AL0
      | clear - M4 NSB; unfold nsmall in *; destruct (Z.leb_spec (8 * bseq_next bc) 64512); lia | exact M2 | clear - M5 NLB; lia
      | exact RICM | exact TRd
      | exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G2, u64_of_Z by lia; lia | exact B64
      | rewrite G2, u64_of_Z by lia; clear - Q12; Z.div_mod_to_equations; lia
      | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia)))
      | lia | rewrite G2, u64_of_Z by lia; unfold AEMH_STACK, AEMP_STACK, AOPNEW_STACK, AMALLOC_STACK, APM_STACK in *; lia
      | rewrite G4; exact ERR | exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G4; exact (wk_tp H w OK)
      | rewrite G1, u64_of_Z by lia; exact Hr2
      | exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
      | pose proof (wk_lfb H w OK) as LFB; unfold PM_FRAMES in LFB; unfold PMLF; cbn [length]; lia
      | exact (LINV_relro m (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) | exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
      | rewrite G2, u64_of_Z by lia; lia
      | exact OWNm ]. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB' & LBm' & F' & fc' & p & v & bl' & bc'
                      & ents' & inserted & rehashed & XS & POST).
    cbv zeta in POST.
    destruct POST as (VIS1 & FRZ1 & KR1 & MP1 & MI1 & ST1 & ER1 & RA1 & U1 & SH1' & AD1 & WR1 & Hin & NINS & INS & NRH & RHD & RH1 & PE1 & PM1 & OW1 & FXS1 & XP1 & RF1 & AC1' & S01 & AL1).
    cbn [cfg_ms cfg_model] in VIS1, KR1, MP1. cbn [emh_voff EMH_EXT] in VIS1.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in ST1 by lia. rewrite G4 in ER1. rewrite G2, u64_of_Z in XP1 by lia.

    pose proof U1 as U1d. destruct U1d as [_ _ _ _ Ubseq' Uload' _ _ _ _ _ _ _ _ Unode' _].
    assert (LEN : Zlength ents <= Zlength ents' <= Zlength ents + 1).
    { destruct inserted.
      - pose proof (Permutation_length (proj2 (INS eq_refl))) as E. unfold Zlength. rewrite E. cbn [length]. lia.
      - destruct (NINS eq_refl) as [-> _]. lia. }
    assert (CASE : bc' = bc \/ ((bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc)).
    { destruct rehashed; [right; exact (RHD eq_refl) | left; exact (proj2 (NRH eq_refl))]. }
    assert (BUD1 : pm_bud (wa_n w) (set_m3A c (bl', bc', ents'))) by exact (bud_emp_m3 (wa_n w) c bl bc ents bl' bc' ents' BUD Em3 Hbs Hlast ACC (proj2 LEN) CASE).
    assert (X1 : PMXA H LINV w s1 LB' (LBm' ++ LBr) m1 mo1 (set_m3A c (bl', bc', ents')) ins tbl ftbl).
    { eapply (emhb3_pmxa w s LB LBs m mo c ins tbl ftbl s1 m1 mo1 LB' LBm LBr LBm' bl bc ents bl' bc' ents' rehashed errv1 XS);
        [ exact OK | exact X | exact Hknn | exact Hfk | exact Em3 | exact PS | exact ELr | exact BUD1
        | exact NRH | intros Hrh; exact (proj2 (RHD Hrh)) | exact Hbs | exact Hlast
        | exact RH1 | exact PE1 | exact PM1 | exact MP1 | exact MI1 | exact ST1 | exact ER1 | exact RA1
        | exact FXS1 | exact XP1 | exact U1 | exact SH1' | exact WR1 | exact RF1 | exact AC1' | exact S01 | exact AL1 ]. }
    destruct (Unode' p key v Hin) as (_ & _ & _ & _ & _ & _ & _ & NV & _). pose proof (proj1 NV) as Rv. cbn in Rv.
    eapply (K ms1 mo1 m1 s1 LB' (LBm' ++ LBr) F' fc' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' p v (bl', bc', ents') inserted);
      [ exact KR1 | exact VIS1 | exact FRZ1 | exact X1 | exact Hin | exact Rv | cbn [t3c snd]; exact LEN
      | intros Hf; cbn [t3c snd]; exact (proj1 (NINS Hf)) | intros Ht; cbn [t3c snd]; exact (INS Ht) | exact BUD1
      | cbn [t3a t3b t3c fst snd]; exact CASE | cbn [t3a t3b t3c fst snd]; exact Hbs | cbn [t3a t3b t3c fst snd]; exact Hlast |].

    intros k cs Hk Hkc RWc. eapply (xpres_rw_cells H); [exact XP1 | exact RWc |]. split.
    - right; right; right; right; left. clear - F1 F2 Hk Hkc. unfold AFS_HDR in *. lia.
    - apply Forall_cons; [cbn [fst snd]; unfold O_M3, PARSER_SIZE in *; clear - PFF Hk Hkc; lia|].
      assert (FOf : fsobj H (PMLF H w) (wa_ff w) 16384) by (right; exists (PM_FCLASS, wa_ff w, wa_fp w); split; [left; reflexivity | unfold ff_addr, ff_class; cbn [fst snd]; change (fsz PM_FCLASS) with 16384; lia]).
      pose proof (xp_scr_obj H HH w m1 XS (wa_ff w) 16384 OK RF1 FXS1 FOf ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) FA) as [SXf _].
      eapply Forall_impl; [| exact SXf]. intros iv Hiv. cbn beta in *. lia.
  Qed.

  Lemma emhb1_nrin : forall (X Y : list (Z * Z)) (a : Z), ~ rin_ivs X a ->
    Forall (fun iv : Z * Z => a + 1 <= fst iv \/ snd iv <= a) Y -> ~ rin_ivs (X ++ Y) a.
  Proof.
    induction X as [|iv X IH]; intros Y a NX FY; cbn [app rin_ivs].
    - induction FY as [|iv Y F1 F2 IHY]; cbn [rin_ivs]; [tauto|]. intros [R|R]; [lia | exact (IHY R)].
    - assert (NX' : ~ rin_ivs X a) by (intros K; apply NX; cbn [rin_ivs]; right; exact K).
      intros [R|R]; [apply NX; cbn [rin_ivs]; left; exact R | exact (IH Y a NX' FY R)].
  Qed.

  Lemma emhb1_lfb : forall (w : pmwA H), pmw_okA H w -> (length (PMLF H w) < AFS_MAXLIVE_BP)%nat.
  Proof.
    intros w OK. pose proof (wk_lfb H w OK) as L. unfold PMLF. cbn [length]. unfold PM_FRAMES, AFS_MAXLIVE_BP in *. lia.
  Qed.

  Lemma emhb1_stk : forall (w : pmwA H), pmw_okA H w -> wa_lo w <= wa_s1 w - AEMH_STACK.
  Proof.
    intros w OK. pose proof (wk_stack H w OK) as (S1 & S2 & _). pose proof (wk_s1 H w OK) as [T1 _].
    unfold AEMH_STACK, AEMP_STACK, AOPNEW_STACK, AMALLOC_STACK, APM_STACK in *. lia.
  Qed.

  Lemma emhb1_kfr : forall (w : pmwA H) (sok : Z), 24 <= sok -> sok + 4 <= 16384 ->
    exists f, In f (PMLF H w) /\ ff_addr f <= wa_ff w + sok /\ wa_ff w + sok + 4 <= ff_addr f + fsz (ff_class f).
  Proof.
    intros w sok H1 H2. exists (PM_FCLASS, wa_ff w, wa_fp w). split; [left; reflexivity|].
    unfold ff_addr, ff_class. cbn [fst snd]. change (fsz PM_FCLASS) with 16384. lia.
  Qed.

  Lemma emhb1_pmxa : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl s' m' mo' (LB' LBm LBr LBm' : list block) (XS : list (Z * Z))
      (bl bc : Z) (ents : list ent) (bl' bc' : Z) (ents' : list ent) (rehashed : bool) (errv' : word),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    c_m1 c = (bl, bc, ents) ->
    Permutation LBs (LBm ++ LBr) -> lbl LBr = rest_m1 c ->
    pm_bud (wa_n w) (set_m1A c (bl', bc', ents')) ->
    (rehashed = false -> bl' = bl /\ bc' = bc) -> (rehashed = true -> bc' = bseq_next bc) -> In bc BSEQ -> bc <> BSEQ_LAST ->

    as_RHEAP H s' LB' m' -> Permutation LB' ((wa_LB0 w ++ LBr) ++ LBm') -> Permutation (lbl LBm') (umap_blocks 24 bl' bc' ents') ->
    as_MPRES H mo mo' -> mem_inv asegs m' ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv'] -> as_rauxv_ok H m' (wa_B w) ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H (wa_LB0 w ++ LBr) (wa_s1 w) (mx1 H w ++ XS) m m' ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M1) bl' bc' ents' -> umap_sh m' 24 (bl', bc', ents') ->
    wr_at asegs m' (wa_p w + O_M1) 40 ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    as_AL H s' >= as_AL H s - (if rehashed then ICM (8 * bc') else 0) ->
    PMXA H LINV w s' LB' (LBm' ++ LBr) m' mo' (set_m1A c (bl', bc', ents')) ins tbl ftbl.
  Proof using HHbp LINV_cl HOWN.
    intros w s LB LBs m mo c ins tbl ftbl s' m' mo' LB' LBm LBr LBm' XS bl bc ents bl' bc' ents' rehashed errv'
           OK X0 Hknn Hfk Em1 PS ELr BUD' NRH RH Hbs Hlast RH' PE' PM' MP' MI' STK' ERR' RA' FXS XP U1' SH1' WR' RFS' AC' S0' AL'.
    pose proof (proj1 HHbp) as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH0.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    set (LBk := wa_LB0 w ++ LBr) in *.
    set (c' := set_m1A c (bl', bc', ents')) in *.
    set (LBs' := LBm' ++ LBr).

    assert (INr : forall b, In b LBr -> In b LBs) by (intros b Hb; apply (Permutation_in _ (Permutation_sym PS)); apply in_or_app; right; exact Hb).
    assert (LBk1 : forall b, In b LBk -> In b LB).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym OWN1)). unfold LBk in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - apply in_or_app; left; exact Hb.
      - apply in_or_app; right; apply in_or_app; left. exact (INr b Hb). }
    assert (LBk0 : forall b, In b (wa_LB0 w) -> In b LBk) by (intros b Hb; unfold LBk; apply in_or_app; left; exact Hb).
    assert (INr' : forall b, In b LBr -> In b LB') by (intros b Hb; apply (Permutation_in _ (Permutation_sym PE')); apply in_or_app; left; unfold LBk; apply in_or_app; right; exact Hb).
    assert (P1 : Permutation LB' (wa_LB0 w ++ LBs' ++ [])).
    { rewrite app_nil_r. unfold LBs'. eapply perm_trans; [exact PE'|]. unfold LBk. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
    assert (P2 : Permutation (lbl LBs') (c_blocks c')).
    { unfold LBs'. replace (lbl (LBm' ++ LBr)) with (lbl LBm' ++ lbl LBr) by (unfold lbl; rewrite map_app; reflexivity). rewrite ELr.
      eapply perm_trans; [| apply Permutation_sym; exact (cbk_m1' c (bl', bc', ents'))]. cbn [t3a t3b t3c fst snd]. apply Permutation_app_tail. exact PM'. }
    pose proof (HOWN s' LB' m' RH') as OWNall.
    assert (OWN3 : lb_own LBs' m').
    { eapply lb_own_incl; [| exact OWNall]. intros b Hb. apply (Permutation_in _ (Permutation_sym P1)). apply in_or_app; right. rewrite app_nil_r. exact Hb. }
    assert (MEAS' : pm_meas_ok (wa_n w) LBs') by (apply (pm_meas_of_bud (wa_n w) c' LBs'); [lia | exact BUD' | exact P2]).
    assert (RESV' : pm_cap c' + PM_RESERVE <= po_cost (wa_n w)) by (apply pm_resv_of_bud; [exact WN | exact BUD']).
    assert (AL1 : as_AL H s' >= as_AL H (wa_s0 w) - pm_phi c' - 0).
    { destruct rehashed.
      - pose proof (RH eq_refl) as Ebc'. pose proof (phi_rehash_m1 c bl bc ents bl' ents' Em1 Hbs Hlast) as PG.
        subst bc'. fold c' in PG. clear - A1 AL' PG. lia.
      - destruct (NRH eq_refl) as [-> ->]. pose proof (phi_same_m1 c bl bc ents ents' Em1) as PG. fold c' in PG. clear - A1 AL' PG. lia. }

    assert (FXI : Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) (mx1 H w ++ XS)).
    { apply Forall_app. split; [unfold mx1; apply Forall_cons; [cbn [fst]; unfold O_M1; lia | apply Forall_nil] | exact (scratch_img H HHbp w m' XS RFS' FXS)]. }
    assert (LI' : LINV m') by (apply (LINV_cl m m' (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)); eapply (xpres_img H); [exact XP | exact FXI]).
    assert (FX : Forall (xv_ok4 H w LBs ftbl) (mx1 H w)).
    { unfold mx1. apply Forall_cons; [| apply Forall_nil]. right; left. cbn [fst snd]. unfold O_M1, PARSER_SIZE. lia. }
    assert (FXW : Forall (fun iv : Z * Z => (snd iv <= wa_ff w + 24 \/ wa_ff w + 16376 <= fst iv) \/ wr_at asegs m' (fst iv) (snd iv - fst iv)) (mx1 H w)).
    { unfold mx1. apply Forall_cons; [| apply Forall_nil]. right. cbn [fst snd]. replace (wa_p w + O_M1 + 40 - (wa_p w + O_M1)) with 40 by lia. exact WR'. }

    assert (FOp : fsobj H (PMLF H w) (wa_p w) PARSER_SIZE) by (right; exists fp0; split; [right; exact Hfp0 | lia]).
    pose proof (xp_scr_obj H HH w m' XS (wa_p w) PARSER_SIZE OK RFS' FXS FOp ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(unfold AAPP_HI, PARSER_SIZE in *; lia) PA) as [SXp _].
    assert (Hp_fs : as_FSB H <= wa_p w /\ wa_p w + PARSER_SIZE <= as_FSB H + AFS_SIZE) by (unfold AFS_HDR in *; lia).
    assert (HEQ : forall a, wa_p w + O_M2 <= a < wa_p w + PARSER_SIZE -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. apply (XP a); [unfold O_M2, PARSER_SIZE in *; lia|]. split.
      - right; right; right; right; left. unfold O_M2, PARSER_SIZE in *. lia.
      - apply emhb1_nrin; [unfold mx1; cbn [rin_ivs fst snd]; unfold O_M1, O_M2 in *; lia |].
        eapply Forall_impl; [| exact SXp]. intros iv Hiv. cbn beta in Hiv. unfold O_M2, PARSER_SIZE in *. lia. }
    assert (BLKr : forall A n, In (A, n) (rest_m1 c) -> exists q, In (q, A, n) LBr /\ In (q, A, n) LBk /\ In (q, A, n) LB /\ ablock_range H A n).
    { intros A n Hin. rewrite <- ELr in Hin. destruct (lbl_in_inv _ _ _ Hin) as (q & Hq). exists q.
      assert (Hk : In (q, A, n) LBk) by (unfold LBk; apply in_or_app; right; exact Hq).
      split; [exact Hq|]. split; [exact Hk|]. split; [exact (LBk1 _ Hk)|]. exact (ah_blocks H HH _ _ _ _ RH0 (LBk1 _ Hk)). }
    assert (SXb : forall A n, In (A, n) (rest_m1 c) ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XS /\ Forall (fun iv : Z * Z => sh A + nsh n <= fst iv \/ snd iv <= sh A) XS).
    { intros A n Hin. destruct (BLKr A n Hin) as (q & Hq & Hk & HL & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      assert (FO : fsobj H (PMLF H w) A n) by (eapply fsobj_block; [exact HH | exact RH0 | exact HL]).
      exact (xp_scr_obj H HH w m' XS A n OK RFS' FXS FO ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) RAPP). }
    assert (BEQ : forall A n a, In (A, n) (rest_m1 c) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros A n a Hin Ha. destruct (BLKr A n Hin) as (q & Hq & Hk & HL & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      apply (XP a); [lia|]. split.
      - right; right; left. exists (q, A, n). split; [exact Hk | cbn; lia].
      - apply emhb1_nrin; [unfold mx1; cbn [rin_ivs fst snd]; unfold AFS_HDR, O_M1, PARSER_SIZE in *; lia |].
        eapply Forall_impl; [| exact (proj1 (SXb A n Hin))]. intros iv Hiv. cbn beta in Hiv. lia. }
    assert (SEQ : forall A n sbs, In (A, n) (rest_m1 c) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs).
    { intros A n sbs Hin Hlen SH. destruct (BLKr A n Hin) as (q & Hq & Hk & HL & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      eapply (xpres_SHAD H); [exact XP | exact SH |]. split.
      - right; right; right; left. exists (q, A, n). split; [exact Hk | cbn; lia].
      - apply Forall_app. split; [| eapply Forall_impl; [| exact (proj2 (SXb A n Hin))]; intros iv Hiv; cbn beta in Hiv; lia].
        unfold mx1. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE A n PA ltac:(lia) ltac:(pose proof (aapp_bounds _ _ RAPP Rn); lia) Rn) as D.
        unfold O_M1, PARSER_SIZE in *. destruct D; lia. }
    assert (LIVE : forall b, In b (rest_m1 c) -> In b (lbl LB) -> In b (lbl LB')).
    { intros [A n] Hin _. destruct (BLKr A n Hin) as (q & Hq & _). exact (lbl_in LB' q A n (INr' _ Hq)). }
    pose proof (pmc_keep_m1 (wa_p w) (lbl LB) (lbl LB') m m' c
                  (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                  (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
                  (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) HEQ BEQ SEQ LIVE)
      as (U2' & U3' & SH2' & SH3' & V1' & VS1' & V2' & VS2' & V3' & VS3').
    assert (SHc' : pmc_sh m' c').
    { unfold pmc_sh. unfold c', set_m1A. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3].
      split; [exact SH1'|]. split; [exact SH2'|]. split; [exact SH3'|]. split; [exact VS1'|]. split; [exact VS2' | exact VS3']. }
    assert (MDh : mdef m' (wa_p w + O_M1) (PARSER_SIZE - O_M1)).
    { eapply mdef_hdrs; [exact U1' | exact U2' | exact U3' | exact V1' | exact V2' | exact V3']. }

    eapply (pmxa_xv4 H HH LINV w s LB LBs m mo c ins tbl ftbl [] 0 s' LB' LBs' m' mo' c' [] 0 LBk (mx1 H w) XS);
      [exact OK | exact X0 | exact Hknn | exact RH' | exact MP' | exact MI' | exact STK' | exists errv'; exact ERR' | exact RA' | exact RFS' | exact AC' | exact S0'
      | exact LI' | exact FXS | exact XP | exact FX | exact FXW | exact MDh | exact Hfk
      | exact LBk1 | exact LBk0
      | exact P1 | exact P2 | exact OWN3 | exact MEAS' | apply lb_own_nil | cbn; lia
      | exact AL1 | exact RESV' | exact A4
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact U1' | exact U2' | exact U3' | exact V1' | exact V2' | exact V3' | exact SHc' ].
  Qed.

  Lemma pm_emh_m1 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl msF R F fc (ret sok key : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 (emh_entry EMH_U32)) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_p w + O_M1) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w + sok) ->

    accessible m (wa_ff w + sok) 4 -> 24 <= sok -> sok + 4 <= 15616 -> sok mod 4 = 0 ->
    rw_cells asegs m (wa_ff w + sok) [C4 (Z_to_bv 64 key)] -> 0 <= key < 2 ^ 32 ->

    pm_bud (wa_n w) c -> 2 * (Zlength (t3c (c_m1 c)) + 1) <= wa_n w + 2 ->
    (forall msF1 mo1 m1 (s1 : as_St H) (LB1 LBs1 : list block) (F1 : bvmap 5 word) (fc1 : bv 32)
            (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (p v : Z) (t : Z * Z * list ent) (inserted : bool),
       as_AKREL H s1 (mkCfg msF1 mo1) ->
       as_VIS H s1 msF1 = MS (mkR (Z_to_bv 64 ret) (PropExec.getr R 2%bv) (PropExec.getr R 3%bv) (PropExec.getr R 4%bv) t0 t1 t2
                                   (PropExec.getr R 8%bv) (PropExec.getr R 9%bv) (Z_to_bv 64 (p + 20)) a1 a2 a3 a4 a5 a6 a7
                                   (PropExec.getr R 18%bv) (PropExec.getr R 19%bv) (PropExec.getr R 20%bv) (PropExec.getr R 21%bv)
                                   (PropExec.getr R 22%bv) (PropExec.getr R 23%bv) (PropExec.getr R 24%bv) (PropExec.getr R 25%bv)
                                   (PropExec.getr R 26%bv) (PropExec.getr R 27%bv) t3 t4 t5 t6)
                              F1 (Z_to_bv 64 ret) fc1 None m1 (seg_rom asegs) ->
       frm_zero fc1 ->
       PMXA H LINV w s1 LB1 LBs1 m1 mo1 (set_m1A c t) ins tbl ftbl ->
       In (p, (key, v)) (t3c t) -> 0 <= v < 2 ^ 32 ->
       Zlength (t3c (c_m1 c)) <= Zlength (t3c t) <= Zlength (t3c (c_m1 c)) + 1 ->
       (inserted = false -> t3c t = t3c (c_m1 c)) ->
       (inserted = true -> v = 0 /\ Permutation (t3c t) ((p, (key, 0)) :: t3c (c_m1 c))) ->
       pm_bud (wa_n w) (set_m1A c t) ->

       (t3b t = t3b (c_m1 c) \/ ((t3b (c_m1 c) = 0 \/ Zlength (t3c (c_m1 c)) = t3b (c_m1 c)) /\ t3b t = bseq_next (t3b (c_m1 c)))) ->
       In (t3b (c_m1 c)) BSEQ -> t3b (c_m1 c) <> BSEQ_LAST ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 -> rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_cl LINV_relro HOWN.
    intros w s LB LBs m mo c ins tbl ftbl msF R F fc ret sok key Q OK X Hknn Hfk KR VIS RF FRZ
           G1 Hr2 Hr G2 G4 G10 G11 Hokk Hk1 Hk2 Hk4 RWk Hkey BUD ACC K.
    pose proof (proj1 HHbp) as HH.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (wk_s1 H w OK) as [T1 T2].
    pose proof (wk_n H w OK) as WN. pose proof (wk_B64 H w OK) as B64.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4).
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SHc & ADp & _).
    pose proof (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FSH.
    destruct (c_m1 c) as [[bl bc] ents] eqn:Em1. cbn [t3a t3b t3c fst snd] in *.
    pose proof (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as U. rewrite Em1 in U. cbn [t3a t3b t3c fst snd] in U.
    pose proof SHc as (SH1 & _). rewrite Em1 in SH1.
    pose proof (u_bseq U) as Hbs. pose proof (LbB_HFind.BSEQ_boundA bc Hbs) as B0.
    pose proof BUD as BUDc. unfold pm_bud in BUDc. rewrite Em1 in BUDc. cbn [t3a t3b t3c fst snd] in BUDc.
    destruct BUDc as ((C1a & _ & _) & C2 & _).
    assert (Hlast : bc <> BSEQ_LAST) by (unfold BSEQ_LAST; clear - C2 WN; lia).
    pose proof (bseq_next_le2 bc Hbs Hlast) as LE2.
    destruct (bseq_next_factsE bc Hbs Hlast) as (_ & Hbcn & Hn28 & _).

    pose proof OWN2 as OWN2'. rewrite <- (app_nil_r (c_blocks c)) in OWN2'.
    destruct (lbl_perm_splitR LBs (mblk1 c) (rest_m1 c) ltac:(eapply perm_trans; [exact OWN2 | exact (cbk_m1 c)])) as (LBm & LBr & PS & ELm & ELr).
    unfold mblk1 in ELm. rewrite Em1 in ELm. cbn [t3a t3b t3c fst snd] in ELm.
    set (LBk := wa_LB0 w ++ LBr).
    assert (PE : Permutation LB (LBk ++ LBm)).
    { eapply perm_trans; [exact OWN1|]. rewrite app_nil_r. unfold LBk. rewrite <- app_assoc. apply Permutation_app_head.
      eapply perm_trans; [exact PS | apply Permutation_app_comm]. }
    assert (OWNm : lb_own LBm m).
    { eapply lb_own_incl; [| exact (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)]. intros b Hb. apply (Permutation_in _ (Permutation_sym PS)). apply in_or_app; left; exact Hb. }

    assert (TRd : trace_ok (as_TR H) APC0_FREE [emp_del_ra EMP_U32]).
    { pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR. exact (proj1 (Forall_forall _ _) TR 0xfad2c ltac:(cbn; tauto)). }

    change (fsz PM_FCLASS) with 16384 in *.
    assert (AKk : accessible m (wa_ff w + sok) 4) by exact Hokk.
    assert (FKk : fldA m (wa_ff w + sok) 4 key).
    { pose proof (fld_of_cell4 m (wa_ff w + sok) (Z_to_bv 64 key) RWk ltac:(lia)) as FL. rewrite HLib.u64_of_Z in FL by lia. exact FL. }
    assert (ESRC : forall so n, 0 <= so -> so + n <= 15616 -> 0 <= n <= 8 -> emp_src H LBk (wa_s1 w) (wa_p w + O_M1) (wa_ff w + so) n).
    { intros so n Hso Hson Hn. split; [| split].
      - right; right; right; right; left. clear - F1 F2 Hso Hson Hn. unfold AFS_HDR in *. lia.
      - right; right; right; right; right; left. split; [apply sh_mono; clear - F1 Hso; unfold AFS_HDR in *; lia|].
        assert (sh (wa_ff w + so) + nsh n <= sh (wa_ff w + so + 16)) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
        assert (sh (wa_ff w + so + 16) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; clear - F2 Hson Hn; lia). lia.
      - unfold apart. unfold O_M1, PARSER_SIZE in *. clear - PFF Hso Hson Hn. lia. }

    pose proof (pm_phi_le_cap c) as PCc.
    assert (AL0 : 0 <= as_AL H s) by (unfold PM_RESERVE in *; clear - A1 A2 A3 PCc; lia).
    assert (RICM : (bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s).
    { intros CASE.
      pose proof (bud_emp_m1 (wa_n w) c bl bc ents 1 (bseq_next bc) ((1, (key, 0)) :: ents) BUD Em1 Hbs Hlast ACC
                    ltac:(unfold Zlength; cbn [length]; lia) (or_intror (conj CASE eq_refl))) as BUDg.
      pose proof (pm_resv_of_bud (wa_n w) _ WN BUDg) as RESVg.
      pose proof (phi_rehash_m1 c bl bc ents 1 ((1, (key, 0)) :: ents) Em1 Hbs Hlast) as PG.
      match type of RESVg with pm_cap ?cc + _ <= _ => pose proof (pm_phi_le_cap cc) as PCg end.
      clear - A1 A3 RESVg PG PCg. unfold PM_RESERVE in *. lia. }
    pose proof (pmxa_meas_LB H LINV w s LB LBs m mo c ins tbl ftbl [] 0 OK X) as (M1 & M2 & M3).
    pose proof (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl [] 0 OK X) as (M4 & M5).
    pose proof (nsmall_bounds (8 * bseq_next bc) ltac:(lia)) as NSB. pose proof (nlg_bounds (8 * bseq_next bc)) as NLB.

    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H HH).
    { eapply (emh_u32_ok H HHbp) with (obj := wa_p w + O_M1) (keyp := wa_ff w + sok)
        (key := key) (bl := bl) (bc := bc) (ents := ents) (LB := LB) (LB0 := LBk) (LBm := LBm) (LF := PMLF H w)
        (lo := wa_lo w) (B := wa_B w) (shi := wa_shi w) (errv := errv) (s := s) (m := m) (mo := mo);
      [ exact VIS | exact FRZ | exact G10 | exact G11
      | exact U | exact SH1 | exact PE | rewrite ELm; apply Permutation_refl
      | apply (pw_addr_sub8 m (wa_p w) PARSER_SIZE O_M1 40 ADp); unfold O_M1, PARSER_SIZE; try reflexivity; lia
      | apply (wr_at_of_mdef m (wa_p w) PARSER_SIZE O_M1 40 (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)); unfold O_M1, PARSER_SIZE; lia
      | exists fp0; split; [right; exact Hfp0 | unfold O_M1, PARSER_SIZE in *; lia]
      | unfold O_M1, PARSER_SIZE in *; lia
      | intros b Hb; pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (_ & _ & _ & _ & _ & RFb & _); unfold AFS_HDR, O_M1, PARSER_SIZE in *; clear - RFb PF1 PF2 PF3 PF4; lia
      | exact FKk | exact AKk | rewrite G2, u64_of_Z by lia; apply ESRC; lia
      | apply emhb1_kfr; lia
      | clear - Q2 Hk4; Z.div_mod_to_equations; lia
      | exact Hkey
      | clear - ACC WN; unfold Zlength in *; lia | exact Hlast
      | exact RH | exact KR | exact AL0
      | clear - M4 NSB; unfold nsmall in *; destruct (Z.leb_spec (8 * bseq_next bc) 64512); lia | exact M2 | clear - M5 NLB; lia
      | exact RICM | exact TRd
      | exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G2, u64_of_Z by lia; lia | exact B64
      | rewrite G2, u64_of_Z by lia; clear - Q12; Z.div_mod_to_equations; lia
      | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia)))
      | lia | rewrite G2, u64_of_Z by lia; exact (emhb1_stk w OK)
      | rewrite G4; exact ERR | exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | rewrite G4; exact (wk_tp H w OK)
      | rewrite G1, u64_of_Z by lia; exact Hr2
      | exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
      | exact (emhb1_lfb w OK) | exact (LINV_relro m (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)) | exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
      | rewrite G2, u64_of_Z by lia; lia
      | exact OWNm ]. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB' & LBm' & F' & fc' & p & v & bl' & bc'
                      & ents' & inserted & rehashed & XS & POST).
    cbv zeta in POST.
    destruct POST as (VIS1 & FRZ1 & KR1 & MP1 & MI1 & ST1 & ER1 & RA1 & U1 & SH1' & AD1 & WR1 & Hin & NINS & INS & NRH & RHD & RH1 & PE1 & PM1 & OW1 & FXS & XP1 & RF1 & AC1' & S01 & AL1).
    cbn [cfg_ms cfg_model] in VIS1, KR1, MP1.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in ST1 by lia. rewrite G4 in ER1. rewrite G2, u64_of_Z in XP1 by lia.

    pose proof U1 as U1d. destruct U1d as [_ _ _ _ Ubseq' Uload' _ _ _ _ _ _ _ _ Unode' _].
    assert (LEN : Zlength ents <= Zlength ents' <= Zlength ents + 1).
    { destruct inserted.
      - pose proof (Permutation_length (proj2 (INS eq_refl))) as E. unfold Zlength. rewrite E. cbn [length]. lia.
      - destruct (NINS eq_refl) as [-> _]. lia. }
    assert (CASE : bc' = bc \/ ((bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc)).
    { destruct rehashed; [right; exact (RHD eq_refl) | left; exact (proj2 (NRH eq_refl))]. }
    assert (BUD1 : pm_bud (wa_n w) (set_m1A c (bl', bc', ents'))) by exact (bud_emp_m1 (wa_n w) c bl bc ents bl' bc' ents' BUD Em1 Hbs Hlast ACC (proj2 LEN) CASE).
    assert (X1 : PMXA H LINV w s1 LB' (LBm' ++ LBr) m1 mo1 (set_m1A c (bl', bc', ents')) ins tbl ftbl).
    { eapply (emhb1_pmxa w s LB LBs m mo c ins tbl ftbl s1 m1 mo1 LB' LBm LBr LBm' XS bl bc ents bl' bc' ents' rehashed errv1);
        [ exact OK | exact X | exact Hknn | exact Hfk | exact Em1 | exact PS | exact ELr | exact BUD1
        | exact NRH | intros Hrh; exact (proj2 (RHD Hrh)) | exact Hbs | exact Hlast
        | exact RH1 | exact PE1 | exact PM1 | exact MP1 | exact MI1 | exact ST1 | exact ER1 | exact RA1
        | exact FXS | exact XP1 | exact U1 | exact SH1' | exact WR1 | exact RF1 | exact AC1' | exact S01 | exact AL1 ]. }
    destruct (Unode' p key v Hin) as (_ & _ & _ & _ & _ & _ & _ & NV & _). pose proof (proj1 NV) as Rv. cbn in Rv.
    eapply (K ms1 mo1 m1 s1 LB' (LBm' ++ LBr) F' fc' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' p v (bl', bc', ents') inserted);
      [ exact KR1 | exact VIS1 | exact FRZ1 | exact X1 | exact Hin | exact Rv | cbn [t3c snd]; exact LEN
      | intros Hf; cbn [t3c snd]; exact (proj1 (NINS Hf)) | intros Ht; cbn [t3c snd]; exact (INS Ht) | exact BUD1
      | cbn [t3a t3b t3c fst snd]; exact CASE | cbn [t3a t3b t3c fst snd]; exact Hbs | cbn [t3a t3b t3c fst snd]; exact Hlast |].

    intros k cs Hk Hkc RWc. eapply (ff_cells_xpres H HHbp w m m1 LBk (mx1 H w) XS k cs); [exact OK | exact RF1 | exact FXS | exact XP1 | | exact Hk | exact Hkc | exact RWc].
    unfold mx1. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold O_M1, PARSER_SIZE in *. clear - PFF Hk Hkc. lia.
  Qed.
End EMHB.
