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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require ContLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_ContStmt LbB_DiagStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmDS LbB_PmVup LbB_PmWKit LbB_PmWG LbB_PmWPT LbB_SegKit LbB_StrPb LbB_MkStr.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition set_trA (c : pmc) (tr : list (Z * Z)) : pmc :=
  {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
     c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := tr |}.

Definition tr_of (sb : sbuf) : list (Z * Z) := match sb with SShort => [] | SLong d asz => [(d, asz)] end.

Lemma set_trA_id : forall c, set_trA c (c_tr c) = c.
Proof. intros []; reflexivity. Qed.
Lemma set_trA_twice : forall c tr tr', set_trA (set_trA c tr) tr' = set_trA c tr'.
Proof. intros c tr tr'. reflexivity. Qed.

Lemma c_blocks_set_tr : forall c tr, c_tr c = [] -> c_blocks (set_trA c tr) = c_blocks c ++ tr.
Proof.
  intros c tr Htr. unfold c_blocks, set_trA. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr]. rewrite Htr, app_nil_r.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma c_blocks_tr_perm : forall c tr, Permutation (c_blocks (set_trA c tr)) (tr ++ c_blocks (set_trA c [])).
Proof.
  intros c tr. change (set_trA c tr) with (set_trA (set_trA c []) tr).
  rewrite (c_blocks_set_tr (set_trA c []) tr eq_refl). apply Permutation_app_comm.
Qed.

Lemma pm_phi_tr_of : forall sb, pm_phi_blocks (tr_of sb) = match sb with SShort => 0 | SLong _ asz => if 64512 <? asz then 8 * asz else 0 end.
Proof.
  intros [|d asz]; [reflexivity|]. unfold tr_of, pm_phi_blocks, ICM_LARGE. cbn [fold_right snd].
  destruct (Z.ltb_spec 64512 asz); lia.
Qed.

Lemma pm_phi_set_tr : forall c tr, c_tr c = [] -> pm_phi (set_trA c tr) = pm_phi c + pm_phi_blocks tr.
Proof. intros c tr Htr. apply pm_phi_eq_blocks; [reflexivity|]. rewrite (c_blocks_set_tr c tr Htr). apply pm_phi_blocks_app. Qed.

Lemma pm_bud_set_tr : forall n c tr, pm_bud n c -> HRep.Zlength tr <= 2 -> (forall b, In b tr -> 0 < snd b <= 2 ^ 28) ->
  pm_bud n (set_trA c tr).
Proof.
  intros n c tr B HL HP. unfold pm_bud in *. unfold set_trA. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr].
  destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & _ & _).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
  split; [exact B7|]. split; [exact HL | exact HP].
Qed.

Lemma pm_bud_tr_of : forall n c sb, pm_bud n c -> (forall d asz, sb = SLong d asz -> 0 < asz <= 2 ^ 28) ->
  pm_bud n (set_trA c (tr_of sb)).
Proof.
  intros n c sb B HS. apply pm_bud_set_tr; [exact B | |].
  - destruct sb; unfold tr_of, HRep.Zlength; cbn [length]; lia.
  - intros b Hb. destruct sb as [|d asz]; cbn [tr_of In] in Hb; [contradiction|]. destruct Hb as [<-|[]]. cbn [snd].
    exact (HS d asz eq_refl).
Qed.

Lemma cblocks_phi_notr : forall n c, 0 <= n -> pm_bud n c -> c_tr c = [] ->
  bsum phi1 (c_blocks c) <= 24 * n + 3 * 4096 + 2 ^ 23 + 2 ^ 20 + 2 ^ 26.
Proof.
  intros n c Hn B Htr.
  destruct B as ((Bn1 & Bn2 & Bn3) & Bb1 & Bb2 & Bb3 & Bv1 & Bv2 & Bv3 & Btr & Btrp).
  unfold c_blocks, vec_opnd_blocks. rewrite Htr, app_nil_r. rewrite !bsum_app.
  destruct (umap_blocks_meas 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ltac:(lia) ltac:(lia)) as (_ & _ & _ & P1).
  destruct (umap_blocks_meas 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) ltac:(lia) ltac:(lia)) as (_ & _ & _ & P2).
  destruct (umap_blocks_meas 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ltac:(lia) ltac:(lia)) as (_ & _ & _ & P3).
  destruct (opt_block_meas (t3a (c_v1 c) =? 0) (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c)) ltac:(lia)) as (_ & _ & _ & P4).
  destruct (opt_block_meas (t3a (c_v2 c) =? 0) (t3a (c_v2 c)) (4 * t3c (c_v2 c)) ltac:(lia)) as (_ & _ & _ & P5).
  destruct (opt_block_meas (t3a (c_v3 c) =? 0) (t3a (c_v3 c)) (4 * t3c (c_v3 c)) ltac:(lia)) as (_ & _ & _ & P6).
  lia.
Qed.

Lemma pm_phi_notr : forall n c, 0 <= n < 2 ^ 24 -> pm_bud n c -> c_tr c = [] -> pm_phi c + 2 ^ 33 <= po_cost n.
Proof.
  intros n c Hn B Htr. pose proof (cblocks_phi_notr n c ltac:(lia) B Htr) as P. pose proof (pm_prog_bounds c) as PB.
  unfold pm_phi. rewrite pm_phi_blocks_bsum. unfold po_cost. lia.
Qed.

Section FW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma ffwin_obj : forall (w : pmwA H) LB ko n, pmw_okA H w ->
    24 <= ko -> ko + n <= 16376 -> 0 <= n -> ko mod 8 = 0 -> n mod 8 = 0 ->
    obj_win H LB (PMLF H w) (wa_s1 w) (wa_lo w) (wa_ff w + ko) n.
  Proof.
    intros w LB ko n OK H0 H1 Hn H8 Hn8.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    change (fsz PM_FCLASS) with 16384 in *.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (FA : aapp (wa_ff w) 16384) by (eapply aapp_sub; [exact F8 | unfold AFS_HDR in *; lia | unfold AFS_HDR in *; lia]).
    assert (A8 : (wa_ff w + ko) mod 8 = 0) by (clear - Q2 H8; Z.div_mod_to_equations; lia).
    unfold obj_win. unfold AFS_HDR in *.
    split; [right; right; right; right; left; lia|].
    split.
    { right; right; right; right; right; left. split.
      - apply sh_mono. lia.
      - rewrite (pw_sh_add (wa_ff w + ko) n A8 Hn8). apply sh_mono. lia. }
    split; [right; right; right; right; left; cbn [fst snd]; lia|].
    split.
    { right. exists (PM_FCLASS, wa_ff w, wa_fp w). split; [left; reflexivity|].
      unfold ff_addr, ff_class. cbn [fst snd]. change (fsz PM_FCLASS) with 16384. lia. }
    split.
    { destruct FA as [(L1 & L2)|(L1 & L2)].
      - apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
          AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
          replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity;
          unfold aapp_lo, AIMG_TOP, ALOWSH_LO in *; lia.
      - apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
          AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
          replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity;
          unfold aapp_hi, AHI_LO in *; lia. }
    left. lia.
  Qed.

  Lemma ffwin_band : forall (w : pmwA H) ko n, pmw_okA H w -> 0 <= ko -> ko + n <= 16384 -> 0 <= n ->
    (0x6e8000 <= wa_ff w + ko /\ wa_ff w + ko + n <= 0x7fff7000) \/ (0x10007fff8000 <= wa_ff w + ko /\ wa_ff w + ko + n <= 2 ^ 47).
  Proof.
    intros w ko n OK H0 H1 Hn.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    change (fsz PM_FCLASS) with 16384 in *.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (FA : aapp (wa_ff w) 16384) by (eapply aapp_sub; [exact F8 | unfold AFS_HDR in *; lia | unfold AFS_HDR in *; lia]).
    destruct FA as [(L1 & L2)|(L1 & L2)]; unfold aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in *; [left | right]; lia.
  Qed.
End FW.

Section MK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.

  Let HH : asan_rt_hyps H := proj1 HHbp.

  Lemma pmxa_after_mkstr : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' (sb : sbuf) (pid : bptr) LB' (ko : Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    c_tr c = [] -> pm_bud (wa_n w) c ->
    24 <= ko -> ko + 24 <= 16376 -> Forall (fun ke : Z * SymExec3.SX2.expr => ko + 24 <= fst ke \/ fst ke + 8 <= ko) ftbl ->
    as_RHEAP H s' LB' m' -> as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) -> as_rauxv_ok H m' (wa_B w) ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) ->
    xpres H LB (wa_s1 w) [(wa_ff w + ko, wa_ff w + ko + 24)] m m' ->
    wr_at asegs m' (wa_ff w + ko) 24 ->
    match sb with
    | SShort => LB' = LB
    | SLong d asz => LB' = (pid, d, asz) :: LB /\ 0 < asz <= 2 ^ 28
    end ->
    as_AL H s' >= as_AL H s - pm_phi_blocks (tr_of sb) ->
    PMXAT H LINV w s' LB' (spb_own sb pid ++ LBs) m' mo' (set_trA c (tr_of sb)) ins tbl ftbl TB spal
    /\ pm_bud (wa_n w) (set_trA c (tr_of sb)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' m' mo' sb pid LB' ko OK X0 Hknn Hfk Htr BUD K0 K1 FTD
           RH' MP' MI' STK' ERR' RA' RFS' AC' S0' XP WR' CASE AL.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [TBO TBL].
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    assert (BUD' : pm_bud (wa_n w) (set_trA c (tr_of sb))).
    { apply pm_bud_tr_of; [exact BUD|]. intros d asz E. subst sb. exact (proj2 CASE). }
    split; [| exact BUD'].
    assert (Is : forall b, In b LBs -> In b LB) by (intros b Hb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; left; exact Hb).
    assert (It : forall b, In b TB -> In b LB) by (intros b Hb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; right; exact Hb).
    assert (I0 : forall b, In b (wa_LB0 w) -> In b LB) by (intros b Hb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; left; exact Hb).
    assert (IL : forall b, In b LB -> In b LB').
    { intros b Hb. destruct sb as [|d asz]; [rewrite CASE; exact Hb | rewrite (proj1 CASE); right; exact Hb]. }
    set (X := [(wa_ff w + ko, wa_ff w + ko + 24)]).
    assert (FXD : Forall (xp_ok H w ftbl) X).
    { apply Forall_cons; [| apply Forall_nil]. unfold xp_ok. left. cbn [fst snd]. split; [lia|]. split; [lia|]. split; [lia|].
      eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia. }
    assert (XP' : xpres H LB (wa_s1 w) (X ++ []) m m') by (rewrite app_nil_r; exact XP).
    assert (FXS : Forall (fs_scratch H (PMLF H w)) []) by apply Forall_nil.
    destruct (pmc_xp_keep H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal LB' m' LB X [] OK X0 RFS' FXS XP' FXD Is
                (fun b Hb => IL b (Is b Hb))) as (U1 & U2 & U3 & V1 & V2 & V3 & SHc).
    assert (OWN' : lb_own LB' m') by exact (HOWN s' LB' m' RH').
    assert (LI' : LINV m').
    { apply (LINV_cl m m' (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)).
      apply (xpres_img H LB (wa_s1 w) X m m' XP).
      apply Forall_cons; [cbn [fst]; unfold AFS_HDR in *; lia | apply Forall_nil]. }
    eapply (pmxa_xp H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal s' LB' (spb_own sb pid ++ LBs) m' mo' (set_trA c (tr_of sb)) TB spal LB X []
              OK X0 Hknn RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP' FXD); try reflexivity.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (wa_ff w + ko + 24 - (wa_ff w + ko)) with 24 by lia. exact WR'.
    - exact Hfk.
    - intros b Hb; exact Hb.
    - exact I0.
    -
      destruct sb as [|d asz]; cbn [spb_own app].
      + rewrite CASE. exact OWN1.
      + rewrite (proj1 CASE). eapply Permutation_trans; [apply perm_skip; exact OWN1|].
        apply Permutation_middle.
    -
      rewrite (c_blocks_set_tr c (tr_of sb) Htr).
      destruct sb as [|d asz]; cbn [spb_own tr_of app]; [rewrite app_nil_r; exact OWN2|].
      unfold lbl in *. cbn [map blk_addr blk_size fst snd].
      eapply Permutation_trans; [apply perm_skip; exact OWN2|]. apply Permutation_cons_append.
    - apply (lb_own_incl LB' _ m'); [| exact OWN'].
      intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (IL b (Is b Hb))].
      destruct sb as [|d asz]; cbn [spb_own In] in Hb; [contradiction|]. destruct Hb as [<-|[]]. rewrite (proj1 CASE). left. reflexivity.
    - apply (pm_meas_of_bud (wa_n w) (set_trA c (tr_of sb)) _ ltac:(lia) BUD').
      rewrite (c_blocks_set_tr c (tr_of sb) Htr).
      destruct sb as [|d asz]; cbn [spb_own tr_of app]; [rewrite app_nil_r; exact OWN2|].
      unfold lbl in *. cbn [map blk_addr blk_size fst snd].
      eapply Permutation_trans; [apply perm_skip; exact OWN2|]. apply Permutation_cons_append.
    - apply (lb_own_incl LB' _ m'); [| exact OWN']. intros b Hb. exact (IL b (It b Hb)).
    - exact TBL.
    - rewrite (pm_phi_set_tr c (tr_of sb) Htr). lia.
    - apply pm_resv_of_bud; [exact WN | exact BUD'].
    - exact A4.
    - exact U1.
    - exact U2.
    - exact U3.
    - exact V1.
    - exact V2.
    - exact V3.
    - exact SHc.
  Qed.

  Lemma mdef_wordsA : forall m (k : nat) a, mdef m a (4 * Z.of_nat k) -> 0 <= a -> a + 4 * Z.of_nat k < 2 ^ 64 ->
    exists ws : list Z, Zlen ws = Z.of_nat k /\ forall i, 0 <= i < Z.of_nat k -> 0 <= Znth i ws < 2 ^ 32 /\ fld ASEGS m (a + 4 * i) 4 (Znth i ws).
  Proof.
    intros m k. induction k as [|k IH]; intros a HD Ha Hhi.
    - exists []. split; [reflexivity | intros i Hi; lia].
    - destruct (IH a ltac:(eapply ContLib.mdef_sub; [exact HD | lia | lia]) Ha ltac:(lia)) as (ws & Hlen & Hws).
      destruct (TablLib.mdef4_fld ASEGS m (a + 4 * Z.of_nat k) ltac:(eapply ContLib.mdef_sub; [exact HD | lia | lia]) ltac:(lia) ltac:(lia)) as (v & Rv & Fv).
      exists (ws ++ [v]). split; [rewrite CRep.Zlen_app1; lia|].
      intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat k)) as [Hlt|Hge].
      + rewrite CRep.Znth_app_l by lia. apply Hws. lia.
      + assert (i = Zlen ws) as -> by lia. rewrite CRep.Znth_app_r1. replace (Zlen ws) with (Z.of_nat k) by lia. split; [lia | exact Fv].
  Qed.

  Lemma pm_words_keep : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal (ko i0 : Z) (ws : list Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> wa_words w <> 0 ->
    0 <= i0 -> Zlen ws = wa_n w - i0 -> 24 <= ko -> ko + 24 <= 16376 ->
    (forall i, 0 <= i < Zlen ws -> fld ASEGS m (wa_words w + 4 * i0 + 4 * i) 4 (Znth i ws)) ->
    ms_words_keep H LB (wa_s1 w) (wa_ff w + ko) m (wa_words w + 4 * i0) (Zlen ws) ws.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal ko i0 ws OK X0 Hw Hi0 Hlen K0 K1 FW m' AC' MI' XP.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (ZL : 0 <= Zlen ws) by apply CRep.Zlen_nonneg.
    assert (HinLB : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)))). apply in_app_iff. left. exact Hin. }
    pose proof (blk_apart_ff H HH w s LB m _ OK RH HinLB) as AP. cbn [blk_addr blk_size fst snd] in AP.
    destruct (blksh_apart_ff H HH w s LB m pw (wa_words w) k OK RH HinLB) as [APS _].
    pose proof (ah_blocks H HH _ _ _ _ RH HinLB) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    assert (Hk : 0 < k \/ wa_n w = 0) by lia.
    split.
    - intros i Hi. eapply (xpres_fld H); [exact XP | exact (FW i Hi) | | lia | lia].
      apply (xr_blk H w LB _ (pw, wa_words w, k)); [exact HinLB | cbn [blk_addr fst snd]; lia | cbn [blk_addr blk_size fst snd]; lia |].
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
    - destruct (Z.eq_dec (Zlen ws) 0) as [Z0|ZN].
      { rewrite Z0. apply accessible_nil. unfold AAPP_HI. lia. }
      assert (Hk0 : 0 < k) by lia.
      assert (Hl : Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * wa_n w))) = nsh k) by (apply cc_gen_length; lia).
      pose proof (pmx_words_sh H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal pw k _ OK X0 Hin Hk0 Hl Wsh) as SH.
      assert (SH' : SHAD m' (wa_words w) (LbB_PrsStmt.cc_gen k (4 * wa_n w))).
      { eapply (xpres_SHAD H); [exact XP | exact SH |]. rewrite Hl.
        apply (xr_blksh H w LB _ (pw, wa_words w, k)); [exact HinLB | cbn [blk_addr fst snd]; lia | cbn [blk_addr blk_size fst snd]; lia |].
        apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
      unfold LbB_PrsStmt.cc_gen in SH'. apply SHAD_app in SH'. destruct SH' as [SH1 _].
      apply (addressable_accessible m' (wa_words w) (4 * wa_n w)); [split; [lia | exact SH1] | lia | lia | unfold AAPP_HI; lia].
  Qed.

  Lemma pm_mkstr : mkstr_stmtA H ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl msF R F fc (ret ko : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c ins tbl ftbl ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    c_tr c = [] -> pm_bud (wa_n w) c -> wa_words w <> 0 ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 MKSTR_ENTRY) fc None m (seg_rom asegs) -> rfull R ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + ko) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_words w + 4 * c_widx c) ->
    PropExec.getr R 12%bv = Z_to_bv 64 (wa_n w - c_widx c) ->
    obj_sh_ok ins ko 24 = true -> 24 <= ko -> ko + 24 <= 16376 -> ko mod 8 = 0 ->
    Forall (fun ke : Z * SymExec3.SX2.expr => ko + 24 <= fst ke \/ fst ke + 8 <= ko) ftbl ->
    (forall msF1 mo1 m1 R1 (s1 : as_St H) (LB1 : list block) (sb : sbuf) (pid : bptr) (ws : list Z),
       as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F (Z_to_bv 64 ret) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s1 LB1 (spb_own sb pid ++ LBs) m1 mo1 (set_trA c (tr_of sb)) ins tbl ftbl ->
       pm_bud (wa_n w) (set_trA c (tr_of sb)) ->
       (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
       Zlen ws = wa_n w - c_widx c ->
       strA LB1 m1 (wa_ff w + ko) sb (ms_chars ws) -> spb_blk LB1 m1 sb pid ->
       (match sb with
        | SShort => True
        | SLong d asz => In (pid, d, asz) LB1 /\ ~ In pid (map blk_id LB) /\ 48 <= asz <= 2 ^ 28 /\ (asz = 48 \/ asz <= 2 * Zlen (ms_chars ws))
                         /\ Zlen (ms_chars ws) <= 4 * (wa_n w - c_widx c)
        end) ->
       (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
          (k + Z.of_nat (cells_size cs) <= ko \/ ko + 24 <= k) ->
          rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HMS w s LB LBs m mo c ins tbl ftbl msF R F fc ret ko Q OK X Hknn Hfk Htr BUD Hw KR VIS RF
           G1 Hr2 Hr G2 G4 G10 G11 G12 Oko K0 K1 K8 FTD K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (wk_s1 H w OK) as [T1 T2].
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4).
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SC1 & SC2 & SC3 & SC4).
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK0.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK0 ltac:(lia)) as [STK1 STK2].
    destruct (wk_words H w OK) as [[E0 _]|(pw & kw & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    set (nw := wa_n w - c_widx c).
    assert (NW : 0 <= nw < 2 ^ 24) by (unfold nw; lia).

    destruct (mdef_wordsA m (Z.to_nat nw) (wa_words w + 4 * c_widx c)
                ltac:(rewrite Z2Nat.id by lia; eapply ContLib.mdef_sub; [exact (xa_wbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Hw) | lia | unfold nw; lia])
                ltac:(lia) ltac:(rewrite Z2Nat.id by lia; unfold nw; lia)) as (ws & Hlen & WS).
    rewrite Z2Nat.id in Hlen, WS by lia.
    assert (WK : ms_words_keep H LB (wa_s1 w) (wa_ff w + ko) m (wa_words w + 4 * c_widx c) (Zlen ws) ws).
    { apply (pm_words_keep w s LB LBs m mo c ins tbl ftbl [] 0 ko (c_widx c) ws OK X Hw ltac:(lia) Hlen K0 K1).
      intros i Hi. rewrite Hlen in Hi. exact (proj2 (WS i Hi)). }

    assert (ADo : addressable m (wa_ff w + ko) 24) by exact (ff_addressable m (wa_ff w) ins ko 24 (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) Oko).
    assert (WRo : wr_at asegs m (wa_ff w + ko) 24).
    { eapply (wr_at_sub asegs m (wa_ff w) (fsz PM_FCLASS)); [exact (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | change (fsz PM_FCLASS) with 16384; lia | lia]. }

    pose proof (pmw_meas_LB3 H LINV w s LB LBs m mo c ins tbl ftbl [] 0 OK X) as (M1 & M2 & M3).
    pose proof (pm_phi_notr (wa_n w) c WN BUD Htr) as PHI.
    destruct (rt_bp_cost H HHbp) as [CFz CMz].
    assert (CST : ms_cost H (Zlen ws) <= as_AL H s).
    { unfold ms_cost. rewrite CFz, CMz. unfold ICM. destruct (Z.leb_spec (16 * Zlen ws + 96) 64512); lia. }
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H HH).
    { eapply (HMS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (PMLF H w)
                (wa_ff w + ko) (wa_words w + 4 * c_widx c) ws (wa_lo w) (wa_B w) (wa_shi w) errv).
      - exact VIS.
      - exact G10.
      - exact G11.
      - rewrite Hlen. exact G12.
      - lia.
      - intros i Hi. rewrite Hlen in Hi. exact (proj1 (WS i Hi)).
      - clear - W16. Z.div_mod_to_equations. lia.
      - lia.
      - lia.
      - rewrite G2, u64_of_Z by lia. exact WK.
      - clear - Q2 K8. Z.div_mod_to_equations. lia.
      - exact ADo.
      - exists (PM_FCLASS, wa_ff w, wa_fp w). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz PM_FCLASS) with 16384. lia.
      - rewrite G2, u64_of_Z by lia. apply (ffwin_obj H w LB ko 24 OK K0 K1 ltac:(lia) K8 eq_refl).
      - exact (ffwin_band H w ko 24 OK ltac:(lia) ltac:(lia) ltac:(lia)).
      - exact WRo.
      - exact (HOWN s LB m RH).
      - exact RH.
      - exact KR.
      - exact M1.
      - exact M2.
      - exact M3.
      - exact CST.
      - exact (proj1 (Forall_forall _ _) (wk_tr H w OK) SPB_DEL_RA ltac:(cbn; tauto)).
      - exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - rewrite G2, u64_of_Z by lia. lia.
      - rewrite G2, u64_of_Z by lia. clear - T2. Z.div_mod_to_equations. lia.
      - rewrite G2, u64_of_Z by lia. lia.
      - rewrite G2, u64_of_Z by lia. exact STK1.
      - exact S1.
      - rewrite G2, u64_of_Z by lia. unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK, APM_STACK in *. lia.
      - rewrite G4. exact ERR.
      - exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - rewrite G4. exact (wk_tp H w OK).
      - exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
      - rewrite G2, u64_of_Z by lia. lia. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & sb & pid & VIS1 & KR1 & MP1 & MI1 & STKa & ERR1 & RA1 & XP & RH1 & REP1 & BLK1 & CASE & AD1 & WR1 & OW1
                      & RFS1 & AC1x & S01 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STKa, XP by lia. rewrite G4 in ERR1.
    assert (STK1' : stk asegs m1 (wa_lo w) (wa_s1 w)) by exact STKa.
    assert (CASE' : match sb with SShort => LB1 = LB | SLong d asz => LB1 = (pid, d, asz) :: LB /\ 0 < asz <= 2 ^ 28 end).
    { destruct sb as [|d asz]; [exact CASE|]. destruct CASE as (E & NI & ABR & BZ & BL). split; [exact E|].
      destruct (strA_long_facts _ _ _ _ _ _ REP1) as (_ & _ & _ & AM & AMIN & _). rewrite Hlen in BL. unfold SSO_CAP in *. lia. }
    assert (ALp : as_AL H s1 >= as_AL H s - pm_phi_blocks (tr_of sb)).
    { rewrite pm_phi_tr_of. unfold ms_phi in AL1. exact AL1. }
    destruct (pmxa_after_mkstr w s LB LBs m mo c ins tbl ftbl [] 0 s1 m1 mo1 sb pid LB1 ko OK X Hknn Hfk Htr BUD K0 K1 FTD
                RH1 MP1 MI1 STK1' (ex_intro _ errv1 ERR1) RA1 RFS1 AC1x S01 XP WR1 CASE' ALp) as [X1 BUD1].
    eapply (K ms1 mo1 m1 _ s1 LB1 sb pid ws); [exact KR1 | exact VIS1 | apply rfull_mkR | exact X1 | exact BUD1 | | exact Hlen | exact REP1 | exact BLK1 | |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - destruct sb as [|d asz]; [exact I|]. destruct CASE as (E & NI & ABR & BZ & BL). split; [rewrite E; left; reflexivity|]. split; [exact NI|].
      destruct (strA_long_facts _ _ _ _ _ _ REP1) as (_ & _ & _ & AM & AMIN & _). rewrite Hlen in BL. unfold SSO_CAP in *.
      split; [split; [clear - AM AMIN; Z.div_mod_to_equations; lia | lia] | split; [exact BZ | exact BL]].
    - intros k cs Hk Hkc Hdj RW.
      eapply (ff_cells_xpres H HHbp w m m1 LB [(wa_ff w + ko, wa_ff w + ko + 24)] [] k cs OK RFS1 (Forall_nil _)); [rewrite app_nil_r; exact XP | | exact Hk | exact Hkc | exact RW].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.
End MK.
