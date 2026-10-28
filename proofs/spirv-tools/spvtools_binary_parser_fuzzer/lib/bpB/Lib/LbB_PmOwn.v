(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Own.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Record pmw_okA (w : pmwA H) : Prop := PMW_OKA {
    wk_fresh : fresh_frame H (wa_LF0 w) PM_FCLASS (wa_ff w) (wa_fp w);
    wk_pobj  : fsobj H (wa_LF0 w) (wa_p w) PARSER_SIZE;

    wk_pin   : exists f, In f (wa_LF0 w) /\ ff_addr f <= wa_p w /\ wa_p w + PARSER_SIZE <= ff_addr f + fsz (ff_class f);
    wk_papp  : aapp (wa_p w) PARSER_SIZE /\ 0 < wa_p w /\ wa_p w mod 16 = 0;
    wk_cobj  : fsobj H (wa_LF0 w) (wa_cons w) 48;
    wk_capp  : aapp (wa_cons w) 48 /\ 0 < wa_cons w /\ wa_cons w mod 16 = 0;
    wk_pcons : wa_p w + PARSER_SIZE <= wa_cons w \/ wa_cons w + 48 <= wa_p w;

    wk_cin   : exists f, In f (wa_LF0 w) /\ ff_addr f <= wa_cons w /\ wa_cons w + 48 <= ff_addr f + fsz (ff_class f);

    wk_chfr  : forall fp ra, In (fp, ra) (wa_CH w) -> wa_sp0 w + 16 <= fp;
    wk_ra    : 0 <= wa_ra w < 2 ^ 64;

    wk_meas0 : lb_small (wa_LB0 w) + po_small (wa_n w) <= RT_SMALL_MAX /\ Z.of_nat (length (wa_LB0 w)) + po_cnt (wa_n w) <= RT_CNT_MAX
               /\ nlarge (wa_LB0 w) + po_large (wa_n w) <= RT_LARGE_MAX;
    wk_stack : aceil <= wa_lo w /\ wa_lo w <= wa_sp0 w - APM_STACK /\ wa_sp0 w mod 16 = 0
               /\ wa_sp0 w <= wa_shi w /\ wa_shi w <= AAPP_HI /\ wa_sp0 w <= wa_B w;
    wk_s1    : wa_sp0 w - 864 <= wa_s1 w <= wa_sp0 w - 832 /\ wa_s1 w mod 32 = 0;
    wk_tp    : wa_tp w = Z_to_bv 64 ATP;
    wk_rfs0  : as_RFS H (wa_LF0 w) (wa_m0 w);
    wk_words : (wa_words w = 0 /\ wa_n w = 0) \/ words_okA (wa_LB0 w) (wa_m0 w) (wa_words w) (wa_n w);
    wk_n     : 0 <= wa_n w < 2 ^ 24;
    wk_saved : length (wa_saved w) = 13%nat;

    wk_lfb   : (length (wa_LF0 w) + PM_FRAMES <= AFS_MAXLIVE_BP)%nat;
    wk_B64   : wa_B w < 2 ^ 64;

    wk_diag  : 0 <= wa_diag w < 2 ^ 64;

    wk_tr    : pm_tr_ok H;
    wk_pf    : pf_ok (as_TR H) PM_PF (wa_ra w) (wa_CH w)
  }.

  Definition own_ivl (w : pmwA H) (iv : Z * Z) : Prop :=
    (wa_lo w <= fst iv /\ snd iv <= wa_sp0 w - 104)
    \/ (wa_ff w + 24 <= fst iv /\ snd iv <= wa_ff w + fsz PM_FCLASS - 8)
    \/ (sh (wa_ff w) <= fst iv /\ snd iv <= sh (wa_ff w) + PM_NSH)
    \/ (wa_p w + O_WIDX <= fst iv /\ snd iv <= wa_p w + O_FLAGS + 2).

  Definition own_apart (w : pmwA H) (a n : Z) : Prop :=
    forall iv, own_ivl w iv -> a + n <= fst iv \/ snd iv <= a.

  Definition own_ivl3 (w : pmwA H) (iv : Z * Z) : Prop :=
    (wa_lo w <= fst iv /\ snd iv <= wa_sp0 w - 104)
    \/ (wa_ff w + 24 <= fst iv /\ snd iv <= wa_ff w + fsz PM_FCLASS - 8)
    \/ (sh (wa_ff w) <= fst iv /\ snd iv <= sh (wa_ff w) + PM_NSH).
  Definition own_apart3 (w : pmwA H) (a n : Z) : Prop :=
    forall iv, own_ivl3 w iv -> a + n <= fst iv \/ snd iv <= a.
  Definition scal_apart (w : pmwA H) (a n : Z) : Prop :=
    a + n <= wa_p w + O_WIDX \/ wa_p w + O_FLAGS + 2 <= a.

  Lemma own_apart_of3 : forall w a n, own_apart3 w a n -> scal_apart w a n -> own_apart w a n.
  Proof.
    intros w a n A3 AS iv [Hiv|[Hiv|[Hiv|(I1 & I2)]]].
    - apply A3. left. exact Hiv.
    - apply A3. right; left. exact Hiv.
    - apply A3. right; right. exact Hiv.
    - unfold scal_apart in AS. destruct AS as [AS|AS]; [left | right]; lia.
  Qed.

  Lemma own_apart3_sub : forall w a n a' n', own_apart3 w a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> own_apart3 w a' n'.
  Proof. intros w a n a' n' AP H1 H2 H3 iv Hiv. destruct (AP iv Hiv); lia. Qed.

  Lemma disjoint_of_own : forall w W a n, Forall (own_ivl w) W -> own_apart w a n -> disjoint_from W a n.
  Proof.
    intros w W a n FW AP. induction W as [|[lo hi] W IH]; cbn; [exact I|].
    split; [exact (AP (lo, hi) (Forall_inv FW)) | exact (IH (Forall_inv_tail FW))].
  Qed.

  Lemma own_apart_sub : forall w a n a' n', own_apart w a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> own_apart w a' n'.
  Proof. intros w a n a' n' AP H1 H2 H3 iv Hiv. destruct (AP iv Hiv); lia. Qed.

  Lemma pmw_frame_facts : forall w, pmw_okA w ->
    AIMG_TOP + AFS_HDR <= wa_ff w /\ wa_ff w + fsz PM_FCLASS <= aceil /\ wa_ff w mod 64 = 0
    /\ as_FSB H + AFS_HDR <= wa_ff w /\ wa_ff w + fsz PM_FCLASS <= as_FSB H + AFS_SIZE
    /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE
    /\ as_FSB H + AFS_FLAGS <= wa_fp w /\ wa_fp w < as_FSB H + AFS_HDR.
  Proof.
    intros w OK. pose proof (fresh_frame_facts H _ _ _ _ (wk_fresh w OK)) as FA.
    destruct FA as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    repeat split; assumption.
  Qed.

  Lemma fsz8 : fsz PM_FCLASS = 16384. Proof. reflexivity. Qed.
  Lemma fshn8 : fshn PM_FCLASS = 2048. Proof. reflexivity. Qed.

  Lemma own_apart_obj3 : forall w O n,
    pmw_okA w -> fsobj H (wa_LF0 w) O n -> aapp O n -> 0 <= O -> 0 <= n -> O + n <= aceil ->
    own_apart3 w O n /\ own_apart3 w (sh O) (nsh n).
  Proof.
    intros w O n OK FO AP HO Hn Hc. pose proof (wk_rfs0 w OK) as RF. set (m := wa_m0 w) in RF.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (Htop : O + n <= AAPP_HI) by (unfold AAPP_HI; lia).
    pose proof (fsobj_windows H HH _ _ _ _ _ _ m RF FO (wk_fresh w OK) HO Hn Htop) as (D1 & D2 & D3 & D4).
    rewrite fsz8 in *. rewrite fshn8 in D2.
    pose proof (aapp_disjoint_sh O n (wa_ff w) 16384 AP ltac:(unfold AIMG_TOP, AFS_HDR in *; lia)
                   ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SH1.
    assert (SHA : sh O + nsh n <= sh aceil).
    { unfold sh, nsh. Z.div_mod_to_equations. nia. }
    assert (SHB : sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    split.
    - intros iv [(I1 & I2)|[(I1 & I2)|(I1 & I2)]]; change (fsz PM_FCLASS) with 16384 in *.
      + left. lia.
      + destruct D1 as [D1|D1]; [left | right]; lia.
      + unfold PM_NSH in I2. unfold nsh in SH1. change ((16384 + 7) / 8) with 2048 in SH1.
        destruct SH1 as [SH1|SH1]; [right | left]; lia.
    - intros iv [(I1 & I2)|[(I1 & I2)|(I1 & I2)]]; change (fsz PM_FCLASS) with 16384 in *.
      + left. lia.
      + pose proof (aapp_disjoint_sh (wa_ff w) 16384 O n ltac:(eapply aapp_sub; [exact F8 | unfold AFS_HDR in *; lia | unfold AFS_HDR in *; lia]) HO Htop Hn) as SH2.
        destruct SH2 as [SH2|SH2]; [left | right]; lia.
      + unfold PM_NSH in I2. destruct D2 as [D2|D2]; [left | right]; lia.
  Qed.

  Lemma p_range : forall w, pmw_okA w -> AIMG_TOP <= wa_p w /\ wa_p w + PARSER_SIZE <= aceil.
  Proof.
    intros w OK. pose proof (wk_papp w OK) as ([(Q1 & Q2)|(Q1 & Q2)] & _ & _); pose proof aceil_facts as ((AC1 & AC2) & _ & _);
      unfold ALOWSH_LO, AHI_LO, AIMG_TOP in *; lia.
  Qed.

  Lemma p_frame : forall w, pmw_okA w -> exists f, In f (wa_LF0 w) /\ ff_addr f <= wa_p w
    /\ wa_p w + PARSER_SIZE <= ff_addr f + fsz (ff_class f)
    /\ as_FSB H + AFS_HDR <= ff_addr f /\ ff_addr f + fsz (ff_class f) <= as_FSB H + AFS_SIZE.
  Proof.
    intros w OK. destruct (wk_pin w OK) as (f & Hf & F1 & F2). exists f.
    pose proof (ah_RFS_range H HH _ _ (wk_rfs0 w OK)) as [_ AR]. destruct (AR f Hf) as (_ & R1 & R2 & _).
    repeat split; assumption.
  Qed.

  Lemma scal_apart_sh : forall w O n, pmw_okA w -> 0 <= O -> O + n <= AAPP_HI -> 0 <= n -> scal_apart w (sh O) (nsh n).
  Proof.
    intros w O n OK H0 H1 H2. pose proof (wk_papp w OK) as (PA & _ & _).
    pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE O n PA H0 H1 H2) as D.
    unfold scal_apart, PARSER_SIZE, O_WIDX, O_FLAGS in *. lia.
  Qed.

  Lemma own_apart_obj : forall w O n,
    pmw_okA w -> fsobj H (wa_LF0 w) O n -> aapp O n -> 0 <= O -> 0 <= n -> O + n <= aceil -> scal_apart w O n ->
    own_apart w O n /\ own_apart w (sh O) (nsh n).
  Proof.
    intros w O n OK FO AP HO Hn Hc HS.
    destruct (own_apart_obj3 w O n OK FO AP HO Hn Hc) as [A1 A2].
    pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    split; apply own_apart_of3; try assumption.
    apply scal_apart_sh; [exact OK | lia | unfold AAPP_HI; lia | lia].
  Qed.

  Lemma scal_apart_blk : forall w s LB m A n, pmw_okA w -> as_RHEAP H s LB m -> In (A, n) (lbl LB) -> scal_apart w A n.
  Proof.
    intros w s LB m A n OK RH Hin. apply lbl_in_inv in Hin. destruct Hin as [pid Hin].
    pose proof (ah_blocks H HH _ _ _ _ RH Hin) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn in R0, R16, Rn, RI, RC, RF, RAPP.
    destruct (p_frame w OK) as (f & Hf & F1 & F2 & F3 & F4).
    unfold scal_apart, PARSER_SIZE, O_WIDX, O_FLAGS, AFS_HDR in *. lia.
  Qed.

  Lemma own_apart_pf : forall w k len, pmw_okA w -> 0 <= k -> 0 <= len -> k + len <= PARSER_SIZE ->
    (k + len <= O_WIDX \/ O_FLAGS + 2 <= k) -> own_apart w (wa_p w + k) len.
  Proof.
    intros w k len OK Hk Hl Hkl Hs. pose proof (wk_papp w OK) as (PA & P0 & _). pose proof (p_range w OK) as (PR1 & PR2).
    apply own_apart_of3.
    - destruct (own_apart_obj3 w (wa_p w) PARSER_SIZE OK (wk_pobj w OK) PA ltac:(lia) ltac:(unfold PARSER_SIZE; lia) PR2) as [A3 _].
      eapply own_apart3_sub; [exact A3 | lia | lia | lia].
    - unfold scal_apart, O_WIDX, O_FLAGS in *. lia.
  Qed.

  Lemma own_apart_psh : forall w, pmw_okA w -> own_apart w (sh (wa_p w)) (nsh PARSER_SIZE).
  Proof.
    intros w OK. pose proof (wk_papp w OK) as (PA & P0 & _). pose proof (p_range w OK) as (PR1 & PR2).
    pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    apply own_apart_of3.
    - exact (proj2 (own_apart_obj3 w (wa_p w) PARSER_SIZE OK (wk_pobj w OK) PA ltac:(lia) ltac:(unfold PARSER_SIZE; lia) PR2)).
    - apply scal_apart_sh; [exact OK | lia | unfold AAPP_HI, PARSER_SIZE in *; lia | unfold PARSER_SIZE; lia].
  Qed.

  Lemma own_apart_img : forall w a n, pmw_okA w -> 0 <= n -> a + n <= AIMG_TOP -> own_apart w a n.
  Proof.
    intros w a n OK Hn Ha. apply own_apart_of3; [| pose proof (p_range w OK); unfold scal_apart, O_WIDX; lia].
    intros iv Hiv.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    left. destruct Hiv as [(I1 & I2)|[(I1 & I2)|(I1 & I2)]]; unfold AFS_HDR in *; try (unfold AIMG_TOP in *; lia).
    - assert (sh AIMG_TOP <= sh (wa_ff w)) by (apply sh_mono; lia).
      replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. unfold AIMG_TOP in *. lia.
  Qed.

  Lemma own_munch_eq : forall w W m m' (x : word), munch W m m' -> Forall (own_ivl w) W -> own_apart w (bv_unsigned x) 1 -> m' x = m x.
  Proof.
    intros w W m m' x MU FW AP. apply MU. eapply disjoint_outside; [exact (disjoint_of_own w W _ 1 FW AP) | lia].
  Qed.

  Lemma own_agree : forall w W m m' (P : Z -> Prop), munch W m m' -> Forall (own_ivl w) W ->
    (forall a, P a -> 0 <= a < 2 ^ 64 /\ own_apart w a 1) -> CRep.agree_on P m m'.
  Proof.
    intros w W m m' P MU FW HP a Ha. destruct (HP a Ha) as [Hr AP].
    apply (own_munch_eq w W m m'); [exact MU | exact FW |]. rewrite unsigned_lit by lia. exact AP.
  Qed.

  Lemma own_fld : forall w W m m' a k v, munch W m m' -> Forall (own_ivl w) W ->
    0 <= a -> a + Z.of_nat k < 2 ^ 64 -> own_apart w a (Z.of_nat k) ->
    fld ASEGS m a k v -> fld ASEGS m' a k v.
  Proof.
    intros w W m m' a k v MU FW H0 H1 AP F. eapply fld_agree; [exact H0 | exact H1 | exact F |].
    eapply own_agree; [exact MU | exact FW |]. intros x Hx. unfold zwin in Hx. split; [lia|].
    eapply own_apart_sub; [exact AP | lia | lia | lia].
  Qed.

  Lemma own_mdef : forall w W m m' a n, munch W m m' -> Forall (own_ivl w) W ->
    0 <= a -> a + n < 2 ^ 64 -> own_apart w a n -> mdef m a n -> mdef m' a n.
  Proof.
    intros w W m m' a n MU FW H0 H1 AP D. eapply mdef_agree; [exact D|].
    eapply own_agree; [exact MU | exact FW |]. intros x Hx. unfold zwin in Hx. split; [lia|].
    eapply own_apart_sub; [exact AP | lia | lia | lia].
  Qed.

  Lemma own_aclient : forall w LB iv, pmw_okA w -> own_ivl w iv -> aclient_write_ok H LB iv.
  Proof.
    intros w LB iv OK Hiv.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; change (fsz PM_FCLASS) with 16384 in *.
    - left. lia.
    - right; right; right; right; left. unfold AFS_HDR in *. lia.
    - right; right; right; right; right; left. split.
      + eapply Z.le_trans; [| exact I1]. apply sh_mono; unfold AFS_HDR in *; lia.
      + eapply Z.le_trans; [exact I2|]. unfold PM_NSH.
        assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
        assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia). lia.
    - right; right; right; right; left. destruct (p_frame w OK) as (f & Hf & P1 & P2 & P3 & P4).
      unfold O_WIDX, O_FLAGS, PARSER_SIZE, AFS_HDR in *. lia.
  Qed.
  Lemma own_afs : forall w iv, pmw_okA w -> own_ivl w iv -> fst iv <= snd iv ->
    afs_write_ok H ((PM_FCLASS, wa_ff w, wa_fp w) :: wa_LF0 w) iv.
  Proof.
    intros w iv OK Hiv Hle.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; change (fsz PM_FCLASS) with 16384 in *.
    - left. unfold ATLS_PRIV_HI, ATP in *. split; [right | right]; lia.
    - right. exists (PM_FCLASS, wa_ff w, wa_fp w). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd].
      change (fsz PM_FCLASS) with 16384. lia.
    - left. split.
      + assert (Q1 : 0 <= wa_ff w) by (unfold AIMG_TOP, AFS_HDR in F1; lia).
        assert (Q2 : wa_ff w + 16384 <= AAPP_HI) by (unfold AAPP_HI; lia).
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (wa_ff w) 16384 F8 Q1 Q2 ltac:(lia)) as SH.
        unfold nsh in SH. change ((16384 + 7) / 8) with 2048 in SH. unfold PM_NSH in I2.
        destruct SH as [SH|SH]; [left | right]; lia.
      + right. unfold ATLS_PRIV_HI, ATP in *.
        assert (sh AIMG_TOP <= sh (wa_ff w)) by (apply sh_mono; unfold AFS_HDR in *; lia).
        replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. lia.
    - right. destruct (wk_pin w OK) as (f & Hf & P1 & P2). exists f. split; [right; exact Hf|].
      unfold O_WIDX, O_FLAGS, PARSER_SIZE in *. lia.
  Qed.

  Lemma own_stack0_ok : forall w iv, pmw_okA w -> own_ivl w iv -> stack0_ok iv.
  Proof.
    intros w iv OK Hiv.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    unfold stack0_ok.
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; change (fsz PM_FCLASS) with 16384 in *.
    - left. unfold AHI_LO. lia.
    - destruct F8 as [(L1 & L2)|(L1 & L2)].
      + right. assert (ALOWSH_LO <= sh aceil) by (unfold sh, ALOWSH_LO, ASHADOW_BASE; Z.div_mod_to_equations; lia).
        unfold ALOWSH_LO, AFS_HDR in *. lia.
      + left. unfold AFS_HDR in *. lia.
    - right. unfold PM_NSH in I2.
      assert (sh (wa_ff w + 11584) <= sh aceil) by (apply sh_mono; lia).
      assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia). lia.
    - pose proof (wk_papp w OK) as ([(Q1 & Q2)|(Q1 & Q2)] & _ & _).
      + right. assert (ALOWSH_LO <= sh aceil) by (unfold sh, ALOWSH_LO, ASHADOW_BASE; Z.div_mod_to_equations; lia).
        unfold ALOWSH_LO, O_WIDX, O_FLAGS, PARSER_SIZE in *. lia.
      + left. unfold O_WIDX in *. lia.
  Qed.

  Lemma own_aconst_ok : forall w iv, pmw_okA w -> own_ivl w iv -> aconst_ok iv.
  Proof.
    intros w [lo hi] OK Hiv.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    unfold own_ivl in Hiv. cbn [fst snd] in Hiv.
    assert (HLO : 0x6e7248 <= lo /\ sh AIMG_TOP <= lo \/ 0x6e7248 <= lo /\ hi <= 0x7fff7000).
    { destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; change (fsz PM_FCLASS) with 16384 in *.
      - left. replace (sh AIMG_TOP) with 0x800d5000 by reflexivity. lia.
      - destruct F8 as [(L1 & L2)|(L1 & L2)].
        + right. unfold AIMG_TOP, AFS_HDR, ALOWSH_LO in *. lia.
        + left. replace (sh AIMG_TOP) with 0x800d5000 by reflexivity. unfold AHI_LO, AFS_HDR in *. lia.
      - left. assert (sh AIMG_TOP <= sh (wa_ff w)) by (apply sh_mono; unfold AFS_HDR in *; lia).
        replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. lia.
      - pose proof (wk_papp w OK) as ([(Q1 & Q2)|(Q1 & Q2)] & _ & _).
        + right. unfold AIMG_TOP, ALOWSH_LO, O_WIDX, O_FLAGS, PARSER_SIZE in *. lia.
        + left. replace (sh AIMG_TOP) with 0x800d5000 by reflexivity. unfold AHI_LO, O_WIDX in *. lia. }
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
      AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
      replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity;
      destruct HLO as [(L1 & L2)|(L1 & L2)]; lia.
  Qed.

  Lemma own_apart_lbl : forall w s LB m A n,
    pmw_okA w -> as_RHEAP H s LB m -> In (A, n) (lbl LB) -> own_apart w A n /\ own_apart w (sh A) (nsh n).
  Proof.
    intros w s LB m A n OK RH Hin. apply lbl_in_inv in Hin. destruct Hin as [pid Hin].
    pose proof (ah_blocks H HH _ _ _ _ RH Hin) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn in R0, R16, Rn, RI, RC, RF, RAPP.
    apply own_apart_obj; [exact OK | eapply fsobj_block; [exact HH | exact RH | exact Hin] | exact RAPP | lia | lia | lia |].
    apply (scal_apart_blk w s LB m A n OK RH). apply (lbl_in LB pid). exact Hin.
  Qed.

  Lemma Forall_own_map : forall w (P : Z * Z -> Prop) W, Forall (own_ivl w) W -> (forall iv, own_ivl w iv -> P iv) -> Forall P W.
  Proof. intros w P W F HP. induction F; constructor; [apply HP; assumption | assumption]. Qed.

  Lemma Forall_own_afs : forall w W, pmw_okA w -> Forall (own_ivl w) W -> Forall (fun iv : Z * Z => fst iv <= snd iv) W ->
    Forall (afs_write_ok H ((PM_FCLASS, wa_ff w, wa_fp w) :: wa_LF0 w)) W.
  Proof.
    intros w W OK FW FLE. induction W as [|iv W IH]; constructor.
    - exact (own_afs w iv OK (Forall_inv FW) (Forall_inv FLE)).
    - apply IH; [exact (Forall_inv_tail FW) | exact (Forall_inv_tail FLE)].
  Qed.

  Lemma own_apart_fhead : forall w k n, pmw_okA w -> (0 <= k /\ k + n <= 24 \/ fsz PM_FCLASS - 8 <= k /\ k + n <= fsz PM_FCLASS) -> 0 <= n ->
    own_apart w (wa_ff w + k) n.
  Proof.
    intros w k n OK Hk Hn. apply own_apart_of3.
    2:{ destruct (wk_pin w OK) as (f & Hf & P1 & P2). destruct (wk_fresh w OK) as (_ & _ & FR).
        destruct (FR f Hf) as [D _]. change (fsz PM_FCLASS) with 16384 in *.
        unfold scal_apart, O_WIDX, O_FLAGS, PARSER_SIZE in *. destruct D as [D|D]; [left | right]; lia. }
    intros iv Hiv.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|(I1 & I2)]]; change (fsz PM_FCLASS) with 16384 in *.
    - left. lia.
    - destruct Hk as [Hk|Hk]; [left | right]; lia.
    - assert (Q1 : 0 <= wa_ff w) by (unfold AIMG_TOP, AFS_HDR in F1; lia).
      assert (Q2 : wa_ff w + 16384 <= AAPP_HI) by (unfold AAPP_HI; lia).
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (wa_ff w) 16384 F8 Q1 Q2 ltac:(lia)) as SH.
      unfold nsh in SH. change ((16384 + 7) / 8) with 2048 in SH. unfold PM_NSH in I2. unfold AFS_HDR in *.
      destruct SH as [SH|SH]; [right | left]; lia.
  Qed.

  Lemma own_apart_saved : forall w, pmw_okA w -> own_apart w (wa_sp0 w - 104) 104.
  Proof.
    intros w OK. apply own_apart_of3.
    2:{ pose proof (p_range w OK) as (PR1 & PR2). pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
        unfold scal_apart, O_WIDX, O_FLAGS, PARSER_SIZE, APM_STACK in *. right. lia. }
    intros iv Hiv.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|(I1 & I2)]]; change (fsz PM_FCLASS) with 16384 in *.
    - right. lia.
    - right. unfold APM_STACK in *. lia.
    - right. unfold PM_NSH in I2.
      assert (sh (wa_ff w + 11584) <= sh aceil) by (apply sh_mono; lia).
      assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia).
      assert (sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
      unfold APM_STACK in *. lia.
  Qed.

  Lemma own_lbl_eq : forall w s LB m m' W A n a, pmw_okA w -> as_RHEAP H s LB m -> munch W m m' -> Forall (own_ivl w) W ->
    In (A, n) (lbl LB) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
  Proof.
    intros w s LB m m' W A n a OK RH MU FW Hin Ha.
    pose proof (own_apart_lbl w s LB m A n OK RH Hin) as [AP _].
    destruct (lbl_in_inv LB A n Hin) as [pid Hb].
    pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn in R0, RC.
    apply (own_munch_eq w W m m'); [exact MU | exact FW |]. rewrite unsigned_lit by (pose proof aceil_facts; lia).
    eapply own_apart_sub; [exact AP | lia | lia | lia].
  Qed.

  Lemma cells_size_mapC8 : forall l, cells_size (map C8 l) = (8 * length l)%nat.
  Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.

  Lemma cc_gen_length : forall len mid, 0 <= mid <= len -> Z.of_nat (length (cc_gen len mid)) = nsh len.
  Proof.
    intros len mid Hm. unfold cc_gen, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
    assert (nsh mid <= nsh len) by (unfold nsh; apply Z.div_le_mono; lia). lia.
  Qed.

  Lemma own_umapx : forall w s LB m m' W NS (V : Type) (nval : mem -> Z -> V -> Prop)
      (nval_agree : forall M M' p v, nval M p v -> HRepFacts.agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v)
      obj bl bc ents,
    24 <= NS -> pmw_okA w -> as_RHEAP H s LB m -> munch W m m' -> Forall (own_ivl w) W ->
    @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m obj bl bc ents -> own_apart w obj 40 -> 0 <= obj -> obj + 40 < 2 ^ 64 ->
    @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m' obj bl bc ents.
  Proof.
    intros w s LB m m' W NS V nval nval_agree obj bl bc ents HNS OK RH MU FW U AP H0 H1.
    eapply (umapx_agree ASEGS LY_A MI_A NS V nval nval_agree HNS); [exact U | | intros p0 n0 _ Hl; exact Hl].
    intros a Ha. pose proof U as U'. destruct U' as [_ _ _ _ _ _ Ublive _ _ _ _ _ _ _ Unode _].
    unfold umap_foot in Ha. destruct Ha as [Ha|[(Hbc & Ha)|(q & Hq & Ha)]].
    - apply (own_munch_eq w W m m'); [exact MU | exact FW |]. rewrite unsigned_lit by lia.
      eapply own_apart_sub; [exact AP | lia | lia | lia].
    - destruct Ublive as [[E _]|[_ Hl]]; [contradiction|].
      exact (own_lbl_eq w s LB m m' W bl (8 * bc) a OK RH MU FW Hl Ha).
    - apply in_map_iff in Hq. destruct Hq as ([q' [k v]] & Eq & Hin). cbn in Eq. subst q'.
      destruct (Unode q k v Hin) as (Hl & _).
      exact (own_lbl_eq w s LB m m' W q NS a OK RH MU FW Hl Ha).
  Qed.

  Lemma own_vec32 : forall w s LB m m' W v b xs cap,
    pmw_okA w -> as_RHEAP H s LB m -> munch W m m' -> Forall (own_ivl w) W ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m v b xs cap -> own_apart w v 24 -> 0 <= v -> v + 24 < 2 ^ 64 ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' v b xs cap.
  Proof.
    intros w s LB m m' W v b xs cap OK RH MU FW V AP H0 H1.
    eapply vec32_frame; [exact V|]. intros a Ha.
    pose proof V as (_ & _ & _ & Hlen & Hb & _). unfold vec32_fp in Ha. destruct Ha as [Ha|(Hb0 & Ha)].
    - apply (own_munch_eq w W m m'); [exact MU | exact FW |]. unfold zwin in Ha. rewrite unsigned_lit by lia.
      eapply own_apart_sub; [exact AP | lia | lia | lia].
    - destruct Hb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|]. unfold zwin in Ha.
      eapply (own_lbl_eq w s LB m m' W b (4 * cap) a OK RH MU FW Hl). unfold Zlen in *. lia.
  Qed.

  Lemma own_vec_opnd : forall w s LB m m' W v b n cap,
    pmw_okA w -> as_RHEAP H s LB m -> munch W m m' -> Forall (own_ivl w) W ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m v b n cap -> own_apart w v 24 -> 0 <= v -> v + 24 < 2 ^ 64 ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m' v b n cap.
  Proof.
    intros w s LB m m' W v b n cap OK RH MU FW V AP H0 H1.
    eapply vec_opnd_frame; [exact V|]. intros a Ha. unfold vec_opnd_fp, zwin in Ha.
    apply (own_munch_eq w W m m'); [exact MU | exact FW |]. rewrite unsigned_lit by lia.
    eapply own_apart_sub; [exact AP | lia | lia | lia].
  Qed.

  Lemma own_addr_lbl : forall w s LB m m' W A n, pmw_okA w -> as_RHEAP H s LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (own_ivl w) W -> In (A, n) (lbl LB) -> addressable m A n -> addressable m' A n.
  Proof.
    intros w s LB m m' W A n OK RH MU WM FW Hin AD.
    pose proof (own_apart_lbl w s LB m A n OK RH Hin) as [_ APs].
    eapply addressable_transport; [exact AD | exact MU | exact WM | exact (disjoint_of_own w W _ _ FW APs)].
  Qed.

  Lemma own_SHAD_lbl : forall w s LB m m' W A n sbs, pmw_okA w -> as_RHEAP H s LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (own_ivl w) W -> In (A, n) (lbl LB) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs.
  Proof.
    intros w s LB m m' W A n sbs OK RH MU WM FW Hin Hl SH.
    pose proof (own_apart_lbl w s LB m A n OK RH Hin) as [_ APs].
    eapply SHAD_transport; [exact SH | exact MU | exact WM |].
    apply (disjoint_of_own w W); [exact FW|]. eapply own_apart_sub; [exact APs | lia | lia | lia].
  Qed.

  Lemma own_umap_sh : forall w s LB m m' W NS (V : Type) (nval : mem -> Z -> V -> Prop) obj bl bc ents,
    pmw_okA w -> as_RHEAP H s LB m -> munch W m m' -> wmono asegs m m' -> Forall (own_ivl w) W ->
    @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m obj bl bc ents ->
    umap_sh m NS (bl, bc, ents) -> umap_sh m' NS (bl, bc, ents).
  Proof.
    intros w s LB m m' W NS V nval obj bl bc ents OK RH MU WM FW U [SB SN].
    destruct U as [_ _ _ _ _ _ Ublive _ _ _ _ _ _ _ Unode _]. cbn [t3a t3b t3c fst snd] in *. split.
    - intros Hbc. destruct Ublive as [[E _]|[_ Hl]]; [contradiction|].
      exact (own_addr_lbl w s LB m m' W bl (8 * bc) OK RH MU WM FW Hl (SB Hbc)).
    - intros q k v Hin. destruct (Unode q k v Hin) as (Hl & _).
      exact (own_addr_lbl w s LB m m' W q NS OK RH MU WM FW Hl (SN q k v Hin)).
  Qed.

  Lemma own_pmc_sh : forall w s LB m m' W c, pmw_okA w -> as_RHEAP H s LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (own_ivl w) W ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (wa_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m (wa_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (wa_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) ->
    pmc_sh m c -> pmc_sh m' c.
  Proof.
    intros w s LB m m' W c OK RH MU WM FW U1 U2 U3 V1 V2 V3 (S1 & S2 & S3 & S4 & S5 & S6).
    destruct (c_m1 c) as [[bl1 bc1] e1] eqn:E1. destruct (c_m2 c) as [[bl2 bc2] e2] eqn:E2. destruct (c_m3 c) as [[bl3 bc3] e3] eqn:E3.
    unfold pmc_sh. rewrite E1, E2, E3 in *. cbn [t3a t3b t3c fst snd] in *.
    split; [exact (own_umap_sh w s LB m m' W 24 Z (nval24 ASEGS) _ bl1 bc1 e1 OK RH MU WM FW U1 S1)|].
    split; [exact (own_umap_sh w s LB m m' W 32 (Z * Z * Z) (nval32 ASEGS) _ bl2 bc2 e2 OK RH MU WM FW U2 S2)|].
    split; [exact (own_umap_sh w s LB m m' W 24 Z (nval24 ASEGS) _ bl3 bc3 e3 OK RH MU WM FW U3 S3)|].
    split; [| split].
    - intros Hb. pose proof V1 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (own_SHAD_lbl w s LB m m' W _ _ _ OK RH MU WM FW Hl); [| exact (S4 Hb)].
      rewrite cc_gen_length by (unfold OPND_SZ; lia). lia.
    - intros Hb. pose proof V2 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (own_SHAD_lbl w s LB m m' W _ _ _ OK RH MU WM FW Hl); [| exact (S5 Hb)].
      rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
    - intros Hb. pose proof V3 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (own_SHAD_lbl w s LB m m' W _ _ _ OK RH MU WM FW Hl); [| exact (S6 Hb)].
      rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
  Qed.

  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma pmxa_own : forall w s LB LBs m mo c ins tbl ftbl TB spal m' W ins' tbl' ftbl' widx icount endian reqconv spal',
    pmw_okA w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    munch W m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_sp0 w) ->
    Forall (own_ivl w) W -> Forall (fun iv : Z * Z => fst iv <= snd iv) W ->
    SHAD m' (wa_ff w) (pm_fsh ins') -> slots_ok w m' bvmap_empty tbl' -> fslots_ok w m' ftbl' ->
    fld ASEGS m' (wa_p w + O_WIDX) 8 widx -> fld ASEGS m' (wa_p w + O_ICOUNT) 8 icount ->
    fld ASEGS m' (wa_p w + O_ENDIAN) 4 endian -> fld ASEGS m' (wa_p w + O_FLAGS) 1 reqconv ->
    fld ASEGS m' (wa_p w + O_FLAGS + 1) 1 0 ->
    0 <= widx <= wa_n w -> 0 <= icount <= widx -> 0 <= endian < 2 ^ 32 -> (reqconv = 0 \/ reqconv = 1) ->

    0 <= spal' <= PM_RESERVE -> pm_phi c + spal <= pm_phi (set_scalA c widx icount endian reqconv) + spal' ->
    PMXAT H LINV w s LB LBs m' mo (set_scalA c widx icount endian reqconv) ins' tbl' ftbl' TB spal'.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' W ins' tbl' ftbl' widx icount endian reqconv spal' OK X MU WM DM MI STK FW FLE FSH SL FSL
           Fw Fi Fe Ff Fr Bw Bi Be Bf Bsp Bphi.
    pose proof (pmw_frame_facts w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_papp w OK) as (P1 & P2 & P3).
    pose proof (wk_capp w OK) as (C1 & C2 & C3).
    pose proof (p_range w OK) as (PR1 & P4).
    assert (C4 : wa_cons w + 48 <= aceil).
    { destruct C1 as [(Q1 & Q2)|(Q1 & Q2)]; [unfold ALOWSH_LO in Q2; lia | exact Q2]. }
    assert (CS : scal_apart w (wa_cons w) 48).
    { pose proof (wk_pcons w OK) as PC. unfold scal_apart, O_WIDX, O_FLAGS, PARSER_SIZE in *. lia. }
    pose proof (own_apart_obj w (wa_cons w) 48 OK (wk_cobj w OK) C1 ltac:(lia) ltac:(lia) C4 CS) as [AC ACs].
    pose proof (own_apart_psh w OK) as APs.
    assert (RH' : as_RHEAP H s LB m').
    { eapply (ah_RHEAP_frame H HH); [exact (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU | exact WM |].
      apply (Forall_own_map w); [exact FW |]. intros iv Hiv. exact (own_aclient w LB iv OK Hiv). }
    destruct X as [Xrheap Xlbown Xtb Xown Xmeas Xmpres Xmeminv Xstk Xerrno Xrauxv Xaconst Xstack0 Xlinv Xrfs Xxpres Xal Xsaved Xfhdr Xfflag Xfwr Xchain Xfsh Xslots Xfslots Xpdef Xcons Xuser Xhdrfn Xinsfn Xhunk Xwords Xn Xdiag Xwidx Xicount Xendian Xflags Xretry Xscal Xconsf Xconsd Xconsw Xwbuf Xm1 Xm2 Xm3 Xv1 Xv2 Xv3 Xsh].
    constructor; cbn [set_scalA c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr].
    - exact RH'.
    - exact (lb_own_wmono _ _ _ Xlbown WM).
    - destruct Xtb as [T1 T2]. split; [exact (lb_own_wmono _ _ _ T1 WM) | exact T2].
    - exact Xown.
    - exact Xmeas.
    - exact Xmpres.
    - exact MI.
    - exact STK.
    - destruct Xerrno as [errv Herr]. exists errv. eapply rw_cells_transport; [exact Herr | exact MU | exact WM |].
      apply (disjoint_of_own w W); [exact FW|]. rewrite (wk_tp w OK). rewrite unsigned_lit by (unfold ATP; lia).
      apply own_apart_img; [exact OK | cbn; lia | unfold ATP, AIMG_TOP; cbn; lia].
    - eapply (ah_rauxv_frame H HH); [exact Xrauxv | exact MU | exact WM |].
      apply (Forall_own_map w); [exact FW |]. intros iv Hiv. exact (own_aclient w LB iv OK Hiv).
    - eapply ACONST_frame; [exact Xaconst | exact MU | exact WM |].
      apply (Forall_own_map w); [exact FW |]. intros iv Hiv. exact (own_aconst_ok w iv OK Hiv).
    - eapply stack0_transport; [exact Xstack0 | exact MU | exact WM |].
      apply (Forall_own_map w); [exact FW |]. intros iv Hiv. exact (own_stack0_ok w iv OK Hiv).
    - eapply LINV_frame; [exact Xlinv | exact MU | exact WM |].
      apply (Forall_own_map w); [exact FW |]. intros [lo hi] Hiv. cbn [fst]. unfold own_ivl in Hiv. cbn [fst snd] in Hiv.
      change (fsz PM_FCLASS) with 16384 in *.
      destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; [unfold AIMG_TOP; lia | unfold AFS_HDR in *; lia | | unfold O_WIDX in *; lia].
      assert (sh AIMG_TOP <= sh (wa_ff w)) by (apply sh_mono; unfold AFS_HDR in *; lia).
      replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. unfold AIMG_TOP. lia.
    - eapply (ah_RFS_frame H HH); [exact Xrfs | exact MU | exact WM |].
      exact (Forall_own_afs w W OK FW FLE).
    - destruct Xxpres as (XS & FXS & XP). exists XS. split; [exact FXS|].
      eapply xpres_trans; [exact XP|].
      eapply (xpres_weaken H LB (wa_LB0 w) (wa_sp0 w) (wa_sp0 w)); [| lia | | intros a Ha; exact Ha].
      2:{ intros b Hb. apply (Permutation_in _ (Permutation_sym (proj1 Xown))). apply in_app_iff. left. exact Hb. }
      eapply (xpres_of_munch H s LB); [exact HH | exact Xrheap | exact MU | exact WM |].
      apply (Forall_own_map w); [exact FW|]. intros [lo hi] Hiv. unfold own_ivl in Hiv. cbn [fst snd] in *.
      change (fsz PM_FCLASS) with 16384 in *. change (fshn PM_FCLASS) with 2048.
      destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]].
      + left. split; lia.
      + right. intros a Ha. cbn [rin_ivs fst snd]. right; right; left. lia.
      + right. intros a Ha. cbn [rin_ivs fst snd]. right; right; right; left. unfold PM_NSH in I2. lia.
      + right. intros a Ha. cbn [rin_ivs fst snd]. right; left. unfold O_WIDX, O_FLAGS, PARSER_SIZE in *. lia.
    - destruct Xal as (A1 & A2 & A3 & A4). split; [| split; [exact A2 | split; [exact A3 | exact Bsp]]].
      change {| c_widx := widx; c_icount := icount; c_endian := endian; c_reqconv := reqconv; c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c;
                c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |} with (set_scalA c widx icount endian reqconv). lia.
    - eapply rw_cells_transport; [exact Xsaved | exact MU | exact WM |].
      apply (disjoint_of_own w W); [exact FW|]. rewrite cells_size_mapC8, (wk_saved w OK). cbn.
      exact (own_apart_saved w OK).
    - eapply rw_cells_transport; [exact Xfhdr | exact MU | exact WM |].
      apply (disjoint_of_own w W); [exact FW|]. cbn [cells_size csize Nat.add].
      replace (wa_ff w) with (wa_ff w + 0) at 1 by lia. apply own_apart_fhead; [exact OK | left; cbn; lia | lia].
    - eapply rw_cells_transport; [exact Xfflag | exact MU | exact WM |].
      apply (disjoint_of_own w W); [exact FW|]. cbn [cells_size csize Nat.add].
      replace (wa_ff w + fsz PM_FCLASS - 8) with (wa_ff w + (fsz PM_FCLASS - 8)) by lia.
      apply own_apart_fhead; [exact OK | right; cbn; lia | lia].
    - destruct Xfwr as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. exact (WM _ (W3 i Hi)).
    - eapply (chain_via_munch H HH); [exact Xchain | exact MU |].
      intros fp ra Hin. apply (disjoint_of_own w W); [exact FW|].
      assert (Hfp : wa_sp0 w <= fp).
      { destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia | pose proof (wk_chfr w OK fp ra Hin); lia]. }
      intros iv Hiv. destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; change (fsz PM_FCLASS) with 16384 in *.
      + right. lia.
      + right. unfold APM_STACK in *. lia.
      + right. unfold PM_NSH in I2.
        assert (sh (wa_ff w + 11584) <= sh aceil) by (apply sh_mono; lia).
        assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia).
        assert (sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
        unfold APM_STACK in *. lia.
      + right. unfold O_FLAGS, PARSER_SIZE, APM_STACK in *. lia.
    - exact FSH.
    - exact SL.
    - exact FSL.
    - intros i Hi. apply DM. exact (Xpdef i Hi).
    - eapply (own_fld w W m m'); [exact MU | exact FW | lia | cbn; unfold PARSER_SIZE in *; lia | | exact Xcons].
      apply own_apart_pf; [exact OK | lia | lia | unfold PARSER_SIZE; lia | unfold O_WIDX; lia].
    - eapply (own_fld w W m m'); [exact MU | exact FW | lia | cbn; unfold PARSER_SIZE in *; lia | | exact Xuser].
      apply own_apart_pf; [exact OK | lia | lia | unfold PARSER_SIZE; lia | unfold O_WIDX; lia].
    - eapply (own_fld w W m m'); [exact MU | exact FW | lia | cbn; unfold PARSER_SIZE in *; lia | | exact Xhdrfn].
      apply own_apart_pf; [exact OK | lia | lia | unfold PARSER_SIZE; lia | unfold O_WIDX; lia].
    - eapply (own_fld w W m m'); [exact MU | exact FW | lia | cbn; unfold PARSER_SIZE in *; lia | | exact Xinsfn].
      apply own_apart_pf; [exact OK | lia | lia | unfold PARSER_SIZE; lia | unfold O_WIDX; lia].
    - eapply (own_fld w W m m'); [exact MU | exact FW | lia | cbn; unfold PARSER_SIZE in *; lia | | exact Xhunk].
      apply own_apart_pf; [exact OK | lia | lia | unfold PARSER_SIZE; lia | unfold O_WIDX; cbn; lia].
    - eapply (own_fld w W m m'); [exact MU | exact FW | unfold O_WORDS; lia | cbn; unfold O_WORDS, PARSER_SIZE in *; lia | | exact Xwords].
      apply own_apart_pf; [exact OK | unfold O_WORDS; lia | lia | unfold O_WORDS, PARSER_SIZE; lia | unfold O_WORDS, O_WIDX; lia].
    - eapply (own_fld w W m m'); [exact MU | exact FW | unfold O_N; lia | cbn; unfold O_N, PARSER_SIZE in *; lia | | exact Xn].
      apply own_apart_pf; [exact OK | unfold O_N; lia | lia | unfold O_N, PARSER_SIZE; lia | unfold O_N, O_WIDX; lia].
    - eapply (own_fld w W m m'); [exact MU | exact FW | unfold O_DIAG; lia | cbn; unfold O_DIAG, PARSER_SIZE in *; lia | | exact Xdiag].
      apply own_apart_pf; [exact OK | unfold O_DIAG; lia | lia | unfold O_DIAG, PARSER_SIZE; lia | unfold O_DIAG, O_WIDX; lia].
    - exact Fw.
    - exact Fi.
    - exact Fe.
    - exact Ff.
    - exact Fr.
    - repeat split; lia.
    - eapply (own_fld w W m m'); [exact MU | exact FW | lia | cbn; lia | | exact Xconsf].
      eapply own_apart_sub; [exact AC | lia | cbn; lia | cbn; lia].
    - eapply (own_mdef w W m m'); [exact MU | exact FW | lia | lia | | exact Xconsd].
      eapply own_apart_sub; [exact AC | lia | lia | lia].
    - exact (wr_at_wmono _ _ _ _ Xconsw WM).
    - intros Hwz. destruct (wk_words w OK) as [[E0 _]|(pw & k & Hin & Hk & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
      assert (Hin' : In (wa_words w, k) (lbl LB)).
      { apply (lbl_in LB pw). apply (Permutation_in _ (Permutation_sym (proj1 Xown))). apply in_app_iff. left. exact Hin. }
      pose proof (own_apart_lbl w s LB m _ _ OK Xrheap Hin') as [APw _].
      eapply (own_mdef w W m m'); [exact MU | exact FW | lia | lia | | exact (Xwbuf Hwz)].
      eapply own_apart_sub; [exact APw | lia | lia | lia].
    - eapply (own_umapx w s LB m m' W 24 Z (nval24 ASEGS) (nval24_agree ASEGS)); [lia | exact OK | exact Xrheap | exact MU | exact FW | exact Xm1 | | unfold O_M1; lia | unfold O_M1, PARSER_SIZE in *; lia].
      apply own_apart_pf; [exact OK | unfold O_M1; lia | lia | unfold O_M1, PARSER_SIZE; lia | unfold O_M1, O_FLAGS; lia].
    - eapply (own_umapx w s LB m m' W 32 (Z * Z * Z) (nval32 ASEGS) (nval32_agree ASEGS)); [lia | exact OK | exact Xrheap | exact MU | exact FW | exact Xm2 | | unfold O_M2; lia | unfold O_M2, PARSER_SIZE in *; lia].
      apply own_apart_pf; [exact OK | unfold O_M2; lia | lia | unfold O_M2, PARSER_SIZE; lia | unfold O_M2, O_FLAGS; lia].
    - eapply (own_umapx w s LB m m' W 24 Z (nval24 ASEGS) (nval24_agree ASEGS)); [lia | exact OK | exact Xrheap | exact MU | exact FW | exact Xm3 | | unfold O_M3; lia | unfold O_M3, PARSER_SIZE in *; lia].
      apply own_apart_pf; [exact OK | unfold O_M3; lia | lia | unfold O_M3, PARSER_SIZE; lia | unfold O_M3, O_FLAGS; lia].
    - eapply (own_vec_opnd w s LB m m' W); [exact OK | exact Xrheap | exact MU | exact FW | exact Xv1 | | unfold O_V1; lia | unfold O_V1, PARSER_SIZE in *; lia].
      apply own_apart_pf; [exact OK | unfold O_V1; lia | lia | unfold O_V1, PARSER_SIZE; lia | unfold O_V1, O_FLAGS; lia].
    - eapply (own_vec32 w s LB m m' W); [exact OK | exact Xrheap | exact MU | exact FW | exact Xv2 | | unfold O_V2; lia | unfold O_V2, PARSER_SIZE in *; lia].
      apply own_apart_pf; [exact OK | unfold O_V2; lia | lia | unfold O_V2, PARSER_SIZE; lia | unfold O_V2, O_FLAGS; lia].
    - eapply (own_vec32 w s LB m m' W); [exact OK | exact Xrheap | exact MU | exact FW | exact Xv3 | | unfold O_V3; lia | unfold O_V3, PARSER_SIZE in *; lia].
      apply own_apart_pf; [exact OK | unfold O_V3; lia | lia | unfold O_V3, PARSER_SIZE; lia | unfold O_V3, O_FLAGS; lia].
    - destruct Xsh as (SHc & SHp & SHk). split; [| split].
      + exact (own_pmc_sh w s LB m m' W c OK Xrheap MU WM FW Xm1 Xm2 Xm3 Xv1 Xv2 Xv3 SHc).
      + eapply addressable_transport; [exact SHp | exact MU | exact WM |]. exact (disjoint_of_own w W _ _ FW APs).
      + eapply addressable_transport; [exact SHk | exact MU | exact WM |]. exact (disjoint_of_own w W _ _ FW ACs).
  Qed.

  Lemma pmxa_own0 : forall w s LB LBs m mo c ins tbl ftbl TB spal m' W ins' tbl' ftbl',
    pmw_okA w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    munch W m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_sp0 w) ->
    Forall (own_ivl w) W -> Forall (fun iv : Z * Z => fst iv <= snd iv) W ->
    SHAD m' (wa_ff w) (pm_fsh ins') -> slots_ok w m' bvmap_empty tbl' -> fslots_ok w m' ftbl' ->
    fld ASEGS m' (wa_p w + O_WIDX) 8 (c_widx c) -> fld ASEGS m' (wa_p w + O_ICOUNT) 8 (c_icount c) ->
    fld ASEGS m' (wa_p w + O_ENDIAN) 4 (c_endian c) -> fld ASEGS m' (wa_p w + O_FLAGS) 1 (c_reqconv c) ->
    fld ASEGS m' (wa_p w + O_FLAGS + 1) 1 0 ->
    PMXAT H LINV w s LB LBs m' mo c ins' tbl' ftbl' TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' W ins' tbl' ftbl' OK X MU WM DM MI STK FW FLE FSH SL FSL Fw Fi Fe Ff Fr.
    rewrite <- (set_scalA_id c). pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (B1 & B2 & B3 & B4).
    eapply pmxa_own; try eassumption.
    - exact (proj2 (proj2 (proj2 (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)))).
    - rewrite (set_scalA_id c). lia.
  Qed.

End Own.
