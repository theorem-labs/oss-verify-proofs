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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmFin LbB_PiStmt LbB_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RT_F3C : list (reg * expr) := RT_EXIT ++ [(11%bv, EVar WV_FF)].

Definition piw_ofA {HCEIL : HeapCeil} {H : asr} (w : pmwA H) : piw H :=
  PIW H (wa_p w) (wa_cons w) (wa_user w) (wa_diag w) (wa_words w) (wa_n w) (wa_LB0 w) (wa_s0 w) (wa_lo w) (wa_B w) (wa_shi w).

Lemma Z_to_bv64_add_mod_x : forall z, Z_to_bv 64 (z + 2 ^ 64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). replace (z + 2 ^ 64) with (z + 1 * 2 ^ 64) by lia. apply Z.mod_add. lia.
Qed.

Lemma sextw_sxw_x : forall e, 0 <= e < 2 ^ 32 -> sext 64 (alu32 ALU_ADD (low32 (sxw e)) (low32 (Z_to_bv 64 0))) = sxw e.
Proof.
  intros e He. rewrite w_addw. unfold v_addw, sxw. rewrite (u64_of_Z 0) by lia. rewrite Z.add_0_r.
  rewrite (bv_swrap32_cases e) by lia. destruct (Z.ltb_spec e (2 ^ 31)).
  - rewrite u64_of_Z by lia. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec e (2 ^ 31)); [reflexivity | lia].
  - rewrite <- (Z_to_bv64_add_mod_x (e - 2 ^ 32)) at 1. rewrite u64_of_Z by lia.
    replace (e - 2 ^ 32 + 2 ^ 64) with (e + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite swrap32_shift.
    rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec e (2 ^ 31)); [lia|]. reflexivity.
Qed.

Lemma sextw_i32 : forall r, - 2 ^ 31 <= r < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 r)) (low32 (Z_to_bv 64 0))) = Z_to_bv 64 r.
Proof.
  intros r Hr.
  assert (E : Z_to_bv 64 r = sxw (r mod 2 ^ 32)).
  { unfold sxw. pose proof (Z.mod_pos_bound r (2 ^ 32) ltac:(lia)) as Hm.
    rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec r 0) as [Hn|Hn].
    - assert (Hq : r mod 2 ^ 32 = r + 2 ^ 32) by (symmetry; apply Z.mod_unique with (q := -1); lia).
      rewrite Hq. destruct (Z.ltb_spec (r + 2 ^ 32) (2 ^ 31)); [lia|]. f_equal. lia.
    - rewrite Z.mod_small by lia. destruct (Z.ltb_spec r (2 ^ 31)); [reflexivity | lia]. }
  rewrite E. apply sextw_sxw_x. apply Z.mod_pos_bound. lia.
Qed.

Lemma pm_ret_ok : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
        x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0xf0fac) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  step. apply evt_done. exact HQ.
Qed.

Lemma aconst_ok_of_x : forall lo hi, (0x6e7248 <= lo /\ sh AIMG_TOP <= lo) \/ (0x6e7248 <= lo /\ hi <= 0x7fff7000) ->
  aconst_ok (lo, hi).
Proof.
  intros lo hi HLO.
  apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL,
    AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
    replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity;
    destruct HLO as [(L1 & L2)|(L1 & L2)]; lia.
Qed.

Section Restrict.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma pmxa_restrict : forall w s LB LBs m mo c ins tbl ftbl TB spal tbl' ftbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    incl tbl' tbl -> incl ftbl' ftbl -> PMXAT H LINV w s LB LBs m mo c ins tbl' ftbl' TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal tbl' ftbl' OK X It If.
    eapply (pmxa_munch H HH LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m [] tbl' ftbl' OK X (munch_refl [] m)
              (wmono_refl asegs m) (fun x Hx => Hx) (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
              (Forall_nil _) (Forall_nil _) I I It); [| exact If |].
    - apply Forall_forall. intros ke _. exact I.
    - apply Forall_forall. intros ke _. exact I.
  Qed.
End Restrict.

Section Fin2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Lemma HHx2 : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_fin_err : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal m' W,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    munch W m m' -> wmono asegs m m' -> Forall (fin_ivl H w) W -> mem_inv asegs m' -> ACONST m' ->
    pi_err H LINV (piw_ofA w) s LB LBs m' (prc_ofA w c).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl spal m' W OK X Htr Hbsz MU WM FW MI AC.
    destruct (pm_fin H HHbp LINV LINV_frame w s LB LBs m mo c ins tbl ftbl spal m' W OK X Htr MU WM FW)
      as (errv' & XSf & Ferr & Faux & Frh & Fso & Flo & Fpr & Fps & Fm1 & Fm2 & Fm3 & Fvs & Fxs & Fxp & Fs0 & Fli & Fal).
    rewrite (wk_tp H w OK) in Ferr.
    split; [exact Frh|]. split; [exact Fso|]. split; [exact Flo|]. split; [exact Fpr|]. split; [exact Fps|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Fm1|]. split; [exact Fm2|]. split; [exact Fm3|]. split; [exact Fvs|].
    split; [intros q k Hq; apply (Hbsz q k); rewrite (state_blocks_of w c), Htr, app_nil_r; exact Hq|].
    split; [exact MI|]. split; [exists errv'; exact Ferr|].
    split; [exact Faux|]. split; [exact AC|]. split; [exact Fs0|]. split; [exact Fli|]. split; [exact Fal|].
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_papp H w OK) as (PA & P0 & P16).
    pose proof (p_range H w OK) as (PR1 & PR2).
    destruct (fin_apart_obj H HHbp w (wa_p w) PARSER_SIZE OK (wk_pobj H w OK) PA ltac:(lia) ltac:(unfold PARSER_SIZE; lia) PR2) as [FP FPs].
    assert (PEQ : forall a, wa_p w <= a < wa_p w + PARSER_SIZE -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. apply (fin_munch_eq H w W m m' a MU FW); [unfold PARSER_SIZE in *; lia|].
      eapply fin_apart_sub; [exact FP | lia | lia | lia]. }
    intros i Hi. cbn [piw_ofA pw_p] in Hi |- *. unfold PARSER_SIZE in *.
    rewrite (PEQ (wa_p w + i) ltac:(lia)). exact (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X i Hi).
  Qed.

  Lemma pm_fin_pix : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl lw m' W,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] 0 -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pi_moreA H w lw c ->
    munch W m m' -> wmono asegs m m' -> Forall (fin_ivl H w) W -> mem_inv asegs m' -> ACONST m' ->
    PIX H LINV (piw_ofA w) s LB LBs m' c.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl lw m' W OK X Htr Hbsz MO MU WM FW MI AC.
    destruct (pm_fin H HHbp LINV LINV_frame w s LB LBs m mo c ins tbl ftbl 0 m' W OK X Htr MU WM FW)
      as (errv' & XSf & Ferr & Faux & Frh & Fso & Flo & Fpr & Fps & Fm1 & Fm2 & Fm3 & Fvs & Fxs & Fxp & Fs0 & Fli & Fal).
    rewrite (wk_tp H w OK) in Ferr.
    destruct MO as (M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_papp H w OK) as (PA & P0 & P16).
    pose proof (wk_capp H w OK) as (CA & C0 & C16).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof (aapp_below_aceil _ _ CA) as C4.
    destruct (fin_apart_obj H HHbp w (wa_p w) PARSER_SIZE OK (wk_pobj H w OK) PA ltac:(lia) ltac:(unfold PARSER_SIZE; lia) PR2) as [FP FPs].
    destruct (fin_apart_obj H HHbp w (wa_cons w) 48 OK (wk_cobj H w OK) CA ltac:(lia) ltac:(lia) C4) as [FC FCs].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2]. rewrite app_nil_r in OWN1.
    pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SHc & SHp & SHk).
    assert (BL : forall A n, In (A, n) (c_blocks c) -> In (A, n) (lbl LB)).
    { intros A n Hb. apply (Permutation_in _ (Permutation_sym OWN2)) in Hb.
      apply lbl_in_inv in Hb as [pid Hb]. apply (lbl_in LB pid).
      apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff. right. exact Hb. }
    assert (PEQ : forall a, wa_p w <= a < wa_p w + PARSER_SIZE -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. apply (fin_munch_eq H w W m m' a MU FW); [unfold PARSER_SIZE in *; lia|].
      eapply fin_apart_sub; [exact FP | lia | lia | lia]. }
    assert (CEQ : forall a, wa_cons w <= a < wa_cons w + 48 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha. apply (fin_munch_eq H w W m m' a MU FW); [lia|].
      eapply fin_apart_sub; [exact FC | lia | lia | lia]. }
    assert (FKp : forall a k v, fld ASEGS m a k v -> wa_p w <= a -> a + Z.of_nat k <= wa_p w + PARSER_SIZE -> fld ASEGS m' a k v).
    { intros a k v Fd H1 H2. eapply fld_munch; [exact Fd | exact MU | | lia | unfold PARSER_SIZE in *; lia].
      apply (disjoint_of_fin H w W); [exact FW|]. eapply fin_apart_sub; [exact FP | lia | lia | lia]. }
    assert (FKc : forall a k v, fld ASEGS m a k v -> wa_cons w <= a -> a + Z.of_nat k <= wa_cons w + 48 -> fld ASEGS m' a k v).
    { intros a k v Fd H1 H2. eapply fld_munch; [exact Fd | exact MU | | lia | lia].
      apply (disjoint_of_fin H w W); [exact FW|]. eapply fin_apart_sub; [exact FC | lia | lia | lia]. }
    assert (BEQ : forall A n a, In (A, n) (c_blocks c) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros A n a Hb Ha. pose proof (BL A n Hb) as HL.
      destruct (fin_apart_lbl H HHbp w s LB m A n OK RH HL) as [FA _].
      destruct (lbl_in_inv LB A n HL) as [pid Hpb].
      pose proof (ah_blocks H HHx2 _ _ _ _ RH Hpb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn in R0, Rn, RC.
      apply (fin_munch_eq H w W m m' a MU FW); [lia|]. eapply fin_apart_sub; [exact FA | lia | lia | lia]. }
    destruct (pmc_keep_gen (wa_p w) (lbl LB) (lbl LB) m m' c
                (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
                (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
                SHc ltac:(lia) ltac:(unfold PARSER_SIZE, AAPP_HI in *; lia))
      as (U1 & U2 & U3 & V1 & V2 & V3 & SH').
    { intros a Ha. apply PEQ. unfold O_M1 in Ha. lia. }
    { exact BEQ. }
    { intros A n sbs Hb Hl Sh. exact (fin_SHAD_lbl H HHbp w s LB m m' W A n sbs OK RH MU WM FW (BL A n Hb) Hl Sh). }
    { intros b _ Hb. exact Hb. }
    constructor.
    - exact Frh.
    - exact Flo.
    - split; [exact OWN1 | exact OWN2].
    - exact (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
    - exact MI.
    - exists errv'. exact Ferr.
    - exact Faux.
    - exact AC.
    - exact Fs0.
    - exact Fli.
    - pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4). cbn [piw_ofA pw_s0 pw_n]. lia.
    - intros i Hi. cbn [piw_ofA pw_p] in Hi |- *. rewrite (PEQ (wa_p w + i) ltac:(lia)). exact (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X i Hi).
    - exact (FKp _ _ _ (xa_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia) ltac:(unfold PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_user _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia) ltac:(unfold PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_hdrfn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia) ltac:(unfold PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_insfn _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia) ltac:(unfold PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_hunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia) ltac:(unfold PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_words _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(unfold O_WORDS; lia) ltac:(unfold O_WORDS, PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(unfold O_N; lia) ltac:(unfold O_N, PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_diag _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(unfold O_DIAG; lia) ltac:(unfold O_DIAG, PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(unfold O_WIDX; lia) ltac:(unfold O_WIDX, PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_icount _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(unfold O_ICOUNT; lia) ltac:(unfold O_ICOUNT, PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(unfold O_ENDIAN; lia) ltac:(unfold O_ENDIAN, PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_flags _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(unfold O_FLAGS; lia) ltac:(unfold O_FLAGS, PARSER_SIZE; lia)).
    - exact (FKp _ _ _ (xa_retry _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(unfold O_FLAGS; lia) ltac:(unfold O_FLAGS, PARSER_SIZE; lia)).
    - exact (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X).
    - exact (FKc _ _ _ (xa_consf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia) ltac:(lia)).
    - intros i Hi. cbn [piw_ofA pw_cons] in Hi |- *. rewrite (CEQ (wa_cons w + 32 + i) ltac:(lia)). exact (xa_consd _ _ _ _ _ _ _ _ _ _ _ _ _ _ X i Hi).
    - exact (wr_at_wmono _ _ _ _ (xa_consw _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) WM).
    - intros NZ i Hi. cbn [piw_ofA pw_words pw_n] in NZ, Hi |- *.
      destruct (wk_words H w OK) as [[W0 _]|(pw & k & Hin & Hk & W0 & W16 & Wtop & WD & WS)]; [contradiction|].
      assert (HL : In (wa_words w, k) (lbl LB)).
      { apply (lbl_in LB pw). apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff. left. exact Hin. }
      destruct (fin_apart_lbl H HHbp w s LB m (wa_words w) k OK RH HL) as [FA _].
      rewrite (fin_munch_eq H w W m m' (wa_words w + i) MU FW ltac:(lia) ltac:(eapply fin_apart_sub; [exact FA | lia | lia | lia])).
      exact (xa_wbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X NZ i Hi).
    - exact U1.
    - exact U2.
    - exact U3.
    - exact V1.
    - exact V2.
    - exact V3.
    - split; [exact SH'|].
      split; [eapply addressable_transport; [exact SHp | exact MU | exact WM | exact (disjoint_of_fin H w W _ _ FW FPs)]|].
      eapply addressable_transport; [exact SHk | exact MU | exact WM | exact (disjoint_of_fin H w W _ _ FW FCs)].
    - exact Htr.
    - exact Hbsz.
    - exact M1.
    - split; [exact M2 | exact M3].
    - split; [exact M4 | exact M5].
    - exact M6.
    - split; [exact M7|]. split; [exact M8 | exact M9].
  Qed.

  Lemma pmx_words_keep : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal m' XS,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal ->
    piw_ok H (piw_ofA w) (wa_LF0 w) (wa_m0 w) -> as_RFS H (wa_LF0 w) m' ->
    Forall (fs_scratch H (wa_LF0 w)) XS ->
    xpres H (wa_LB0 w) (wa_sp0 w) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (wa_p w, wa_p w + PARSER_SIZE) :: XS) (wa_m0 w) m' ->
    words_okA (wa_LB0 w) m' (wa_words w) (wa_n w).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl spal m' XS OK X K RFS FXS XP.
    pose proof (pk_words _ _ _ _ K) as (pw & k & Hin & Hk & W0 & W16 & Wtop & WD & WS).
    cbn [piw_ofA pw_LB0 pw_words pw_n] in Hin, Hk, W0, W16, Wtop, WD, WS.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _]. rewrite app_nil_r in OWN1.
    assert (HinL : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff. left. exact Hin. }
    pose proof (ah_blocks H HHx2 _ _ _ _ RH HinL) as (B0 & B16 & Bn & BI & BC & BF & BA). cbn [blk_addr blk_size fst snd] in *.
    pose proof (pk_papp _ _ _ _ K) as (PA & PA0 & PA16). cbn [piw_ofA pw_p] in PA, PA0, PA16.
    destruct (pk_pin _ _ _ _ K) as (f & Hf & Pf1 & Pf2). cbn [piw_ofA pw_p] in Pf1, Pf2.
    pose proof (proj2 (ah_RFS_range H HHx2 _ _ RFS) f Hf) as FR. unfold aframe_range in FR.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (FO : fsobj H (wa_LF0 w) (wa_words w) k) by (eapply fsobj_block; [exact HHx2 | exact RH | exact HinL]).
    assert (D1 : Forall (fun iv : Z * Z => wa_words w + k <= fst iv \/ snd iv <= wa_words w) XS).
    { eapply Forall_impl; [| exact FXS]. intros iv Hiv.
      eapply fsobj_scratch; [exact HHx2 | exact RFS | exact FO | lia | lia | unfold AAPP_HI in *; lia | exact BA | exact Hiv]. }
    assert (D2 : Forall (fun iv : Z * Z => sh (wa_words w) + nsh k <= fst iv \/ snd iv <= sh (wa_words w)) XS).
    { eapply Forall_impl; [| exact FXS]. intros iv Hiv.
      eapply fsobj_scratch_sh; [exact HHx2 | exact RFS | exact FO | lia | lia | unfold AAPP_HI in *; lia | exact Hiv]. }
    exists pw, k. split; [exact Hin|]. split; [exact Hk|]. split; [exact W0|]. split; [exact W16|]. split; [exact Wtop|]. split.
    - eapply xpres_mdef; [exact XP | exact WD | | lia | unfold AAPP_HI in *; lia].
      split.
      + right; right; left. exists (pw, wa_words w, k). cbn [blk_addr blk_size fst snd]. split; [exact Hin | lia].
      + apply Forall_cons; [cbn [fst snd]; unfold RtB_Td.ATDLOC, AIMG_TOP in *; lia|].
        apply Forall_cons; [cbn [fst snd]; unfold PARSER_SIZE, AFS_HDR in *; lia|].
        eapply Forall_impl; [| exact D1]. intros iv Hiv. cbn beta in *. lia.
    - eapply xpres_SHAD; [exact XP | exact WS |].
      rewrite cc_gen_length by lia.
      split.
      + right; right; right; left. exists (pw, wa_words w, k). cbn [blk_addr blk_size fst snd]. split; [exact Hin | lia].
      + pose proof (sh_in_shadowland (wa_words w) ltac:(unfold AAPP_HI in *; lia)) as SL.
        pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE (wa_words w) k PA ltac:(lia) ltac:(unfold AAPP_HI in *; lia) ltac:(lia)) as SP.
        apply Forall_cons; [cbn [fst snd]; unfold RtB_Td.ATDLOC, ALOWSH_LO in *; lia|].
        apply Forall_cons; [cbn [fst snd]; lia|].
        exact D2.
  Qed.
End Fin2.

Section Epi.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Lemma HHe : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_epi_go : forall (w : pmwA H) s LB LBs m mo c tbl spal msF R F fc (pc : Z) ins (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl [] [] spal -> incl TBL_EXIT tbl ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_EXIT ->
    (pc = EXIT_RET /\ ins = S_INSTR) \/ (pc = EXIT_OPC /\ ins = [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC])
      \/ (pc = EXIT_IWC /\ ins = [OB_INST; OB_FIRST_WORD; OB_INST_WC] /\ PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w)) ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf0f3c) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c [] TBL_EXIT [] [] spal -> regs_tbl w R1 RT_F3C ->
       (forall r, In r [3%bv; 4%bv; 23%bv] -> PropExec.getr R1 r = PropExec.getr R r) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c tbl spal msF R F fc pc ins Q OK X Hi KR VIS RF HT PC K.
    pose proof (pmxa_restrict H HHe LINV LINV_frame w s LB LBs m mo c ins tbl [] [] spal TBL_EXIT [] OK X Hi (incl_refl _)) as X'.
    clear X.
    destruct PC as [[-> ->]|[[-> ->]|(-> & -> & A1)]].
    - unfold EXIT_RET in VIS.
      pm_go HHe LINV_frame OK X' KR VIS RF HT (@nil word) (@nil kentry) 40%nat [0xf0f3c] (@nil bool) 41%N
            (@nil nat) (@nil Z) (@nil Z) TBL_EXIT (@nil (Z * expr)) RT_F3C.
      + split_scs.
      + intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 HR1 _. eapply K; [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact HT1 |].
        intros r Hr. rewrite (HR1 r).
        repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity |]); destruct Hr.
    - unfold EXIT_OPC in VIS.
      pm_go HHe LINV_frame OK X' KR VIS RF HT (@nil word) (@nil kentry) 40%nat [0xf0f3c] (@nil bool) 41%N
            (@nil nat) (@nil Z) (@nil Z) TBL_EXIT (@nil (Z * expr)) RT_F3C.
      + split_scs.
      + intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 HR1 _. eapply K; [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact HT1 |].
        intros r Hr. rewrite (HR1 r).
        repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity |]); destruct Hr.
    - assert (HT' : regs_tbl w R RT_F3C).
      { unfold RT_F3C, regs_tblX. apply Forall_app. split; [exact HT|].
        apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. rewrite A1. reflexivity. }
      unfold EXIT_IWC in VIS.
      pm_go HHe LINV_frame OK X' KR VIS RF HT' (@nil word) (@nil kentry) 40%nat [0xf0f3c] (@nil bool) 41%N
            (@nil nat) (@nil Z) (@nil Z) TBL_EXIT (@nil (Z * expr)) RT_F3C.
      + split_scs.
      + intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 HR1 _. eapply K; [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact HT1 |].
        intros r Hr. rewrite (HR1 r).
        repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity |]); destruct Hr.
  Qed.

  Lemma pm_epi_b : forall (w : pmwA H) s LB LBs m mo c spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [] TBL_EXIT [] [] spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf0f3c) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_F3C ->
    (forall msF2 mo2 R2 M2, munch [(wa_ff w, wa_ff w + 8)] m M2 -> wmono asegs m M2 -> mem_inv asegs M2 -> as_MPRES H mo mo2 ->
       as_AKREL H s (mkCfg msF2 mo2) -> as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0x9e65c) fc None M2 (seg_rom asegs) -> rfull R2 ->
       PropExec.getr R2 1%bv = Z_to_bv 64 0xf0f5c -> PropExec.getr R2 2%bv = Z_to_bv 64 (wa_s1 w) ->
       PropExec.getr R2 8%bv = Z_to_bv 64 (wa_sp0 w) ->
       PropExec.getr R2 10%bv = Z_to_bv 64 (wa_ff w) -> PropExec.getr R2 11%bv = Z_to_bv 64 11584 ->
       (forall r, In r [3%bv; 4%bv; 23%bv] -> PropExec.getr R2 r = PropExec.getr R r) ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c spal msF R F fc Q OK X KR VIS RF HT K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose (E := Eseed R (wenv_vals w ++ [])).
    pose proof (regs_ok_of_tbl w R RT_F3C [] 41%N HT ltac:(vm_compute; reflexivity)) as HR.
    assert (HK : know_ok asegs E m [KRange (EVar WV_FF) (AIMG_TOP + AFS_HDR) (2 ^ 47); KWr (SA (EVar WV_FF) 0) (ELit 8)]).
    { pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FW. change (fsz PM_FCLASS) with 16384 in FW.
      assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by reflexivity.
      assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (rewrite EF; apply u64_of_Z; lia).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - cbn [kentry_ok]. rewrite UF. unfold AIMG_TOP, AFS_HDR in *. lia.
      - eapply (kwr_of_wr_at asegs E m (wa_ff w) 16384); [exact FW | | |].
        + unfold estart. cbn [a_base a_off]. rewrite UF. lia.
        + unfold estart, elenZ. cbn [a_base a_off]. rewrite UF. change (edenot E (ELit 8)) with (Z_to_bv 64 8). rewrite u64_of_Z by lia. lia.
        + unfold elenZ. change (edenot E (ELit 8)) with (Z_to_bv 64 8). rewrite u64_of_Z by lia. lia. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xf0f3c m (seg_rom asegs) HR HK 20%nat [0x9e65c] (SCR [] [] []) 41%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg => set (LOG3 := lg) in * end.
    lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ ?mm _) => change mm with (mem_denot E m LOG3) in Hms end.
    set (M2 := mem_denot E m LOG3) in Hms.
    assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (change (edenot E (EVar WV_FF)) with (Z_to_bv 64 (wa_ff w)); apply u64_of_Z; lia).
    assert (MU3 : munch [(wa_ff w, wa_ff w + 8)] m M2).
    { pose proof (munch_sym E m LOG3 [(EVar WV_FF, 0, 8)] Hlf ltac:(vm_compute; reflexivity)) as MS3.
      cbn [num_wins map] in MS3. rewrite UF in MS3. replace (wa_ff w + 0) with (wa_ff w) in MS3 by lia. exact MS3. }
    assert (WM3 : wmono asegs m M2) by (subst M2; apply LbB_Conv.wmono_mem_denot).
    assert (MI3 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)).
    assert (Y1 : PropExec.getr R' 1%bv = Z_to_bv 64 0xf0f5c) by (rewrite (HR' 1%bv); reflexivity).
    assert (Y2 : PropExec.getr R' 2%bv = Z_to_bv 64 (wa_s1 w)) by (rewrite (HR' 2%bv); reflexivity).
    assert (Y8 : PropExec.getr R' 8%bv = Z_to_bv 64 (wa_sp0 w)) by (rewrite (HR' 8%bv); reflexivity).
    assert (Y10 : PropExec.getr R' 10%bv = Z_to_bv 64 (wa_ff w)) by (rewrite (HR' 10%bv); reflexivity).
    assert (Y11 : PropExec.getr R' 11%bv = Z_to_bv 64 11584) by (rewrite (HR' 11%bv); reflexivity).
    assert (YK : forall r, In r [3%bv; 4%bv; 23%bv] -> PropExec.getr R' r = PropExec.getr R r).
    { intros r Hr. rewrite (HR' r). repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity |]); destruct Hr. }
    assert (RF' : rfull R') by exact (msteps_full asegs _ _ Hms RF).
    eapply (sr_blk H HHe _ s msF mo R F (Z_to_bv 64 0xf0f3c) fc m (seg_rom asegs) R' (Z_to_bv 64 0x9e65c) M2 KR VIS RF Hms).
    intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R' RF') in VIS2.
    exact (K msF2 mo2 R' M2 MU3 WM3 MI3 MP2 KR2 VIS2 RF' Y1 Y2 Y8 Y10 Y11 YK).
  Qed.

  Lemma pm_epi_call : forall (w : pmwA H) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word) (fc0 : bv 32)
      (c0 : pmc) (lw r : Z) s LB LBs m mo c ins tbl ftbl spal msF2 mo2 R2 F fc M2,
    pmw_okA H w -> wa_sp0 w = bv_unsigned sp -> wa_saved w = [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra] ->
    piw_ok H (piw_ofA w) (wa_LF0 w) (wa_m0 w) -> c_widx c0 <= lw ->
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    munch [(wa_ff w, wa_ff w + 8)] m M2 -> wmono asegs m M2 -> mem_inv asegs M2 -> as_MPRES H mo mo2 ->
    as_AKREL H s (mkCfg msF2 mo2) -> as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0x9e65c) fc None M2 (seg_rom asegs) -> rfull R2 ->
    frm_zero fc ->
    PropExec.getr R2 1%bv = Z_to_bv 64 0xf0f5c -> PropExec.getr R2 2%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R2 3%bv = gp -> PropExec.getr R2 4%bv = tp -> PropExec.getr R2 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R2 10%bv = Z_to_bv 64 (wa_ff w) -> PropExec.getr R2 11%bv = Z_to_bv 64 11584 ->
    PropExec.getr R2 23%bv = Z_to_bv 64 r -> - 2 ^ 31 <= r < 2 ^ 31 ->
    (r = 0 -> spal = 0 /\ pi_moreA H w lw c) ->
    as_SR H (pi_post H LINV (piw_ofA w) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 (wa_LF0 w) c0 (wa_m0 w) (wa_mo0 w))
      (mkCfg msF2 mo2).
  Proof.
    intros w ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 c0 lw r s LB LBs m mo c ins tbl ftbl spal msF2 mo2 R2 F fc M2
           OK Hsp Hsav K0 Hlw X Htr Hbsz MU3 WM3 MI3 MP2 KR2 VIS2 RF2 FZ Y1 Y2 Y3 Y4 Y8 Y10 Y11 Y23 Hr Hok.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    rewrite (rfull_eq R2 RF2) in VIS2.

    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10). change (fsz PM_FCLASS) with 16384 in *.
    pose proof (wk_stack H w OK) as (SK1 & SK2 & SK3 & SK4 & SK5 & SK6).
    pose proof (wk_s1 H w OK) as (WS1 & WS2).
    assert (STK2 : stk asegs M2 (wa_lo w) (wa_s1 w)).
    { destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia)) as [ST1 _].
      eapply (stk_transport_disjoint asegs _ m M2 _ _ ST1 MU3 WM3). cbn [disjoint_from]. split; [right; lia | exact I]. }
    assert (RFS2 : as_RFS H (PMLF H w) M2).
    { eapply (ah_RFS_frame H HHe); [exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU3 | exact WM3 |].
      apply Forall_cons; [| apply Forall_nil]. unfold afs_write_ok. right. exists (PM_FCLASS, wa_ff w, wa_fp w).
      split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (fsz PM_FCLASS) with 16384. lia. }
    assert (FFL2 : rw_cells asegs M2 (wa_ff w + fsz 8 - 8) [C8 (Z_to_bv 64 (wa_fp w))]).
    { eapply rw_cells_transport; [exact (xa_fflag _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU3 | exact WM3 |].
      cbn [disjoint_from cells_size csize Nat.add]. change (fsz 8) with 16384. split; [right; lia | exact I]. }
    assert (ACM2 : ACONST M2).
    { eapply ACONST_frame; [exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU3 | exact WM3 |].
      apply Forall_cons; [| apply Forall_nil]. apply aconst_ok_of_x.
      destruct F8 as [(L1 & L2)|(L1 & L2)].
      - right. unfold AIMG_TOP, AFS_HDR, AFS_SIZE, ALOWSH_LO in *. lia.
      - left. replace (sh AIMG_TOP) with 2148356096 by reflexivity. unfold AHI_LO, AFS_HDR in *. lia. }
    pose proof (rt_bp_ext H HHbp) as EXT. destruct EXT as (_ & _ & _ & _ & _ & _ & _ & _ & SF8 & _).
    eapply (ahh_evt_then H HHe _ _ s msF2 _ mo2 KR2 VIS2).
    { eapply (SF8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc M2 (PMLF H w) (wa_ff w) (wa_fp w) (wa_lo w) 11584);
        [exact RFS2 | left; reflexivity | exact Y10 | exact FFL2 | exact Y11 | change (fsz 8) with 16384; lia | reflexivity
        | rewrite Y2, u64_of_Z by (unfold AAPP_HI in *; lia); exact STK2 | exact SK1 | rewrite Y2, u64_of_Z by (unfold AAPP_HI in *; lia); unfold AFS_STACK, APM_STACK in *; lia
        | exact MI3 | exact ACM2]. }
    intros msF3 mo3 KR3 MP3 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & M3 & VIS3 & MU4 & WM4 & MI4 & STK4 & RFS4 & SH4 & ACM4).
    rewrite Y1, (ret_pc_even 0xf0f5c ltac:(lia) eq_refl) in VIS3. rewrite Y2, u64_of_Z in MU4, STK4 by (unfold AAPP_HI in *; lia).
    change (11584 / 8) with 1448 in MU4.

    assert (SAV3 : rw_cells asegs M3 (wa_sp0 w - 104) (map C8 (wa_saved w))).
    { pose proof (xa_saved _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SV.
      assert (Q5' : sh (wa_ff w) + 2048 <= aceil) by lia.
      eapply rw_cells_transport; [eapply rw_cells_transport; [exact SV | exact MU3 | exact WM3 |] | exact MU4 | exact WM4 |].
      - rewrite cells_size_mapC8, (wk_saved H w OK). cbn [disjoint_from]. split; [right; lia | exact I].
      - rewrite cells_size_mapC8, (wk_saved H w OK). cbn [disjoint_from]. unfold AFS_STACK.
        split; [right; lia|]. split; [right; unfold AFS_HDR, AFS_SIZE in *; lia|]. split; [right; lia | exact I]. }
    rewrite Hsav in SAV3.

    lazymatch type of VIS3 with _ = MS ?RR _ _ _ _ _ _ => set (R5 := RR) in VIS3 end.
    pose (E5 := Eseed R5 (wenv_vals w ++ [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra])).
    assert (HR5 : regs_ok E5 (srs sr_id [(8%bv, EVar WV_SP0)]) R5).
    { apply regs_ok_srs; [apply regs_ok_seed|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      split; [intros Hx; discriminate Hx|]. subst R5. transitivity (PropExec.getr R2 8%bv); [reflexivity | rewrite Y8; reflexivity]. }
    assert (U34 : bv_unsigned (edenot E5 (EVar WV_SP0)) = wa_sp0 w) by (change (edenot E5 (EVar WV_SP0)) with (Z_to_bv 64 (wa_sp0 w)); apply u64_of_Z; unfold AAPP_HI in *; lia).
    assert (HK5 : know_ok asegs E5 M3 [KRange (EVar WV_SP0) 140735332483072 (2 ^ 47);
                                  KWord (SA (EVar WV_SP0) (-104)) 8 (EVar 41);
                                  KWord (SA (EVar WV_SP0) (-96)) 8 (EVar 42);
                                  KWord (SA (EVar WV_SP0) (-88)) 8 (EVar 43);
                                  KWord (SA (EVar WV_SP0) (-80)) 8 (EVar 44);
                                  KWord (SA (EVar WV_SP0) (-72)) 8 (EVar 45);
                                  KWord (SA (EVar WV_SP0) (-64)) 8 (EVar 46);
                                  KWord (SA (EVar WV_SP0) (-56)) 8 (EVar 47);
                                  KWord (SA (EVar WV_SP0) (-48)) 8 (EVar 48);
                                  KWord (SA (EVar WV_SP0) (-40)) 8 (EVar 49);
                                  KWord (SA (EVar WV_SP0) (-32)) 8 (EVar 50);
                                  KWord (SA (EVar WV_SP0) (-24)) 8 (EVar 51);
                                  KWord (SA (EVar WV_SP0) (-16)) 8 (EVar 52);
                                  KWord (SA (EVar WV_SP0) (-8)) 8 (EVar 53)]).
    { apply Forall_cons; [cbn [kentry_ok]; rewrite U34; unfold AAPP_HI in *; lia|].
      repeat (apply Forall_cons;
        [ lazymatch goal with |- kentry_ok _ _ _ (KWord (SA _ ?off) _ _) =>
            let k := eval compute in (Z.to_nat (off + 104)) in
            eapply (kword_of_rw_cells asegs E5 M3 (wa_sp0 w - 104) (map C8 [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra]) k (C8 _) _ _ 8%nat SAV3);
            [ reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite U34; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
            | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold AAPP_HI in *; lia | reflexivity ]
          end |]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R5 0xf0f5c M3 (seg_rom asegs) HR5 HK5 30%nat [0xf0fac] (SCR [] [] []) 54%N.
    { split_scs. }

    rename R' into R6. rename HR' into HR6. rename Hms into Hms6. rename Hlf into Hlf6.
    lazymatch type of Hms6 with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms6 end.
    assert (HF5 : rfull R5) by (unfold R5; apply rfull_mkR).
    assert (HF6 : rfull R6) by exact (msteps_full asegs _ _ Hms6 HF5).
    assert (K1 : PropExec.getr R6 1%bv = ra) by (rewrite (HR6 1%bv); reflexivity).
    assert (K2 : PropExec.getr R6 2%bv = sp).
    { rewrite (HR6 2%bv). transitivity (Z_to_bv 64 (wa_sp0 w)); [reflexivity | rewrite Hsp; apply Z_to_bv_bv_unsigned]. }
    assert (K3 : PropExec.getr R6 3%bv = gp).
    { rewrite (HR6 3%bv). transitivity (PropExec.getr R2 3%bv); [reflexivity | exact Y3]. }
    assert (K4 : PropExec.getr R6 4%bv = tp).
    { rewrite (HR6 4%bv). transitivity (PropExec.getr R2 4%bv); [reflexivity | exact Y4]. }
    assert (K8 : PropExec.getr R6 8%bv = s0) by (rewrite (HR6 8%bv); reflexivity).
    assert (K9 : PropExec.getr R6 9%bv = s1) by (rewrite (HR6 9%bv); reflexivity).
    assert (K10 : PropExec.getr R6 10%bv = Z_to_bv 64 r).
    { rewrite (HR6 10%bv).
      transitivity (sext 64 (alu32 ALU_ADD (low32 (PropExec.getr R5 23%bv)) (low32 (Z_to_bv 64 0)))); [reflexivity|].
      change (PropExec.getr R5 23%bv) with (PropExec.getr R2 23%bv). rewrite Y23. apply sextw_i32. exact Hr. }
    assert (K18 : PropExec.getr R6 18%bv = s2) by (rewrite (HR6 18%bv); reflexivity).
    assert (K19 : PropExec.getr R6 19%bv = s3) by (rewrite (HR6 19%bv); reflexivity).
    assert (K20 : PropExec.getr R6 20%bv = s4) by (rewrite (HR6 20%bv); reflexivity).
    assert (K21 : PropExec.getr R6 21%bv = s5) by (rewrite (HR6 21%bv); reflexivity).
    assert (K22 : PropExec.getr R6 22%bv = s6) by (rewrite (HR6 22%bv); reflexivity).
    assert (K23 : PropExec.getr R6 23%bv = s7) by (rewrite (HR6 23%bv); reflexivity).
    assert (K24 : PropExec.getr R6 24%bv = s8) by (rewrite (HR6 24%bv); reflexivity).
    assert (K25 : PropExec.getr R6 25%bv = s9) by (rewrite (HR6 25%bv); reflexivity).
    assert (K26 : PropExec.getr R6 26%bv = s10) by (rewrite (HR6 26%bv); reflexivity).
    assert (K27 : PropExec.getr R6 27%bv = s11) by (rewrite (HR6 27%bv); reflexivity).

    assert (MUa : munch ([(wa_ff w, wa_ff w + 8)] ++ [(wa_s1 w - AFS_STACK, wa_s1 w); (wa_fp w, wa_fp w + 1); (sh (wa_ff w), sh (wa_ff w) + 1448)]) m M3)
      by exact (LbB_Conv.munch_app _ _ _ _ _ MU3 MU4).
    assert (WMa : wmono asegs m M3) by exact (wmono_trans asegs _ _ _ WM3 WM4).
    assert (FWa : Forall (fin_ivl H w) ([(wa_ff w, wa_ff w + 8)] ++ [(wa_s1 w - AFS_STACK, wa_s1 w); (wa_fp w, wa_fp w + 1); (sh (wa_ff w), sh (wa_ff w) + 1448)])).
    { unfold AFS_STACK, APM_STACK in *. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; unfold fin_ivl; cbn [fst snd]; change (fsz PM_FCLASS) with 16384.
      - right; left. lia.
      - left. lia.
      - right; right; right. lia.
      - right; right; left. unfold PM_NSH. lia. }
    destruct (pm_fin H HHbp LINV LINV_frame w s LB LBs m mo c ins tbl ftbl spal M3 _ OK X Htr MUa WMa FWa)
      as (errv' & XSf & Ferr & Faux & Frh & Fso & Flo & Fpr & Fps & Fm1 & Fm2 & Fm3 & Fvs & Fxs & Fxp & Fs0 & Fli & Fal).
    assert (STKf : stk asegs M3 (wa_lo w) (wa_sp0 w)).
    { eapply stk_wmono_fin; [exact (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact WMa | lia]. }
    assert (RFSf : as_RFS H (wa_LF0 w) M3).
    { unfold PMLF in RFS4. cbn [lf_remove ff_addr fst snd] in RFS4. rewrite Z.eqb_refl in RFS4. exact RFS4. }
    assert (WK : words_okA (wa_LB0 w) M3 (wa_words w) (wa_n w))
      by exact (pmx_words_keep H HHbp LINV w s LB LBs m mo c ins tbl ftbl spal M3 XSf OK X K0 RFSf Fxs Fxp).
    assert (PK : piw_ok H (piw_ofA w) (wa_LF0 w) M3).
    { destruct K0. constructor; assumption. }
    assert (FIN : (r = 0 /\ exists c' : pmc, PIX H LINV (piw_ofA w) s LB LBs M3 c' /\ c_widx c0 < c_widx c')
                  \/ (r <> 0 /\ exists c' : parserC, pi_err H LINV (piw_ofA w) s LB LBs M3 c')).
    { destruct (Z.eq_dec r 0) as [R0|R0].
      - left. split; [exact R0|]. destruct (Hok R0) as [Hs0 MO]. subst spal. exists c. split.
        + exact (pm_fin_pix H HHbp LINV LINV_frame w s LB LBs m mo c ins tbl ftbl lw M3 _ OK X Htr Hbsz MO MUa WMa FWa MI4 ACM4).
        + destruct MO as (L0 & _). lia.
      - right. split; [exact R0|]. exists (prc_ofA w c).
        exact (pm_fin_err H HHbp LINV LINV_frame w s LB LBs m mo c ins tbl ftbl spal M3 _ OK X Htr Hbsz MUa WMa FWa MI4 ACM4). }
    pose proof (xa_mpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MP0.
    eapply (sr_evt H HHe) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (PropExec.getr R6 5) (PropExec.getr R6 6) (PropExec.getr R6 7) s0 s1
                                   (Z_to_bv 64 r)
                                   (PropExec.getr R6 11) (PropExec.getr R6 12) (PropExec.getr R6 13) (PropExec.getr R6 14)
                                   (PropExec.getr R6 15) (PropExec.getr R6 16) (PropExec.getr R6 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                   (PropExec.getr R6 28) (PropExec.getr R6 29) (PropExec.getr R6 30) (PropExec.getr R6 31))
                              F (ret_pc ra) fc None M3 (seg_rom asegs));
      [exact KR3 | exact VIS3 | |].
    { eapply evt_of_msteps; [exact Hms6|]. rewrite (rfull_eq R6 HF6). apply pm_ret_ok.
      rewrite K1, K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. reflexivity. }
    intros msF4 mo4 KR4 MP4 HP. cbv beta in HP.
    exists (PropExec.getr R6 5), (PropExec.getr R6 6), (PropExec.getr R6 7), r,
      (PropExec.getr R6 11), (PropExec.getr R6 12), (PropExec.getr R6 13), (PropExec.getr R6 14), (PropExec.getr R6 15),
      (PropExec.getr R6 16), (PropExec.getr R6 17), (PropExec.getr R6 28), (PropExec.getr R6 29), (PropExec.getr R6 30),
      (PropExec.getr R6 31), M3, s, LB, LBs, XSf, F, fc.
    cbn [cfg_ms cfg_model].
    split; [exact HP|]. split; [exact FZ|]. split; [exact Hr|]. split; [exact KR4|].
    split; [eapply (ah_mpres_trans H HHe); [exact MP0 | eapply (ah_mpres_trans H HHe); [exact MP2 | eapply (ah_mpres_trans H HHe); [exact MP3 | exact MP4]]]|].
    split; [rewrite <- Hsp; exact STKf|]. split; [exact RFSf|]. split; [exact PK|]. split; [exact Fxs|].
    split; [rewrite <- Hsp; exact Fxp|].
    exact FIN.
  Qed.

  Lemma pm_exit : forall (w : pmwA H) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word) (fc0 : bv 32)
      (c0 : pmc) (lw : Z),
    pmw_okA H w -> wa_sp0 w = bv_unsigned sp -> wa_ra w = bv_unsigned ra ->
    wa_saved w = [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra] -> wa_gp w = gp -> wa_tp w = tp ->
    piw_ok H (piw_ofA w) (wa_LF0 w) (wa_m0 w) -> c_widx c0 <= lw ->
    EXITKA H LINV w lw (pi_post H LINV (piw_ofA w) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 (wa_LF0 w) c0 (wa_m0 w) (wa_mo0 w)).
  Proof.
    intros w ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 c0 lw OK Hsp Hra Hsav Hgp Htp K0 Hlw.
    intros s LB LBs m mo c msF R F fc pc ins r EX PC.
    destruct EX as [(tbl & spal & X & Hi & Hsp0) KR VIS RF FZ HT G3 G4 (G23 & Hr) Htr Hbsz Hok].
    eapply (pm_epi_go w s LB LBs m mo c tbl spal msF R F fc pc ins _ OK X Hi KR VIS RF HT PC).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 HK1.
    eapply (pm_epi_b w s LB LBs m1 mo1 c spal msF1 R1 F fc _ OK X1 KR1 VIS1 RF1 HT1).
    intros msF2 mo2 R2 M2 MU3 WM3 MI3 MP2 KR2 VIS2 RF2 Y1 Y2 Y8 Y10 Y11 HK2.
    assert (Z3 : PropExec.getr R2 3%bv = gp) by (rewrite (HK2 3%bv ltac:(inb)), (HK1 3%bv ltac:(inb)), G3; exact Hgp).
    assert (Z4 : PropExec.getr R2 4%bv = tp) by (rewrite (HK2 4%bv ltac:(inb)), (HK1 4%bv ltac:(inb)), G4; exact Htp).
    assert (Z23 : PropExec.getr R2 23%bv = Z_to_bv 64 r) by (rewrite (HK2 23%bv ltac:(inb)), (HK1 23%bv ltac:(inb)); exact G23).
    assert (ZOK : r = 0 -> spal = 0 /\ pi_moreA H w lw c) by (intros R0; split; [exact (Hsp0 R0) | exact (Hok R0)]).
    exact (pm_epi_call w ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 c0 lw r s LB LBs m1 mo1 c [] TBL_EXIT [] spal
             msF2 mo2 R2 F fc M2 OK Hsp Hsav K0 Hlw X1 Htr Hbsz MU3 WM3 MI3 MP2 KR2 VIS2 RF2 FZ Y1 Y2 Z3 Z4 Y8 Y10 Y11 Z23 Hr ZOK).
  Qed.
End Epi.
