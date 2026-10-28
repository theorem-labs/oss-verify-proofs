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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_DiagStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma fold_permA : forall (A : Type) (f : A -> Z) l l', Permutation l l' ->
  fold_right (fun x acc => f x + acc) 0 l = fold_right (fun x acc => f x + acc) 0 l'.
Proof. intros A f l l' P. induction P; cbn [fold_right]; lia. Qed.

Lemma fold_appA : forall (A : Type) (f : A -> Z) l l',
  fold_right (fun x acc => f x + acc) 0 (l ++ l') = fold_right (fun x acc => f x + acc) 0 l + fold_right (fun x acc => f x + acc) 0 l'.
Proof. intros A f l l'. induction l as [|x l IH]; cbn [fold_right app]; lia. Qed.

Lemma lb_small_perm : forall L L', Permutation L L' -> lb_small L = lb_small L'.
Proof. intros L L' P. unfold lb_small. exact (fold_permA _ (fun b => nsmall (blk_size b)) _ _ P). Qed.
Lemma nlarge_perm : forall L L', Permutation L L' -> nlarge L = nlarge L'.
Proof. intros L L' P. unfold nlarge. exact (fold_permA _ (fun b => nlg (blk_size b)) _ _ P). Qed.
Lemma lb_small_app : forall L L', lb_small (L ++ L') = lb_small L + lb_small L'.
Proof. intros L L'. unfold lb_small. exact (fold_appA _ (fun b => nsmall (blk_size b)) L L'). Qed.
Lemma nlarge_app : forall L L', nlarge (L ++ L') = nlarge L + nlarge L'.
Proof. intros L L'. unfold nlarge. exact (fold_appA _ (fun b => nlg (blk_size b)) L L'). Qed.

Lemma nsmall_le : forall n, nsmall n <= 64512.
Proof. intros n. unfold nsmall. destruct (Z.leb_spec n 64512); lia. Qed.

Lemma tb_meas : forall (TB : list block), (length TB <= 1)%nat ->
  lb_small TB <= 64512 /\ nlarge TB <= 1 /\ 0 <= nlarge TB.
Proof.
  intros [|b [|b' TB]] HL; cbn [length] in HL; [cbn; lia | | lia].
  rewrite lb_small_cons, nlarge_cons. cbn [lb_small nlarge fold_right].
  pose proof (nsmall_le (blk_size b)). pose proof (nlg_bounds (blk_size b)). lia.
Qed.

Lemma nlarge_nonneg : forall L, 0 <= nlarge L.
Proof. induction L as [|b L IH]; [cbn; lia|]. rewrite nlarge_cons. pose proof (nlg_bounds (blk_size b)). lia. Qed.

Lemma pm_phi_nonneg : forall c, 0 <= pm_phi c.
Proof.
  intros c. unfold pm_phi, pm_phi_blocks.
  assert (G : forall bs : list (Z * Z), 0 <= fold_right (fun b acc => (if ICM_LARGE <? snd b then snd b else 0) + acc) 0 bs).
  { induction bs as [|b bs IH]; cbn [fold_right]; [lia|].
    destruct (ICM_LARGE <? snd b) eqn:E; [apply Z.ltb_lt in E; unfold ICM_LARGE in E|]; lia. }
  pose proof (G (c_blocks c)). pose proof (pm_prog_bounds c). lia.
Qed.

Definition rt_keep (RT : list (reg * SymExec3.SX2.expr)) : list (reg * SymExec3.SX2.expr) :=
  List.filter (fun re => existsb (fun x => bv_eqb (fst re) x) KEPT_REGS) RT.

Lemma regs_keep {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R R' RT,
  regs_tblX w X R RT -> (forall r, In r KEPT_REGS -> PropExec.getr R' r = PropExec.getr R r) -> regs_tblX w X R' (rt_keep RT).
Proof.
  intros w X R R' RT HT HK. unfold regs_tblX, rt_keep in *. apply Forall_forall. intros [r e] Hin.
  apply filter_In in Hin as [Hin Hk]. cbn [fst snd] in *. rewrite (HK r (LbB_Call.inb_In r KEPT_REGS Hk)).
  exact (proj1 (Forall_forall _ _) HT (r, e) Hin).
Qed.

Section DSGen.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHd : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pmxa_meas_LB : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    lb_small LB + 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + 1 <= RT_LARGE_MAX.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal OK X.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    pose proof (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (M1 & M2 & M3).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [_ TBL].
    pose proof (wk_meas0 H w OK) as (W1 & W2 & W3).
    pose proof (tb_meas TB TBL) as (T1 & T2 & T3).
    rewrite (lb_small_perm _ _ OWN1), (nlarge_perm _ _ OWN1), (Permutation_length OWN1).
    rewrite !lb_small_app, !nlarge_app, !length_app.
    pose proof (nlarge_nonneg (wa_LB0 w)). pose proof (nlarge_nonneg LBs).
    unfold RT_SMALL_MAX, RT_CNT_MAX, RT_LARGE_MAX, po_small, po_cnt, po_large in *. lia.
  Qed.

  Lemma pmxa_meas_LB2 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    lb_small LB + 2 * 64512 <= RT_SMALL_MAX /\ nlarge LB + 2 <= RT_LARGE_MAX.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal OK X.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    pose proof (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (M1 & M2 & M3).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [_ TBL].
    pose proof (wk_meas0 H w OK) as (W1 & W2 & W3).
    pose proof (tb_meas TB TBL) as (T1 & T2 & T3).
    rewrite (lb_small_perm _ _ OWN1), (nlarge_perm _ _ OWN1).
    rewrite !lb_small_app, !nlarge_app.
    pose proof (nlarge_nonneg (wa_LB0 w)). pose proof (nlarge_nonneg LBs).
    unfold RT_SMALL_MAX, RT_LARGE_MAX, po_small, po_large in *. lia.
  Qed.

  Lemma pm_ds_pre : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF F fc entry cost DB
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) errv,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) ->
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 entry) fc None m (seg_rom asegs) -> frm_zero fc ->
    sp = Z_to_bv 64 (wa_s1 w) -> s0 = Z_to_bv 64 (wa_sp0 w) -> tp = wa_tp w -> bv_unsigned ra mod 2 = 0 ->
    rw_cells asegs m (errno_addr tp) [C4 errv] ->
    lb_own DB m -> 0 <= cost -> spal + cost <= PM_RESERVE ->
    ds_pre H LINV entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB DB (PMLF H w) ((wa_sp0 w, wa_ra w) :: wa_CH w) cost (wa_lo w) (wa_B w) (wa_shi w) errv.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF F fc entry cost DB
           ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 errv
           OK X KR VIS FZ Esp Es0 Etp Hra ERR DBO Hc Hsc.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (wk_s1 H w OK) as (Q1 & Q2).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmxa_meas_LB w s LB LBs m mo c ins tbl ftbl TB spal OK X) as (M1 & M2 & M3).
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4).
    pose proof (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as STK.
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) STK ltac:(lia)) as [STK1 _].
    pose proof (wk_lfb H w OK) as LFB. pose proof (wk_B64 H w OK) as B64.
    assert (Us1 : bv_unsigned sp = wa_s1 w) by (rewrite Esp; apply u64_of_Z; unfold AAPP_HI in *; lia).
    assert (Us0 : bv_unsigned s0 = wa_sp0 w) by (rewrite Es0; apply u64_of_Z; unfold AAPP_HI in *; lia).
    pose proof (pm_phi_nonneg c) as PH.
    unfold ds_pre. rewrite Us1, Us0.
    refine (conj VIS (conj FZ (conj (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (conj KR (conj DBO _))))).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
    split; [exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|]. split; [lia|]. split; [exact B64|].
    split; [rewrite <- Q2; Z.div_mod_to_equations; lia|].
    split; [exact STK1|]. split; [exact S1|]. split; [unfold ADS_STACK, APM_STACK in *; lia|].
    split; [exact ERR|]. split; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|]. split; [rewrite Etp; exact (wk_tp H w OK)|].
    split; [exact Hra|]. split; [exact (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|].
    split; [exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|].
    split; [exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|].
    split; [unfold PMLF; cbn [length]; unfold PM_FRAMES, DS_FRAMES in *; lia|].
    split; [exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|]. split; [lia|].
    split; [exact (xa_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)|].
    split; [unfold pf_ok, DS_PF; apply Forall_nil|].
    split.
    { intros fp' ra' Hin. destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]. pose proof (wk_chfr H w OK fp' ra' Hin). lia. }
    split; [exact (proj1 (Forall_forall _ _) (wk_tr H w OK) 0x1200e8 ltac:(cbn; tauto)) |].
    pose proof (pm_phi_le_cap c) as PCAP. unfold PM_RESERVE in *. lia.
  Qed.

  Lemma lb_own_xpres_xp : forall (w : pmwA H) s LB m m' LBk XS LBs ftbl,
    pmw_okA H w -> as_RHEAP H s LB m -> as_RFS H (PMLF H w) m' -> Forall (fs_scratch H (PMLF H w)) XS ->
    (forall b, In b LBs -> In b LBk) -> (forall b, In b LBs -> In b LB) ->
    forall X, Forall (xp_ok H w ftbl) X ->
    xpres H LBk (wa_s1 w) (X ++ XS) m m' -> lb_own LBs m -> lb_own LBs m'.
  Proof.
    intros w s LB m m' LBk XS LBs ftbl OK RH RFS' FXS IN1 IN2 X FX XP OWN.
    unfold lb_own in *. apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) OWN b Hb) as W.
    pose proof (ah_blocks H HHd _ _ _ _ RH (IN2 b Hb)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    pose proof (blk_apart_ff H HHd w s LB m b OK RH (IN2 b Hb)) as BF.
    assert (FOb : fsobj H (PMLF H w) (blk_addr b) (blk_size b)).
    { destruct b as [[pid A] n]. eapply fsobj_block; [exact HHd | exact RH | exact (IN2 _ Hb)]. }
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xp_scr_obj H HHd w m' XS (blk_addr b) (blk_size b) OK RFS' FXS FOb ltac:(lia) Rn ltac:(unfold AAPP_HI; lia) RAPP) as [SX _].
    eapply xpres_wr_at; [exact XP | exact W |].
    apply (xr_blk H w LBk (X ++ XS) b); [exact (IN1 b Hb) | lia | lia |].
    apply Forall_app. split; [| exact SX].
    eapply (ap_X_apart H w ftbl X); [exact FX | destruct BF; lia | unfold RtB_Td.ATDLOC, AIMG_TOP in *; lia].
  Qed.

  Lemma pmxa_after_ds_gen : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal ds s' LB' m' mo' XS LBk TB' cost (XT : list (Z * Z)),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    xp_ok H w ftbl (ds, ds + DS_SIZE) ->
    Forall (xp_ok H w ftbl) XT -> Forall (fun iv : Z * Z => wr_at asegs m' (fst iv) (snd iv - fst iv)) XT ->
    as_RHEAP H s' LB' m' -> as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) -> as_rauxv_ok H m' (wa_B w) ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) -> LINV m' ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LBk (wa_s1 w) (((ds, ds + DS_SIZE) :: XT) ++ XS) m m' ->
    wr_at asegs m' ds DS_SIZE ->
    as_AL H s' >= as_AL H s - cost -> 0 <= cost -> spal + cost <= PM_RESERVE ->
    Permutation LB (TB ++ LBk) -> Permutation LB' (TB' ++ LBk) -> lb_own TB' m' -> (length TB' <= 1)%nat ->
    PMXAT H LINV w s' LB' LBs m' mo' c ins tbl ftbl TB' (spal + cost).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal ds s' LB' m' mo' XS LBk TB' cost XT OK X0 Hknn Hfk XPD FXT FWT
           RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP WRD AL Hc Hsc P1 P2 TBO TBL.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (A1 & A2 & A3 & A4).
    assert (PK : Permutation LBk (wa_LB0 w ++ LBs)).
    { assert (PP : Permutation (TB ++ LBk) (TB ++ (wa_LB0 w ++ LBs))).
      { eapply Permutation_trans; [apply Permutation_sym; exact P1|]. eapply Permutation_trans; [exact OWN1|].
        rewrite app_assoc. apply Permutation_app_comm. }
      exact (Permutation_app_inv_l _ _ _ PP). }
    assert (Ik : forall b, In b LBk -> In b LB) by (intros b Hb; apply (Permutation_in _ (Permutation_sym P1)); apply in_app_iff; right; exact Hb).
    assert (I0 : forall b, In b (wa_LB0 w) -> In b LBk) by (intros b Hb; apply (Permutation_in _ (Permutation_sym PK)); apply in_app_iff; left; exact Hb).
    assert (Is : forall b, In b LBs -> In b LBk) by (intros b Hb; apply (Permutation_in _ (Permutation_sym PK)); apply in_app_iff; right; exact Hb).
    assert (Is' : forall b, In b LBs -> In b LB') by (intros b Hb; apply (Permutation_in _ (Permutation_sym P2)); apply in_app_iff; right; exact (Is b Hb)).
    assert (Isl : forall b, In b LBs -> In b LB) by (intros b Hb; exact (Ik b (Is b Hb))).
    assert (XPD0 : ds <= ds + DS_SIZE /\ wa_ff w + 24 <= ds /\ ds + DS_SIZE <= wa_ff w + 16376)
      by (destruct XPD as [(K0 & K1 & K2 & _)|E]; [cbn [fst snd] in *; lia | exfalso; injection E as E1 E2; unfold DS_SIZE in E2; lia]).
    destruct XPD0 as (XD0 & XD1 & XD2).
    assert (FXD : Forall (xp_ok H w ftbl) ((ds, ds + DS_SIZE) :: XT)) by (apply Forall_cons; [exact XPD | exact FXT]).
    destruct (pmc_xp_keep H HHd LINV w s LB LBs m mo c ins tbl ftbl TB spal LB' m' LBk ((ds, ds + DS_SIZE) :: XT) XS OK X0 RFS' FXS XP
                FXD Is Is') as (U1 & U2 & U3 & V1 & V2 & V3 & SHc).
    eapply (pmxa_xp H HHd LINV w s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs m' mo' c TB' (spal + cost) LBk
              ((ds, ds + DS_SIZE) :: XT) XS OK X0 Hknn RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP
              FXD); try reflexivity.
    - apply Forall_cons; [| exact FWT]. cbn [fst snd]. replace (ds + DS_SIZE - ds) with DS_SIZE by lia. exact WRD.
    - exact Hfk.
    - exact Ik.
    - exact I0.
    - eapply Permutation_trans; [exact P2|]. eapply Permutation_trans; [apply Permutation_app_comm|].
      rewrite app_assoc. apply Permutation_app_tail. exact PK.
    - exact OWN2.
    - eapply (lb_own_xpres_xp w s LB m m' LBk XS LBs ftbl OK (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) RFS' FXS Is Isl ((ds, ds + DS_SIZE) :: XT));
        [exact FXD | exact XP | exact (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)].
    - exact (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0).
    - exact TBO.
    - exact TBL.
    - lia.
    - exact A2.
    - lia.
    - exact U1.
    - exact U2.
    - exact U3.
    - exact V1.
    - exact V2.
    - exact V3.
    - exact SHc.
  Qed.

  Lemma pmxa_after_ds : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal ds s' LB' m' mo' XS LBk TB' cost,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    xp_ok H w ftbl (ds, ds + DS_SIZE) ->
    as_RHEAP H s' LB' m' -> as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) -> as_rauxv_ok H m' (wa_B w) ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) -> LINV m' ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LBk (wa_s1 w) ([(ds, ds + DS_SIZE)] ++ XS) m m' ->
    wr_at asegs m' ds DS_SIZE ->
    as_AL H s' >= as_AL H s - cost -> 0 <= cost -> spal + cost <= PM_RESERVE ->
    Permutation LB (TB ++ LBk) -> Permutation LB' (TB' ++ LBk) -> lb_own TB' m' -> (length TB' <= 1)%nat ->
    PMXAT H LINV w s' LB' LBs m' mo' c ins tbl ftbl TB' (spal + cost).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal ds s' LB' m' mo' XS LBk TB' cost OK X0 Hknn Hfk XPD
           RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP WRD AL Hc Hsc P1 P2 TBO TBL.
    eapply (pmxa_after_ds_gen w s LB LBs m mo c ins tbl ftbl TB spal ds s' LB' m' mo' XS LBk TB' cost []); eauto.
  Qed.
End DSGen.

Section DSObj.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.

  Lemma ff_ds_obj : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal k n,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    obj_sh_ok ins k n = true -> 24 <= k -> k + n <= 16376 ->
    ds_obj H (PMLF H w) m (wa_s1 w) (wa_ff w + k) n /\ obj_inframe (PMLF H w) (wa_ff w + k) n.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal k n OK X Hok Hk Hkn.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (xp_geom H (HHd H HHbp) w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof Hok as Hok'. unfold obj_sh_ok in Hok'.
    apply andb_true_iff in Hok' as [Hb _]. apply andb_true_iff in Hb as [Hb H4]. apply andb_true_iff in Hb as [Hb H3].
    apply andb_true_iff in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
    assert (IFR : obj_inframe (PMLF H w) (wa_ff w + k) n).
    { exists (PM_FCLASS, wa_ff w, wa_fp w). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd].
      change (fsz PM_FCLASS) with 16384. lia. }
    split; [| exact IFR].
    unfold ds_obj. split; [exact (ff_addressable m (wa_ff w) ins k n (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) Hok)|].
    split; [Z.div_mod_to_equations; lia|].
    split; [right; exact IFR|].
    split; [lia|]. split; [unfold AAPP_HI in *; lia|].
    split; [left; pose proof (wk_s1 H w OK) as (WS1 & _); unfold ADS_STACK; lia|].
    unfold app_obj. destruct FA as [(L1 & L2)|(L1 & L2)]; unfold aapp_lo, aapp_hi in *; unfold AAPP_HI, AFS_HDR in *; lia.
  Qed.

  Lemma cons_ds_obj : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    ds_obj H (PMLF H w) m (wa_s1 w) (wa_cons w) 48 /\ rw_cells asegs m (wa_cons w + 32) [C8 (Z_to_bv 64 0)].
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal OK X.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (wk_capp H w OK) as (CA & CA0 & CA16).
    destruct (wk_cin H w OK) as (fc0 & Hfc0 & CF1 & CF2).
    pose proof (proj2 (ah_RFS_range H (HHd H HHbp) _ _ (wk_rfs0 H w OK)) fc0 Hfc0) as (_ & CR1 & CR2 & _).
    pose proof (xp_geom H (HHd H HHbp) w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    split.
    - unfold ds_obj. split; [exact (proj2 (proj2 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)))|].
      split; [Z.div_mod_to_equations; lia|].
      split; [right; exists fc0; split; [right; exact Hfc0 | lia]|].
      split; [lia|]. split; [unfold AAPP_HI, AFS_SIZE in *; lia|].
      split; [left; pose proof (wk_s1 H w OK) as (WS1 & _); unfold ADS_STACK, AFS_SIZE in *; lia|].
      unfold app_obj. destruct CA as [(L1 & L2)|(L1 & L2)]; unfold aapp_lo, aapp_hi in *; unfold AAPP_HI, AIMG_TOP, AHI_LO, ALOWSH_LO in *; lia.
    - pose proof (xa_consf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as CF. pose proof (xa_consw _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as CW.
      apply rw_C8_of_rdn; [lia | unfold AAPP_HI in *; lia | exact CF |].
      destruct CW as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi.
      replace (wa_cons w + 32 + i) with (wa_cons w + (32 + i)) by lia. apply W2. lia.
  Qed.

  Lemma ff_cells_xpres : forall (w : pmwA H) m m' LBk X XS k cs,
    pmw_okA H w -> as_RFS H (PMLF H w) m' -> Forall (fs_scratch H (PMLF H w)) XS -> xpres H LBk (wa_s1 w) (X ++ XS) m m' ->
    Forall (fun iv : Z * Z => wa_ff w + k + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= wa_ff w + k) X ->
    0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 -> rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs.
  Proof.
    intros w m m' LBk X XS k cs OK RFS' FXS XP FX Hk Hkn RW.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (xp_geom H (HHd H HHbp) w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    assert (FOf : fsobj H (PMLF H w) (wa_ff w) 16384)
      by (right; exists (PM_FCLASS, wa_ff w, wa_fp w); split; [left; reflexivity | unfold ff_addr, ff_class; cbn [fst snd]; change (fsz PM_FCLASS) with 16384; lia]).
    pose proof (xp_scr_obj H (HHd H HHbp) w m' XS (wa_ff w) 16384 OK RFS' FXS FOf ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) FA) as [SXf _].
    eapply (xpres_rw_cells H); [exact XP | exact RW |].
    apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |].
    apply Forall_app. split; [exact FX|]. eapply Forall_impl; [| exact SXf]. intros iv Hiv. cbn beta in *. lia.
  Qed.
End DSObj.

Section DSOps.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.

  Definition ds_K (w : pmwA H) (LBs : list block) (c : pmc) ins tbl ftbl (R : bvmap 5 word) (ret ds : Z) (m : mem)
      (P : list block -> mem -> list block -> bvmap 5 word -> Prop) (spal' : Z) (Q : config -> Prop) : Prop :=
    forall msF1 mo1 R1 F1 fc1 (s1 : as_St H) LB1 m1 TB1,
      as_AKREL H s1 (mkCfg msF1 mo1) -> as_VIS H s1 msF1 = MS R1 F1 (Z_to_bv 64 ret) fc1 None m1 (seg_rom asegs) ->
      rfull R1 -> frm_zero fc1 ->
      PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl TB1 spal' ->
      (forall r, In r KEPT_REGS -> PropExec.getr R1 r = PropExec.getr R r) ->
      P LB1 m1 TB1 R1 ->
      (forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
                    (wa_ff w + k + Z.of_nat (cells_size cs) <= ds \/ ds + DS_SIZE <= wa_ff w + k) ->
                    rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m1 (wa_ff w + k) cs) ->
      as_SR H Q (mkCfg msF1 mo1).

  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.

  Lemma pm_ds_ctor : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal msF R F fc
      (dso po so so2 ret err : Z) (pos : list word) (j1 j2 : list byte) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 ADS_CTOR) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w + po) ->
    PropExec.getr R 12%bv = Z_to_bv 64 (wa_cons w) -> PropExec.getr R 13%bv = Z_to_bv 64 (wa_ff w + so) ->
    PropExec.getr R 14%bv = Z_to_bv 64 (err mod 2 ^ 64) -> PropExec.getr R 15%bv = Z_to_bv 64 (wa_ff w + so2) ->
    - 2 ^ 31 <= err < 0 ->

    obj_sh_ok ins dso DS_SIZE = true -> obj_sh_ok ins po 24 = true -> obj_sh_ok ins so 24 = true -> obj_sh_ok ins so2 24 = true ->
    24 <= dso -> dso + DS_SIZE <= 16376 -> 24 <= po -> po + 24 <= 16376 -> 24 <= so -> so + 24 <= 16376 ->
    24 <= so2 -> so2 + 24 <= 16376 ->
    (po + 24 <= dso \/ dso + DS_SIZE <= po) -> (so + 24 <= dso \/ dso + DS_SIZE <= so) -> (so2 + 24 <= dso \/ dso + DS_SIZE <= so2) ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    u64arr asegs m (wa_ff w + po) pos -> length pos = 3%nat ->
    rw_cells asegs m (wa_ff w + so) [C2 (Z_to_bv 64 0); CB 22 j1] -> rw_cells asegs m (wa_ff w + so2) [C2 (Z_to_bv 64 0); CB 22 j2] ->
    ds_K w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 _ => TB1 = [] /\ ds_repA LB1 m1 (wa_ff w + dso) err 0 []) spal Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl spal msF R F fc dso po so so2 ret err pos j1 j2 Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 G13 G14 G15 Herr Ods Opo Oso Oso2 D1 D2 D3 D4 D5 D6 D7 D8 A1 A2 A3 FTD
           POS PL STR STR2 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal dso DS_SIZE OK X Ods D1 D2) as [OBd IFd].
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal po 24 OK X Opo D3 D4) as [OBp IFp].
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal so 24 OK X Oso D5 D6) as [OBs IFs].
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal so2 24 OK X Oso2 D7 D8) as [OBs2 IFs2].
    destruct (cons_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal OK X) as [OBc CONS].
    pose proof (wk_pcons H w OK) as PCo.
    destruct (wk_cin H w OK) as (fc0 & Hfc0 & CF1 & CF2).
    pose proof (lf0_apart_ff H w fc0 (wa_cons w) 48 OK Hfc0 CF1 CF2) as CFF.
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H (HHd H HHbp)).
    { eapply (HCTOR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (PMLF H w)
                ((wa_sp0 w, wa_ra w) :: wa_CH w) (wa_lo w) (wa_B w) (wa_shi w) errv
                (wa_ff w + dso) (wa_ff w + po) (wa_cons w) (wa_ff w + so) (wa_ff w + so2) err pos j1 j2).
      - eapply (pm_ds_pre H LINV w s LB LBs m mo c ins tbl ftbl [] spal msF F fc ADS_CTOR 0 []);
          [exact OK | exact X | exact KR | exact VIS | exact FZ | exact G2 | exact G8 | exact G4 | rewrite G1, u64_of_Z by lia; exact Hr2
          | rewrite G4; exact ERR | apply lb_own_nil | lia | pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & _ & _ & S1 & S2); lia].
      - exact G10.
      - exact G11.
      - exact G12.
      - exact G13.
      - exact G14.
      - exact G15.
      - exact Herr.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBd.
      - pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (W0 & W1 & W2). change (fsz PM_FCLASS) with 16384 in *.
        split; [lia|]. split; [lia|]. intros i Hi. replace (wa_ff w + dso + i) with (wa_ff w + (dso + i)) by lia. apply W2. unfold DS_SIZE in *. lia.
      - exact IFd.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBp.
      - exact POS.
      - exact PL.
      - exact IFp.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBs.
      - exact STR.
      - exact IFs.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBs2.
      - exact STR2.
      - exact IFs2.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBc.
      - exact CONS.
      - intros a Ha. unfold DS_SIZE in *. repeat split; intros Hb; destruct CFF as [CF|CF]; lia. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & _ & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & (PL1 & DS1 & WR1) & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STK1 by (unfold AAPP_HI in *; lia).
    rewrite G2, u64_of_Z in XP by (unfold AAPP_HI in *; lia). rewrite G4 in ERR1.
    assert (X1 : PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl [] (spal + 0)).
    { eapply (pmxa_after_ds H HHbp LINV w s LB LBs m mo c ins tbl ftbl [] spal (wa_ff w + dso) s1 LB1 m1 mo1 XS LB [] 0
                OK X Hknn Hfk); try eassumption.
      - unfold xp_ok; cbn [fst snd]. left. split; [unfold DS_SIZE in *; lia|]. split; [lia|]. split; [unfold DS_SIZE in *; lia|].
        eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia.
      - exists errv1. exact ERR1.
      - lia.
      - pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & _ & _ & S1 & S2). lia.
      - apply Permutation_refl.
      - apply lb_own_nil.
      - cbn [length]. lia. }
    rewrite Z.add_0_r in X1.
    eapply (K ms1 mo1 _ F1 fc1 s1 LB1 m1 []); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | split; [reflexivity | exact DS1] |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - intros k cs Hk Hkc Hdj RW. eapply (ff_cells_xpres H HHbp w m m1 LB [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] XS k cs OK RFS1 FXS XP);
        [| exact Hk | exact Hkc | exact RW]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.
End DSOps.
Arguments ds_K {HCEIL} H LINV w LBs c ins tbl ftbl R ret ds m P spal' Q.

Section DSOps2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.

  Lemma tb_split : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal,
    PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> Permutation LB (TB ++ (wa_LB0 w ++ LBs)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal X. pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    eapply Permutation_trans; [exact OWN1|]. rewrite app_assoc. apply Permutation_app_comm.
  Qed.

  Lemma xfer_kept : forall LB TB LBk LB' TB', Permutation LB (TB ++ LBk) -> ds_xfer LB TB LB' TB' -> Permutation LB' (TB' ++ LBk).
  Proof.
    intros LB TB LBk LB' TB' P1 (LR & X1 & X2).
    assert (PR : Permutation LR LBk).
    { apply (Permutation_app_inv_l TB). eapply Permutation_trans; [apply Permutation_sym; exact X1 | exact P1]. }
    eapply Permutation_trans; [exact X2|]. apply Permutation_app_head. exact PR.
  Qed.

  Lemma pm_put_num : forall (entry lo_x hi_x : Z) (enc : Z -> Z),
    put_num_stmtA H LINV ds_repA entry lo_x hi_x enc ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (dso ret x err len : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 entry) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 (enc x) -> lo_x <= x < hi_x ->
    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    ds_repA LB m (wa_ff w + dso) err len TB -> len + 24 <= DS_MAXLEN -> spal + ds_cost (len + 24) <= PM_RESERVE ->
    ds_K H LINV w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 R1 => ds_repA LB1 m1 (wa_ff w + dso) err (len + 24) TB1 /\ PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + dso))
         (spal + ds_cost (len + 24)) Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros entry lo_x hi_x enc HNUM w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret x err len Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 Hx Ods D1 D2 FTD DS0 Hlen Hsc K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [TBO TBL].
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal dso DS_SIZE OK X Ods D1 D2) as [OBd IFd].
    pose proof (tb_split w s LB LBs m mo c ins tbl ftbl TB spal X) as PK.
    assert (Hcost : 0 <= ds_cost (len + 24)) by (pose proof (proj2 (proj2 (proj2 (proj2 (dla_def _ _ DSL _ _ _ _ _ _ DS0))))); unfold ds_cost; lia).
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H (HHd H HHbp)).
    { eapply (HNUM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (wa_LB0 w ++ LBs) (PMLF H w)
                ((wa_sp0 w, wa_ra w) :: wa_CH w) (wa_lo w) (wa_B w) (wa_shi w) errv (wa_ff w + dso) err len x TB).
      - eapply (pm_ds_pre H LINV w s LB LBs m mo c ins tbl ftbl TB spal msF F fc entry (ds_cost (len + 24)) TB);
          [exact OK | exact X | exact KR | exact VIS | exact FZ | exact G2 | exact G8 | exact G4 | rewrite G1, u64_of_Z by lia; exact Hr2
          | rewrite G4; exact ERR | exact TBO | exact Hcost | exact Hsc].
      - exact G10.
      - exact G11.
      - exact Hx.
      - exact DS0.
      - exact PK.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBd.
      - exact IFd.
      - exact Hlen.
      - exact (proj1 (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X)).
      - exact (proj2 (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X)). }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & RES & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & (TB1 & XF & DS1 & TBO1 & WR1) & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STK1 by (unfold AAPP_HI in *; lia).
    rewrite G2, u64_of_Z in XP by (unfold AAPP_HI in *; lia). rewrite G4 in ERR1.
    pose proof (proj1 (dla_blocks _ _ DSL _ _ _ _ _ _ DS1)) as TBL1.
    assert (X1 : PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl TB1 (spal + ds_cost (len + 24))).
    {
      eapply (pmxa_after_ds_gen H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal (wa_ff w + dso) s1 LB1 m1 mo1 XS (wa_LB0 w ++ LBs) TB1
                (ds_cost (len + 24)) [(RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] OK X Hknn Hfk).
      - unfold xp_ok; cbn [fst snd]. left. split; [unfold DS_SIZE in *; lia|]. split; [lia|]. split; [unfold DS_SIZE in *; lia|].
        eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia.
      - apply Forall_cons; [right; reflexivity | apply Forall_nil].
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (RtB_Td.ATDLOC + 8 - RtB_Td.ATDLOC) with 8 by lia. exact (RtB_Td.td_wr_any m1).
      - exact RH1.
      - exact MP1.
      - exact MI1.
      - exact STK1.
      - exists errv1. exact ERR1.
      - exact RA1.
      - exact RFS1.
      - exact AC1.
      - exact S01.
      - exact LI1.
      - exact FXS.
      - exact XP.
      - exact WR1.
      - exact AL1.
      - exact Hcost.
      - exact Hsc.
      - exact PK.
      - exact (xfer_kept _ _ _ _ _ PK XF).
      - exact TBO1.
      - exact TBL1. }
    eapply (K ms1 mo1 _ F1 fc1 s1 LB1 m1 TB1); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | split; [exact DS1 | ] |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - cbn. exact (RES _ eq_refl).
    - intros k cs Hk Hkc Hdj RW. eapply (ff_cells_xpres H HHbp w m m1 (wa_LB0 w ++ LBs) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE); (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] XS k cs OK RFS1 FXS XP);
        [| exact Hk | exact Hkc | exact RW]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; [lia|].
      right. pose proof (xp_geom H (HHd H HHbp) w OK) as (F1' & F2' & F3' & _). unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR in *. lia.
  Qed.

  Lemma pm_put_cseq_img : put_cseq_stmtA H LINV ds_repA ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (dso ret p n err len : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 APUT_CSEQ) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) -> PropExec.getr R 11%bv = Z_to_bv 64 p -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    0 <= n -> AIMG_LO + 64 <= p -> p + n + 64 <= AIMG_TOP ->
    (forall m', ACONST m' -> accessible m' p n) ->
    (exists bs, length bs = Z.to_nat n /\ forall m', mem_inv asegs m' -> bytes_at asegs m' p bs) ->
    ds_repA LB m (wa_ff w + dso) err len TB -> len + n <= DS_MAXLEN -> spal + ds_cost (len + n) <= PM_RESERVE ->
    ds_K H LINV w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 R1 => ds_repA LB1 m1 (wa_ff w + dso) err (len + n) TB1 /\ PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + dso))
         (spal + ds_cost (len + n)) Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HCSEQ w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret p n err len Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 G11 G12 Ods D1 D2 FTD Hn Hp0 Hp ACC BYT DS0 Hlen Hsc K.
    pose proof aceil_facts as ((ACe1 & ACe2) & ACe3 & ACe4).
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (wk_s1 H w OK) as (WS1 & _).
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [TBO TBL].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal dso DS_SIZE OK X Ods D1 D2) as [OBd IFd].
    pose proof (tb_split w s LB LBs m mo c ins tbl ftbl TB spal X) as PK.
    assert (Hcost : 0 <= ds_cost (len + n)) by (pose proof (proj2 (proj2 (proj2 (proj2 (dla_def _ _ DSL _ _ _ _ _ _ DS0))))); unfold ds_cost; lia).
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H (HHd H HHbp)).
    { eapply (HCSEQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (wa_LB0 w ++ LBs) (PMLF H w)
                ((wa_sp0 w, wa_ra w) :: wa_CH w) (wa_lo w) (wa_B w) (wa_shi w) errv (wa_ff w + dso) err len p n TB).
      - eapply (pm_ds_pre H LINV w s LB LBs m mo c ins tbl ftbl TB spal msF F fc APUT_CSEQ (ds_cost (len + n)) TB);
          [exact OK | exact X | exact KR | exact VIS | exact FZ | exact G2 | exact G8 | exact G4 | rewrite G1, u64_of_Z by lia; exact Hr2
          | rewrite G4; exact ERR | exact TBO | exact Hcost | exact Hsc].
      - exact G10.
      - exact G11.
      - exact G12.
      - exact DS0.
      - exact PK.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBd.
      - exact IFd.
      - exact Hn.
      - left. unfold AIMG_LO in *. lia.
      - destruct BYT as (bs & LEN & BYT'). exists bs. split; [exact LEN|]. intros m' XS s' LB' ACm MIm _ _ _ _.
        split; [exact (BYT' m' MIm)|]. split; [exact (ACC m' ACm)|]. eapply ACONST_shvis; [exact ACm | lia | lia | lia].
      - unfold in_app_mem, ASHADOW_BASE, AIMG_TOP, AIMG_LO in *. left. lia.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). left. unfold ADS_STACK, AIMG_TOP in *. lia.
      - intros a Ha. split.
        + unfold AIMG_TOP, AFS_HDR in *. lia.
        + intros (b & Hb & Hr0). assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; right; exact Hb).
          pose proof (ah_blocks H (HHd H HHbp) _ _ _ _ RH HbL) as (_ & _ & _ & BT & _). lia.
      - exact Hlen.
      - exact (proj1 (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X)).
      - exact (proj2 (pmxa_meas_LB2 H LINV w s LB LBs m mo c ins tbl ftbl TB spal OK X)). }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & RES & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & (TB1 & XF & DS1 & TBO1 & WR1) & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STK1 by (unfold AAPP_HI in *; lia).
    rewrite G2, u64_of_Z in XP by (unfold AAPP_HI in *; lia). rewrite G4 in ERR1.
    pose proof (proj1 (dla_blocks _ _ DSL _ _ _ _ _ _ DS1)) as TBL1.
    assert (X1 : PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl TB1 (spal + ds_cost (len + n))).
    { eapply (pmxa_after_ds H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal (wa_ff w + dso) s1 LB1 m1 mo1 XS (wa_LB0 w ++ LBs) TB1
                (ds_cost (len + n)) OK X Hknn Hfk).
      - unfold xp_ok; cbn [fst snd]. left. split; [unfold DS_SIZE in *; lia|]. split; [lia|]. split; [unfold DS_SIZE in *; lia|].
        eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia.
      - exact RH1.
      - exact MP1.
      - exact MI1.
      - exact STK1.
      - exists errv1. exact ERR1.
      - exact RA1.
      - exact RFS1.
      - exact AC1.
      - exact S01.
      - exact LI1.
      - exact FXS.
      - exact XP.
      - exact WR1.
      - exact AL1.
      - exact Hcost.
      - exact Hsc.
      - exact PK.
      - exact (xfer_kept _ _ _ _ _ PK XF).
      - exact TBO1.
      - exact TBL1. }
    eapply (K ms1 mo1 _ F1 fc1 s1 LB1 m1 TB1); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | split; [exact DS1 | ] |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - cbn. exact (RES _ eq_refl).
    - intros k cs Hk Hkc Hdj RW. eapply (ff_cells_xpres H HHbp w m m1 (wa_LB0 w ++ LBs) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] XS k cs OK RFS1 FXS XP);
        [| exact Hk | exact Hkc | exact RW]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.

  Lemma pm_ds_dtor : ds_dtor_stmtA H LINV ds_repA ->
    forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (dso ret err len : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 ADS_DTOR) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc ->
    PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + dso) ->
    obj_sh_ok ins dso DS_SIZE = true -> 24 <= dso -> dso + DS_SIZE <= 16376 ->
    Forall (fun ke => dso + DS_SIZE <= fst ke \/ fst ke + 8 <= dso) ftbl ->
    ds_repA LB m (wa_ff w + dso) err len TB ->
    In (APC0_FREE, [0xfd148; ret]) PM_PF ->
    ds_K H LINV w LBs c ins tbl ftbl R ret (wa_ff w + dso) m
         (fun LB1 m1 TB1 _ => TB1 = [] /\ addressable m1 (wa_ff w + dso) DS_SIZE) (spal + 0) Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros HDTOR w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc dso ret err len Q OK X Hknn Hfk KR VIS RF FZ
           G1 Hr2 Hr G2 G8 G4 G10 Ods D1 D2 FTD DS0 HPF K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (errv & ERR).
    pose proof (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [TBO TBL].
    destruct (ff_ds_obj H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal dso DS_SIZE OK X Ods D1 D2) as [OBd IFd].
    pose proof (tb_split w s LB LBs m mo c ins tbl ftbl TB spal X) as PK.
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & _ & _ & SP1 & SP2).
    rewrite (rfull_eq R RF) in VIS.
    eapply (ah_seq H (HHd H HHbp)).
    { eapply (HDTOR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB (wa_LB0 w ++ LBs) (PMLF H w)
                ((wa_sp0 w, wa_ra w) :: wa_CH w) (wa_lo w) (wa_B w) (wa_shi w) errv (wa_ff w + dso) err len TB).
      - eapply (pm_ds_pre H LINV w s LB LBs m mo c ins tbl ftbl TB spal msF F fc ADS_DTOR 0 TB);
          [exact OK | exact X | exact KR | exact VIS | exact FZ | exact G2 | exact G8 | exact G4 | rewrite G1, u64_of_Z by lia; exact Hr2
          | rewrite G4; exact ERR | exact TBO | lia | lia].
      - rewrite G1, u64_of_Z by lia. eapply pf_ok_call; [exact (wk_pf H w OK) |].
        intros pp Hpp. cbn in Hpp. destruct Hpp as [<-|[]]. exact HPF.
      - exact G10.
      - exact DS0.
      - exact PK.
      - rewrite G2, u64_of_Z by (unfold AAPP_HI in *; lia). exact OBd.
      - exact IFd. }
    intros [ms1 mo1] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & _ & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & (PL1 & AD1 & WR1) & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    cbn [cfg_ms cfg_model] in *.
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite G2, u64_of_Z in STK1 by (unfold AAPP_HI in *; lia).
    rewrite G2, u64_of_Z in XP by (unfold AAPP_HI in *; lia). rewrite G4 in ERR1.
    assert (X1 : PMXAT H LINV w s1 LB1 LBs m1 mo1 c ins tbl ftbl [] (spal + 0)).
    { eapply (pmxa_after_ds H HHbp LINV w s LB LBs m mo c ins tbl ftbl TB spal (wa_ff w + dso) s1 LB1 m1 mo1 XS (wa_LB0 w ++ LBs) []
                0 OK X Hknn Hfk).
      - unfold xp_ok; cbn [fst snd]. left. split; [unfold DS_SIZE in *; lia|]. split; [lia|]. split; [unfold DS_SIZE in *; lia|].
        eapply Forall_impl; [| exact FTD]. intros [k e] Hk. cbn [fst snd] in *. lia.
      - exact RH1.
      - exact MP1.
      - exact MI1.
      - exact STK1.
      - exists errv1. exact ERR1.
      - exact RA1.
      - exact RFS1.
      - exact AC1.
      - exact S01.
      - exact LI1.
      - exact FXS.
      - exact XP.
      - exact WR1.
      - exact AL1.
      - lia.
      - lia.
      - exact PK.
      - exact PL1.
      - apply lb_own_nil.
      - cbn [length]. lia. }
    eapply (K ms1 mo1 _ F1 fc1 s1 LB1 m1 []); [exact KR1 | exact VIS1 | apply rfull_mkR | exact FZ1 | exact X1 | | split; [reflexivity | exact AD1] |].
    - intros r Hr0. repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr0.
    - intros k cs Hk Hkc Hdj RW. eapply (ff_cells_xpres H HHbp w m m1 (wa_LB0 w ++ LBs) [(wa_ff w + dso, wa_ff w + dso + DS_SIZE)] XS k cs OK RFS1 FXS XP);
        [| exact Hk | exact Hkc | exact RW]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia.
  Qed.
End DSOps2.

Definition PM_OWN_DS (dso : Z) : list (SymExec3.SX2.expr * Z * Z) :=
  [(SymExec3.SX2.EVar WV_S1, PM_RF_LO, PM_RF_TOP); (SymExec3.SX2.EVar WV_FF, 24, dso); (SymExec3.SX2.EVar WV_FF, dso + DS_SIZE, 16376);
   (FSHB, SHBASE, SHBASE + dso / 8); (FSHB, SHBASE + dso / 8 + 49, SHBASE + PM_NSH);
   (SymExec3.SX2.EVar WV_P, O_WIDX, O_FLAGS + 2)].

Section DSRun.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.

  Lemma num_wins_ds : forall (w : pmwA H) E dso, pmw_okA H w -> env_world H w E ->
    num_wins E (PM_OWN_DS dso) =
    [(wa_s1 w + PM_RF_LO, wa_s1 w + PM_RF_TOP); (wa_ff w + 24, wa_ff w + dso); (wa_ff w + (dso + DS_SIZE), wa_ff w + 16376);
     (sh (wa_ff w), sh (wa_ff w) + dso / 8); (sh (wa_ff w) + dso / 8 + 49, sh (wa_ff w) + PM_NSH);
     (wa_p w + O_WIDX, wa_p w + (O_FLAGS + 2))].
  Proof.
    intros w E dso OK HE. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    unfold num_wins, PM_OWN_DS. cbn [map]. rewrite (ev_s1 H w E OK HE), (ev_ff H w E OK HE), (ev_fshb H w E OK HE), (ev_p H w E OK HE).
    destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SHf). rewrite SHf.
    rewrite !Z.add_assoc. reflexivity.
  Qed.

  Lemma ds_wins_own : forall (w : pmwA H) dso, pmw_okA H w -> 24 <= dso -> dso + DS_SIZE <= 11584 -> dso mod 8 = 0 ->
    Forall (own_ivl H w)
      [(wa_s1 w + PM_RF_LO, wa_s1 w + PM_RF_TOP); (wa_ff w + 24, wa_ff w + dso); (wa_ff w + (dso + DS_SIZE), wa_ff w + 16376);
       (sh (wa_ff w), sh (wa_ff w) + dso / 8); (sh (wa_ff w) + dso / 8 + 49, sh (wa_ff w) + PM_NSH);
       (wa_p w + O_WIDX, wa_p w + (O_FLAGS + 2))].
  Proof.
    intros w dso OK H1 H2 H3. unfold DS_SIZE in *. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    assert (dso / 8 + 49 <= 1448) by (unfold DS_SIZE in *; Z.div_mod_to_equations; lia).
    assert (0 <= dso / 8) by (apply Z.div_pos; lia).
    unfold own_ivl, PM_RF_TOP, PM_RF_LO, PM_NSH. change (fsz PM_FCLASS) with 16384.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - left. lia.
    - right; left. lia.
    - right; left. unfold DS_SIZE in *. lia.
    - right; right; left. lia.
    - right; right; left. lia.
    - right; right; right. unfold O_WIDX, O_FLAGS. lia.
  Qed.

  Lemma ds_rep_run : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal E LOG dso err len,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E -> log_flat E LOG ->
    forallb (sym_inside (PM_OWN_DS dso)) LOG = true -> 24 <= dso -> dso + DS_SIZE <= 11584 -> dso mod 8 = 0 ->
    ds_repA LB m (wa_ff w + dso) err len TB -> ds_repA LB (mem_denot E m LOG) (wa_ff w + dso) err len TB.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E LOG dso err len OK X HE Hf Hchk D1 D2 D3 DS0.
    pose proof (munch_sym E m LOG (PM_OWN_DS dso) Hf Hchk) as MU. rewrite (num_wins_ds w E dso OK HE) in MU.
    pose proof (ds_wins_own w dso OK D1 D2 D3) as FW.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (p_apart_ff H w OK) as PAF.
    pose proof (xp_geom H (HHd H HHbp) w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 _].
    assert (INB : forall b, In b TB -> In (blk_addr b, blk_size b) (lbl LB)).
    { intros [[pid A] n] Hb. apply (lbl_in LB pid). apply (Permutation_in _ (Permutation_sym OWN1)).
      apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
    assert (SHd : sh (wa_ff w + dso) = sh (wa_ff w) + dso / 8).
    { unfold sh. rewrite (div8_add (wa_ff w) dso) by (Z.div_mod_to_equations; lia). lia. }
    assert (Hd8 : dso / 8 + 49 <= 1448 /\ 3 <= dso / 8) by (unfold DS_SIZE in *; split; Z.div_mod_to_equations; lia).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as (PR1 & PR2).
    assert (SHP : sh (wa_ff w) + 2048 <= wa_p w \/ wa_p w + PARSER_SIZE <= sh (wa_ff w)).
    { pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE (wa_ff w) 16384 PA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D.
      unfold nsh in D. change ((16384 + 7) / 8) with 2048 in D. exact D. }
    eapply (dla_frame _ _ DSL LB LB m (mem_denot E m LOG)); [exact DS0 | | intros b Hb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; right; apply in_app_iff; right; exact Hb].
    intros a Ha Hin. apply MU. rewrite unsigned_lit by lia.
    destruct Hin as [Hin|[(b & Hb & Hr)|[(b & Hb & Hr)|Hin]]].
    -
      unfold outside. unfold PM_RF_LO, PM_RF_TOP, PM_NSH, O_WIDX, O_FLAGS, DS_SIZE, PARSER_SIZE in *. change (fsz PM_FCLASS) with 16384 in *.
      repeat split; try lia.
    -
      destruct (own_apart_lbl H (HHd H HHbp) w s LB m _ _ OK RH (INB b Hb)) as [AP _].
      eapply disjoint_outside; [exact (disjoint_of_own H w _ _ _ FW AP) | lia].
    -
      destruct (own_apart_lbl H (HHd H HHbp) w s LB m _ _ OK RH (INB b Hb)) as [_ AP].
      eapply disjoint_outside; [exact (disjoint_of_own H w _ _ _ FW AP) | lia].
    -
      rewrite SHd in Hin. unfold nsh, DS_SIZE in Hin. change ((392 + 7) / 8) with 49 in Hin.
      unfold outside. unfold PM_RF_LO, PM_RF_TOP, PM_NSH, O_WIDX, O_FLAGS, DS_SIZE, PARSER_SIZE in *. change (fsz PM_FCLASS) with 16384 in *.
      rewrite G13 in *. unfold SHBASE in *. repeat split; try lia.
  Qed.
End DSRun.
