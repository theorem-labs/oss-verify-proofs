(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutShA CutShB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CSLR.
Definition mem := (word -> option byte).

Record row := ROW { r_i : nat; r_pc : Z; r_j : nat; r_sid : CC.subst; r_rd : nat; r_rs : nat; r_cur : expr; r_a : Z; r_b : Z; r_tab : bool }.

Definition find_row (ROWS : list row) (i : nat) (pc : Z) : option row :=
  find (fun r => (Nat.eqb (r_i r) i && Z.eqb (r_pc r) pc)%bool) ROWS.

(* [comment removed for export] *)
Definition sites_ok (segs : list Segment) (ROWS : list row) : bool :=
  forallb (fun r => match CSL1.site_chk1 segs (r_pc r) with
                    | Some (d, s0) => (Nat.eqb d (r_rd r) && Nat.eqb s0 (r_rs r))%bool
                    | None => false end) ROWS.
Lemma sites_ok_In : forall segs ROWS r, sites_ok segs ROWS = true -> In r ROWS -> CSL1.site_chk1 segs (r_pc r) = Some (r_rd r, r_rs r).
Proof.
  intros segs ROWS r H Hin. unfold sites_ok in H. rewrite forallb_forall in H. specialize (H r Hin).
  destruct (CSL1.site_chk1 segs (r_pc r)) as [[d s0]|]; [|discriminate]. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma find_row_In : forall ROWS i pc r, find_row ROWS i pc = Some r -> In r ROWS /\ r_i r = i /\ r_pc r = pc.
Proof.
  intros ROWS i pc r H. unfold find_row in H. apply find_some in H as [Hin Hb]. apply andb_prop in Hb as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Definition text_chk (cells : list kentry) (cur SE ENDE : expr) (LENB : Z) (KZB : kentry) : bool :=
  (CC.has_cell cells KZB && CX.fact2_ok cells (KRange (APC.esub cur SE) 0 LENB) && CX.fact2_ok cells (KRange (APC.esub (APC.eaddz ENDE (-1)) cur) 0 LENB))%bool.
Definition tab_chk (cells : list kentry) (cur : expr) (TLO TG : Z) (KZT : kentry) : bool :=
  (CC.has_cell cells KZT && CX.fact2_ok cells (KRange cur TLO (TLO + 8 * TG - 1)))%bool.

Definition row_chk (NF : nat) (d : CH.hdecl) (CPS : list CC.cutpoint) (BLS : list CA.blocks) (FFS : list (list (expr * Z * Z))) (CPF : list SGP.region)
           (SBz : Z) (kv : nat) (SE ENDE : expr) (LENB : Z) (KZB : kentry) (TLO TG : Z) (KZT : kentry)
           (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (r : row) : bool :=
  match nth_error CPS (r_j r) with
  | Some cj =>
      (Nat.eqb (r_i r) i && Z.eqb (SR.ps_pc ps) (r_pc r) && Z.leb 0 (r_pc r) && Z.ltb (r_pc r + 4) (2 ^ 64) && CBA.regions_eqb (CC.cp_F c) CPF
       && CSL.shl_chk NF c ps cj (r_sid r) (r_rd r) (r_rs r) (r_pc r + 4) (r_cur r) SBz kv (r_a r) (r_b r)
       && CHA.goto_amb_chk NF d c (nth i BLS []) (nth (r_j r) BLS []) (nth i FFS []) (nth (r_j r) FFS []) (r_sid r)
       && (if r_tab r then tab_chk (SR.ps_cells ps) (r_cur r) TLO TG KZT else text_chk (SR.ps_cells ps) (r_cur r) SE ENDE LENB KZB))%bool
  | None => false
  end.

Lemma mod_neg_small : forall x, - 2 ^ 64 <= x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. intros x Hx. replace x with ((x + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma cover_arith : forall s len uc LENB,
  0 <= LENB -> 0 < s -> 0 <= len -> s + len + 2 * LENB < 2 ^ 63 -> 0 <= uc < 2 ^ 64 ->
  (uc - s) mod 2 ^ 64 <= LENB -> (s + len - 1 - uc) mod 2 ^ 64 <= LENB -> s <= uc <= s + len - 1.
Proof.
  intros s len uc LENB HL Hs Hlen Hsl Huc H1 H2.
  assert (G1 : s <= uc).
  { destruct (Z_lt_le_dec uc s) as [Hl|Hl]; [|lia]. exfalso. rewrite mod_neg_small in H1 by lia. lia. }
  rewrite Z.mod_small in H1 by lia.
  destruct (Z_lt_le_dec (s + len - 1) uc) as [Hg|Hg]; [|lia]. exfalso. rewrite mod_neg_small in H2 by lia. lia.
Qed.

Section Leaf.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).

(* [comment removed for export] *)
Variable CPF : list SGP.region.      (* [comment removed for export] *)
Variable SBz : Z.
Variable kv : nat.                   (* [comment removed for export] *)
Variables SE ENDE BE GE : expr.      (* [comment removed for export] *)
Variables s len Bb G LENB : Z.
Variables TLO TG TSH : Z.            (* [comment removed for export] *)
Definition KZB : kentry := KZero (SA (EAlu ALU_SRL BE (ELit 3)) SBz) GE.
Definition KZT : kentry := KZero (SA (ELit 0) TSH) (ELit TG).
Hypothesis VARS : (APC.expr_vars_lt NF SE && APC.expr_vars_lt NF ENDE && APC.expr_vars_lt NF BE && APC.expr_vars_lt NF GE)%bool = true.
Hypothesis VALS : bv_unsigned (edenot E0 SE) = s /\ bv_unsigned (edenot E0 ENDE) = s + len /\ bv_unsigned (edenot E0 BE) = Bb /\ bv_unsigned (edenot E0 GE) = G.
Hypothesis BLK : Bb mod 8 = 0 /\ 0 < Bb <= s /\ 0 <= len /\ s + len <= Bb + 8 * G /\ 0 <= LENB /\ s + len + 2 * LENB < 2 ^ 63.
Hypothesis TAB : TLO mod 8 = 0 /\ 0 <= TLO /\ 0 <= TG /\ TLO + 8 * TG < 2 ^ 63 /\ TSH = TLO / 8 + SBz /\ 0 <= TSH < 2 ^ 64.

Abbreviation RCHK := (row_chk NF d CPS BLS FFS CPF SBz kv SE ENDE LENB KZB TLO TG KZT).

Theorem rows_leaf : forall i c ps r,
  RCHK i c ps r = true ->
  CSL1.site_chk1 (hl_segs L) (r_pc r) = Some (r_rd r, r_rs r) ->
  (forall E E' R R' A M model M1 model1,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> XI (r_j r) (CC.env_over NF (r_sid r) E') A M1 model1) ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred (r_j r) (CC.env_over NF (r_sid r) E') cr) ->
  CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps.
Proof.
  intros i c ps r Hchk Hsite XIT CRED.
  unfold row_chk in Hchk. destruct (nth_error CPS (r_j r)) as [cj|] eqn:Hcj; [|discriminate].
  apply andb_prop in Hchk as [Hchk Xcov]. apply andb_prop in Hchk as [Hchk Xgam]. apply andb_prop in Hchk as [Hchk Xshl]. apply andb_prop in Hchk as [Hchk XF].
  apply andb_prop in Hchk as [Hchk Xpc4]. apply andb_prop in Hchk as [Hchk Xpc0]. apply andb_prop in Hchk as [Xi Xpc].
  apply Nat.eqb_eq in Xi. apply Z.eqb_eq in Xpc. apply Z.leb_le in Xpc0. apply Z.ltb_lt in Xpc4.
  pose proof Xshl as Xshl'. unfold CSL.shl_chk in Xshl'.
  do 15 (apply andb_prop in Xshl' as [Xshl' _]). apply andb_prop in Xshl' as [_ Xnf]. apply Nat.leb_le in Xnf.
  intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
  refine (CSL1.shload1_leaf L ar C HI HIok LY_img LY_ro LY_below LY_nowrap NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok CPS K FPI XI
            i c ps (r_j r) cj (r_sid r) (r_rd r) (r_rs r) (r_cur r) SBz kv (r_a r) (r_b r) Hcj _ _ Xgam _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH).
  - rewrite Xpc. exact Hsite.
  - rewrite Xpc. exact Xshl.
  - rewrite Xpc. split; [exact Xpc0 | exact Xpc4].
  - clear fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
    intros Ex Ex' Rx Rx' Ax Mx mx Mx1 mx1 HAt' HA' HXI' Hag' HLF'. split; [| exact (XIT Ex Ex' Rx Rx' Ax Mx mx Mx1 mx1 HAt' HA' HXI' Hag' HLF')].
    pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF') as HLFv.
    assert (HK : know_ok (hl_segs L) Ex' (CCA.vis Ax mx1 Mx1) (SR.ps_cells ps)) by (unfold know_ok; apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HY)).
    (* [comment removed for export] *)
    pose proof (CBA.leaf_agree0 L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i c Ex Ex' Ax Mx mx HA' Xnf Hag') as HagE'.
    apply andb_prop in VARS as [VARS' V4]. apply andb_prop in VARS' as [VARS'' V3]. apply andb_prop in VARS'' as [V1 V2].
    destruct VALS as (U1 & U2 & U3 & U4). destruct BLK as (B8 & Bs & Hlen & Bsl & HL0 & HsL).
    rewrite (SR.edenot_agree_AP _ E0 Ex' _ HagE' V1) in U1. rewrite (SR.edenot_agree_AP _ E0 Ex' _ HagE' V2) in U2.
    rewrite (SR.edenot_agree_AP _ E0 Ex' _ HagE' V3) in U3. rewrite (SR.edenot_agree_AP _ E0 Ex' _ HagE' V4) in U4.
    pose proof (u64_range (edenot Ex' (r_cur r))) as Rc. change two64 with (2 ^ 64) in Rc. set (uc := bv_unsigned (edenot Ex' (r_cur r))) in *.
    destruct (r_tab r).
    + (* [comment removed for export] *)
      unfold tab_chk in Xcov. apply andb_prop in Xcov as [Xz Xr]. apply CC.has_cell_In in Xz.
      pose proof (CX.fact2_ok_sound (hl_segs L) Ex' _ _ _ HK Xr) as R1. cbn [kentry_ok] in R1. fold uc in R1.
      destruct TAB as (T8 & T0 & TG0 & Thi & Tsh & Tsh64).
      exists (ELit 0), TSH, (ELit TG), TLO. split; [exact Xz|].
      split; [unfold estart; cbn [a_base a_off edenot]; rewrite L5.unsigned_lit by (clear; lia); rewrite Tsh; clear; lia|]. split; [exact T8|].
      cbn [edenot]. rewrite L5.unsigned_lit by (clear - TG0 Thi T0; lia). clear - R1. lia.
    + (* [comment removed for export] *)
      unfold text_chk in Xcov. apply andb_prop in Xcov as [Xcov Xr2]. apply andb_prop in Xcov as [Xz Xr1]. apply CC.has_cell_In in Xz.
      pose proof (CX.fact2_ok_sound (hl_segs L) Ex' _ _ _ HK Xr1) as R1. pose proof (CX.fact2_ok_sound (hl_segs L) Ex' _ _ _ HK Xr2) as R2. cbn [kentry_ok] in R1, R2.
      unfold APC.esub, APC.eaddz in R1, R2. rewrite mkAlu_denot, u_sub64 in R1. fold uc in R1. rewrite U1 in R1.
      rewrite mkAlu_denot, u_sub64, mkAlu_denot, u_add64 in R2. fold uc in R2. rewrite U2 in R2.
      change (edenot Ex' (ELit (-1))) with (Z_to_bv 64 (-1)) in R2. rewrite u_lit64a in R2.
      assert (HM : (s + len + (-1) mod 2 ^ 64) mod 2 ^ 64 = s + len - 1).
      { rewrite (mod_neg_small (-1)) by (clear; lia). replace (s + len + (-1 + 2 ^ 64)) with ((s + len - 1) + 1 * 2 ^ 64) by (clear; lia). rewrite Z.mod_add by (clear; lia).
        apply Z.mod_small. clear - Bs Hlen HsL HL0. lia. }
      rewrite HM in R2. clear HM.
      pose proof (cover_arith s len uc LENB HL0 ltac:(clear - Bs; lia) Hlen HsL Rc (proj2 R1) (proj2 R2)) as CV.
      exists (EAlu ALU_SRL BE (ELit 3)), SBz, GE, Bb. split; [exact Xz|].
      split; [rewrite CL5A.estart_srl3'; unfold CL5A.uv; rewrite U3; reflexivity|]. split; [exact B8|].
      rewrite U4. clear - CV Bs Bsl. lia.
  - exact CRED.
Qed.
End Leaf.
End CSLR.
