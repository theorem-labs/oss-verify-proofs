(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutShA CutShB CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_validate_casan_T Cut_validate_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_validate_casan.
Module GT := Cut_validate_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module VDA.
Definition RETPC : Z := 813844.
Definition SBz : Z := 2147450880.
Definition LENB : Z := 134217728.
Definition LENP : Z := 268435456.
Definition TLO : Z := 152096.
Definition TG : Z := 32.
Definition TSH : Z := 2147469892.
Definition SE := EVar 10. Definition LNE := EVar 11. Definition BE := EVar 32. Definition GE := EVar 33.
Definition ENDE : expr := EAlu Instr.ALU_ADD SE LNE.
Definition P : expr := EAlu Instr.ALU_ADD SE (EAlu Instr.ALU_ADD LNE (EMd Instr.M_MUL (ELit (-1)) (EVar 40))).
Definition PK (k : Z) : expr := EAlu Instr.ALU_ADD P (ELit k).
Definition TABA : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EExt true 0 1 (EVar 44)) (ELit 255)) (ELit TLO).
Definition SIDI : CC.subst := [(40%nat, EVar 40); (41%nat, EVar 41); (42%nat, EVar 42); (43%nat, EVar 43); (44%nat, EVar 44); (45%nat, EVar 45); (46%nat, EVar 46); (47%nat, EVar 47)].
Definition SIDB : CC.subst := [(40%nat, EVar 40); (41%nat, EVar 41); (42%nat, EVar 42); (43%nat, EVar 43); (44%nat, EExt true 0 1 (EVar 48)); (45%nat, EVar 45); (46%nat, EVar 46); (47%nat, EVar 47)].
Definition KZB : kentry := CSLR.KZB SBz BE GE.
Definition KZT : kentry := CSLR.KZT TG TSH.
Definition arow (k : Z) : CSLR.row := CSLR.ROW (Z.to_nat (1 + k)) (813132 + 28 * k) (Z.to_nat (2 + k)) SIDB 11 11 (PK k) (40 - 2 * k) (38 - 2 * k) false.
Definition ROWS : list CSLR.row :=
  [CSLR.ROW 1 813124 2 SIDI 10 10 P 40 38 false; arow 1; arow 2; arow 3; arow 4; arow 5; arow 6; arow 7;
   CSLR.ROW 10 813380 11 SIDI 12 12 TABA 30 22 true;
   CSLR.ROW 11 813452 12 SIDI 11 11 (PK 3) 22 20 false;
   CSLR.ROW 11 813484 15 SIDI 11 11 (PK 2) 22 20 false; CSLR.ROW 12 813484 13 SIDI 11 11 (PK 2) 20 18 false;
   CSLR.ROW 11 813512 17 SIDI 11 11 (PK 1) 22 20 false; CSLR.ROW 15 813512 16 SIDI 11 11 (PK 1) 20 18 false; CSLR.ROW 13 813512 14 SIDI 11 11 (PK 1) 18 16 false].
Definition FFS : list (list (expr * Z * Z)) := repeat [] 18.
Definition CPF0 : list SGP.region := [(EVar 2, -128, ELit 128)].
Definition has := CC.has_cell.
Definition a0e (ps : SR.post_spec) : expr := nth 10 (CA.ps_reglist ps) (ELit 0).
Definition a1e (ps : SR.post_spec) : expr := nth 11 (CA.ps_reglist ps) (ELit 0).
Definition post_chk (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let q := a0e ps in
  (CL.ps_reg_is ps 10 q && CX.fact2_ok cells (KRange (APC.esub q SE) 0 LENP) && CX.fact2_ok cells (KRange (APC.esub ENDE q) 0 LENP)
   && CL.ps_reg_is ps 11 (a1e ps) && CX.fact2_ok cells (KRange (a1e ps) 0 6))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => true
  | CC.TOther pc =>
      if Z.eqb pc RETPC then (CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) && post_chk ps)%bool
      else match CSLR.find_row ROWS i (SR.ps_pc ps) with
           | Some r => CSLR.row_chk GT.NF G.HDECL G.CPS G.BLS FFS CPF0 SBz 40 SE ENDE LENB KZB TLO TG KZT i c ps r
           | None => false
           end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma sites : CSLR.sites_ok RSEGS ROWS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros i. unfold FFS. apply nth_repeat. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = [].
Proof. intros i. do 18 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
End VDA.

Section ValidateOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL0 : icpt_layout.
Abbreviation IC := PMLA.C_casan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis ISH : rt_img_shadow L IL0 HI.
Hypothesis POI_TAB : Forall (fun r : Z * Z => VDA.TLO + 256 <= fst r \/ snd r <= VDA.TLO) (icl_poison IL0).
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Theorem validate_ok : PMSA.validate_specA L ar HI IC 812976.
Proof.
  intros LB FF LK cr A s len sp r. unfold PMSA.cps_asan, PMSA.text_inA.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & HLEN & HDEF & HIR & (b & n & HinB & N8 & HBS & HSN & HBZ)) Hcont.
  unfold PMSA.a0, PMSA.a1 in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.

  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (b, n) HinB) as ((KB0 & KB1 & KB16 & KB3 & KB4 & (KB5 & KB6 & KB7)) & KBdef & KBsha & KBbap & KBfap). cbn [fst snd] in KB0, KB1, KB16, KB3, KB4, KB5, KB6, KB7, KBdef, KBsha, KBbap, KBfap.
  pose proof (CHA.mod8_of_16 _ KB16) as KB8.
  unfold BIGSHADOW_LO, BIGSHADOW_HI in KB6. change (hid (b + n <= 2147446784 \/ 17594333495296 <= b)) in KB6.
  assert (N8' : n = 8 * (n / 8)) by (pose proof (Z_div_mod_eq_full n 8) as D; rewrite N8 in D; clear - D; lia).
  assert (G1 : 1 <= n / 8) by (clear - N8' KB3; lia).

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; n / 8] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 s) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 len) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity. assert (V33 : ev E0 33 = Z_to_bv 64 (n / 8)) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = s) by (rewrite V10; apply u64_of_Z; clear - HBS HSN HLEN KB0 KB7; lia).
  assert (U11 : bv_unsigned (ev E0 11) = len) by (rewrite V11; apply u64_of_Z; clear - HLEN; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; clear - KB0 KB7 KB3; lia).
  assert (U33 : bv_unsigned (ev E0 33) = n / 8) by (rewrite V33; apply u64_of_Z; clear - G1 N8' KB7 KB0; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 128) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := ([] : list L5.range)).
  assert (WINC : incl WW WW) by (apply incl_refl).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a [] _).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a))
    by (intros rg []).
  assert (SHR : forall q n0 a, 0 <= q -> 0 < n0 -> q + n0 <= 2 ^ 47 -> in_shadow_of q n0 a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha;
      rewrite ?CL5A.estart_srl3' in Ha; unfold estart, elenZ, CL5A.uv in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?U10, ?U11, ?U32, ?U33 in Ha; rewrite ?u64_of_Z in Ha by (clear; lia).
    - split; [clear - Ha HBS HSN KB0 KB7; lia|]. split; [left; exists (b, n); split; [exact HinB | cbn [fst snd]; clear - Ha HBS HSN; lia]|].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in KB6. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Ha KB6 HBS HSN. lia.
    - pose proof (CL5A.shreg_in_shadow b (n / 8) a KB8 ltac:(clear - G1; lia) ltac:(unfold SB; clear - Ha; lia)) as Hsh. rewrite <- N8' in Hsh.
      pose proof (SHR b n a ltac:(clear - KB0; lia) KB3 KB7 Hsh) as RG. split; [clear - RG; lia|]. split; [do 6 right; exists (b, n); split; [exact HinB | exact Hsh]|].
      exact (CL5A.not_stk_shadow_sh L ar LB FF b n a RFx ltac:(clear - KB0; lia) KB3 KB4 Hsh). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[<-|[]]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (_ : word -> option byte) (_ : Model) => True).

  assert (VARS : (APC.expr_vars_lt GT.NF VDA.SE && APC.expr_vars_lt GT.NF VDA.ENDE && APC.expr_vars_lt GT.NF VDA.BE && APC.expr_vars_lt GT.NF VDA.GE)%bool = true) by vmc_refl.
  assert (VALS : bv_unsigned (edenot E0 VDA.SE) = s /\ bv_unsigned (edenot E0 VDA.ENDE) = s + len /\ bv_unsigned (edenot E0 VDA.BE) = b /\ bv_unsigned (edenot E0 VDA.GE) = n / 8).
  { unfold VDA.ENDE; unfold VDA.SE, VDA.LNE, VDA.BE, VDA.GE. cbn [edenot]. rewrite u_add64, U10, U11, U32, U33. split; [reflexivity|]. split; [apply Z.mod_small; clear - HBS HSN HLEN KB0 KB7; lia|]. split; reflexivity. }
  assert (BLK : b mod 8 = 0 /\ 0 < b <= s /\ 0 <= len /\ s + len <= b + 8 * (n / 8) /\ 0 <= VDA.LENB /\ s + len + 2 * VDA.LENB < 2 ^ 63).
  { unfold VDA.LENB. split; [exact KB8|]. split; [clear - KB0 HBS; lia|]. split; [clear - HLEN; lia|]. split; [clear - HSN N8'; lia|]. clear - HSN KB7. lia. }
  assert (TAB : VDA.TLO mod 8 = 0 /\ 0 <= VDA.TLO /\ 0 <= VDA.TG /\ VDA.TLO + 8 * VDA.TG < 2 ^ 63 /\ VDA.TSH = VDA.TLO / 8 + VDA.SBz /\ 0 <= VDA.TSH < 2 ^ 64).
  { unfold VDA.TLO, VDA.TG, VDA.TSH, VDA.SBz. repeat split; reflexivity || (clear; lia). }

  assert (LEAFK : forall i c ps0 E1 A1 M1 m1 E' R' M' m', nth_error G.CPS i = Some c -> CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS VDA.FFS Cred 0 i E1 A1 M1 m1 ->
            env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
            bv_unsigned (edenot E' VDA.SE) = s /\ bv_unsigned (edenot E' VDA.ENDE) = s + len
            /\ know_ok (hl_segs L) E' (CCA.vis A1 m' M') (SR.ps_cells ps0)
            /\ (forall (q : nat) (e0 : expr), CL.ps_reg_is ps0 q e0 = true -> getr R' (Z_to_bv 5 (Z.of_nat q)) = edenot E' e0)).
  { intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF.
    pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS VDA.FFS Cred 0 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
    apply andb_prop in VARS as [VARS' _]. apply andb_prop in VARS' as [VARS'' _]. apply andb_prop in VARS'' as [X1 X2].
    split; [rewrite <- (SR.edenot_agree_AP _ E0 E' _ HagE' X1); exact (proj1 VALS)|]. split; [rewrite <- (SR.edenot_agree_AP _ E0 E' _ HagE' X2); exact (proj1 (proj2 VALS))|].
    split; [unfold know_ok; apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HY)|].
    intros q e0 Hq. exact (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). }
  pose proof (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok) as AIOWF.
  rewrite <- LS in FPM.
  change 812976 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VDA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact VDA.heap_ok.
  -   intros i c kk ps0 j sg IL E1 E' R' Mq Mq' cr1 _ _ _ HC. exact HC.
  -   intros i c kk ps0 j sg IL E1 R1 E' R' A1 M1 m1 M' m' _ _ _ _ _. exact I.
  -
    intros i c kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ VDA.leaf_ok _ _ _ _ _ IL) as X. unfold VDA.leaf_chk in X. cbn beta iota in X.
    assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hci & _); exact Hci).
    destruct (Z.eqb_spec pc VDA.RETPC) as [->|Hne].
    +
      apply andb_prop in X as [X Ypost]. apply andb_prop in X as [Xbase Xfoot].
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA _].
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VDA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
                K DEF0 R r EV Hra Hraok VDA.RETPC i c ps0 _ Xbase _ (VDA.ffs_i i) fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
        [rewrite LS; exact VDA.ret_at | exact Xfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (HB : CHA.curB LB G.BLS i E1 = LB) by (unfold CHA.curB; rewrite VDA.bls_i; reflexivity). rewrite HB in HH1.
      rewrite SCRV in HP.
      apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      split; [|repeat split; reflexivity].
      destruct (LEAFK i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF) as (W10 & WEND & HK & REG).
      unfold VDA.post_chk in Ypost. apply andb_prop in Ypost as [Ypost Ycode]. apply andb_prop in Ypost as [Ypost Yc1]. apply andb_prop in Ypost as [Ypost Y2]. apply andb_prop in Ypost as [Yq Y1].
      set (q := VDA.a0e ps0) in *. set (q1 := VDA.a1e ps0) in *.
      pose proof (CX.fact2_ok_sound (hl_segs L) E' _ _ _ HK Y1) as Q1. pose proof (CX.fact2_ok_sound (hl_segs L) E' _ _ _ HK Y2) as Q2. cbn [kentry_ok] in Q1, Q2.
      unfold APC.esub in Q1, Q2. rewrite mkAlu_denot, u_sub64, W10 in Q1. rewrite mkAlu_denot, u_sub64, WEND in Q2.
      pose proof (u64_range (edenot E' q)) as Rq. change two64 with (2 ^ 64) in Rq. set (uq := bv_unsigned (edenot E' q)) in *.
      assert (HQ : s <= uq <= s + len).
      { unfold VDA.LENP in Q1, Q2.
        assert (G1' : s <= uq) by (destruct (Z_lt_le_dec uq s) as [Hl|Hl]; [exfalso; rewrite CSLR.mod_neg_small in Q1 by (clear - Hl Rq HBS KB0 HSN KB7 HLEN; lia); clear - Q1 Hl Rq HBS KB0 HSN KB7 HLEN; lia | exact Hl]).
        rewrite Z.mod_small in Q1 by (clear - G1' Rq HBS KB0; lia).
        destruct (Z_lt_le_dec (s + len) uq) as [Hg|Hg]; [exfalso; rewrite CSLR.mod_neg_small in Q2 by (clear - Hg Q1 HBS HSN KB0 KB7 HLEN; lia); clear - Q2 Hg Q1 HBS HSN KB0 KB7 HLEN; lia|].
        clear - G1' Hg. lia. }
      pose proof (CX.fact2_ok_sound (hl_segs L) E' _ _ _ HK Ycode) as Q3. cbn [kentry_ok] in Q3.
      exists uq, (bv_unsigned (edenot E' q1)). split; [unfold PMSA.a0; replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity); rewrite (REG 10%nat q Yq); unfold uq; symmetry; apply Z_to_bv_bv_unsigned|].
      split; [replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity); rewrite (REG 11%nat q1 Yc1); symmetry; apply Z_to_bv_bv_unsigned|].
      split; [exact HQ|]. clear - Q3. lia.
    +
      destruct (CSLR.find_row VDA.ROWS i (SR.ps_pc ps0)) as [rw|] eqn:Hrow; [|discriminate].
      destruct (CSLR.find_row_In _ _ _ _ Hrow) as (Hin & _ & _).
      refine (CSLR.rows_leaf L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VDA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK G.CPS K PMSA.fp_ok XI
                VDA.CPF0 VDA.SBz 40%nat VDA.SE VDA.ENDE VDA.BE VDA.GE s len b (n / 8) VDA.LENB VDA.TLO VDA.TG VDA.TSH VARS VALS BLK TAB i c ps0 rw X _ _ _).
      * rewrite LS. exact (CSLR.sites_ok_In _ _ _ VDA.sites Hin).
      * intros; exact I.
      * intros Ea Eb Rb Ma Mb cr1 _ _ _ HC. exact HC.
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VS : CL5A.visr (ahid A model) (sp - 128) 128).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    assert (VB : CL5A.visr (ahid A model) b n).
    { intros q Hq. apply CLV; [clear - Hq KB0 KB7; lia | left; exists (b, n); split; [exact HinB | cbn [fst snd]; clear - Hq; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in KB6. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq KB6. lia. }
    assert (VBS : forall a, in_shadow_of b n a -> ahid A model (Z_to_bv 64 a) = false).
    { intros a Ha. pose proof (SHR b n a ltac:(clear - KB0; lia) KB3 KB7 Ha) as RG. apply CLV; [clear - RG; lia | do 6 right; exists (b, n); split; [exact HinB | exact Ha] |].
      exact (CL5A.not_stk_shadow_sh L ar LB FF b n a RFx ltac:(clear - KB0; lia) KB3 KB4 Ha). }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 128) 128) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DTX : L5.defined Mv s len) by (apply (CL5A.defined_vis _ M s len (CL5A.visr_sub _ b n s len VB HBS HSN)); exact HDEF).
    assert (UVB : CL5A.uv E0 (EVar 32) = b) by (unfold CL5A.uv; cbn [edenot]; exact U32).
    unfold PMLA.img_ro in HIR. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_casan] in HIR.
    assert (IMGK : forall lo hi, 65536 <= lo -> hi <= 1392640 -> kentry_ok (hl_segs L) E0 Mv (KImg lo hi)).
    { intros lo hi Hlo Hhi. apply AxSymRun3.kimg_intro; [clear - Hlo; lia | clear - Hhi; lia |]. intros i1 Hi1. unfold Mv, CCA.vis.
      destruct (mrestrict (ahid A model) M (Z_to_bv 64 i1)) eqn:Hv; [|reflexivity]. exfalso. exact (CL5A.vis_def (ahid A model) M (Z_to_bv 64 i1) ltac:(rewrite Hv; discriminate) (HIR i1 ltac:(clear - Hi1 Hlo Hhi; lia))). }
    destruct (ISH _ _ _ _ _ _ _ HH VDA.TLO 256 ltac:(rewrite ILO; unfold VDA.TLO; clear; lia) ltac:(rewrite IHI; unfold VDA.TLO; clear; lia) ltac:(clear; lia) POI_TAB) as [BZ BA].
    assert (ISX : forall jj, 0 <= jj < 32 -> in_shadow_of VDA.TLO 256 (VDA.TSH + jj)) by (intros jj Hjj; unfold in_shadow_of, S, VDA.TLO, VDA.TSH, SB; clear - Hjj; lia).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); try (apply Forall_nil).
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply IMGK; clear; lia.
    + eapply CL5A.kzero_intro with (A := VDA.TSH) (N := 32); [unfold estart, VDA.TSH; cbn [a_base a_off edenot]; rewrite L5.unsigned_lit by (clear; lia); clear; lia | reflexivity | unfold VDA.TSH; clear; lia | unfold VDA.TSH; clear; lia | unfold VDA.TSH; clear; lia |].
      intros jj Hjj. apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BA _ (ISX jj Hjj)) | exact (BZ _ (ISX jj Hjj))].
    + eapply CL5.kunk_intro with (A := s) (N := len); [ev0 | unfold elenZ; cbn [edenot]; exact U11 | clear - HBS KB0; lia | clear - HSN KB7; lia | clear - HSN KB7 HLEN; lia | exact DTX].
    + eapply CL5.krange_intro with (v := len); [lin_eval; rw_atoms; clear; lia | clear - HLEN; lia | clear - HLEN; lia].
    + eapply CL5.krange_intro with (v := s); [lin_eval; rw_atoms; clear; lia | clear - HBS HSN KB0 KB7 HLEN; lia | clear - HBS HSN KB0 KB4 HLEN SP1; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := s) (N2 := len); [reflexivity | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U11 | unfold hid in KB6; clear - KB6 HBS HSN; lia].
    + eapply CL5.krange_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - KB0 KB7 KB3; lia | clear - KB0 KB7 KB3; lia].
    + eapply CL5.kalign_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - KB0 KB7 KB3; lia | clear; lia | exact KB8].
    + eapply CL5A.kzero_intro with (A := b / 8 + SB) (N := n / 8); [rewrite CL5A.estart_srl3', UVB; reflexivity | unfold elenZ; cbn [edenot]; exact U33 | unfold SB; clear - KB0; lia | unfold SB; clear - KB0 KB7 KB3; pose proof (Z.div_le_upper_bound b 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia | unfold SB; clear - KB0 KB7 KB3; pose proof (Z.div_le_upper_bound b 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia |].
      intros j Hj. apply CL5A.byte_vis; [apply VBS; rewrite N8'; apply (CL5A.shreg_in_shadow b (n / 8)); [exact KB8 | clear - G1; lia | unfold S, SB; clear - Hj; lia] | exact (HBZ j Hj)].
    + eapply CL5.krange_intro with (v := n / 8); [lin_eval; rw_atoms; clear; lia | clear - G1 KB7 KB0 N8'; lia | clear - G1 KB7 KB0 N8'; lia].
    + eapply CL5.kwr_intro with (A := sp - 128) (N := 128); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 128) (N1 := 128) (A2 := s) (N2 := len); [ev0 | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U11 | clear - KB4 S2 HBS HSN; lia].
    + eapply CL5.kunk_intro with (A := sp - 128) (N := 128); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := s + len); [lin_eval; rw_atoms; clear; lia | clear - HBS HSN KB0 KB7 HLEN; lia | clear - HBS HSN KB0 KB4 KB7 HLEN SP1 CL; lia].
  -
    split; [|exact I].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. rewrite VDA.bls_i, VDA.ffs_i. cbn [CH2.den CHA.denF map app length Z.of_nat Z.sub].
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.

End ValidateOk.
