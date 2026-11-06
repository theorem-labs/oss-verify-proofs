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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutShA CutShB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_dec_u64_casan_T Cut_dec_u64_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_dec_u64_casan.
Module GT := Cut_dec_u64_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module DUA.
Definition SITE1 : Z := 806808. Definition LOOPB : Z := 806812.
Definition SITE2 : Z := 806908. Definition TAIL1 : Z := 806912.
Definition SITE3 : Z := 806940. Definition TAIL2 : Z := 806944.
Definition RETPC : Z := 807048.
Definition SBz : Z := 2147450880.
Definition TABLO : Z := 151704.
Definition TABSH : Z := 2147469843.
Definition SE := EVar 10. Definition LNE := EVar 11. Definition VPE := EVar 12. Definition BE := EVar 32. Definition GE := EVar 33.
Definition DE := EVar 40. Definition KE := EVar 41. Definition BYE := EVar 45.
Definition LDK : expr := EAlu Instr.ALU_ADD LNE (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) DE) (EMd Instr.M_MUL (ELit (-1)) KE)).
Definition CUR : expr := EAlu Instr.ALU_ADD SE LDK.
Definition CUR1 : expr := EAlu Instr.ALU_ADD CUR (ELit 1).
Definition CUR3 : expr := EAlu Instr.ALU_ADD BYE (ELit 151709).
Definition DIG : expr := EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD BYE (ELit (-48))) (ELit 255).
Definition ACC2 : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 10) (EVar 42)) DIG.
Definition SID1 : CC.subst := [(40%nat, EVar 40); (41%nat, EVar 41); (42%nat, EVar 42); (43%nat, EVar 43); (44%nat, EVar 44)].
Definition SID2 : CC.subst := [(40%nat, EVar 40); (41%nat, EVar 41); (42%nat, ACC2); (43%nat, DIG); (44%nat, EVar 44)].
Definition SID3 : CC.subst := [(40%nat, EVar 40); (41%nat, EVar 41); (42%nat, EVar 42); (43%nat, EVar 43); (44%nat, EVar 44); (45%nat, EVar 45)].
Definition FFS : list (list (expr * Z * Z)) := [[]; []; []; []; []].
Definition CPF0 : list SGP.region := [(EVar 2, -64, ELit 64); (VPE, 0, ELit 8)].
Definition KZB : kentry := KZero (SA (EAlu Instr.ALU_SRL BE (ELit 3)) SBz) GE.
Definition KZT : kentry := KZero (SA (ELit 0) TABSH) (ELit 33).
Definition has := CC.has_cell.
Definition code_ok (ps : SR.post_spec) : bool := (CL.ps_reg_is ps 11 (ELit 0) || CL.ps_reg_is ps 11 (ELit 22) || CL.ps_reg_is ps 11 (ELit 34))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto j s => (Nat.eqb j 1 && (Nat.eqb i 0 || Nat.eqb i 2))%bool
  | CC.TOther pc =>
      if Z.eqb pc SITE1 then
        match nth_error G.CPS 2 with
        | Some cj => (Z.eqb (SR.ps_pc ps) SITE1 && Nat.eqb i 1 && CBA.regions_eqb (CC.cp_F c) CPF0 && Nat.ltb 41 (CC.cp_nx c)
                      && CSL.shl_chk GT.NF c ps cj SID1 28 28 LOOPB CUR SBz 41 8 6
                      && CHA.goto_amb_chk GT.NF G.HDECL c (nth i G.BLS []) (nth 2 G.BLS []) (nth i FFS []) (nth 2 FFS []) SID1
                      && has cells KZB)%bool
        | None => false end
      else if Z.eqb pc SITE2 then
        match nth_error G.CPS 3 with
        | Some cj => (Z.eqb (SR.ps_pc ps) SITE2 && Nat.eqb i 2 && CBA.regions_eqb (CC.cp_F c) CPF0 && Nat.ltb 41 (CC.cp_nx c)
                      && CSL.shl_chk GT.NF c ps cj SID2 13 13 TAIL1 CUR1 SBz 41 6 4
                      && CHA.goto_amb_chk GT.NF G.HDECL c (nth i G.BLS []) (nth 3 G.BLS []) (nth i FFS []) (nth 3 FFS []) SID2
                      && has cells KZB && has cells (KRange KE 1 1) && has cells (KRange DE 1 1))%bool
        | None => false end
      else if Z.eqb pc SITE3 then
        match nth_error G.CPS 4 with
        | Some cj => (Z.eqb (SR.ps_pc ps) SITE3 && Nat.eqb i 3 && CBA.regions_eqb (CC.cp_F c) CPF0
                      && CSL.shl_chk GT.NF c ps cj SID3 6 6 TAIL2 CUR3 SBz 41 4 2
                      && CHA.goto_amb_chk GT.NF G.HDECL c (nth i G.BLS []) (nth 4 G.BLS []) (nth i FFS []) (nth 4 FFS []) SID3
                      && has cells KZT && has cells (KRange BYE 0 255))%bool
        | None => false end
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) && code_ok ps)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma site1 : CSL1.site_chk1 RSEGS SITE1 = Some (28%nat, 28%nat). Proof. vmc_refl. Qed.
Lemma site2 : CSL1.site_chk1 RSEGS SITE2 = Some (13%nat, 13%nat). Proof. vmc_refl. Qed.
Lemma site3 : CSL1.site_chk1 RSEGS SITE3 = Some (6%nat, 6%nat). Proof. vmc_refl. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros i. do 5 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = [].
Proof. intros i. do 5 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma kn_loop : forall i c, (i = 1%nat \/ i = 2%nat) -> nth_error G.CPS i = Some c ->
  has (CC.cp_know c) (KRange KE 1 19) = true /\ has (CC.cp_know c) (KRange DE 0 134217728) = true /\ has (CC.cp_know c) (KRange LDK 0 19) = true.
Proof. intros i c [-> | ->] Hc; injection Hc as <-; vm_compute; (split; [reflexivity | split; reflexivity]). Qed.

Lemma lin_small : forall E e v hi, lden E (lin_of e) = v -> - 2 ^ 62 <= v < 2 ^ 62 -> bv_unsigned (edenot E e) <= hi -> hi < 2 ^ 62 -> bv_unsigned (edenot E e) = v.
Proof.
  intros E e v hi H Hv Hhi Hh. pose proof (lin_of_sound E e) as [q Hq]. unfold uE in Hq. rewrite H in Hq.
  pose proof (u64_range (edenot E e)) as Hu. unfold two64 in Hu. assert (q = 0) by lia. subst q. lia.
Qed.
End DUA.

Section DecU64Ok.
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
Hypothesis POI_TAB : Forall (fun r : Z * Z => DUA.TABLO + 264 <= fst r \/ snd r <= DUA.TABLO) (icl_poison IL0).
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Theorem dec_u64_ok : PMSA.dec_u64_specA L ar HI IC 806728.
Proof.
  intros LB FF LK cr A s len vp sp r. unfold PMSA.cps_asan, PMSA.text_inA.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (HIR & Ha0 & Ha1 & Ha2 & HLEN & HDEF & (b & n & HinB & N8 & HBS & HSN & HBZ) & HVD & HVO & HV8 & HVZ) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.acobj in *.

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
  destruct (CL5A.acobj_rng L ar LB FF sp vp 8 RFx CSP HVO ltac:(clear; lia)) as (O3 & O6 & O5 & O1 & O4).
  unfold BIGSHADOW_LO, BIGSHADOW_HI in O5. change (hid (vp + 8 <= 2147446784 \/ 17594333495296 <= vp)) in O5. change (hid (ar_fs ar + 32 <= vp \/ ahl_ceil ar <= vp)) in O1. change (hid (vp + 8 <= ahl_ceil ar \/ sp <= vp)) in O4.

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; n / 8] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 s) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 len) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 vp) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity. assert (V33 : ev E0 33 = Z_to_bv 64 (n / 8)) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = s) by (rewrite V10; apply u64_of_Z; clear - HBS HSN HLEN KB0 KB7; lia).
  assert (U11 : bv_unsigned (ev E0 11) = len) by (rewrite V11; apply u64_of_Z; clear - HLEN; lia).
  assert (U12 : bv_unsigned (ev E0 12) = vp) by (rewrite V12; apply u64_of_Z; clear - O3 O6; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; clear - KB0 KB7 KB3; lia).
  assert (U33 : bv_unsigned (ev E0 33) = n / 8) by (rewrite V33; apply u64_of_Z; clear - G1 N8' KB7 KB0; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 64) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(vp, 8)]).
  assert (WINC : incl WW WW) by (apply incl_refl).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.acobj_wok L ar LB FF sp _ vp 8 a RFx CSP HVO Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U12 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    exists (vp, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (SHR : forall q n0 a, 0 <= q -> 0 < n0 -> q + n0 <= 2 ^ 47 -> in_shadow_of q n0 a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha;
      rewrite ?CL5A.estart_srl3' in Ha; unfold estart, elenZ, CL5A.uv in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?U10, ?U11, ?U12, ?U32, ?U33 in Ha; rewrite ?u64_of_Z in Ha by (clear; lia).
    - split; [clear - Ha HBS HSN KB0 KB7; lia|]. split; [left; exists (b, n); split; [exact HinB | cbn [fst snd]; clear - Ha HBS HSN; lia]|].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in KB6. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Ha KB6 HBS HSN. lia.
    - destruct (CL5A.acobj_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) vp 8 a RFx CSP HVO ltac:(clear; lia) (CL5A.shreg_in_shadow vp 1 a HV8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1' & G2 & G3).
      split; [exact G1' | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
    - pose proof (CL5A.shreg_in_shadow b (n / 8) a KB8 ltac:(clear - G1; lia) ltac:(unfold SB; clear - Ha; lia)) as Hsh. rewrite <- N8' in Hsh.
      pose proof (SHR b n a ltac:(clear - KB0; lia) KB3 KB7 Hsh) as RG. split; [clear - RG; lia|]. split; [do 6 right; exists (b, n); split; [exact HinB | exact Hsh]|].
      exact (CL5A.not_stk_shadow_sh L ar LB FF b n a RFx ltac:(clear - KB0; lia) KB3 KB4 Hsh). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[<-|[<-|[]]]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (_ : word -> option byte) (_ : Model) => True).

  assert (LEAFK : forall i c ps0 E1 A1 M1 m1 E' R' M' m', nth_error G.CPS i = Some c -> CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DUA.FFS Cred 0 i E1 A1 M1 m1 ->
            env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
            bv_unsigned (ev E' 2) = sp /\ bv_unsigned (ev E' 10) = s /\ bv_unsigned (ev E' 11) = len /\ bv_unsigned (ev E' 12) = vp /\ bv_unsigned (ev E' 32) = b /\ bv_unsigned (ev E' 33) = n / 8
            /\ (forall X0, DUA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
            /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)).
  { intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF.
    pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DUA.FFS Cred 0 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
    assert (FZ : forall n0, (n0 <? 40)%nat = true -> ev E' n0 = ev E0 n0) by (intros n0 Hn; symmetry; apply (proj1 HagE'); unfold GT.NF; apply Nat.ltb_lt; exact Hn).
    split; [rewrite (FZ 2%nat eq_refl); exact U2|]. split; [rewrite (FZ 10%nat eq_refl); exact U10|]. split; [rewrite (FZ 11%nat eq_refl); exact U11|]. split; [rewrite (FZ 12%nat eq_refl); exact U12|].
    split; [rewrite (FZ 32%nat eq_refl); exact U32|]. split; [rewrite (FZ 33%nat eq_refl); exact U33|].
    split; [intros X0 HX0; apply CC.has_cell_In in HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)|].
    intros q e0 z Hq Hz; rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq); rewrite <- Hz; symmetry; apply Z_to_bv_bv_unsigned. }

  assert (CURV : forall Ex, bv_unsigned (ev Ex 10) = s -> bv_unsigned (ev Ex 11) = len -> 0 <= len - bv_unsigned (ev Ex 40) - bv_unsigned (ev Ex 41) <= len ->
            CL5A.uv Ex DUA.CUR = s + (len - bv_unsigned (ev Ex 40) - bv_unsigned (ev Ex 41)) /\ CL5A.uv Ex DUA.CUR1 = s + (len - bv_unsigned (ev Ex 40) - bv_unsigned (ev Ex 41)) + 1).
  { intros Ex X10 X11 Hc. unfold CL5A.uv, DUA.CUR, DUA.CUR1, DUA.LDK, DUA.SE, DUA.LNE, DUA.DE, DUA.KE.
    split; (apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hc HBS HSN HLEN KB0 KB7; lia]). }
  pose proof (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok) as AIOWF.
  rewrite <- LS in FPM.
  change 806728 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS DUA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact DUA.heap_ok.
  -   intros i c kk ps0 j sg IL E1 E' R' Mq Mq' cr1 _ _ _ HC. exact HC.
  -   intros i c kk ps0 j sg IL E1 R1 E' R' A1 M1 m1 M' m' _ _ _ _ _. exact I.
  -
    intros i c kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ DUA.leaf_ok _ _ _ _ _ IL) as X. unfold DUA.leaf_chk in X. cbn beta iota in X.
    assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hci & _); exact Hci).
    destruct (Z.eqb_spec pc DUA.SITE1) as [->|Hne1].
    {
      destruct (nth_error G.CPS 2) as [c2|] eqn:Hc2; [|discriminate].
      apply andb_prop in X as [X Ykz]. apply andb_prop in X as [X Ygam]. apply andb_prop in X as [X Yshl]. apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YF]. apply andb_prop in X as [Y0 Yi].
      apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi. subst i. apply Nat.ltb_lt in Ynx. apply CBA.regions_eqb_eq in YF.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
      refine (CSL1.shload1_leaf L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS DUA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK G.CPS K PMSA.fp_ok XI
                1%nat c ps0 2%nat c2 DUA.SID1 28%nat 28%nat DUA.CUR DUA.SBz 41%nat 8 6 Hc2 _ _ Ygam _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH).
      + rewrite Y0, LS. exact DUA.site1.
      + rewrite Y0. exact Yshl.
      + rewrite Y0. unfold DUA.SITE1. clear. lia.
      + clear fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
        intros Ex Ex' Rx Rx' Ax Mx mx Mx1 mx1 HAt' HA' _ Hag' HLF'. split; [|exact I].
        destruct (LEAFK 1%nat c ps0 Ex Ax Mx mx Ex' Rx' Mx1 mx1 Hci HA' Hag' HLF') as (W2 & W10 & W11 & W12 & W32 & W33 & CELL & REG).
        destruct (DUA.kn_loop 1%nat c (or_introl eq_refl) Hci) as (HK1 & HK2 & HK3). apply CC.has_cell_In in HK1. apply CC.has_cell_In in HK2. apply CC.has_cell_In in HK3.
        pose proof (proj2 HAt') as HK. unfold know_ok in HK. rewrite Forall_forall in HK.
        pose proof (HK _ HK1) as R1. pose proof (HK _ HK2) as R2. pose proof (HK _ HK3) as R3. cbn [kentry_ok edenot DUA.KE DUA.DE] in R1, R2. cbn [kentry_ok] in R3.
        assert (X11 : ev Ex' 11 = ev Ex 11) by (symmetry; apply (proj1 Hag' 11%nat); clear - Ynx; lia).
        assert (X40 : ev Ex' 40 = ev Ex 40) by (symmetry; apply (proj1 Hag' 40%nat); clear - Ynx; lia).
        assert (X41 : ev Ex' 41 = ev Ex 41) by (symmetry; apply (proj1 Hag' 41%nat); clear - Ynx; lia).
        assert (XL : edenot Ex' DUA.LDK = edenot Ex DUA.LDK) by (cbn [edenot DUA.LDK DUA.LNE DUA.DE DUA.KE]; rewrite X11, X40, X41; reflexivity).
        rewrite <- X40 in R2. rewrite <- X41 in R1. rewrite <- XL in R3.
        pose proof (DUA.lin_small Ex' DUA.LDK (len - bv_unsigned (ev Ex' 40) - bv_unsigned (ev Ex' 41)) 19 ltac:(unfold DUA.LDK, DUA.LNE, DUA.DE, DUA.KE; lin_eval; rw_atoms; clear; lia) ltac:(clear - R1 R2 HLEN; lia) (proj2 R3) ltac:(clear; lia)) as UL.
        destruct (CURV Ex' W10 W11 ltac:(clear - R1 R2 R3 UL; lia)) as (UC & _).
        exists (EAlu Instr.ALU_SRL DUA.BE (ELit 3)), DUA.SBz, DUA.GE, b. split; [apply CC.has_cell_In; exact Ykz|].
        split; [rewrite CL5A.estart_srl3'; unfold CL5A.uv, DUA.BE; cbn [edenot]; rewrite W32; reflexivity|]. split; [exact KB8|].
        change (bv_unsigned (edenot Ex' DUA.CUR)) with (CL5A.uv Ex' DUA.CUR). rewrite UC. unfold DUA.GE. cbn [edenot]. rewrite W33. rewrite <- N8'. clear - R1 R2 R3 UL HBS HSN. lia.
      + intros Ea Eb Rb Ma Mb cr1 _ _ _ HC. exact HC. }
    destruct (Z.eqb_spec pc DUA.SITE2) as [->|Hne2].
    {
      destruct (nth_error G.CPS 3) as [c3|] eqn:Hc3; [|discriminate].
      apply andb_prop in X as [X Ykd]. apply andb_prop in X as [X Ykk]. apply andb_prop in X as [X Ykz]. apply andb_prop in X as [X Ygam]. apply andb_prop in X as [X Yshl]. apply andb_prop in X as [X Ynx].
      apply andb_prop in X as [X YF]. apply andb_prop in X as [Y0 Yi].
      apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi. subst i. apply Nat.ltb_lt in Ynx. apply CBA.regions_eqb_eq in YF.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
      refine (CSL1.shload1_leaf L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS DUA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK G.CPS K PMSA.fp_ok XI
                2%nat c ps0 3%nat c3 DUA.SID2 13%nat 13%nat DUA.CUR1 DUA.SBz 41%nat 6 4 Hc3 _ _ Ygam _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH).
      + rewrite Y0, LS. exact DUA.site2.
      + rewrite Y0. exact Yshl.
      + rewrite Y0. unfold DUA.SITE2. clear. lia.
      + clear fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
        intros Ex Ex' Rx Rx' Ax Mx mx Mx1 mx1 HAt' HA' _ Hag' HLF'. split; [|exact I].
        destruct (LEAFK 2%nat c ps0 Ex Ax Mx mx Ex' Rx' Mx1 mx1 Hci HA' Hag' HLF') as (W2 & W10 & W11 & W12 & W32 & W33 & CELL & REG).
        pose proof (CELL _ Ykk) as R1. pose proof (CELL _ Ykd) as R2. cbn [kentry_ok edenot DUA.KE DUA.DE] in R1, R2.
        destruct (DUA.kn_loop 2%nat c (or_intror eq_refl) Hci) as (_ & _ & HK3). apply CC.has_cell_In in HK3.
        pose proof (proj1 (Forall_forall _ _) (proj2 HAt') _ HK3) as R3. cbn [kentry_ok] in R3.
        assert (X11 : ev Ex' 11 = ev Ex 11) by (symmetry; apply (proj1 Hag' 11%nat); clear - Ynx; lia).
        assert (X40 : ev Ex' 40 = ev Ex 40) by (symmetry; apply (proj1 Hag' 40%nat); clear - Ynx; lia).
        assert (X41 : ev Ex' 41 = ev Ex 41) by (symmetry; apply (proj1 Hag' 41%nat); clear - Ynx; lia).
        assert (XL : edenot Ex' DUA.LDK = edenot Ex DUA.LDK) by (cbn [edenot DUA.LDK DUA.LNE DUA.DE DUA.KE]; rewrite X11, X40, X41; reflexivity).
        rewrite <- XL in R3.
        assert (D40 : bv_unsigned (ev Ex' 40) = 1) by (clear - R2; lia). assert (D41 : bv_unsigned (ev Ex' 41) = 1) by (clear - R1; lia).
        pose proof (DUA.lin_small Ex' DUA.LDK (len - 2) 19 ltac:(unfold DUA.LDK, DUA.LNE, DUA.DE, DUA.KE; lin_eval; rw_atoms; clear; lia) ltac:(clear - HLEN; lia) (proj2 R3) ltac:(clear; lia)) as UL.
        destruct (CURV Ex' W10 W11 ltac:(clear - R3 UL HLEN D40 D41; lia)) as (_ & UC1). rewrite D40, D41 in UC1.
        exists (EAlu Instr.ALU_SRL DUA.BE (ELit 3)), DUA.SBz, DUA.GE, b. split; [apply CC.has_cell_In; exact Ykz|].
        split; [rewrite CL5A.estart_srl3'; unfold CL5A.uv, DUA.BE; cbn [edenot]; rewrite W32; reflexivity|]. split; [exact KB8|].
        change (bv_unsigned (edenot Ex' DUA.CUR1)) with (CL5A.uv Ex' DUA.CUR1). rewrite UC1. unfold DUA.GE. cbn [edenot]. rewrite W33. rewrite <- N8'. clear - R3 UL HBS HSN. lia.
      + intros Ea Eb Rb Ma Mb cr1 _ _ _ HC. exact HC. }
    destruct (Z.eqb_spec pc DUA.SITE3) as [->|Hne3].
    {
      destruct (nth_error G.CPS 4) as [c4|] eqn:Hc4; [|discriminate].
      apply andb_prop in X as [X Ykb]. apply andb_prop in X as [X Ykz]. apply andb_prop in X as [X Ygam]. apply andb_prop in X as [X Yshl]. apply andb_prop in X as [X YF]. apply andb_prop in X as [Y0 Yi].
      apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi. subst i. apply CBA.regions_eqb_eq in YF.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
      refine (CSL1.shload1_leaf L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS DUA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK G.CPS K PMSA.fp_ok XI
                3%nat c ps0 4%nat c4 DUA.SID3 6%nat 6%nat DUA.CUR3 DUA.SBz 41%nat 4 2 Hc4 _ _ Ygam _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH).
      + rewrite Y0, LS. exact DUA.site3.
      + rewrite Y0. exact Yshl.
      + rewrite Y0. unfold DUA.SITE3. clear. lia.
      + clear fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
        intros Ex Ex' Rx Rx' Ax Mx mx Mx1 mx1 HAt' HA' _ Hag' HLF'. split; [|exact I].
        destruct (LEAFK 3%nat c ps0 Ex Ax Mx mx Ex' Rx' Mx1 mx1 Hci HA' Hag' HLF') as (W2 & W10 & W11 & W12 & W32 & W33 & CELL & REG).
        pose proof (CELL _ Ykb) as RB. cbn [kentry_ok edenot DUA.BYE] in RB.
        exists (ELit 0), DUA.TABSH, (ELit 33), DUA.TABLO. split; [apply CC.has_cell_In; exact Ykz|].
        split; [unfold estart; cbn [a_base a_off edenot]; rewrite L5.unsigned_lit by (clear; lia); reflexivity|]. split; [reflexivity|].
        unfold DUA.CUR3, DUA.BYE, DUA.TABLO. cbn [edenot]. rewrite u_add64, !u_lit64. change two64 with (2 ^ 64). rewrite (Z.mod_small 151709) by (clear; lia). rewrite Z.mod_small by (clear - RB; lia).
        clear - RB. lia.
      + intros Ea Eb Rb Ma Mb cr1 _ _ _ HC. exact HC. }

    apply andb_prop in X as [X Ycode]. apply andb_prop in X as [Xbase Xfoot].
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA _].
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS DUA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok DUA.RETPC i c ps0 _ Xbase _ (DUA.ffs_i i) fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact DUA.ret_at | exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB LB G.BLS i E1 = LB) by (unfold CHA.curB; rewrite DUA.bls_i; reflexivity). rewrite HB in HH1.
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [|repeat split; reflexivity].
    destruct (LEAFK i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF) as (_ & _ & _ & _ & _ & _ & CELL & REG).
    assert (HC : exists cc, In cc [0; 22; 34] /\ CL.ps_reg_is ps0 11 (ELit cc) = true).
    { unfold DUA.code_ok in Ycode. apply orb_prop in Ycode. destruct Ycode as [Yc|Yc]; [apply orb_prop in Yc; destruct Yc as [Yc|Yc]|];
        [exists 0; split; [left; reflexivity | exact Yc] | exists 22; split; [right; left; reflexivity | exact Yc] | exists 34; split; [right; right; left; reflexivity | exact Yc]]. }
    destruct HC as (cc & Hcc & Yc). exists (bv_unsigned (getr R' 10%bv)), cc.
    split; [unfold PMSA.a0; symmetry; apply Z_to_bv_bv_unsigned|]. split; [|exact Hcc].
    replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply (REG 11%nat (ELit cc) cc Yc). cbn [edenot]. apply L5.unsigned_lit. cbn [In] in Hcc. clear - Hcc. lia.
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VS : CL5A.visr (ahid A model) (sp - 64) 64).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    assert (VB : CL5A.visr (ahid A model) b n).
    { intros q Hq. apply CLV; [clear - Hq KB0 KB7; lia | left; exists (b, n); split; [exact HinB | cbn [fst snd]; clear - Hq; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in KB6. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq KB6. lia. }
    assert (VBS : forall a, in_shadow_of b n a -> ahid A model (Z_to_bv 64 a) = false).
    { intros a Ha. pose proof (SHR b n a ltac:(clear - KB0; lia) KB3 KB7 Ha) as RG. apply CLV; [clear - RG; lia | do 6 right; exists (b, n); split; [exact HinB | exact Ha] |].
      exact (CL5A.not_stk_shadow_sh L ar LB FF b n a RFx ltac:(clear - KB0; lia) KB3 KB4 Ha). }
    assert (VO : CL5A.visr (ahid A model) vp 8).
    { intros q Hq. destruct (CL5A.acobj_wok L ar LB FF sp 0 vp 8 (vp + q) RFx CSP HVO ltac:(clear - Hq; lia)) as (G1' & G2 & G3). exact (CLV _ G1' (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 1 -> ahid A model (Z_to_bv 64 (S vp + j)) = false).
    { intros j Hj. destruct (CL5A.acobj_sh_wok L ar LB FF sp 0 vp 8 (S vp + j) RFx CSP HVO ltac:(clear; lia) (CL5A.shreg_in_shadow vp 1 (S vp + j) HV8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1' & G2 & G3).
      exact (CLV _ G1' (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 64) 64) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DTX : L5.defined Mv s len) by (apply (CL5A.defined_vis _ M s len (CL5A.visr_sub _ b n s len VB HBS HSN)); exact HDEF).
    assert (DVP : L5.defined Mv vp 8) by (apply (CL5A.defined_vis _ M vp 8 VO); exact HVD).
    assert (UVB : CL5A.uv E0 (EVar 32) = b) by (unfold CL5A.uv; cbn [edenot]; exact U32).
    assert (UVP : CL5A.uv E0 (EVar 12) = vp) by (unfold CL5A.uv; cbn [edenot]; exact U12).
    unfold PMLA.img_ro in HIR. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_casan] in HIR.
    assert (IMGK : forall lo hi, 65536 <= lo -> hi <= 1392640 -> kentry_ok (hl_segs L) E0 Mv (KImg lo hi)).
    { intros lo hi Hlo Hhi. apply AxSymRun3.kimg_intro; [clear - Hlo; lia | clear - Hhi; lia |]. intros i1 Hi1. unfold Mv, CCA.vis.
      destruct (mrestrict (ahid A model) M (Z_to_bv 64 i1)) eqn:Hv; [|reflexivity]. exfalso. exact (CL5A.vis_def (ahid A model) M (Z_to_bv 64 i1) ltac:(rewrite Hv; discriminate) (HIR i1 ltac:(clear - Hi1 Hlo Hhi; lia))). }
    destruct (ISH _ _ _ _ _ _ _ HH DUA.TABLO 264 ltac:(rewrite ILO; unfold DUA.TABLO; clear; lia) ltac:(rewrite IHI; unfold DUA.TABLO; clear; lia) ltac:(clear; lia) POI_TAB) as [BZ BA].
    assert (ISX : forall jj, 0 <= jj < 33 -> in_shadow_of DUA.TABLO 264 (DUA.TABSH + jj)) by (intros jj Hjj; unfold in_shadow_of, S, DUA.TABLO, DUA.TABSH, SB; clear - Hjj; lia).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); try (apply Forall_nil).
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply IMGK; clear; lia.
    + apply IMGK; clear; lia.
    + eapply CL5A.kzero_intro with (A := DUA.TABSH) (N := 33); [unfold estart, DUA.TABSH; cbn [a_base a_off edenot]; rewrite L5.unsigned_lit by (clear; lia); clear; lia | reflexivity | unfold DUA.TABSH; clear; lia | unfold DUA.TABSH; clear; lia | unfold DUA.TABSH; clear; lia |].
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
    + eapply CL5.kunk_intro with (A := vp) (N := 8); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DVP].
    + eapply CL5.kwr_intro with (A := vp) (N := 8); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DVP].
    + eapply CL5.krange_intro with (v := vp); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | unfold hid in O1; clear - O1 O6 FSLO CL; lia].
    + eapply CL5.kalign_intro with (v := vp); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact HV8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 vp UVP); [clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (HVZ j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := vp) (N2 := 8); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.kwr_intro with (A := sp - 64) (N := 64); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 64) (N1 := 64) (A2 := vp) (N2 := 8); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in O4; clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 64) (N1 := 64) (A2 := s) (N2 := len); [ev0 | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U11 | clear - KB4 S2 HBS HSN; lia].
    + eapply CL5.kunk_intro with (A := sp - 64) (N := 64); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
  -
    split; [|exact I].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. rewrite DUA.bls_i, DUA.ffs_i. cbn [CH2.den CHA.denF map app length Z.of_nat Z.sub].
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.

End DecU64Ok.
