(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmCurSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_cstr_null_csrc_u Cut_cstr_true_csrc_u Cut_cstr_false_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module CSTR.
Module GN := Cut_cstr_null_csrc_u.  Module GT := Cut_cstr_true_csrc_u.  Module GF := Cut_cstr_false_csrc_u.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.
Definition RET : Z := 0x45354.
Definition SCRT : Z := 8304.
Definition CSAVED := CL5.CSAVED.
Definition has := GK.has.
Definition NFV : nat := 32.
Abbreviation NOGOTO := (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end).
Definition e_o := EVar 10.  Definition SP := EVar 2.

Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.
Lemma csaved_lt : forall y : reg, In (ridx y) CSAVED -> (ridx y < NFV)%nat.
Proof. intros y Hy. unfold CSAVED, CL5.CSAVED in Hy. cbn [In] in Hy. unfold NFV. intuition lia. Qed.
Fixpoint exprs_eqb (a b : list expr) : bool := match a, b with [], [] => true | x :: a', y :: b' => (expr_eqb x y && exprs_eqb a' b')%bool | _, _ => false end.
Lemma exprs_eqb_eq : forall a b, exprs_eqb a b = true -> a = b.
Proof. induction a as [|x a IH]; intros [|y b] H; try discriminate H; [reflexivity|]. cbn in H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. rewrite H1, (IH b H2). reflexivity. Qed.

Fixpoint chars_chk (cells : list kentry) (k : Z) (txt : list Z) : bool :=
  match txt with [] => true | c :: t => (has cells (KWord (SA e_o k) 1 (ELit c)) && chars_chk cells (k + 1) t)%bool end.
Lemma chars_chk_nth : forall cells txt k i, chars_chk cells k txt = true -> (i < length txt)%nat ->
  has cells (KWord (SA e_o (k + Z.of_nat i)) 1 (ELit (nth i txt 0))) = true.
Proof.
  intros cells txt. induction txt as [|c t IH]; intros k i H Hi; [cbn in Hi; lia|].
  cbn [chars_chk] in H. apply andb_prop in H as [H1 H2]. destruct i as [|i].
  - rewrite Z.add_0_r. exact H1.
  - cbn [nth]. replace (k + Z.of_nat (S i)) with ((k + 1) + Z.of_nat i) by lia. apply IH; [exact H2 | cbn in Hi; lia].
Qed.
Definition leaf_c (txt : list Z) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [] pc) && CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && Nat.leb NFV (CC.cp_nx c)
                     && has (SR.ps_cells ps) (KWord (SA e_o 0) 1 (ELit (2 * Z.of_nat (length txt))))
                     && chars_chk (SR.ps_cells ps) 1 txt
                     && has (SR.ps_cells ps) (KWord (SA e_o (1 + Z.of_nat (length txt))) 1 (ELit 0)))%bool
  end.

Definition COMMON : list kentry :=
  [KUnk (SA e_o 0) (ELit 24); KWr (SA e_o 0) (ELit 24); KRange e_o (2 ^ 40) (2 ^ 47); KAlign e_o 8;
   KUnk (SA SP (- SCRT)) (ELit SCRT); KWr (SA SP (- SCRT)) (ELit SCRT); KRange SP (2 ^ 40) (2 ^ 47); KAlign SP 16; KDisj (SA SP (- SCRT)) (ELit SCRT) (SA e_o 0) (ELit 24);
   KImg 0x10000 0xc3a78].
Definition kn_chk (lit : Z) (cp0 : CC.cutpoint) : bool :=
  (forallb (fun K => has COMMON K) (CC.cp_know cp0) && exprs_eqb (CC.cp_regs cp0) (sr_upd sr_id 11 (ELit lit)))%bool.

Lemma kn_n : kn_chk PMCS.STR_NULL GN.cp0 = true.  Proof. vmc_refl. Qed.
Lemma kn_t : kn_chk PMCS.STR_TRUE GT.cp0 = true.  Proof. vmc_refl. Qed.
Lemma kn_f : kn_chk PMCS.STR_FALSE GF.cp0 = true.  Proof. vmc_refl. Qed.
Lemma heap_n : CH2.heap_chk NFV GN.HDECL GN.BLS GN.CPS GK.HULL_LO GK.HULL_HI GN.TAGS GN.RETS MALLOC FREE [] = true.  Proof. vmc_refl. Qed.
Lemma heap_t : CH2.heap_chk NFV GT.HDECL GT.BLS GT.CPS GK.HULL_LO GK.HULL_HI GT.TAGS GT.RETS MALLOC FREE [] = true.  Proof. vmc_refl. Qed.
Lemma heap_f : CH2.heap_chk NFV GF.HDECL GF.BLS GF.CPS GK.HULL_LO GK.HULL_HI GF.TAGS GF.RETS MALLOC FREE [] = true.  Proof. vmc_refl. Qed.
Lemma leaf_n : CH2.leaves_all GN.CPS GN.TAGS (leaf_c [110; 117; 108; 108]) = true.  Proof. vmc_refl. Qed.
Lemma leaf_t : CH2.leaves_all GT.CPS GT.TAGS (leaf_c [116; 114; 117; 101]) = true.  Proof. vmc_refl. Qed.
Lemma leaf_f : CH2.leaves_all GF.CPS GF.TAGS (leaf_c [102; 97; 108; 115; 101]) = true.  Proof. vmc_refl. Qed.
Lemma ng_n : CH2.leaves_all GN.CPS GN.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.
Lemma ng_t : CH2.leaves_all GT.CPS GT.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.
Lemma ng_f : CH2.leaves_all GF.CPS GF.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.

Section Lit.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Variables (lit : Z) (txt : list Z).
Hypothesis H_len : (length txt <= 22)%nat.
Hypothesis H_chars : forall c, In c txt -> 0 <= c < 256.
Variables (HDECL : CH.hdecl) (BLS : list CA.blocks) (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (RETS : list (nat * nat * nat * Z)) (cp0 : CC.cutpoint).
Hypothesis H_hd : HDECL = CH.HD SCRT 8224 [] [(e_o, 0, ELit 24)] [].
Hypothesis H_cp0 : nth_error CPS 0 = Some cp0.
Hypothesis H_pc : CC.cp_pc cp0 = PMCS.PC_CSTR_CTOR.
Hypothesis H_BL : forall i, nth i BLS [] = [].
Hypothesis H_kn : kn_chk lit cp0 = true.
Hypothesis plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound GK.RSEGS c.
Hypothesis tags_ok : CC.tags_chk CPS TAGS NFV = true.
Hypothesis heap_ok : CH2.heap_chk NFV HDECL BLS CPS GK.HULL_LO GK.HULL_HI TAGS RETS MALLOC FREE [] = true.
Hypothesis no_goto : CH2.leaves_all CPS TAGS NOGOTO = true.
Hypothesis leaf_ok : CH2.leaves_all CPS TAGS (leaf_c txt) = true.

Lemma lit_ok : forall (LB : list (Z * Z)) (cr : credit) (o sp r : Z),
  PML.cps_heap L HI PMCS.PC_CSTR_CTOR r sp (64 + PMS.OPNEW_SCR) LB cr
      (fun R M => PML.entry L R M sp r (64 + PMS.OPNEW_SCR) /\ PML.a0 R o /\ PML.a1 R lit /\ PML.img_ro M /\ PML.obj_on_stack L sp o 24 /\ L5.defined M o 24)
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\ PML.str_at_w M' o (PML.SShort txt) /\ LB' = LB /\ cr' = cr).
Proof.
  intros LB cr o sp r. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Himg & Hobj & Hdo) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hobj as (O1 & O2 & O3).
  set (n := Z.of_nat (length txt)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (HSCR : CH.hd_scr HDECL = SCRT) by (rewrite H_hd; reflexivity).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite HSCR; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr HDECL) by (rewrite HSCR; unfold SCRT; lia).
  assert (NF32 : (32 <= NFV)%nat) by (unfold NFV; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs HDECL) -> SGP.region_vars_lt NFV rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { rewrite H_hd. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ, e_o in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. rewrite <- H_pc. rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := NFV) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := HDECL)
    (W := [(o, 24)]) (BLS := BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := CPS) (TAGS := TAGS) (RETS := RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - rewrite H_hd. rewrite LSTK. reflexivity.
  - exact NF32.
  - exact U2.
  - rewrite V4, (PmLayout.ly_tp L LAY). reflexivity.
  - exact W_OK.
  - rewrite H_hd. intros rg [].
  - exact WRS_OK.
  - rewrite H_hd. intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact plans.
  - exact tags_ok.
  - exact heap_ok.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto _ _ _ _ _ IL) as X. discriminate X.
  - intros i c kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_c in X.
    change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. discriminate X.
  - intros i c kk ps pc j cj IL Hcall. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_c in X. rewrite Hcall in X. discriminate X.
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_c in X. rewrite Hnc in X. cbn [negb andb] in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) NFV E0 M model LB sp HDECL [(o, 24)] BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  CPS GK.HULL_LO GK.HULL_HI TAGS RETS MALLOC FREE [] heap_ok i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).

    apply Z.eqb_eq in X. apply Nat.leb_le in Y2.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree NFV E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y2]]).
    assert (F10 : bv_unsigned (ev E' 10) = o) by (destruct HagE' as [A _]; rewrite <- A by (unfold NFV; lia); exact U10).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold CH2.cur in HH1. rewrite (H_BL i) in HH1. cbn [CH2.den map app] in HH1.
    assert (B0 : L5.u8_at GK.RSEGS M' o (2 * n)).
    { apply (GK.kword8_elim E' M' _ _ o (2 * n) (CELL _ Y1)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | cbn [edenot]; apply u64_of_Z; lia]. }
    assert (BS : L5.bytes_at GK.RSEGS M' (o + 1) txt).
    { intros j Hj. pose proof (chars_chk_nth _ _ 1 j Y0 Hj) as Hc. pose proof (nth_In txt 0 Hj) as Hin.
      apply (GK.kword8_elim E' M' _ _ (o + 1 + Z.of_nat j) (nth j txt 0) (CELL _ Hc)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia|].
      cbn [edenot]. apply u64_of_Z. pose proof (H_chars _ Hin). lia. }
    assert (NUL : L5.u8_at GK.RSEGS M' (o + 1 + n) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y)). unfold estart, e_o. cbn [a_base a_off edenot]. rewrite F10. lia. }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED NFV y HLF Y3 HagE' Hy (csaved_lt y Hy)). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr HDECL) (CH.hd_scr HDECL)) by (rewrite HSCR; unfold SCRT; exact S5).
    pose proof (CH2.amb_hpres L HI LYI LYE NFV E0 M model LB sp HDECL [(o, 24)] BLS (fun _ _ cr' => cr' = cr) STKF NF32 i E M' m1 HA2 Hds) as HP.
    rewrite HSCR in HP; unfold SCRT in HP.
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    apply (Hcont fx' R' M' m1 LB cr LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
    split; [reflexivity|]. split; [reflexivity|]. split; [|auto]. unfold PML.str_at_w, L5.lstr_short. fold n. split; [exact H_len|]. split; [exact B0|].
    split; [exact BS | exact NUL].
  - exact H_cp0.
  -
    rewrite LS.
    apply andb_prop in H_kn as [HKN HRG]. apply exprs_eqb_eq in HRG.
    split.
    { rewrite HRG. apply (regs_ok_pin E0 sr_id R 11%bv); [exact (regs_ok_id R _ _)|]. rewrite Ha1. reflexivity. }
    assert (COM : Forall (kentry_ok GK.RSEGS E0 M) COMMON).
    { unfold COMMON, e_o, SP. repeat (apply Forall_cons); [.. | apply Forall_nil].
      + e_unk.
      + e_wr.
      + e_range.
      + e_align O3.
      + unfold SCRT. e_unk.
      + unfold SCRT. e_wr.
      + e_range.
      + e_align S1.
      + unfold SCRT. e_disj.
      + cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros a Ha. apply Himg. unfold PML.IMG_RO_HI. lia. }
    unfold know_ok. apply Forall_forall. intros K0 HK0. rewrite forallb_forall in HKN. exact (proj1 (Forall_forall _ _) COM K0 (GK.has_In _ _ (HKN K0 HK0))).
  - split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. rewrite (H_BL 0%nat). exact HH.
  - exact Hfp.
Qed.
End Lit.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Lemma chars_rng : forall (l : list Z), forallb (fun c => (Z.leb 0 c && Z.ltb c 256)%bool) l = true -> forall c, In c l -> 0 <= c < 256.
Proof. intros l H c Hc. rewrite forallb_forall in H. specialize (H c Hc). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.
Theorem cstr_ctor_ok : PMCS.cstr_ctor_spec L HI.
Proof.
  intros LB cr o src sp r txt fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Hsrc & Himg & Hobj & Hdo) Hcont.
  cbn [In] in Hsrc. destruct Hsrc as [Hs|[Hs|[Hs|[]]]]; injection Hs as <- <-.
  - exact (lit_ok L HI HIok LAY FPM PMCS.STR_NULL [110; 117; 108; 108] ltac:(cbn; lia) (chars_rng [110; 117; 108; 108] eq_refl)
             GN.HDECL GN.BLS GN.CPS GN.TAGS GN.RETS GN.cp0 eq_refl eq_refl eq_refl (fun i => ltac:(destruct i as [|[|]]; reflexivity)) kn_n GN.plans GN.tags_ok heap_n ng_n leaf_n
             LB cr o sp r fx R M model K HH Hmo HKnil Hfp (conj Hentry (conj Ha0 (conj Ha1 (conj Himg (conj Hobj Hdo))))) Hcont).
  - exact (lit_ok L HI HIok LAY FPM PMCS.STR_TRUE [116; 114; 117; 101] ltac:(cbn; lia) (chars_rng [116; 114; 117; 101] eq_refl)
             GT.HDECL GT.BLS GT.CPS GT.TAGS GT.RETS GT.cp0 eq_refl eq_refl eq_refl (fun i => ltac:(destruct i as [|[|]]; reflexivity)) kn_t GT.plans GT.tags_ok heap_t ng_t leaf_t
             LB cr o sp r fx R M model K HH Hmo HKnil Hfp (conj Hentry (conj Ha0 (conj Ha1 (conj Himg (conj Hobj Hdo))))) Hcont).
  - exact (lit_ok L HI HIok LAY FPM PMCS.STR_FALSE [102; 97; 108; 115; 101] ltac:(cbn; lia) (chars_rng [102; 97; 108; 115; 101] eq_refl)
             GF.HDECL GF.BLS GF.CPS GF.TAGS GF.RETS GF.cp0 eq_refl eq_refl eq_refl (fun i => ltac:(destruct i as [|[|]]; reflexivity)) kn_f GF.plans GF.tags_ok heap_f ng_f leaf_f
             LB cr o sp r fx R M model K HH Hmo HKnil Hfp (conj Hentry (conj Ha0 (conj Ha1 (conj Himg (conj Hobj Hdo))))) Hcont).
Qed.
End Final.
End CSTR.

