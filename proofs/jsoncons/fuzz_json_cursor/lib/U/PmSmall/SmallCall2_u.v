(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SPC2.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Section InstOwn.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBrest sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable XI : nat -> env -> mem -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).
Hypothesis HEAPCHK : CH2.heap_chk3 NF d BLS CPS TAGS = true.

Hypothesis CRED_BLK : forall i j E E2 cr, CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS []) -> Cred i E cr -> Cred j E2 cr.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Lemma wclient_not_private : forall LB a, CH2.wclient L sp0 a -> ~ alloc_private L LB a.
Proof.
  intros LB a (Ha & HW) HP. pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof LYI as [LI1 LI2]. unfold hl_ceil in *.
  destruct HP as [(P1 & P2 & P3)|P].
  - destruct HW as [HW|(I1 & I2 & I3 & I4)]; [lia | apply P3; split; assumption].
  - destruct HW as [HW|(I1 & I2 & I3 & I4)]; [destruct (LYR a P) as [Q|Q]; lia | exact (I3 P)].
Qed.
Lemma pure_leaf_own_ok : forall pc scr ng wregs news a0x (Wz : list L5.range) i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  CH2.custom_chk NF d scr ng (nth i BLS []) wregs news a0x c ps cj (nth i BLS []) = Some ci ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true ->
  (forall w a, In w Wz -> L5.in_rng w a -> (exists w', In w' W /\ L5.in_rng w' a) \/ sp0 - CH.hd_scr d <= a < sp0 \/ in_errno L a) ->
  (forall E', env_agree NF E0 E' -> forall w a, In w Wz -> L5.in_rng w a -> exists r, In r wregs /\ CH2.in_reg E' r a) ->
  (forall (fx' : FPState) E E' R' (M M' : mem) model,
      env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> regs_ok E' (CA.ps_reglist ps) R' -> HAMB i E M' model -> XI i E M ->
      PML.entry L R' M' (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) scr -> CH2.ci_csp ci <= 0 ->
      PML.fp_ok fx' -> m_halted model = None -> m_vm_lazy model = [] ->
      (forall (fx2 : FPState) R2 (M2 : mem) (ghosts : list word), length ghosts = ng -> PML.fp_ok fx2 -> regs_preserved R' R2 ->
           L5.frame_but ((sp0 + CH2.ci_csp ci - scr, scr) :: Wz) M' M2 -> mem_grows M' M2 ->
           match a0x with Some e => getr R2 10%bv = edenot (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) e | None => True end ->
           (forall X, In X news -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) M2 X) ->
           (L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBrest) (sp0 + CH2.ci_csp ci) scr Wz M' M2 -> XI j (CH2.retEx E' (CH2.ci_nx ci) ghosts R2) M2) ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model) K) ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros pc scr ng wregs news a0x Wz i c k ps j cj ci IL Hret Hcj Hpc Hchk B5 WZW WZR USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0. apply CH2.blocks_eqb_eq in B5.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              scr ng (nth i BLS []) wregs news a0x i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  set (nx := CH2.ci_nx ci) in *.
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO. pose proof LYI as [LI1 LI2].
  destruct Hmo as (Hm1 & Hm2 & Hm3).
  rewrite Hpc, LS.
  apply (USER fx' E E' R' M M' model HagE' Hag HLF ltac:(rewrite <- Hreq; exact HR) HA' HXI0); [| exact Hc1 | exact HFP | exact Hm1 | exact Hm2 |].
  { split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]. }
  intros fx2 R2 M2 ghosts Hlen HFP2 HRP HFB HGR Ha0 HNEWS HXI2.
  set (LBk := CH2.den E' (nth i BLS []) ++ LBrest).
  assert (HHk : hi_heap HI LBk cr M' (m_vmmaps model)) by (unfold LBk; rewrite Hden; exact HH).
  pose proof (proj1 (hio_wf L SCFG HI HIok _ _ _ _ HHk)) as Hwf.
  assert (OUTF : forall a, 0 <= a < 2 ^ 64 -> L5.outside Wz a -> ~ (sp0 + CH2.ci_csp ci - scr <= a < sp0 + CH2.ci_csp ci) -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha Hout Hns. apply HFB. rewrite L5.unsigned_lit by exact Ha. intros r [<-|Hr]; [unfold L5.in_rng; cbn [fst snd]; lia | exact (Hout r Hr)]. }
  assert (HPRES : L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wz M' M2).
  { apply L5C.hpres_intro.
    - intros a (K1 & K2 & K3 & K4). apply (OUTF a K1 K4). destruct K2 as [(b & Hb & Hin)|[[C1 C2]|[C1 C2]]]; [|exact C2 | unfold hl_ceil in *; lia].
      destruct (Hwf b Hb) as ((R0 & R1 & R2' & R3 & R4) & _). unfold hl_ceil in *. lia.
    - intros q Hq. apply HGR. destruct Hstk as (_ & _ & _ & _ & T5). apply T5. exact Hq.
    - intros a _ _ _ Hd. apply HGR. exact Hd. }
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model ghosts LBk Wz Hlen HFP2 (CH2.regs_preserved_kept R' R2 HRP) Ha0 HPRES).
  - intros b Hb. exact Hb.
  - exact (WZR E' HagE').
  - intros X HX _. exact (HNEWS X HX).
  - fold nx. set (E2 := CH2.retEx E' nx ghosts R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (Z3 : CH2.blocks_vars_lt nx (nth i BLS []) = true).
    { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x _ _ _ _ _ _ _ _) as [ci0|] eqn:Hc0; [|discriminate].
      lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb2; [|discriminate] end. injection Hchk as ->.
      apply andb_prop in Hb2 as [Hb2 _]. apply andb_prop in Hb2 as [Hb2 _]. apply andb_prop in Hb2 as [_ Hb2]. exact Hb2. }
    assert (Hden2 : CH2.den E2 (nth j BLS []) = CH2.den E (nth i BLS [])).
    { rewrite B5, (CH2.den_agree nx E' E2 _ Hag2 Z3). exact Hden. }
    split; [|exact (HXI2 HPRES)].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 (PB.FLOOR L NF sp0 d STK NF32) scr ng c ps cj ci i j E E' R' M' model E2 M2 model LBk Wz cr CF HPRES).
    + intros b Hb. unfold LBk. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (K1 & K2 & K3 & Hout). destruct (WZW w a Hw Hin) as [(w' & Hw' & Hin')|[Hown|Herr]]; [exact (Hout w' Hw' Hin') | | exact (K3 Herr)].
      destruct K2 as [(b & Hb & Hinb)|[[C1 C2]|[C1 C2]]]; [|exact (C2 Hown) | unfold hl_ceil in *; lia].
      destruct (Hwf b ltac:(unfold LBk; apply in_or_app; right; exact Hb)) as ((R0 & R1 & R2' & R3 & R4) & _). unfold hl_ceil in *. lia.
    + apply L5C.model_but_vm_refl.
    + unfold CH2.cur. rewrite Hden2, <- Hden. fold LBk.
      apply (hio_frame L SCFG HI HIok LBk cr M' M2 _ HHk); [|intros x Hx; apply HGR; exact Hx].
      intros a Ha Hpriv. apply (OUTF a Ha).
      * intros w Hw Hin. destruct (WZW w a Hw Hin) as [(w' & Hw' & Hin')|[Hown|Herr]]; [exact (wclient_not_private LBk a (W_ok w' a Hw' Hin') Hpriv) | |].
        -- destruct Hpriv as [(P1 & _)|P]; [unfold hl_ceil in *; lia|]. destruct (LYR a P) as [Q|Q]; unfold hl_ceil in *; lia.
        -- unfold in_errno in Herr. rewrite (PmLayout.ly_errno L LAY) in Herr. destruct Hpriv as [(_ & _ & P3)|P].
           ++ apply P3. split; [rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia].
           ++ destruct (PmLayout.ly_ro_img L LAY a P ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; lia.
      * intros Hin. destruct Hpriv as [(P1 & _)|P]; [unfold hl_ceil in *; lia|]. destruct (LYR a P) as [Q|Q]; unfold hl_ceil in *; lia.
    + exact Hag2.
    + exact (CRED_BLK i j E E2 cr Hden2 HC).
Qed.
End InstOwn.
End SPC2.
