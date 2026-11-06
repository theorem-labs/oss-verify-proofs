(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmIcptIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import CurKitCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_after_value_cboth_T Cut_after_value_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_after_value_cboth.
Module GT := Cut_after_value_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module AVA.
Definition PC_SM : Z := 413284.
Definition PC_PARENT : Z := 801208.
Definition RETPC : Z := 806944.
Definition DEADPC : Z := 806948.
Definition SBz : Z := 2147450880.
Definition IMGHI : Z := 7028736.
Definition PE := EVar 10.
Definition FR : expr * Z * Z := (EVar 37, 0, -96).
Definition FFS : list (list (expr * Z * Z)) := [[]; [FR]; [FR]].
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz); KWord (SA (ELit 0) 1432832) 4 (ELit 1)].
Definition NEWS_PAR : list kentry := STAT ++ [KRange (EVar 49) 0 255; KWord (SA (EVar 37) 56) 8 (EVar 32); KWr (SA (EVar 32) 0) (ELit 1)].
Definition sm_ok (ps : SR.post_spec) (i : nat) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok IMGHI G.HDECL (SR.ps_cells ps) 32 (nth i G.BLS []) (nth i FFS []) 0 37 32 X)%bool.
Definition kind (j : nat) : Z :=
  match find (fun r : nat * nat * nat * Z => Nat.eqb (fst (fst (fst r))) j) G.RETS with Some (_, _, _, pc) => pc | None => 0 end.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition sltu0 (c : Z) : kentry := KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EVar 49) (ELit c)) (ELit 1)) 0 0.
Definition CPF0 : list SGP.region := [(EVar 2, -1152, ELit 1152); (PE, 208, ELit 1)].
Definition CPF1 : list SGP.region := CPF0 ++ [(EVar 37, 0, ELit 24); (EVar 37, 32, ELit 24); (CHA.SRL3 (EVar 37), SBz, ELit 8)].
Definition CPF : list SGP.region := CPF1 ++ [(EVar 32, 0, ELit 1)].

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      if Z.eqb pc PC_SM then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_SM && Nat.eqb i 0 && Nat.eqb j 1 && CBA.regions_eqb (CC.cp_F c) CPF0
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth i G.BLS []) (nth i FFS []) [] (List.filter (sm_ok ps i) (CC.cp_know cj)) None c ps cj
                                             (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                     | Some ci => (Nat.eqb (CH2.ci_nx ci) 32 && Z.eqb (CH2.ci_csp ci) (-96))%bool | None => false end)%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc PC_PARENT then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_PARENT && Nat.eqb i 1 && Nat.eqb j 2 && Nat.ltb 37 (CC.cp_nx c) && CBA.regions_eqb (CC.cp_F c) CPF1
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 640 1 [] (nth i FFS []) [] NEWS_PAR (Some (EVar 49)) c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                     | Some ci => (Nat.eqb (CH2.ci_nx ci) 49 && Z.eqb (CH2.ci_csp ci) (-96))%bool | None => false end
                                  && CL.ps_reg_is ps 10 PE && has cells (KWord (SA (EVar 37) 56) 8 (EVar 32)))%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc DEADPC then
        (Nat.eqb i 2 && Nat.ltb 49 (CC.cp_nx c) && has cells (sltu0 8) && has cells (sltu0 14) && CBA.has_range cells (EVar 49) 1 255)%bool
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && Nat.eqb i 2 && Nat.ltb 49 (CC.cp_nx c)
         && match CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) with Some fle => expr_eqb fle (EVar 32) | None => false end
         && has cells (KWord (SA (EVar 32) 0) 1 (ELit 0)) && CBA.regions_eqb (CC.cp_F c) CPF
         && ((CBA.has_range cells (EVar 49) 0 0 && has cells (KWord (SA PE 208) 1 (ELit 2)))
             || ((CBA.has_range cells (EVar 49) 8 8 || CBA.has_range cells (EVar 49) 14 14) && has cells (KWord (SA PE 208) 1 (ELit 7)))))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End AVA.

Section AfterValueOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_cboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis SM0 : hl_stack_malloc L 0 = AVA.PC_SM.
Hypothesis FOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis PARENT_OK : PMSA.parent_specA L ar HI AVA.PC_PARENT.

Definition hid (P : Prop) : Prop := P.
Lemma last_cases : forall (l : list Z), l = [] \/ exists l' y, l = l' ++ [y].
Proof. intros l. destruct l as [|a l0]; [left; reflexivity|]. right. destruct (@exists_last _ (a :: l0) ltac:(discriminate)) as (l' & y & H). exists l', y. exact H. Qed.
Lemma app_last_inj : forall (l1 l2 : list Z) x y, l1 ++ [x] = l2 ++ [y] -> x = y.
Proof. intros l1 l2 x y H. apply app_inj_tail in H. exact (proj2 H). Qed.

Lemma last_stack : forall ps, PML.ps_more ps = true -> PML.ps_st ps = PML.ST_NUMBER -> PML.wf_ps_stale ps ->
  exists rest x, PML.ps_stack ps = rest ++ [x] /\ ((x = 0 /\ PML.ps_level ps = 0) \/ ((x = 8 \/ x = 14) /\ 1 <= PML.ps_level ps)) /\
  exists C0, PML.ps_stack ps = PML.ST_ROOT :: C0 /\ Forall PML.is_container C0 /\ Z.of_nat (length C0) = PML.ps_level ps.
Proof.
  intros ps Hmore Hst HWF.
  destruct HWF as (Wn & n' & W1 & W2 & W3 & W4 & (C0 & T & W5 & W6 & W7)). cbn [PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st] in *.
  destruct (W7 Hmore) as (W8 & W9 & _ & W11 & _). rewrite Hst in W11.
  assert (HT : T = []).
  { unfold PML.transient, PML.comment_or_cr, PML.ST_NUMBER, PML.ST_STRING, PML.ST_CR in W11. destruct W11 as [(HT & _)|[(_ & X)|[(S0 & _ & _ & X)|(S0 & _ & _ & X)]]]; [exact HT | lia | lia | lia]. }
  subst T. rewrite app_nil_r in W5.
  destruct (last_cases C0) as [->|(C' & y & ->)].
  - exists [], 0. split; [exact W5|]. split; [left; split; [reflexivity | cbn in W8; lia]|]. exists []. split; [exact W5|]. split; [constructor | exact W8].
  - exists (PML.ST_ROOT :: C'), y. split; [rewrite W5; reflexivity|]. split.
    + right. pose proof W6 as W6'. apply Forall_app in W6' as [_ W6']. inversion W6' as [|y' l' Hy _]; subst. unfold PML.is_container, PML.ST_OBJECT, PML.ST_ARRAY in Hy.
      split; [lia | rewrite length_app in W8; cbn [length] in W8; lia].
    + exists (C' ++ [y]). split; [exact W5|]. split; [exact W6 | exact W8].
Qed.
Theorem after_value_ok : PMSA.after_value_specA L ar HI IC 806480.
Proof.
  intros mw LBo FF LK cr A sp r P V E B kx bx g ps. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         ((Ha0 & Ha1 & Hmore & Hst & HWF1) & Hsp32 & Hstksh & HPA & HPSH & (HWF & HLVL0) & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & OP & OV & OE & AP1 & AP2 & AP3) Hcont.
  specialize (Hsp32 eq_refl). set (LB := PML.ps_blocks ps ++ LBo) in *.
  unfold PMSA.a0, PMSA.a1, PMSA.AFTERV_SCR, PMSA.SETEC_SCR, PMSA.fobj in *. change (128 + 1024) with 1152 in *.
  destruct OP as (Pfr & P8 & Psh). destruct OE as (Efr & E8 & Esh). destruct OV as (Vfr & V8 & Vsh).

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : AVA.IMGHI <= hl_img_hi L /\ hl_img_lo L < FS_BYTES) by (rewrite ILO, IHI; unfold AVA.IMGHI, FS_BYTES; lia).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF P 272 RFx Pfr ltac:(lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.infr_rng L ar LB FF E 16 RFx Efr ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (P + 272 <= 2147446784 \/ 17594333495296 <= P)) in O5. change (hid (P + 272 <= hl_img_lo L \/ hl_img_hi L <= P)) in O7.
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in Q5. change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in Q7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 P) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = P) by (rewrite V10; apply u64_of_Z; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 1152) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (WW := PMLA.W_parA IC P E).
  assert (WINC : incl [(P, 272)] WW) by (intros y [<-|[]]; left; reflexivity).
  assert (WOK : forall (w : L5.range) (a : Z), In w [(P, 272)] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ P 272 a RFx Pfr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [(P, 272)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (UP208 : CL5A.uv E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit 208)) = P + 208) by (apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia]).
  assert (SH208 : forall a, a = S (P + 208) -> in_shadow_of P 272 a).
  { intros a ->. apply (CL5A.in_shadow_mono (P + 208) 1 P 272); [clear; lia | clear; lia | clear; lia | apply CL5A.shreg1_in_shadow; reflexivity]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha; unfold CHA.sclientA.
    rewrite CL5A.estart_srl3', UP208 in Ha. unfold elenZ in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) P 272 a RFx Pfr ltac:(clear; lia) (SH208 a ltac:(unfold S, SB; clear - Ha; lia))) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[<-|[]]]; apply (L5A.aly_cells L C LAY); [left; reflexivity | right; left; reflexivity] | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (inW := fun a : Z => exists w, In w WW /\ L5.in_rng w a).
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (FOOTCL : forall a, PMLA.in_foot IC a -> 65536 <= a < 7028736 /\ forall sp' scr', aclient L ar LB FF sp' scr' a).
  { intros a Hf. assert (RG : 65536 <= a < 7028736) by (destruct Hf as (iv & Hiv & Hr); cbn in Hiv; repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]); destruct Hiv).
    split; [exact RG|]. intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - RG; lia | exact (FOOTC a Hf)]. }
  assert (WCL : forall a, inW a -> 0 <= a /\ a < ahl_ceil ar /\ (a < 2147446784 \/ 17594333495296 <= a) /\ (forall sp' scr', aclient L ar LB FF sp' scr' a)
                             /\ ((P <= a < P + 272 \/ E <= a < E + 16) \/ a < 7028736)).
  { intros a (w & Hw & Hin). unfold L5.in_rng in Hin. unfold WW, PMLA.W_parA in Hw. cbn [In] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin.
    - split; [clear - Hin O3; lia|]. split; [clear - Hin O4; lia|]. split; [unfold hid in O5; clear - Hin O5; lia|].
      split; [intros sp' scr'; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp' scr' P 272 a Pfr Hin)) | left; left; exact Hin].
    - split; [clear - Hin Q3; lia|]. split; [clear - Hin Q4; lia|]. split; [unfold hid in Q5; clear - Hin Q5; lia|].
      split; [intros sp' scr'; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF sp' scr' E 16 a Efr Hin)) | left; right; exact Hin].
    - destruct (FOOTCL a) as (RG & CLa); [exists (0x690388, 0x69038a); split; [left; reflexivity | cbn [fst snd]; cbn in Hin; clear - Hin; lia]|].
      split; [clear - RG; lia|]. split; [clear - RG CL; lia|]. split; [clear - RG; lia|]. split; [exact CLa | right; clear - RG; lia].
    - destruct (FOOTCL a) as (RG & CLa); [exists (0x6b1de0, 0x6b2000); split; [do 5 right; left; reflexivity | cbn [fst snd]; cbn in Hin; unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin; lia]|].
      split; [clear - RG; lia|]. split; [clear - RG CL; lia|]. split; [clear - RG; lia|]. split; [exact CLa | right; clear - RG; lia]. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XIW := fun (M1 : word -> option byte) => forall a, inW a -> a <> P + 208 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  set (FLF := fun (E1 : env) => ar_fs ar <= CL5A.uv E1 (EVar 32) < ar_fs ar + 11571200 /\ ~ aclient L ar LB FF sp (CH.hd_scr G.HDECL) (CL5A.uv E1 (EVar 32))).
  set (GH := fun (E1 : env) => exists rest x, PML.ps_stack ps = rest ++ [x] /\ CL5A.uv E1 (EVar 49) = x).
  set (XI := fun (i : nat) (E1 : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) => XIW M1 /\ (i = 0%nat \/ FLF E1) /\ (i = 2%nat -> GH E1)).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg IL. pose proof (CH2.leaves_all_sound _ _ _ AVA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM.
  change 806480 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P, 272)] G.BLS AVA.FFS Cred 3 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact AVA.heap_ok.
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  -
    intros i c kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ AVA.leaf_ok _ _ _ _ _ IL) as X. unfold AVA.leaf_chk in X.
    destruct (Z.eqb_spec pc AVA.PC_SM) as [->|Hne1].
    {
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
      apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply CBA.regions_eqb_eq in YF.
      lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      apply andb_prop in Y5 as [Ynx Ycsp]. apply Nat.eqb_eq in Ynx. apply Z.eqb_eq in Ycsp.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA (HXW & _ & _)].
      pose proof (CRA.smalloc_leaf L ar C HI HIok LYI LYR AVA.IMGHI LYH GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P, 272)] G.BLS AVA.FFS Cred 3 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                    G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil 0 (List.filter (AVA.sm_ok ps0 0) (CC.cp_know cj)) 0%nat c ps0 1%nat cj ci) as SML.
      rewrite (L5A.aly_scr_sm L C LAY), SM0 in SML.
      refine (SML ltac:(left; reflexivity) Hcj Hchk Y0 _ _ _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _).
      - rewrite Ynx, Ycsp. reflexivity.
      - reflexivity.
      - rewrite Ynx. exact (CL5A.forallb_filter_self (AVA.sm_ok ps0 0) _).
      - cbn [nth AVA.FFS length]. clear. lia.
      - intros Ea Eb cr1 Hc _. exact Hc.
      - intros R2 M2 m2 F fl LK' cr1 HRP Ha0' SMF HH2. unfold CHA.curB, CHA.curF in SMF. cbn [nth G.BLS AVA.FFS CH2.den CHA.denF map app] in SMF. change (CH2.den E1 Cut_after_value_cboth_T.BL0) with (@nil (Z * Z)) in SMF. cbn [app] in SMF.
        destruct SMF as [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Zp]. rewrite Ynx.
        assert (Hc0 : nth_error G.CPS 0 = Some c) by (destruct IL as (tg & Hc0 & _); exact Hc0).
        pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS AVA.FFS Cred 3 0%nat c E1 E' A1 M1 m1 HA (G.NF_le 0%nat c Hc0) Hag) as HagE'.
        assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
        assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
        unfold XI. split; [|split; [right | intros X2; discriminate X2]].
        + intros a Ha Hne. destruct (WCL a Ha) as (C0 & C1 & C2 & C3 & _).
          rewrite (proj1 Zp a ltac:(clear - C0 C1 CL SP1; lia) (C3 _ _)). rewrite <- (HXW a Ha Hne).
          apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside. rewrite L5.unsigned_lit by (clear - C0 C1 CL SP1; lia).
          constructor; [|constructor; [|constructor]]; unfold estart, elenZ, AVA.PE; cbn [a_base a_off edenot fst snd]; rewrite ?W2, ?W10; rewrite u64_of_Z by (clear; lia); clear - C1 S2 Hne; lia.
        + pose proof (CH2.retEx_ghost E' 32 [Z_to_bv 64 fl] R2 0 ltac:(cbn; clear; lia)) as G32. cbn [nth Nat.add] in G32.
          assert (T32 : CL5A.uv (CH2.retEx E' 32 [Z_to_bv 64 fl] R2) (EVar 32) = fl).
          { unfold CL5A.uv. cbn [edenot]. rewrite G32. apply u64_of_Z. unfold FS_BYTES in Z7. destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _). unfold FS_BYTES in G3. clear - Z7 G0 G3 CL SP1. lia. }
          unfold FLF. rewrite T32. split; [unfold FS_BYTES in Z7; exact Z7|]. intros Hc. apply Z8.
          eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact Hc] | intros y Hy; clear - Hy; lia]. }

    assert (FRM : forall E1 A1 M1 m1, (i = 1%nat \/ i = 2%nat) ->
              CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS AVA.FFS Cred 3 i E1 A1 M1 m1 ->
              let F := CL5A.uv E1 (EVar 37) in
              CHA.curB LB G.BLS i E1 = LB /\ CHA.curF FF sp AVA.FFS i E1 = (F, 0, sp + -96 + 32) :: FF /\ env_agree GT.NF E0 E1 /\
              0 <= F /\ F + 64 <= 140737488355328 /\ F mod 8 = 0 /\ (F + 64 <= 2147446784 \/ 17594333495296 <= F) /\ ar_fs ar <= F /\ F + 64 <= ar_fs ar + 11571200 /\ fframes_apart F 64 FF).
    { intros E1 A1 M1 m1 Hi HA. cbv zeta.
      assert (HcB : CHA.curB LB G.BLS i E1 = LB) by (destruct Hi as [-> | ->]; reflexivity).
      assert (HcF : CHA.curF FF sp AVA.FFS i E1 = (CL5A.uv E1 (EVar 37), 0, sp + -96 + 32) :: FF) by (destruct Hi as [-> | ->]; reflexivity).
      pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _) & _). rewrite HcB, HcF in HHa.
      pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHa) as WFa. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFa) as RFa.
      destruct (CHA.rf_frm _ _ _ _ RFa _ (or_introl eq_refl)) as (G1 & G2 & G3 & _). unfold ff_addr, ff_class in G1, G2, G3. cbn [fst snd] in G1, G2, G3. change (ff_bytes 0) with 64 in G2.
      destruct (CHA.rf_fs _ _ _ _ RFa) as ((G0 & G4 & G5) & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
      destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WFa _ (or_introl eq_refl)) as (_ & _ & _ & _ & _ & FAP). cbn [ff_addr ff_class fst snd ff_remove] in FAP. rewrite Z.eqb_refl in FAP. change (ff_bytes 0) with 64 in FAP.
      split; [exact HcB|]. split; [exact HcF|]. split; [exact HagE|]. split; [clear - G0 G1; lia|]. split; [clear - G2 G5; lia|]. split; [exact (CHA.mod8_of_64 _ G3)|].
      split; [clear - G1 G2 G4; lia|]. split; [exact G1|]. split; [exact G2|]. intros f Hf. apply FAP. apply in_or_app. left. exact Hf. }

    assert (WFR : forall a F, inW a -> ar_fs ar <= F -> fframes_apart F 64 FF -> ~ (F <= a < F + 64)).
    { intros a F Ha HF0 FAP Hin. destruct (WCL a Ha) as (_ & _ & _ & _ & [[Hp|He]|Himg]).
      - destruct Pfr as (f & Hf & F1 & F2). specialize (FAP f Hf). clear - FAP Hp Hin F1 F2. lia.
      - destruct Efr as (f & Hf & F1 & F2). specialize (FAP f Hf). clear - FAP He Hin F1 F2. lia.
      - clear - Himg Hin HF0 FSLO. lia. }

    pose proof HPA as HPA0. unfold PMLA.parser_at in HPA0. cbn [PML.ps_set_win PML.ps_sb PML.ps_stack PML.ps_scap] in HPA0.
    destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A25 & A26 & A27 & A28 & A29 & _).
    destruct (last_stack (PMCUR.ps_set_more ps true) eq_refl Hst (proj1 HWF1)) as (rest & x & Hstk & Hx & (C0 & HSC & HCC & HCL)).
    cbn [PMCUR.ps_set_more PML.ps_stack PML.ps_level] in Hstk, Hx, HSC, HCL.
    set (sb := PML.ps_sb ps) in *. set (scap := PML.ps_scap ps) in *. set (slen := Z.of_nat (length (PML.ps_stack ps))) in *.
    assert (SLEN : 0 <= slen <= scap) by (split; [unfold slen; apply Nat2Z.is_nonneg | exact A29]).
    assert (HinSB : In (sb, scap) LB) by (unfold LB, PML.ps_blocks; right; left; reflexivity).
    destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (sb, scap) HinSB) as ((B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)) & Bdef & _ & _ & Bfap). cbn [fst snd] in B0, B1, B16, B3, B4, B5, B6, B7, Bdef, Bfap.
    assert (SCAP : 0 < scap <= 4096) by (destruct HWF as (_ & n' & _ & _ & _ & W4 & _); cbn [PML.ps_set_nst PML.ps_scap] in W4; fold scap in W4; cbn [In] in W4; clear - W4; lia).

    assert (KSHP : forall a, in_shadow_of P 272 a -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
    { intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) P 272 a RFx Pfr ltac:(clear; lia) Ha) as (G1 & G2 & _). pose proof (SHR P 272 a O3 ltac:(clear; lia) O6 Ha) as SRa.
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & C2 & _). clear - C2 SRa. lia. }
    assert (KSB : forall a, sb <= a < sb + scap \/ in_shadow_of sb scap a -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
    { intros a Ha. assert (AR : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [clear - Ha B0 B7; lia | pose proof (SHR sb scap a ltac:(clear - B0; lia) B3 B7 Ha); lia]).
      split; [exact AR|]. split; [destruct Ha as [Ha|Ha]; [left; exists (sb, scap); split; [exact HinSB | exact Ha] | do 6 right; exists (sb, scap); split; [exact HinSB | exact Ha]]|].
      intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & C2 & _ & C4). destruct Ha as [Ha|Ha]; [|pose proof (SHR sb scap a ltac:(clear - B0; lia) B3 B7 Ha); clear - C2 H; lia].
      destruct C4 as [[Hp|He]|Himg].
      - destruct Pfr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. clear - QF Hp Ha F1 F2. lia.
      - destruct Efr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. clear - QF He Ha F1 F2. lia.
      - rewrite ILO, IHI in B1. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (C0' & _). unfold WW, PMLA.W_parA in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
        destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [destruct Pfr as (f & Hf & F1 & F2); pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))); clear - H Hin Ha F1 F2; lia
          | destruct Efr as (f & Hf & F1 & F2); pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))); clear - H Hin Ha F1 F2; lia | cbn in Hin; clear - Hin Ha B1; lia | cbn in Hin; unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin Ha B1; lia]. }

    assert (KLB : forall u n a, In (u, n) LB -> u <= a < u + n \/ in_shadow_of u n a -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
    { intros u n a Hun Ha.
      destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (u, n) Hun) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & Ddef & _ & _ & Dfap). cbn [fst snd] in D0, D1, D16, D3, D4, D5, D6, D7, Ddef, Dfap.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [clear - Ha D0 D7; lia | pose proof (SHR u n a ltac:(clear - D0; lia) D3 D7 Ha); lia]).
      split; [exact AR|]. split; [destruct Ha as [Ha|Ha]; [left; exists (u, n); split; [exact Hun | exact Ha] | do 6 right; exists (u, n); split; [exact Hun | exact Ha]]|].
      intros w Hw Hin. destruct (WCL a (ex_intro _ w (conj Hw Hin))) as (_ & _ & C2 & _ & C4). destruct Ha as [Ha|Ha]; [|pose proof (SHR u n a ltac:(clear - D0; lia) D3 D7 Ha); clear - C2 H; lia].
      rewrite ILO, IHI in D1. unfold WW, PMLA.W_parA in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
      destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [destruct Pfr as (f & Hf & F1 & F2); pose proof (Dfap f (in_or_app _ _ _ (or_introl Hf))); clear - H Hin Ha F1 F2; lia
        | destruct Efr as (f & Hf & F1 & F2); pose proof (Dfap f (in_or_app _ _ _ (or_introl Hf))); clear - H Hin Ha F1 F2; lia | cbn in Hin; clear - Hin Ha D0 D1; lia | cbn in Hin; unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin Ha D0 D1; lia]. }

    assert (DECW : forall a, a < 7028736 -> inW a \/ L5.outside WW a).
    { intros a Ha. destruct (Z_le_dec 0x690388 a) as [G1|G1]; [destruct (Z_lt_dec a 0x69038a) as [G2|G2]|].
      - left. exists (PMLA.ERRCAT_GUARD IC, 2). split; [right; right; left; reflexivity | unfold L5.in_rng; cbn; clear - G1 G2; lia].
      - destruct (Z_le_dec 0x6b1de0 a) as [G3|G3]; [destruct (Z_lt_dec a 0x6b2000) as [G4|G4]|].
        + left. exists (PMLA.ATEXIT_TAB IC, PmIcptIfaceA.ATEXIT_TAB_BYTES). split; [do 3 right; left; reflexivity | unfold L5.in_rng, PmIcptIfaceA.ATEXIT_TAB_BYTES; cbn; clear - G3 G4; lia].
        + right. intros w Hw Hin. unfold WW, PMLA.W_parA in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
          destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G2; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G4; lia].
        + right. intros w Hw Hin. unfold WW, PMLA.W_parA in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
          destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G2; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G3; lia].
      - right. intros w Hw Hin. unfold WW, PMLA.W_parA in Hw. cbn [In] in Hw. unfold L5.in_rng in Hin.
        destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hin; [clear - Hin Ha O1 FSLO; lia | clear - Hin Ha Q1 FSLO; lia | clear - Hin G1; lia | unfold PmIcptIfaceA.ATEXIT_TAB_BYTES in Hin; clear - Hin G1; lia]. }
    assert (PTKF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
                     \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
                     \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a).
    { intros a Ha. pose proof PMTA.C_cboth_wf as [T1 T2 T3 _ T5 T6 T7 T8 _ _ T9]. unfold PMTA.cell_in_foot, PmIcptIfaceA.ATEXIT_TAB_BYTES in *.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]];
        [apply (proj2 (proj2 T5)); exact Ha | apply (proj2 (proj2 T6)); exact Ha | apply (proj2 (proj2 T7)); exact Ha | apply (proj2 (proj2 T8)); exact Ha
        | apply (proj2 (proj2 T1)); exact Ha | subst a; apply (proj2 (proj2 T2)); clear; lia | apply (proj2 (proj2 T3)); exact Ha | apply (proj2 (proj2 T9)); exact Ha]. }
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P, 272)] G.BLS AVA.FFS Cred 3 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    destruct (Z.eqb_spec pc AVA.PC_PARENT) as [->|Hne2].
    {
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y7]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y3].
      apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply Nat.ltb_lt in Y3. apply CBA.regions_eqb_eq in YF.
      lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      apply andb_prop in Y5 as [Ynx Ycsp]. apply Nat.eqb_eq in Ynx. apply Z.eqb_eq in Ycsp.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA (HXW & HXF & _)]. destruct HXF as [HXF|HFL]; [discriminate HXF|].
      destruct (FRM E1 A1 M1 m1 (or_introl eq_refl) HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP). set (F := CL5A.uv E1 (EVar 37)) in *.
      destruct HFL as (HFL1 & HFL2). set (fl := CL5A.uv E1 (EVar 32)) in *.
      refine (CALLEE AVA.PC_PARENT 640 1%nat [] [] AVA.NEWS_PAR (Some (EVar 49)) 2 1%nat c ps0 2%nat cj ci Hcj Hchk Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [reflexivity | cbn [nth AVA.FFS length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
      assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
      assert (W37 : bv_unsigned (ev E' 37) = F) by (rewrite <- (proj1 Hag 37%nat) by exact Y3; reflexivity).
      assert (W32 : bv_unsigned (ev E' 32) = fl) by (rewrite <- (proj1 Hag 32%nat) by (clear - Y3; lia); reflexivity).
      assert (CELL : forall X0, AVA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS AVA.FFS Cred 3 1%nat E1 A1 M' m' HA') as Hoff.
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).

      assert (AGW : forall a, inW a -> a <> P + 208 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hne. destruct (WCL a Ha) as (C0' & C1 & C2 & C3 & _). rewrite <- (HXW a Ha Hne).
        apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside. rewrite L5.unsigned_lit by (clear - C0' C1 CL SP1; lia).
        pose proof (WFR a F Ha F3 FAP) as NF0.
        pose proof (Z.div_pos F 8 F0 ltac:(clear; lia)) as D0. assert (D1 : F / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; clear - F1; lia).
        unfold AVA.CPF1, AVA.CPF0. cbn [app]. repeat (apply Forall_cons); [.. | apply Forall_nil];
          unfold AVA.PE, AVA.SBz; cbn [fst snd]; rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; rewrite ?W2, ?W10, ?W37;
          rewrite u64_of_Z by (clear; lia); clear - C1 C2 S2 Hne NF0 D0 D1; lia. }
      eexists. eexists. split; [exact (PARENT_OK LB ((F, 0, sp + -96 + 32) :: FF) LK1 cr A1 P sb scap x (sp + CH2.ci_csp ci) (CC.cp_pc cj) rest)|]. split.
      {
        unfold PMSA.a0, PMSA.vec_ok, PMSA.vec_at, PMSA.u64, PMSA.ainfr.
        split; [replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
                rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y7); unfold AVA.PE; cbn [edenot];
                rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact V10|].
        split; [rewrite Ycsp; clear - Hsp32; pose proof (Z_div_mod_eq_full sp 32); rewrite Hsp32 in H; replace (sp + -96) with ((sp / 32 - 3) * 32) by lia; apply Z_mod_mult|].
        assert (LENEQ : Z.of_nat (length rest) + 1 = slen) by (unfold slen; rewrite Hstk, length_app; cbn [length]; clear; lia).
        assert (INP : forall k n, 0 <= k -> 0 < n -> k + n <= 272 -> forall y, P + k <= y < P + k + n -> inW y).
        { intros k n K0 K1 K2 y Hy. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - K0 K2 Hy; lia]. }
        split.
        { rewrite LENEQ. split.
          - split; [|split]; [apply (CL5A.u64_same (hl_segs L) M M' (P + 248) sb) | apply (CL5A.u64_same (hl_segs L) M M' (P + 248 + 8) (sb + slen)) | apply (CL5A.u64_same (hl_segs L) M M' (P + 248 + 16) (sb + scap))];
              try (clear - O3 O6; lia); try (intros y Hy; apply AGW; [apply (INP 248 24); [clear; lia | clear; lia | clear; lia | clear - Hy; lia] | clear - Hy; lia]).
            + exact A25.
            + replace (P + 248 + 8) with (P + 256) by (clear; lia). exact A26.
            + replace (P + 248 + 16) with (P + 264) by (clear; lia). exact A27.
          - split; [destruct Pfr as (f & Hf & G1 & G2); exists f; split; [right; exact Hf | clear - G1 G2; lia]|].
            split; [clear - P8; pose proof (Z_div_mod_eq_full P 8); rewrite P8 in H; replace (P + 248) with ((P / 8 + 31) * 8) by lia; apply Z_mod_mult|].
            split.
            { intros jj Hj. unfold byte_at. rewrite (CL5A.S_add_al P 248 P8). change (248 / 8) with 31.
              replace (S P + 31 + jj) with (S P + (31 + jj)) by (clear; lia). rewrite Hfr1; [exact (Psh (31 + jj) ltac:(clear - Hj; lia)) | apply KSHP].
              apply (CL5A.shreg_in_shadow P 34); [exact P8 | clear; lia | unfold S; clear - Hj; lia]. }
            split; [exact HinSB|]. split; [exact SLEN|]. split; [exact SCAP|].
            apply (CL5A.shadow_cont_same M M' sb scap slen SLEN (CHA.mod8_of_16 _ B16)); [|exact (proj2 HPSH)].
            intros a Ha. apply Hfr1. apply KSB. right. exact Ha. }
        split.
        { rewrite <- Hstk. apply (CL5A.bytes_same (hl_segs L) M M' sb (PML.ps_stack ps)); [clear - B0; lia | fold slen; clear - SLEN B7; lia | | exact A28].
          intros y Hy. apply Hfr1. apply KSB. left. fold slen in Hy. clear - Hy SLEN. lia. }
        clear - Hx. lia. }
      {
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        assert (XR : 0 <= x < 256) by (clear - Hx; lia).
        exists [Z_to_bv 64 x]. split; [reflexivity|]. cbv zeta. rewrite Ynx.
        pose proof (CH2.retEx_agree E' 49 [Z_to_bv 64 x] R2 : env_agree 49 E' (CH2.retEx E' 49 [Z_to_bv 64 x] R2)) as Hag2.
        pose proof (CH2.retEx_ghost E' 49 [Z_to_bv 64 x] R2 0 ltac:(cbn; clear; lia)) as T49. cbn [nth Nat.add] in T49.
        set (E2 := CH2.retEx E' 49 [Z_to_bv 64 x] R2) in *.
        assert (T37 : bv_unsigned (ev E2 37) = F) by (rewrite <- (proj1 Hag2 37%nat) by (clear; lia); exact W37).
        assert (T32 : CL5A.uv E2 (EVar 32) = fl) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 32%nat) by (clear; lia); exact W32).
        split; [unfold PMSA.a0 in Ha0'; cbn [edenot]; rewrite T49; exact Ha0'|].
        split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
        split; [exact HH2|]. split; [reflexivity|].
        split.
        { unfold XI. split; [|split; [right | intros _]].
          - intros a Ha Hne. destruct (WCL a Ha) as (C0' & C1 & C2 & C3 & _). rewrite <- (AGW a Ha Hne). apply (proj1 HP). split; [clear - C0' C1 CL SP1; lia|]. split; [|intros w []].
            eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact (C3 _ _)].
          - unfold FLF. rewrite T32. split; [exact HFL1 | exact HFL2].
          - exists rest, x. split; [exact Hstk|]. unfold CL5A.uv. cbn [edenot]. rewrite T49. apply u64_of_Z. clear - XR. lia. }
        intros X0 HX0 _. unfold AVA.NEWS_PAR, AVA.STAT in HX0. cbn [app In] in HX0.
        pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) as WF2.
        assert (VFS : forall y, ar_fs ar <= y < ar_fs ar + 11571200 -> ahid A2 m2 (Z_to_bv 64 y) = false).
        { intros y Hy. apply (CHA.fs_vis L ar C HI HIok GT.NF 0 NF32 _ _ _ _ _ _ m2 y HH2); [destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _); unfold FS_BYTES in G3; clear - Hy G0 G3 CL SP1; lia | unfold FS_BYTES; exact Hy]. }
        destruct HX0 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
        - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
        - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
        - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
        - cbn [kentry_ok edenot]. rewrite T49. rewrite u64_of_Z by (clear - XR; lia). clear - XR. lia.
        -
          pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (F + 56) (CELL _ Y8) ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite W37; reflexivity)) as G0.
          apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0.
          assert (G32 : CL5A.uv E' (EVar 32) = fl) by (unfold CL5A.uv; cbn [edenot]; exact W32). rewrite G32 in G0.
          pose proof (PmHeapIfaceA.aio_flagptr _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0 (sp + -96 + 32) (sp + -96 + 32) fl HH1 HH2 (or_introl eq_refl) (or_introl eq_refl)) as FP.
          change (ff_bytes 0) with 64 in FP. replace (F + 64 - 8) with (F + 56) in FP by (clear; lia). specialize (FP G0).
          eapply CL5.kword64_intro with (A := F + 56) (z := fl); [unfold estart; cbn [a_base a_off edenot]; rewrite T37; reflexivity | clear - F0; lia | clear - F1; lia | |].
          + cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned _ (ev E2 32)). f_equal. exact T32.
          + apply (CL5A.u64_vis (hl_segs L)); [clear - F0; lia | clear - F1; lia | | exact FP]. intros y Hy. apply VFS. clear - Hy F3 F4. lia.
        - eapply CL5.kwr_intro with (A := fl) (N := 1); [unfold estart; cbn [a_base a_off edenot]; unfold CL5A.uv in T32; cbn [edenot] in T32; rewrite T32; clear; lia | reflexivity | | | |].
          + destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & _). clear - HFL1 G0. lia.
          + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
          + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
          + intros y Hy. unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ (VFS (fl + y) ltac:(clear - Hy HFL1; lia))).
            pose proof (CHA.wf_fs_def _ _ _ _ _ _ _ _ WF2) as FD. replace (fl + y) with (ar_fs ar + (fl + y - ar_fs ar)) by (clear; lia). apply FD. unfold FS_BYTES. clear - Hy HFL1. lia. } }
    destruct (Z.eqb_spec pc AVA.DEADPC) as [->|Hne3].
    {
      apply andb_prop in X as [X Yr]. apply andb_prop in X as [X Y14]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [Y2 Y3].
      apply Nat.eqb_eq in Y2. subst i. apply Nat.ltb_lt in Y3.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. exfalso. pose proof HAX as [HA (_ & _ & HGH)].
      destruct (HGH eq_refl) as (rest' & x' & Hstk' & Hx').
      assert (Hxx : x = x') by (rewrite Hstk in Hstk'; exact (app_last_inj _ _ _ _ Hstk')).
      assert (CELL : forall X0, AVA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
        by (intros X0 HX0; apply CC.has_cell_In in HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)).
      assert (U49 : CL5A.uv E' (EVar 49) = x) by (rewrite (CL5A.uv_agree _ E1 E' (EVar 49) Hag); [rewrite Hxx; exact Hx' | cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; exact Y3]).
      pose proof (CELL _ Y8) as K8. pose proof (CELL _ Y14) as K14. cbn [kentry_ok AVA.sltu0] in K8, K14.
      pose proof (PTA.sltu_sub_ne E' (EVar 49) 8 ltac:(unfold CL5A.uv; clear - K8; lia) ltac:(clear; lia)) as N8.
      pose proof (PTA.sltu_sub_ne E' (EVar 49) 14 ltac:(unfold CL5A.uv; clear - K14; lia) ltac:(clear; lia)) as N14.
      pose proof (CBA.has_range_sound (hl_segs L) E' _ _ _ _ _ (fun X0 HX0 => CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0) Yr) as KR.
      rewrite U49 in N8, N14. unfold CL5A.uv in U49. cbn [edenot] in U49, KR. rewrite U49 in KR. clear - Hx N8 N14 KR. lia. }

    apply andb_prop in X as [X Ycase]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Yfl]. apply andb_prop in X as [X Yr]. apply andb_prop in X as [X Y3].
    apply andb_prop in X as [Xbase Y2]. apply Nat.eqb_eq in Y2. subst i. apply Nat.ltb_lt in Y3. apply CBA.regions_eqb_eq in YF.
    destruct (CHA.retire_chk GT.NF G.HDECL c (nth 2 G.BLS []) (nth 2 AVA.FFS [])) as [fle|] eqn:Hrc; [|discriminate]. apply expr_eqb_eq in Yr. subst fle.
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA (HXW & HXF & HGH)].
    destruct HXF as [HXF|(HFL1 & HFL2)]; [discriminate HXF|].
    destruct (FRM E1 A1 M1 m1 (or_intror eq_refl) HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP). set (F := CL5A.uv E1 (EVar 37)) in *.
    set (fl := CL5A.uv E1 (EVar 32)) in *.
    refine (CRA.exit_retire L ar C HI HIok LYI LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [(P, 272)] G.BLS AVA.FFS Cred 3 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok AVA.RETPC 2%nat c ps0 (EVar 32) (EVar 37) 0 (-96) _ Xbase eq_refl Hrc Yfl fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF HFL1 HFL2 _);
      [rewrite LS; exact AVA.ret_at |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE'. rewrite HcB in HH1. assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (FZ : forall n, (n <? 32)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply (Nat.lt_le_trans _ 32); [apply Nat.ltb_lt; exact Hn | exact NF32]).
    assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite (FZ 2%nat eq_refl); exact U2).
    assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite (FZ 10%nat eq_refl); exact U10).
    assert (W37 : bv_unsigned (ev E' 37) = F) by (rewrite <- (proj1 Hag 37%nat) by (clear - Y3; lia); reflexivity).
    assert (W32 : bv_unsigned (ev E' 32) = fl) by (rewrite <- (proj1 Hag 32%nat) by (clear - Y3; lia); reflexivity).
    assert (U49 : bv_unsigned (ev E' 49) = x).
    { destruct (HGH eq_refl) as (rest' & x' & Hstk' & Hx'). assert (Hxx : x = x') by (rewrite Hstk in Hstk'; exact (app_last_inj _ _ _ _ Hstk')).
      rewrite Hxx, <- Hx'. exact (CL5A.uv_agree _ E1 E' (EVar 49) Hag ltac:(cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; exact Y3)). }
    assert (CELL : forall X0, AVA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
      by (intros X0 HX0; apply CC.has_cell_In in HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)).
    assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')).
    { rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)). exact (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS AVA.FFS Cred 3 2%nat E1 A1 M1 m1 HA). }

    assert (CASE : exists stz, L5.u8_at (hl_segs L) M' (P + 208) stz /\ ((stz = 2 /\ x = 0) \/ (stz = 7 /\ (x = 8 \/ x = 14)))).
    { assert (RD : forall v, AVA.has (SR.ps_cells ps0) (KWord (SA AVA.PE 208) 1 (ELit v)) = true -> 0 <= v < 2 ^ 64 -> L5.u8_at (hl_segs L) M' (P + 208) v).
      { intros v Hv Hv'. pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (P + 208) (CELL _ Hv) ltac:(unfold estart, AVA.PE; cbn [a_base a_off edenot]; rewrite W10; reflexivity)) as G0.
        apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear - Hv'; lia). exact G0. }
      pose proof (fun e lo hi => CBA.has_range_sound (hl_segs L) E' _ (SR.ps_cells ps0) e lo hi (fun X0 HX0 => CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)) as HRS.
      apply orb_prop in Ycase. destruct Ycase as [Yc|Yc]; apply andb_prop in Yc as [Yg Yb].
      - exists 2. split; [apply (RD 2 Yb); clear; lia | left]. split; [reflexivity|]. pose proof (HRS _ _ _ Yg) as KR. cbn [edenot] in KR. rewrite U49 in KR. clear - KR. lia.
      - exists 7. split; [apply (RD 7 Yb); clear; lia | right]. split; [reflexivity|].
        apply orb_prop in Yg. destruct Yg as [Yg|Yg]; pose proof (HRS _ _ _ Yg) as KR; cbn [edenot] in KR; rewrite U49 in KR; clear - KR; lia. }
    destruct CASE as (stz & HST & Hsx).

    assert (AGW : forall a, inW a -> a <> P + 208 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hne. destruct (WCL a Ha) as (C0' & C1 & C2 & C3 & _). rewrite <- (HXW a Ha Hne).
      apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside. rewrite L5.unsigned_lit by (clear - C0' C1 CL SP1; lia).
      pose proof (WFR a F Ha F3 FAP) as NF0.
      pose proof (Z.div_pos F 8 F0 ltac:(clear; lia)) as D0. assert (D1 : F / 8 <= 2 ^ 44 - 8) by (apply Z.div_le_upper_bound; clear - F1; lia).
      assert (NFL : a <> fl) by (intros Heq; apply HFL2; rewrite <- Heq; exact (C3 _ _)).
      unfold AVA.CPF, AVA.CPF1, AVA.CPF0. cbn [app]. repeat (apply Forall_cons); [.. | apply Forall_nil];
        unfold AVA.PE, AVA.SBz; cbn [fst snd]; rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; rewrite ?W2, ?W10, ?W37, ?W32;
        rewrite u64_of_Z by (clear; lia); clear - C1 C2 S2 Hne NF0 D0 D1 NFL; lia. }
    pose proof HP as (HP1 & HP2 & HP3).
    set (Sg := fun a => CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a \/ (inW a /\ a <> P + 208)).
    assert (AG : forall a, Sg a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a [Ha|(Ha & Hne)]; [exact (HP1 a Ha) | exact (AGW a Ha Hne)]).
    assert (INWP : forall y, P <= y < P + 272 -> inW y) by (intros y Hy; exists (P, 272); split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Hy; lia]).
    assert (INWE : forall y, E <= y < E + 16 -> inW y) by (intros y Hy; exists (E, 16); split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Hy; lia]).
    assert (OUTP : forall k n, 0 <= k -> k + n <= 272 -> (k + n <= 208 \/ 209 <= k) -> PTA.out Sg (P + k) n).
    { intros k n K0 K1 K2. split; [clear - K0 O3; lia|]. split; [clear - K1 O6; lia|]. intros y Hy. right. split; [apply INWP; clear - Hy K0 K1; lia | clear - Hy K2; lia]. }
    assert (OUTE : PTA.out Sg E 16).
    { split; [clear - Q3; lia|]. split; [clear - Q6; lia|]. intros y Hy. right. split; [apply INWE; exact Hy | unfold PMLA.apart in AP2; clear - Hy AP2; lia]. }
    assert (INB : In (PML.ps_bptr ps, PML.ps_bcap ps) LB) by (unfold LB, PML.ps_blocks; left; reflexivity).
    assert (OUTB : forall u n, In (u, n) LB -> PTA.out Sg u n /\ (forall a, in_shadow_of u n a -> Sg a) /\ u mod 8 = 0 /\ 0 < n).
    { intros u n Hun. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (u, n) Hun) as ((D0 & _ & D16 & D3 & D4 & (_ & _ & D7)) & _). cbn [fst snd] in D0, D16, D3, D4, D7.
      split; [|split; [intros a Ha; left; exact (KLB u n a Hun (or_intror Ha)) | split; [exact (CHA.mod8_of_16 _ D16) | exact D3]]].
      split; [clear - D0; lia|]. split; [clear - D7; lia|]. intros y Hy. left. exact (KLB u n y Hun (or_introl Hy)). }

    set (ps' := PML.PS stz (PML.ps_sst ps) (PML.ps_nst ps) (PML.ps_more ps) (PML.ps_done ps) (PML.ps_level ps) (PML.ps_stack ps) sb scap
                       (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps) (PML.ps_win ps)).

    assert (AHM : CHA.ahpres L ar LB FF sp (CH.hd_scr G.HDECL) WW M M') by exact HP.
    rewrite SCRV in AHM.
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact AHM | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    exists ps', 0, g.
    assert (HPA' : PMLA.parser_at (hl_segs L) IC M' P (PML.ps_set_win ps' mw)).
    { unfold ps', PML.ps_set_win. cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win].
      pose proof (PTA.parser_at_st (hl_segs L) IC M M' Sg AG P (PML.ps_set_win ps mw) stz) as T. unfold PML.ps_set_win in T.
      cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win] in T.
      fold sb scap in T. apply T; [exact OUTP | exact (proj1 (OUTB _ _ INB)) | exact (proj1 (OUTB _ _ HinSB)) | exact HPA | exact HST |].
      apply (HP3 (P + 208)); [clear - O3 O6; lia | destruct (WCL (P + 208) (INWP (P + 208) ltac:(clear; lia))) as (_ & _ & _ & C3 & _); exact (C3 _ _) |].
      pose proof HPA as HPA0. unfold PMLA.parser_at in HPA0. destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HdefP).
      exact (HdefP 208 ltac:(clear; lia)). }
    split; [split; [exact HPA' | reflexivity]|].
    split.
    {   unfold PMSA.parser_sh. apply (PTA.parser_sh_ag M M' Sg AG ps'); unfold ps'; cbn [PML.ps_bcap PML.ps_stack PML.ps_scap PML.ps_bptr PML.ps_sb].
      - destruct (OUTB _ _ INB) as (_ & _ & _ & D3). clear - D3. lia.
      - exact SLEN.
      - exact (proj1 (proj2 (proj2 (OUTB _ _ INB)))).
      - exact (CHA.mod8_of_16 _ B16).
      - exact (proj1 (proj2 (OUTB _ _ INB))).
      - exact (proj1 (proj2 (OUTB _ _ HinSB))).
      - exact HPSH. }
    assert (WT : PML.wf_ps (PMCUR.ps_set_more ps' true)).
    {
      destruct (proj1 HWF1) as (Wn & n' & Vw1 & Vw2 & Vw3 & Vw4 & (Cx & Tx & Vw5 & Vw6 & Vw7)). cbn [PMCUR.ps_set_more PML.ps_set_nst PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level] in Wn, Vw1, Vw2, Vw3, Vw4, Vw7.
      destruct (Vw7 eq_refl) as (_ & Vw9 & _).
      unfold PML.wf_ps, ps'. cbn [PMCUR.ps_set_more PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
      split; [exact Vw1|]. split; [exact Wn|]. split; [exact Vw3|]. split; [exact Vw4|]. exists C0, []. rewrite app_nil_r. split; [exact HSC|]. split; [exact HCC|]. intros _.
      split; [exact HCL|]. split; [exact Vw9|].
      unfold PML.handled, PML.transient, PML.comment_or_cr, PML.ST_EXPECT_COMMA_OR_END, PML.ST_NUMBER, PML.ST_CR.
      split; [destruct Hsx as [(-> & _)|(-> & _)]; clear; lia|]. split; [left; split; [reflexivity | destruct Hsx as [(-> & _)|(-> & _)]; clear; lia]|].
      split; [intros [Hq|[]]; destruct Hsx as [(-> & ->)|(-> & Hx8)]; [discriminate Hq | destruct Hx as [(Hq0 & _)|(_ & Hq1)]; [clear - Hx8 Hq0; lia | exact Hq1]]|].
      intros Hq. destruct Hsx as [(-> & _)|(-> & _)]; discriminate Hq. }
    assert (LT : PMCUR.lvl_ok (PMCUR.ps_set_more ps' true)).
    { apply (CKA.lvl_ok_rootc _ C0); [unfold ps'; cbn [PMCUR.ps_set_more PML.ps_stack]; exact HSC | exact HCC |]. intros Hin _. unfold ps' in Hin |- *. cbn [PMCUR.ps_set_more PML.ps_st PML.ps_level] in Hin |- *.
      destruct Hsx as [(-> & ->)|(-> & Hx8)]; [exfalso; unfold PMCUR.ICS in Hin; cbn [In] in Hin; unfold PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_MEMBER_NAME, PML.ST_EXPECT_COLON, PML.ST_EXPECT_VALUE_OR_END, PML.ST_EXPECT_VALUE, PML.ST_MEMBER_NAME in Hin; clear - Hin; lia|].
      destruct Hx as [(Hq0 & _)|(_ & Hq1)]; [clear - Hx8 Hq0; lia | exact Hq1]. }
    split; [exact (CKA.wf_c_stop ps' ltac:(unfold ps'; cbn [PML.ps_more]; exact Hmore) WT)|].
    split.
    {   unfold PMSA.win_okA. apply (PTA.win_okA_ag M M' Sg AG LBo ps'); unfold ps'; cbn [PML.ps_win].
      - intros ch a Hch Ha. destruct (OUTB ch 16384 ltac:(unfold LB; apply in_or_app; right; exact Hch)) as (X1 & X2 & _).
        destruct Ha as [Ha|Ha]; [exact (proj2 (proj2 X1) a Ha) | exact (X2 a Ha)].
      - intros ch Hch. destruct (OUTB ch 16384 ltac:(unfold LB; apply in_or_app; right; exact Hch)) as ((X0 & X1 & _) & _ & X8 & _). split; [exact X0 | split; [exact X1 | exact X8]].
      - exact HWIN. }
    split.
    {   destruct HBB as (HB1 & HB2 & HB3). unfold PMSA.buf_bound_stale, PML.buf_bound, PML.buf_need, PML.winlen, ps' in *. cbn [PML.ps_buf PML.ps_win PML.ps_more PML.ps_st PML.ps_sst].
      replace (stz =? PML.ST_STRING) with false by (destruct Hsx as [(-> & _)|(-> & _)]; reflexivity). rewrite andb_false_r. split; [clear - HB1; lia | exact HB2]. }
    split; [exact (PTA.ec_at_ag (hl_segs L) IC M M' Sg AG E 0 OUTE HEC)|].
    split; [intros Hq; exfalso; apply Hq; reflexivity|].
    split.
    {
      apply (PTA.ls_ok_ag (hl_segs L) IC M M' Sg AG g HG); [|intros a Ha; exact (PTKF a Ha) | exact HLS].
      intros a Ha.
      assert (RG : 65536 <= a < 7028736 /\ forall sp' scr', aclient L ar LB FF sp' scr' a).
      { destruct Ha as [Ha|Ha]; [|exact (FOOTCL a Ha)]. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Ha. split; [clear - Ha; lia|].
        intros sp' scr'. right; right; left. rewrite ILO, IHI. split; [clear - Ha; lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia]. }
      destruct RG as (RG & CLa). split; [clear - RG; lia|]. destruct (DECW a (proj2 RG)) as [Hi|Ho].
      + right. split; [exact Hi | clear - RG O1 FSLO; lia].
      + left. split; [clear - RG; lia|]. split; [exact (CLa _ _) | exact Ho]. }
    split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact HPC|].
    split; [|reflexivity].
    split; [exact (conj WT LT)|].
    split; [reflexivity|]. split; [exact Hmore|]. split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
    unfold ps'. cbn [PML.ps_st]. unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END.
    destruct Hsx as [(-> & ->)|(-> & Hx8)]; destruct Hx as [(Hq0 & Hl0)|(Hq1 & Hl1)]; try (clear - Hx8 Hq0; lia); try (clear - Hq1; lia).
    + rewrite Hl0. reflexivity.
    + destruct (Z.eqb_spec (PML.ps_level ps) 0); [clear - Hl1 e; lia | reflexivity].
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VP : CL5A.visr (ahid A model) P 272).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 P 272 (P + k) RFx Pfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSP : ahid A model (Z_to_bv 64 (S (P + 208))) = false).
    { destruct (CL5A.infr_sh_wok L ar LB FF sp 0 P 272 (S (P + 208)) RFx Pfr ltac:(clear; lia) (SH208 _ eq_refl)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 1152) 1152).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DP : L5.defined Mv P 272).
    { apply (CL5A.defined_vis _ M P 272 VP). destruct Pfr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF f Hf) as (_ & _ & _ & _ & Fdef & _).
      intros k Hk. replace (P + k) with (ff_addr f + (P - ff_addr f + k)) by (clear; lia). apply Fdef. clear - Hk F1 F2. lia. }
    assert (DS : L5.defined Mv (sp - 1152) 1152) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kwr_intro with (A := P + 208) (N := 1); [ev_start | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact (L5.defined_sub Mv P 272 (P + 208) 1 DP ltac:(clear; lia) ltac:(clear; lia))].
    + eapply CL5.krange_intro with (v := P); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := P); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact P8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 (P + 208)); [exact UP208 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. assert (j = 0) by (clear - Hj; lia). subst j. rewrite Z.add_0_r. apply CL5A.byte_vis; [exact VSP|].
      pose proof (Psh 26 ltac:(clear; lia)) as G0. replace (S (P + 208)) with (S P + 26); [exact G0|]. rewrite (CL5A.S_add_al P 208 P8). reflexivity.
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := P + 208) (N2 := 1); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.kunk_intro with (A := sp - 1152) (N := 1152); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 1152) (N := 1152); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact Hsp32].
    + eapply CL5.kdisj_intro with (A1 := sp - 1152) (N1 := 1152) (A2 := P + 208) (N2 := 1); [ev_start | reflexivity | ev_start | reflexivity | clear - O4 S2; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. cbn [nth G.BLS AVA.FFS CH2.den CHA.denF map app length]. change (CH2.den E0 Cut_after_value_cboth_T.BL0) with (@nil (Z * Z)). cbn [app].
      split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + split; [intros a _ _; reflexivity|]. split; [left; reflexivity | intros X; discriminate X].
  - exact Hfp.
Qed.
End AfterValueOk.

