(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncBridgesU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ESTNU.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable LBo : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
(* [comment removed for export] *)
Variable GR : list (Z * Z).
Variable kx bx : Z.
Variable XIv : eghost -> nat -> env -> mem -> Prop.
Abbreviation gB := (EBU.gB GR).
Abbreviation CredV := (EBU.CredV L kx bx).

Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBo sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - CH.hd_scr d) (CH.hd_scr d).
(* [comment removed for export] *)
Variables V S2 : Z.
Hypothesis OBJS : objs_enc L sp0 V S2.
Hypothesis W_S2 : In (S2, 24) W.
(* [comment removed for export] *)
Variable OB : expr.
Variable OK : Z.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Hypothesis OADDR : estart E0 (SA OB OK) = S2.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.

Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS eghost gB CredV).
Abbreviation AMB3V := (CH2V.amb3V L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

(* [comment removed for export] *)
Definition kxs (g : eghost) : Z := kx + kv_st (g_scap g) * hl_k_per_malloc L.
Definition bxs (g : eghost) : Z := bx + bpot_st L (g_scap g).
Definition PAYMAX : Z := 2 ^ 50.

Definition a0e (a0 : option Z) : option expr := match a0 with Some z => Some (ELit z) | None => None end.
(* [comment removed for export] *)
Definition strans_chkN (scr : Z) (a0 : option Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  if CH2.blocks_eqb BLj BLi then CH2.custom_chk NF d scr 0 BLi [(OB, OK, ELit 24)] [] (a0e a0) c ps cj BLi else None.

Lemma objs_facts : sp0 <= V /\ V + 408 <= hl_sptop L /\ sp0 <= S2 /\ S2 + 24 <= hl_sptop L /\ S2 mod 8 = 0 /\ PML.apart V 408 S2 24.
Proof. destruct OBJS as ((A1 & A2 & A3) & (B1 & B2 & B3) & C). unfold ENC_SIZE in *. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma enc_inv_kept : forall (M' M2 : mem) g rep' n LBk spc scr,
  enc_inv M' V S2 g -> L5C.hpres L LBk spc scr [(S2, 24)] M' M2 -> L5C.stk (hl_sptop L) M2 spc scr -> 0 <= scr -> spc <= sp0 ->
  incl (stack_blocks (g_sb g) (g_scap g)) LBk -> (forall b, In b LBk -> block_range L (fst b) (snd b)) ->
  sink_at M2 S2 rep' -> len (PML.srep_chars rep') = g_len g + n ->
  enc_inv M2 V S2 (EBU.g_upd g rep' n).
Proof.
  intros M' M2 g rep' n LBk spc scr (I1 & I2 & I3 & I4 & I5) HP HSTK Hscr Hsp Hst Hbr Hsink Hlen.
  destruct objs_facts as (O1 & O2 & O3 & O4 & O5 & O6). pose proof STK as (S1 & S2' & S3 & S4 & S5).
  pose proof (PmLayout.ly_errno L LAY) as LE.
  assert (KV : forall a, V <= a < V + 408 -> L5C.kept L LBk spc scr [(S2, 24)] a).
  { intros a Ha. apply (L5C.kept_stack_stk L LBk M2 spc scr); [exact HSTK | exact Hscr | lia | rewrite LE; lia |].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold PML.apart in O6. lia. }
  assert (AV : forall a n0, V <= a -> a + n0 <= V + 408 -> L5C.agree_on M' M2 a n0).
  { intros a n0 H1 H2 i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply KV. lia. }
  unfold EBU.g_upd. split; [|split; [|split; [|split]]]; cbn [g_es g_len g_rep g_sb g_scap].
  - apply (EK.enc_obj_agree M' M2 V S2 _ ltac:(lia) ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_COLUMN; lia | apply AV; unfold O_COLON, ENC_SIZE; lia | | exact I1].
    apply (L5C.defined_agree M' M2 (V + O_COLUMN) 8); [apply AV; unfold O_COLUMN; lia|].
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X.
  - apply (EK.stack_at_agree M' M2 V _ _ _ ltac:(lia) ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_STACK; lia | | exact I2].
    intros Hne. assert (Hin : In (g_sb g, g_scap g) LBk).
    { apply Hst. unfold stack_blocks. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (Hbr _ Hin) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in *.
    split; [lia|]. split; [lia|]. intros i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP).
    pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
    apply (L5C.kept_block L LBk spc scr [(S2, 24)] (g_sb g) (g_scap g) i Hin); [lia | lia | lia | rewrite LE; lia|].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
  - exact Hsink.
  - exact Hlen.
  - exact I5.
Qed.

Lemma scredit_of_ecredit : forall cr g, ecreditU L cr g kx bx -> screditU L cr (g_rep g) (kxs g) (bxs g).
Proof.
  intros cr g H. exact (EK.scredit_of_ecreditU L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) cr g kx bx H).
Qed.
Lemma ecredit_of_scredit : forall cr g rep' n, screditU L cr rep' (kxs g) (bxs g) -> 0 <= kx -> 0 <= bx -> ecreditU L cr (EBU.g_upd g rep' n) kx bx.
Proof.
  intros cr g rep' n H Hkx Hbx.
  exact (EK.ecredit_of_screditU L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) cr g kx bx rep' (EBU.g_upd g rep' n) eq_refl eq_refl H Hkx Hbx).
Qed.

(* [comment removed for export] *)
Lemma strans_leaf_okN : forall (pc scr : Z) (PayP : Z -> Prop) (Ret : bvmap 5 word -> Z -> Prop) (a0 : option Z) i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  strans_chkN scr a0 c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall R2 pay, Ret R2 pay -> match a0 with Some z => PML.a0 R2 z /\ 0 <= z < 2 ^ 64 | None => True end) ->
  (forall E R (M : mem) model E' R' (M' : mem), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     enc_inv M' V S2 g /\ incl (stack_blocks (g_sb g) (g_scap g)) (CH2.den E' (nth i BLS []) ++ LBo ++ GR)) ->
  (forall E R (M : mem) model E' R' (M' : mem) cr (fx' : FPState), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo eghost gB g) sp0 d W BLS (CredV g) scr 0 c ps cj ci i E E' R' M' model ->
     enc_inv M' V S2 g ->
     hi_heap HI ((CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g)) cr M' (m_vmmaps model) -> screditU L cr (g_rep g) (kxs g) (bxs g) ->
     PML.fp_ok fx' ->
     ((forall (fx2 : FPState) R2 (M2 : mem) model2 LB' cr' LBk Wc, PML.fp_ok fx2 ->
           (exists (rep' : PML.srep) (pay : Z), PayP pay /\ Ret R2 pay /\ sink_at M2 S2 rep' /\
              len (PML.srep_chars rep') = len (PML.srep_chars (g_rep g)) + pay /\
              LB' = (CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks rep' /\ LBk = CH2.den E' (nth i BLS []) ++ LBo ++ GR /\ Wc = [(S2, 24)] /\
              screditU L cr' rep' (kxs g) (bxs g)) ->
           regs_preserved R' R2 -> L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> model_but_vm model model2 -> hi_heap HI LB' cr' M2 (m_vmmaps model2) ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model2) K) ->
        srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K)) ->
  (forall E R (M : mem) model E' R' (M' : mem) E2 (M2 : mem) g' pay, CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree NF E0 E' ->
     env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (sp0 + CH2.ci_csp ci) scr [(S2, 24)] M' M2 ->
     enc_inv M2 V S2 g' -> g_es g' = g_es g -> g_sb g' = g_sb g -> g_scap g' = g_scap g ->
     g_len g' = g_len g + pay -> PayP pay ->
     XIv g' j E2 M2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr PayP Ret a0 i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk RETA0 XILEAF CALL XIRET fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct HAmb as [HAmbH HXI0].
  unfold strans_chkN in Hchk.
  destruct (CH2.blocks_eqb (nth j BLS []) (nth i BLS [])) eqn:B3; [|discriminate]. apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *.
  destruct (CH2V.custom_retV L HI HIok LYI LYE LYR NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok
              g M0c scr 0%nat BLi _ _ (a0e a0) i c ps j cj ci HOKV Hcj Hchk E R M model E' R' M' HAt HAmbH Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  (* [comment removed for export] *)
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x NF d scr 0 c ps cj BLi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  destruct (XILEAF E R M model E' R' M' HAt HAmbH HXI0 Hag HLF) as [HINV HST].
  set (own := CH2.den E' BLi) in *.
  unfold CH2.cur, CH2V.LBr in HH. fold BLi in HH, Hden. rewrite <- Hden in HH. fold own in HH.
  assert (Ho : estart E' (SA OB OK) = S2) by (rewrite (PB.estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct objs_facts as (O1 & O2 & O3 & O4 & O5 & O6). pose proof STK as (S1 & S2' & S3 & S4 & S5).
  (* [comment removed for export] *)
  assert (PERM1 : Permutation (own ++ LBo ++ gB g) ((own ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g))).
  { unfold EBU.gB. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH PERM1) as HH1.
  pose proof (scredit_of_ecredit cr g HC) as HSC.
  pose proof (CALL E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF HINV HH1 HSC HFP) as Hcall.
  rewrite Hpc. rewrite LS. apply Hcall.
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (rep' & pay & HPay & HRet & Hsink2 & Hlen' & -> & -> & -> & HSC') HRP HPRES Hbv2 HH2.
  pose proof (PmLayout.ly_kpm L LAY) as KPM.
  assert (Hlen2 : len (PML.srep_chars rep') = g_len g + pay) by (destruct HINV as (_ & _ & _ & I4 & _); lia).
  assert (PERM2 : Permutation ((own ++ LBo ++ GR) ++ PML.srep_blocks rep') (own ++ LBo ++ PML.srep_blocks rep' ++ GR)).
  { rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2 PERM2) as HH2'.
  assert (Hbr : forall b, In b (own ++ LBo ++ GR) -> block_range L (fst b) (snd b)).
  { intros b Hb. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). apply in_or_app. left. exact Hb. }
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  assert (HSTK2 : L5C.stk (hl_sptop L) M2 (sp0 + CH2.ci_csp ci) scr).
  { destruct Hstk as (K1 & K2 & K3 & K4 & _). split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
    exact (L5C.hpres_defined _ _ _ _ _ _ _ HPRES). }
  assert (HINV2 : enc_inv M2 V S2 (EBU.g_upd g rep' pay)).
  { apply (enc_inv_kept M' M2 g rep' pay (own ++ LBo ++ GR) (sp0 + CH2.ci_csp ci) scr HINV HPRES HSTK2); [lia | lia | exact HST | exact Hbr | exact Hsink2 | exact Hlen2]. }
  assert (HC' : CredV (EBU.g_upd g rep' pay) j (CH2.retEx E' (CH2.ci_nx ci) [] R2) cr').
  { pose proof HC as (Hkx0 & _ & Hbx0 & _). exact (ecredit_of_scredit cr' g rep' pay HSC' Hkx0 Hbx0). }
  (* [comment removed for export] *)
  unfold PML.cfg. rewrite <- LS.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  eapply (RET fx2 R2 M2 model2 [] (own ++ LBo ++ GR) [(S2, 24)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) _ HPRES).
  - intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb].
  - intros w a Hw Hin. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  - intros X [].
  - fold E2.
    assert (Hcur : CH2.cur (CH2V.LBr LBo eghost gB (EBU.g_upd g rep' pay)) BLS j E2 = own ++ LBo ++ PML.srep_blocks rep' ++ GR).
    { unfold CH2.cur, CH2V.LBr, EBU.gB, EBU.g_upd. cbn [g_rep]. rewrite B3. fold BLi. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
    destruct (CH2V.amb_callee_xV L HI LYI LYE NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV STK SCR_pos NF32 DEF0 g (EBU.g_upd g rep' pay) M0c scr 0%nat c ps cj ci i j E E' R' M' model
                E2 M2 model2 (own ++ LBo ++ GR) [(S2, 24)] cr' HOKV CF HPRES) as [OK2 HA2].
    + intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct Hw as [<-|[]]. exact (Hout (S2, 24) W_S2 Hin).
    + exact Hbv2.
    + rewrite Hcur. exact HH2'.
    + exact Hag2.
    + exact HC'.
    + apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv (EBU.g_upd g rep' pay) M2 j E2 M2 model2 OK2).
      split; [exact HA2|].
      apply (XIRET E R M model E' R' M' E2 M2 (EBU.g_upd g rep' pay) pay HAt HAmbH HXI0 HagE' Hag HLF Hag2 V3 HPRES HINV2); try reflexivity. exact HPay.
  Unshelve. destruct a0 as [z|]; [|exact I]. cbv beta iota. destruct (RETA0 R2 pay HRet) as [Hz Hzr]. rewrite Hz. cbn [edenot]. reflexivity.
Qed.
End Inst.
End ESTNU.
