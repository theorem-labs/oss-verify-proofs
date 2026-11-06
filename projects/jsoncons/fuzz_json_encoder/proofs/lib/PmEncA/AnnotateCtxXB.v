(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA PmEncSpecs2A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_annotate_ctx_xboth_T Cut_annotate_ctx_xboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_annotate_ctx_xboth.
Module GT := Cut_annotate_ctx_xboth_T.

Module ANCA.
Definition PC_ANN : Z := 542968.      (* [comment removed for export] *)
Definition PCE : Z := 769920.         (* [comment removed for export] *)
Definition RETPC : Z := 770068.       (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition FFS : list (list (expr * Z * Z)) := [[]; []].
Definition WSH : list SGP.region := [(CHA.SRL3 (EVar 32), SBz, CHA.SRL3 (APC.eaddz (EVar 34) 7))].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition omE : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32) (EVar 11)) (EVar 32).
Definition nmE : expr := EAlu Instr.ALU_ADD (EVar 32) (EVar 33).
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      if Z.eqb pc PC_ANN then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_ANN && Nat.eqb i 0 && Nat.eqb j 1 && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) []
                                  && CHA.foot_chk GT.NF G.HDECL c [] []
                                  && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4096 0 [] [] WSH [] None c ps cj [] [] [] [])
                                  && CL.ps_reg_is ps 10 (EVar 32) && CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD (EVar 32) (EVar 34)) && CL.ps_reg_is ps 12 omE && CL.ps_reg_is ps 13 nmE
                                  && has cells (KWord (SA (EVar 10) 0) 8 (EVar 32)))%bool
                    | None => false end
        | None => false end
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c [] [] && Nat.eqb i 1 && CH2.blocks_eqb (nth i G.BLS []) [])%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC. Proof. CL.solve_is_ret. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = []. Proof. intros [|[|[|i]]]; reflexivity. Qed.
Lemma ffs_i : forall i, nth i FFS [] = []. Proof. intros [|[|[|i]]]; reflexivity. Qed.
End ANCA.

Section AnnotateCtxOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ANN : aannotate_spec L ar SCFG HI ANCA.PC_ANN 4096.        (* [comment removed for export] *)
Definition hid (P : Prop) : Prop := P.

Theorem annotate_shrink_ctx_ok : PMES2A.annotate_shrink_ctx_specA L ar HI ANCA.PCE.
Proof.
  intros LB FF LK cr A o b len old cap sp r.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hw0 & Hw8 & Hw16 & Hodef & Hofr & Ho8 & Hosh & HinLB & Hlen & Hold & HSC0 & Hb0 & Hcap) Hcont.
  unfold PMSA.u64, PMSA.a0, PMSA.a1, PMSA.AINC_SCR in *.
  set (om := 32 * old) in *. set (nm := len) in *.
  (* [comment removed for export] *)
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar _ _ o 24 RFx Hofr ltac:(clear; lia)) as (Q1 & Q2 & O3 & Q4 & O5 & O6 & Q7).
  assert (O1 : hid (ar_fs ar + 32 <= o \/ ahl_ceil ar <= o)) by (left; exact Q1). assert (O4 : hid (o + 24 <= ahl_ceil ar \/ sp <= o)) by (left; exact Q4).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  (* [comment removed for export] *)
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (b, cap) HinLB) as ((B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)) & Bdef & _ & _ & Bfap). cbn [fst snd] in B0, B1, B16, B3, B4, B5, B6, B7, Bdef, Bfap.
  assert (BLO : 16 <= b) by (clear - B0 B16 Hb0; apply Z.mod_divide in B16; [|lia]; destruct B16 as [q ->]; lia).
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (Hold' : 0 <= old <= 1024) by (clear - Hlen Hold Hcap; lia).
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; len; cap] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 old) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 len) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 cap) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = old) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = len) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = cap) by (rewrite V34; apply u64_of_Z; lia).
  (* [comment removed for export] *)
  assert (SCRV : CH.hd_scr G.HDECL = 4112) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (WW := [(S b, (cap + 7) / 8)] : list L5.range).
  assert (WINC : incl (@nil L5.range) WW) by (intros y []).
  assert (WOK : forall (w : L5.range) (a : Z), In w [] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a []).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [] /\ L5.in_rng w a)) by (intros rg []).
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. cbv beta iota in Ha. unfold CHA.sclientA.
    rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Hofr ltac:(clear; lia) ltac:(apply (CL5A.shreg_in_shadow o 3); [exact Ho8 | clear; lia | unfold S, SB in *; clear - Ha; lia])) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  (* [comment removed for export] *)
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (i : nat) (_ : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) =>
               (i = 0%nat -> shadow_cont M1 b cap om) /\ (i = 1%nat -> shadow_cont M1 b cap nm)).
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ ANCA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  unfold PMSA.cfg. change ANCA.PCE with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANCA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact ANCA.heap_ok.
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - (* [comment removed for export] *)
    intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ ANCA.leaf_ok _ _ _ _ _ IL) as X. unfold ANCA.leaf_chk in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANCA.FFS Cred 0 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    destruct (Z.eqb_spec pc ANCA.PC_ANN) as [->|Hne1].
    { (* [comment removed for export] *)
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y9]. apply andb_prop in X as [X Y8].
      apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2].
      apply andb_prop in X as [Y0 Yi]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi. apply Nat.eqb_eq in Y2. apply CH2.blocks_eqb_eq in Y3, Y4. subst i j.
      lazymatch type of Y5 with ANCA.isSome ?t = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA (HXom & _)]. specialize (HXom eq_refl).
      assert (HcB : CHA.curB LB G.BLS 0 E = LB) by (unfold CHA.curB; rewrite Y3; reflexivity).
      assert (HcF : CHA.curF FF sp ANCA.FFS 0 E = FF) by (unfold CHA.curF; rewrite ANCA.ffs_i; reflexivity).
      refine (CALLEE ANCA.PC_ANN 4096 0%nat [] ANCA.WSH [] None 0 0%nat c ps 1%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !ANCA.ffs_i, Y3, Y4; exact Hchk | rewrite !ANCA.ffs_i; reflexivity | rewrite ANCA.ffs_i; cbn [length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
      assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
      assert (W11 : bv_unsigned (ev E' 11) = old) by (rewrite (FZ 11%nat eq_refl); exact U11).
      assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
      assert (W33 : bv_unsigned (ev E' 33) = len) by (rewrite (FZ 33%nat eq_refl); exact U33).
      assert (W34 : bv_unsigned (ev E' 34) = cap) by (rewrite (FZ 34%nat eq_refl); exact U34).
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS ANCA.FFS Cred 0 0%nat E A1 M' m' HA') as Hoff.
      (* [comment removed for export] *)
      assert (FRS : forall a, in_shadow_of b cap a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
        refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANCA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                  0%nat c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite ANCA.ffs_i, Y3; exact YF|].
        rewrite ANCA.ffs_i, Y3. intros [Z0|[Z0|[Z0|[Z0|Z0]]]]; [rewrite SCRV in Z0; clear - Z0 SRa S2 CL; lia | destruct Z0 as (w & [] & _) | destruct Z0 as (bb & [] & _) | destruct Z0 as (f & [] & _) | destruct Z0 as (f & [] & _)]. }
      (* [comment removed for export] *)
      assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
      { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
      eexists. eexists. split; [exact (CRC.annotate_cps L ar C HI HIok PMSA.fp_ok ANCA.PC_ANN 4096 ANN 4096 LB FF LK1 cr A1 b cap om nm (sp + CH2.ci_csp ci) (CC.cp_pc cj) ltac:(clear; lia))|].
      split.
      { (* [comment removed for export] *)
        unfold CRC.annotate_pre. split; [exact HinLB|].
        split; [exact (REG 10%nat _ _ Y8 ltac:(cbn [edenot]; exact W32))|].
        split; [exact (REG 11%nat _ (b + cap) Y9 ltac:(apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B3 B7 Hcap; lia]))|].
        assert (OM : bv_unsigned (edenot E' ANCA.omE) = b + om) by (unfold om, ANCA.omE; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B3 B7 Hcap Hlen Hold Hold'; lia]).
        assert (NM : bv_unsigned (edenot E' ANCA.nmE) = b + nm) by (unfold nm, ANCA.nmE; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B3 B7 Hcap Hlen Hold; lia]).
        split; [exact (REG 12%nat _ _ Y10 OM)|]. split; [exact (REG 13%nat _ _ Y11 NM)|].
        split; [unfold om; clear - Hlen Hold Hold'; lia|]. split; [unfold nm; clear - Hlen Hold; lia|]. split; [clear - Hcap; lia|].
        apply (CL5A.shadow_cont_same M1 M' b cap om ltac:(unfold om; clear - Hlen Hold Hold'; lia) (CHA.mod8_of_16 _ B16)); [|exact HXom]. intros a Ha. exact (FRS a Ha). }
      { (* [comment removed for export] *)
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Hsh2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *. destruct HV as (_ & _ & HV3 & HV4 & _).
        assert (T32 : bv_unsigned (ev E2 32) = b) by (rewrite <- (proj1 Hag2 32%nat) by (clear - HV3 HV4; unfold GT.NF in HV4; lia); exact W32).
        assert (T34 : bv_unsigned (ev E2 34) = cap) by (rewrite <- (proj1 Hag2 34%nat) by (clear - HV3 HV4; unfold GT.NF in HV4; lia); exact W34).
        split; [cbn [CH2.den map app]; apply incl_refl|]. split.
        { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 (EVar 32), ANCA.SBz, CHA.SRL3 (APC.eaddz (EVar 34) 7)). split; [left; reflexivity|].
          unfold CHA.in_reg. rewrite CL5A.estart_srl3. unfold elenZ. rewrite CHA.u_srl3. unfold CL5A.uv. cbn [edenot]. rewrite W32.
          replace (bv_unsigned (edenot E' (APC.eaddz (EVar 34) 7))) with (cap + 7) by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap B3; lia]).
          unfold S, SB, ANCA.SBz in *. exact Hin. }
        split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko _ (or_introl eq_refl) Hin)|].
        split; [unfold CHA.curB; rewrite Y4; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|].
        split; [unfold XI; split; [intros Hx; discriminate Hx | intros _; exact Hsh2]|].
        intros X0 HX0 _. destruct HX0. } }
    (* [comment removed for export] *)
    apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y1]. apply andb_prop in X as [Xbase Xfoot].
    apply Nat.eqb_eq in Y1. apply CH2.blocks_eqb_eq in Y3. subst i.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA (_ & HXnm)]. specialize (HXnm eq_refl).
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANCA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok ANCA.RETPC 1%nat c ps _ Xbase _ (ANCA.ffs_i 1%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact ANCA.ret_at | rewrite ANCA.ffs_i, Y3; exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB LB G.BLS 1 E = LB) by (unfold CHA.curB; rewrite Y3; reflexivity). rewrite HB in HH1.
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [|repeat split; reflexivity].
    (* [comment removed for export] *)
    apply (CL5A.shadow_cont_same M1 M' b cap nm ltac:(unfold nm; clear - Hlen Hold; lia) (CHA.mod8_of_16 _ B16)); [|exact HXnm]. intros a Ha.
    pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
    refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANCA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
              1%nat c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite ANCA.ffs_i, Y3; exact Xfoot|].
    rewrite ANCA.ffs_i, Y3. intros [Z0|[Z0|[Z0|[Z0|Z0]]]]; [rewrite SCRV in Z0; clear - Z0 SRa S2 CL; lia | destruct Z0 as (w & [] & _) | destruct Z0 as (bb & [] & _) | destruct Z0 as (f & [] & _) | destruct Z0 as (f & [] & _)].
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Hofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Hofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) Ho8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4112) 4112).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : forall k, 0 <= k -> k + 8 <= 24 -> L5.u64_at (hl_segs L) M (o + k) (match k with 0 => b | 8 => b + len | _ => b + cap end) -> L5.u64_at (hl_segs L) Mv (o + k) (match k with 0 => b | 8 => b + len | _ => b + cap end)).
    { intros k K0 K1 Hk. apply (CL5A.u64_vis (hl_segs L)); [clear - O3 K0; lia | clear - O6 K1; lia | exact (CL5A.visr_sub _ o 24 (o + k) 8 VO ltac:(clear - K0; lia) ltac:(clear - K1; lia)) | exact Hk]. }
    assert (DS : L5.defined Mv (sp - 4112) 4112) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := o) (z := b); [ev_start | clear - O3; lia | clear - O6; lia | exact V32 | replace o with (o + 0) by (clear; lia); exact (DO 0 ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite Z.add_0_r; exact Hw0))].
    + eapply CL5.kword64_intro with (A := o + 8) (z := b + len); [ev_start | clear - O3; lia | clear - O6; lia | | exact (DO 8 ltac:(clear; lia) ltac:(clear; lia) Hw8)].
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B3 B7 Hcap Hlen Hold; lia].
    + eapply CL5.kword64_intro with (A := o + 16) (z := b + cap); [ev_start | clear - O3; lia | clear - O6; lia | | exact (DO 16 ltac:(clear; lia) ltac:(clear; lia) Hw16)].
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B3 B7 Hcap; lia].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | unfold hid in O1; clear - O1 O6 FSLO CL; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact Ho8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Hosh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.krange_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear - BLO B7 B3 B16; apply Z.mod_divide in B16; [|lia]; destruct B16 as [q ->]; lia].
    + eapply CL5.kalign_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear; lia | exact B16].
    + eapply CL5.krange_intro with (v := cap); [lin_eval; rw_atoms; clear; lia | clear - B3 Hcap; lia | clear - B3 Hcap; lia].
    + eapply CL5.krange_intro with (v := cap - len); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hold Hcap B3; lia | clear - Hlen Hold Hcap B3; lia].
    + eapply CL5.krange_intro with (v := len); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hold Hcap; lia | clear - Hlen Hold Hcap; lia].
    + eapply CL5.krange_intro with (v := old); [lin_eval; rw_atoms; clear; lia | clear - Hold'; lia | clear - Hold'; lia].
    + eapply CL5.kunk_intro with (A := sp - 4112) (N := 4112); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4112) (N := 4112); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4112) (N1 := 4112) (A2 := o) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | unfold hid in O4; clear - O4 S2; lia].
  - (* [comment removed for export] *)
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite ANCA.ffs_i, ANCA.bls_i.
      cbn [CH2.den map app CHA.denF length]. split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + unfold XI. split; [intros _; exact HSC0 | intros Hx; discriminate Hx].
  - exact Hfp.
Qed.
Print Assumptions annotate_shrink_ctx_ok.
End AnnotateCtxOk.
