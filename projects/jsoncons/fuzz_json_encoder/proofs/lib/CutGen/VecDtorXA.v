(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_vec_dtor_xasan_T Cut_vec_dtor_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_vec_dtor_xasan.
Module GT := Cut_vec_dtor_xasan_T.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.

Module VDA.
Definition PC_ASHR : Z := 730684.   (* [comment removed for export] *)
Definition PC_ADEL : Z := 730524.   (* [comment removed for export] *)
Definition PC_OPDEL : Z := 1031544.  (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition tE := EVar 10. Definition oE := EVar 32. Definition bE := EVar 33. Definition lnE := EVar 34. Definition capE := EVar 35.
Definition BLK : list (expr * expr) := [(bE, capE)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1482488) 8 (ELit SBz)].
Definition WSH : list SGP.region := [(CHA.SRL3 bE, SBz, CHA.SRL3 (APC.eaddz capE 7))].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition vcells (cells : list kentry) : bool :=
  (has cells (KWord (SA oE 0) 8 bE) && has cells (KWord (SA oE 8) 8 bE) && has cells (KWord (SA oE 16) 8 (EAlu Instr.ALU_ADD bE capE)) && has cells (KZero (SA (CHA.SRL3 oE) SBz) (ELit 3)))%bool.
Definition call_chk (pc scr : Z) (a1req : bool) (i0 j0 : nat) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  match CH2.ret_of G.RETS i k with
  | Some j => match nth_error G.CPS j with
              | Some cj => (Z.eqb (SR.ps_pc ps) pc && Nat.eqb i i0 && Nat.eqb j j0 && CH2.blocks_eqb (nth i G.BLS []) BLK && CH2.blocks_eqb (nth j G.BLS []) BLK
                            && CHA.foot_chk GT.NF G.HDECL c BLK []
                            && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr 0 BLK [] WSH STAT None c ps cj BLK [] BLK [])
                            && CL.ps_reg_is ps 10 oE && (negb a1req || CL.ps_reg_is ps 11 lnE) && vcells (SR.ps_cells ps))%bool
              | None => false end
  | None => false end.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_ASHR then call_chk PC_ASHR 4112 true 0 1 i c k ps
      else if Z.eqb pc PC_ADEL then call_chk PC_ADEL 4128 false 1 2 i c k ps
      else (Z.eqb pc PC_OPDEL && CRB.tail_base_chk GT.NF PC_OPDEL c ps && CHA.foot_chk GT.NF G.HDECL c BLK [] && Nat.eqb i 2 && CH2.blocks_eqb (nth i G.BLS []) BLK && CL.ps_reg_is ps 10 bE)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
End VDA.

Section VecDtorOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ASH_OK : PMSA.annotate_shrink_spec L ar HI VDA.PC_ASHR.
Hypothesis ADEL_OK : PMSA.annotate_delete_spec L ar HI VDA.PC_ADEL.
Hypothesis OPDEL_OK : PMSA.opdel_specA L ar HI VDA.PC_OPDEL.

Lemma FFSnil : forall i, nth i VDA.FFS [] = [].
Proof. intros i. unfold VDA.FFS. do 4 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.

Theorem vec_dtor_ok : PMSA.vec_dtor_specA L ar HI 730236.
Proof.
  intros LB FF LK cr A t o b len cap sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Hto & Htob & Ht8 & Htsh & Hto' & Hvec) Hcont.
  destruct Hvec as ((Hw0 & Hw8 & Hw16) & Hofr & Ho8 & Hosh & HinLB & Hlen & Hcap & Hshc).
  unfold PMSA.a0, PMSA.u64, PMSA.ANEW_SCR, PMSA.ANNOT_SCR, PMSA.ainfr, PMSA.acobj in *. change (64 + (32 + 4096)) with 4192 in *.
  (* [comment removed for export] *)
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  (* [comment removed for export] *)
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (b, cap) HinLB) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bdef, Bsa, Bap, Bfap.
  pose proof (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH (b, cap) HinLB ltac:(cbn [snd]; lia)) as BHI. cbn [fst] in BHI.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)).
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Hofr ltac:(lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.acobj_rng L ar LB FF sp t 8 RFx CSP Htob ltac:(lia)) as (T3 & T6 & T5 & T1 & T4).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (B1' : hl_img_hi L <= b) by (rewrite ILO, IHI in *; lia). clear B1 B6.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (t + 8 <= 2147446784 \/ 17594333495296 <= t)) in T5.
  change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7. change (hid (t + 8 <= o \/ o + 24 <= t)) in Hto'.
  change (hid (ar_fs ar + 32 <= t \/ ahl_ceil ar <= t)) in T1. change (hid (t + 8 <= ahl_ceil ar \/ sp <= t)) in T4.
  assert (RFr : CHA.rng_facts L ar (lb_remove b LB) FF).
  { apply (CHA.rng_incl L ar LB FF); [exact RFx | intros y Hy; exact (L5C.in_lb_remove b y LB Hy) | apply incl_refl]. }
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [o; b; len; cap] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 t) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 o) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 b) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 len) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 cap) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = t) by (rewrite V10; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = o) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = b) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = len) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = cap) by (rewrite V35; apply u64_of_Z; lia).
  (* [comment removed for export] *)
  assert (SCRV : CH.hd_scr G.HDECL = 4192) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar (lb_remove b LB) FF sp _ o 24 a RFr Hofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U32 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar (lb_remove b LB) FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; unfold CHA.sclientA.
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U32 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow o 3 a Ho8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) o 24 a RFr Hofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. unfold estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      destruct (CL5A.acobj_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) t 8 a RFr CSP Htob ltac:(clear - Ha; lia)) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow t 1 a Ht8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 1) with 8 in SH.
      destruct (CL5A.acobj_sh_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) t 8 a RFr CSP Htob ltac:(clear; lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  (* [comment removed for export] *)
  assert (KSH : forall p n a, CL5A.acobj ar FF sp p n -> 0 < n -> in_shadow_of p n a -> CHA.akept L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) WW a).
  { intros p n a Hp Hn Ha. destruct (CL5A.acobj_sh_wok L ar _ FF sp (CH.hd_scr G.HDECL) p n a RFr CSP Hp Hn Ha) as (G1 & G2 & _).
    destruct (CL5A.acobj_rng L ar LB FF sp p n RFx CSP Hp Hn) as (P3 & P6 & _). pose proof (SHR p n a P3 Hn P6 Ha) as SR.
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin SR O5. lia. }
  assert (KT : forall a, t <= a < t + 8 -> CHA.akept L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (CL5A.acobj_wok L ar _ FF sp (CH.hd_scr G.HDECL) t 8 a RFr CSP Htob Ha) as (G1 & G2 & _).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in Hto'. clear - Hin Ha Hto'. lia. }
  (* [comment removed for export] *)
  assert (NOFOOT : forall a, 2147450880 <= a < 17594333495296 -> ~ CHA.afoot_sem sp G.HDECL WW [(b, cap)] [] a).
  { intros a Ha [X|[X|[X|[X|X]]]].
    - rewrite SCRV in X. clear - X Ha S2 CL. lia.
    - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin Ha O5. lia.
    - destruct X as (bb & [<-|[]] & Hin). cbn [fst snd] in Hin. clear - Hin Ha BHI. lia.
    - destruct X as (f & [] & _).
    - destruct X as (f & [] & _). }
  (* [comment removed for export] *)
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (i : nat) (_ : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) =>
               match i with 0%nat => shadow_cont M1 b cap len | 1%nat => shadow_cont M1 b cap 0 | _ => True end).
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ VDA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  assert (DEN : forall E, env_agree GT.NF E0 E -> CH2.den E VDA.BLK = [(b, cap)]).
  { intros E HagE. unfold CH2.den, VDA.BLK, VDA.bE, VDA.capE. cbn [map fst snd edenot]. rewrite <- (proj1 HagE 33%nat), <- (proj1 HagE 35%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U33, U35. reflexivity. }
  rewrite <- LS in FPM.
  change 730236 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VDA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact VDA.heap_ok.
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - (* [comment removed for export] *)
    intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ VDA.leaf_ok _ _ _ _ _ IL) as X. unfold VDA.leaf_chk in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VDA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    (* [comment removed for export] *)
    assert (ANNOT : forall cpc scr (a1req : bool) (i0 j0 : nat) (om nm : Z),
      VDA.call_chk cpc scr a1req i0 j0 i c kk ps = true ->
      (forall Ex Ax Mx mx, XI i0 Ex Ax Mx mx -> shadow_cont Mx b cap om) -> (forall Ex Ax Mx mx, shadow_cont Mx b cap nm -> XI j0 Ex Ax Mx mx) -> 0 <= om <= cap -> 0 <= nm <= cap ->
      (forall LB0 FF0 LK0 cr0 A0 sp0 r0, CBA.cps_asanG L ar HI PMSA.fp_ok cpc r0 sp0 scr LB0 FF0 LK0 cr0 A0 0
          (fun R0 M0 => getr R0 10%bv = Z_to_bv 64 o /\ (a1req = true -> getr R0 11%bv = Z_to_bv 64 len) /\ L5.u64_at (hl_segs L) M0 o b /\ L5.u64_at (hl_segs L) M0 (o + 8) (b + 0) /\ L5.u64_at (hl_segs L) M0 (o + 16) (b + cap) /\
                        CL5A.ainfr FF0 o 24 /\ o mod 8 = 0 /\ shadow_zero M0 o 3 /\ In (b, cap) LB0 /\ shadow_cont M0 b cap om)
          (fun R0 M0 R' M' LB' cr' LBk W => shadow_cont M' b cap nm /\ LB' = LB0 /\ cr' = cr0 /\ LBk = LB0 /\ W = [(S b, (cap + 7) / 8)])) ->
      CCA.leaf_ok (hl_segs L) G.CPS (CHA.ambX L ar HI GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW G.BLS VDA.FFS Cred 0 XI) K PMSA.fp_ok i c ps).
    { intros cpc scr a1req i0 j0 om nm X0 XIi XIj Hom Hnm CALL_OK. unfold VDA.call_chk in X0.
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X0 as [X0 Y9]. apply andb_prop in X0 as [X0 Y8]. apply andb_prop in X0 as [X0 Y7]. apply andb_prop in X0 as [X0 Y5]. apply andb_prop in X0 as [X0 YF].
      apply andb_prop in X0 as [X0 Y4]. apply andb_prop in X0 as [X0 Y3]. apply andb_prop in X0 as [X0 Y2]. apply andb_prop in X0 as [Y0 Y1].
      apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply CH2.blocks_eqb_eq in Y3, Y4.
      lazymatch type of Y5 with VDA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
      unfold VDA.vcells in Y9. apply andb_prop in Y9 as [Y9 Ysh]. apply andb_prop in Y9 as [Y9 Yc]. apply andb_prop in Y9 as [Ya Yb].
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi]. apply XIi in HXi.
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      assert (HcB : CHA.curB (lb_remove b LB) G.BLS i0 E = (b, cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y3, (DEN E HagE); reflexivity).
      assert (HcF : CHA.curF FF sp VDA.FFS i0 E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
      refine (CALLEE cpc scr 0%nat VDA.BLK VDA.WSH VDA.STAT None 0 i0 c ps j0 cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
      assert (W32 : bv_unsigned (ev E' 32) = o) by (rewrite (FZ 32%nat eq_refl); exact U32).
      assert (W33 : bv_unsigned (ev E' 33) = b) by (rewrite (FZ 33%nat eq_refl); exact U33).
      assert (W35 : bv_unsigned (ev E' 35) = cap) by (rewrite (FZ 35%nat eq_refl); exact U35).
      assert (CELL : forall X0, VDA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW G.BLS VDA.FFS Cred 0 i0 E A1 M' m' HA') as Hoff.
      unfold VDA.oE, VDA.bE, VDA.lnE, VDA.capE in *.
      eexists. eexists. split; [exact (CALL_OK ((b, cap) :: lb_remove b LB) FF LK1 cr A1 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
      { (* [comment removed for export] *)
        split; [replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
                rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y7); cbn [edenot]; rewrite (FZ 32%nat eq_refl); exact V32|].
        split; [intros ->; cbn [negb orb] in Y8; replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity);
                rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 11 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y8); cbn [edenot]; rewrite (FZ 34%nat eq_refl); exact V34|].
        split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Ya) ltac:(ev_start)) as G0; unfold CL5A.uv in G0; cbn [edenot] in G0; rewrite W33 in G0; exact G0|].
        split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yb) ltac:(ev_start)) as G0; unfold CL5A.uv in G0; cbn [edenot] in G0; rewrite W33, <- (Z.add_0_r b) in G0; exact G0|].
        split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc) ltac:(ev_start)) as G0;
                replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EVar 33) (EVar 35))) with (b + cap) in G0; [exact G0 | symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap; lia]]|].
        split; [exact Hofr|]. split; [exact Ho8|].
        pose proof (CL5A.shz_elim (hl_segs L) E' _ (EVar 32) 3 o (CELL _ Ysh) ltac:(unfold CL5A.uv; cbn [edenot]; exact W32) ltac:(clear; lia)) as SZ.
        split; [intros jj Hj; exact (CL5A.byte_full _ _ _ _ (SZ jj Hj))|].
        split; [left; reflexivity|].
        apply (CL5A.shadow_cont_same M1 M' b cap om Hom (CHA.mod8_of_16 _ B16)); [|exact HXi]. intros a Ha.
        pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
        refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VDA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                  i0 c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
        rewrite FFSnil, Y3, (DEN E HagE). exact (NOFOOT a SRa). }
      { (* [comment removed for export] *)
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Hsh2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        assert (HagE2 : env_agree GT.NF E0 E2).
        { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
        split; [rewrite (DEN E' HagE'); apply incl_refl|]. split.
        { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 (EVar 33), VDA.SBz, CHA.SRL3 (APC.eaddz (EVar 35) 7)). split; [left; reflexivity|].
          unfold CHA.in_reg. rewrite CL5A.estart_srl3. unfold elenZ. rewrite CHA.u_srl3. unfold CL5A.uv. cbn [edenot]. rewrite W33.
          replace (bv_unsigned (edenot E' (APC.eaddz (EVar 35) 7))) with (cap + 7) by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]).
          unfold S, SB, VDA.SBz in *. exact Hin. }
        split.
        { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
          refine (CHA.obj_not_client L ar LYI (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) b cap a RFr _ B3 (CHA.mod8_of_16 _ B16) B4 (or_intror B1') Bap _ (or_intror _) Kc).
          - unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - B0 B7 BHI. lia.
          - intros f Hf. apply Bfap. apply in_or_app. left. exact Hf.
          - exact (CL5A.blk_shadow_in b cap a (CHA.mod8_of_16 _ B16) B3 Hin). }
        split; [unfold CHA.curB; rewrite Y4, (DEN E2 HagE2); exact HH2|]. split; [reflexivity|].
        split; [exact (XIj E2 A2 M2 m2 Hsh2)|].
        intros X0 HX0 _. unfold VDA.STAT in HX0. cbn [In] in HX0.
        destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
    destruct (Z.eqb_spec pc VDA.PC_ASHR) as [->|Hne1].
    { apply (ANNOT VDA.PC_ASHR 4112 true 0%nat 1%nat len 0 X); [intros Ex Ax Mx mx HX; exact HX | intros Ex Ax Mx mx HX; exact HX | clear - Hlen; lia | clear - Hlen; lia |].
      intros LB0 FF0 LK0 cr0 A0 sp0 r0. intros fx0 R0 M0 model0 K0 HH0 Hmo0 HK0 Hfp0 Hra0 Hraok0 Hsp0 Htp0 Hstk0 Hroom0 Hffrs0 (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10) Hcont0.
      destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH0) (b, cap) P9) as ((_ & _ & _ & Q3 & _) & _). cbn [snd] in Q3.
      apply (ASH_OK LB0 FF0 LK0 cr0 A0 o b 0 len cap sp0 r0 fx0 R0 M0 model0 K0 HH0 Hmo0 HK0 Hfp0 Hra0 Hraok0 Hsp0 Htp0 Hstk0 Hroom0 Hffrs0); [|exact Hcont0].
      unfold PMSA.a0, PMSA.a1, PMSA.vec_at, PMSA.u64, PMSA.ainfr. split; [exact P1|]. split; [exact (P2 eq_refl)|]. split; [split; [exact P3 | split; [exact P4 | exact P5]]|].
      split; [exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [clear - Hlen; lia|]. split; [clear - Hlen; lia|]. split; [exact P10|]. split; [clear - Q3 BHI; lia | clear - Hcap; lia]. }
    destruct (Z.eqb_spec pc VDA.PC_ADEL) as [->|Hne2].
    { apply (ANNOT VDA.PC_ADEL 4128 false 1%nat 2%nat 0 cap X); [intros Ex Ax Mx mx HX; exact HX | intros Ex Ax Mx mx HX; exact I | clear - Hlen; lia | clear - Hlen; lia |].
      intros LB0 FF0 LK0 cr0 A0 sp0 r0. intros fx0 R0 M0 model0 K0 HH0 Hmo0 HK0 Hfp0 Hra0 Hraok0 Hsp0 Htp0 Hstk0 Hroom0 Hffrs0 (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10) Hcont0.
      destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH0) (b, cap) P9) as ((_ & _ & _ & Q3 & _) & _). cbn [snd] in Q3.
      apply (ADEL_OK LB0 FF0 LK0 cr0 A0 o b 0 cap sp0 r0 fx0 R0 M0 model0 K0 HH0 Hmo0 HK0 Hfp0 Hra0 Hraok0 Hsp0 Htp0 Hstk0 Hroom0 Hffrs0); [|exact Hcont0].
      unfold PMSA.a0, PMSA.vec_at, PMSA.u64, PMSA.acobj. split; [exact P1|]. split; [split; [exact P3 | split; [exact P4 | exact P5]]|].
      split; [left; exact P6|]. split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [clear - Hlen; lia|]. split; [clear - Hcap; lia|]. split; [exact P10 | clear - Q3 BHI; lia]. }
    (* [comment removed for export] *)
    apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [X YF]. apply andb_prop in X as [Y0 Y1].
    apply Z.eqb_eq in Y0. subst pc. apply Nat.eqb_eq in Y2. subst i. apply CH2.blocks_eqb_eq in Y3.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA _].
    assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
    refine (CRB.tail_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL WW WW G.BLS VDA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs WRS_OK
              K PMSA.fp_ok DEF0 S6 HKnil R r EV Hra Hraok VDA.PC_OPDEL 4096 0 2%nat c ps Y1 _ (FFSnil 2%nat) _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HA HFP Hag HLF _);
      [rewrite FFSnil, Y3; exact YF | rewrite SCRV; clear; lia | clear; lia |].
    intros cr1 LK1 HRP HP HH1 HLK1 HC1 HagE' HA'. assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB (lb_remove b LB) G.BLS 2 E = (b, cap) :: lb_remove b LB) by (unfold CHA.curB; rewrite Y3, (DEN E HagE); reflexivity).
    rewrite HB in *.
    eexists. eexists. split; [exact (OPDEL_OK ((b, cap) :: lb_remove b LB) FF LK1 cr A1 b cap sp r)|].
    split.
    { split; [|left; reflexivity]. unfold PMSA.a0.
      replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
      rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10). unfold VDA.bE. cbn [edenot].
      rewrite <- (proj1 HagE' 33%nat) by (apply Nat.ltb_lt; reflexivity). exact V33. }
    intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 (-> & -> & -> & ->) HRP2 HP2 Hrt2 HA2 Hmo2 HLK2 HH2.
    assert (RM : lb_remove b ((b, cap) :: lb_remove b LB) = lb_remove b LB) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
    rewrite RM in *.
    apply (Hcont fx2 R2 M2 model2 (lb_remove b LB) cr (lb_remove b LB) WW LK2 A2 HFP2); [repeat split; reflexivity | exact HRP2 | | exact Hrt2 | exact HA2 | exact Hmo2 | exact HLK2 | exact HH2].
    rewrite SCRV in HP. unfold PMSA.OPDEL_SCR, PMSA.MALLOC_SCR in HP2.
    apply (CRB.ahpres_trans L ar (lb_remove b LB) (lb_remove b LB) (lb_remove b LB) FF sp 4192 4096 WW WW [] M M' M2 HP HP2 (incl_refl _) (incl_refl _));
      [clear; lia | clear - S3 SP1; lia | clear - CL; lia | clear - S2; lia | intros w a Hw Hin; exists w; split; assumption | intros w a []].
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Hofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VT : CL5A.visr (ahid A model) t 8).
    { intros k Hk. destruct (CL5A.acobj_wok L ar LB FF sp 0 t 8 (t + k) RFx CSP Htob ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Hofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) Ho8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VST : ahid A model (Z_to_bv 64 (S t)) = false).
    { destruct (CL5A.acobj_sh_wok L ar LB FF sp 0 t 8 (S t) RFx CSP Htob ltac:(clear; lia) (CL5A.shreg_in_shadow t 1 (S t) Ht8 ltac:(clear; lia) ltac:(unfold S; clear; lia))) as (G1 & G2 & G3).
      exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4192) 4192).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv o 24).
    { apply (CL5A.defined_vis _ M o 24 VO). destruct Hofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF f Hf) as (_ & _ & _ & _ & Fdef & _).
      intros k Hk. replace (o + k) with (ff_addr f + (o - ff_addr f + k)) by (clear; lia). apply Fdef. clear - Hk F1 F2. lia. }
    assert (DS : L5.defined Mv (sp - 4192) 4192) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := t) (z := o); [ev_start | clear - T3; lia | clear - T6; lia | exact V32 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - T3; lia | clear - T6; lia | exact VT | exact Hto].
    + eapply CL5.krange_intro with (v := t); [lin_eval; rw_atoms; clear; lia | clear - T3 T6; lia | unfold hid in T1; clear - T1 T6 FSLO CL; lia].
    + eapply CL5.kalign_intro with (v := t); [lin_eval; rw_atoms; clear; lia | clear - T3 T6; lia | clear; lia | exact Ht8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 t); [exact U10 | clear; lia | clear - T3 T6; lia |].
      intros j Hj. assert (j = 0) by (clear - Hj; lia). subst j. apply CL5A.byte_vis; [rewrite Z.add_0_r; exact VST | exact (Htsh 0 ltac:(clear; lia))].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := t) (N2 := 8); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in T5; clear - T5; lia].
    + eapply CL5.kword64_intro with (A := o) (z := b); [ev_start | clear - O3; lia | clear - O6; lia | exact V33 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := b + len); [ev_start | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia].
      * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 8) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := b + cap); [ev_start | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia].
      * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 16) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw16].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev_start | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact Ho8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U32 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Hosh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.krange_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear - BHI B4 B3 SP1; lia].
    + eapply CL5.kalign_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear; lia | exact B16].
    + eapply CL5.krange_intro with (v := cap); [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia | clear - Hcap; lia].
    + eapply CL5.krange_intro with (v := cap - len); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap; lia].
    + eapply CL5.krange_intro with (v := len); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap; lia].
    + eapply CL5.kunk_intro with (A := sp - 4192) (N := 4192); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4192) (N := 4192); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4192) (N1 := 4192) (A2 := o) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4192) (N1 := 4192) (A2 := t) (N2 := 8); [ev_start | reflexivity | ev_start | reflexivity | unfold hid in T4; clear - T4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := t) (N1 := 8) (A2 := o) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | unfold hid in Hto'; clear - Hto'; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4192) (N1 := 4192) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U35 | clear - B4 S2; lia].
    + destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF.
      eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U35 | clear - QF F1 F2; lia].
    + eapply CL5.kdisj_intro with (A1 := t) (N1 := 8) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U35 |].
      destruct Htob as [(f & Hf & F1 & F2)|(XS1 & XS2)]; [pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF; clear - QF F1 F2; lia | clear - XS1 B4 S2; lia].
    + destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _).
      eapply CL5.kdisj_intro with (A1 := o / 8 + SB) (N1 := 3) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U33; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      pose proof (CL5A.gran_blk cap ltac:(clear - Hcap; lia)) as GB. destruct QF as [QF|QF].
      * right. pose proof (CL5A.gran_le b ((cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) o ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
      * left. pose proof (CL5A.gran_le o 3 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ b QF) as G2. clear - G1 G2. lia.
    + eapply CL5.kdisj_intro with (A1 := t / 8 + SB) (N1 := 1) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U10; reflexivity | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U33; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      pose proof (CL5A.gran_blk cap ltac:(clear - Hcap; lia)) as GB.
      destruct Htob as [(f & Hf & F1 & F2)|(XS1 & XS2)];
        [|right; pose proof (CL5A.gran_le b ((cap + 7) / 8) (ahl_ceil ar) C8 ltac:(clear - B4 GB; lia)) as G1; pose proof (CL5A.div8_le (ahl_ceil ar) t ltac:(clear - XS1 S2; lia)) as G2; clear - G1 G2; lia].
      pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _). destruct QF as [QF|QF].
      * right. pose proof (CL5A.gran_le b ((cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) t ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
      * left. pose proof (CL5A.gran_le t 1 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ b QF) as G2. clear - G1 G2. lia.
    + destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G1 & G2).
      eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [ev_start | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U33; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold hid in O5. unfold SB in *. clear - O5 G1 G2. lia.
    + destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G1 & G2).
      eapply CL5.kdisj_intro with (A1 := t) (N1 := 8) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [ev_start | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U33; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold hid in T5. unfold SB in *. clear - T5 G1 G2. lia.
  - (* [comment removed for export] *)
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 G.BLS []) with VDA.BLK. rewrite (DEN E0 (CC.env_agree_refl _ _)), FFSnil. cbn [app CHA.denF map length].
      split; [exact (CBA.own_front L ar C HI HIok _ _ _ _ _ _ _ b cap HH HinLB)|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + exact Hshc.
  - exact Hfp.
Qed.
Print Assumptions vec_dtor_ok.
End VecDtorOk.
