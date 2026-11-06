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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_annotate_xasan_T Cut_annotate_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_annotate_xasan.
Module GT := Cut_annotate_xasan_T.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.

Module ANA.
Definition PC_ANN : Z := 540712.   (* [comment removed for export] *)
Definition PCE (i : nat) : Z := nth i [842060; 730684; 841184; 730524] 0.          (* [comment removed for export] *)
Definition RETPC (i : nat) : Z := nth (i - 4) [842184; 730808; 841284; 730644] 0.  (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition WSH : list SGP.region := [(CHA.SRL3 (EVar 32), SBz, CHA.SRL3 (APC.eaddz (EVar 34) 7))].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition omE (i : nat) : expr :=
  match i with 0%nat => EAlu Instr.ALU_ADD (EVar 32) (EVar 33) | 1%nat => EAlu Instr.ALU_ADD (EVar 11) (EVar 32) | 2%nat => EAlu Instr.ALU_ADD (EVar 32) (EVar 34) | _ => EAlu Instr.ALU_ADD (EVar 32) (EVar 33) end.
Definition nmE (i : nat) : expr :=
  match i with 0%nat => EAlu Instr.ALU_ADD (EVar 11) (EAlu Instr.ALU_ADD (EVar 32) (EVar 33)) | 1%nat => EAlu Instr.ALU_ADD (EVar 32) (EVar 33) | 2%nat => EAlu Instr.ALU_ADD (EVar 11) (EVar 32) | _ => EAlu Instr.ALU_ADD (EVar 32) (EVar 34) end.
Definition KNC : list kentry := firstn 18 (CC.cp_know G.cp0).
Lemma knc_ok : forall i c, (i < 4)%nat -> nth_error G.CPS i = Some c -> firstn 18 (CC.cp_know c) = KNC /\ CC.cp_regs c = CC.cp_regs G.cp0 /\ CC.cp_pc c = PCE i.
Proof. intros i c Hi Hc. do 4 (destruct i as [|i]; [injection Hc as <-; vm_compute; repeat split; reflexivity|]). lia. Qed.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      if Z.eqb pc PC_ANN then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_ANN && Nat.ltb i 4 && Nat.eqb j (i + 4) && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) []
                                  && CHA.foot_chk GT.NF G.HDECL c [] []
                                  && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4096 0 [] [] WSH [] None c ps cj [] [] [] [])
                                  && CL.ps_reg_is ps 10 (EVar 32) && CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD (EVar 32) (EVar 34)) && CL.ps_reg_is ps 12 (omE i) && CL.ps_reg_is ps 13 (nmE i)
                                  && has cells (KWord (SA (EVar 10) 0) 8 (EVar 32)))%bool
                    | None => false end
        | None => false end
      else
        (CBA.exit_base_chk GT.NF (RETPC i) c ps && CHA.foot_chk GT.NF G.HDECL c [] [] && Nat.leb 4 i && Nat.ltb i 8 && CH2.blocks_eqb (nth i G.BLS []) [])%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at4 : CL.is_ret_at RSEGS 842184. Proof. CL.solve_is_ret. Qed.
Lemma ret_at5 : CL.is_ret_at RSEGS 730808. Proof. CL.solve_is_ret. Qed.
Lemma ret_at6 : CL.is_ret_at RSEGS 841284. Proof. CL.solve_is_ret. Qed.
Lemma ret_at7 : CL.is_ret_at RSEGS 730644. Proof. CL.solve_is_ret. Qed.
Lemma ret_at : forall i, (4 <= i)%nat -> (i < 8)%nat -> CL.is_ret_at RSEGS (RETPC i).
Proof.
  intros i H1 H2. do 4 (destruct i as [|i]; [lia|]).
  destruct i as [|[|[|[|i]]]]; [exact ret_at4 | exact ret_at5 | exact ret_at6 | exact ret_at7 | lia].
Qed.
End ANA.

Section AnnotateOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ANN : aannotate_spec L ar SCFG HI ANA.PC_ANN 4096.        (* [comment removed for export] *)

Lemma FFSnil : forall i, nth i ANA.FFS [] = [].
Proof. intros i. unfold ANA.FFS. do 9 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.

(* [comment removed for export] *)
Definition omv (i0 : nat) (len cap a1v : Z) : Z := match i0 with 0%nat => len | 1%nat => a1v | 2%nat => cap | _ => len end.
Definition nmv (i0 : nat) (len cap a1v : Z) : Z := match i0 with 0%nat => len + a1v | 1%nat => len | 2%nat => a1v | _ => cap end.

Lemma annot_gen : forall i0, (i0 < 4)%nat -> forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o b len cap a1v sp r : Z),
  CBA.cps_asanG L ar HI PMSA.fp_ok (ANA.PCE i0) r sp 4112 LB FF LK cr A 0
    (fun R M => getr R 10%bv = Z_to_bv 64 o /\ (i0 <> 3%nat -> getr R 11%bv = Z_to_bv 64 a1v) /\
                PMSA.u64 L M o b /\ (i0 <> 2%nat -> PMSA.u64 L M (o + 8) (b + len)) /\ PMSA.u64 L M (o + 16) (b + cap) /\
                PMSA.acobj ar FF sp o 24 /\ o mod 8 = 0 /\ shadow_zero M o 3 /\ In (b, cap) LB /\ 0 <= len <= cap /\ 0 < cap <= 4096 /\ 0 <= a1v <= 4096 /\
                0 <= omv i0 len cap a1v <= cap /\ 0 <= nmv i0 len cap a1v <= cap /\ shadow_cont M b cap (omv i0 len cap a1v))
    (fun R M R' M' LB' cr' LBk W => shadow_cont M' b cap (nmv i0 len cap a1v) /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S b, (cap + 7) / 8)]).
Proof.
  intros i0 Hi0 LB FF LK cr A o b len cap a1v sp r.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hw0 & Hw8 & Hw16 & Hofr & Ho8 & Hosh & HinLB & Hlen & Hcap & Ha1v & Hom & Hnm & HSC0) Hcont.
  unfold PMSA.u64 in *.
  set (om := omv i0 len cap a1v) in *. set (nm := nmv i0 len cap a1v) in *.
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
  destruct (CL5A.acobj_rng L ar LB FF sp o 24 RFx CSP Hofr ltac:(lia)) as (O3 & O6 & O5 & O1 & O4).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (ar_fs ar + 32 <= o \/ ahl_ceil ar <= o)) in O1. change (hid (o + 24 <= ahl_ceil ar \/ sp <= o)) in O4.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  (* [comment removed for export] *)
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (b, cap) HinLB) as ((B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)) & Bdef & _ & _ & Bfap). cbn [fst snd] in B0, B1, B16, B3, B4, B5, B6, B7, Bdef, Bfap.
  pose proof (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH (b, cap) HinLB ltac:(cbn [snd]; clear - Hcap; lia)) as BHI. cbn [fst] in BHI. unfold BIGSHADOW_HI in BHI.
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; len; cap] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 len) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 cap) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
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
    destruct (CL5A.acobj_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx CSP Hofr ltac:(clear; lia) ltac:(apply (CL5A.shreg_in_shadow o 3); [exact Ho8 | clear; lia | unfold S, SB in *; clear - Ha; lia])) as (G1 & G2 & G3).
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
               (i = i0 \/ i = (i0 + 4)%nat) /\ (i = i0 -> shadow_cont M1 b cap om) /\ (i = (i0 + 4)%nat -> shadow_cont M1 b cap nm)).
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ ANA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM.
  destruct (nth_error G.CPS i0) as [c0|] eqn:Hc0; [|exfalso; do 4 (destruct i0 as [|i0]; [discriminate Hc0|]); clear - Hi0; lia].
  destruct (ANA.knc_ok i0 c0 Hi0 Hc0) as (KN1 & KR1 & KP1). rewrite <- KP1.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact ANA.heap_ok.
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - (* [comment removed for export] *)
    intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ ANA.leaf_ok _ _ _ _ _ IL) as X. unfold ANA.leaf_chk in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANA.FFS Cred 0 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    destruct (Z.eqb_spec pc ANA.PC_ANN) as [->|Hne1].
    { (* [comment removed for export] *)
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y9]. apply andb_prop in X as [X Y8].
      apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2].
      apply andb_prop in X as [Y0 Yi]. apply Z.eqb_eq in Y0. apply Nat.ltb_lt in Yi. apply Nat.eqb_eq in Y2. apply CH2.blocks_eqb_eq in Y3, Y4.
      lazymatch type of Y5 with ANA.isSome ?t = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA (HXi & HXom & _)].
      assert (Hii : i = i0) by (destruct HXi as [Hx|Hx]; [exact Hx | exfalso; clear - Hx Yi; lia]). subst i. subst j. specialize (HXom eq_refl).
      assert (HcB : CHA.curB LB G.BLS i0 E = LB) by (unfold CHA.curB; rewrite Y3; reflexivity).
      assert (HcF : CHA.curF FF sp ANA.FFS i0 E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
      refine (CALLEE ANA.PC_ANN 4096 0%nat [] ANA.WSH [] None 0 i0 c ps (i0 + 4)%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
      assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
      assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
      assert (W33 : bv_unsigned (ev E' 33) = len) by (rewrite (FZ 33%nat eq_refl); exact U33).
      assert (W34 : bv_unsigned (ev E' 34) = cap) by (rewrite (FZ 34%nat eq_refl); exact U34).
      assert (W11 : i0 <> 3%nat -> bv_unsigned (ev E' 11) = a1v) by (intros Hne; rewrite (FZ 11%nat eq_refl); change 11%nat with (ridx 11%bv); rewrite (EV 11%bv), (Ha1 Hne); apply u64_of_Z; clear - Ha1v; lia).
      assert (CELL : forall X0, ANA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS ANA.FFS Cred 0 i0 E A1 M' m' HA') as Hoff.
      (* [comment removed for export] *)
      assert (FRS : forall a, in_shadow_of b cap a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
        refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                  i0 c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
        rewrite FFSnil, Y3. intros [Z0|[Z0|[Z0|[Z0|Z0]]]]; [rewrite SCRV in Z0; clear - Z0 SRa S2 CL; lia | destruct Z0 as (w & [] & _) | destruct Z0 as (bb & [] & _) | destruct Z0 as (f & [] & _) | destruct Z0 as (f & [] & _)]. }
      (* [comment removed for export] *)
      assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
      { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
      eexists. eexists. split; [exact (CRC.annotate_cps L ar C HI HIok PMSA.fp_ok ANA.PC_ANN 4096 ANN 4096 LB FF LK1 cr A1 b cap om nm (sp + CH2.ci_csp ci) (CC.cp_pc cj) ltac:(clear; lia))|].
      split.
      { (* [comment removed for export] *)
        unfold CRC.annotate_pre. split; [exact HinLB|].
        split; [exact (REG 10%nat _ _ Y8 ltac:(cbn [edenot]; exact W32))|].
        split; [exact (REG 11%nat _ (b + cap) Y9 ltac:(apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap; lia]))|].
        assert (OMNM : bv_unsigned (edenot E' (ANA.omE i0)) = b + om /\ bv_unsigned (edenot E' (ANA.nmE i0)) = b + nm).
        { unfold om, nm. clear CALLEE. destruct i0 as [|[|[|[|i0]]]]; [| | | |exfalso; clear - Hi0; lia]; cbn [ANA.omE ANA.nmE omv nmv];
            try (specialize (W11 ltac:(discriminate))); split; (apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap Hlen Ha1v Hom Hnm; cbn [omv nmv] in *; lia]). }
        destruct OMNM as [OM NM].
        split; [exact (REG 12%nat _ _ Y10 OM)|]. split; [exact (REG 13%nat _ _ Y11 NM)|].
        split; [exact Hom|]. split; [exact Hnm|]. split; [clear - Hcap; lia|].
        apply (CL5A.shadow_cont_same M1 M' b cap om Hom (CHA.mod8_of_16 _ B16)); [|exact HXom]. intros a Ha. exact (FRS a Ha). }
      { (* [comment removed for export] *)
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Hsh2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *. destruct HV as (_ & _ & HV3 & HV4 & _).
        assert (T32 : bv_unsigned (ev E2 32) = b) by (rewrite <- (proj1 Hag2 32%nat) by (clear - HV3 HV4; unfold GT.NF in HV4; lia); exact W32).
        assert (T34 : bv_unsigned (ev E2 34) = cap) by (rewrite <- (proj1 Hag2 34%nat) by (clear - HV3 HV4; unfold GT.NF in HV4; lia); exact W34).
        split; [cbn [CH2.den map app]; apply incl_refl|]. split.
        { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 (EVar 32), ANA.SBz, CHA.SRL3 (APC.eaddz (EVar 34) 7)). split; [left; reflexivity|].
          unfold CHA.in_reg. rewrite CL5A.estart_srl3. unfold elenZ. rewrite CHA.u_srl3. unfold CL5A.uv. cbn [edenot]. rewrite W32.
          replace (bv_unsigned (edenot E' (APC.eaddz (EVar 34) 7))) with (cap + 7) by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]).
          unfold S, SB, ANA.SBz in *. exact Hin. }
        split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko _ (or_introl eq_refl) Hin)|].
        split; [unfold CHA.curB; rewrite Y4; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|].
        split; [unfold XI; split; [right; reflexivity | split; [intros Hx; exfalso; clear - Hx; lia | intros _; exact Hsh2]]|].
        intros X0 HX0 _. destruct HX0. } }
    (* [comment removed for export] *)
    apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [X Y1]. apply andb_prop in X as [Xbase Xfoot].
    apply Nat.leb_le in Y1. apply Nat.ltb_lt in Y2. apply CH2.blocks_eqb_eq in Y3.
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA (HXi & _ & HXnm)].
    assert (Hii : i = (i0 + 4)%nat) by (destruct HXi as [Hx|Hx]; [exfalso; clear - Hx Y1 Hi0; lia | exact Hx]). specialize (HXnm Hii).
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok (ANA.RETPC i) i c ps _ Xbase _ (FFSnil i) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
      [rewrite LS; exact (ANA.ret_at i Y1 Y2) | rewrite FFSnil, Y3; exact Xfoot |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    assert (HB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite Y3; reflexivity). rewrite HB in HH1.
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [|repeat split; reflexivity].
    (* [comment removed for export] *)
    apply (CL5A.shadow_cont_same M1 M' b cap nm Hnm (CHA.mod8_of_16 _ B16)); [|exact HXnm]. intros a Ha.
    pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
    refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW [] G.BLS ANA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
              i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact Xfoot|].
    rewrite FFSnil, Y3. intros [Z0|[Z0|[Z0|[Z0|Z0]]]]; [rewrite SCRV in Z0; clear - Z0 SRa S2 CL; lia | destruct Z0 as (w & [] & _) | destruct Z0 as (bb & [] & _) | destruct Z0 as (f & [] & _) | destruct Z0 as (f & [] & _)].
  - exact Hc0.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros k Hk. destruct (CL5A.acobj_wok L ar LB FF sp 0 o 24 (o + k) RFx CSP Hofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
    { intros j Hj. destruct (CL5A.acobj_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx CSP Hofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) Ho8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4112) 4112).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : forall k, 0 <= k -> k + 8 <= 24 -> L5.u64_at (hl_segs L) M (o + k) (match k with 0 => b | 8 => b + len | _ => b + cap end) -> L5.u64_at (hl_segs L) Mv (o + k) (match k with 0 => b | 8 => b + len | _ => b + cap end)).
    { intros k K0 K1 Hk. apply (CL5A.u64_vis (hl_segs L)); [clear - O3 K0; lia | clear - O6 K1; lia | exact (CL5A.visr_sub _ o 24 (o + k) 8 VO ltac:(clear - K0; lia) ltac:(clear - K1; lia)) | exact Hk]. }
    assert (DS : L5.defined Mv (sp - 4112) 4112) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (COMMON : Forall (kentry_ok (hl_segs L) E0 Mv) ANA.KNC).
    { unfold ANA.KNC. cbn [firstn CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      + eapply CL5.kword64_intro with (A := o) (z := b); [ev_start | clear - O3; lia | clear - O6; lia | exact V32 | replace o with (o + 0) by (clear; lia); exact (DO 0 ltac:(clear; lia) ltac:(clear; lia) ltac:(rewrite Z.add_0_r; exact Hw0))].
      + eapply CL5.kword64_intro with (A := o + 16) (z := b + cap); [ev_start | clear - O3; lia | clear - O6; lia | | exact (DO 16 ltac:(clear; lia) ltac:(clear; lia) Hw16)].
        rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap; lia].
      + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | unfold hid in O1; clear - O1 O6 FSLO CL; lia].
      + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact Ho8].
      + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |].
        intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Hosh j Hj)].
      + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in O5; clear - O5; lia].
      + eapply CL5.krange_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear - BHI B4 B3 SP1; lia].
      + eapply CL5.kalign_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear; lia | exact B16].
      + eapply CL5.krange_intro with (v := cap); [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia | clear - Hcap; lia].
      + eapply CL5.krange_intro with (v := cap - len); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap; lia].
      + eapply CL5.krange_intro with (v := len); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap; lia].
      + eapply CL5.kunk_intro with (A := sp - 4112) (N := 4112); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
      + eapply CL5.kwr_intro with (A := sp - 4112) (N := 4112); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
      + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
      + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
      + eapply CL5.kdisj_intro with (A1 := sp - 4112) (N1 := 4112) (A2 := o) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | unfold hid in O4; clear - O4 S2; lia]. }
    assert (KEND : i0 <> 2%nat -> kentry_ok (hl_segs L) E0 Mv (KWord (SA (EVar 10) 8) 8 (EAlu Instr.ALU_ADD (EVar 32) (EVar 33)))).
    { intros Hne. eapply CL5.kword64_intro with (A := o + 8) (z := b + len); [ev_start | clear - O3; lia | clear - O6; lia | | exact (DO 8 ltac:(clear; lia) ltac:(clear; lia) (Hw8 Hne))].
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hcap Hlen; lia]. }
    assert (KARG : i0 <> 3%nat -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 11) 0 4096)).
    { intros Hne. assert (U11 : bv_unsigned (ev E0 11) = a1v) by (change 11%nat with (ridx 11%bv); rewrite (EV 11%bv), (Ha1 Hne); apply u64_of_Z; clear - Ha1v; lia).
      eapply CL5.krange_intro with (v := a1v); [lin_eval; rw_atoms; clear; lia | clear - Ha1v; lia | clear - Ha1v; lia]. }
    split; [rewrite KR1; exact (regs_ok_id R _ _)|]. unfold know_ok. rewrite <- (firstn_skipn 18 (CC.cp_know c0)), KN1. apply Forall_app. split; [exact COMMON|].
    destruct i0 as [|[|[|[|i0]]]]; [.. | exfalso; clear - Hi0; lia]; injection Hc0 as <-; cbn [skipn CC.cp_know G.cp0 G.cp1 G.cp2 G.cp3]; (repeat (apply Forall_cons); [.. | apply Forall_nil]).
    + exact (KEND ltac:(discriminate)). + exact (KARG ltac:(discriminate)).
    + exact (KEND ltac:(discriminate)). + exact (KARG ltac:(discriminate)).
    + exact (KARG ltac:(discriminate)).
    + exact (KEND ltac:(discriminate)).
  - (* [comment removed for export] *)
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite FFSnil. replace (nth i0 G.BLS []) with (@nil (expr * expr)) by (do 4 (destruct i0 as [|i0]; [reflexivity|]); clear - Hi0; lia).
      cbn [CH2.den map app CHA.denF length]. split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + unfold XI. split; [left; reflexivity|]. split; [intros _; exact HSC0 | intros Hx; exfalso; clear - Hx; lia].
  - exact Hfp.
Qed.

(* [comment removed for export] *)
Lemma astk_mono : forall (M : word -> option byte) sp scr scr', 0 <= scr' <= scr -> CHA.astk ar M sp scr -> CHA.astk ar M sp scr'.
Proof.
  intros M sp scr scr' Hs (K1 & K2 & K3 & K4 & K5 & K6). split; [exact K1|]. split; [lia|]. split; [exact K3|]. split; [exact K4|]. split; [|exact K6].
  intros i Hi. replace (sp - scr' + i) with (sp - scr + (scr - scr' + i)) by lia. apply K5. lia.
Qed.
Lemma ahpres_widen : forall LB FF (M M' : word -> option byte) sp scr scr' W, 0 <= scr' <= scr -> CHA.astk ar M sp scr ->
  CHA.ahpres L ar LB FF sp scr' W M M' -> CHA.ahpres L ar LB FF sp scr W M M'.
Proof.
  intros LB FF M M' sp scr scr' W Hs (K1 & K2 & K3 & K4 & K5 & K6) HP.
  assert (HP0 : CHA.ahpres L ar LB FF sp scr W M M) by (split; [intros a _; reflexivity | split; [exact K5 | intros a _ _ Hd; exact Hd]]).
  apply (CRB.ahpres_trans L ar LB LB LB FF sp scr scr' W W W M M M' HP0 HP); [apply incl_refl | apply incl_refl | exact Hs | clear - K3 K4; lia | clear - K4; lia | clear - K2; lia | |];
    intros w a Hw Hin; exists w; split; assumption.
Qed.

Theorem annotate_increase_ok : PMSA.annotate_increase_spec L ar HI 842060.
Proof.
  intros LB FF LK cr A o b len cap n sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & (Hv0 & Hv8 & Hv16) & Hfr & Ho8 & Hsh & Hin & Hlen & Hn & Hle & HSC & _ & Hcap) Hcont.
  apply (annot_gen 0%nat ltac:(lia) LB FF LK cr A o b len cap n sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
  - cbn [omv nmv]. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) (b, cap) Hin) as ((_ & _ & _ & B3 & _) & _). cbn [snd] in B3.
    split; [exact Ha0|]. split; [intros _; exact Ha1|]. split; [exact Hv0|]. split; [intros _; exact Hv8|]. split; [exact Hv16|]. split; [left; exact Hfr|]. split; [exact Ho8|]. split; [exact Hsh|].
    split; [exact Hin|]. do 5 (split; [lia|]). exact HSC.
  - intros fx' R' M' model' LB' cr' LBk W HFP' HPost. exact (Hcont fx' R' M' model' LB' cr' LBk W HFP' HPost).
Qed.
Theorem annotate_shrink_ok : PMSA.annotate_shrink_spec L ar HI 730684.
Proof.
  intros LB FF LK cr A o b len old cap sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & (Hv0 & Hv8 & Hv16) & Hfr & Ho8 & Hsh & Hin & Hlen & Hold & HSC & _ & Hcap) Hcont.
  apply (annot_gen 1%nat ltac:(lia) LB FF LK cr A o b len cap old sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
  - cbn [omv nmv]. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) (b, cap) Hin) as ((_ & _ & _ & B3 & _) & _). cbn [snd] in B3.
    split; [exact Ha0|]. split; [intros _; exact Ha1|]. split; [exact Hv0|]. split; [intros _; exact Hv8|]. split; [exact Hv16|]. split; [left; exact Hfr|]. split; [exact Ho8|]. split; [exact Hsh|].
    split; [exact Hin|]. do 5 (split; [lia|]). exact HSC.
  - intros fx' R' M' model' LB' cr' LBk W HFP' HPost. exact (Hcont fx' R' M' model' LB' cr' LBk W HFP' HPost).
Qed.
Theorem annotate_new_ok : PMSA.annotate_new_spec L ar HI 841184.
Proof.
  intros LB FF LK cr A o b cap n sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & Hv0 & Hv16 & Hco & Ho8 & Hsh & Hin & Hn & Hcap & HSC & _) Hcont.
  unfold PMSA.ANEW_SCR, PMSA.ANNOT_SCR in *.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) (b, cap) Hin) as ((_ & _ & _ & B3 & _) & _). cbn [snd] in B3.
  apply (annot_gen 2%nat ltac:(lia) LB FF LK cr A o b 0 cap n sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp (astk_mono M sp (32 + 4096) 4112 ltac:(lia) Hstk) Hroom Hffrs).
  - cbn [omv nmv]. split; [exact Ha0|]. split; [intros _; exact Ha1|]. split; [exact Hv0|]. split; [intros X; exfalso; apply X; reflexivity|]. split; [exact Hv16|]. split; [exact Hco|].
    split; [exact Ho8|]. split; [exact Hsh|]. split; [exact Hin|]. do 5 (split; [lia|]). exact HSC.
  - intros fx' R' M' model' LB' cr' LBk W LK' A' HFP' HPost HRP HP. exact (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP' HPost HRP (ahpres_widen _ _ _ _ _ (32 + 4096) 4112 _ ltac:(lia) Hstk HP)).
Qed.
Theorem annotate_delete_ok : PMSA.annotate_delete_spec L ar HI 730524.
Proof.
  intros LB FF LK cr A o b len cap sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & (Hv0 & Hv8 & Hv16) & Hco & Ho8 & Hsh & Hin & Hlen & Hcap & HSC & _) Hcont.
  unfold PMSA.ANEW_SCR, PMSA.ANNOT_SCR in *.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) (b, cap) Hin) as ((_ & _ & _ & B3 & _) & _). cbn [snd] in B3.
  apply (annot_gen 3%nat ltac:(lia) LB FF LK cr A o b len cap 0 sp r fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp (astk_mono M sp (32 + 4096) 4112 ltac:(lia) Hstk) Hroom Hffrs).
  - cbn [omv nmv]. split; [exact Ha0|]. split; [intros X; exfalso; apply X; reflexivity|]. split; [exact Hv0|]. split; [intros _; exact Hv8|]. split; [exact Hv16|]. split; [exact Hco|].
    split; [exact Ho8|]. split; [exact Hsh|]. split; [exact Hin|]. do 5 (split; [lia|]). exact HSC.
  - intros fx' R' M' model' LB' cr' LBk W LK' A' HFP' HPost HRP HP. exact (Hcont fx' R' M' model' LB' cr' LBk W LK' A' HFP' HPost HRP (ahpres_widen _ _ _ _ _ (32 + 4096) 4112 _ ltac:(lia) Hstk HP)).
Qed.
Print Assumptions annotate_new_ok.
End AnnotateOk.
