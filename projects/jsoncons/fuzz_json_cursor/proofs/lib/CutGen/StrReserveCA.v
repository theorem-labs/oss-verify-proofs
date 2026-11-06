(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_strres_casan_T Cut_strres_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_strres_casan.
Module GT := Cut_strres_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module SRA.
Definition PC_OPNEW : Z := 1358140.
Definition PC_MM : Z := 519788.
Definition RETPC : Z := 984384.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10. Definition nbE := EVar 44.
Definition IA (k : Z) : expr := EAlu Instr.ALU_ADD oE (ELit k).
Definition BLKS (i : nat) : list (expr * expr) := if Nat.eqb i 0 then [] else [(nbE, ELit 264)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1427896) 8 (ELit SBz)].
Definition NEWS_MM : list kentry := STAT ++ [KZero (SA nbE 0) (ELit 1)].
Definition CPF : list SGP.region := [(EVar 2, -4368, ELit 4368); (oE, 0, ELit 24)].
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (CH2.blocks_eqb (nth i G.BLS []) (BLKS i) && CH2.blocks_eqb (nth j G.BLS []) (BLKS j) && CHA.foot_chk GT.NF G.HDECL c (BLKS i) [] &&
              if Z.eqb pc PC_OPNEW then
                let nx := (CC.cp_nx cj - APC.NCS)%nat in let news := news_of (nx + 4) cj in
                (Z.eqb (SR.ps_pc ps) PC_OPNEW && Nat.eqb i 0 && Nat.eqb j 1 && Nat.eqb nx 40
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 [] [] [] news None c ps cj [] [] (BLKS 1%nat) [])
                 && CRB.fresh_news_ok 65536 7024640 G.HDECL GT.SCELLS GT.GLO GT.GHI cells nx [] [] (nx + 4) (ELit 264) news
                 && CL.ps_reg_is ps 10 (ELit 264))%bool
              else if Z.eqb pc PC_MM then
                (Z.eqb (SR.ps_pc ps) PC_MM && Nat.eqb i 1 && Nat.eqb j 2 && CBA.regions_eqb (CC.cp_F c) CPF && Nat.leb 45 (CC.cp_nx c)
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 (BLKS 1%nat) [] [(nbE, 0, ELit 1)] NEWS_MM (Some nbE) c ps cj (BLKS 1%nat) [] (BLKS 2%nat) [])
                 && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 (IA 1) && CL.ps_reg_is ps 12 (ELit 1)
                 && has cells (KZero (SA (CHA.SRL3 oE) SBz) (ELit 3)) && has cells (KWord (SA oE 0) 8 (ELit 0)))%bool
              else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && Nat.eqb i 2 && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (BLKS i) [] && CH2.blocks_eqb (nth i G.BLS []) (BLKS i)
           && CBA.regions_eqb (CC.cp_F c) CPF && Nat.leb 45 (CC.cp_nx c)
           && has cells (KWord (SA oE 0) 8 (ELit 265)) && has cells (KWord (SA oE 8) 8 (ELit 0)) && has cells (KWord (SA oE 16) 8 nbE) && has cells (KZero (SA nbE 0) (ELit 1)))%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End SRA.

Section StrReserveOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis OPNEW_OK : PMSA.opnew_specA L ar HI SRA.PC_OPNEW.
Hypothesis MEMMOVE_LIBC : amemcpy_spec_at L ar SCFG HI SRA.PC_MM false.

Lemma FFSnil : forall i, nth i SRA.FFS [] = [].
Proof. intros i. unfold SRA.FFS. do 3 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma est0 : forall E k, 0 <= k -> estart E (SA (ELit 0) k) = k.
Proof. intros E k Hk. unfold estart. cbn [a_base a_off edenot]. rewrite u64_of_Z by lia. lia. Qed.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.

Theorem str_reserve_ok : PMSA.str_reserve_specA L ar HI 983892.
Proof.
  intros LB FF LK cr A o sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Z0 & Z8 & Z16 & (Ofr & O8 & Osh) & Hstksh & CRD) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.stksh, PMSA.u64 in *. change (256 + (16 + 4096)) with 4368 in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYHN : hl_img_lo L <= 65536 /\ 7024640 <= hl_img_hi L) by (rewrite ILO, IHI; clear; lia).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM.

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as STT.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar _ FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (SHR : forall p k a, 0 <= p -> 0 < k -> p + k <= 2 ^ 47 -> in_shadow_of p k a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  assert (DEFO : forall LBx LKx crx Ax (Mx : mem) Vx, ri_inv HI LBx FF LKx crx Ax Mx Vx -> L5.defined Mx o 24).
  { intros LBx LKx crx Ax Mx Vx HHx. destruct Ofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by (clear; lia). apply FD. clear - Hq F1 F2. lia. }
  assert (DO : L5.defined M o 24) by exact (DEFO _ _ _ _ _ _ HH).

  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 256) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4368) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (RFr : CHA.rng_facts L ar LB FF) by exact RFx.
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFr Ofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (UOK : forall k, 0 <= k -> k <= 24 -> bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit k))) = o + k).
  { intros k K0 K1. cbn [edenot]. rewrite AX2S.u_add64, U10, (u64_of_Z k) by (clear - K0 K1; lia). apply Z.mod_small. clear - K0 K1 O3 O6; lia. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFr Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => cr1 = (if (i =? 0)%nat then cr else adebit L cr 264)).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) => (1 <= i)%nat -> PMSA.afresh L ar LB FF M1 (CL5A.uv E SRA.nbE) 264).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ SRA.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM. unfold PMSA.cfg. replace 983892 with (CC.cp_pc G.cp0) by vmc_refl.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SRA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact SRA.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    assert (UVE : forall E e z, env_agree GT.NF E0 E -> APC.expr_vars_lt GT.NF e = true -> CL5A.uv E0 e = z -> CL5A.uv E e = z).
    { intros E e z Hag Hv Hz. rewrite (CL5A.uv_agree GT.NF E0 E e Hag Hv). exact Hz. }
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SRA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.

    assert (LAGF : forall c ps0 E' R' A1 (M1 : mem) m1 (M' : mem) m' a, CBA.regions_eqb (CC.cp_F c) SRA.CPF = true -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
        env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 -> (a + 1 <= sp - 4368 \/ sp <= a) -> (a + 1 <= o \/ o + 24 <= a) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros c ps0 E' R' A1 M1 m1 M' m' a YF HLF HagE' Ha N1 N2. apply CBA.regions_eqb_eq in YF.
      apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF (Z_to_bv 64 a)). rewrite YF. unfold SRA.CPF, SGP.outside.
      assert (Wsp : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
      assert (WR : bv_unsigned (edenot E' SRA.oE) = o) by (unfold SRA.oE; cbn [edenot]; rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
      constructor; [unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite Wsp; rewrite !u64_of_Z by (clear - Ha; lia); clear - N1; lia|].
      constructor; [unfold estart, elenZ; cbn [a_base a_off]; rewrite WR; cbn [edenot]; rewrite !u64_of_Z by (clear - Ha; lia); clear - N2; lia|]. constructor. }
    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ SRA.leaf_ok _ _ _ _ _ HIL) as X. unfold SRA.leaf_chk in X.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X XK]. apply andb_prop in X as [X YF]. apply andb_prop in X as [YBi YBj]. apply CH2.blocks_eqb_eq in YBi, YBj.
      destruct (Z.eqb_spec pc SRA.PC_OPNEW) as [->|Hne1].
      {
        cbv zeta in XK. apply andb_prop in XK as [XK Y10]. apply andb_prop in XK as [XK YNEWS]. apply andb_prop in XK as [XK Y5]. apply andb_prop in XK as [XK YN]. apply andb_prop in XK as [XK Yj].
        apply andb_prop in XK as [Y0 Yi]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi, Yj, YN. subst i j.
        lazymatch type of Y5 with SRA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HcB : CHA.curB LB G.BLS 0%nat E = LB) by (unfold CHA.curB; rewrite YBi; reflexivity).
        assert (HcF : CHA.curF FF sp SRA.FFS 0%nat E = FF) by reflexivity.
        refine (CALLEE SRA.PC_OPNEW 4112 0%nat [] [] (SRA.news_of 44%nat cj) None 0 0%nat c ps0 1%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, YBi, YBj; rewrite YN in Hchk; exact Hchk | rewrite !FFSnil; reflexivity | cbn; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        assert (NXeq : CH2.ci_nx ci = 40%nat) by (destruct HV as (_ & _ & _ & _ & HV5); clear - HV5 YN; unfold APC.NCS in *; lia).
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        eexists. eexists. split; [exact (OPNEW_OK LB FF LK1 cr A1 264 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|].
        split; [split; [exact (REG 10%nat (ELit 264) 264 Y10 eq_refl) | split; [clear; lia | exact CRD]]|].
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (u & Hu & Hfresh & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        pose proof Hfresh as (Hrng & Hbap & Hfap & Hdef & Hsh). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)).
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        assert (UR : 0 <= u < 2 ^ 64) by (clear - NQ5 NQ7 NQ3; lia).
        assert (Hvu : CL5A.uv E2 SRA.nbE = u).
        { unfold CL5A.uv, SRA.nbE. cbn [edenot]. pose proof (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2) as G0. cbn [length] in G0. rewrite Nat.add_0_r in G0.
          unfold E2. rewrite NXeq in G0 |- *. change (40 + 4)%nat with 44%nat in G0. unfold PMSA.a0 in Hu. rewrite G0, Hu. apply u64_of_Z. exact UR. }
        assert (HagE2 : env_agree GT.NF E0 E2).
        { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
        split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
        assert (HBj : CHA.curB LB G.BLS 1%nat E2 = (u, 264) :: LB).
        { unfold CHA.curB. rewrite YBj. unfold SRA.BLKS. cbn [Nat.eqb CH2.den map app fst snd]. change (bv_unsigned (edenot E2 SRA.nbE)) with (CL5A.uv E2 SRA.nbE). rewrite Hvu. cbn [edenot]. rewrite u64_of_Z by (clear; lia). reflexivity. }
        split; [rewrite HBj; exact HH2|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity|].
        split; [unfold XI; intros _; rewrite Hvu; exact Hfresh|].
        intros X0 HX0 _.
        refine (CRB.news_sound L ar C HI HIok LYI 65536 7024640 LYHN GT.NF E0 LB FF sp G.HDECL WW STKF SCRP NF32 U2 WOK CRS_OK WRS_OK GT.SCELLS GT.GLO GT.GHI SCOK GOTOK
                  E' E2 (CH2.ci_nx ci) (SR.ps_cells ps0) [] [] 44%nat (ELit 264) M' M2 A1 A2 m' m2 LB ((u, 264) :: LB) FF FF LK1 LK2 cr (adebit L cr 264) u 264 (SRA.news_of 44%nat cj)
                  HagE' Hag2 HK HH1 eq_refl eq_refl Hvu _ (elit E' 264 ltac:(clear; lia)) Hrng Hbap Hfap Hdef Hsh HH2 (or_introl eq_refl) _ X0 HX0); [rewrite NXeq; reflexivity | rewrite NXeq; rewrite YN in YNEWS; exact YNEWS]. }
      destruct (Z.eqb_spec pc SRA.PC_MM) as [->|Hne2]; [|exfalso; clear - XK; discriminate XK].
      {
        apply andb_prop in XK as [XK Yz0]. apply andb_prop in XK as [XK Ysh]. apply andb_prop in XK as [XK Y12]. apply andb_prop in XK as [XK Y11]. apply andb_prop in XK as [XK Y10].
        apply andb_prop in XK as [XK Y5]. apply andb_prop in XK as [XK Ynx]. apply andb_prop in XK as [XK YFX]. apply andb_prop in XK as [XK Yj]. apply andb_prop in XK as [Y0 Yi].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Yi, Yj. apply Nat.leb_le in Ynx. subst i j.
        lazymatch type of Y5 with SRA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _) & _).
        unfold XI in HXi. destruct (HXi ltac:(clear; lia)) as (Hrng & Hbap & Hfap & Hdef & Hsh). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in NQ6.
        set (nb := CL5A.uv E SRA.nbE) in *.
        assert (HcB : CHA.curB LB G.BLS 1%nat E = (nb, 264) :: LB).
        { unfold CHA.curB. rewrite YBi. unfold SRA.BLKS. cbn [Nat.eqb CH2.den map app fst snd edenot]. rewrite u64_of_Z by (clear; lia). reflexivity. }
        assert (HcF : CHA.curF FF sp SRA.FFS 1%nat E = FF) by reflexivity.
        refine (CALLEE SRA.PC_MM 2560 0%nat (SRA.BLKS 1%nat) [(SRA.nbE, 0, ELit 1)] SRA.NEWS_MM (Some SRA.nbE) 0 1%nat c ps0 2%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | cbn; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = adebit L cr 264) by exact HC1. subst cr1.
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (CELL : forall X0, SRA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SRA.FFS Cred 0 1%nat E A1 M' m' HA') as Hoff.
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (W10 : CL5A.uv E' SRA.oE = o) by exact (UVE E' SRA.oE o HagE' eq_refl U10).
        assert (V44 : CL5A.uv E' SRA.nbE = nb) by (unfold CL5A.uv, SRA.nbE; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by (clear - Ynx; lia); reflexivity).
        assert (UK1 : CL5A.uv E0 (SRA.IA 1) = o + 1) by (unfold CL5A.uv, SRA.IA, SRA.oE; exact (UOK 1 ltac:(clear; lia) ltac:(clear; lia))).

        assert (Hdef' : L5.defined M' nb 264) by exact (L5.defined_grows M1 M' nb 264 (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) Hdef).
        assert (Hsh' : shadow_blk M' nb 264).
        { apply (PTA.shadow_blk_ag M1 M' (in_shadow_of nb 264)); [| clear; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ NQ16) | exact Hsh].
          intros a Ha. pose proof (SHR nb 264 a ltac:(clear - NQ0; lia) ltac:(clear; lia) NQ7 Ha) as SRa.
          apply (LAGF c ps0 E' R' A1 M1 m1 M' m' a YFX HLF HagE' ltac:(clear - SRa; lia)); [clear - SRa S2 CL; lia | unfold hid in O5; clear - SRa O5; lia]. }

        assert (DO' : L5.defined M' o 24) by exact (DEFO _ _ _ _ _ _ HH1).
        assert (SRC0 : byte_at M' (o + 1) 0).
        { pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Yz0) ltac:(unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' SRA.oE)) with (CL5A.uv E' SRA.oE); rewrite W10; clear; lia)) as G0.
          apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. replace (CL5A.uv E' (ELit 0)) with 0 in G0 by (unfold CL5A.uv; cbn [edenot]; rewrite u64_of_Z by (clear; lia); reflexivity).
          unfold L5.u64_at in G0. pose proof (L5C.rdn_bytes_at (hl_segs L) M' (word_to_le_bytes 8 (Z_to_bv 64 0)) o ltac:(clear - O3; lia) ltac:(change (Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 0)))) with 8; clear - O6; lia) G0) as BY.
          pose proof (BY 1%nat ltac:(cbn; clear; lia)) as B1. assert (E1 : nth 1 (map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 0))) 0 = 0) by vmc_refl. rewrite E1 in B1. change (Z.of_nat 1) with 1 in B1.
          exact (CL5A.u8_byte_at (hl_segs L) M' _ _ (DO' 1 ltac:(clear; lia)) B1). }
        eexists. eexists. split; [exact (CRC.memcpy_cps L ar HI PMSA.fp_ok SRA.PC_MM MEMMOVE_LIBC 2560 ((nb, 264) :: LB) FF LK1 (adebit L cr 264) A1 nb (o + 1) 1 [Z_to_bv 8 0] (sp + CH2.ci_csp ci) (CC.cp_pc cj) ltac:(rewrite SCRMEM; clear; lia))|].
        split.
        { unfold CRC.memcpy_pre. split; [exact (REG 10%nat SRA.nbE nb Y10 V44)|]. split; [exact (REG 11%nat (SRA.IA 1) (o + 1) Y11 (UVE E' (SRA.IA 1) (o + 1) HagE' eq_refl UK1))|]. split; [exact (REG 12%nat (ELit 1) 1 Y12 eq_refl)|].
          split; [exact (CRC.dst_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 nb 264 nb 1 HH1 (or_introl eq_refl) Hsh' ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))|].
          split.
          - unfold CRC.mem_src. split.
            { intros a Ha. left. replace (S a) with (S o + 0) by (unfold S; pose proof O8 as O8'; clear - Ha O8'; apply Z.mod_divide in O8'; [|lia]; destruct O8' as [q Hq]; rewrite Hq; replace a with (q * 8 + 1) by lia; rewrite Z.div_add_l, Z.div_mul by lia; change (1 / 8) with 0; lia).
              apply (CL5A.byte_full (ahid A1 m') M'). exact (CL5A.shz_elim (hl_segs L) E' _ SRA.oE 3 o (CELL _ Ysh) W10 ltac:(clear; lia) 0 ltac:(clear; lia)). }
            split; [clear - O3 O6; lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; unfold hid in O5; split; [clear - O3; lia|]; split; [clear - O5; lia | left; clear - O4 S2 S3 Hc1; lia]|].
            split; [intros q Hq; right; exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar _ _ _ _ o 24 (o + 1 + q) Ofr ltac:(clear - Hq; lia)))|].
            change (Z.to_nat 1) with (length [Z_to_bv 8 0]). apply (TKA.rdn_of_bytes (hl_segs L) M'). intros jj Hjj. destruct jj as [|jj]; [cbn [nth Z.of_nat]; rewrite Z.add_0_r; exact SRC0 | cbn in Hjj; exfalso; clear - Hjj; lia].
          - destruct Ofr as (f & Hf & F1 & F2). pose proof (Hfap f Hf) as AP. destruct AP as [AP|AP]; [left | right]; clear - AP F1 F2; lia. }

        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & HBY & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta.
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        assert (HagE2 : env_agree GT.NF E0 E2).
        { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
        assert (T44 : CL5A.uv E2 SRA.nbE = nb).
        { rewrite <- V44. unfold CL5A.uv, SRA.nbE. cbn [edenot]. rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Ynx; lia). reflexivity. }
        split; [rewrite Ha0'; unfold CL5A.uv in T44; rewrite <- T44; apply Z_to_bv_bv_unsigned|].
        split; [unfold SRA.BLKS; cbn [Nat.eqb CH2.den map app fst snd]; change (bv_unsigned (edenot E' SRA.nbE)) with (CL5A.uv E' SRA.nbE); rewrite V44; cbn [edenot]; rewrite u64_of_Z by (clear; lia); apply incl_refl|].
        split.
        { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (SRA.nbE, 0, ELit 1). split; [left; reflexivity|].
          unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. change (bv_unsigned (edenot E' SRA.nbE)) with (CL5A.uv E' SRA.nbE). rewrite V44. cbn [edenot]. rewrite u64_of_Z by (clear; lia). clear - Hin. lia. }
        split.
        { intros w a [<-|[]] Hin (Ka & Kc & Kw). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. assert (Ha' : nb <= a < nb + 264) by (clear - Hin; lia).
          exact (CHA.obj_not_client L ar LYI LB FF sp (CH.hd_scr G.HDECL) nb 264 a RFx (conj NQ5 (conj NQ6 NQ7)) ltac:(clear; lia) (CHA.mod8_of_16 _ NQ16) NQ4 NQ1 Hbap Hfap (or_introl Ha') Kc). }
        assert (HBj : CHA.curB LB G.BLS 2%nat E2 = (nb, 264) :: LB).
        { unfold CHA.curB. rewrite YBj. unfold SRA.BLKS. cbn [Nat.eqb CH2.den map app fst snd]. change (bv_unsigned (edenot E2 SRA.nbE)) with (CL5A.uv E2 SRA.nbE). rewrite T44. cbn [edenot]. rewrite u64_of_Z by (clear; lia). reflexivity. }
        split; [rewrite HBj; exact HH2|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity|].
        pose proof HP as (HP1 & _ & HP3).
        assert (KB : forall a, (nb <= a < nb + 264 /\ a <> nb) \/ in_shadow_of nb 264 a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
        { intros a Ha. apply HP1. destruct Ha as [[Ha Hne]|Ha].
          - split; [clear - Ha NQ5 NQ7; lia|]. split; [left; exists (nb, 264); split; [left; reflexivity | exact Ha]|]. intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hr Hne. lia.
          - pose proof (SHR nb 264 a ltac:(clear - NQ0; lia) ltac:(clear; lia) NQ7 Ha) as SRa. split; [clear - SRa; lia|]. split; [do 6 right; exists (nb, 264); split; [left; reflexivity | exact Ha]|].
            intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hr SRa NQ6. lia. }
        assert (DEF2 : L5.defined M2 nb 264).
        { intros q Hq. apply (HP3 (nb + q)); [clear - Hq NQ5 NQ7; lia | left; exists (nb, 264); split; [left; reflexivity | cbn [fst snd]; clear - Hq; lia] | exact (Hdef' q Hq)]. }
        split.
        { unfold XI. intros _. rewrite T44. split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split; [exact DEF2|].
          exact (PTA.shadow_blk_ag M' M2 (in_shadow_of nb 264) (fun a Ha => KB a (or_intror Ha)) nb 264 ltac:(clear; lia) (fun a Ha => Ha) (CHA.mod8_of_16 _ NQ16) Hsh'). }

        intros X0 HX0 _. unfold SRA.NEWS_MM, SRA.STAT in HX0. cbn [In app] in HX0.
        destruct HX0 as [<-|[<-|[<-|[]]]]; [apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity
                                        | apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity |].
        pose proof (TKA.bytes_of_copy2 (hl_segs L) M2 nb [0] HBY) as BY2.
        eapply CL5A.kzero_intro with (A := nb) (N := 1); [unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E2 SRA.nbE)) with (CL5A.uv E2 SRA.nbE); rewrite T44; clear; lia | exact (elit E2 1 ltac:(clear; lia)) | clear - NQ5; lia | clear - NQ7; lia | clear - NQ7; lia |].
        intros jj Hjj. replace (nb + jj) with nb by (clear - Hjj; lia). apply CL5A.byte_vis.
        - apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 _ HH2); [clear - NQ5 NQ7; lia | left; exists (nb, 264); split; [left; reflexivity | cbn [fst snd]; clear; lia] |].
          intros Hc. exfalso. pose proof (SHR (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) _ ltac:(clear - CL; lia) ltac:(clear - S2 S3 SP1; lia) ltac:(clear; lia) Hc) as SRa. clear - SRa NQ6. lia.
        - apply (CL5A.u8_byte_at (hl_segs L) M2); [replace nb with (nb + 0) by (clear; lia); exact (DEF2 0 ltac:(clear; lia))|].
          pose proof (BY2 0%nat ltac:(cbn; clear; lia)) as Y. cbn [nth Z.of_nat] in Y. rewrite Z.add_0_r in Y. exact Y. }
    +
      apply andb_prop in X as [X Yz]. apply andb_prop in X as [X Y16]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y0w]. apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YFX].
      apply andb_prop in X as [X YB]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Xbase]. apply andb_prop in X as [Ypc Yi].
      apply Z.eqb_eq in Ypc. apply Nat.eqb_eq in Yi. subst pc i. apply CH2.blocks_eqb_eq in YB. apply Nat.leb_le in Ynx.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      unfold XI in HXi. destruct (HXi ltac:(clear; lia)) as (Hrng & Hbap & Hfap & Hdef & Hsh). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in NQ6.
      set (nb := CL5A.uv E SRA.nbE) in *.
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS SRA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok SRA.RETPC 2%nat c ps0 _ Xbase _ (FFSnil 2%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact SRA.ret_at | rewrite (FFSnil 2%nat), YB; exact Xfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (CELL : forall X0, SRA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS SRA.FFS Cred 0 2%nat E A1 M' m' HA') as Hoff.
      assert (W10 : CL5A.uv E' SRA.oE = o) by exact (UVE E' SRA.oE o HagE' eq_refl U10).
      assert (V44 : CL5A.uv E' SRA.nbE = nb) by (unfold CL5A.uv, SRA.nbE; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by (clear - Ynx; lia); reflexivity).
      assert (Hcr1 : cr1 = adebit L cr 264) by exact HC1. subst cr1.
      assert (HB : CHA.curB LB G.BLS 2%nat E = (nb, 264) :: LB).
      { unfold CHA.curB. rewrite YB. unfold SRA.BLKS. cbn [Nat.eqb CH2.den map app fst snd edenot]. rewrite u64_of_Z by (clear; lia). reflexivity. }
      rewrite HB in HH1.
      assert (U64C : forall k v z, SRA.has (SR.ps_cells ps0) (KWord (SA SRA.oE k) 8 v) = true -> CL5A.uv E' v = z -> L5.u64_at (hl_segs L) M' (o + k) z).
      { intros k v z Hc Hz. apply (CL5A.u64_full (hl_segs L) _ Hoff). rewrite <- Hz. exact (CL5A.kword64_elim (hl_segs L) E' _ _ v (o + k) (CELL _ Hc) ltac:(unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' SRA.oE)) with (CL5A.uv E' SRA.oE); rewrite W10; reflexivity)). }
      assert (KBA : forall a, (nb <= a < nb + 264 \/ in_shadow_of nb 264 a) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. destruct Ofr as (f & Hf & F1 & F2). pose proof (Hfap f Hf) as AP.
        destruct Ha as [Ha|Ha].
        - apply (LAGF c ps0 E' R' A1 M1 m1 M' m' a YFX HLF HagE' ltac:(clear - Ha NQ5 NQ7; lia)); [clear - Ha NQ4 S2; lia | clear - Ha AP F1 F2; lia].
        - pose proof (SHR nb 264 a ltac:(clear - NQ0; lia) ltac:(clear; lia) NQ7 Ha) as SRa.
          apply (LAGF c ps0 E' R' A1 M1 m1 M' m' a YFX HLF HagE' ltac:(clear - SRa; lia)); [clear - SRa S2 CL; lia | unfold hid in O5; clear - SRa O5; lia]. }
      apply (Hcont fx' R' M' model2 ((nb, 264) :: LB) (adebit L cr 264) LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      exists nb. split; [|split; [|repeat split; reflexivity]].
      * unfold PMSA.str_at, PMLA.str_at, L5.lstr_long. cbn [length Z.of_nat]. split; [|split; [reflexivity | clear; lia]].
        split; [reflexivity|]. split; [replace o with (o + 0) by (clear; lia); exact (U64C 0 (ELit 265) 265 Y0w ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia))|].
        split; [exact (U64C 8 (ELit 0) 0 Y8 ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia))|]. split; [exact (U64C 16 SRA.nbE nb Y16 V44)|].
        split; [intros q Hq; cbn in Hq; exfalso; clear - Hq; lia|]. rewrite Z.add_0_r. apply CL5A.byte_at_u8. apply (CL5A.byte_full (ahid A1 m') M').
        replace nb with (nb + 0) by (clear; lia). exact (CL5A.kzero_elim (hl_segs L) E' _ _ _ nb 1 (CELL _ Yz) ltac:(unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' SRA.nbE)) with (CL5A.uv E' SRA.nbE); rewrite V44; clear; lia) (elit E' 1 ltac:(clear; lia)) 0 ltac:(clear; lia)).
      * split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split; [exact (L5.defined_grows M1 M' nb 264 (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) Hdef)|].
        exact (PTA.shadow_blk_ag M1 M' (in_shadow_of nb 264) (fun a Ha => KBA a (or_intror Ha)) nb 264 ltac:(clear; lia) (fun a Ha => Ha) (CHA.mod8_of_16 _ NQ16) Hsh).
  - reflexivity.
  -
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Ofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Ofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4368) 4368).
    { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DOv : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact DO).
    assert (DS : L5.defined Mv (sp - 4368) 4368) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (U64V : forall k, 0 <= k -> k + 8 <= 24 -> L5.u64_at (hl_segs L) M (o + k) 0 -> L5.u64_at (hl_segs L) Mv (o + k) 0).
    { intros k K0 K1 Hk. apply (CL5A.u64_vis (hl_segs L)); [clear - O3 K0; lia | clear - O6 K1; lia | exact (CL5A.visr_sub _ o 24 (o + k) 8 VO ltac:(clear - K0; lia) ltac:(clear - K1; lia)) | exact Hk]. }
    assert (REGS : regs_ok E0 (CC.cp_regs G.cp0) R).
    { intros rr. unfold sr_get. destruct (bv_eqb rr 0) eqn:Hr0.
      - assert (rr = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; clear - Hr0; lia). subst rr. unfold getr. rewrite Hr0. reflexivity.
      - unfold E0, reg_ev. rewrite <- (ridx_roundtrip rr) at 1. pose proof (ridx_range rr) as Hlt. set (nn := ridx rr) in *. clearbody nn.
        let l := eval vm_compute in (CC.cp_regs G.cp0) in change (CC.cp_regs G.cp0) with l.
        do 32 (destruct nn as [|nn]; [cbn [nth edenot ev Nat.ltb Nat.leb]; first [reflexivity | rewrite <- Ha1; reflexivity] |]). exfalso. clear - Hlt. lia. }
    split; [exact REGS|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := o) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | replace o with (o + 0) by (clear; lia); apply (U64V 0); [clear; lia | clear; lia | rewrite Z.add_0_r; exact Z0]].
    + eapply CL5.kword64_intro with (A := o + 8) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | apply (U64V 8); [clear; lia | clear; lia | exact Z8]].
    + eapply CL5.kword64_intro with (A := o + 16) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | apply (U64V 16); [clear; lia | clear; lia | exact Z16]].
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia | intros j Hj; apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Osh j ltac:(change (24 / 8) with 3; exact Hj))]].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.kunk_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4368) (N := 4368); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4368) (N1 := 4368) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. cbn [nth G.BLS SRA.FFS app CHA.denF CH2.den map length].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; cbn [Nat.eqb]; reflexivity | exact Hroom].
    + unfold XI. intros H1. exfalso. clear - H1. lia.
  - exact Hfp.
Qed.

End StrReserveOk.
