(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutInlA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_decstr_cboth_T Cut_decstr_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_decstr_cboth.
Module GT := Cut_decstr_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module DSA.
Definition PC_SM : Z := 413656. Definition PC_STRTOD : Z := 1333096. Definition PC_FCL : Z := 805824. Definition RETPC : Z := 806080.
Definition TP : Z := 6888848. Definition ERRNO : Z := 6888684.
Definition SBz : Z := 2147450880.
Definition SE := EVar 10. Definition LE := EVar 11. Definition DE := EVar 12. Definition FLE := EVar 40. Definition FE := EVar 45.
Definition FR : expr * Z * Z := (FE, 1, -160).
Definition FFS : list (list (expr * Z * Z)) := [[]; [FR]; [FR]; [FR]].
Definition CPF0 : list SGP.region := [(EVar 2, -9120, ELit 9120); (DE, 0, ELit 8)].
Definition CPF1 : list SGP.region := CPF0 ++ [(FE, 0, ELit 24); (FE, 32, ELit 88); (CHA.SRL3 FE, SBz, ELit 16)].
Definition CPFX : list SGP.region := CPF1 ++ [(FLE, 0, ELit 1)].
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz); KWord (SA (ELit 0) 1432832) 4 (ELit 1)].
Definition FLAG : list kentry := [KWord (SA FE 120) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition NEWS_F : list kentry := STAT ++ FLAG.
Definition SLE : expr := EAlu Instr.ALU_ADD SE LE.
Definition ENDC : kentry := KWord (SA FE 32) 8 SLE.
Definition NEWS_S : list kentry := STAT ++ [ENDC] ++ FLAG.
Definition STRTOD_W : list SGP.region := [(FE, 32, ELit 8); (ELit 0, ERRNO, ELit 4)].
Definition A1X (x : expr) : expr := EAlu Instr.ALU_AND (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SLTU x (ELit 1)) (ELit (-1))) (ELit 34).
Definition has := CC.has_cell.
Definition sm_ok (ps : SR.post_spec) (i : nat) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok 7028736 G.HDECL (SR.ps_cells ps) 40 (nth i G.BLS []) (nth i FFS []) 1 45 40 X)%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      if Z.eqb pc RETPC then
        (Nat.eqb i 3 && CBA.exit_base_chk GT.NF RETPC c ps && CBA.regions_eqb (CC.cp_F c) CPFX && Nat.ltb 45 (CC.cp_nx c)
         && match CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) with Some fle => expr_eqb fle FLE | None => false end
         && has cells (KWord (SA FLE 0) 1 (ELit 0)) && CL.ps_reg_is ps 10 SLE && CL.ps_reg_is ps 11 (A1X (EAlu Instr.ALU_AND (EVar 74) (ELit 129))))%bool
      else if Z.eqb pc PC_FCL then
        (Nat.eqb i 2 && Z.eqb (SR.ps_pc ps) PC_FCL && CBA.regions_eqb (CC.cp_F c) CPF1 && Nat.ltb 45 (CC.cp_nx c)
         && match nth_error G.CPS 3 with Some cj => CIA.inl1_chk GT.NF c ps cj 4 10 | None => false end
         && CIA.same_chk GT.NF G.HDECL c (nth 2 G.BLS []) (nth 3 G.BLS []) (nth 2 FFS []) (nth 3 FFS []))%bool
      else
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match nth_error G.CPS j with
            | Some cj =>
                (Z.eqb (SR.ps_pc ps) pc &&
                 if Z.eqb pc PC_SM then (Nat.eqb i 0 && Nat.eqb j 1 && CBA.regions_eqb (CC.cp_F c) CPF0
                                        && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                        && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth i G.BLS []) (nth i FFS []) [] (List.filter (sm_ok ps i) (CC.cp_know cj)) None c ps cj
                                                   (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                           | Some ci => (Nat.eqb (CH2.ci_nx ci) 40 && Z.eqb (CH2.ci_csp ci) (-160))%bool | None => false end)
                 else if Z.eqb pc PC_STRTOD then (Nat.eqb i 1 && Nat.eqb j 2 && CBA.regions_eqb (CC.cp_F c) CPF1 && Nat.ltb 45 (CC.cp_nx c)
                                        && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                        && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 8944 0 [] (nth i FFS []) STRTOD_W NEWS_S None c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                           | Some ci => Z.eqb (CH2.ci_csp ci) (-160) | None => false end
                                        && CL.ps_reg_is ps 10 SE && CL.ps_reg_is ps 11 (EAlu Instr.ALU_ADD FE (ELit 32)) && has cells (KWord (SA FE 120) 8 FLE))
                 else false)%bool
            | None => false end
        | None => false end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma site_fcl : CIA.site_fclass_chk RSEGS PC_FCL = Some 10%nat.
Proof. vmc_refl. Qed.
Lemma ffs_i : forall i, (1 <= i <= 3)%nat -> nth i FFS [] = [FR].
Proof. intros i Hi. do 4 (destruct i as [|i]; [first [reflexivity | lia]|]). lia. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = [].
Proof. intros i. do 4 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma c3 : nth_error G.CPS 3 = Some (nth 3 G.CPS G.cp0).
Proof. reflexivity. Qed.

Lemma a1_val : forall E x, CL5A.uv E (A1X x) = 0 \/ CL5A.uv E (A1X x) = 34.
Proof.
  intros E x. unfold CL5A.uv, A1X. cbn [edenot]. rewrite u_and64, u_add64, u_sltu64, !u_lit64. change two64 with (2 ^ 64). change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  change (bv_unsigned (Z_to_bv 64 34)) with 34. rewrite (Z.mod_small 1) by lia.
  destruct (bv_unsigned (edenot E x) <? 1); [left | right]; vm_compute; reflexivity.
Qed.
End DSA.

Section DecstrOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_cboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis SM1 : hl_stack_malloc L 1 = DSA.PC_SM.
Hypothesis TPV : hl_tp L = DSA.TP.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis STRTOD_OK : PMSA.strtod_specA L ar HI IC DSA.PC_STRTOD.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Theorem decstr_ok : PMSA.decstr_to_double_specA L ar HI IC 805428.
Proof.
  unfold PMSA.decstr_to_double_specA. intros LB FF LK cr A s dp sp r txt. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & Ha2 & Hsp32 & HIR & Hstksh & HTXT & HNUL & HNUM & HLEN & HDEF & (bk & HinB0 & HBS & HSN) & HVD & HVO & HV8 & HVZ) Hcont.
  destruct bk as [b n]. cbn [fst snd] in HBS, HSN. rename HinB0 into HinB.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.DECSTR_SCR, PMSA.STRTOD_SCR, PML.STRTOD_SCR_V, PMSA.acobj, PMSA.u8, PMSA.stksh in *. change (176 + 8944) with 9120 in *.
  set (len := Z.of_nat (length txt)) in *.
  assert (LEN0 : 0 <= len) by (unfold len; clear; lia).

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : 7028736 <= hl_img_hi L /\ hl_img_lo L < FS_BYTES) by (rewrite ILO, IHI; unfold FS_BYTES; clear; lia).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WFT) as STOP.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.

  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (b, n) HinB) as ((KB0 & KB1 & KB16 & KB3 & KB4 & (KB5 & KB6 & KB7)) & KBdef & KBsha & KBbap & KBfap). cbn [fst snd] in KB0, KB1, KB16, KB3, KB4, KB5, KB6, KB7, KBdef, KBsha, KBbap, KBfap.
  rewrite ILO, IHI in KB1. unfold BIGSHADOW_LO, BIGSHADOW_HI in KB6.
  destruct (CL5A.acobj_rng L ar LB FF sp dp 8 RFx CSP HVO ltac:(clear; lia)) as (O3 & O6 & O5 & O1 & O4).
  unfold BIGSHADOW_LO, BIGSHADOW_HI in O5. change (hid (dp + 8 <= 2147446784 \/ 17594333495296 <= dp)) in O5. change (hid (ar_fs ar + 32 <= dp \/ ahl_ceil ar <= dp)) in O1. change (hid (dp + 8 <= ahl_ceil ar \/ sp <= dp)) in O4.

  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 s) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 len) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 dp) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = s) by (rewrite V10; apply u64_of_Z; clear - HBS HSN KB0 KB7 LEN0; lia).
  assert (U11 : bv_unsigned (ev E0 11) = len) by (rewrite V11; apply u64_of_Z; clear - HLEN LEN0; lia).
  assert (U12 : bv_unsigned (ev E0 12) = dp) by (rewrite V12; apply u64_of_Z; clear - O3 O6; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 9120) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(dp, 8); (hl_tp L - 164, 4)]). set (Wo := [(dp, 8)]).
  assert (WINC : incl Wo WW) by (intros w [<-|[]]; left; reflexivity).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.acobj_wok L ar LB FF sp _ dp 8 a RFx CSP HVO Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?U12 in Ha; rewrite u64_of_Z in Ha by (clear; lia).
    exists (dp, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (SHR : forall q n0 a, 0 <= q -> 0 < n0 -> q + n0 <= 2 ^ 47 -> in_shadow_of q n0 a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha;
      rewrite ?CL5A.estart_srl3' in Ha; unfold estart, elenZ, CL5A.uv in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?U12 in Ha; rewrite ?u64_of_Z in Ha by (clear; lia).
    destruct (CL5A.acobj_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) dp 8 a RFx CSP HVO ltac:(clear; lia) (CL5A.shreg_in_shadow dp 1 a HV8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1' & G2 & G3).
    split; [exact G1' | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[<-|[]]]; apply (L5A.aly_cells L C LAY); [left; reflexivity | right; left; reflexivity] | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  assert (KLB : forall a, b <= a < b + n -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. split; [clear - Ha KB0 KB7; lia|]. split; [left; exists (b, n); split; [exact HinB | cbn [fst snd]; exact Ha]|].
    intros w Hw Hin. unfold WW in Hw. unfold L5.in_rng in Hin. destruct Hw as [<-|[<-|[]]]; cbn [fst snd] in Hin.
    - destruct HVO as [(f & Hf & F1 & F2)|(R1 & R2)]; [pose proof (KBfap f (in_or_app _ _ _ (or_introl Hf))) as QF; clear - Hin Ha QF F1 F2; lia | clear - Hin Ha R1 KB4 S2; lia].
    - rewrite TPV in Hin. unfold DSA.TP in Hin. clear - Hin Ha KB1. lia. }
  assert (IMGK : forall a, 65536 <= a < 1400832 -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. split; [clear - Ha; lia|]. split.
    - right; right; left. rewrite ILO, IHI. split; [clear - Ha; lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia].
    - intros w Hw Hin. unfold WW in Hw. unfold L5.in_rng in Hin. destruct Hw as [<-|[<-|[]]]; cbn [fst snd] in Hin; [clear - Hin Ha O3 O1 FSLO CL; unfold hid in O1; lia | rewrite TPV in Hin; unfold DSA.TP in Hin; clear - Hin Ha; lia]. }
  assert (IR : L5.img_clear M 65536 1400832) by exact HIR.

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (FLF := fun (E1 : env) => ar_fs ar <= CL5A.uv E1 DSA.FLE < ar_fs ar + 11571200 /\ ~ aclient L ar LB FF sp (CH.hd_scr G.HDECL) (CL5A.uv E1 DSA.FLE)).
  set (XI := fun (i : nat) (E1 : env) (_ : list (Z * Z)) (_ : word -> option byte) (_ : Model) => (1 <= i)%nat -> FLF E1).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg IL. pose proof (CH2.leaves_all_sound _ _ _ DSA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  rewrite <- LS in FPM.
  change 805428 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS DSA.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact DSA.heap_ok.
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps0 j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  -
    intros i c kk ps0 pc IL. pose proof (CH2.leaves_all_sound _ _ _ DSA.leaf_ok _ _ _ _ _ IL) as X. unfold DSA.leaf_chk in X.
    assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hci & _); exact Hci).

    assert (FRM : forall E1 A1 M1 m1, (1 <= i <= 3)%nat ->
              CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DSA.FFS Cred 2 i E1 A1 M1 m1 ->
              let F := CL5A.uv E1 DSA.FE in
              CHA.curB LB G.BLS i E1 = LB /\ CHA.curF FF sp DSA.FFS i E1 = (F, 1, sp + -160 + 32) :: FF /\ env_agree GT.NF E0 E1 /\
              0 <= F /\ F + 128 <= 140737488355328 /\ F mod 8 = 0 /\ (F + 128 <= 2147446784 \/ 17594333495296 <= F) /\ ar_fs ar <= F /\ F + 128 <= ar_fs ar + 11571200 /\ fframes_apart F 128 FF
              /\ (forall u m, In (u, m) LB -> u + m <= F \/ F + 128 <= u) /\ L5.defined M1 F 128
              /\ (forall a, F <= a < F + 128 -> ~ aclient L ar LB FF sp (CH.hd_scr G.HDECL) a)).
    { intros E1 A1 M1 m1 Hi HA. cbv zeta.
      assert (HcB : CHA.curB LB G.BLS i E1 = LB) by (unfold CHA.curB; rewrite DSA.bls_i; reflexivity).
      assert (HcF : CHA.curF FF sp DSA.FFS i E1 = (CL5A.uv E1 DSA.FE, 1, sp + -160 + 32) :: FF) by (unfold CHA.curF; rewrite (DSA.ffs_i i Hi); reflexivity).
      pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _) & _). rewrite HcB, HcF in HHa.
      pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHa) as WFa. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFa) as RFa.
      destruct (CHA.rf_frm _ _ _ _ RFa _ (or_introl eq_refl)) as (G1 & G2 & G3 & _). unfold ff_addr, ff_class in G1, G2, G3. cbn [fst snd] in G1, G2, G3. change (ff_bytes 1) with 128 in G2.
      destruct (CHA.rf_fs _ _ _ _ RFa) as ((G0 & G4 & G5) & FS3 & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
      destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WFa _ (or_introl eq_refl)) as (_ & _ & _ & _ & Fdef & FAP). cbn [ff_addr ff_class fst snd ff_remove] in FAP, Fdef. rewrite Z.eqb_refl in FAP. change (ff_bytes 1) with 128 in FAP, Fdef.
      assert (FBL : forall u m, In (u, m) LB -> u + m <= CL5A.uv E1 DSA.FE \/ CL5A.uv E1 DSA.FE + 128 <= u).
      { intros u m Hum. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFa (u, m) Hum) as (_ & _ & _ & _ & Bfap). cbn [fst snd] in Bfap.
        pose proof (Bfap (CL5A.uv E1 DSA.FE, 1, sp + -160 + 32) (or_introl eq_refl)) as QF. cbn [ff_addr ff_class fst snd] in QF. change (ff_bytes 1) with 128 in QF. exact QF. }
      assert (FAP' : fframes_apart (CL5A.uv E1 DSA.FE) 128 FF) by (intros f Hf; apply FAP; apply in_or_app; left; exact Hf).
      split; [exact HcB|]. split; [exact HcF|]. split; [exact HagE|]. split; [clear - G0 G1; lia|]. split; [clear - G2 G5; lia|]. split; [exact (CHA.mod8_of_64 _ G3)|].
      split; [clear - G1 G2 G4; lia|]. split; [exact G1|]. split; [exact G2|]. split; [exact FAP'|]. split; [exact FBL|]. split; [intros q Hq; apply (Fdef q Hq)|].
      intros a Ha [Hb|[Hs|[Him|[Hf|[Hss|[Hfs|Hbs]]]]]].
      + destruct Hb as ((u & m) & Hum & Hr). cbn [fst snd] in Hr. pose proof (FBL u m Hum) as X1. clear - X1 Hr Ha. lia.
      + clear - Hs FS3 G2 Ha. lia.
      + rewrite IHI in Him. clear - Him Ha G1 FSLO. lia.
      + destruct Hf as (f & Hf & Hr & _). pose proof (FAP' f Hf) as X1. destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (_ & _ & _ & _ & X5). clear - X1 X5 Hr Ha. lia.
      + pose proof (SHR (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(clear - CL; lia) ltac:(clear - CL S2 S3 SP1; lia) ltac:(clear; lia) Hss) as X1. clear - X1 Ha G1 G2 G4. lia.
      + destruct Hfs as (f & Hf & Hr). destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (X1 & X2 & _ & _ & X5). destruct (CHA.rf_fs _ _ _ _ RFx) as ((R0 & _ & R6) & _).
        pose proof (SHR (ff_addr f) (ff_bytes (ff_class f)) a ltac:(clear - X1 R0; lia) ltac:(clear - X5; lia) ltac:(unfold FS_BYTES in X2, R6; clear - X2 R6; lia) Hr) as X6. clear - X6 Ha G1 G2 G4. lia.
      + destruct Hbs as ((u & m) & Hum & Hr). cbn [fst snd] in Hr. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, m) Hum) as ((B0 & _ & _ & B3 & _ & (_ & _ & B7)) & _). cbn [fst snd] in B0, B3, B7.
        pose proof (SHR u m a ltac:(clear - B0; lia) B3 B7 Hr) as X6. clear - X6 Ha G1 G2 G4. lia. }
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS DSA.FFS Cred 2 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.

    assert (LEAFK : forall E1 A1 M1 m1 E' R' M' m', (1 <= i <= 3)%nat -> CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DSA.FFS Cred 2 i E1 A1 M1 m1 ->
              env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> (45 < CC.cp_nx c)%nat ->
              (CC.cp_F c = DSA.CPF1 \/ CC.cp_F c = DSA.CPFX) -> FLF E1 ->
              bv_unsigned (ev E' 2) = sp /\ bv_unsigned (ev E' 10) = s /\ bv_unsigned (ev E' 11) = len /\ bv_unsigned (ev E' 12) = dp
              /\ bv_unsigned (ev E' 45) = CL5A.uv E1 DSA.FE /\ bv_unsigned (ev E' 40) = CL5A.uv E1 DSA.FLE
              /\ (forall X0, DSA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
              /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)
              /\ (forall a, CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))).
    { intros E1 A1 M1 m1 E' R' M' m' Hi HA Hag HLF Y45 YF HFL.
      pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DSA.FFS Cred 2 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
      assert (FZ : forall q, (q <? 40)%nat = true -> ev E' q = ev E0 q) by (intros q Hq; symmetry; apply (proj1 HagE'); unfold GT.NF; apply Nat.ltb_lt; exact Hq).
      destruct (FRM E1 A1 M1 m1 Hi HA) as (_ & _ & _ & F0 & F1 & F8 & F2 & F3 & F4 & FAP & FBL & FDEF & FNC). set (F := CL5A.uv E1 DSA.FE) in *. set (fl := CL5A.uv E1 DSA.FLE) in *.
      assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite (FZ 2%nat eq_refl); exact U2). assert (W12 : bv_unsigned (ev E' 12) = dp) by (rewrite (FZ 12%nat eq_refl); exact U12).
      assert (W45 : bv_unsigned (ev E' 45) = F) by (rewrite <- (proj1 Hag 45%nat) by exact Y45; reflexivity).
      assert (W40 : bv_unsigned (ev E' 40) = fl) by (rewrite <- (proj1 Hag 40%nat) by (clear - Y45; lia); reflexivity).
      pose proof (Z.div_pos F 8 F0 ltac:(clear; lia)) as D0. assert (D1 : F / 8 <= 2 ^ 44 - 16) by (apply Z.div_le_upper_bound; clear - F1; lia).
      assert (OUTF : forall a, 0 <= a < 2 ^ 64 -> (a < sp - 9120 \/ sp <= a) -> ~ (dp <= a < dp + 8) -> ~ (F <= a < F + 128) ->
                      ~ (F / 8 + DSA.SBz <= a < F / 8 + DSA.SBz + 16) -> a <> fl -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha Hs Hdp HF HFS HFL'. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). unfold SGP.outside. rewrite L5.unsigned_lit by exact Ha.
        destruct YF as [-> | ->]; unfold DSA.CPFX, DSA.CPF1, DSA.CPF0, DSA.DE, DSA.FE, DSA.FLE; cbn [app]; repeat (apply Forall_cons); try (apply Forall_nil);
          cbn [fst snd]; rewrite ?CL5A.estart_srl3, ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; unfold CL5A.uv, DSA.FE, DSA.FLE in F, fl; fold F fl; rewrite ?W2, ?W12, ?W45, ?W40;
          rewrite u64_of_Z by (clear; lia); clear - Ha Hs Hdp HF HFS HFL' D0 D1; lia. }
      assert (AKF : forall a, CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a (Ha & Hcl & Ho). rewrite SCRV in Hcl. destruct (CHA.rf_fs _ _ _ _ RFx) as ((R0 & R4 & R6) & FS3 & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in R4, R6, FS3.
        apply OUTF.
        - exact Ha.
        - destruct (Z_lt_dec a (ahl_ceil ar)) as [Hlt|Hge]; [left; clear - Hlt S2; lia|]. pose proof (CHA.client_high L ar LYI GT.NF sp G.HDECL STKF SCRP NF32 LB FF sp 9120 a RFx Hcl ltac:(clear - Hge; lia)) as NW. clear - NW. lia.
        - intros Hin. apply (Ho (dp, 8)); [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Hin; lia].
        - intros HFa. rewrite <- SCRV in Hcl. exact (FNC a HFa Hcl).
        - intros HFS. assert (ISF : in_shadow_of F 128 a) by (apply (CL5A.shreg_in_shadow F 16 a F8 ltac:(clear; lia)); unfold SB, DSA.SBz in *; clear - HFS; lia). unfold DSA.SBz in HFS.
          destruct Hcl as [Hb|[Hs|[Him|[Hf|[Hss|[Hfs|Hbs]]]]]].
          + destruct Hb as ((u & m) & Hum & Hr). cbn [fst snd] in Hr. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, m) Hum) as ((B0 & _ & _ & B3 & _ & (B5 & B6 & B7)) & _). cbn [fst snd] in B0, B3, B5, B6, B7.
            unfold BIGSHADOW_LO, BIGSHADOW_HI in B6. clear - Hr B6 HFS D0 D1. lia.
          + clear - Hs HFS D1 CL. lia.
          + rewrite IHI in Him. clear - Him HFS D0. lia.
          + destruct Hf as (f & Hf & Hr & _). destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (X1 & X2 & _). unfold FS_BYTES in X2. clear - Hr X1 X2 R4 HFS D0 D1. lia.
          + exact (CL5A.sh_apart2 F 128 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a F0 ltac:(clear - CL; lia) ltac:(clear; lia) ltac:(clear - CL S2 S3 SP1; lia) F8 C8 ltac:(left; clear - FS3 F4; lia) ISF Hss).
          + destruct Hfs as (f & Hf & Hr). destruct (CHA.rf_frm _ _ _ _ RFx f Hf) as (X1 & X2 & X3 & _ & X5).
            exact (CL5A.sh_apart2 F 128 (ff_addr f) (ff_bytes (ff_class f)) a F0 ltac:(clear - X1 R0; lia) ltac:(clear; lia) ltac:(clear - X5; lia) F8 (CHA.mod8_of_64 _ X3) (FAP f Hf) ISF Hr).
          + destruct Hbs as ((u & m) & Hum & Hr). cbn [fst snd] in Hr. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (u, m) Hum) as ((B0 & _ & B16 & B3 & _) & _). cbn [fst snd] in B0, B16, B3.
            pose proof (FBL u m Hum) as X1.
            exact (CL5A.sh_apart2 F 128 u m a F0 ltac:(clear - B0; lia) ltac:(clear; lia) B3 F8 (CHA.mod8_of_16 _ B16) ltac:(clear - X1; lia) ISF Hr).
        - intros Heq. apply (proj2 HFL). fold fl. rewrite <- Heq. rewrite SCRV. exact Hcl. }
      split; [exact W2|]. split; [rewrite (FZ 10%nat eq_refl); exact U10|]. split; [rewrite (FZ 11%nat eq_refl); exact U11|]. split; [exact W12|]. split; [exact W45|]. split; [exact W40|].
      split; [intros X0 HX0; apply CC.has_cell_In in HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)|].
      split; [intros q e0 z Hq Hz; rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq); rewrite <- Hz; symmetry; apply Z_to_bv_bv_unsigned|].
      exact AKF. }

    assert (NEWSF : forall E' E2 A1 A2 M' m' M2 m2 LKa LKb cra crb LBa F fl,
              ri_inv HI LB ((F, 1, sp + -160 + 32) :: FF) LKa cra A1 M' (vml_of m') -> ri_inv HI LBa ((F, 1, sp + -160 + 32) :: FF) LKb crb A2 M2 (vml_of m2) ->
              H_off_segments (hl_segs L) (ahid A1 m') ->
              0 <= F -> F + 128 <= 140737488355328 -> ar_fs ar <= F -> F + 128 <= ar_fs ar + 11571200 -> ar_fs ar <= fl < ar_fs ar + 11571200 ->
              bv_unsigned (ev E' 45) = F -> bv_unsigned (ev E' 40) = fl -> bv_unsigned (ev E2 45) = F -> bv_unsigned (ev E2 40) = fl ->
              kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA DSA.FE 120) 8 DSA.FLE) ->
              forall X0, In X0 DSA.NEWS_F -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0).
    { intros E' E2 A1 A2 M' m' M2 m2 LKa LKb cra crb LBa F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W45 W40 T45 T40 KFL X0 HX0.
      unfold DSA.NEWS_F, DSA.STAT, DSA.FLAG in HX0. cbn [app In] in HX0.
      pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) as WF2.
      assert (VFS : forall y, ar_fs ar <= y < ar_fs ar + 11571200 -> ahid A2 m2 (Z_to_bv 64 y) = false).
      { intros y Hy. apply (CHA.fs_vis L ar C HI HIok GT.NF 0 NF32 _ _ _ _ _ _ m2 y HH2); [destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _); unfold FS_BYTES in G3; clear - Hy G0 G3 CL SP1; lia | unfold FS_BYTES; exact Hy]. }
      destruct HX0 as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (F + 120) KFL ltac:(unfold estart, DSA.FE; cbn [a_base a_off edenot]; rewrite W45; reflexivity)) as G0.
        apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv, DSA.FLE in G0. cbn [edenot] in G0. rewrite W40 in G0.
        pose proof (PmHeapIfaceA.aio_flagptr _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 1 (sp + -160 + 32) (sp + -160 + 32) fl HH1 HH2 (or_introl eq_refl) (or_introl eq_refl)) as FP.
        change (ff_bytes 1) with 128 in FP. replace (F + 128 - 8) with (F + 120) in FP by (clear; lia). specialize (FP G0).
        eapply CL5.kword64_intro with (A := F + 120) (z := fl); [unfold estart, DSA.FE; cbn [a_base a_off edenot]; rewrite T45; reflexivity | clear - F0; lia | clear - F1; lia | |].
        + unfold DSA.FLE. cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned _ (ev E2 40)). f_equal. exact T40.
        + apply (CL5A.u64_vis (hl_segs L)); [clear - F0; lia | clear - F1; lia | | exact FP]. intros y Hy. apply VFS. clear - Hy F3 F4. lia.
      - eapply CL5.kwr_intro with (A := fl) (N := 1); [unfold estart, DSA.FLE; cbn [a_base a_off edenot]; rewrite T40; clear; lia | reflexivity | | | |].
        + destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & _). clear - HFL1 G0. lia.
        + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
        + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
        + intros y Hy. unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ (VFS (fl + y) ltac:(clear - Hy HFL1; lia))).
          pose proof (CHA.wf_fs_def _ _ _ _ _ _ _ _ WF2) as FD. replace (fl + y) with (ar_fs ar + (fl + y - ar_fs ar)) by (clear; lia). apply FD. unfold FS_BYTES. clear - Hy HFL1. lia. }
    destruct (Z.eqb_spec pc DSA.RETPC) as [->|HneR].
    2:{ destruct (Z.eqb_spec pc DSA.PC_FCL) as [->|HneF].
    2:{
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    apply andb_prop in X as [Y0 X]. apply Z.eqb_eq in Y0.
    destruct (Z.eqb_spec pc DSA.PC_SM) as [->|Hne1].
    {
      apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Yfoot]. apply andb_prop in X as [X YF]. apply andb_prop in X as [Y1 Y2].
      apply Nat.eqb_eq in Y1, Y2. subst i j. apply CBA.regions_eqb_eq in YF.
      lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      apply andb_prop in Y5 as [Ynx Ycsp]. apply Nat.eqb_eq in Ynx. apply Z.eqb_eq in Ycsp.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
      pose proof (CRA.smalloc_leaf_u L ar C HI HIok LYI LYR 7028736 LYH GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS DSA.FFS Cred 2 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                    G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil (fun _ => False) 1 (List.filter (DSA.sm_ok ps0 0) (CC.cp_know cj)) 0%nat c ps0 1%nat cj ci) as SML.
      rewrite (L5A.aly_scr_sm L C LAY), SM1 in SML.
      refine (SML ltac:(right; left; reflexivity) Hcj Hchk Y0 _ _ _ _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _).
      - rewrite Ynx, Ycsp. reflexivity.
      - rewrite !DSA.bls_i. reflexivity.
      - intros X0 HX0. apply filter_In in HX0 as [_ HX0]. unfold DSA.sm_ok in HX0. rewrite Ynx. left. exact HX0.
      - intros X0 E2 LB2 FF2 LK2 cr2 A2 M2 m2 [].
      - cbn [nth DSA.FFS length]. clear. lia.
      - intros Ea Eb cr1 Hc _. exact Hc.
      -
        intros R2 M2 m2 F fl LK' cr1 HRP Ha0' SMF HH2. unfold CHA.curB, CHA.curF in SMF. rewrite DSA.bls_i in SMF. cbn [nth DSA.FFS CH2.den CHA.denF map app] in SMF.
        destruct SMF as [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Zp]. rewrite Ynx. unfold XI. intros _.
        pose proof (CH2.retEx_ghost E' 40 [Z_to_bv 64 fl] R2 0 ltac:(cbn; clear; lia)) as G40. cbn [nth Nat.add] in G40.
        assert (T40 : CL5A.uv (CH2.retEx E' 40 [Z_to_bv 64 fl] R2) DSA.FLE = fl).
        { unfold CL5A.uv, DSA.FLE. cbn [edenot]. rewrite G40. apply u64_of_Z. unfold FS_BYTES in Z7. destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _). unfold FS_BYTES in G3. clear - Z7 G0 G3 CL SP1. lia. }
        unfold FLF. rewrite T40. split; [unfold FS_BYTES in Z7; exact Z7|]. intros Hc. apply Z8.
        eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact Hc] | intros y Hy; clear - Hy; lia]. }
    destruct (Z.eqb_spec pc DSA.PC_STRTOD) as [->|Hne2]; [|exfalso; cbn [orb] in X; discriminate X].
    {
      apply andb_prop in X as [X Ycell]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Yfoot]. apply andb_prop in X as [X Y3].
      apply andb_prop in X as [X YF]. apply andb_prop in X as [Y1 Y2].
      apply Nat.eqb_eq in Y1, Y2. subst i j. apply Nat.ltb_lt in Y3. apply CBA.regions_eqb_eq in YF.
      lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end. apply Z.eqb_eq in Y5. rename Y5 into Ycsp.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI]. pose proof (HXI ltac:(clear; lia)) as HXF. pose proof HXF as (HFL1 & HFL2).
      destruct (FRM E1 A1 M1 m1 ltac:(clear; lia) HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP & FBL & FDEF & FNC). set (F := CL5A.uv E1 DSA.FE) in *. set (fl := CL5A.uv E1 DSA.FLE) in *.
      refine (CALLEE DSA.PC_STRTOD 8944 0%nat [] DSA.STRTOD_W DSA.NEWS_S None 0 1%nat c ps0 2%nat cj ci Hcj Hchk Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [reflexivity | cbn; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      destruct (LEAFK E1 A1 M1 m1 E' R' M' m' ltac:(clear; lia) HA Hag HLF Y3 (or_introl YF) HXF) as (W2 & W10 & W11 & W12 & W45 & W40 & CELL & REG & AKF). fold F in W45. fold fl in W40.
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DSA.FFS Cred 2 1%nat E1 A1 M' m' HA') as Hoff.
      pose proof HA as (_ & _ & _ & _ & _ & Hfr1 & Hdf1).
      assert (MKB : forall a, b <= a < b + n -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a Ha; rewrite (AKF a (KLB a Ha)); exact (Hfr1 a (KLB a Ha))).
      assert (XF32 : bv_unsigned (edenot E' (EAlu Instr.ALU_ADD DSA.FE (ELit 32))) = F + 32) by (unfold DSA.FE; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - F0 F1; lia]).
      eexists. eexists. split; [exact (STRTOD_OK LB ((F, 1, sp + -160 + 32) :: FF) LK1 cr A1 s (F + 32) (sp + CH2.ci_csp ci) (CC.cp_pc cj) txt)|]. split.
      {
        unfold PMSA.a0, PMSA.a1, PMSA.u8, PMSA.acobj, CL5A.acobj, PMSA.STRTOD_SCR, PML.STRTOD_SCR_V. fold len.
        split; [exact (REG 10%nat _ s Y10 ltac:(cbn [edenot]; exact W10))|]. split; [exact (REG 11%nat _ (F + 32) Y11 XF32)|].
        split; [unfold PMLA.img_ro; cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth]; intros a Ha; rewrite (AKF a (IMGK a Ha)), (Hfr1 a (IMGK a Ha)); exact (IR a Ha)|].
        split; [apply (CL5A.bytes_same (hl_segs L) M M' s txt); [clear - HBS KB0; lia | fold len; clear - HSN KB7; lia | intros y Hy; apply MKB; fold len in Hy; clear - Hy HBS HSN; lia | exact HTXT]|].
        split; [apply (CL5A.u8_same (hl_segs L) M M' (s + len) 0); [clear - HBS KB0 LEN0; lia | clear - HSN KB7; lia | apply MKB; clear - HBS HSN LEN0; lia | exact HNUL]|].
        split; [exact HNUM|]. split; [exact HLEN|].
        split; [intros q Hq; apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF); replace (F + 32 + q) with (F + (32 + q)) by (clear; lia); apply (FDEF (32 + q)); clear - Hq; lia|].
        split; [left; exists (F, 1, sp + -160 + 32); split; [left; reflexivity | cbn [ff_addr ff_class fst snd]; change (ff_bytes 1) with 128; clear; lia]|].
        split; [left; rewrite Ycsp; clear - HSN KB4 S2; lia|].
        split; [pose proof (FBL b n HinB) as X1; clear - X1 HBS HSN LEN0; lia|].
        split; [rewrite TPV; unfold DSA.TP; clear - KB1 HBS HSN LEN0; lia|].
        split; [intros q Hq; apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF); apply (Hdf1 (s + q)); [clear - Hq HBS HSN KB0 KB7 LEN0; lia | left; exists (b, n); split; [exact HinB | cbn [fst snd]; clear - Hq HBS HSN; lia] | exact (HDEF q Hq)]|].
        exists (b, n). split; [exact HinB | cbn [fst snd]; split; [exact HBS | exact HSN]]. }

      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (HEND & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      exists []. split; [reflexivity|]. cbv zeta.
      pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
      set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
      destruct HV as (_ & _ & HV3 & _).
      assert (T45 : bv_unsigned (ev E2 45) = F) by (rewrite <- (proj1 Hag2 45%nat) by (clear - HV3 Y3; lia); exact W45).
      assert (T40 : bv_unsigned (ev E2 40) = fl) by (rewrite <- (proj1 Hag2 40%nat) by (clear - HV3 Y3; lia); exact W40).
      assert (T10 : bv_unsigned (ev E2 10) = s) by (rewrite <- (proj1 Hag2 10%nat) by (clear - HV3 Y3; lia); exact W10).
      assert (T11 : bv_unsigned (ev E2 11) = len) by (rewrite <- (proj1 Hag2 11%nat) by (clear - HV3 Y3; lia); exact W11).
      split; [exact I|].
      split; [cbn [CH2.den map app]; apply incl_refl|].
      split.
      { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
        - exists (DSA.FE, 32, ELit 8). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, DSA.FE. cbn [a_base a_off edenot]. rewrite W45. rewrite u64_of_Z by (clear; lia). clear - Hin. lia.
        - exists (ELit 0, DSA.ERRNO, ELit 4). split; [right; left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, DSA.ERRNO. cbn [a_base a_off edenot]. rewrite !u64_of_Z by (clear; lia).
          rewrite TPV in Hin. unfold DSA.TP in Hin. clear - Hin. lia. }
      split.
      { intros w a [<-|[<-|[]]] Hin (Ha & Hcl & Ho); unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
        - exact (FNC a ltac:(clear - Hin; lia) Hcl).
        - exact (Ho (hl_tp L - 164, 4) (or_intror (or_introl eq_refl)) Hin). }
      split; [unfold CHA.curB; rewrite DSA.bls_i; cbn [CH2.den map app]; exact HH2|].
      split; [reflexivity|].
      split.
      { unfold XI. intros _. unfold FLF. replace (CL5A.uv E2 DSA.FLE) with fl by (unfold CL5A.uv, DSA.FLE; cbn [edenot]; symmetry; exact T40). exact HXF. }
      intros X0 HX0 _. unfold DSA.NEWS_S in HX0. apply in_app_or in HX0 as [HX0|HX0]; [|apply in_app_or in HX0 as [HX0|HX0]].
      - exact (NEWSF E' E2 A1 A2 M' m' M2 m2 _ _ _ _ _ F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W45 W40 T45 T40 (CELL _ Ycell) X0 ltac:(unfold DSA.NEWS_F; apply in_or_app; left; exact HX0)).
      - destruct HX0 as [<-|[]]. unfold DSA.ENDC.
        eapply CL5.kword64_intro with (A := F + 32) (z := s + len); [unfold estart, DSA.FE; cbn [a_base a_off edenot]; rewrite T45; reflexivity | clear - F0; lia | clear - F1; lia | |].
        + rewrite <- (Z_to_bv_bv_unsigned _ (edenot E2 _)). f_equal. unfold DSA.SLE, DSA.SE, DSA.LE. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - HBS HSN KB0 KB7 LEN0; lia].
        + apply (CL5A.u64_vis (hl_segs L)); [clear - F0; lia | clear - F1; lia | | exact HEND].
          intros y Hy. apply (CHA.fs_vis L ar C HI HIok GT.NF 0 NF32 _ _ _ _ _ _ m2 (F + 32 + y) HH2); [clear - Hy F0 F1; lia | unfold FS_BYTES; clear - Hy F3 F4; lia].
      - exact (NEWSF E' E2 A1 A2 M' m' M2 m2 _ _ _ _ _ F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W45 W40 T45 T40 (CELL _ Ycell) X0 ltac:(unfold DSA.NEWS_F; apply in_or_app; right; exact HX0)). } }

    apply andb_prop in X as [X Ysame]. apply andb_prop in X as [X Yinl]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X YF]. apply andb_prop in X as [Yi Ypc].
    apply Nat.eqb_eq in Yi. subst i. apply Z.eqb_eq in Ypc. apply Nat.ltb_lt in Y3. apply CBA.regions_eqb_eq in YF. rewrite DSA.c3 in Yinl.
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
    refine (CIA.inl1_leaf L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS DSA.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK G.CPS K PMSA.fp_ok XI
              2%nat c ps0 3%nat _ 4 10%nat DSA.c3 Yinl Ysame ltac:(rewrite Ypc; unfold DSA.PC_FCL; clear; lia) ltac:(rewrite Ypc; unfold DSA.PC_FCL; clear; lia) ltac:(clear; lia) _ _ _
              fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH).
    + rewrite Ypc, LS. exact (CIA.fclass_step RSEGS DSA.PC_FCL 10 ltac:(unfold DSA.PC_FCL; clear; lia) ltac:(unfold DSA.PC_FCL; clear; lia) DSA.site_fcl).
    + intros Ea Eb Ra Rb Aa Ma ma M1a m1a E2 _ _ HXIa Haga _ Hag2. unfold XI in HXIa |- *. intros _. specialize (HXIa ltac:(clear; lia)).
      unfold FLF, DSA.FLE in HXIa |- *. rewrite (CL5A.uv_var (CC.cp_nx c) Eb E2 40 Hag2 ltac:(clear - Y3; lia)), (CL5A.uv_var (CC.cp_nx c) Ea Eb 40 Haga ltac:(clear - Y3; lia)). exact HXIa.
    + intros Ea E2 cr1 Hc _. exact Hc. }

    apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Yfl]. apply andb_prop in X as [X Yr]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X YF].
    apply andb_prop in X as [Yi Xbase]. apply Nat.eqb_eq in Yi. subst i. apply Nat.ltb_lt in Y3. apply CBA.regions_eqb_eq in YF.
    destruct (CHA.retire_chk GT.NF G.HDECL c (nth 3 G.BLS []) (nth 3 DSA.FFS [])) as [fle|] eqn:Hrc; [|discriminate]. apply expr_eqb_eq in Yr. subst fle.
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXI]. pose proof (HXI ltac:(clear; lia)) as HXF. pose proof HXF as (HFL1 & HFL2).
    destruct (FRM E1 A1 M1 m1 ltac:(clear; lia) HA) as (HcB & HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP & FBL & FDEF & FNC). set (F := CL5A.uv E1 DSA.FE) in *. set (fl := CL5A.uv E1 DSA.FLE) in *.
    refine (CRA.exit_retire L ar C HI HIok LYI LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS DSA.FFS Cred 2 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok DSA.RETPC 3%nat c ps0 DSA.FLE DSA.FE 1 (-160) _ Xbase (DSA.ffs_i 3 ltac:(clear; lia)) Hrc Yfl fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF HFL1 HFL2 _);
      [rewrite LS; exact DSA.ret_at |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE'. rewrite HcB in HH1. assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
    destruct (LEAFK E1 A1 M1 m1 E' R' M' m' ltac:(clear; lia) HA Hag HLF Y3 (or_intror YF) HXF) as (W2 & W10 & W11 & W12 & W45 & W40 & CELL & REG & AKF).
    rewrite SCRV in HP.
    apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    split; [exact (REG 10%nat _ (s + len) Y10 ltac:(unfold DSA.SLE, DSA.SE, DSA.LE; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - HBS HSN KB0 KB7 LEN0; lia]))|].
    split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | reflexivity]]]].
    destruct (DSA.a1_val E' (EAlu Instr.ALU_AND (EVar 74) (ELit 129))) as [Hc|Hc].
    + exists 0. split; [exact (REG 11%nat _ 0 Y11 Hc) | left; reflexivity].
    + exists 34. split; [exact (REG 11%nat _ 34 Y11 Hc) | right; left; reflexivity].
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VS : CL5A.visr (ahid A model) (sp - 9120) 9120).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    assert (VV : CL5A.visr (ahid A model) dp 8).
    { intros q Hq. destruct (CL5A.acobj_wok L ar LB FF sp 0 dp 8 (dp + q) RFx CSP HVO ltac:(clear - Hq; lia)) as (G1' & G2 & G3). exact (CLV _ G1' (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VVS : ahid A model (Z_to_bv 64 (S dp)) = false).
    { destruct (CL5A.acobj_sh_wok L ar LB FF sp 0 dp 8 (S dp) RFx CSP HVO ltac:(clear; lia) (CL5A.shreg_in_shadow dp 1 (S dp) HV8 ltac:(clear; lia) ltac:(unfold S; clear; lia))) as (G1' & G2 & G3).
      exact (CLV _ G1' (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 9120) 9120) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DV : L5.defined Mv dp 8) by (apply (CL5A.defined_vis _ M _ _ VV); exact HVD).
    assert (UVD : CL5A.uv E0 (EVar 12) = dp) by (unfold CL5A.uv; cbn [edenot]; exact U12).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); try (apply Forall_nil).
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.krange_intro with (v := len); [lin_eval; rw_atoms; clear; lia | clear - HLEN LEN0; lia | clear - HLEN LEN0; lia].
    + eapply CL5.krange_intro with (v := s); [lin_eval; rw_atoms; clear; lia | clear - HBS HSN KB0 KB7 LEN0; lia | clear - HBS HSN KB0 KB4 CL SP1 LEN0; lia].
    + eapply CL5.krange_intro with (v := s + len); [lin_eval; rw_atoms; clear; lia | clear - HBS HSN KB0 KB7 LEN0; lia | clear - HBS HSN KB0 KB4 CL SP1 LEN0; lia].
    + eapply CL5.kunk_intro with (A := dp) (N := 8); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DV].
    + eapply CL5.kwr_intro with (A := dp) (N := 8); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DV].
    + eapply CL5.krange_intro with (v := dp); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | unfold hid in O1; clear - O1 O6 FSLO CL S2; lia].
    + eapply CL5.kalign_intro with (v := dp); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact HV8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 dp UVD); [clear; lia | clear - O3 O6; lia |].
      intros j Hj. replace j with 0 by (clear - Hj; lia). rewrite Z.add_0_r. apply CL5A.byte_vis; [exact VVS | pose proof (HVZ 0 ltac:(clear; lia)) as X0; rewrite Z.add_0_r in X0; exact X0].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := dp) (N2 := 8); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.kunk_intro with (A := sp - 9120) (N := 9120); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 9120) (N := 9120); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact Hsp32].
    + eapply CL5.kdisj_intro with (A1 := sp - 9120) (N1 := 9120) (A2 := dp) (N2 := 8); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in O4; clear - O4 S2; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite DSA.bls_i. cbn [nth DSA.FFS CH2.den CHA.denF map app length Z.of_nat Z.sub].
      split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | replace (2 - 0) with 2 by (clear; lia); exact Hroom].
    + unfold XI. intros H1. exfalso. clear - H1. lia.
  - exact Hfp.
Qed.

End DecstrOk.
