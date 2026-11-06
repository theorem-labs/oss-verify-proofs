(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopSpecsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_detect_xasan_T Cut_detect_xasan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := Cut_detect_xasan.
Module GT := Cut_detect_xasan_T.
Abbreviation RSEGS := Pm4PlanKit.RSEGS.

Module DTA.
Definition PC_BCMP : Z := 440624.    (* [comment removed for export] *)
Definition RETPC : Z := 846596.      (* [comment removed for export] *)
Definition BOM_LO : Z := 165598.     (* [comment removed for export] *)
Definition BOM_HI : Z := 165614.     (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition CHE := EVar 10. Definition KE := EVar 11.
Definition FFS : list (list (expr * Z * Z)) := [[]; []; []; []; []; []; []; []; []].
Definition CPF0 : list SGP.region := [(EVar 2, -8256, ELit 8256)].
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1482488) 8 (ELit SBz)].
Definition SITES : list (Z * Z) := [(165605, 4); (165609, 4); (165601, 2); (165603, 2); (165598, 3)].
Definition has := CC.has_cell.
(* [comment removed for export] *)
Definition kmin_chk (cells : list kentry) (c : Z) : bool :=
  existsb (fun X => match X with KRange (EVar 11) lo _ => Z.leb c lo | _ => false end) cells.
(* [comment removed for export] *)
Definition SLT3 (v : nat) : expr := EAlu Instr.ALU_ADD CHE (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_SLTU (EVar v) (ELit 1))) (ELit 3)).
Definition a0_chk (ps : SR.post_spec) (cells : list kentry) : bool :=
  (CL.ps_reg_is ps 10 CHE
   || (CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD CHE (ELit 2)) && kmin_chk cells 2)
   || (CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD CHE (ELit 4)) && kmin_chk cells 4)
   || ((CL.ps_reg_is ps 10 (SLT3 68) || CL.ps_reg_is ps 10 (SLT3 100)) && kmin_chk cells 3))%bool.
Definition site_chk (ps : SR.post_spec) (cells : list kentry) : bool :=
  existsb (fun qn : Z * Z => (CL.ps_reg_is ps 11 (ELit (fst qn)) && CL.ps_reg_is ps 12 (ELit (snd qn)) && kmin_chk cells (snd qn))%bool) SITES.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      ((Nat.leb 32 (CC.cp_nx c) && CBA.regions_eqb (CC.cp_F c) CPF0 && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])) &&
      if Z.eqb pc PC_BCMP then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_BCMP
                                  && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 8192 0 [] (nth i FFS []) [] STAT None c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                     | Some ci => Z.eqb (CH2.ci_csp ci) (-64) | None => false end
                                  && CL.ps_reg_is ps 10 CHE && site_chk ps cells)%bool
                    | None => false end
        | None => false end
      else (CBA.exit_base_chk GT.NF RETPC c ps && a0_chk ps cells))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma ffs_i : forall i, nth i FFS [] = [].
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma bls_i : forall i, nth i G.BLS [] = [].
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
(* [comment removed for export] *)
Lemma bom_bytes : forall q n, In (q, n) SITES -> exists zs, AX2.img_bytes RSEGS q (Z.to_nat n) = Some zs.
Proof.
  intros q n Hin. cbn [SITES In] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-; eexists; vm_compute; reflexivity.
Qed.
End DTA.

Section DetectOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Abbreviation IC := PMLA.C_xasan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis ISH : rt_img_shadow L IL HI.                                            (* [comment removed for export] *)
Hypothesis POI : Forall (fun r : Z * Z => DTA.BOM_HI <= fst r \/ snd r <= DTA.BOM_LO) (icl_poison IL).   (* [comment removed for export] *)
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis MEMCMP : amemcmp_spec_at L ar SCFG HI DTA.PC_BCMP 8192.                (* [comment removed for export] *)

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart, DTA.CHE, DTA.KE; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

(* [comment removed for export] *)
Lemma slt3_val : forall E v ch, CL5A.uv E DTA.CHE = ch -> 0 <= ch -> ch + 3 < 2 ^ 64 -> exists d, (d = 0 \/ d = 3) /\ CL5A.uv E (DTA.SLT3 v) = ch + d.
Proof.
  intros E v ch Hch H0 Hhi. unfold CL5A.uv, DTA.SLT3, DTA.CHE in *. cbn [edenot] in *.
  rewrite u_add64, u_and64, u_mul64, u_sltu64, !u_lit64a, Hch.
  destruct (bv_unsigned (ev E v) <? 1 mod 2 ^ 64).
  - exists 3. split; [right; reflexivity|]. change (Z.land ((-1) mod 2 ^ 64 * 1 mod 2 ^ 64) (3 mod 2 ^ 64)) with 3. rewrite Z.mod_small by lia. reflexivity.
  - exists 0. split; [left; reflexivity|]. change (Z.land ((-1) mod 2 ^ 64 * 0 mod 2 ^ 64) (3 mod 2 ^ 64)) with 0. rewrite Z.mod_small by lia. lia.
Qed.

Theorem detect_json_ok : TPSA.detect_json_specA L ar HI IC 846264.
Proof.
  unfold TPSA.detect_json_specA. intros LB FF LK cr A ch k sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & HK & Hch & HSH & HDEF & HIR & Hstksh) Hcont.
  unfold PMSA.a0, PMSA.a1, TPSA.DETECT_SCR, PMSA.MEMCMP_SCR, PMSA.stksh in *. change (64 + 8192) with 8256 in *.
  (* [comment removed for export] *)
  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WFT) as STOP.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  (* [comment removed for export] *)
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (ch, 16384) Hch) as ((KC0 & KC1 & KC16 & KC3 & KC4 & (KC5 & KC6 & KC7)) & KCdef & _). cbn [fst snd] in KC0, KC1, KC16, KC3, KC4, KC5, KC6, KC7, KCdef.
  rewrite ILO, IHI in KC1. unfold BIGSHADOW_LO, BIGSHADOW_HI in KC6. pose proof (CHA.mod8_of_16 _ KC16) as KC8.
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (CHSH : forall a, ch <= a < ch + 16384 -> byte_at M (S a) 0).
  { intros a Ha. pose proof (Z_div_mod_eq_full a 8) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(clear; lia)) as Ma. pose proof (Z_div_mod_eq_full ch 8) as Dc. rewrite KC8 in Dc.
    replace (S a) with (S ch + (a / 8 - ch / 8)) by (unfold S; clear; lia). apply (proj1 HSH). clear - Ha Da Ma Dc. lia. }
  (* [comment removed for export] *)
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => @nil byte)).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 ch) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 k) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = ch) by (rewrite V10; apply u64_of_Z; clear - KC0 KC7; lia).
  assert (U11 : bv_unsigned (ev E0 11) = k) by (rewrite V11; apply u64_of_Z; clear - HK; lia).
  (* [comment removed for export] *)
  assert (SCRV : CH.hd_scr G.HDECL = 8256) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := @nil L5.range). set (Wo := @nil L5.range).
  assert (WINC : incl Wo WW) by (intros w []).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))) by (intros w a [] _).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)) by (intros rg []).
  (* [comment removed for export] *)
  assert (KBLK : forall a, (ch <= a < ch + 16384 -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)))
                        /\ (in_shadow_of ch 16384 a -> 0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)))).
  { intros a. split; intros Ha.
    - split; [clear - Ha KC0 KC7; lia|]. split; [left; exists (ch, 16384); split; [exact Hch | exact Ha]|]. apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Ha KC6. lia.
    - pose proof (SHR ch 16384 a ltac:(clear - KC0; lia) ltac:(clear; lia) KC7 Ha) as RG. split; [clear - RG; lia|]. split; [do 6 right; exists (ch, 16384); split; [exact Hch | exact Ha]|].
      exact (CL5A.not_stk_shadow_sh L ar LB FF ch 16384 a RFx ltac:(clear - KC0; lia) ltac:(clear; lia) KC4 Ha). }
  assert (KLB : forall a, ch <= a < ch + 16384 \/ in_shadow_of ch 16384 a -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (KBLK a) as [KB1' KB2'].
    destruct Ha as [Ha|Ha]; [destruct (KB1' Ha) as (G1 & G2 & _); split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | intros w []]]
                          | destruct (KB2' Ha) as (G1 & G2 & _); split; [exact G1 | split; [exact G2 | intros w []]]]. }
  assert (KIMG : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xasan] in Ha. split; [clear - Ha; lia|]. split; [|intros w []].
    right; right; left. rewrite ILO, IHI. split; [clear - Ha; lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia]. }
  assert (AL : (sp - 8256) mod 8 = 0) by (clear - S1; pose proof (Z_div_mod_eq_full sp 16) as D; rewrite S1, Z.add_0_r in D; rewrite D; replace (16 * (sp / 16) - 8256) with ((2 * (sp / 16) - 1032) * 8) by lia; apply Z_mod_mult).
  assert (KSTK : forall a, S (sp - 8256) <= a < S (sp - 8256) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 8256)) / 8 -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (PTA.stksh_rng ar sp 8256 a ltac:(clear - S2; lia) AL C8 (proj2 SP1) STOP ltac:(clear - CL; lia) Ha) as (G1 & G2).
    split; [exact G1|]. split; [do 4 right; left; exact G2 | intros w []]. }
  (* [comment removed for export] *)
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    assert (G8 : forall i, 0 <= i < 8 -> (ch + i) / 8 = ch / 8) by (intros i Hi; pose proof (Z_div_mod_eq_full ch 8) as Dc; rewrite KC8 in Dc; rewrite Dc, Z.add_0_r; replace (8 * (ch / 8) + i) with (i + ch / 8 * 8) by (clear; lia); rewrite Z.div_add by (clear; lia); rewrite Z.div_small by exact Hi; clear; lia).
    destruct Hrg as [<-|[<-|[<-|[<-|[<-|[]]]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha;
      rewrite ?CL5A.estart_srl3' in Ha; unfold estart, elenZ, CL5A.uv in Ha; cbn [a_base a_off edenot] in Ha; rewrite ?u_add64, ?U10, ?U11 in Ha; rewrite ?u64_of_Z in Ha by (clear; lia); rewrite ?Z.mod_small in Ha by (clear - KC0 KC7; lia);
      rewrite ?G8 in Ha by (clear; lia).
    - destruct (proj1 (KBLK a) ltac:(clear - Ha HK; lia)) as (G1 & G2 & G3). split; [exact G1 | split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]].
    - destruct (proj2 (KBLK a) (CL5A.shreg_in_shadow ch 2048 a KC8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3). split; [exact G1 | split; [exact G2 | exact G3]].
    - destruct (proj2 (KBLK a) (CL5A.shreg_in_shadow ch 2048 a KC8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3). split; [exact G1 | split; [exact G2 | exact G3]].
    - destruct (proj2 (KBLK a) (CL5A.shreg_in_shadow ch 2048 a KC8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3). split; [exact G1 | split; [exact G2 | exact G3]].
    - destruct (proj2 (KBLK a) (CL5A.shreg_in_shadow ch 2048 a KC8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia))) as (G1 & G2 & G3). split; [exact G1 | split; [exact G2 | exact G3]]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[<-|[]]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }
  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (_ : word -> option byte) (_ : Model) => True).
  (* [comment removed for export] *)
  assert (CUTF : forall i E1 A1 M1 m1, CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DTA.FFS Cred 0 i E1 A1 M1 m1 ->
            CHA.curB LB G.BLS i E1 = LB /\ CHA.curF FF sp DTA.FFS i E1 = FF /\ env_agree GT.NF E0 E1 /\
            (forall a, CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
            (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> M (Z_to_bv 64 a) <> None -> M1 (Z_to_bv 64 a) <> None)).
  { intros i E1 A1 M1 m1 HA. pose proof HA as (_ & _ & _ & HagE & _ & Hfr & Hdf).
    split; [unfold CHA.curB; rewrite DTA.bls_i; reflexivity|]. split; [unfold CHA.curF; rewrite DTA.ffs_i; reflexivity|]. split; [exact HagE|]. split; [exact Hfr | exact Hdf]. }
  assert (LEAFK : forall i c ps0 E1 A1 M1 m1 E' R' M' m', nth_error G.CPS i = Some c -> CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DTA.FFS Cred 0 i E1 A1 M1 m1 ->
            env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
            bv_unsigned (ev E' 2) = sp /\ bv_unsigned (ev E' 10) = ch /\ bv_unsigned (ev E' 11) = k
            /\ (forall X0, In X0 (SR.ps_cells ps0) -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
            /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)).
  { intros i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF.
    pose proof (CBA.leaf_agree0 L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS DTA.FFS Cred 0 i c E1 E' A1 M1 m1 HA (G.NF_le i c Hci) Hag) as HagE'.
    assert (FZ : forall n, (n <? 32)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); unfold GT.NF; apply Nat.ltb_lt; exact Hn).
    split; [rewrite (FZ 2%nat eq_refl); exact U2|]. split; [rewrite (FZ 10%nat eq_refl); exact U10|]. split; [rewrite (FZ 11%nat eq_refl); exact U11|].
    split; [intros X0 HX0; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0)|].
    intros q e0 z Hq Hz; rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq); rewrite <- Hz; symmetry; apply Z_to_bv_bv_unsigned. }
  assert (KMIN : forall E' Ax mx Mx cells c0, bv_unsigned (ev E' 11) = k -> (forall X0, In X0 cells -> kentry_ok (hl_segs L) E' (CCA.vis Ax mx Mx) X0) -> DTA.kmin_chk cells c0 = true -> c0 <= k).
  { intros E' Ax mx Mx cells c0 W11 CELL H. unfold DTA.kmin_chk in H. apply existsb_exists in H as (X0 & HX0 & Hb).
    destruct X0 as [| | | | |e lo hi| | | |]; try discriminate Hb. destruct e as [|v| | | | | |]; try discriminate Hb. do 11 (destruct v as [|v]; [discriminate Hb|]). destruct v; [|discriminate Hb].
    apply Z.leb_le in Hb. pose proof (CELL (KRange (EVar 11) lo hi) HX0) as R0. cbn [kentry_ok edenot] in R0. rewrite W11 in R0. clear - Hb R0. lia. }
  rewrite <- LS in FPM.
  change 846264 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS DTA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact DTA.heap_ok.
  - intros i c kk ps0 j sg IL0. exfalso. pose proof (CH2.leaves_all_sound _ _ _ DTA.leaf_ok _ _ _ _ _ IL0) as X. exact (Bool.diff_false_true X).
  - intros i c kk ps0 j sg IL0. exfalso. pose proof (CH2.leaves_all_sound _ _ _ DTA.leaf_ok _ _ _ _ _ IL0) as X. exact (Bool.diff_false_true X).
  - (* [comment removed for export] *)
    intros i c kk ps0 pc IL0. pose proof (CH2.leaves_all_sound _ _ _ DTA.leaf_ok _ _ _ _ _ IL0) as X. unfold DTA.leaf_chk in X. cbn beta iota in X.
    assert (Hci : nth_error G.CPS i = Some c) by (destruct IL0 as (tg & Hci & _); exact Hci).
    apply andb_prop in X as [X0 X]. apply andb_prop in X0 as [X0 Yfoot]. apply andb_prop in X0 as [Ynx YF]. apply Nat.leb_le in Ynx. apply CBA.regions_eqb_eq in YF.
    destruct (Z.eqb_spec pc DTA.PC_BCMP) as [->|Hne].
    { (* [comment removed for export] *)
      destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X Ysite]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [Y0 Y9]. apply Z.eqb_eq in Y0.
      lazymatch type of Y9 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end. apply Z.eqb_eq in Y9. rename Y9 into Ycsp.
      unfold DTA.site_chk in Ysite. apply existsb_exists in Ysite as ([q n] & HinS & Ys). cbn [fst snd] in Ys. apply andb_prop in Ys as [Ys Ykm]. apply andb_prop in Ys as [Y11 Y12].
      assert (QN : DTA.BOM_LO <= q /\ q + n <= DTA.BOM_HI /\ 2 <= n <= 4) by (clear - HinS; cbn [DTA.SITES In] in HinS; unfold DTA.BOM_LO, DTA.BOM_HI; destruct HinS as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-; lia).
      destruct (DTA.bom_bytes q n HinS) as (zs & Hzs).
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA _].
      destruct (CUTF i E1 A1 M1 m1 HA) as (HcB & HcF & HagE & Hfr & Hdf).
      pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS DTA.FFS Cred 0 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
      refine (CALLEE DTA.PC_BCMP 8192 0%nat [] [] DTA.STAT None 0 i c ps0 j cj ci Hcj Hchk Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite (DTA.ffs_i j), (DTA.ffs_i i); reflexivity | rewrite (DTA.ffs_i i); cbn; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HKN [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr' & Hdf').
      destruct (LEAFK i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF) as (W2 & W10 & W11 & CELL & REG).
      pose proof (KMIN E' A1 m' M' _ n W11 CELL Ykm) as KN.
      (* [comment removed for export] *)
      destruct (AX2S.rdn_defined (hl_segs L) M' (Z.to_nat n) (Z_to_bv 64 ch)) as (b1 & Hb1 & Lb1).
      { rewrite L5.unsigned_lit by (clear - KC0 KC7; lia). rewrite Z2Nat.id by (clear - QN; lia). clear - KC0 KC7 QN. lia. }
      { intros jj Hjj. rewrite L5.unsigned_lit by (clear - KC0 KC7; lia). unfold AX2S.rd1.
        destruct (M' (Z_to_bv 64 (ch + Z.of_nat jj))) eqn:Hm; [discriminate|]. exfalso.
        apply (Hdf' (ch + Z.of_nat jj)); [clear - Hjj KC0 KC7 QN; lia | left; exists (ch, 16384); split; [exact Hch | cbn [fst snd]; clear - Hjj QN; lia] | apply HDEF; clear - Hjj KN QN; lia | exact Hm]. }
      destruct (rdn_img (hl_segs L) M' (Z.to_nat n) (Z_to_bv 64 q) zs) as (b2 & Hb2 & _).
      { rewrite L5.unsigned_lit by (clear - QN; unfold DTA.BOM_LO, DTA.BOM_HI in QN; lia). rewrite Z2Nat.id by (clear - QN; lia). clear - QN. unfold DTA.BOM_LO, DTA.BOM_HI in QN. lia. }
      { intros jj Hjj. rewrite L5.unsigned_lit by (clear - QN; unfold DTA.BOM_LO, DTA.BOM_HI in QN; lia).
        rewrite (Hfr' _ (KIMG (q + Z.of_nat jj) ltac:(cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xasan]; unfold DTA.BOM_LO, DTA.BOM_HI in QN; clear - QN Hjj; lia))).
        unfold PMLA.img_ro, L5.img_clear in HIR. apply HIR. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xasan]. unfold DTA.BOM_LO, DTA.BOM_HI in QN. clear - QN Hjj. lia. }
      { rewrite L5.unsigned_lit by (clear - QN; unfold DTA.BOM_LO, DTA.BOM_HI in QN; lia). rewrite LS. exact Hzs. }
      destruct (ISH _ _ _ _ _ _ _ HH1 q n ltac:(rewrite ILO; unfold DTA.BOM_LO in QN; clear - QN; lia) ltac:(rewrite IHI; unfold DTA.BOM_HI in QN; clear - QN; lia) ltac:(clear - QN; lia)
                  ltac:(eapply Forall_impl; [|exact POI]; intros rr Hr; cbn beta in Hr; clear - Hr QN; lia)) as [BZ BA].
      eexists. eexists. split; [exact (CRC.memcmp_cps L ar HI PMSA.fp_ok DTA.PC_BCMP 8192 MEMCMP 8192 LB FF LK1 cr1 A1 ch q n b1 b2 (sp + CH2.ci_csp ci) (CC.cp_pc cj) ltac:(clear; lia))|].
      split.
      { unfold CRC.memcmp_pre, CRC.mem_src.
        split; [exact (REG 10%nat _ ch Y10 ltac:(cbn [edenot]; exact W10))|]. split; [exact (REG 11%nat _ q Y11 ltac:(cbn [edenot]; apply u64_of_Z; unfold DTA.BOM_LO, DTA.BOM_HI in QN; clear - QN; lia))|].
        split; [exact (REG 12%nat _ n Y12 ltac:(cbn [edenot]; apply u64_of_Z; clear - QN; lia))|]. split; [clear - QN; lia|]. split.
        - split; [intros a Ha; left; unfold byte_at; assert (ISa : in_shadow_of ch 16384 (S a)) by (unfold in_shadow_of; clear - Ha QN; split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia); rewrite (Hfr' _ (KLB (S a) (or_intror ISa))); apply CHSH; clear - Ha QN; lia|].
          split; [clear - KC0 KC7 QN; lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; clear - KC0 KC6 KC4 QN; lia|]. split; [|exact Hb1].
          intros i1 Hi1. right. left. exists (ch, 16384). split; [exact Hch | cbn [fst snd]; clear - Hi1 QN; lia].
        - split; [intros a Ha; left; apply BZ; unfold in_shadow_of; clear - Ha; split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia|].
          unfold DTA.BOM_LO, DTA.BOM_HI in QN. split; [clear - QN; lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; clear - QN SP1; lia|]. split; [|exact Hb2].
          intros i1 Hi1. left. rewrite ILO, IHI. clear - Hi1 QN. lia. }
      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Pa0 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
      split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a [] _|]. split; [intros w a [] _|].
      split; [unfold CHA.curB; rewrite DTA.bls_i; exact HH2|]. split; [exact HC1|]. split; [exact I|].
      intros X0 HX0 _. unfold DTA.STAT in HX0. cbn [In] in HX0.
      destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ (CH2.retEx E' (CH2.ci_nx ci) [] R2) _ HH2); reflexivity). }
    (* [comment removed for export] *)
    apply andb_prop in X as [Xbase Ya0].
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA _].
    destruct (CUTF i E1 A1 M1 m1 HA) as (HcB & HcF & HagE & Hfr & Hdf).
    refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS DTA.FFS Cred 0 STKF SCRP NF32 U2 WINC WOK WRS_OK
              K DEF0 R r EV Hra Hraok DTA.RETPC i c ps0 _ Xbase Yfoot (DTA.ffs_i i) fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact DTA.ret_at |].
    intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
    destruct (LEAFK i c ps0 E1 A1 M1 m1 E' R' M' m' Hci HA Hag HLF) as (W2 & W10 & W11 & CELL & REG).
    rewrite HcB in HH1. rewrite SCRV in HP.
    assert (UCH : CL5A.uv E' DTA.CHE = ch) by (unfold CL5A.uv, DTA.CHE; cbn [edenot]; exact W10).
    assert (RES : exists d, 0 <= d <= 4 /\ d <= k /\ getr R' (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (ch + d)).
    { unfold DTA.a0_chk in Ya0. apply orb_prop in Ya0. destruct Ya0 as [Ya0|Ya0]; [apply orb_prop in Ya0; destruct Ya0 as [Ya0|Ya0]; [apply orb_prop in Ya0; destruct Ya0 as [Ya0|Ya0]|]|].
      - exists 0. split; [clear; lia|]. split; [clear - HK; lia|]. rewrite Z.add_0_r. exact (REG 10%nat _ ch Ya0 ltac:(cbn [edenot]; exact W10)).
      - apply andb_prop in Ya0 as [Yr Ykm]. pose proof (KMIN E' A1 m' M' _ 2 W11 CELL Ykm) as KN. exists 2. split; [clear; lia|]. split; [exact KN|].
        exact (REG 10%nat _ (ch + 2) Yr ltac:(change (CL5A.uv E' (EAlu Instr.ALU_ADD DTA.CHE (ELit 2)) = ch + 2); apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - KC0 KC7; lia])).
      - apply andb_prop in Ya0 as [Yr Ykm]. pose proof (KMIN E' A1 m' M' _ 4 W11 CELL Ykm) as KN. exists 4. split; [clear; lia|]. split; [exact KN|].
        exact (REG 10%nat _ (ch + 4) Yr ltac:(change (CL5A.uv E' (EAlu Instr.ALU_ADD DTA.CHE (ELit 4)) = ch + 4); apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - KC0 KC7; lia])).
      - apply andb_prop in Ya0 as [Yr Ykm]. pose proof (KMIN E' A1 m' M' _ 3 W11 CELL Ykm) as KN.
        assert (EXv : exists v, CL.ps_reg_is ps0 10 (DTA.SLT3 v) = true) by (apply orb_prop in Yr; destruct Yr as [Yr|Yr]; [exists 68%nat | exists 100%nat]; exact Yr).
        destruct EXv as (v & Yr'). destruct (slt3_val E' v ch UCH ltac:(clear - KC0; lia) ltac:(clear - KC7; lia)) as (d & Hd & Hv).
        exists d. split; [clear - Hd; lia|]. split; [clear - Hd KN; lia|]. exact (REG 10%nat _ (ch + d) Yr' Hv). }
    destruct RES as (d & Hd & Hdk & HA0R).
    apply (Hcont fx' R' M' model2 LB cr1 LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
    exists (ch + d). unfold PMSA.a0. split; [exact HA0R|]. split; [clear - Hd Hdk; lia|]. split; [clear - Hd; lia|]. split; [reflexivity|]. split; [exact HC1|]. split; reflexivity.
  - reflexivity.
  - (* [comment removed for export] *)
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VS : CL5A.visr (ahid A model) (sp - 8256) 8256).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    assert (VCH : CL5A.visr (ahid A model) ch 16384).
    { intros q Hq. apply CLV; [clear - Hq KC0 KC7; lia | left; exists (ch, 16384); split; [exact Hch | cbn [fst snd]; clear - Hq; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq KC6. lia. }
    assert (VCHS : forall a, in_shadow_of ch 16384 a -> ahid A model (Z_to_bv 64 a) = false).
    { intros a Ha. pose proof (SHR ch 16384 a ltac:(clear - KC0; lia) ltac:(clear; lia) KC7 Ha) as RG. apply CLV; [clear - RG; lia | do 6 right; exists (ch, 16384); split; [exact Hch | exact Ha] |].
      exact (CL5A.not_stk_shadow_sh L ar LB FF ch 16384 a RFx ltac:(clear - KC0; lia) ltac:(clear; lia) KC4 Ha). }
    set (Mv := CCA.vis A model M).
    assert (DS : L5.defined Mv (sp - 8256) 8256) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DW : L5.defined Mv ch k) by (apply (CL5A.defined_vis _ M ch k (CL5A.visr_sub _ ch 16384 ch k VCH ltac:(clear; lia) ltac:(clear - HK; lia))); exact HDEF).
    assert (CD : 0 <= ch / 8 <= 2 ^ 44 - 2048) by (split; [apply Z.div_pos; clear - KC0; lia | apply Z.div_le_upper_bound; clear - KC7; lia]).
    assert (UVC : CL5A.uv E0 (EVar 10) = ch) by (unfold CL5A.uv; cbn [edenot]; exact U10).
    unfold PMLA.img_ro, L5.img_clear in HIR. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xasan] in HIR.
    assert (IMGK : forall lo hi, 65536 <= lo -> hi <= 1449984 -> kentry_ok (hl_segs L) E0 Mv (KImg lo hi)).
    { intros lo hi Hlo Hhi. apply AxSymRun3.kimg_intro; [clear - Hlo; lia | clear - Hhi; lia |]. intros i1 Hi1. unfold Mv, CCA.vis.
      destruct (mrestrict (ahid A model) M (Z_to_bv 64 i1)) eqn:Hv; [|reflexivity]. exfalso. exact (CL5A.vis_def (ahid A model) M (Z_to_bv 64 i1) ltac:(rewrite Hv; discriminate) (HIR i1 ltac:(clear - Hi1 Hlo Hhi; lia))). }
    assert (G1Z : forall off, 0 <= off < 8 -> kentry_ok (hl_segs L) E0 Mv (KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 10) (ELit off)) (ELit 3)) DTA.SBz) (ELit 1))).
    { intros off Hoff. pose proof (Z_div_mod_eq_full ch 8) as Dc. rewrite KC8 in Dc.
      assert (UVo : CL5A.uv E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit off)) = ch + off) by (unfold CL5A.uv; cbn [edenot]; rewrite u_add64, U10, L5.unsigned_lit by (clear - Hoff; lia); apply Z.mod_small; clear - KC0 KC7 Hoff; lia).   (* [comment removed for export] *)
      assert (Dv : (ch + off) / 8 = ch / 8) by (rewrite Dc, Z.add_0_r; replace (8 * (ch / 8) + off) with (off + ch / 8 * 8) by (clear; lia); rewrite Z.div_add by (clear; lia); rewrite Z.div_small by exact Hoff; clear; lia).
      unfold DTA.SBz. apply (CL5A.kzero_intro (hl_segs L) E0 Mv _ _ (ch / 8 + SB) 1); [rewrite CL5A.estart_srl3', UVo, Dv; reflexivity | reflexivity | unfold SB; clear - CD; lia | unfold SB; clear - CD; lia | unfold SB; clear - CD; lia |].
      intros j Hj. replace (ch / 8 + SB + j) with (S ch + j) by (unfold S; clear; lia).
      apply CL5A.byte_vis; [apply VCHS; apply (CL5A.shreg_in_shadow ch 2048); [exact KC8 | clear; lia | unfold S, SB; clear - Hj; lia] |].
      replace (S ch + j) with (S (ch + 8 * j)) by (unfold S; rewrite Dc; clear; rewrite Z.add_0_r; replace (8 * (ch / 8) + 8 * j) with ((ch / 8 + j) * 8) by lia; rewrite Z.div_mul by lia; replace (8 * (ch / 8)) with (ch / 8 * 8) by lia; rewrite Z.div_mul by lia; lia).
      apply CHSH. clear - Hj Dc. lia. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); try (apply Forall_nil).
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply IMGK; clear; lia.
    + eapply CL5.krange_intro with (v := ch); [lin_eval; rw_atoms; clear; lia | clear - KC0 KC7; lia | clear - KC0 KC4 SP1; lia].
    + eapply CL5.kalign_intro with (v := ch); [lin_eval; rw_atoms; clear; lia | clear - KC0 KC7; lia | clear; lia | exact KC16].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 2048 ch UVC); [clear; lia | clear - KC0 KC7; lia |].
      intros j Hj. apply CL5A.byte_vis; [apply VCHS; apply (CL5A.shreg_in_shadow ch 2048); [exact KC8 | clear; lia | unfold S, SB; clear - Hj; lia] |].
      pose proof (Z_div_mod_eq_full ch 8) as Dc. rewrite KC8 in Dc. replace (S ch + j) with (S (ch + 8 * j)) by (unfold S; rewrite Dc; clear; rewrite Z.add_0_r; replace (8 * (ch / 8) + 8 * j) with ((ch / 8 + j) * 8) by lia; rewrite Z.div_mul by lia; replace (8 * (ch / 8)) with (ch / 8 * 8) by lia; rewrite Z.div_mul by lia; lia).
      apply CHSH. clear - Hj Dc. lia.
    + apply G1Z; clear; lia.
    + apply G1Z; clear; lia.
    + apply G1Z; clear; lia.
    + eapply CL5.kunk_intro with (A := ch) (N := k); [ev0 | unfold elenZ; cbn [edenot]; exact U11 | clear - KC0; lia | clear - KC7 HK; lia | clear - KC7 HK; lia | exact DW].
    + eapply CL5.krange_intro with (v := k); [lin_eval; rw_atoms; clear; lia | clear - HK; lia | clear - HK; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := ch) (N2 := 16384); [reflexivity | reflexivity | ev0 | reflexivity | clear - KC6; lia].
    + eapply CL5.kwr_intro with (A := sp - 8256) (N := 8256); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kunk_intro with (A := sp - 8256) (N := 8256); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 8256) (N1 := 8256) (A2 := ch) (N2 := 16384); [ev0 | reflexivity | ev0 | reflexivity | clear - KC4 S2; lia].
  - (* [comment removed for export] *)
    split; [|exact I].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. rewrite DTA.bls_i, DTA.ffs_i. cbn [CH2.den CHA.denF map app length Z.of_nat Z.sub].
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.
Print Assumptions detect_json_ok.
End DetectOk.
