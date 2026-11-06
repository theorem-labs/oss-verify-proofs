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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutBridgeB
  CutRtCpsA CutRtA CutRtB CutRtC CutRtD CutShA CutInlA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmFloatCSpecsA PmFloatCWD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import CutInlFA Call2A.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_wd_cboth_T Cut_wd_cboth_D Cut_wd_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_wd_cboth_D.  Module GF := Cut_wd_cboth.  Module GT := Cut_wd_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module WDC.
Definition PC_SM : Z := 414896.  Definition PC_DT : Z := 861312.  Definition PC_SETSH : Z := 536236.  Definition RETPC : Z := 848184.
Definition TP : Z := 6888848.  Definition ERRNO : Z := 6888684.
Definition SBz : Z := 2147450880.
Definition WDE := EVar 10.  Definition OE := EVar 11.  Definition DPE := EVar 32.  Definition FLE := EVar 49.  Definition FE := EVar 54.
Definition SPX : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit 16).
Definition FR : expr * Z * Z := (FE, 4, -96).
Definition FFS : list (list (expr * Z * Z)) := map (fun i => if (Nat.eqb i 0 || Nat.eqb i 2)%bool then [] else [FR]) (seq 0 8).
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz); KWord (SA (ELit 0) 1432832) 4 (ELit 1)].
Definition FLAG : list kentry := [KWord (SA FE 1016) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Definition NEWS_C : list kentry := STAT ++ FLAG.
Definition DT_W : list SGP.region := [(OE, 0, ELit 24); (ELit 0, ERRNO, ELit 4)].
Definition SH_W : list SGP.region := [(CHA.SRL3 FE, SBz, ELit 128)].
Definition has := CC.has_cell.
Definition isnil {A} (l : list A) : bool := match l with [] => true | _ => false end.
Definition sm_ok (ps : SR.post_spec) (i : nat) (X : kentry) : bool :=
  (CHA.static_chk GT.SCELLS GT.GLO GT.GHI X || CRA.smalloc_fact_ok 7028736 G.HDECL (SR.ps_cells ps) 49 (nth i G.BLS []) (nth i FFS []) 4 54 49 X)%bool.
Definition callee_ci (ps : SR.post_spec) (i j : nat) (c cj : CC.cutpoint) (scr : Z) (ng : nat) (BLk : CA.blocks) (wregs : list SGP.region) (news : list kentry) (a0x : option expr) :=
  CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr ng BLk (nth i FFS []) wregs news a0x c ps cj (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []).
Definition callee (ps : SR.post_spec) (i j : nat) (c cj : CC.cutpoint) (scr : Z) (ng : nat) (BLk : CA.blocks) (wregs : list SGP.region) (news : list kentry) (a0x : option expr) : bool :=
  (CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
   && match callee_ci ps i j c cj scr ng BLk wregs news a0x with Some ci => Z.eqb (CH2.ci_csp ci) (-96) | None => false end)%bool.

Definition twin_ok (ps : SR.post_spec) (i j tl : nat) (c cj : CC.cutpoint) (scr : Z) (wregs : list SGP.region) (news : list kentry) (a0x : option expr) : bool :=
  match nth_error G.CPS tl with
  | Some ctl => match callee_ci ps i tl c ctl scr 1 [] wregs news a0x, callee_ci ps i j c cj scr 0 [] wregs news a0x with
                | Some ci2, Some ci1 => (Z.eqb (CH2.ci_csp ci2) (CH2.ci_csp ci1) && Z.eqb (CC.cp_pc ctl) (CC.cp_pc cj))%bool
                | _, _ => false end
  | None => false end.

Definition INLS : list (Z * nat * nat) := [(846920, 0%nat, 2%nat); (848356, 4%nat, 5%nat)].
Definition o_empty (cells : list kentry) : bool := (has cells (KWord (SA OE 0) 1 (ELit 0)) && has cells (KWord (SA OE 1) 1 (ELit 0)))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc RETPC then
        (CBB.exit_base_chk_sp GT.NF RETPC SPX c ps && Nat.ltb 54 (CC.cp_nx c)
         && match CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS []) with Some fle => expr_eqb fle FLE | None => false end
         && has cells (KWord (SA FLE 0) 1 (ELit 0)) && CL.ps_reg_is ps 10 (ELit 0) && (Nat.eqb i 7 || Nat.eqb i 3))%bool
      else
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match nth_error G.CPS j with
            | Some cj =>
                (Z.eqb (SR.ps_pc ps) pc &&
                 match CIFA.fp_site RSEGS pc with
                 | Some hv => (CIFA.inlF_chk GT.NF c ps cj 4 hv && CIA.same_chk GT.NF G.HDECL c (nth i G.BLS []) (nth j G.BLS []) (nth i FFS []) (nth j FFS [])
                               && existsb (fun p => (Z.eqb (fst (fst p)) pc && Nat.eqb (snd (fst p)) i && Nat.eqb (snd p) j)%bool) INLS)%bool
                 | None =>
                 if Z.eqb pc PC_SM then (Nat.eqb i 2 && Nat.eqb j 4 && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i FFS [])
                                        && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 512 1 (nth i G.BLS []) (nth i FFS []) [] (List.filter (sm_ok ps i) (CC.cp_know cj)) None c ps cj
                                                   (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                           | Some ci => (Nat.eqb (CH2.ci_nx ci) 49 && Z.eqb (CH2.ci_csp ci) (-96))%bool | None => false end)
                 else if Z.eqb pc PC_DT then (Nat.eqb i 5 && Nat.eqb j 6
                                              && callee ps i j c cj 12800 0 [] DT_W NEWS_C (Some (ELit 1))
                                              && twin_ok ps i j 1 c cj 12800 DT_W NEWS_C (Some (ELit 1))
                                              && CL.ps_reg_is ps 10 DPE && CL.ps_reg_is ps 11 OE && o_empty cells && has cells (KWord (SA FE 1016) 8 FLE)
                                              && has cells (KRange DPE 0 255))
                 else if Z.eqb pc PC_SETSH then (((Nat.eqb i 6 && Nat.eqb j 7) || (Nat.eqb i 1 && Nat.eqb j 3))
                                              && CHA.frames_eqb (nth j FFS []) (nth i FFS []) && CH2.blocks_eqb (nth j G.BLS []) (nth i G.BLS [])
                                              && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 256 0 (nth i G.BLS []) (nth i FFS []) SH_W NEWS_C None c ps cj
                                                         (nth i G.BLS []) (nth i FFS []) (nth j G.BLS []) (nth j FFS []) with
                                                 | Some ci => Z.eqb (CH2.ci_csp ci) (-96) | None => false end
                                              && CL.ps_reg_is ps 10 (EAlu Instr.ALU_ADD (CHA.SRL3 FE) (ELit SBz)) && CL.ps_reg_is ps 11 (ELit 128)
                                              && has cells (KWord (SA FE 1016) 8 FLE) && Nat.ltb 54 (CC.cp_nx c))
                 else false
                 end)%bool
            | None => false end
        | None => false end
  end.

Lemma custom_chk_nx : forall scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj ci,
  CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj = Some ci ->
  CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - ng)%nat.
Proof.
  intros scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj ci H. unfold CHA.custom_chk in H.
  destruct (CHA.common_chk GT.NF G.HDECL scr ng c ps cj BLi FLi) as [ci0|] eqn:Hc; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection H as <-.
  unfold CHA.common_chk in Hc.
  destruct (nth 1 (CA.ps_reglist ps) (ELit 0)) as [ra| | | | | | |]; try discriminate.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp]. destruct spb as [|v| | | | | |]; try discriminate.
  destruct v as [|[|[|v]]]; cbv beta iota in Hc; try discriminate.
  lazymatch type of Hc with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection Hc as <-. reflexivity.
Qed.

Definition FX : list SGP.region := [(EVar 2, -14320, ELit 14320); (EVar 2, 0, ELit 16); (FE, 0, ELit 24); (FE, 32, ELit 984); (CHA.SRL3 FE, SBz, ELit 128)].
Lemma cpF_X : forall i c, nth_error G.CPS i = Some c -> (i = 1 \/ i = 6)%nat -> CC.cp_F c = FX.
Proof. intros i c H Hi. unfold G.CPS in H. destruct Hi as [->| ->]; cbn [nth_error] in H; injection H as <-; vm_compute; reflexivity. Qed.
Lemma cpF_XF : forall i c, nth_error G.CPS i = Some c -> (i = 3 \/ i = 7)%nat -> CC.cp_F c = FX ++ [(FLE, 0, ELit 1)].
Proof. intros i c H Hi. unfold G.CPS in H. destruct Hi as [->| ->]; cbn [nth_error] in H; injection H as <-; vm_compute; reflexivity. Qed.
Lemma outside_FX : forall E sp F a, bv_unsigned (ev E 2) = sp - 16 -> bv_unsigned (ev E 54) = F -> 0 <= a < 2 ^ 64 -> 14336 <= sp < 2 ^ 64 ->
  (a < sp - 14336 \/ sp <= a) -> (a < F \/ F + 24 <= a) -> (a < F + 32 \/ F + 1016 <= a) -> (a < F / 8 + SBz \/ F / 8 + SBz + 128 <= a) ->
  SGP.outside E FX (Z_to_bv 64 a).
Proof.
  intros E sp F a H2 H54 Ha Hsp Hs HF1 HF2 HF3. unfold SGP.outside, FX. rewrite L5.unsigned_lit by exact Ha.
  repeat (apply Forall_cons); try (apply Forall_nil); cbn [fst snd]; rewrite ?CL5A.estart_srl3; unfold estart, elenZ, CL5A.uv, FE; cbn [a_base a_off edenot];
    rewrite ?H2, ?H54; rewrite ?u64_of_Z by lia; lia.
Qed.
Lemma outside_FXF : forall E sp F fl a, bv_unsigned (ev E 2) = sp - 16 -> bv_unsigned (ev E 54) = F -> bv_unsigned (ev E 49) = fl -> 0 <= a < 2 ^ 64 -> 14336 <= sp < 2 ^ 64 ->
  (a < sp - 14336 \/ sp <= a) -> (a < F \/ F + 24 <= a) -> (a < F + 32 \/ F + 1016 <= a) -> (a < F / 8 + SBz \/ F / 8 + SBz + 128 <= a) -> a <> fl ->
  SGP.outside E (FX ++ [(FLE, 0, ELit 1)]) (Z_to_bv 64 a).
Proof.
  intros E sp F fl a H2 H54 H49 Ha Hsp Hs HF1 HF2 HF3 Hfl. unfold SGP.outside. apply Forall_app. split; [exact (outside_FX E sp F a H2 H54 Ha Hsp Hs HF1 HF2 HF3)|].
  rewrite L5.unsigned_lit by exact Ha. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold estart, elenZ, FLE; cbn [a_base a_off edenot]. rewrite H49. rewrite ?u64_of_Z by lia. lia.
Qed.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End WDC.

Section WriteDoubleOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_cboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis TPV : hl_tp L = WDC.TP.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis SETSH : aset_shadow_spec L ar SCFG HI WDC.PC_SETSH 245 256.
Hypothesis DT_OK : PMFCA.dtoa_true_specA L ar HI IC WDC.PC_DT.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.

Theorem write_double_ok : PMFCW.write_double_specW L ar HI IC 846852.
Proof.
  unfold PMFCW.write_double_specW.
  intros LB FF LK cr A wd o dp sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & Hu0 & Hu4 & Hu8 & (Hwd1 & Hwd2) & Hstr & Hdefo & (Ofr & O8 & Osh) & Hap & Hstksh & Himg & Hcred & Hsp32) Hcont.
  assert (SCRE : PMFCA.WD_SCR_A = 14336) by reflexivity. rewrite SCRE in *. clear SCRE.
  assert (DE : PMFCA.WD_D = 5) by reflexivity. rewrite DE in *. clear DE.
  unfold PMSA.a0, PMSA.a1, PMSA.stksh, PMSA.u8, PMSA.u32, PMLA.apart in *. change (24 / 8) with 3 in Osh.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : 7028736 <= hl_img_hi L /\ hl_img_lo L < FS_BYTES) by (rewrite ILO, IHI; unfold FS_BYTES; clear; lia).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP47.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (Hsp16 : (sp - 16) mod 32 = 0).
  { clear - Hsp32. pose proof (Z_div_mod_eq_full sp 32) as D. rewrite Hsp32 in D. rewrite D. replace (32 * (sp / 32) + 16 - 16) with ((sp / 32) * 32) by lia. apply Z_mod_mult. }
  assert (S1x : (sp - 16) mod 16 = 0) by (clear - Hsp16; apply Z.mod_divide in Hsp16; [|lia]; destruct Hsp16 as [q Hq]; rewrite Hq; replace (q * 32) with ((q * 2) * 16) by lia; apply Z_mod_mult).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (ERRV : hl_tp L - 164 = WDC.ERRNO) by (rewrite TPV; reflexivity).

  set (RSP := regupd R 2%bv (Z_to_bv 64 (sp - 16))).
  set (dpb := dp mod 256).
  set (gh := fun n : nat => if Nat.eqb n 32 then Z_to_bv 64 dpb else Z_to_bv 64 0).
  set (E0 := Env (reg_ev RSP gh) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr RSP y) by (intros y; apply CL5.ev_reg).
  assert (EV' : forall y : reg, y <> 2%bv -> ev E0 (ridx y) = getr R y) by (intros y Hy; rewrite (EV y); unfold RSP; apply getr_other; exact Hy).
  assert (EVN : forall y : reg, In (ridx y) CBB.CSAVED_nosp -> ev E0 (ridx y) = getr R y).
  { intros y Hy. apply EV'. intros Heq. subst y. unfold CBB.CSAVED_nosp in Hy. cbn in Hy. clear - Hy. intuition discriminate. }
  assert (V2 : ev E0 2 = Z_to_bv 64 (sp - 16)) by (rewrite (EV 2%bv); unfold RSP; apply getr_same; discriminate).
  assert (SPE : edenot E0 WDC.SPX = getr R 2%bv).
  { rewrite Hsp. unfold WDC.SPX. rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E0 _)). f_equal. cbn [edenot]. rewrite u_add64, V2, !u64_of_Z by (clear - S2 S3 SP1 CL; lia).
    rewrite Z.mod_small by (clear - S2 S3 SP1 CL; lia). clear; lia. }
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV' 4%bv ltac:(discriminate))).
  assert (REGS0 : regs_ok E0 (CC.cp_regs G.cp0) R).
  { assert (RQ : regs_ok E0 (sr_upd sr_id (ridx (2%bv : bv 5)) WDC.SPX) (regupd RSP 2%bv (getr R 2%bv))) by exact (regs_ok_upd E0 sr_id RSP 2%bv (getr R 2%bv) WDC.SPX (regs_ok_id RSP _ _) SPE).
    assert (CR : CC.cp_regs G.cp0 = sr_upd sr_id (ridx (2%bv : bv 5)) WDC.SPX) by vmc_refl. rewrite CR. intros y. pose proof (RQ y) as Ry. rewrite <- Ry.
    destruct (bv_eq_dec _ y 2%bv) as [->|Hy]; [rewrite getr_same; [reflexivity | discriminate] | rewrite (getr_other _ _ _ _ Hy); unfold RSP; rewrite (getr_other _ _ _ _ Hy); reflexivity]. }
  assert (V10 : ev E0 10 = Z_to_bv 64 wd) by (rewrite <- Ha0; exact (EV' 10%bv ltac:(discriminate))).
  assert (V11 : ev E0 11 = Z_to_bv 64 o) by (rewrite <- Ha1; exact (EV' 11%bv ltac:(discriminate))).
  assert (V32 : ev E0 32 = Z_to_bv 64 dpb) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp - 16) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = wd) by (rewrite V10; apply u64_of_Z; clear - Hwd1 Hwd2 S2 SP1 CL; lia).
  assert (U11 : bv_unsigned (ev E0 11) = o) by (rewrite V11; apply u64_of_Z; clear - O3 O6; lia).
  assert (DPR : 0 <= dpb < 256) by (apply Z.mod_pos_bound; clear; lia).
  assert (U32 : bv_unsigned (ev E0 32) = dpb) by (rewrite V32; apply u64_of_Z; clear - DPR; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 14320) by reflexivity.
  pose proof (CHA.ffrs_le FF sp (sp - 16) Hffrs ltac:(clear; lia)) as Hffrs16.
  assert (STKF : (sp - 16) mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp - 16 /\ sp - 16 <= ar_sptop ar) by (rewrite SCRV; split; [exact S1x | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(o, 24); (hl_tp L - 164, 4); (sp - 16, 16)] : list L5.range). set (Wo := [(sp - 16, 16)] : list L5.range).
  assert (WINC : incl Wo WW) by (intros w [<-|[]]; right; right; left; reflexivity).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    rewrite SCRV. split; [clear - Hin S2 S3 SP1 CL; lia|]. split; [right; left; split; [clear - Hin S2 S3 SP1 CL; lia | clear - Hin; lia]|].
    intros Hs. exfalso. pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(clear - CL; lia) ltac:(clear - SP1 S2 S3; lia) ltac:(clear; lia) Hs). clear - H Hin S2 CL. lia. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)).
  { intros rg Hrg. change (CH.hd_wrs G.HDECL) with [(EVar 2, 0, ELit 16)] in Hrg. destruct Hrg as [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha.
    unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U2 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    exists (sp - 16, 16). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF (sp - 16) G.HDECL a)).
  { intros rg Hrg.
    change (CH.hd_crs G.HDECL) with [(EVar 11, 0, ELit 24); (CHA.SRL3 (EVar 11), 2147450880, ELit 3); (EVar 10, 0, ELit 12); (CHA.SRL3 (EVar 10), 2147450880, ELit 1);
                                     (CHA.SRL3 (EAlu Instr.ALU_ADD (EVar 10) (ELit 4)), 2147450880, ELit 1); (CHA.SRL3 (EAlu Instr.ALU_ADD (EVar 10) (ELit 8)), 2147450880, ELit 1);
                                     (EVar 2, 0, ELit 16)] in Hrg.
    assert (STKSH : forall a, wd <= a < wd + 12 -> CHA.sclientA L ar LB FF (sp - 16) G.HDECL (S a)).
    { intros a Ha. unfold CHA.sclientA. rewrite SCRV. unfold HeapIfaceA.S, SB in *.
      assert (D1 : (ahl_ceil ar) / 8 <= a / 8) by (apply Z.div_le_mono; clear - Ha Hwd1 S2; lia).
      assert (D2 : a / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; clear - Ha Hwd2 SP1; lia).
      assert (D3 : a / 8 < (ar_sptop ar) / 8).
      { apply Z.div_lt_upper_bound; [clear; lia|]. pose proof (Z.div_mod (ar_sptop ar) 16 ltac:(clear; lia)) as DD. rewrite SP16 in DD.
        replace (8 * (ar_sptop ar / 8)) with (ar_sptop ar) by (rewrite DD at 2; rewrite DD at 1; replace (16 * (ar_sptop ar / 16) + 0) with ((2 * (ar_sptop ar / 16)) * 8) by (clear; lia);
                                                              rewrite Z.div_mul by (clear; lia); clear; lia).
        clear - Ha Hwd2. lia. }
      change (2 ^ 47 / 8) with 17592186044416 in *. change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
      split; [pose proof (Z.div_pos (ahl_ceil ar) 8 ltac:(clear - CL; lia) ltac:(clear; lia)); clear - D1 D2 H; lia|].
      split; [do 4 right; left; unfold in_shadow_of, HeapIfaceA.S, SB; split; [clear - D1; lia|]; replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia);
              change ((2 ^ 47 - 1) / 8) with 17592186044415; clear - D2; lia|].
      intros _. unfold HeapIfaceA.S, SB. clear - D3. lia. }
    destruct Hrg as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (split; [vm_compute; reflexivity|]); intros a Ha.
    - unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      destruct (CL5A.infr_wok L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) o 24 a RFx Ofr ltac:(clear - Ha; lia)) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3 in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) o 24 a RFx Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      unfold CHA.sclientA. rewrite SCRV. split; [clear - Ha Hwd1 Hwd2 S2 SP1 CL; lia|]. split; [right; left; split; [clear - Ha Hwd1 Hwd2 S2 SP1 CL; lia | clear - Ha Hwd1; lia]|].
      intros Hs. exfalso. pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(clear - CL; lia) ltac:(clear - SP1 S2 S3; lia) ltac:(clear; lia) Hs). clear - H Ha Hwd1 S2 CL. lia.
    - unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3 in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      replace a with (S wd) by (unfold HeapIfaceA.S, SB; clear - Ha; lia). apply STKSH. clear; lia.
    - unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3 in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite u_add64, U10, (u64_of_Z 4) in Ha by (clear; lia).
      rewrite Z.mod_small in Ha by (clear - Hwd1 Hwd2 S2 SP1 CL; lia). rewrite u64_of_Z in Ha by (clear; lia).
      replace a with (S (wd + 4)) by (unfold HeapIfaceA.S, SB; clear - Ha; lia). apply STKSH. clear; lia.
    - unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3 in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite u_add64, U10, (u64_of_Z 8) in Ha by (clear; lia).
      rewrite Z.mod_small in Ha by (clear - Hwd1 Hwd2 S2 SP1 CL; lia). rewrite u64_of_Z in Ha by (clear; lia).
      replace a with (S (wd + 8)) by (unfold HeapIfaceA.S, SB; clear - Ha; lia). apply STKSH. clear; lia.
    - unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U2 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      try rewrite (Z.mod_small (sp - 16 + 0)) in Ha by (clear - S2 S3 SP1 CL; lia).
      unfold CHA.sclientA. rewrite SCRV. split; [clear - Ha S2 S3 SP1 CL; lia|]. split; [right; left; split; [clear - Ha S2 S3 SP1 CL; lia | clear - Ha; lia]|].
      intros Hs. exfalso. pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(clear - CL; lia) ltac:(clear - SP1 S2 S3; lia) ltac:(clear; lia) Hs). clear - H Ha S2 CL. lia. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - 16 - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; intros q Hq; replace (sp - 16 - 14320 + q) with (sp - 14336 + q) by (clear; lia); apply S5; clear - Hq; lia).
  assert (DEFUP : L5.defined M (sp - 16) (ar_stack_top ar - (sp - 16))).
  { intros q Hq. destruct (Z_lt_dec q 16) as [Hq16|Hq16].
    - replace (sp - 16 + q) with (sp - 14336 + (14320 + q)) by (clear; lia). apply S5. clear - Hq Hq16. lia.
    - replace (sp - 16 + q) with (sp + (q - 16)) by (clear; lia). apply S6. clear - Hq Hq16. lia. }
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[<-|[]]]; apply (L5A.aly_cells L C LAY); [left; reflexivity | right; left; reflexivity] | rewrite IHI; repeat constructor; cbn; clear; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  assert (OSHK : forall a, S o <= a < S o + 3 -> CHA.akept L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold S in Ha; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) o 24 a RFx Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[<-|[<-|[]]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    - pose proof (SHR o 24 a ltac:(clear - O3; lia) ltac:(clear; lia) ltac:(clear - O6; lia) SH) as SRa. unfold hid in O5. clear - Hin SRa O5. lia.
    - rewrite ERRV in Hin. unfold WDC.ERRNO in Hin. pose proof (SHR o 24 a ltac:(clear - O3; lia) ltac:(clear; lia) ltac:(clear - O6; lia) SH) as SRa. clear - Hin SRa. lia.
    - pose proof (SHR o 24 a ltac:(clear - O3; lia) ltac:(clear; lia) ltac:(clear - O6; lia) SH) as SRa. clear - Hin SRa S2 CL. lia. }
  assert (AL0 : (sp - 14336) mod 8 = 0) by (clear - Hsp16; pose proof (Z_div_mod_eq_full (sp - 16) 32) as D; rewrite Hsp16, Z.add_0_r in D;
                                            replace (sp - 14336) with ((4 * ((sp - 16) / 32) - 1790) * 8) by lia; apply Z_mod_mult).
  assert (KSTK : forall a, S (sp - 14336) <= a < S (sp - 14336) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 14336)) / 8 -> CHA.akept L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (PTA.stksh_rng ar sp 14336 a ltac:(clear - S2; lia) AL0 C8 (proj2 SP1) TOP47 ltac:(clear - CL; lia) Ha) as (G1 & G2).
    split; [exact G1|]. split; [right; right; right; right; left; exact G2|]. intros w [<-|[<-|[<-|[]]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; unfold in_shadow_of, S, SB in G2.
    - unfold hid in O5. clear - Hin G2 O5 CL. lia.
    - rewrite ERRV in Hin. unfold WDC.ERRNO in Hin. clear - Hin G2 CL. lia.
    - clear - Hin G2 S2 CL. lia. }
  assert (DEFO : forall LBx LKx crx Ax (Mx : mem) Vx FFx, incl FF FFx -> ri_inv HI LBx FFx LKx crx Ax Mx Vx -> L5.defined Mx o 24).
  { intros LBx LKx crx Ax Mx Vx FFx HFF HHx. destruct Ofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) f (HFF f Hf)) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by (clear; lia). apply FD. clear - Hq F1 F2. lia. }
  assert (FFS0 : nth 0 WDC.FFS [] = []) by reflexivity. assert (FFS2 : nth 2 WDC.FFS [] = []) by reflexivity.
  assert (FFSi : forall i, (i < 8)%nat -> i <> 0%nat -> i <> 2%nat -> nth i WDC.FFS [] = [WDC.FR]).
  { intros i Hi H0 H2. do 8 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). exfalso; lia. }
  assert (BLSi : forall i, i <> 1%nat -> i <> 3%nat -> nth i G.BLS [] = []).
  { intros i H1 H3. do 8 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). destruct i; reflexivity. }

  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => if WDC.isnil (nth i G.BLS []) then cr1 = cr else cr1 = adebit L cr 48).
  set (FLF := fun (E1 : env) => ar_fs ar <= CL5A.uv E1 WDC.FLE < ar_fs ar + 11571200 /\ ~ aclient L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) (CL5A.uv E1 WDC.FLE)).
  set (SSTR := fun (M1 : mem) => exists s', 1 <= Z.of_nat (length s') <= 22 /\ PMLA.str_at (hl_segs L) M1 o (PML.SShort s') /\ L5.defined M1 o 24).
  set (LSTR := fun (g : nat) (E1 : env) (M1 : mem) => let p := CL5A.uv E1 (EVar g) in
                 exists s', 23 <= Z.of_nat (length s') < 48 /\ PMLA.str_at (hl_segs L) M1 o (PML.SLong 48 p s') /\ L5.defined M1 o 24 /\ PMLA.afresh L ar LB FF M1 p 48).
  set (XI := fun (i : nat) (E1 : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) =>
               (i <> 0%nat -> i <> 2%nat -> FLF E1) /\ ((i = 6 \/ i = 7)%nat -> SSTR M1) /\ ((i = 1 \/ i = 3)%nat -> LSTR 66%nat E1 M1)).
  rewrite <- LS in FPM. unfold PMSA.cfg. change 846852 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS WDC.FFS Cred 5 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact GF.plans.
  - exact GF.tags_ok.
  - exact WDC.heap_ok.
  -
    intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ WDC.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X.
  - intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ WDC.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X.
  -
    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ WDC.leaf_ok _ _ _ _ _ HIL) as X. unfold WDC.leaf_chk in X. cbv beta iota zeta in X.
    assert (Hci : nth_error G.CPS i = Some c) by (destruct HIL as (tg & Hc & _); exact Hc).
    assert (Hi8 : (i < 8)%nat) by (change 8%nat with (length G.CPS); apply nth_error_Some; rewrite Hci; discriminate).

    assert (FRM : forall E1 A1 M1 m1, (i <> 0 /\ i <> 2)%nat ->
              CHA.aamb L ar HI GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW G.BLS WDC.FFS Cred 5 i E1 A1 M1 m1 ->
              let F := CL5A.uv E1 WDC.FE in
              CHA.curF FF (sp - 16) WDC.FFS i E1 = (F, 4, sp - 16 + -96 + 32) :: FF /\ env_agree GT.NF E0 E1 /\
              0 <= F /\ F + 1024 <= 140737488355328 /\ F mod 8 = 0 /\ (F + 1024 <= 2147446784 \/ 17594333495296 <= F) /\ ar_fs ar <= F /\ F + 1024 <= ar_fs ar + 11571200
              /\ fframes_apart F 1024 FF /\ (forall u n, In (u, n) LB -> u + n <= F \/ F + 1024 <= u)).
    { intros E1 A1 M1 m1 Hi02 HA. cbv zeta.
      assert (HcF : CHA.curF FF (sp - 16) WDC.FFS i E1 = (CL5A.uv E1 WDC.FE, 4, sp - 16 + -96 + 32) :: FF) by (unfold CHA.curF; rewrite (FFSi i Hi8 (proj1 Hi02) (proj2 Hi02)); reflexivity).
      pose proof HA as (_ & _ & _ & HagE & (cra & LKa & HHa & _) & _). rewrite HcF in HHa.
      pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHa) as WFa. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFa) as RFa.
      destruct (CHA.rf_frm _ _ _ _ RFa _ (or_introl eq_refl)) as (G1 & G2 & G3 & _). unfold ff_addr, ff_class in G1, G2, G3. cbn [fst snd] in G1, G2, G3. change (ff_bytes 4) with 1024 in G2.
      destruct (CHA.rf_fs _ _ _ _ RFa) as ((G0 & G4 & G5) & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
      destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WFa _ (or_introl eq_refl)) as (_ & _ & _ & _ & _ & FAP). cbn [ff_addr ff_class fst snd ff_remove] in FAP. rewrite Z.eqb_refl in FAP. change (ff_bytes 4) with 1024 in FAP.
      split; [exact HcF|]. split; [exact HagE|]. split; [clear - G0 G1; lia|]. split; [clear - G2 G5; lia|]. split; [exact (CHA.mod8_of_64 _ G3)|].
      split; [clear - G1 G2 G4; lia|]. split; [exact G1|]. split; [exact G2|]. split; [intros f Hf; apply FAP; apply in_or_app; left; exact Hf|].
      intros u n Hun. assert (Hun' : In (u, n) (CHA.curB LB G.BLS i E1)) by (unfold CHA.curB; apply in_or_app; right; exact Hun).
      destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFa (u, n) Hun') as (_ & _ & _ & _ & Bfap). cbn [fst snd] in Bfap.
      pose proof (Bfap (CL5A.uv E1 WDC.FE, 4, sp - 16 + -96 + 32) (or_introl eq_refl)) as QF. cbn [ff_addr ff_class fst snd] in QF. change (ff_bytes 4) with 1024 in QF. exact QF. }

    assert (OAP : forall F fl, fframes_apart F 1024 FF -> (F + 1024 <= 2147446784 \/ 17594333495296 <= F) -> 0 <= F -> F + 1024 <= 140737488355328 ->
              ~ aclient L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) fl -> forall q, 0 <= q < 24 ->
              (o + q < sp - 14336 \/ sp <= o + q) /\ (o + q < F \/ F + 24 <= o + q) /\ (o + q < F + 32 \/ F + 1016 <= o + q) /\
              (o + q < F / 8 + WDC.SBz \/ F / 8 + WDC.SBz + 128 <= o + q) /\ o + q <> fl).
    { intros F fl FAP F5 F0 F1 HFL q Hq. pose proof Ofr as (f & Hf & Q1 & Q2). pose proof (FAP f Hf) as AP.
      assert (D1 : F / 8 + WDC.SBz + 128 <= 17594333495296) by (unfold WDC.SBz; assert (F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; clear - F1; lia); clear - H; lia).
      assert (D0 : 0 <= F / 8) by (apply Z.div_pos; clear - F0; lia).
      split; [left; clear - Hq O4 S2; lia|]. split; [clear - Hq AP Q1 Q2; lia|]. split; [clear - Hq AP Q1 Q2; lia|].
      split; [unfold WDC.SBz in *; unfold hid in O5; clear - Hq O5 D0 D1; lia|].
      intros Heq. apply HFL. rewrite <- Heq. exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LB FF (sp - 16) _ o 24 (o + q) Ofr ltac:(clear - Hq; lia))). }

    assert (IMGK : forall a, 65536 <= a < 1400832 -> CHA.akept L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) WW a).
    { intros a Ha. split; [clear - Ha; lia|]. split.
      - right; right; left. rewrite ILO, IHI. split; [clear - Ha; lia | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs) as HS0; clear - Ha HS0; lia].
      - intros w [<-|[<-|[<-|[]]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; [clear - Hin Ha O1 FSLO; lia | rewrite ERRV in Hin; unfold WDC.ERRNO in Hin; clear - Hin Ha; lia
                                                                                     | clear - Hin Ha S2 CL; lia]. }
    assert (IR : L5.img_clear M 65536 1400832) by exact Himg.

    assert (NEWSF : forall E' E2 A1 A2 (M' : mem) m' (M2 : mem) m2 LKa LKb cra crb LBa F fl,
              ri_inv HI LB ((F, 4, sp - 16 + -96 + 32) :: FF) LKa cra A1 M' (vml_of m') -> ri_inv HI LBa ((F, 4, sp - 16 + -96 + 32) :: FF) LKb crb A2 M2 (vml_of m2) ->
              H_off_segments (hl_segs L) (ahid A1 m') ->
              0 <= F -> F + 1024 <= 140737488355328 -> ar_fs ar <= F -> F + 1024 <= ar_fs ar + 11571200 -> ar_fs ar <= fl < ar_fs ar + 11571200 ->
              bv_unsigned (ev E' 54) = F -> bv_unsigned (ev E' 49) = fl -> bv_unsigned (ev E2 54) = F -> bv_unsigned (ev E2 49) = fl ->
              kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA WDC.FE 1016) 8 WDC.FLE) ->
              forall X0, In X0 (WDC.STAT ++ WDC.FLAG) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0).
    { intros E' E2 A1 A2 M' m' M2 m2 LKa LKb cra crb LBa F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W54 W49 T54 T49 KFL X0 HX0.
      unfold WDC.STAT, WDC.FLAG in HX0. cbn [app In] in HX0.
      pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) as WF2.
      assert (VFS : forall y, ar_fs ar <= y < ar_fs ar + 11571200 -> ahid A2 m2 (Z_to_bv 64 y) = false).
      { intros y Hy. apply (CHA.fs_vis L ar C HI HIok GT.NF 0 NF32 _ _ _ _ _ _ m2 y HH2); [destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _); unfold FS_BYTES in G3; clear - Hy G0 G3 CL SP1; lia | unfold FS_BYTES; exact Hy]. }
      destruct HX0 as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
      - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (F + 1016) KFL ltac:(unfold estart, WDC.FE; cbn [a_base a_off edenot]; rewrite W54; reflexivity)) as G0.
        apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv, WDC.FLE in G0. cbn [edenot] in G0. rewrite W49 in G0.
        pose proof (PmHeapIfaceA.aio_flagptr _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 4 (sp - 16 + -96 + 32) (sp - 16 + -96 + 32) fl HH1 HH2 (or_introl eq_refl) (or_introl eq_refl)) as FP.
        change (ff_bytes 4) with 1024 in FP. replace (F + 1024 - 8) with (F + 1016) in FP by (clear; lia). specialize (FP G0).
        eapply CL5.kword64_intro with (A := F + 1016) (z := fl); [unfold estart, WDC.FE; cbn [a_base a_off edenot]; rewrite T54; reflexivity | clear - F0; lia | clear - F1; lia | |].
        + unfold WDC.FLE. cbn [edenot]. rewrite <- (Z_to_bv_bv_unsigned 64 (ev E2 49)). f_equal. exact T49.
        + apply (CL5A.u64_vis (hl_segs L)); [clear - F0; lia | clear - F1; lia | | exact FP]. intros y Hy. apply VFS. clear - Hy F3 F4. lia.
      - eapply CL5.kwr_intro with (A := fl) (N := 1); [unfold estart, WDC.FLE; cbn [a_base a_off edenot]; rewrite T49; clear; lia | reflexivity | | | |].
        + destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & _). clear - HFL1 G0. lia.
        + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
        + destruct (CHA.rf_fs _ _ _ _ RFx) as (_ & G3 & _). unfold FS_BYTES in G3. clear - HFL1 G3 CL SP1. lia.
        + intros y Hy. unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ (VFS (fl + y) ltac:(clear - Hy HFL1; lia))).
          pose proof (CHA.wf_fs_def _ _ _ _ _ _ _ _ WF2) as FD. replace (fl + y) with (ar_fs ar + (fl + y - ar_fs ar)) by (clear; lia). apply FD. unfold FS_BYTES. clear - Hy HFL1. lia. }
    revert X. destruct (Z.eqb pc WDC.RETPC) eqn:Eret; intros X.
    {
      apply andb_prop in X as [X Yalt]. apply andb_prop in X as [X Ya0]. apply andb_prop in X as [X Yfl]. apply andb_prop in X as [X Yr]. apply andb_prop in X as [Xbase Y54].
      apply Nat.ltb_lt in Y54. apply Z.eqb_eq in Eret. subst pc.
      destruct (CHA.retire_chk GT.NF G.HDECL c (nth i G.BLS []) (nth i WDC.FFS [])) as [fle|] eqn:Hrc; [|discriminate]. apply expr_eqb_eq in Yr. subst fle.
      assert (Hi : i = 7%nat \/ i = 3%nat) by (apply orb_prop in Yalt as [Y|Y]; apply Nat.eqb_eq in Y; [left|right]; exact Y).
      assert (Hi02 : (i <> 0 /\ i <> 2)%nat) by (clear - Hi; lia).
      assert (HFi : nth i WDC.FFS [] = [(WDC.FE, 4, -96)]) by (apply FFSi; clear - Hi; lia).
      assert (HcpF : CC.cp_F c = WDC.FX ++ [(WDC.FLE, 0, ELit 1)]) by (apply (WDC.cpF_XF i c Hci); clear - Hi; lia).
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXI]. pose proof HXI as (HXF & HXS & HXL).
      specialize (HXF (proj1 Hi02) (proj2 Hi02)). pose proof HXF as (HFL1 & HFL2).
      destruct (FRM E1 A1 M1 m1 Hi02 HA) as (HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP & FBL). set (F := CL5A.uv E1 WDC.FE) in *. set (fl := CL5A.uv E1 WDC.FLE) in *.
      pose proof (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF) as HFR.
      refine (CBB.exit_retire_sp L ar C HI HIok LYI LYB LYN GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS WDC.FFS Cred 5 STKF SCRP NF32 U2 WINC WOK WRS_OK
                K DEF0 R r WDC.SPX WDC.RETPC i c ps0 WDC.FLE WDC.FE 4 (-96) EVN Hra Hraok SPE _ Xbase HFi Hrc Yfl fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF HFL1 HFL2 _);
        [rewrite LS; exact WDC.ret_at |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE'.

      assert (AHM : CHA.ahpres L ar (CHA.curB LB G.BLS i E1) FF sp 14336 [(o, 24); (hl_tp L - 164, 4)] M M' -> True) by (intros _; exact I).
      clear AHM.
      assert (AHM : CHA.ahpres L ar LB FF sp 14336 [(o, 24); (hl_tp L - 164, 4)] M M').
      { pose proof HP as (HP1 & HP2 & HP3). rewrite SCRV in HP1, HP2, HP3.
        assert (WINX : forall a, aclient L ar LB FF sp 14336 a -> ~ (sp - 16 <= a < sp)).
        { intros a Hc Ha. apply (CHA.client_high L ar LYI GT.NF (sp - 16) G.HDECL STKF SCRP NF32 LB FF sp 14336 a RFx Hc); [clear - Ha S2; lia | clear - Ha; lia]. }
        assert (SCRX : forall a, aclient L ar LB FF sp 14336 a -> aclient L ar LB FF (sp - 16) 14320 a).
        { intros a Hc. apply (CHA.aclient_scr _ _ L ar LB FF sp 14336 (sp - 16) 14320 a Hc). intros x Hx. clear - Hx. lia. }
        split; [|split].
        - intros a (Ha & Hcl & Ho). apply HP1. split; [exact Ha|]. split; [exact (SCRX a Hcl)|].
          intros w Hw Hin. destruct Hw as [<-|[<-|[<-|[]]]]; [exact (Ho _ (or_introl eq_refl) Hin) | exact (Ho _ (or_intror (or_introl eq_refl)) Hin)|].
          unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (WINX a Hcl ltac:(clear - Hin; lia)).
        - intros q Hq. destruct (Z_lt_dec q 14320) as [Hlt|Hge].
          + replace (sp - 14336 + q) with (sp - 16 - 14320 + q) by (clear; lia). apply HP2. clear - Hq Hlt. lia.
          + apply (HP3 (sp - 14336 + q)); [clear - Hq S2 S3 SP1 CL; lia | right; left; split; [clear - Hq Hge S2 S3 SP1 CL; lia | clear - Hq Hge; lia] | apply S5; exact Hq].
        - intros a Ha Hcl Hd. apply (HP3 a Ha); [exact (SCRX a Hcl) | exact Hd]. }
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (W2 : bv_unsigned (ev E' 2) = sp - 16) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
      assert (W54 : bv_unsigned (ev E' 54) = F) by (rewrite <- (proj1 Hag 54%nat) by exact Y54; reflexivity).
      assert (W49 : bv_unsigned (ev E' 49) = fl) by (rewrite <- (proj1 Hag 49%nat) by (clear - Y54; lia); reflexivity).
      assert (RA0' : PMSA.a0 R' 0).
      { unfold PMSA.a0. replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ HLFv Ya0). reflexivity. }
      pose proof (DEFO _ _ _ _ _ _ _ (incl_refl FF) HH1) as DO'.
      assert (D0 : 0 <= F / 8) by (apply Z.div_pos; clear - F0; lia). assert (D1 : F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; clear - F1; lia).
      set (SgO := fun a => M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).

      assert (OO : PTA.out SgO o 24).
      { split; [exact O3|]. split; [clear - O6; lia|]. intros y Hy. unfold SgO. apply HFR. rewrite HcpF.
        destruct (OAP F fl FAP F2 F0 F1 HFL2 (y - o) ltac:(clear - Hy; lia)) as (X1 & X2 & X3 & X4 & X5). replace (o + (y - o)) with y in * by (clear; lia).
        exact (WDC.outside_FXF E' sp F fl y W2 W54 W49 ltac:(clear - Hy O3 O6; lia) ltac:(clear - S2 S3 SP1 CL; lia) X1 X2 X3 X4 X5). }
      destruct Hi as [-> | ->].
      -
        destruct (HXS (or_intror eq_refl)) as (s' & Hls & HSTR & HDF1).
        assert (BL0 : nth 7 G.BLS [] = []) by reflexivity.
        assert (HcB : CHA.curB LB G.BLS 7 E1 = LB) by (unfold CHA.curB; rewrite BL0; reflexivity).
        assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite BL0 in HC1; exact HC1). subst cr1.
        rewrite HcB in HH1.
        apply (Hcont fx' R' M' model2 LB cr LB [(o, 24); (hl_tp L - 164, 4)] LK1 A1 HFP); [| exact HRP | exact AHM | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
        split; [exact RA0'|]. split; [|split; reflexivity]. exists s'. split; [clear - Hls; lia|]. left. split; [clear - Hls; lia|].
        split; [|split; [exact DO' | split; reflexivity]].
        destruct HSTR as (Hl22 & Hb0 & Hbs & Hnul). unfold PMLA.str_at, L5.lstr_short.
        split; [exact Hl22|]. split; [apply (PTA.u8_ag (hl_segs L) M1 M' SgO (fun a Ha => Ha)); [apply (PTA.out_sub _ _ _ _ _ OO); clear; lia | exact Hb0]|].
        split; [apply (PTA.bytes_ag (hl_segs L) M1 M' SgO (fun a Ha => Ha)); [apply (PTA.out_sub _ _ _ _ _ OO); clear - Hl22; lia | exact Hbs]|].
        apply (PTA.u8_ag (hl_segs L) M1 M' SgO (fun a Ha => Ha)); [apply (PTA.out_sub _ _ _ _ _ OO); clear - Hl22; lia | exact Hnul].
      -
        destruct (HXL (or_intror eq_refl)) as (s' & Hls & HSTR & HDF1 & HAF1). cbv zeta in HSTR, HAF1.
        set (p := CL5A.uv E1 (EVar 66)) in *.
        assert (HcB : CHA.curB LB G.BLS 3 E1 = (p, 48) :: LB) by (unfold CHA.curB; change (nth 3 G.BLS []) with [(EVar 66, ELit 48)]; unfold CH2.den; cbn [map fst snd app]; reflexivity).
        assert (Hcr1 : cr1 = adebit L cr 48) by (unfold Cred in HC1; change (nth 3 G.BLS []) with [(EVar 66, ELit 48)] in HC1; exact HC1). subst cr1.
        rewrite HcB in HH1.
        destruct (PmHeapIfaceA.aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB & _).
        destruct (WB (p, 48) (or_introl eq_refl)) as (B1 & B2 & B3 & _ & B5 & B6 & B7). cbn [fst snd] in B1, B2, B3, B5, B6, B7.
        pose proof B1 as (P0 & _ & P16 & _ & P4 & (P5 & P6 & P7)). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in P6, B7.
        assert (OP : PTA.out SgO p 48).
        { split; [clear - P5; lia|]. split; [clear - P7; lia|]. intros y Hy. unfold SgO. apply HFR. rewrite HcpF.
          apply (WDC.outside_FXF E' sp F fl y W2 W54 W49); [clear - Hy P5 P7; lia | clear - S2 S3 SP1 CL; lia | left; clear - Hy P4 S2; lia | clear - Hy B7 F3 F4; lia | clear - Hy B7 F3 F4; lia | | clear - Hy B7 HFL1; lia].
          unfold WDC.SBz. clear - Hy P6 D0 D1. lia. }
        assert (OPS : forall a, in_shadow_of p 48 a -> SgO a).
        { intros a Ha. pose proof (SHR p 48 a ltac:(clear - P5; lia) ltac:(clear; lia) P7 Ha) as SRa.
          destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & G4 & G5) & _). unfold FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in G4, G5.
          unfold SgO. apply HFR. rewrite HcpF.
          apply (WDC.outside_FXF E' sp F fl a W2 W54 W49); [clear - SRa; lia | clear - S2 S3 SP1 CL; lia | left; clear - SRa S2 CL; lia | clear - SRa F2; lia | clear - SRa F2; lia | | clear - SRa HFL1 G0 G4; lia].
          destruct (Z_lt_dec a (F / 8 + WDC.SBz)) as [Hlt|Hge]; [left; exact Hlt|]. destruct (Z_lt_dec a (F / 8 + WDC.SBz + 128)) as [Hlt2|Hge2]; [|right; clear - Hge2; lia].
          exfalso. apply (CL5A.sh_apart2 p 48 F 1024 a P5 F0 ltac:(clear; lia) ltac:(clear; lia) (CHA.mod8_of_16 _ P16) F8 ltac:(clear - B7 F3 F4; lia) Ha).
          apply (CL5A.shreg_in_shadow F 128 a F8 ltac:(clear; lia)). unfold SB, WDC.SBz in *. clear - Hge Hlt2. lia. }
        apply (Hcont fx' R' M' model2 ((p, 48) :: LB) (adebit L cr 48) LB [(o, 24); (hl_tp L - 164, 4)] LK1 A1 HFP); [| exact HRP | exact AHM | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
        split; [exact RA0'|]. split; [|split; reflexivity]. exists s'. split; [clear - Hls; lia|]. right. exists p. split; [exact Hls|].
        split; [exact (PTA.str_long_ag (hl_segs L) M1 M' SgO (fun a Ha => Ha) o 48 p s' OO OP HSTR)|]. split; [exact DO'|].
        split; [|split; reflexivity].
        destruct HAF1 as (_ & HBA & HFA & _ & HSB1). split; [exact B1|]. split; [exact HBA|]. split; [exact HFA|]. split; [exact B2|].
        exact (PTA.shadow_blk_ag M1 M' SgO (fun a Ha => Ha) p 48 ltac:(clear; lia) OPS (CHA.mod8_of_16 _ P16) HSB1). }
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate X].
    destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate X].
    apply andb_prop in X as [Ypc X]. apply Z.eqb_eq in Ypc.
    assert (Hj8 : (j < 8)%nat) by (change 8%nat with (length G.CPS); apply nth_error_Some; rewrite Hcj; discriminate).
    revert X. destruct (CIFA.fp_site RSEGS pc) as [hv|] eqn:Hfs; intros X.
    {
      apply andb_prop in X as [X Xsite]. apply andb_prop in X as [Xchk Xsame].
      assert (SITE : pc = 846920 /\ (i = 0 /\ j = 2)%nat \/ pc = 848356 /\ (i = 4 /\ j = 5)%nat).
      { unfold WDC.INLS in Xsite. cbn [existsb fst snd] in Xsite.
        repeat (apply orb_prop in Xsite as [Xs|Xsite]; [apply andb_prop in Xs as [Xs X3]; apply andb_prop in Xs as [X1 X2]; apply Z.eqb_eq in X1; apply Nat.eqb_eq in X2, X3; rewrite <- X1, <- X2, <- X3; clear; lia|]).
        discriminate Xsite. }
      assert (Hpcr : 0 <= pc /\ pc + 4 < 2 ^ 64) by (clear - SITE; lia).
      refine (CIFA.inlF_leaf L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS WDC.FFS Cred 5 STKF SCRP NF32 U2 WINC WOK WRS_OK G.CPS K PMSA.fp_ok XI
                i c ps0 j cj 4 hv Hcj Xchk Xsame _ _ ltac:(clear; lia) _ _ _).
      - rewrite Ypc. exact (proj1 Hpcr).
      - rewrite Ypc. exact (proj2 Hpcr).
      - rewrite Ypc. rewrite LS. exact (CIFA.fp_site_step RSEGS pc hv (proj1 Hpcr) (proj2 Hpcr) Hfs).
      - intros E E' R1 R' A1 M1 m1 M' m' E2 HAt HA HXI Hag HLF Hag2.
        destruct HXI as (HF & _). split; [|split; intros ?; exfalso; clear - SITE H; lia].
        intros Hj0 Hj2. assert (Hi02 : (i = 4)%nat) by (clear - SITE Hj2; lia). subst i.
        assert (NX4 : (54 < CC.cp_nx c)%nat) by (unfold G.CPS in Hci; cbn [nth_error] in Hci; injection Hci as <-; apply Nat.ltb_lt; vm_compute; reflexivity).
        assert (FLV : CL5A.uv E2 WDC.FLE = CL5A.uv E WDC.FLE).
        { unfold CL5A.uv, WDC.FLE. cbn [edenot]. rewrite <- (proj1 Hag2 49%nat) by (clear - NX4; lia). rewrite <- (proj1 Hag 49%nat) by (clear - NX4; lia). reflexivity. }
        unfold FLF. rewrite FLV. exact (HF ltac:(clear; lia) ltac:(clear; lia)).
      - intros E E2 cr1 HC _. unfold Cred in *. rewrite (BLSi i ltac:(clear - SITE; lia) ltac:(clear - SITE; lia)) in HC.
        rewrite (BLSi j ltac:(clear - SITE; lia) ltac:(clear - SITE; lia)). exact HC. }
    revert X. destruct (Z.eqb pc WDC.PC_SM) eqn:Esm; intros X.
    {
      apply Z.eqb_eq in Esm. rewrite Esm in Ypc.
      apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Yfoot]. apply andb_prop in X as [Y1 Y2]. apply Nat.eqb_eq in Y1, Y2. subst i j.
      lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
      apply andb_prop in Y5 as [Ynx Ycsp]. apply Nat.eqb_eq in Ynx. apply Z.eqb_eq in Ycsp.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA _].
      pose proof (CRA.smalloc_leaf_u L ar C HI HIok LYI LYR 7028736 LYH GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS WDC.FFS Cred 5 STKF SCRP NF32 U2 V4 WINC WOK Hffrs16 CRS_OK WRS_OK IMG_OK
                    G.CPS K PMSA.fp_ok DEF0 DEFUP GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil (fun _ => False) 4 (List.filter (WDC.sm_ok ps0 2) (CC.cp_know cj)) 2%nat c ps0 4%nat cj ci) as SML.
      rewrite (L5A.aly_scr_sm L C LAY), (L5A.aly_sm4 L C LAY) in SML.
      refine (SML ltac:(do 4 right; left; reflexivity) Hcj Hchk Ypc _ _ _ _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _).
      - rewrite Ynx, Ycsp. reflexivity.
      - rewrite !BLSi by (clear; lia). reflexivity.
      - intros X0 HX0. apply filter_In in HX0 as [_ HX0]. unfold WDC.sm_ok in HX0. rewrite Ynx. left. exact HX0.
      - intros X0 E2 LB2 FF2 LK2 cr2 A2 M2 m2 [].
      - rewrite FFS2. cbn [length Z.of_nat]. clear. lia.
      - intros Ea Eb cr1 HC _. unfold Cred in *. rewrite !BLSi in * by (clear; lia). exact HC.
      -
        intros R2 M2 m2 F fl LK' cr1 HRP Ha0' SMF HH2. unfold CHA.curB, CHA.curF in SMF. rewrite BLSi in SMF by (clear; lia). rewrite FFS2 in SMF. cbn [CH2.den CHA.denF map app] in SMF.
        destruct SMF as [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Zp]. rewrite Ynx.
        split; [|split; intros H9; exfalso; clear - H9; lia]. intros _ _.
        pose proof (CH2.retEx_ghost E' 49 [Z_to_bv 64 fl] R2 0 ltac:(cbn; clear; lia)) as G49. cbn [nth Nat.add] in G49.
        assert (T49 : CL5A.uv (CH2.retEx E' 49 [Z_to_bv 64 fl] R2) WDC.FLE = fl).
        { unfold CL5A.uv, WDC.FLE. cbn [edenot]. rewrite G49. apply u64_of_Z. unfold FS_BYTES in Z7. destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _). unfold FS_BYTES in G3. clear - Z7 G0 G3 CL SP1. lia. }
        unfold FLF. rewrite T49. split; [unfold FS_BYTES in Z7; exact Z7|]. intros Hc. apply Z8.
        eapply CHA.aclient_scr; [eapply CHA.aclient_incl; [apply incl_refl | apply incl_tl, incl_refl | exact Hc] | intros y Hy; clear - Hy; lia]. }
    revert X. destruct (Z.eqb pc WDC.PC_DT) eqn:Edt; intros X.
    {
      apply Z.eqb_eq in Edt. rewrite Edt in Ypc.
      apply andb_prop in X as [X Ydpr]. apply andb_prop in X as [X Yflc]. apply andb_prop in X as [X Yoe]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10].
      apply andb_prop in X as [X Ytl]. apply andb_prop in X as [X Ycal]. apply andb_prop in X as [Y1 Y2]. apply Nat.eqb_eq in Y1, Y2. subst i j.
      unfold WDC.callee in Ycal. apply andb_prop in Ycal as [Yfoot Y5].
      unfold WDC.twin_ok in Ytl. revert Y5 Ytl.
      destruct (WDC.callee_ci ps0 5 6 c cj 12800 0 [] WDC.DT_W WDC.NEWS_C (Some (ELit 1))) as [ci1|] eqn:Hchk1; [|intros Y5; discriminate Y5]. intros Y5 Ytl. apply Z.eqb_eq in Y5. rename Y5 into Ycsp.
      destruct (nth_error G.CPS 1) as [ctl|] eqn:Hctl; [|discriminate Ytl].
      destruct (WDC.callee_ci ps0 5 1 c ctl 12800 1 [] WDC.DT_W WDC.NEWS_C (Some (ELit 1))) as [ci2|] eqn:Hchk2; [|discriminate Ytl].
      apply andb_prop in Ytl as [Ycsp2 Ypc2]. apply Z.eqb_eq in Ycsp2, Ypc2.
      assert (Hi06 : (5 <> 0 /\ 5 <> 2)%nat) by (clear; lia).
      assert (FFSi' : nth 5 WDC.FFS [] = [WDC.FR]) by reflexivity. assert (FFS10 : nth 6 WDC.FFS [] = [WDC.FR]) by reflexivity. assert (FFS3 : nth 1 WDC.FFS [] = [WDC.FR]) by reflexivity.
      assert (BLSi' : nth 5 G.BLS [] = []) by reflexivity. assert (BLS10 : nth 6 G.BLS [] = []) by reflexivity. assert (BLS3 : nth 1 G.BLS [] = [(EVar 66, ELit 48)]) by reflexivity.
      assert (NX2 : CH2.ci_nx ci2 = 66%nat).
      { pose proof (WDC.custom_chk_nx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk2) as G0. rewrite G0. pose proof Hctl as Hctl'. unfold G.CPS in Hctl'. cbn [nth_error] in Hctl'.
        injection Hctl' as Hctl'. rewrite <- Hctl'. reflexivity. }
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI]. pose proof HXI as (HXF & _).
      specialize (HXF (proj1 Hi06) (proj2 Hi06)). pose proof HXF as (HFL1 & HFL2).
      destruct (FRM E1 A1 M1 m1 Hi06 HA) as (HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP & FBL). set (F := CL5A.uv E1 WDC.FE) in *. set (fl := CL5A.uv E1 WDC.FLE) in *.
      assert (HcB : CHA.curB LB G.BLS 5 E1 = LB) by (unfold CHA.curB; rewrite BLSi'; reflexivity).
      assert (NX54 : (54 < CC.cp_nx c)%nat) by (unfold G.CPS in Hci; cbn [nth_error] in Hci; injection Hci as <-; apply Nat.ltb_lt; vm_compute; reflexivity).
      refine (CB2.callee_leaf2 L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS WDC.FFS Cred 5 STKF SCRP NF32 U2 V4 WINC WOK Hffrs16 CRS_OK WRS_OK IMG_OK
                G.CPS K PMSA.fp_ok DEF0 DEFUP GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil WDC.PC_DT 12800 4 0%nat [] WDC.DT_W WDC.NEWS_C (Some (ELit 1)) 1%nat [] WDC.DT_W WDC.NEWS_C (Some (ELit 1))
                5%nat c ps0 6%nat cj ci1 1%nat ctl ci2 Hcj Hctl Hchk1 Hchk2 Ypc2 Ycsp2 Ypc _ _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite FFS10, FFSi'; reflexivity | rewrite FFS3, FFSi'; reflexivity | rewrite FFSi'; cbn [length Z.of_nat]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite BLSi' in HC1; exact HC1). subst cr1.
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & Hdf1).
      assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')) by exact (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW G.BLS WDC.FFS Cred 5 5%nat E1 A1 M' m' HA').
      assert (W32 : bv_unsigned (ev E' 32) = dpb) by (rewrite <- (proj1 HagE' 32%nat) by (apply Nat.ltb_lt; reflexivity); exact U32).
      assert (W11 : bv_unsigned (ev E' 11) = o) by (rewrite <- (proj1 HagE' 11%nat) by (apply Nat.ltb_lt; reflexivity); exact U11).
      assert (W54 : bv_unsigned (ev E' 54) = F) by (rewrite <- (proj1 Hag 54%nat) by exact NX54; reflexivity).
      assert (W49 : bv_unsigned (ev E' 49) = fl) by (rewrite <- (proj1 Hag 49%nat) by (clear - NX54; lia); reflexivity).
      assert (REG : forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
      { intros q e0 z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (UO : forall k v, WDC.has (SR.ps_cells ps0) (KWord (SA WDC.OE k) 1 (ELit v)) = true -> 0 <= k < 24 -> 0 <= v < 256 -> L5.u8_at (hl_segs L) M' (o + k) v).
      { intros k v Hk Hk24 Hv. pose proof (proj1 (Forall_forall _ _) HK _ (CC.has_cell_In _ _ Hk)) as KC.
        pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (o + k) KC ltac:(unfold estart, WDC.OE; cbn [a_base a_off edenot]; rewrite W11; reflexivity)) as G0.
        apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite u64_of_Z in G0 by (clear - Hv; lia). exact G0. }
      unfold WDC.o_empty in Yoe. apply andb_prop in Yoe as [Yo0 Yo1].
      eexists. eexists. split; [exact (DT_OK LB ((F, 4, sp - 16 + -96 + 32) :: FF) LK1 cr A1 dpb o (sp - 16 + CH2.ci_csp ci1) (CC.cp_pc cj))|].
      split.
      {
        unfold PMSA.a0, PMSA.a1.
        split; [exact (REG 10%nat _ _ Y10 ltac:(cbn [edenot]; exact W32))|]. split; [clear - DPR; lia|].
        split; [exact (REG 11%nat _ _ Y11 ltac:(cbn [edenot]; exact W11))|].
        split.
        { unfold PMLA.str_at, L5.lstr_short. cbn [length Z.of_nat]. split; [clear; lia|].
          split; [replace (2 * 0) with 0 by reflexivity; replace o with (o + 0) at 1 by (clear; lia); exact (UO 0 0 Yo0 ltac:(clear; lia) ltac:(clear; lia))|].
          split; [intros q Hq; cbn [length] in Hq; clear - Hq; lia | rewrite Z.add_0_r; exact (UO 1 0 Yo1 ltac:(clear; lia) ltac:(clear; lia))]. }
        split; [exact (DEFO _ _ _ _ _ _ _ (incl_tl _ (incl_refl FF)) HH1)|].
        split.
        { split; [destruct Ofr as (f & Hf & G1 & G2); exists f; split; [right; exact Hf | split; assumption]|]. split; [exact O8|].
          change (24 / 8) with 3. apply (CL5A.shadow_zero_same M M'); [|exact Osh]. intros j0 Hj0. exact (Hfr1 (S o + j0) (OSHK (S o + j0) ltac:(clear - Hj0; lia))). }
        split.
        { unfold PMSA.stksh. assert (DTS : PMFCA.DT_SCR = 12800) by reflexivity. rewrite DTS.
          rewrite Ycsp. apply (PTA.stksh_mono ar M' sp 14336 (sp - 16 + -96) 12800); [| exact AL0 | | clear; lia].
          - apply (PTA.stksh_ag ar M M' sp 14336); [|exact Hstksh]. intros a Ha. exact (Hfr1 a (KSTK a Ha)).
          - clear - Hsp16. pose proof (Z_div_mod_eq_full (sp - 16) 32) as D. rewrite Hsp16, Z.add_0_r in D.
            replace (sp - 16 + -96 - 12800) with ((4 * ((sp - 16) / 32) - 1612) * 8) by lia. apply Z_mod_mult. }
        split; [unfold PMLA.img_ro; cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth]; intros a Ha; rewrite (Hfr1 a (IMGK a Ha)); exact (IR a Ha)|].
        split; [exact Hcred|].
        rewrite Ycsp. clear - Hsp16. pose proof (Z_div_mod_eq_full (sp - 16) 32) as D. rewrite Hsp16, Z.add_0_r in D.
        replace (sp - 16 + -96) with (((sp - 16) / 32 - 3) * 32) by lia. apply Z_mod_mult. }

      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & (s' & Hls' & HGR) & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      destruct HV as (_ & _ & HV3 & _ & HV5).
      assert (WCR : forall w a, In w [(o, 24); (hl_tp L - 164, 4)] -> L5.in_rng w a -> exists r0, In r0 WDC.DT_W /\ CHA.in_reg E' r0 a).
      { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
        - exists (WDC.OE, 0, ELit 24). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, WDC.OE. cbn [a_base a_off edenot]. rewrite W11.
          rewrite u64_of_Z by (clear; lia). clear - Hin. lia.
        - exists (ELit 0, WDC.ERRNO, ELit 4). split; [right; left; reflexivity|]. unfold CHA.in_reg, estart, elenZ, WDC.ERRNO. cbn [a_base a_off edenot]. rewrite !u64_of_Z by (clear; lia).
          rewrite ERRV in Hin. unfold WDC.ERRNO in Hin. clear - Hin. lia. }
      assert (WCK : forall w a, In w [(o, 24); (hl_tp L - 164, 4)] -> L5.in_rng w a -> ~ CHA.akept L ar LB FF (sp - 16) (CH.hd_scr G.HDECL) WW a).
      { intros w a [<-|[<-|[]]] Hin (Ka & Kcl & Ko); [exact (Ko (o, 24) ltac:(left; reflexivity) Hin) | exact (Ko (hl_tp L - 164, 4) ltac:(right; left; reflexivity) Hin)]. }
      destruct HGR as [(Hl22 & HSTR & HDO & -> & ->) | (p & Hl48 & HSTR & HDO & HAF & -> & ->)].
      +
        left. exists []. split; [reflexivity|]. cbv zeta.
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci1) [] R2 : env_agree (CH2.ci_nx ci1) E' (CH2.retEx E' (CH2.ci_nx ci1) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci1) [] R2) in *.
        assert (T54 : bv_unsigned (ev E2 54) = F) by (rewrite <- (proj1 Hag2 54%nat) by (clear - HV3 NX54; lia); exact W54).
        assert (T49 : bv_unsigned (ev E2 49) = fl) by (rewrite <- (proj1 Hag2 49%nat) by (clear - HV3 NX54; lia); exact W49).
        split; [cbn [edenot]; exact Ha0'|]. split; [cbn [CH2.den map app]; apply incl_refl|]. split; [exact WCR|]. split; [exact WCK|].
        split; [unfold CHA.curB; rewrite BLS10; cbn [CH2.den map app]; exact HH2|].
        split; [unfold Cred; rewrite BLS10; reflexivity|].
        split.
        { unfold XI. split; [intros _ _; unfold FLF; replace (CL5A.uv E2 WDC.FLE) with fl by (unfold CL5A.uv, WDC.FLE; cbn [edenot]; symmetry; exact T49); exact HXF|].
          split; [|intros H9; exfalso; clear - H9; lia].
          intros _. exists s'. split; [clear - Hls' Hl22; lia|]. split; [exact HSTR | exact HDO]. }
        intros X0 HX0 _. exact (NEWSF E' E2 A1 A2 M' m' M2 m2 _ _ _ _ _ F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W54 W49 T54 T49 (proj1 (Forall_forall _ _) HK _ (CC.has_cell_In _ _ Yflc)) X0 HX0).
      +
        right. exists [Z_to_bv 64 p]. split; [reflexivity|]. cbv zeta.
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci2) [Z_to_bv 64 p] R2 : env_agree (CH2.ci_nx ci2) E' (CH2.retEx E' (CH2.ci_nx ci2) [Z_to_bv 64 p] R2)) as Hag2.
        pose proof (CH2.retEx_ghost E' (CH2.ci_nx ci2) [Z_to_bv 64 p] R2 0 ltac:(cbn; clear; lia)) as G88.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci2) [Z_to_bv 64 p] R2) in *.
        rewrite NX2 in Hag2, G88. cbn [nth Nat.add] in G88.
        destruct HAF as (HAR & HBA & HFA & HDF2 & HSB2). pose proof HAR as (P0 & _ & P16 & _ & P4 & (P5 & P6 & P7)).
        assert (T88 : CL5A.uv E2 (EVar 66) = p) by (unfold CL5A.uv; cbn [edenot]; rewrite G88; apply u64_of_Z; clear - P5 P7; lia).
        assert (T54 : bv_unsigned (ev E2 54) = F) by (rewrite <- (proj1 Hag2 54%nat) by (clear; lia); exact W54).
        assert (T49 : bv_unsigned (ev E2 49) = fl) by (rewrite <- (proj1 Hag2 49%nat) by (clear; lia); exact W49).
        assert (HcB5 : CHA.curB LB G.BLS 1 E2 = (p, 48) :: LB).
        { unfold CHA.curB. rewrite BLS3. unfold CH2.den. cbn [map fst snd app]. change (bv_unsigned (edenot E2 (EVar 66))) with (CL5A.uv E2 (EVar 66)). rewrite T88. f_equal. }
        split; [cbn [edenot]; exact Ha0'|]. split; [cbn [CH2.den map app]; apply incl_refl|]. split; [exact WCR|]. split; [exact WCK|].
        split; [rewrite HcB5; exact HH2|].
        split; [unfold Cred; rewrite BLS3; reflexivity|].
        split.
        { unfold XI. split; [intros _ _; unfold FLF; replace (CL5A.uv E2 WDC.FLE) with fl by (unfold CL5A.uv, WDC.FLE; cbn [edenot]; symmetry; exact T49); exact HXF|].
          split; [intros H9; exfalso; clear - H9; lia|].
          intros _. unfold LSTR. cbv zeta. rewrite T88. exists s'. split; [exact Hl48|]. split; [exact HSTR|]. split; [exact HDO|].
          split; [exact HAR|]. split; [exact HBA|]. split; [intros f Hf; apply HFA; right; exact Hf|]. split; [exact HDF2 | exact HSB2]. }
        intros X0 HX0 _. exact (NEWSF E' E2 A1 A2 M' m' M2 m2 _ _ _ _ _ F fl HH1 HH2 Hoff F0 F1 F3 F4 HFL1 W54 W49 T54 T49 (proj1 (Forall_forall _ _) HK _ (CC.has_cell_In _ _ Yflc)) X0 HX0). }
    revert X. destruct (Z.eqb pc WDC.PC_SETSH) eqn:Esh; intros X; [|discriminate X].

    apply Z.eqb_eq in Esh. rewrite Esh in Ypc.
    apply andb_prop in X as [X Ynx54]. apply andb_prop in X as [X Yfl]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10].
    apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Ybeq]. apply andb_prop in X as [Yij Yfeq].
    apply Nat.ltb_lt in Ynx54.
    lazymatch type of Y5 with match ?t with _ => _ end = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end. apply Z.eqb_eq in Y5. rename Y5 into Ycsp.
    assert (Hij : (i = 6 /\ j = 7 \/ i = 1 /\ j = 3)%nat).
    { apply orb_prop in Yij as [Yij|Yij]; apply andb_prop in Yij as [Y1 Y2]; apply Nat.eqb_eq in Y1, Y2; [left | right]; split; assumption. }
    assert (Hi02 : (i <> 0 /\ i <> 2)%nat) by (clear - Hij; lia).
    assert (HFi : nth i WDC.FFS [] = [WDC.FR]) by (apply FFSi; clear - Hij; lia).
    assert (NXci : (66 < CH2.ci_nx ci)%nat).
    { pose proof (WDC.custom_chk_nx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk) as G0. rewrite G0. unfold G.CPS in Hcj.
      destruct Hij as [(_ & ->)|(_ & ->)]; cbn [nth_error] in Hcj; injection Hcj as <-; apply Nat.ltb_lt; vm_compute; reflexivity. }
    intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
    pose proof HXi as (HXF & HXS & HXL). specialize (HXF (proj1 Hi02) (proj2 Hi02)). pose proof HXF as (HFL1 & HFL2).
    destruct (FRM E A1 M1 m1 Hi02 HA) as (HcF & HagE & F0 & F1 & F8 & F2 & F3 & F4 & FAP & FBL). set (F := CL5A.uv E WDC.FE) in *. set (fl := CL5A.uv E WDC.FLE) in *.
    assert (V49 : CL5A.uv E' WDC.FLE = fl) by (unfold fl, CL5A.uv, WDC.FLE; cbn [edenot]; rewrite <- (proj1 Hag 49%nat) by (clear - Ynx54; lia); reflexivity).
    pose proof (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF) as HFR.
    assert (HcpF : CC.cp_F c = WDC.FX) by (apply (WDC.cpF_X i c Hci); clear - Hij; lia).
    refine (CRSH2.setsh_leaf L ar C HI HIok LYI LYR LYB GT.NF E0 M model A LB FF LK (sp - 16) G.HDECL WW Wo G.BLS WDC.FFS Cred 5 STKF SCRP NF32 U2 V4 WINC WOK Hffrs16 CRS_OK WRS_OK IMG_OK
              G.CPS K PMSA.fp_ok DEF0 DEFUP GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil
              WDC.PC_SETSH 245 256 SETSH 256 WDC.NEWS_C i c ps0 j cj ci WDC.FE 4 (-96) WDC.FLE (EAlu Instr.ALU_ADD (CHA.SRL3 WDC.FE) (ELit WDC.SBz))
              Hcj _ Ypc ltac:(clear; lia) HFi Yfeq Ybeq ltac:(clear; lia) Y10 _ Y11 _ Yfl (le_n _) _
              fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _ _ _).
    -- exact Hchk.
    -- intros Ex. unfold CL5A.uv. cbn [edenot]. rewrite AX2S.u_add64. unfold CHA.SRL3. rewrite (CL5A.elen_srl3' Ex WDC.FE : bv_unsigned (edenot Ex (EAlu Instr.ALU_SRL WDC.FE (ELit 3))) = CL5A.uv Ex WDC.FE / 8).
      unfold WDC.SBz, SB. rewrite u64_of_Z by (clear; lia). pose proof (CL5A.uv_range Ex WDC.FE) as UR. unfold CL5A.uv in UR |- *.
      apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; clear - UR; lia | clear; lia]|]. pose proof (CL5A.div8_le _ _ (proj2 (conj (proj1 UR) (Z.lt_le_incl _ _ (proj2 UR))))) as D8.
      change (2 ^ 64 / 8) with 2305843009213693952 in D8. clear - D8. lia.
    -- intros X0 HX0. unfold WDC.NEWS_C, WDC.STAT, WDC.FLAG in HX0. cbn [In app] in HX0.
      destruct HX0 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [left; reflexivity | left; reflexivity | left; reflexivity | right; left; reflexivity | right; right; reflexivity].
    -- intros Ea Eb crx Hc _. unfold Cred in *. destruct Hij as [(-> & ->)|(-> & ->)]; exact Hc.
    -- rewrite V49. unfold FS_BYTES. exact HFL1.
    -- intros Ea Eb Hg. unfold CL5A.uv, WDC.FLE. cbn [edenot]. rewrite (proj1 Hg 49%nat) by (clear - Ynx54; lia). reflexivity.
    -- cbv zeta. intros R2 M2 m2 A2 LK2 crx HRP HP1 HP3 HPOI HA2 Hmo2 Hrt2 HH2.
      fold F. set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
      pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' E2) as Hag2.
      assert (T49 : CL5A.uv E2 WDC.FLE = fl) by (rewrite <- V49; unfold CL5A.uv, WDC.FLE; cbn [edenot]; rewrite <- (proj1 Hag2 49%nat) by (clear - NXci; lia); reflexivity).
      assert (W2 : bv_unsigned (ev E' 2) = sp - 16) by (rewrite <- (proj1 Hag 2%nat) by (clear - Ynx54; lia); rewrite <- (proj1 HagE 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
      assert (W54 : bv_unsigned (ev E' 54) = F) by (rewrite <- (proj1 Hag 54%nat) by (clear - Ynx54; lia); reflexivity).
      pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2)) as RF2.
      assert (Ofr2 : CL5A.ainfr (CHA.curF FF (sp - 16) WDC.FFS i E) o 24) by (rewrite HcF; destruct Ofr as (f & Hf & Q1 & Q2); exists f; split; [right; exact Hf | split; assumption]).
      assert (D0 : 0 <= F / 8) by (apply Z.div_pos; clear - F0; lia). assert (D1 : F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; clear - F1; lia).
      set (SgO := fun a => M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).

      assert (TRA : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (CHA.curB LB G.BLS i E) (CHA.curF FF (sp - 16) WDC.FFS i E) (sp - 16 + CH2.ci_csp ci) 256 a ->
                   ~ (S F <= a < S F + 128) -> SGP.outside E' WDC.FX (Z_to_bv 64 a) -> SgO a).
      { intros a Ha Hc Hs Ho. unfold SgO. rewrite (HP1 a); [rewrite <- HcpF in Ho; exact (HFR _ Ho)|]. split; [exact Ha|]. split; [exact Hc|].
        intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. change (ff_bytes 4 / 8) with 128 in Hin. exact (Hs Hin). }
      assert (OO : PTA.out SgO o 24).
      { split; [exact O3|]. split; [clear - O6; lia|]. intros y Hy.
        destruct (OAP F fl FAP F2 F0 F1 HFL2 (y - o) ltac:(clear - Hy; lia)) as (X1 & X2 & X3 & X4 & X5). replace (o + (y - o)) with y in * by (clear; lia).
        apply TRA; [clear - Hy O3 O6; lia | | unfold S, SB; unfold WDC.SBz in X4; clear - X4; lia |].
        - destruct (CL5A.infr_wok L ar _ _ (sp - 16 + CH2.ci_csp ci) 256 o 24 y RF2 Ofr2 Hy) as (_ & G2 & _). exact (aclientw_client _ _ _ _ _ _ _ G2).
        - exact (WDC.outside_FX E' sp F y W2 W54 ltac:(clear - Hy O3 O6; lia) ltac:(clear - S2 S3 SP1 CL; lia) X1 X2 X3 X4). }
      destruct Hij as [(-> & ->)|(-> & ->)].
      +
        destruct (HXS (or_introl eq_refl)) as (s' & Hls & HSTR & HDO).
        unfold XI. split; [intros _ _; unfold FLF; rewrite T49; exact HXF|]. split; [|intros H9; exfalso; clear - H9; lia].
        intros _. exists s'. split; [exact Hls|].
        split; [|exact (DEFO _ _ _ _ _ _ _ (incl_tl _ (incl_refl FF)) ltac:(rewrite HcF in HH2; exact HH2))].
        destruct HSTR as (Hl22 & Hb0 & Hbs & Hnul). unfold PMLA.str_at, L5.lstr_short.
        split; [exact Hl22|]. split; [apply (PTA.u8_ag (hl_segs L) M1 M2 SgO (fun a Ha => Ha)); [apply (PTA.out_sub _ _ _ _ _ OO); clear; lia | exact Hb0]|].
        split; [apply (PTA.bytes_ag (hl_segs L) M1 M2 SgO (fun a Ha => Ha)); [apply (PTA.out_sub _ _ _ _ _ OO); clear - Hl22; lia | exact Hbs]|].
        apply (PTA.u8_ag (hl_segs L) M1 M2 SgO (fun a Ha => Ha)); [apply (PTA.out_sub _ _ _ _ _ OO); clear - Hl22; lia | exact Hnul].
      +
        destruct (HXL (or_introl eq_refl)) as (s' & Hls & HSTR & HDO & HAF). cbv zeta in HSTR, HAF.
        set (p := CL5A.uv E (EVar 66)) in *.
        assert (HcB : CHA.curB LB G.BLS 1 E = (p, 48) :: LB) by (unfold CHA.curB; change (nth 1 G.BLS []) with [(EVar 66, ELit 48)]; unfold CH2.den; cbn [map fst snd app]; reflexivity).
        pose proof HH2 as HH2'. rewrite HcB, HcF in HH2'.
        pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2') as WF2.
        destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF2 (p, 48) (or_introl eq_refl)) as (_ & _ & _ & _ & Bfap). cbn [fst snd] in Bfap.
        pose proof (Bfap (F, 4, sp - 16 + -96 + 32) (or_introl eq_refl)) as QF. cbn [ff_addr ff_class fst snd] in QF. change (ff_bytes 4) with 1024 in QF.
        destruct HAF as (HAR & HBA & HFA & HDF1 & HSB1). pose proof HAR as (P0 & _ & P16 & _ & P4 & (P5 & P6 & P7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in P6.
        assert (OP : PTA.out SgO p 48).
        { split; [clear - P5; lia|]. split; [clear - P7; lia|]. intros y Hy.
          apply TRA; [clear - Hy P5 P7; lia | left; rewrite HcB; exists (p, 48); split; [left; reflexivity | cbn [fst snd]; exact Hy] | unfold S, SB; clear - Hy P6 D0 D1; lia |].
          apply (WDC.outside_FX E' sp F y W2 W54); [clear - Hy P5 P7; lia | clear - S2 S3 SP1 CL; lia | left; clear - Hy P4 S2; lia | clear - Hy QF; lia | clear - Hy QF; lia |].
          unfold WDC.SBz. clear - Hy P6 D0 D1. lia. }
        assert (OPS : forall a, in_shadow_of p 48 a -> SgO a).
        { intros a Ha. pose proof (SHR p 48 a ltac:(clear - P5; lia) ltac:(clear; lia) P7 Ha) as SRa.
          assert (NSF : ~ (S F <= a < S F + 128)).
          { intros Hin. apply (CL5A.sh_apart2 p 48 F 1024 a P5 F0 ltac:(clear; lia) ltac:(clear; lia) (CHA.mod8_of_16 _ P16) F8 QF Ha).
            apply (CL5A.shreg_in_shadow F 128 a F8 ltac:(clear; lia)). unfold S in Hin. clear - Hin. lia. }
          apply TRA; [clear - SRa; lia | | exact NSF |].
          - do 6 right. rewrite HcB. exists (p, 48). split; [left; reflexivity | exact Ha].
          - apply (WDC.outside_FX E' sp F a W2 W54); [clear - SRa; lia | clear - S2 S3 SP1 CL; lia | left; clear - SRa S2 CL; lia | clear - SRa F2; lia | clear - SRa F2; lia |].
            unfold S, SB in NSF. unfold WDC.SBz. clear - NSF. lia. }
        assert (NXc1 : (66 < CC.cp_nx c)%nat) by (unfold G.CPS in Hci; cbn [nth_error] in Hci; injection Hci as <-; apply Nat.ltb_lt; vm_compute; reflexivity).
        assert (T66 : CL5A.uv E2 (EVar 66) = p).
        { unfold p, CL5A.uv. cbn [edenot]. rewrite <- (proj1 Hag2 66%nat) by (clear - NXci; lia). rewrite <- (proj1 Hag 66%nat) by (clear - NXc1; lia). reflexivity. }
        unfold XI. split; [intros _ _; unfold FLF; rewrite T49; exact HXF|]. split; [intros H9; exfalso; clear - H9; lia|].
        intros _. unfold LSTR. cbv zeta. rewrite T66. exists s'. split; [exact Hls|].
        split; [exact (PTA.str_long_ag (hl_segs L) M1 M2 SgO (fun a Ha => Ha) o 48 p s' OO OP HSTR)|].
        split; [exact (DEFO _ _ _ _ _ _ _ (incl_tl _ (incl_refl FF)) HH2')|].
        split; [exact HAR|]. split; [exact HBA|]. split; [exact HFA|].
        split; [exact (PTA.def_ag M1 M2 SgO (fun a Ha => Ha) p 48 OP HDF1)|].
        exact (PTA.shadow_blk_ag M1 M2 SgO (fun a Ha => Ha) p 48 ltac:(clear; lia) OPS (CHA.mod8_of_16 _ P16) HSB1).
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + q) RFx Ofr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 14336) 14336).
    { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    assert (VW : CL5A.visr (ahid A model) wd 12).
    { intros q Hq. apply CLV; [clear - Hq Hwd1 Hwd2 S2 SP1 CL; lia | right; left; split; [clear - Hq Hwd1 Hwd2 S2 SP1 CL; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq Hwd1 S2 CL. lia. }
    assert (VSH : shadow_zero (CCA.vis A model M) o 3).
    { intros j Hj. apply (CL5A.byte_vis _ M). 2: exact (Osh j Hj).
      pose proof (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }

    assert (WSH : forall k, 0 <= k < 12 -> L5.u8_at (hl_segs L) (CCA.vis A model M) (S (wd + k)) 0).
    { intros k Hk. apply CL5A.byte_at_u8. apply (CL5A.byte_vis _ M).
      - destruct (CRS_OK (CHA.SRL3 (EVar 10), 2147450880, ELit 1) ltac:(do 3 right; left; reflexivity)) as [_ CR1]. clear CR1.
        assert (D1 : (ahl_ceil ar) / 8 <= (wd + k) / 8) by (apply Z.div_le_mono; clear - Hk Hwd1 S2; lia).
        assert (D2 : (wd + k) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; clear - Hk Hwd2 SP1; lia).
        assert (D3 : (wd + k) / 8 < (ar_sptop ar) / 8).
        { apply Z.div_lt_upper_bound; [clear; lia|]. pose proof (Z.div_mod (ar_sptop ar) 16 ltac:(clear; lia)) as DD. rewrite SP16 in DD.
          replace (8 * (ar_sptop ar / 8)) with (ar_sptop ar) by (rewrite DD at 2; rewrite DD at 1; replace (16 * (ar_sptop ar / 16) + 0) with ((2 * (ar_sptop ar / 16)) * 8) by (clear; lia);
                                                                rewrite Z.div_mul by (clear; lia); clear; lia).
          clear - Hk Hwd2. lia. }
        change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
        apply CLV; unfold HeapIfaceA.S, SB.
        + pose proof (Z.div_pos (ahl_ceil ar) 8 ltac:(clear - CL; lia) ltac:(clear; lia)). clear - D1 D2 H; lia.
        + do 4 right; left. unfold in_shadow_of, HeapIfaceA.S, SB. split; [clear - D1; lia|]. replace (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) with (2 ^ 47 - 1) by (clear; lia).
          change ((2 ^ 47 - 1) / 8) with 17592186044415. clear - D2; lia.
        + intros _. unfold HeapIfaceA.S, SB. clear - D3. lia.
      - assert (SY : S (wd + k) = S (sp - 14336) + (S (wd + k) - S (sp - 14336))) by (clear; lia). rewrite SY. apply Hstksh.
        unfold HeapIfaceA.S, SB. split.
        + assert ((sp - 14336) / 8 <= (wd + k) / 8) by (apply Z.div_le_mono; clear - Hk Hwd1; lia). clear - H; lia.
        + assert (X1 : (wd + k) / 8 < (sp - 14336) / 8 + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 14336)) / 8).
          { rewrite <- Z.div_add_l by (clear; lia). apply Z.div_lt_upper_bound; [clear; lia|].
            pose proof (Z.div_mod (sp - 14336) 8 ltac:(clear; lia)) as DD. rewrite AL0 in DD.
            assert (8 * (((sp - 14336) / 8 * 8 + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 14336))) / 8) >= (sp - 14336) / 8 * 8 + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 14336)) - 7)
              by (pose proof (Z.div_mod ((sp - 14336) / 8 * 8 + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 14336))) 8 ltac:(clear; lia));
                  pose proof (Z.mod_pos_bound ((sp - 14336) / 8 * 8 + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 14336))) 8 ltac:(clear; lia)); clear - H H0; lia).
            pose proof (Z.div_mod (ar_sptop ar) 16 ltac:(clear; lia)) as DS16. rewrite SP16 in DS16.
            assert (Z.max (ar_sptop ar) (ar_stack_top ar) >= ar_sptop ar) by (clear; lia). clear - H H0 DD DS16 Hk Hwd2. lia. }
          clear - X1; lia. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact Hdefo).
    assert (DS : L5.defined Mv (sp - 14336) 14336) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    destruct Hstr as (Hl22 & Hb0 & Hbs & Hnul). cbn [length Z.of_nat] in Hb0, Hnul. rewrite Z.add_0_r in Hnul.
    assert (U8D : L5.u8_at (hl_segs L) M (wd + 8) dpb).
    { unfold L5.u8_at in *. rewrite Hu8. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold dpb. rewrite Zmod_mod. reflexivity. }
    assert (KW4 : forall E a A0, estart E a = A0 -> 0 <= A0 -> A0 + 4 <= 2 ^ 64 -> L5.u32_at (hl_segs L) Mv A0 0 -> kentry_ok (hl_segs L) E Mv (KWord a 4 (ELit 0))).
    { intros E a A0 Ha H0 H1 Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 4)) by (unfold flat; rewrite Ha; lia).
      split; [clear; lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha. cbn [edenot]. exact Hu. }
    split; [exact REGS0|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5A.kword8_intro with (A := o) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 1 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hb0].
    + eapply CL5A.kword8_intro with (A := o + 1) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 1) 1 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hnul].
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1 CL; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv (EVar 11) 3 o); [unfold CL5A.uv; cbn [edenot]; exact U11 | clear; lia | clear - O3 O6; lia | exact VSH].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5A.kword8_intro with (A := wd) (z := 0); [ev0 | clear - Hwd1 S2 CL; lia | clear - Hwd2 SP1; lia | reflexivity | clear; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - Hwd1 S2 CL; lia | clear - Hwd2 SP1; lia | exact (CL5A.visr_sub _ wd 12 wd 1 VW ltac:(clear; lia) ltac:(clear; lia)) | exact Hu0].
    + apply (KW4 E0 _ (wd + 4)); [ev0 | clear - Hwd1 S2 CL; lia | clear - Hwd2 SP1; lia |].
      apply (CL5A.u32_vis (hl_segs L)); [clear - Hwd1 S2 CL; lia | clear - Hwd2 SP1; lia | exact (CL5A.visr_sub _ wd 12 (wd + 4) 4 VW ltac:(clear; lia) ltac:(clear; lia)) | exact Hu4].
    + eapply CL5A.kword8_intro with (A := wd + 8) (z := dpb); [ev0 | clear - Hwd1 S2 CL; lia | clear - Hwd2 SP1; lia | cbn [edenot]; exact V32 | clear - DPR; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - Hwd1 S2 CL; lia | clear - Hwd2 SP1; lia | exact (CL5A.visr_sub _ wd 12 (wd + 8) 1 VW ltac:(clear; lia) ltac:(clear; lia)) | exact U8D].
    + eapply CL5.krange_intro with (v := dpb); [lin_eval; rw_atoms; clear; lia | clear - DPR; lia | clear - DPR; lia].
    + eapply CL5.krange_intro with (v := wd); [lin_eval; rw_atoms; clear; lia | clear - Hwd1 Hwd2 S2 SP1 CL; lia | clear - Hwd1 Hwd2 S2 SP1 CL; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := wd) (N2 := 12); [reflexivity | reflexivity | ev0 | reflexivity | clear - Hwd1 S2 CL; lia].
    + eapply CL5A.kword8_intro with (A := S wd) (z := 0); [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U10; reflexivity | unfold S, SB; clear - Hwd1 S2 CL; pose proof (Z.div_pos wd 8); lia
                                                         | unfold S, SB; assert (wd / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - Hwd2 SP1; lia); clear - H; lia | reflexivity | clear; lia |].
      replace (S wd) with (S (wd + 0)) by (rewrite Z.add_0_r; reflexivity). exact (WSH 0 ltac:(clear; lia)).
    + eapply CL5A.kword8_intro with (A := S (wd + 4)) (z := 0);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite u_add64, U10, (u64_of_Z 4) by (clear; lia); rewrite Z.mod_small by (clear - Hwd1 Hwd2 S2 SP1 CL; lia); reflexivity
        | unfold S, SB; clear - Hwd1 S2 CL; pose proof (Z.div_pos (wd + 4) 8); lia
        | unfold S, SB; assert ((wd + 4) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - Hwd2 SP1; lia); clear - H; lia | reflexivity | clear; lia |].
      exact (WSH 4 ltac:(clear; lia)).
    + eapply CL5A.kword8_intro with (A := S (wd + 8)) (z := 0);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite u_add64, U10, (u64_of_Z 8) by (clear; lia); rewrite Z.mod_small by (clear - Hwd1 Hwd2 S2 SP1 CL; lia); reflexivity
        | unfold S, SB; clear - Hwd1 S2 CL; pose proof (Z.div_pos (wd + 8) 8); lia
        | unfold S, SB; assert ((wd + 8) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - Hwd2 SP1; lia); clear - H; lia | reflexivity | clear; lia |].
      exact (WSH 8 ltac:(clear; lia)).
    + eapply CL5.kunk_intro with (A := sp - 14336) (N := 14320); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros q Hq; apply DS; clear - Hq; lia].
    + eapply CL5.kunk_intro with (A := sp - 16) (N := 16); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros q Hq; replace (sp - 16 + q) with (sp - 14336 + (14320 + q)) by (clear; lia); apply DS; clear - Hq; lia].
    + eapply CL5.kwr_intro with (A := sp - 14336) (N := 14320); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros q Hq; apply DS; clear - Hq; lia].
    + eapply CL5.kwr_intro with (A := sp - 16) (N := 16); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | intros q Hq; replace (sp - 16 + q) with (sp - 14336 + (14320 + q)) by (clear; lia); apply DS; clear - Hq; lia].
    + eapply CL5.krange_intro with (v := sp - 16); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp - 16); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact Hsp16].
    + eapply CL5.kdisj_intro with (A1 := sp - 14336) (N1 := 14336) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 14336) (N1 := 14336) (A2 := wd) (N2 := 12); [ev0 | reflexivity | ev0 | reflexivity | clear - Hwd1; lia].
    + eapply CL5.kdisj_intro with (A1 := wd) (N1 := 12) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - Hap; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite FFS0. cbn [CH2.den CHA.denF map app length G.BLS nth].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; reflexivity | rewrite Z.sub_0_r; exact Hroom].
    + split; [intros H0; exfalso; exact (H0 eq_refl)|]. split; [intros H; exfalso; clear - H; lia|]. intros H; exfalso; clear - H; lia.
  - exact Hfp.
Qed.
End WriteDoubleOk.
