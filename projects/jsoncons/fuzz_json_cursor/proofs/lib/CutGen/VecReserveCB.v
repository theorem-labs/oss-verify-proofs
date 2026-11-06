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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_vec_reserve_cboth_T Cut_vec_reserve_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_vec_reserve_cboth.
Module GT := Cut_vec_reserve_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module VRA.
Definition PC_OPNEW : Z := 1363704.
Definition PC_ADEL : Z := 727788.
Definition PC_MEMCPY : Z := 520756.
Definition PC_ANEW : Z := 810224.
Definition RETPC : Z := 829832.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10. Definition nbE := EVar 44.
Definition BLK : list (expr * expr) := [(nbE, ELit 66)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].
Definition WSH : list SGP.region := [(CHA.SRL3 nbE, SBz, CHA.SRL3 (APC.eaddz (EVar 11) 7))].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition news_of (ci_nx : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt (ci_nx + 4) X)) (CC.cp_know cj).
Definition oshz (cells : list kentry) : bool := has cells (KZero (SA (CHA.SRL3 oE) SBz) (ELit 3)).

Definition HAND : list kentry := [KDisj (SA (CHA.SRL3 nbE) SBz) (CHA.SRL3 (APC.eaddz (EVar 11) 7)) (SA (CHA.SRL3 (APC.eaddz (EVar 2) (-56))) SBz) (ELit 5)].
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              if Z.eqb pc PC_OPNEW then
                let nx := (CC.cp_nx cj - APC.NCS)%nat in let news := news_of nx cj in
                (Z.eqb (SR.ps_pc ps) PC_OPNEW && Nat.eqb i 0 && Nat.eqb j 1 && Nat.eqb nx 40 && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) BLK
                 && CHA.foot_chk GT.NF G.HDECL c [] []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 [] [] [] news None c ps cj [] [] BLK [])
                 && CRB.fresh_news_ok 65536 7028736 G.HDECL GT.SCELLS GT.GLO GT.GHI cells nx [] [] (nx + 4) (ELit 66) (List.filter (fun X => negb (has HAND X)) news)
                 && CL.ps_reg_is ps 10 (ELit 66))%bool
              else if Z.eqb pc PC_ADEL then
                (Z.eqb (SR.ps_pc ps) PC_ADEL && Nat.eqb i 1 && Nat.eqb j 2 && Nat.ltb 44 (CC.cp_nx c) && CH2.blocks_eqb (nth i G.BLS []) BLK && CH2.blocks_eqb (nth j G.BLS []) BLK
                 && CHA.foot_chk GT.NF G.HDECL c BLK []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4128 0 BLK [] [] STAT None c ps cj BLK [] BLK [])
                 && CL.ps_reg_is ps 10 oE && has cells (KWord (SA oE 0) 8 (ELit 0)) && has cells (KWord (SA oE 8) 8 (ELit 0)) && has cells (KWord (SA oE 16) 8 (ELit 0)) && oshz cells)%bool
              else if Z.eqb pc PC_MEMCPY then
                (Z.eqb (SR.ps_pc ps) PC_MEMCPY && Nat.eqb i 2 && Nat.eqb j 3 && Nat.ltb 44 (CC.cp_nx c) && CH2.blocks_eqb (nth i G.BLS []) BLK && CH2.blocks_eqb (nth j G.BLS []) BLK
                 && CHA.foot_chk GT.NF G.HDECL c BLK []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 BLK [] [] STAT (Some (EVar 44)) c ps cj BLK [] BLK [])
                 && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 (ELit 0) && CL.ps_reg_is ps 12 (ELit 0))%bool
              else if Z.eqb pc PC_ANEW then
                (Z.eqb (SR.ps_pc ps) PC_ANEW && Nat.eqb i 3 && Nat.eqb j 4 && Nat.ltb 44 (CC.cp_nx c) && CH2.blocks_eqb (nth i G.BLS []) BLK && CH2.blocks_eqb (nth j G.BLS []) BLK
                 && CHA.foot_chk GT.NF G.HDECL c BLK []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4128 0 BLK [] WSH STAT None c ps cj BLK [] BLK [])
                 && CL.ps_reg_is ps 10 oE && CL.ps_reg_is ps 11 (ELit 0) && has cells (KWord (SA oE 0) 8 nbE) && has cells (KWord (SA oE 16) 8 (EAlu Instr.ALU_ADD nbE (ELit 66))) && oshz cells)%bool
              else false
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c BLK [] && Nat.eqb i 4 && CH2.blocks_eqb (nth i G.BLS []) BLK
           && has cells (KWord (SA oE 0) 8 nbE) && has cells (KWord (SA oE 8) 8 nbE) && has cells (KWord (SA oE 16) 8 (EAlu Instr.ALU_ADD nbE (ELit 66)))
           && Nat.ltb 44 (CC.cp_nx c))%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End VRA.

Section VecReserveOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis OPNEW_OK : PMSA.opnew_specA L ar HI VRA.PC_OPNEW.
Hypothesis ADEL0_OK : PMSA.annotate_delete_null_spec L ar HI VRA.PC_ADEL.
Hypothesis ANEW_OK : PMSA.annotate_new_spec L ar HI VRA.PC_ANEW.

Lemma FFSnil : forall i, nth i VRA.FFS [] = [].
Proof. intros i. unfold VRA.FFS. do 6 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.

Theorem vec_reserve_ok : PMSA.vec_reserve_specA L ar HI 829676.
Proof.
  intros LB FF LK cr A o sp r. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hw0 & Hw8 & Hw16 & Hofr & Ho8 & Hosh & Hstksh & Hcred) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.u64, PMSA.VRES_SCR, PMSA.ainfr, PMSA.stksh in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYH : hl_img_lo L <= 65536 /\ 7028736 <= hl_img_hi L) by (rewrite ILO, IHI; lia).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Hofr ltac:(lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 66) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = 66) by (rewrite V11; apply u64_of_Z; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 8192) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFx Hofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }

  assert (SSH : forall a, in_shadow_of (sp - 56) 40 a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros a Ha. pose proof (SHR (sp - 56) 40 a ltac:(clear - S2 CL; lia) ltac:(clear; lia) ltac:(clear - S3 SP1; lia) Ha) as SRa. destruct Ha as [A1 A2].
    split; [clear - SRa; lia|]. split.
    - right; right; right; right; left. split; [|unfold S in *; clear - A2 S3 SP1 CL; lia]. apply (Z.le_trans _ (S (sp - 56))); [|exact A1]. unfold S. apply Z.add_le_mono_r. apply Z.div_le_mono; [lia|]. clear - S2. lia.
    - intros _. unfold S in *. apply Z.mod_divide in SP16; [|clear; lia]. destruct SP16 as [q Hq].
      assert (E1 : ar_sptop ar / 8 = 2 * q) by (rewrite Hq; replace (q * 16) with ((2 * q) * 8) by lia; apply Z.div_mul; lia).
      assert (E2 : (sp - 56 + 40 - 1) / 8 < 2 * q) by (apply Z.div_lt_upper_bound; [lia|]; clear - S3 Hq; lia). clear - A2 E1 E2. lia. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; unfold CHA.sclientA.
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow o 3 a Ho8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Hofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold elenZ in Ha.
      replace (CL5A.uv E0 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-56)))) with (sp - 56) in Ha by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia]).
      cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      assert (SP8 : (sp - 56) mod 8 = 0).
      { clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp / 16) - 56) with ((2 * (sp / 16) - 7) * 8) by lia. apply Z_mod_mult. }
      pose proof (CL5A.shreg_in_shadow (sp - 56) 5 a SP8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 5) with 40 in SH.
      destruct (SSH a SH) as (G1 & G2 & G3). split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => match i with 0%nat => cr1 = cr | _ => cr1 = adebit L cr 66 end).
  set (AFP := fun (nb : Z) => ablock_range L ar nb 66 /\ blocks_apart nb 66 LB /\ fframes_apart nb 66 FF /\ 17594333495296 <= nb).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) =>
               let nb := CL5A.uv E (EVar 44) in
               match i with 0%nat => True | 4%nat => AFP nb /\ L5.defined M1 nb 66 /\ shadow_cont M1 nb 66 0 | _ => AFP nb /\ L5.defined M1 nb 66 /\ shadow_blk M1 nb 66 end).
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ VRA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }
  assert (DEN : forall E, CH2.den E VRA.BLK = [(CL5A.uv E (EVar 44), 66)]) by (intros E; unfold CH2.den, VRA.BLK, VRA.nbE, CL5A.uv; cbn [map fst snd edenot]; rewrite u64_of_Z by (clear; lia); reflexivity).

  assert (NOFOOT : forall nb a, 17594333495296 <= nb -> nb + 66 <= 2 ^ 47 -> in_shadow_of nb 66 a -> ~ CHA.afoot_sem sp G.HDECL WW [(nb, 66)] [] a).
  { intros nb a NB1 NB2 Ha. pose proof (SHR nb 66 a ltac:(clear - NB1; lia) ltac:(clear; lia) NB2 Ha) as SRa. intros [X|[X|[X|[X|X]]]].
    - rewrite SCRV in X. clear - X SRa S2 CL. lia.
    - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin SRa O5. lia.
    - destruct X as (bb & [<-|[]] & Hin). cbn [fst snd] in Hin. clear - Hin SRa NB1. lia.
    - destruct X as (f & [] & _).
    - destruct X as (f & [] & _). }

  assert (KSHO : forall a, in_shadow_of o 24 a -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Hofr ltac:(clear; lia) Ha) as (G1 & G2 & _). pose proof (SHR o 24 a O3 ltac:(clear; lia) O6 Ha) as SRa.
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin SRa O5. lia. }
  rewrite <- LS in FPM.
  change 829676 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VRA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact VRA.heap_ok.
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
  -
    intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ VRA.leaf_ok _ _ _ _ _ IL) as X. unfold VRA.leaf_chk in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VRA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    +
      destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].

      destruct (Z.eqb_spec pc VRA.PC_OPNEW) as [->|Hne1].
      {
        cbv zeta in X. set (nx := (CC.cp_nx cj - APC.NCS)%nat) in *. set (news := VRA.news_of nx cj) in *.
        apply andb_prop in X as [X Y9]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
        apply andb_prop in X as [X YN]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2, YN. subst i j. apply CH2.blocks_eqb_eq in Y3, Y4.
        lazymatch type of Y5 with VRA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA _].
        assert (HcB : CHA.curB LB G.BLS 0 E = LB) by (unfold CHA.curB; rewrite Y3; reflexivity).
        assert (HcF : CHA.curF FF sp VRA.FFS 0 E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE VRA.PC_OPNEW 4112 0%nat [] [] news None 0 0%nat c ps 1%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        assert (NXeq : CH2.ci_nx ci = nx) by (destruct HV as (_ & _ & _ & _ & HV5); unfold nx; rewrite HV5; unfold APC.NCS; clear; lia).
        eexists. eexists. split; [exact (OPNEW_OK LB FF LK1 cr A1 66 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
        { unfold PMSA.a0. split; [|split; [clear; lia | exact Hcred]].
          replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
          rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y9). reflexivity. }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (u & Hu & Hfresh & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          pose proof Hfresh as (Hrng & Hbap & Hfap & Hdef & Hsh).
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (UR : 0 <= u < 2 ^ 64) by (destruct Hrng as (Q0 & _ & _ & Q3 & Q4 & _); clear - Q0 Q3 Q4 CL SP1; lia).
          assert (Hvu : CL5A.uv E2 (EVar 44) = u).
          { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2) as G0. cbn [length] in G0. rewrite Nat.add_0_r in G0.
            unfold E2. rewrite NXeq, YN in G0. rewrite NXeq, YN. change (40 + 4)%nat with 44%nat in G0. unfold PMSA.a0 in Hu. rewrite G0, Hu. apply u64_of_Z. exact UR. }
          assert (HagE2 : env_agree GT.NF E0 E2).
          { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
          pose proof Hfap as FA.
          split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
          assert (HBj : CHA.curB LB G.BLS 1 E2 = (u, 66) :: LB) by (unfold CHA.curB; rewrite Y4, (DEN E2), Hvu; reflexivity).
          split; [rewrite HBj; exact HH2|]. split; [reflexivity|]. split.
          { unfold XI. cbv zeta. rewrite Hvu. split; [|split; [exact Hdef | exact Hsh]]. split; [exact Hrng|]. split; [exact Hbap|]. split; [exact FA|].
            pose proof (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2 (u, 66) (or_introl eq_refl) ltac:(cbn [snd]; clear; lia)) as BHI. cbn [fst] in BHI. unfold BIGSHADOW_HI in BHI. exact BHI. }
          intros X0 HX0 _. destruct (VRA.has VRA.HAND X0) eqn:HH0.
          -
            apply CC.has_cell_In in HH0. unfold VRA.HAND, VRA.nbE, VRA.SBz, CHA.SRL3 in HH0. cbn [In] in HH0. destruct HH0 as [<-|[]].
            assert (SP8 : (sp - 56) mod 8 = 0).
            { clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp / 16) - 56) with ((2 * (sp / 16) - 7) * 8) by lia. apply Z_mod_mult. }
            pose proof (CL5A.gran_blk 66 ltac:(clear; lia)) as GB. pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & Q7).
            pose proof Hvu as T44. unfold CL5A.uv in T44. cbn [edenot] in T44.
            assert (T11 : bv_unsigned (ev E2 11) = 66) by (rewrite <- (proj1 HagE2 11%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact U11).
            assert (T2 : bv_unsigned (ev E2 2) = sp) by (rewrite <- (proj1 HagE2 2%nat ltac:(apply Nat.ltb_lt; reflexivity)); exact U2).
            eapply CL5.kdisj_intro with (A1 := u / 8 + SB) (N1 := (66 + 7) / 8) (A2 := (sp - 56) / 8 + SB) (N2 := 5);
              [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite T44; reflexivity
              | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear; lia]
              | rewrite CL5A.estart_srl3'; f_equal; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia] | reflexivity |].
            left. pose proof (CL5A.gran_le u ((66 + 7) / 8) (sp - 56) SP8 ltac:(clear - Q4 GB S2; lia)) as G1. clear - G1. lia.
          - refine (CRB.news_sound L ar C HI HIok LYI 65536 7028736 LYH GT.NF E0 LB FF sp G.HDECL WW STKF SCRP NF32 U2 WOK CRS_OK WRS_OK GT.SCELLS GT.GLO GT.GHI SCOK GOTOK
                      E' E2 (CH2.ci_nx ci) (SR.ps_cells ps) [] [] 44%nat (ELit 66) M' M2 A1 A2 m' m2 LB ((u, 66) :: LB) FF FF LK1 LK2 cr (adebit L cr 66) u 66 (List.filter (fun X => negb (VRA.has VRA.HAND X)) news)
                      HagE' Hag2 HK HH1 eq_refl eq_refl Hvu _ _ Hrng Hbap FA Hdef Hsh HH2 (or_introl eq_refl) _ X0 _).
            + reflexivity.
            + reflexivity.
            + rewrite NXeq. rewrite YN in Y8 |- *. exact Y8.
            + apply filter_In. split; [exact HX0 | rewrite HH0; reflexivity]. } }

      assert (PRO : forall i0 : nat, (1 <= i0 <= 3)%nat -> forall E A1 M1 m1, CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS VRA.FFS Cred 0 i0 E A1 M1 m1 ->
                nth i0 G.BLS [] = VRA.BLK -> XI i0 E A1 M1 m1 ->
                let nb := CL5A.uv E (EVar 44) in
                env_agree GT.NF E0 E /\ CHA.curB LB G.BLS i0 E = (nb, 66) :: LB /\ CHA.curF FF sp VRA.FFS i0 E = FF /\ AFP nb /\ L5.defined M1 nb 66 /\ shadow_blk M1 nb 66).
      { intros i0 Hi0 Ex Ax Mx mx HAx HBL HXx. cbv zeta.
        assert (HagE : env_agree GT.NF E0 Ex) by exact (proj1 (proj2 (proj2 (proj2 HAx)))).
        split; [exact HagE|]. split; [unfold CHA.curB; rewrite HBL, (DEN Ex); reflexivity|]. split; [unfold CHA.curF; rewrite FFSnil; reflexivity|].
        unfold XI in HXx. destruct i0 as [|[|[|[|i0]]]]; [exfalso; clear - Hi0; lia | exact HXx | exact HXx | exact HXx | exfalso; clear - Hi0; lia]. }
      destruct (Z.eqb_spec pc VRA.PC_ADEL) as [->|Hne2]; [|destruct (Z.eqb_spec pc VRA.PC_MEMCPY) as [->|Hne3]; [|destruct (Z.eqb_spec pc VRA.PC_ANEW) as [->|Hne4]; [|discriminate X]]].
      {
        apply andb_prop in X as [X Ysh]. apply andb_prop in X as [X Yc16]. apply andb_prop in X as [X Yc8]. apply andb_prop in X as [X Yc0]. apply andb_prop in X as [X Y7]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF].
        apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y44]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply CH2.blocks_eqb_eq in Y3, Y4. apply Nat.ltb_lt in Y44.
        lazymatch type of Y5 with VRA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        destruct (PRO 1%nat ltac:(clear; lia) E A1 M1 m1 HA Y3 HXi) as (HagE & HcB & HcF & HAFP & HDF & HSB). set (nb := CL5A.uv E (EVar 44)) in *.
        refine (CALLEE VRA.PC_ADEL 4128 0%nat VRA.BLK [] VRA.STAT None 0 1%nat c ps 2%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = adebit L cr 66) by exact HC1. subst cr1.
        assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (CELL : forall X0, VRA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS VRA.FFS Cred 0 1%nat E A1 M' m' HA') as Hoff.
        pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
        unfold VRA.oE in *.
        eexists. eexists. split; [exact (ADEL0_OK ((nb, 66) :: LB) FF LK1 (adebit L cr 66) A1 o (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
        { unfold PMSA.a0, PMSA.u64, PMSA.acobj. split; [replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y7); cbn [edenot]; rewrite (FZ 10%nat eq_refl); exact V10|].
          split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Yc0) ltac:(ev_start)) as G0; unfold CL5A.uv in G0; cbn [edenot] in G0; rewrite u64_of_Z in G0 by (clear; lia); exact G0|].
          split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yc8) ltac:(ev_start)) as G0; unfold CL5A.uv in G0; cbn [edenot] in G0; rewrite u64_of_Z in G0 by (clear; lia); exact G0|].
          split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc16) ltac:(ev_start)) as G0; unfold CL5A.uv in G0; cbn [edenot] in G0; rewrite u64_of_Z in G0 by (clear; lia); exact G0|].
          split; [left; exact Hofr|]. split; [exact Ho8|].
          pose proof (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 3 o (CELL _ Ysh) ltac:(unfold CL5A.uv; cbn [edenot]; exact W10) ltac:(clear; lia)) as SZ.
          intros jj Hj; exact (CL5A.byte_full _ _ _ _ (SZ jj Hj)). }
        { intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (-> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (HagE2 : env_agree GT.NF E0 E2).
          { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
          assert (NB' : CL5A.uv E' (EVar 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
          assert (NB2 : CL5A.uv E2 (EVar 44) = nb) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Y44; lia); exact NB').
          split; [rewrite (DEN E'), NB'; apply incl_refl|].
          split; [intros w a [] |]. split; [intros w a []|].
          split; [unfold CHA.curB; rewrite Y4, (DEN E2), NB2; exact HH2|]. split; [reflexivity|].
          split.
          { unfold XI. cbv zeta. rewrite NB2. pose proof HAFP as (Hrng & Hbap & Hfap & NBHI). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
            pose proof HP as (HP1 & HP2 & HP3).
            assert (KEEP : forall a, (nb <= a < nb + 66 \/ in_shadow_of nb 66 a) -> aclient L ar ((nb, 66) :: LB) FF (sp + CH2.ci_csp ci) 4128 a).
            { intros a [Ha|Ha]; [left; exists (nb, 66); split; [left; reflexivity | exact Ha] | do 6 right; exists (nb, 66); split; [left; reflexivity | exact Ha]]. }
            split; [exact HAFP|]. split.
            - intros k Hk. apply (HP3 (nb + k)); [clear - Hk Q0 Q7; lia | apply KEEP; left; clear - Hk; lia |]. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk).
            - destruct HSB as [Z0 P0]. assert (FRS : forall a, in_shadow_of nb 66 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
              { intros a Ha. pose proof (SHR nb 66 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa. assert (AR : 0 <= a < 2 ^ 64) by (clear - SRa; lia).
                assert (OUT0 : L5.outside (@nil L5.range) a) by (intros w []).
                rewrite (HP1 a (conj AR (conj (KEEP a (or_intror Ha)) OUT0))).
                refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VRA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                          1%nat c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
                rewrite FFSnil, Y3, (DEN E). exact (NOFOOT nb a NBHI Q7 Ha). }
              split; [intros jj Hj; unfold byte_at; rewrite FRS; [exact (Z0 jj Hj) | apply (CL5A.blk_shadow_in nb 66); [exact (CHA.mod8_of_16 _ Q16) | clear; lia | change ((66 + 7) / 8) with 9; clear - Hj; change (66 / 8) with 8 in Hj; unfold S; lia]]|].
              intros NZ. unfold byte_at. rewrite FRS; [exact (P0 NZ) | apply (CL5A.blk_shadow_in nb 66); [exact (CHA.mod8_of_16 _ Q16) | clear; lia | change ((66 + 7) / 8) with 9; change (66 / 8) with 8; unfold S; clear; lia]]. }
          intros X0 HX0 _. unfold VRA.STAT in HX0. cbn [In] in HX0.
          destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
      {
        apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF].
        apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y44]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply CH2.blocks_eqb_eq in Y3, Y4. apply Nat.ltb_lt in Y44.
        lazymatch type of Y5 with VRA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        destruct (PRO 2%nat ltac:(clear; lia) E A1 M1 m1 HA Y3 HXi) as (HagE & HcB & HcF & HAFP & HDF & HSB). set (nb := CL5A.uv E (EVar 44)) in *.
        pose proof HAFP as (Hrng & Hbap & Hfap & NBHI). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
        refine (CALLEE VRA.PC_MEMCPY 2560 0%nat VRA.BLK [] VRA.STAT (Some (EVar 44)) 0 2%nat c ps 3%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = adebit L cr 66) by exact HC1. subst cr1.
        assert (NB' : CL5A.uv E' (EVar 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        eexists. eexists. split.
        { unfold VRA.PC_MEMCPY. rewrite <- (L5A.aly_memcpy L C LAY). exact (CRC.asan_memcpy_cps L ar C HI HIok PMSA.fp_ok 2560 ((nb, 66) :: LB) FF LK1 (adebit L cr 66) A1 nb 0 0 [] (sp + CH2.ci_csp ci) (CC.cp_pc cj) ltac:(rewrite (L5A.aly_scr_mem L C LAY); clear; lia)). }
        split.
        { unfold CRC.memcpy_pre, CRC.mem_dst, CRC.mem_src.
          split; [exact (REG 10%nat _ nb Y10 NB')|]. split; [exact (REG 11%nat _ 0 Y11 ltac:(cbn [edenot]; apply u64_of_Z; clear; lia))|]. split; [exact (REG 12%nat _ 0 Y12 ltac:(cbn [edenot]; apply u64_of_Z; clear; lia))|].
          split.
          { split; [clear; lia|]. split; [intros a Ha; exfalso; clear - Ha; lia|]. split; [intros k Hk; exfalso; clear - Hk; lia|].
            split; [intros d k Hd Hk; destruct k; [reflexivity | exfalso; clear - Hd Hk; lia]|].
            unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. clear - Q0 NBHI Q4 CL SP1. lia. }
          split; [|right; clear - Q0; lia].
          split; [intros a Ha; exfalso; clear - Ha; lia|]. split; [clear; lia|]. split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; clear - S3 SP1; lia|].
          split; [intros k Hk; exfalso; clear - Hk; lia | reflexivity]. }
        { intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & _ & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta.
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (HagE2 : env_agree GT.NF E0 E2).
          { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
          assert (NB2 : CL5A.uv E2 (EVar 44) = nb) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Y44; lia); exact NB').
          split; [cbn [edenot]; unfold CL5A.uv in NB2; cbn [edenot] in NB2; rewrite Ha0', <- NB2; apply Z_to_bv_bv_unsigned|].
          split; [rewrite (DEN E'), NB'; apply incl_refl|].
          split; [intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exfalso; clear - Hin; lia|].
          split; [intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exfalso; clear - Hin; lia|].
          split; [unfold CHA.curB; rewrite Y4, (DEN E2), NB2; exact HH2|]. split; [reflexivity|].
          split.
          { unfold XI. cbv zeta. rewrite NB2. pose proof HP as (HP1 & HP2 & HP3).
            assert (KEEP : forall a, (nb <= a < nb + 66 \/ in_shadow_of nb 66 a) -> aclient L ar ((nb, 66) :: LB) FF (sp + CH2.ci_csp ci) 2560 a).
            { intros a [Ha|Ha]; [left; exists (nb, 66); split; [left; reflexivity | exact Ha] | do 6 right; exists (nb, 66); split; [left; reflexivity | exact Ha]]. }
            split; [exact HAFP|]. split.
            - intros k Hk. apply (HP3 (nb + k)); [clear - Hk Q0 Q7; lia | apply KEEP; left; clear - Hk; lia |]. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk).
            - destruct HSB as [Z0 P0]. assert (FRS : forall a, in_shadow_of nb 66 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
              { intros a Ha. pose proof (SHR nb 66 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa. assert (AR : 0 <= a < 2 ^ 64) by (clear - SRa; lia).
                assert (OUT0 : L5.outside [(nb, 0)] a) by (intros w [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; clear - Hin; lia).
                rewrite (HP1 a (conj AR (conj (KEEP a (or_intror Ha)) OUT0))).
                refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VRA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                          2%nat c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
                rewrite FFSnil, Y3, (DEN E). exact (NOFOOT nb a NBHI Q7 Ha). }
              split; [intros jj Hj; unfold byte_at; rewrite FRS; [exact (Z0 jj Hj) | apply (CL5A.blk_shadow_in nb 66); [exact (CHA.mod8_of_16 _ Q16) | clear; lia | change ((66 + 7) / 8) with 9; clear - Hj; change (66 / 8) with 8 in Hj; unfold S; lia]]|].
              intros NZ. unfold byte_at. rewrite FRS; [exact (P0 NZ) | apply (CL5A.blk_shadow_in nb 66); [exact (CHA.mod8_of_16 _ Q16) | clear; lia | change ((66 + 7) / 8) with 9; change (66 / 8) with 8; unfold S; clear; lia]]. }
          intros X0 HX0 _. unfold VRA.STAT in HX0. cbn [In] in HX0.
          destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
      {
        apply andb_prop in X as [X Ysh]. apply andb_prop in X as [X Yc16]. apply andb_prop in X as [X Yc0]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10].
        apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y44].
        apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply CH2.blocks_eqb_eq in Y3, Y4. apply Nat.ltb_lt in Y44.
        lazymatch type of Y5 with VRA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        destruct (PRO 3%nat ltac:(clear; lia) E A1 M1 m1 HA Y3 HXi) as (HagE & HcB & HcF & HAFP & HDF & HSB). set (nb := CL5A.uv E (EVar 44)) in *.
        pose proof HAFP as (Hrng & Hbap & Hfap & NBHI). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
        refine (CALLEE VRA.PC_ANEW 4128 0%nat VRA.BLK VRA.WSH VRA.STAT None 0 3%nat c ps 4%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = adebit L cr 66) by exact HC1. subst cr1.
        assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (W11 : bv_unsigned (ev E' 11) = 66) by (rewrite (FZ 11%nat eq_refl); exact U11).
        assert (NB' : CL5A.uv E' (EVar 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
        assert (W44 : bv_unsigned (ev E' 44) = nb) by exact NB'.
        assert (CELL : forall X0, VRA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS VRA.FFS Cred 0 3%nat E A1 M' m' HA') as Hoff.
        unfold VRA.oE, VRA.nbE in *.
        assert (FRS1 : forall a, in_shadow_of nb 66 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros a Ha. pose proof (SHR nb 66 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa.
          refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VRA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                    3%nat c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
          rewrite FFSnil, Y3, (DEN E). exact (NOFOOT nb a NBHI Q7 Ha). }
        eexists. eexists. split; [exact (ANEW_OK ((nb, 66) :: LB) FF LK1 (adebit L cr 66) A1 o nb 66 0 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
        { unfold PMSA.a0, PMSA.a1, PMSA.u64, PMSA.acobj.
          split; [replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y10); cbn [edenot]; rewrite (FZ 10%nat eq_refl); exact V10|].
          split; [replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 11 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y11); reflexivity|].
          split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Yc0) ltac:(ev_start)) as G0; unfold CL5A.uv in G0; cbn [edenot] in G0; rewrite W44 in G0; exact G0|].
          split; [apply (CL5A.u64_full (hl_segs L) _ Hoff); pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc16) ltac:(ev_start)) as G0;
                  replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EVar 44) (ELit 66))) with (nb + 66) in G0; [exact G0 | symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q7; lia]]|].
          split; [left; exact Hofr|]. split; [exact Ho8|].
          pose proof (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 3 o (CELL _ Ysh) ltac:(unfold CL5A.uv; cbn [edenot]; exact W10) ltac:(clear; lia)) as SZ.
          split; [intros jj Hj; exact (CL5A.byte_full _ _ _ _ (SZ jj Hj))|].
          split; [left; reflexivity|]. split; [clear; lia|]. split; [clear; lia|]. split; [|clear - NBHI; lia].
          apply PmHeapIfaceA.shadow_blk_cont. destruct HSB as [Z0 P0]. split.
          - intros jj Hj. unfold byte_at. rewrite FRS1; [exact (Z0 jj Hj) | apply (CL5A.blk_shadow_in nb 66); [exact (CHA.mod8_of_16 _ Q16) | clear; lia | change ((66 + 7) / 8) with 9; clear - Hj; change (66 / 8) with 8 in Hj; unfold S; lia]].
          - intros NZ. unfold byte_at. rewrite FRS1; [exact (P0 NZ) | apply (CL5A.blk_shadow_in nb 66); [exact (CHA.mod8_of_16 _ Q16) | clear; lia | change ((66 + 7) / 8) with 9; change (66 / 8) with 8; unfold S; clear; lia]]. }
        { intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Hsc2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (HagE2 : env_agree GT.NF E0 E2).
          { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
          assert (NB2 : CL5A.uv E2 (EVar 44) = nb) by (unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 44%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Y44; lia); exact NB').
          split; [rewrite (DEN E'), NB'; apply incl_refl|]. split.
          { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 (EVar 44), VRA.SBz, CHA.SRL3 (APC.eaddz (EVar 11) 7)). split; [left; reflexivity|].
            unfold CHA.in_reg. rewrite CL5A.estart_srl3. unfold elenZ. rewrite CHA.u_srl3. unfold CL5A.uv. cbn [edenot]. rewrite W44.
            replace (bv_unsigned (edenot E' (APC.eaddz (EVar 11) 7))) with (66 + 7) by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear; lia]).
            unfold S, SB, VRA.SBz in *. exact Hin. }
          split.
          { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
            refine (CHA.obj_not_client L ar LYI LB FF sp (CH.hd_scr G.HDECL) nb 66 a RFx (conj Q5 (conj Q6 Q7)) ltac:(clear; lia) (CHA.mod8_of_16 _ Q16) Q4 Q1 Hbap Hfap (or_intror _) Kc).
            exact (CL5A.blk_shadow_in nb 66 a (CHA.mod8_of_16 _ Q16) ltac:(clear; lia) Hin). }
          split; [unfold CHA.curB; rewrite Y4, (DEN E2), NB2; exact HH2|]. split; [reflexivity|].
          split.
          { unfold XI. cbv zeta. rewrite NB2. pose proof HP as (HP1 & HP2 & HP3). split; [exact HAFP|]. split; [|exact Hsc2].
            intros k Hk. apply (HP3 (nb + k)); [clear - Hk Q0 Q7; lia | left; exists (nb, 66); split; [left; reflexivity | cbn [fst snd]; clear - Hk; lia] |].
            apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk). }
          intros X0 HX0 _. unfold VRA.STAT in HX0. cbn [In] in HX0.
          destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
    +
      apply andb_prop in X as [X Y44]. apply andb_prop in X as [X Yc16]. apply andb_prop in X as [X Yc8]. apply andb_prop in X as [X Yc0]. apply andb_prop in X as [X Y3].
      apply andb_prop in X as [X Y2]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Y0 Xbase].
      apply Z.eqb_eq in Y0. subst pc. apply Nat.eqb_eq in Y2. subst i. apply CH2.blocks_eqb_eq in Y3. apply Nat.ltb_lt in Y44.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      set (nb := CL5A.uv E (EVar 44)) in *. unfold XI in HXi. cbv zeta in HXi. destruct HXi as ((Hrng & Hbap & Hfap & NBHI) & HDF & HSC).
      pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VRA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok VRA.RETPC 4%nat c ps _ Xbase _ (FFSnil 4%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
        [rewrite LS; exact VRA.ret_at | rewrite FFSnil, Y3; exact Xfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      assert (Hcr1 : cr1 = adebit L cr 66) by exact HC1. subst cr1.
      assert (HB : CHA.curB LB G.BLS 4 E = (nb, 66) :: LB) by (unfold CHA.curB; rewrite Y3, (DEN E); reflexivity). rewrite HB in HH1.
      assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
      assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
      assert (W44 : bv_unsigned (ev E' 44) = nb) by (unfold nb, CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 44%nat) by exact Y44; reflexivity).
      assert (CELL : forall X0, VRA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS VRA.FFS Cred 0 4%nat E A1 M' m' HA') as Hoff.
      unfold VRA.oE, VRA.nbE in *. rewrite SCRV in HP.
      apply (Hcont fx' R' M' model2 ((nb, 66) :: LB) (adebit L cr 66) LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      exists nb. split; [|split; [|repeat split; reflexivity]].
      { unfold PMSA.vec_at, PMSA.u64. split; [|split]; apply (CL5A.u64_full (hl_segs L) _ Hoff).
        - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Yc0) ltac:(ev_start)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W44 in G0. exact G0.
        - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yc8) ltac:(ev_start)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W44, <- (Z.add_0_r nb) in G0. exact G0.
        - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc16) ltac:(ev_start)) as G0.
          replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EVar 44) (ELit 66))) with (nb + 66) in G0; [exact G0 | symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q7; lia]]. }
      unfold PMSA.afresh_cont. split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split.
      { intros k Hk. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HDF k Hk). }
      apply (CL5A.shadow_cont_same M1 M' nb 66 0 ltac:(clear; lia) (CHA.mod8_of_16 _ Q16)); [|exact HSC]. intros a Ha.
      pose proof (SHR nb 66 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa.
      refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS VRA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                4%nat c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact Xfoot|].
      rewrite FFSnil, Y3, (DEN E). exact (NOFOOT nb a NBHI Q7 Ha).
  - reflexivity.
  -
    assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Hofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Hofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) Ho8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 8192) 8192).
    { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    assert (SP8 : (sp - 56) mod 8 = 0).
    { clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp / 16) - 56) with ((2 * (sp / 16) - 7) * 8) by lia. apply Z_mod_mult. }
    assert (VSS : forall j, 0 <= j < 5 -> ahid A model (Z_to_bv 64 (S (sp - 56) + j)) = false).
    { intros j Hj. pose proof (CL5A.shreg_in_shadow (sp - 56) 5 (S (sp - 56) + j) SP8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia)) as SH. change (8 * 5) with 40 in SH.
      destruct (SSH _ SH) as (G1 & G2 & G3). apply CLV; [exact G1 | | exact G3].
      eapply CHA.aclient_scr; [exact (aclientw_client _ _ _ _ _ _ _ G2) | intros x Hx; clear - Hx; lia]. }
    set (Mv := CCA.vis A model M).
    assert (DO : L5.defined Mv o 24).
    { apply (CL5A.defined_vis _ M o 24 VO). destruct Hofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF f Hf) as (_ & _ & _ & _ & Fdef & _).
      intros k Hk. replace (o + k) with (ff_addr f + (o - ff_addr f + k)) by (clear; lia). apply Fdef. clear - Hk F1 F2. lia. }
    assert (DS : L5.defined Mv (sp - 8192) 8192) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := o) (z := 0); [ev_start | clear - O3; lia | clear - O6; lia | reflexivity |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := 0); [ev_start | clear - O3; lia | clear - O6; lia | reflexivity |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 8) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := 0); [ev_start | clear - O3; lia | clear - O6; lia | reflexivity |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 16) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw16].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev_start | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact Ho8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Hosh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.krange_intro with (v := 66); [lin_eval; rw_atoms; clear; lia | clear; lia | clear; lia].
    + eapply CL5.kunk_intro with (A := sp - 8192) (N := 8192); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 8192) (N := 8192); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 5 (sp - 56)); [apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia] | clear; lia | clear - S2 S3 CL SP1; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSS j Hj)|].
      assert (AL : (sp - 8192) mod 8 = 0) by (clear - SP8; replace (sp - 8192) with (sp - 56 + (-1017) * 8) by lia; rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod, SP8 by lia; reflexivity).
      replace (S (sp - 56) + j) with (S (sp - 8192) + (1017 + j)) by (replace (sp - 56) with (sp - 8192 + 8136) by (clear; lia); rewrite (CL5A.S_add_al (sp - 8192) 8136 AL); change (8136 / 8) with 1017; clear; lia).
      apply Hstksh. split; [clear - Hj; lia|]. enough (GE : 1017 + j + 1 <= (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 8192)) / 8) by (clear - GE; lia). apply Z.div_le_lower_bound; [clear; lia|]. clear - Hj S3. lia.
    + eapply CL5.kdisj_intro with (A1 := sp - 8192) (N1 := 8192) (A2 := o) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := o / 8 + SB) (N1 := 3) (A2 := (sp - 56) / 8 + SB) (N2 := 5);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U10; reflexivity | reflexivity
        | rewrite CL5A.estart_srl3'; f_equal; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia] | reflexivity |].
      left. pose proof (CL5A.gran_le o 3 (sp - 56) SP8 ltac:(clear - O4 S2; lia)) as G1. clear - G1. lia.
  -
    split; [|exact I].
    split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr, LK. unfold CHA.curB, CHA.curF. cbn [nth G.BLS Cut_vec_reserve_cboth_T.BL0 CH2.den map app]. rewrite FFSnil. cbn [app CHA.denF map length].
    split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
  - exact Hfp.
Qed.

End VecReserveOk.
