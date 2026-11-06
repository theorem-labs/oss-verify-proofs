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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCA GetSpecCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_getlit_casan_T Cut_getlit_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_getlit_casan.
Module GT := Cut_getlit_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module GLC.
Definition PC_CSTR : Z := 857780.
Definition RETPC : Z := 838856.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10.

Definition chain (i : nat) : nat := (i mod 3)%nat.
Definition stage (i : nat) : nat := (i / 3)%nat.
Definition FLG (ch : nat) : Z := match ch with 0%nat => 4 | _ => 8 end.
Definition BV (ch : nat) : Z := match ch with 1%nat => 1 | _ => 0 end.
Definition BVC (ch : nat) : list kentry := match ch with 0%nat => [] | _ => [KWord (SA (EVar 11) 24) 1 (ELit (BV ch))] end.
Definition LIT (ch : nat) : Z := match ch with 0%nat => 155456 | 1%nat => 155392 | _ => 155424 end.
Definition TXT (ch : nat) : list Z := match ch with 0%nat => [110; 117; 108; 108] | 1%nat => [116; 114; 117; 101] | _ => [102; 97; 108; 115; 101] end.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1427896) 8 (ELit SBz)].
Definition FST : list SGP.region := [(EVar 2, -14384, ELit 14384)].
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
              (Nat.eqb (chain j) (chain i) && Nat.eqb (stage j) (Datatypes.S (stage i)) && Nat.ltb i 6 && Nat.ltb j 6 &&
               CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) [] && CHA.foot_chk GT.NF G.HDECL c [] [] && CBA.regions_eqb (CC.cp_F c) FST &&
              if Z.eqb pc PC_CSTR then
                (Z.eqb (SR.ps_pc ps) PC_CSTR && Nat.eqb (stage i) 0
                 && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4176 0 [] [] [(oE, 0, ELit 24)] STAT None c ps cj [] [] [] [] with
                    | Some ci => Z.eqb (CH2.ci_csp ci) (-48) | None => false end
                 && CL.ps_reg_is ps 10 oE && CL.ps_reg_is ps 11 (ELit (LIT (chain i))) && has cells (KZero (SA (CHA.SRL3 oE) SBz) (ELit 3)))%bool
              else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c [] [] && CH2.blocks_eqb (nth i G.BLS []) []
           && Nat.eqb (stage i) 1 && Nat.ltb i 6 && CBA.regions_eqb (CC.cp_F c) FST)%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Definition KNC : list kentry := firstn 29 (CC.cp_know G.cp0).
Lemma kn_entry : forall ch, (ch <= 2)%nat -> CC.cp_know (nth ch G.CPS G.cp0) = (KNC ++ [KWord (SA (EVar 11) 0) 8 (ELit (FLG ch))]) ++ BVC ch.
Proof. intros ch Hch. destruct ch as [|[|[|ch]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia]. Qed.
Lemma regs_entry : forall ch (R : bvmap 5 word), (ch <= 2)%nat ->
  regs_ok (Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])) (CC.cp_regs (nth ch G.CPS G.cp0)) R.
Proof.
  intros ch R Hch rr. unfold sr_get. destruct (bv_eqb rr 0) eqn:Hr0.
  - assert (rr = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; clear - Hr0; lia). subst rr. unfold getr. rewrite Hr0.
    destruct ch as [|[|[|ch]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hch; lia].
  - unfold reg_ev. rewrite <- (ridx_roundtrip rr) at 1. pose proof (ridx_range rr) as Hlt. set (nn := ridx rr) in *. clearbody nn.
    destruct ch as [|[|[|ch]]]; [| | | exfalso; clear - Hch; lia];
      [ let l := eval vm_compute in (CC.cp_regs (nth 0 G.CPS G.cp0)) in change (CC.cp_regs (nth 0 G.CPS G.cp0)) with l
      | let l := eval vm_compute in (CC.cp_regs (nth 1 G.CPS G.cp0)) in change (CC.cp_regs (nth 1 G.CPS G.cp0)) with l
      | let l := eval vm_compute in (CC.cp_regs (nth 2 G.CPS G.cp0)) in change (CC.cp_regs (nth 2 G.CPS G.cp0)) with l ];
      (do 32 (destruct nn as [|nn]; [cbn [nth edenot ev Nat.ltb Nat.leb Nat.sub]; reflexivity |]); exfalso; clear - Hlt; lia).
Qed.
End GLC.

Section GetLitOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Abbreviation IC := PMLA.C_casan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis CSTR_OK : PMCSA.cstr_ctor_specA L ar HI IC GLC.PC_CSTR.
Hypothesis RTG : rt_globals IL HI.
Hypothesis ILG : forall ch, (ch <= 2)%nat -> In (GLC.LIT ch, Z.of_nat (length (GLC.TXT ch)) + 1) (icl_globals IL).

Lemma FFSnil : forall i, nth i GLC.FFS [] = [].
Proof. intros i. unfold GLC.FFS. do 6 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma est0 : forall E k, 0 <= k -> estart E (SA (ELit 0) k) = k.
Proof. intros E k Hk. unfold estart. cbn [a_base a_off edenot]. rewrite u64_of_Z by lia. lia. Qed.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.

Lemma lstr_ag : forall (M1 M2 : mem) o s, 0 <= o -> o + 24 <= 2 ^ 64 -> (forall a, o <= a < o + 24 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  L5.lstr_short (hl_segs L) M1 o s -> L5.lstr_short (hl_segs L) M2 o s.
Proof.
  intros M1 M2 o s H0 H1 AG (X1 & X2 & X3 & X4).
  assert (OO : PTA.out (fun a => o <= a < o + 24) o 24) by (split; [lia|]; split; [lia|]; intros i Hi; exact Hi).
  split; [exact X1|]. split; [exact (PTA.u8_ag (hl_segs L) M1 M2 _ AG o _ (PTA.out_sub _ o 24 o 1 OO ltac:(lia) ltac:(lia)) X2)|].
  split; [exact (PTA.bytes_ag (hl_segs L) M1 M2 _ AG (o + 1) s (PTA.out_sub _ o 24 (o + 1) (Z.of_nat (length s)) OO ltac:(lia) ltac:(lia)) X3)|].
  exact (PTA.u8_ag (hl_segs L) M1 M2 _ AG (o + 1 + Z.of_nat (length s)) _ (PTA.out_sub _ o 24 (o + 1 + Z.of_nat (length s)) 1 OO ltac:(lia) ltac:(lia)) X4).
Qed.

Theorem get_lit_ok : GSP.get_string_on L ar HI IC GSP.is_lit 837940.

Proof.
  intros LB FF LK cr A o V E sp r e g He. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & Ha3 & HEV & _ & DV & HEC & HRO & HLS & HG0 & (Ofr & O8 & Osh) & DO & (Efr & E8 & Esh) & APOE & APOV & APVE & _ & (Vfr & V8 & Vsh) & Hstksh & SP32) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a3, PMLA.apart in *. assert (SCRG : PMCSA.GETSTR_SCR = 14384) by reflexivity. rewrite SCRG in *.

  assert (HCH : exists ch0, (ch0 <= 2)%nat /\ L5.u64_at (hl_segs L) M (V + 8) (GLC.FLG ch0) /\ (ch0 <> 0%nat -> L5.u8_at (hl_segs L) M (V + 32) (GLC.BV ch0)) /\ PMCSA.conv_ok e).
  { destruct e as [|[|]| | | | | | | | |]; try contradiction He; destruct HEV as (_ & HF).
    - exists 0%nat. split; [lia|]. split; [exact HF | split; [intros X; exfalso; exact (X eq_refl) | exact I]].
    - exists 1%nat. destruct HF as (HF1 & HF2). split; [lia|]. split; [exact HF1 | split; [intros _; exact HF2 | exact I]].
    - exists 2%nat. destruct HF as (HF1 & HF2). split; [lia|]. split; [exact HF1 | split; [intros _; exact HF2 | exact I]]. }
  destruct HCH as (ch0 & Hch0 & HFL & HBV & HCO).
  assert (DEV : L5.defined M (V + 8) 40) by exact (proj1 HEV).

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM. pose proof (L5A.aly_memset L C LAY) as PCAMS.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar _ FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.infr_rng L ar _ FF V 48 RFx Vfr ltac:(clear; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  destruct (CL5A.infr_rng L ar _ FF E 16 RFx Efr ltac:(clear; lia)) as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  change (hid (V + 48 <= 2147446784 \/ 17594333495296 <= V)) in Q5. change (hid (V + 48 <= hl_img_lo L \/ hl_img_hi L <= V)) in Q7.
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in W5. change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in W7.
  change (hid (o + 24 <= E \/ E + 16 <= o)) in APOE. change (hid (o + 24 <= V \/ V + 48 <= o)) in APOV. change (hid (V + 48 <= E \/ E + 16 <= V)) in APVE.
  assert (SHR : forall p k a, 0 <= p -> 0 < k -> p + k <= 2 ^ 47 -> in_shadow_of p k a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 (V + 8)) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V13 : ev E0 13 = Z_to_bv 64 E) by (rewrite <- Ha3; exact (EV 13%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = V + 8) by (rewrite V11; apply u64_of_Z; clear - Q3 Q6; lia).
  assert (U13 : bv_unsigned (ev E0 13) = E) by (rewrite V13; apply u64_of_Z; clear - W3 W6; lia).
  assert (GRN : forall k, 0 <= k < 24 -> (o + k) / 8 = o / 8 + k / 8).
  { intros k Hk. clear - O8 Hk. apply Z.mod_divide in O8; [|lia]. destruct O8 as [q ->]. rewrite Z.div_mul by lia. rewrite Z.div_add_l by lia. lia. }

  assert (SCRV : CH.hd_scr G.HDECL = 14384) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(o, 24); (E, 16); (PMLA.CONVCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES); (hl_tp L - 164, 4)] : list L5.range).
  set (Wo := [(o, 24); (E, 16)] : list L5.range).
  assert (RFr : CHA.rng_facts L ar LB FF) by exact RFx.
  assert (WINC : incl Wo WW) by (intros w [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity]).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin;
      [exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFr Ofr Hin) | exact (CL5A.infr_wok L ar LB FF sp _ E 16 a RFr Efr Hin)]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_wrs G.HDECL) in change (CH.hd_wrs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia].
    - rewrite U13 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (E, 16). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { assert (GOBJ : forall p n (Hf : CL5A.ainfr FF p n) a, 0 < n -> p <= a < p + n -> CHA.sclientA L ar LB FF sp G.HDECL a).
    { intros p n Hf a Hn Ha. destruct (CL5A.infr_wok L ar LB FF sp (CH.hd_scr G.HDECL) p n a RFr Hf Ha) as (G1 & G2 & G3). split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
    assert (GSH : forall p n (Hf : CL5A.ainfr FF p n) a, 0 < n -> p mod 8 = 0 -> p / 8 + 2147450880 <= a < p / 8 + 2147450880 + n / 8 -> CHA.sclientA L ar LB FF sp G.HDECL a).
    { intros p n Hf a Hn Hp8 Ha. pose proof (CL5A.shreg_in_shadow p (n / 8) a Hp8 ltac:(clear - Ha; lia) ltac:(unfold SB; clear - Ha; lia)) as SH.
      destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) p n a RFr Hf Hn (CL5A.in_shadow_mono p (8 * (n / 8)) p n a ltac:(clear; lia) ltac:(pose proof (Z.mul_div_le n 8 ltac:(clear; lia)); clear - H; lia) ltac:(clear - Ha; lia) SH)) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
    intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[]]]]].
    - split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      exact (GOBJ V 48 Vfr a ltac:(clear; lia) ltac:(clear - Ha; lia)).
    - split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      exact (GSH o 24 Ofr a ltac:(clear; lia) O8 Ha).
    - split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      assert (SV : (V + 8) / 8 = V / 8 + 1) by (clear - V8; apply Z.mod_divide in V8; [|lia]; destruct V8 as [q ->]; rewrite Z.div_mul by lia; replace (q * 8 + 8) with ((q + 1) * 8) by lia; rewrite Z.div_mul by lia; lia).
      rewrite SV in Ha. exact (GSH V 48 Vfr a ltac:(clear; lia) V8 ltac:(clear - Ha; lia)).
    - split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U13 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      exact (GSH E 16 Efr a ltac:(clear; lia) E8 Ha). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (i : nat) (_ : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) =>
     GLC.chain i = ch0 /\ PMLA.img_ro IC M1 /\ PMLA.ec_at (hl_segs L) IC M1 E 0 /\ PMLA.ls_ok (hl_segs L) IC g M1 /\
     (GLC.stage i = 0%nat -> L5.defined M1 o 24 /\ PMSA.stksh ar M1 sp 14384) /\
     (GLC.stage i <> 0%nat -> PMLA.str_at_w (hl_segs L) M1 o (PML.SShort (GLC.TXT ch0)))).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ GLC.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }
  assert (ST0 : GLC.stage ch0 = 0%nat /\ GLC.chain ch0 = ch0 /\ nth ch0 G.BLS [] = [] /\ nth_error G.CPS ch0 = Some (nth ch0 G.CPS G.cp0) /\ CC.cp_pc (nth ch0 G.CPS G.cp0) = 837940).
  { destruct ch0 as [|[|[|ch0]]]; [repeat split; reflexivity | repeat split; reflexivity | repeat split; reflexivity | exfalso; clear - Hch0; lia]. }
  destruct ST0 as (ST0 & CHN0 & BLS0 & CP0 & PC0).
  rewrite <- LS in FPM. rewrite <- PC0.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS GLC.FFS Cred 6 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := ch0) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact GLC.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    assert (UVE : forall E1 e1 z, env_agree GT.NF E0 E1 -> APC.expr_vars_lt GT.NF e1 = true -> CL5A.uv E0 e1 = z -> CL5A.uv E1 e1 = z).
    { intros E1 e1 z Hag Hv Hz. rewrite (CL5A.uv_agree GT.NF E0 E1 e1 Hag Hv). exact Hz. }
    assert (ULIT : forall E1 z, 0 <= z < 2 ^ 64 -> CL5A.uv E1 (ELit z) = z) by (intros E1 z Hz; unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; exact Hz).

    assert (FOOTRG : forall a, PMLA.in_foot IC a \/ PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> 65536 <= a < 7015876).
    { intros a [Ha|Ha]; [|cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_casan] in Ha; clear - Ha; lia].
      pose proof Ha as (iv & Hiv & Hr). cbn [PMLA.FOOT PMLA.C_casan] in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hiv. }
    assert (STF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
               \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
               \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a).
    { intros a Ha. cbn [PMLA.GLOC_GUARD PMLA.GLOC_PTR PMLA.SYSCAT_GUARD PMLA.ERRCAT_GUARD PMLA.ATEXIT_TAB PMLA.NEED_LOCKS PMLA.LOCALE_LOCK PMLA.CONVCAT_GUARD PMLA.C_casan] in Ha.
      unfold PMLA.in_foot. cbn [PMLA.FOOT PMLA.C_casan].
      destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]].
      - exists (6877840, 6878344). split; [right; right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (6877840, 6878344). split; [right; right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (6877824, 6877826). split; [right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (6877256, 6877258). split; [left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (7015072, 7015616). split; [do 5 right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (7015651, 7015652). split; [do 6 right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (7015872, 7015876). split; [do 7 right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (6877248, 6877250). split; [do 8 right; left; reflexivity | cbn [fst snd]; clear - Ha; lia]. }

    set (KS := fun a : Z => (o <= a < o + 24) \/ (E <= a < E + 16) \/ PMLA.in_foot IC a \/ PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).
    assert (KSR : forall a, KS a -> 0 <= a < 2 ^ 64 /\ ~ (sp - 14384 <= a < sp)).
    { intros a [Ha|[Ha|Ha]]; [clear - Ha O3 O6 O4 S2; lia | clear - Ha W3 W6 W4 S2; lia | pose proof (FOOTRG a Ha); clear - H S2 CL; lia]. }
    assert (KSC : forall LBx spx scrx a, incl LB LBx -> KS a -> aclient L ar LBx FF spx scrx a).
    { intros LBx spx scrx a HiB [Ha|[Ha|Ha]].
      - right; right; right; left. destruct Ofr as (f & Hf & F1 & F2). exists f. split; [exact Hf | clear - Ha F1 F2; lia].
      - right; right; right; left. destruct Efr as (f & Hf & F1 & F2). exists f. split; [exact Hf | clear - Ha F1 F2; lia].
      - right; right; left. pose proof (FOOTRG a Ha) as RG. rewrite ILO, IHI. split; [clear - RG; lia|].
        destruct Ha as [Ha|Ha]; [exact (proj1 (FOOTC2 a Ha)) | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_casan] in Ha; clear - Ha H; lia]. }

    assert (LFR : forall c ps0 E1 R' A1 M1 m1 M' m', CBA.regions_eqb (CC.cp_F c) GLC.FST = true -> env_agree GT.NF E0 E1 ->
              CCA.leaf_factsA (hl_segs L) c ps0 E1 R' A1 M1 m1 M' m' -> forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 14384 <= a < sp) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros c ps0 E1 R' A1 M1 m1 M' m' HF Hag1 HLF a Ha Hn. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF (Z_to_bv 64 a)).
      apply CBA.regions_eqb_eq in HF. rewrite HF. unfold GLC.FST, SGP.outside. rewrite u64_of_Z by exact Ha. constructor; [|constructor].
      rewrite (CL5.estart_lin E1 (EVar 2) (-14384) sp ltac:(lin_eval; rewrite <- (proj1 Hag1 2%nat) by (apply Nat.ltb_lt; reflexivity); rewrite U2; clear; lia) ltac:(clear - S2 S3 CL SP1; lia)).
      unfold elenZ. cbn [edenot]. rewrite u64_of_Z by (clear; lia). clear - Hn. lia. }

    set (KS2 := fun a : Z => (E <= a < E + 16) \/ PMLA.in_foot IC a \/ PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).
    assert (KS2_KS : forall a, KS2 a -> KS a) by (intros a Ha; right; exact Ha).
    assert (TR : forall (M1 M2 : mem), (forall a, KS2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
              (PMLA.img_ro IC M1 -> PMLA.img_ro IC M2) /\
              (forall code, PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M2 E code) /\
              (PMCSA.ec_conv_atA L IC M1 E 11 -> PMCSA.ec_conv_atA L IC M2 E 11) /\
              (forall gg, gg <> PML.LS0 -> PMLA.ls_ok (hl_segs L) IC gg M1 -> PMLA.ls_ok (hl_segs L) IC gg M2)).
    { intros M1 M2 AG.
      assert (OE : PTA.out KS2 E 16) by (split; [clear - W3; lia|]; split; [clear - W6; lia|]; intros ii Hii; left; exact Hii).
      split; [exact (PTA.clear_ag M1 M2 KS2 AG _ _ (fun ii Hii => or_intror (or_intror Hii)))|].
      split; [intros code H; exact (PTA.ec_at_ag (hl_segs L) IC M1 M2 KS2 AG E code OE H)|].
      split.
      { intros (X1 & X2 & X3). unfold PMLA.u32, PMLA.u64 in *. split; [exact (PTA.u32_ag (hl_segs L) M1 M2 KS2 AG E 11 (PTA.out_sub KS2 E 16 E 4 OE ltac:(clear; lia) ltac:(clear; lia)) X1)|].
        split; [exact (PTA.def_ag M1 M2 KS2 AG E 16 OE X2)|]. exact (PTA.u64_ag (hl_segs L) M1 M2 KS2 AG (E + 8) _ (PTA.out_sub KS2 E 16 (E + 8) 8 OE ltac:(clear; lia) ltac:(clear; lia)) X3). }
      intros gg Hgg H. refine (PTA.ls_ok_ag (hl_segs L) IC M1 M2 KS2 AG gg Hgg _ STF H).
      intros a Ha. pose proof (FOOTRG a ltac:(destruct Ha as [Ha|Ha]; [right; exact Ha | left; exact Ha])) as RG. split; [clear - RG; lia|]. right. destruct Ha as [Ha|Ha]; [right; exact Ha | left; exact Ha]. }
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS GLC.FFS Cred 6 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    assert (STNEWS : forall E2 A2 m2 M2 LB2 LK2 cr2, ri_inv HI LB2 FF LK2 cr2 A2 M2 (vml_of m2) -> forall X0, In X0 GLC.STAT -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0).
    { intros E2 A2 m2 M2 LB2 LK2 cr2 HH2 X0 HX0. unfold GLC.STAT in HX0. cbn [In] in HX0.
      destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). }

    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ GLC.leaf_ok _ _ _ _ _ HIL) as X. unfold GLC.leaf_chk in X.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X0 XIF]. apply andb_prop in X0 as [X0 YFS]. apply andb_prop in X0 as [X0 YF]. apply andb_prop in X0 as [X0 YBj]. apply andb_prop in X0 as [X0 YBi].
      apply andb_prop in X0 as [X0 Yj6]. apply andb_prop in X0 as [X0 Yi6]. apply andb_prop in X0 as [YCH YST].
      apply Nat.eqb_eq in YCH, YST. apply CH2.blocks_eqb_eq in YBi, YBj.
      assert (HcF : forall E1, CHA.curF FF sp GLC.FFS i E1 = FF) by (intros E1; unfold CHA.curF; rewrite FFSnil; reflexivity).
      assert (HcB : forall E1, CHA.curB LB G.BLS i E1 = LB) by (intros E1; unfold CHA.curB; rewrite YBi; reflexivity).
      assert (HcBj : forall E1, CHA.curB LB G.BLS j E1 = LB) by (intros E1; unfold CHA.curB; rewrite YBj; reflexivity).
      destruct (Z.eqb_spec pc GLC.PC_CSTR) as [->|Hne1]; [|cbn iota in XIF; discriminate XIF].

      apply andb_prop in XIF as [XIF Ysh]. apply andb_prop in XIF as [XIF Y11]. apply andb_prop in XIF as [XIF Y10].
      apply andb_prop in XIF as [XIF Ychk]. apply andb_prop in XIF as [Y0 Ys0]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Ys0.
      destruct (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4176 0 [] [] [(GLC.oE, 0, ELit 24)] GLC.STAT None c ps0 cj [] [] [] []) as [ci|] eqn:Hchk; [|discriminate].
      apply Z.eqb_eq in Ychk.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
      unfold XI in HXi. destruct HXi as (XC & XR & XEC & XLS & XS0 & _). destruct (XS0 Ys0) as (XD & XSK).
      refine (CALLEE GLC.PC_CSTR 4176 0%nat [] [(GLC.oE, 0, ELit 24)] GLC.STAT None 0 i c ps0 j cj ci Hcj _ Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LKc CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1. rewrite Ychk in *.
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (CELL : forall X0, GLC.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
      assert (REG : forall (q : nat) (e1 : expr) (z : Z), CL.ps_reg_is ps0 q e1 = true -> CL5A.uv E' e1 = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
      { intros q e1 z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (AGL : forall a, KS a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha; exact (LFR c ps0 E' R' A1 M1 m1 M' m' YFS HagE' HLF a (proj1 (KSR a Ha)) (proj2 (KSR a Ha)))).
      destruct (TR M1 M' (fun a Ha => AGL a (KS2_KS a Ha))) as (TRO & TEC & _ & TLS).
      assert (XD' : L5.defined M' o 24) by (intros ii Hii; rewrite (AGL (o + ii) ltac:(left; clear - Hii; lia)); exact (XD ii Hii)).
      assert (XSK' : PMLA.stksh ar M' (sp + -48) 4176).
      { assert (XSK2 : PMLA.stksh ar M1 (sp + -48) 4176) by (apply (PTA.stksh_mono ar M1 sp 14384); [exact XSK | clear - SP32; lia | clear - SP32; lia | clear; lia]).
        apply (PTA.stksh_ag ar M1 M' (sp + -48) 4176); [|exact XSK2].
        intros a Ha. destruct (PTA.stksh_rng ar (sp + -48) 4176 a ltac:(clear - S2; lia) ltac:(clear - SP32; lia) C8 (proj2 SP1) ltac:(pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as STT; clear - STT; lia) ltac:(clear - CL; lia) Ha) as (R1a & R2a).
        apply (LFR c ps0 E' R' A1 M1 m1 M' m' YFS HagE' HLF a R1a). unfold in_shadow_of in R2a. clear - R2a S2 S3 SP1 CL. unfold S, SB in *. lia. }
      assert (W10 : CL5A.uv E' GLC.oE = o) by exact (UVE E' (EVar 10) o HagE' eq_refl U10).
      assert (SZ' : shadow_zero M' o 3).
      { intros jj Hj. apply (CL5A.byte_full (ahid A1 m') M'). exact (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 3 o (CELL _ Ysh) W10 ltac:(clear; lia) jj Hj). }
      assert (SRC : shadow_blk M' (GLC.LIT ch0) (Z.of_nat (length (GLC.TXT ch0)) + 1)).
      { pose proof (RTG _ _ _ _ _ _ _ HH1) as GL. rewrite Forall_forall in GL. destruct (GL _ (ILG ch0 Hch0)) as (SB & _). exact SB. }
      rewrite XC in Y11.
      eexists. eexists. split; [exact (CSTR_OK LB FF LKc cr A1 o (GLC.LIT ch0) (sp + -48) (CC.cp_pc cj) (GLC.TXT ch0))|]. split.
      { unfold PMSA.a0, PMSA.a1. split; [exact (REG 10%nat _ o Y10 W10)|]. split; [exact (REG 11%nat _ (GLC.LIT ch0) Y11 (ULIT E' (GLC.LIT ch0) ltac:(clear - Hch0; destruct ch0 as [|[|[|]]]; cbn; lia)))|].
        split; [destruct ch0 as [|[|[|ch0]]]; [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | exfalso; clear - Hch0; lia]|].
        split; [exact (TRO XR)|]. split; [exact SRC|]. split; [exact (conj Ofr (conj O8 SZ'))|]. split; [exact XD' | exact XSK']. }
      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (-> & -> & Hstr & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      exists []. split; [reflexivity|]. cbv zeta. set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
      split; [exact I|]. split; [cbn [CH2.den map app]; apply incl_refl|].
      assert (WIN : forall w a, In w [(o, 24)] -> L5.in_rng w a -> o <= a < o + 24) by (intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin).
      split.
      { intros w a Hw Hin. pose proof (WIN w a Hw Hin) as Ha. exists (GLC.oE, 0, ELit 24). split; [left; reflexivity|].
        unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. unfold CL5A.uv in W10. unfold GLC.oE in *. rewrite W10, u64_of_Z by (clear; lia). clear - Ha. lia. }
      split.
      { intros w a Hw Hin (Ka & Kc & Kw). apply (Kw (o, 24)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. exact (WIN w a Hw Hin). }
      split; [rewrite HcBj; exact HH2|]. split; [unfold Cred; reflexivity|].
      assert (KEI : forall a, KS2 a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { intros a KSa. pose proof HP as (HP1 & _ & _). apply HP1. split; [exact (proj1 (KSR a (KS2_KS a KSa)))|]. split; [exact (KSC LB _ _ a (incl_refl _) (KS2_KS a KSa))|].
        intros w Hw Hin. pose proof (WIN w a Hw Hin) as Hoa. destruct KSa as [Ha|Ha]; [unfold hid in APOE; clear - Ha Hoa APOE; lia|].
        pose proof (FOOTRG a ltac:(destruct Ha as [Ha|Ha]; [left; exact Ha | right; exact Ha])) as RG. clear - RG Hoa O1 FSLO. lia. }
      destruct (TR M' M2 KEI) as (TRO2 & TEC2 & _ & TLS2).
      split.
      { unfold XI. split; [rewrite YCH; exact XC|]. split; [exact (TRO2 (TRO XR))|]. split; [exact (TEC2 0 (TEC 0 XEC))|].
        split; [exact (TLS2 g HG0 (TLS g HG0 XLS))|]. split; [intros Hs; exfalso; rewrite YST, Ys0 in Hs; discriminate Hs|]. intros _. exact Hstr. }
      intros X0 HX0 _. exact (STNEWS E2 A2 m2 M2 _ _ _ HH2 X0 HX0).
    +
      apply andb_prop in X as [X YFX]. apply andb_prop in X as [X Yi6]. apply andb_prop in X as [X Ys1]. apply andb_prop in X as [X YB].
      apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Y0 Xbase].
      apply Z.eqb_eq in Y0. subst pc. apply CH2.blocks_eqb_eq in YB. apply Nat.eqb_eq in Ys1.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      unfold XI in HXi. destruct HXi as (XC & XR & XEC & XLS & _ & XS1). specialize (XS1 ltac:(rewrite Ys1; discriminate)).
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS GLC.FFS Cred 6 STKF SCRP NF32 U2 WINC WOK WRS_OK
                K DEF0 R r EV Hra Hraok GLC.RETPC i c ps0 _ Xbase _ (FFSnil i) fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact GLC.ret_at | rewrite FFSnil, YB; exact Xfoot |].
      intros model2 cr1 LK1' HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (HB : CHA.curB LB G.BLS i E1 = LB) by (unfold CHA.curB; rewrite YB; reflexivity). rewrite HB in HH1.
      rewrite SCRV in HP.
      assert (AGL : forall a, KS a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha; exact (LFR c ps0 E' R' A1 M1 m1 M' m' YFX HagE' HLF a (proj1 (KSR a Ha)) (proj2 (KSR a Ha)))).
      destruct (TR M1 M' (fun a Ha => AGL a (KS2_KS a Ha))) as (_ & TEC & _ & TLS).
      assert (XS1' : PMLA.str_at_w (hl_segs L) M' o (PML.SShort (GLC.TXT ch0))).
      { cbn [PMLA.str_at_w] in XS1 |- *. apply (lstr_ag M1 M' o _ ltac:(clear - O3; lia) ltac:(clear - O6; lia)); [|exact XS1]. intros a Ha. exact (AGL a (or_introl Ha)). }
      apply (Hcont fx' R' M' model2 LB cr LB WW LK1' A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      pose proof (TEC 0 XEC) as XEC'. pose proof XEC' as (XU & XDF & _).
      exists 0, g. split.
      { exists (PML.SShort (GLC.TXT ch0)). split; [exact XS1'|]. cbn [PMLA.srep_sh PML.srep_blocks app]. split; [exact I|]. split; [reflexivity|]. split; [intros _; reflexivity | intros b []]. }
      split; [reflexivity|]. split; [exact XU|]. split; [exact XDF|]. split; [exact (TLS g HG0 XLS)|].
      split; [left; split; [exact HCO | split; [reflexivity | split; [reflexivity | exact XEC']]]|]. reflexivity.

  - exact CP0.
  -
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VOBJ : forall p n, CL5A.ainfr FF p n -> CL5A.visr (ahid A model) p n).
    { intros p n Hf k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 p n (p + k) RFx Hf ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSH : forall p n j, CL5A.ainfr FF p n -> p mod 8 = 0 -> 0 <= j < n / 8 -> 0 < n -> ahid A model (Z_to_bv 64 (S p + j)) = false).
    { intros p n j Hf Hp8 Hj Hn. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 p n (S p + j) RFx Hf Hn
                (CL5A.in_shadow_mono p (8 * (n / 8)) p n (S p + j) ltac:(clear; lia) ltac:(pose proof (Z.mul_div_le n 8 ltac:(clear; lia)); clear - H; lia) ltac:(clear - Hj; lia)
                   (CL5A.shreg_in_shadow p (n / 8) (S p + j) Hp8 ltac:(clear - Hj; lia) ltac:(unfold S; clear - Hj; lia)))) as (G1 & G2 & G3).
      exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 14384) 14384).
    { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DOv : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 (VOBJ o 24 Ofr)); exact DO).
    assert (DEv : L5.defined Mv (V + 8) 40) by (apply (CL5A.defined_vis _ M (V + 8) 40 (CL5A.visr_sub _ V 48 (V + 8) 40 (VOBJ V 48 Vfr) ltac:(clear; lia) ltac:(clear; lia))); exact DEV).
    assert (DEE : L5.defined Mv E 16) by (apply (CL5A.defined_vis _ M E 16 (VOBJ E 16 Efr)); exact (proj1 (proj2 HEC))).
    assert (DSv : L5.defined Mv (sp - 14384) 14384) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (SZv : forall p n j, CL5A.ainfr FF p n -> p mod 8 = 0 -> 0 < n -> shadow_zero M p (n / 8) -> 0 <= j < n / 8 -> byte_at Mv (S p + j) 0).
    { intros p n j Hf Hp8 Hn HZ Hj. apply CL5A.byte_vis; [exact (VSH p n j Hf Hp8 Hj Hn) | exact (HZ j Hj)]. }
    assert (SEV : S (V + 8) = S V + 1) by (unfold S; clear - V8; apply Z.mod_divide in V8; [|lia]; destruct V8 as [q ->]; rewrite Z.div_mul by lia; replace (q * 8 + 8) with ((q + 1) * 8) by lia; rewrite Z.div_mul by lia; lia).
    split; [exact (GLC.regs_entry ch0 R Hch0)|]. unfold know_ok. rewrite (GLC.kn_entry ch0 Hch0). rewrite <- app_assoc. apply Forall_app. split.
    + let l := eval vm_compute in GLC.KNC in change GLC.KNC with l. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      * apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      * eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
      * eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
      * eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
      * eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
      * apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |]. intros j Hj. exact (SZv o 24 j Ofr O8 ltac:(clear; lia) Osh Hj).
      * eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
      * eapply CL5.kunk_intro with (A := V + 8) (N := 40); [ev0 | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DEv].
      * eapply CL5.krange_intro with (v := V + 8); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO S2 S3 SP1; lia].
      * eapply CL5.kalign_intro with (v := V + 8); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | clear - V8; rewrite Z.add_mod, V8 by lia; reflexivity].
      * apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 5 (V + 8)); [exact U11 | clear; lia | clear - Q3 Q6; lia |]. intros j Hj. rewrite SEV. replace (S V + 1 + j) with (S V + (j + 1)) by (clear; lia).
        exact (SZv V 48 (j + 1) Vfr V8 ltac:(clear; lia) Vsh ltac:(change (48 / 8) with 6; clear - Hj; lia)).
      * eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := V + 8) (N2 := 40); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in Q5; clear - Q5; lia].
      * eapply CL5.kunk_intro with (A := E) (N := 16); [ev0 | reflexivity | clear - W3; lia | clear - W6; lia | clear - W6; lia | exact DEE].
      * eapply CL5.kwr_intro with (A := E) (N := 16); [ev0 | reflexivity | clear - W3; lia | clear - W6; lia | clear - W6; lia | exact DEE].
      * eapply CL5.krange_intro with (v := E); [lin_eval; rw_atoms; clear; lia | clear - W3 W6; lia | clear - W1 W4 FSLO S2 S3 SP1; lia].
      * eapply CL5.kalign_intro with (v := E); [lin_eval; rw_atoms; clear; lia | clear - W3 W6; lia | clear; lia | exact E8].
      * apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 2 E); [exact U13 | clear; lia | clear - W3 W6; lia |]. intros j Hj. exact (SZv E 16 j Efr E8 ltac:(clear; lia) Esh Hj).
      * eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := E) (N2 := 16); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in W5; clear - W5; lia].
      * eapply CL5.kunk_intro with (A := sp - 14384) (N := 14384); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DSv].
      * eapply CL5.kwr_intro with (A := sp - 14384) (N := 14384); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DSv].
      * eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
      * eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact SP32].
      * eapply CL5.kdisj_intro with (A1 := sp - 14384) (N1 := 14384) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
      * eapply CL5.kdisj_intro with (A1 := sp - 14384) (N1 := 14384) (A2 := V + 8) (N2 := 40); [ev0 | reflexivity | ev0 | reflexivity | clear - Q4 S2; lia].
      * eapply CL5.kdisj_intro with (A1 := sp - 14384) (N1 := 14384) (A2 := E) (N2 := 16); [ev0 | reflexivity | ev0 | reflexivity | clear - W4 S2; lia].
      * eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := V + 8) (N2 := 40); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in APOV; clear - APOV; lia].
      * eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := E) (N2 := 16); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in APOE; clear - APOE; lia].
      * eapply CL5.kdisj_intro with (A1 := V + 8) (N1 := 40) (A2 := E) (N2 := 16); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in APVE; clear - APVE; lia].
    + apply Forall_cons.
      * eapply CL5.kword64_intro with (A := V + 8) (z := GLC.FLG ch0); [ev0 | clear - Q3; lia | clear - Q6; lia | cbn [edenot]; reflexivity |].
        exact (CL5A.u64_vis (hl_segs L) (ahid A model) M (V + 8) _ ltac:(clear - Q3; lia) ltac:(clear - Q6; lia) (CL5A.visr_sub _ V 48 (V + 8) 8 (VOBJ V 48 Vfr) ltac:(clear; lia) ltac:(clear; lia)) HFL).
      * destruct (Nat.eq_dec ch0 0) as [->|Hn0]; [apply Forall_nil|].
        assert (BV : GLC.BVC ch0 = [KWord (SA (EVar 11) 24) 1 (ELit (GLC.BV ch0))]) by (destruct ch0 as [|[|[|ch0]]]; [exfalso; exact (Hn0 eq_refl) | reflexivity | reflexivity | exfalso; clear - Hch0; lia]).
        rewrite BV. apply Forall_cons; [|apply Forall_nil].
        apply (CL5A.kword8_intro (hl_segs L) E0 Mv _ _ (V + 32) (GLC.BV ch0)); [ev0 | clear - Q3; lia | clear - Q6; lia | cbn [edenot]; reflexivity | destruct ch0 as [|[|[|]]]; cbn; clear; lia |].
        exact (CL5A.u8_vis (hl_segs L) (ahid A model) M (V + 32) _ ltac:(clear - Q3; lia) ltac:(clear - Q6; lia) (CL5A.visr_sub _ V 48 (V + 32) 1 (VOBJ V 48 Vfr) ltac:(clear; lia) ltac:(clear; lia)) (HBV Hn0)).
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite FFSnil, BLS0. cbn [app CHA.denF CH2.den map length].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; reflexivity | exact Hroom].
    + unfold XI. split; [exact CHN0|]. split; [exact HRO|]. split; [exact HEC|]. split; [exact HLS|]. split; [intros _; split; [exact DO | exact Hstksh]|].
      intros H0. exfalso. exact (H0 ST0).
  - exact Hfp.
Qed.

End GetLitOk.
