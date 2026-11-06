(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitA EncSinkBridgesA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FXKA.
Import PMES.
Import ESBA.
Abbreviation mem := (word -> option byte).

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable IC : PMLA.consts.
Variable CL : Z.                    (* [comment removed for export] *)
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBo : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable D0 : Z.
(* [comment removed for export] *)
Variable GR : list (Z * Z).
Abbreviation gB := (ESBA.gB GR).
Variable kx bx : Z.
Abbreviation CredV := (ESBA.CredV L CL kx bx).
Variable S2 : Z.
Variable XIv : ESBA.sghost -> nat -> env -> list (Z * Z) -> mem -> Model -> Prop.
(* [comment removed for export] *)
Abbreviation sink_inv := (ESBA.sink_inv L S2).

Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis SCR8 : SCR mod 8 = 0.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBo FFrest sp0 SCR a
                                                       /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBo FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M00 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
(* [comment removed for export] *)
Variable STAT : list kentry.
Hypothesis STAT_ok : forallb (CHA.static_chk SCELLS GLO GHI) STAT = true.
(* [comment removed for export] *)
Hypothesis FOBJ0 : PMSA.fobj M00 FFrest S2 24.
Hypothesis STKSH0 : PMSA.stksh ar M00 sp0 SCR.
Hypothesis IMG0 : PMLA.img_ro IC M00.
Hypothesis IMG_RO_ok : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Hypothesis W_S2 : In (S2, 24) W.
(* [comment removed for export] *)
Hypothesis W_app : forall w a, In w W -> L5.in_rng w a -> ~ (BIGSHADOW_LO <= a < BIGSHADOW_HI) /\ ~ (PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).
(* [comment removed for export] *)
Variable OB : expr.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Hypothesis OADDR : bv_unsigned (edenot E0 OB) = S2.

Abbreviation FPI := PMSA.fp_ok.
Abbreviation OKV := (CHV.okV L ar M00 LBo FFrest sp0 d W).
Abbreviation AAMBV := (CHV.aambV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 ESBA.sghost gB CredV).
Abbreviation LEAFOKV := (CHV.leaf_okV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 ESBA.sghost gB CredV XIv CPS K FPI).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).

(* [comment removed for export] *)
Definition strans_specA (pc scr dcal : Z) (Wx : list L5.range)
           (Args : list (Z * Z) -> list fframe -> Z -> bvmap 5 word -> mem -> Z -> Prop) (Ret : bvmap 5 word -> Z -> Prop) (PayP : Z -> Prop) (paymax : Z) : Prop :=
  forall (LB1 : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r SK o kx' bx' : Z) (rep : PML.srep),
    PMSA.cps_asan L ar HI pc r sp scr (LB1 ++ PML.srep_blocks rep) FF LK cr A dcal
      (fun R M => Args LB1 FF sp R M SK /\ PMSA.u64 L M SK o /\ L5.defined M SK 8 /\ PMSA.acobj ar FF sp SK 8 /\ SK mod 8 = 0 /\ shadow_zero M SK 1 /\ PMLA.apart SK 8 o 24 /\
                  PMSA.stksh ar M sp scr /\ PMESA.sink_atA L M o rep /\ PMSA.fobj M FF o 24 /\ PMLA.img_ro IC M /\ PMESA.screditA L CL cr rep kx' bx' /\ len (PML.srep_chars rep) + paymax <= CL)
      (fun R M R' M' LB' cr' LBk Wc => exists (rep' : PML.srep) (pay : Z),
          PayP pay /\ Ret R' pay /\ PMESA.sink_atA L M' o rep' /\ len (PML.srep_chars rep') = len (PML.srep_chars rep) + pay /\
          LB' = LB1 ++ PML.srep_blocks rep' /\ LBk = LB1 /\ Wc = (o, 24) :: Wx /\ PMESA.screditA L CL cr' rep' kx' bx').
Lemma of_stransA : forall pc scr dcal Args Ret PayP paymax, PMESA.stransA L ar HI IC CL pc scr dcal Args Ret PayP paymax -> strans_specA pc scr dcal [] Args Ret PayP paymax.
Proof. intros pc scr dcal Args Ret PayP paymax H LB1 FF LK cr A sp r SK o kx' bx' rep. exact (H LB1 FF LK cr A sp r SK o kx' bx' rep). Qed.
Lemma of_stransA_w : forall pc scr dcal Wx Args Ret PayP paymax, PMESA.stransA_w L ar HI IC CL pc scr dcal Wx Args Ret PayP paymax -> strans_specA pc scr dcal Wx Args Ret PayP paymax.
Proof. intros pc scr dcal Wx Args Ret PayP paymax H LB1 FF LK cr A sp r SK o kx' bx' rep. exact (H LB1 FF LK cr A sp r SK o kx' bx' rep). Qed.

(* [comment removed for export] *)
Definition strans_chkA (scr : Z) (Wxe : list (expr * Z * expr)) (unews : list kentry) (a0x : option expr) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint)
           (BLi : CA.blocks) (FFi : list (expr * Z * Z)) (BLj : CA.blocks) (FFj : list (expr * Z * Z)) : option CH2.cinfo :=
  if (CH2.blocks_eqb BLj BLi && CHA.frames_eqb FFj FFi)%bool
  then CHA.custom_chk NF d SCELLS GLO GHI scr 0 BLi FFi ((OB, 0, ELit 24) :: Wxe) (STAT ++ unews) a0x c ps cj BLi FFi BLj FFj
  else None.

Lemma cps_perm : forall pc r sp scr LB1 LB2 FF LK cr A dc Pre Post, Permutation LB1 LB2 ->
  PMSA.cps_asan L ar HI pc r sp scr LB2 FF LK cr A dc Pre Post -> PMSA.cps_asan L ar HI pc r sp scr LB1 FF LK cr A dc Pre Post.
Proof.
  intros pc r sp scr LB1 LB2 FF LK cr A dc Pre Post HP SPEC fx R M model KK HH. apply SPEC. exact (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH HP).
Qed.
Lemma perm4 : forall (A1 B1 C1 D1 : list (Z * Z)), Permutation (A1 ++ B1 ++ C1 ++ D1) ((A1 ++ B1 ++ D1) ++ C1).
Proof. clear. intros. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm. Qed.

Lemma al16_8 : forall x k, x mod 16 = 0 -> k mod 8 = 0 -> (x - k) mod 8 = 0.
Proof.
  clear. intros x k Hx Hk. rewrite Zminus_mod, Hk. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->].
  replace (q * 16) with ((q * 2) * 8) by lia. rewrite Z_mod_mult. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma strans_leaf_okA : forall (pc scr dcal : Z) (Wx : list L5.range) (Wxe : list (expr * Z * expr)) Args Ret PayP paymax (unews : list kentry) (a0x : option expr)
                          i c k ps j cj ci g M0c,
  strans_specA pc scr dcal Wx Args Ret PayP paymax ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  strans_chkA scr Wxe unews a0x c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  dcal <= D0 - Z.of_nat (length (nth i FFS [])) -> 0 <= scr -> scr mod 8 = 0 -> 0 <= paymax ->
  (forall E', env_agree NF E0 E' -> forall w a, In w Wx -> L5.in_rng w a -> exists r, In r Wxe /\ CHA.in_reg E' r a) ->
  (forall w a, In w Wx -> L5.in_rng w a -> In w W) ->
  (forall (R2 : bvmap 5 word) pay (E2 : env), Ret R2 pay -> match a0x with Some e => getr R2 10%bv = edenot E2 e | None => True end) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' (cr : credit) LK R2 (M2 : mem) model2 LB' (cr' : credit) LK2 A2,
     CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo ESBA.sghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 scr 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI (CH2.den E' (nth i BLS []) ++ LBo ++ PML.srep_blocks (s_rep g) ++ GR) (curF i E) LK cr A M' (vml_of model') ->
     regs_preserved R' R2 -> CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) scr ((S2, 24) :: Wx) M' M2 ->
     ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) -> incl (CH2.den E' (nth i BLS []) ++ LBo ++ GR) LB' ->
     forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [] R2) (CCA.vis A2 model2 M2) X) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo ESBA.sghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 scr 0 c ps cj ci i E E' R' A M' model' ->
     sink_inv M' g /\ s_len g + paymax <= CL /\
     exists SK, Args (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) R' M' SK /\ PMSA.u64 L M' SK S2 /\ L5.defined M' SK 8 /\
                PMSA.acobj ar (curF i E) (sp0 + CH2.ci_csp ci) SK 8 /\ SK mod 8 = 0 /\ shadow_zero M' SK 1 /\ PMLA.apart SK 8 S2 24) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' E2 A2 (M2 : mem) model2 g' (pay : Z) R2, CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model ->
     XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo ESBA.sghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 scr 0 c ps cj ci i E E' R' A M' model' ->
     CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) scr ((S2, 24) :: Wx) M' M2 ->
     PayP pay -> Ret R2 pay -> ev E2 (CH2.ci_nx ci + 0 + 4)%nat = getr R2 10%bv ->
     sink_inv M2 g' -> s_len g' = s_len g + pay ->
     XIv g' j E2 A2 M2 model2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr dcal Wx Wxe Args Ret PayP paymax unews a0x i c k ps j cj ci g M0c SPEC HOKV IL Hret Hcj Hpc Hchk Hdc Hscr0 Hscr8 Hpay0 WXE WXW RETA0 UNEWS XILEAF XIRET.
  intros fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  unfold strans_chkA in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [B3 B4]. apply CH2.blocks_eqb_eq in B3. pose proof (CHA.frames_eqb_eq _ _ B4) as B4e.
  set (BLi := nth i BLS []) in *. set (FFi := nth i FFS []) in *.
  apply (CHV.callee_leafV L ar C HI HIok LY_img LY_ro NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W Wo BLS FFS D0 ESBA.sghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
           CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok K_nil g M0c pc scr 0%nat BLi ((OB, 0, ELit 24) :: Wxe) (STAT ++ unews) a0x dcal i c ps j cj ci HOKV Hcj Hchk Hpc B4 Hdc
           fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH).
  intros cr LK CF HH1 HLK1 HC1.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  destruct (XILEAF E R A M model E' R' M1 model1 HAt HA HXI Hag HLF CF) as ([Hsink Hlen] & HROOM & SK & HARGS & KU & KD & KA & K8 & KZ & KP).
  destruct (ESBA.amb_env L ar C HI HIok LY_img IC CL NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 GR kx bx S2 STK SCR_pos SCR8 NF32 FOBJ0 STKSH0 IMG0 IMG_RO_ok W_app
              g M0c i E A M1 model1 HOKV HA') as (ZS & ZSTK & ZIMG).
  destruct (ESBA.amb_rng L ar C HI HIok CL NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 GR kx bx g M0c i E A M1 model1 HA') as [RF TOP].
  destruct (ESBA.objs_facts M00 FFrest S2 FOBJ0) as (O4 & O5 & O6). pose proof STK as (S1 & S2' & S3).
  destruct (CHA.rf_ceil _ _ _ _ RF) as (CL0 & C8). destruct (CHA.rf_sptop _ _ _ _ RF) as (SP1 & _).
  set (own := CH2.den E' BLi) in *.
  assert (GBL : forall g1, gB g1 = PML.srep_blocks (s_rep g1) ++ GR) by (intros g1; reflexivity).
  assert (HcB : CHA.curB (CHV.LBr LBo ESBA.sghost gB g) BLS i E = own ++ LBo ++ PML.srep_blocks (s_rep g) ++ GR).
  { unfold CHA.curB, CHV.LBr, own. fold BLi. fold BLi in HdenB. rewrite <- HdenB, (GBL g). reflexivity. }
  fold BLi in HdenB. fold FFi in HdenF.
  rewrite HcB in HH1 |- *.
  assert (Ho : estart E' (SA OB 0) = S2).
  { unfold estart. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP NF E0 E' OB HagE' OB_frozen). rewrite OADDR. lia. }
  eexists _, _. split.
  { exact (cps_perm _ _ _ _ _ _ _ _ _ _ _ _ _ (perm4 own LBo (PML.srep_blocks (s_rep g)) GR)
             (SPEC (own ++ LBo ++ GR) (curF i E) LK cr A (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) SK S2 kx bx (s_rep g))). }
  split.
  { (* [comment removed for export] *)
    split; [exact HARGS|]. split; [exact KU|]. split; [exact KD|]. split; [exact KA|]. split; [exact K8|]. split; [exact KZ|]. split; [exact KP|].
    split.
    { destruct Hstk as (A1 & _). apply (PTA.stksh_mono ar M1 sp0 SCR (sp0 + CH2.ci_csp ci) scr ZSTK (al16_8 _ _ S1 SCR8) (al16_8 _ _ A1 Hscr8)). lia. }
    split; [exact Hsink|].
    split; [split; [destruct O4 as (f & Hf & F1 & F2); exists f; split; [unfold CHA.curF; apply in_or_app; right; exact Hf | exact (conj F1 F2)] | split; [exact O5 | exact ZS]]|].
    split; [exact ZIMG|]. split; [exact HC1|]. rewrite Hlen. exact HROOM. }
  (* [comment removed for export] *)
  intros R2 M2 model2 LB' cr' LBk Wc LK2 A2 (rep' & pay & HPP & HRet & Hs2 & Hls' & -> & -> & -> & HCR') HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  pose proof (fun LBKE INCL => UNEWS E R A M model E' R' M1 model1 cr LK R2 M2 model2 _ cr' LK2 A2 HAt HA HXI HagE' Hag HLF CF HH1 HRP LBKE HH2 INCL) as UN.
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { clear - Hchk. unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d scr 0 c ps cj BLi FFi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    do 6 (apply andb_prop in Hb as [Hb _]). apply andb_prop in Hb as [_ Hb]. exact Hb. }
  exists [], (SG rep' (s_len g + pay)). split; [reflexivity|]. cbv zeta.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  split; [destruct a0x as [e|]; [exact (RETA0 R2 pay E2 HRet) | exact I]|].
  split; [rewrite app_assoc; apply incl_appl; apply incl_refl|].
  split.
  { intros w a Hw Hin. destruct Hw as [<-|Hw].
    - exists (OB, 0, ELit 24). split; [left; reflexivity|].
      unfold CHA.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
    - destruct (WXE E' HagE' w a Hw Hin) as (rr & Hrr & Hin'). exists rr. split; [right; exact Hrr | exact Hin']. }
  split; [intros w a Hw Hin (_ & _ & Ko); destruct Hw as [<-|Hw]; [exact (Ko (S2, 24) W_S2 Hin) | exact (Ko w (WXW w a Hw Hin) Hin)]|].
  assert (Hcur : CHA.curB (CHV.LBr LBo ESBA.sghost gB (SG rep' (s_len g + pay))) BLS j E2 = own ++ LBo ++ PML.srep_blocks rep' ++ GR).
  { unfold CHA.curB, CHV.LBr. rewrite (GBL (SG rep' (s_len g + pay))). cbn [s_rep]. rewrite B3. unfold own. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
  split; [rewrite Hcur; exact (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH2 (Permutation_sym (perm4 own LBo (PML.srep_blocks rep') GR)))|].
  split; [exact HCR'|].
  split.
  { apply (XIRET E R A M model E' R' M1 model1 E2 A2 M2 model2 (SG rep' (s_len g + pay)) pay R2 HAt HA HXI HagE' Hag HLF Hag2 V3 CF HP HPP HRet).
    - unfold E2. exact (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2).
    - split; [exact Hs2 | cbn [s_rep s_len]; rewrite Hls'; lia].
    - reflexivity. }
  (* [comment removed for export] *)
  intros X HX HXj. apply in_app_or in HX. destruct HX as [HX|HX].
  - rewrite forallb_forall in STAT_ok.
    exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 (STAT_ok X HX)).
  - unfold E2. apply (UN HP); [|exact HX | exact HXj].
    intros bb Hbb. apply in_or_app. left. exact Hbb.
Qed.
End Inst.
End FXKA.
