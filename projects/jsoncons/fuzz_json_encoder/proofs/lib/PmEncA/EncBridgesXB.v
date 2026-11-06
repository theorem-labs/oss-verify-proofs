(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitXB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EBA.
Import PMES.
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
Variable EC : PMESA.econsts.
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
Definition gB (g : eghost) : list (Z * Z) := PML.srep_blocks (g_rep g) ++ GR.
Variable kx bx : Z.
Definition CredV (g : eghost) (i : nat) (E : env) (cr : credit) : Prop := PMESA.ecreditA L CL cr g kx bx.
Variable XIv : eghost -> nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

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
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BLIN : 0 <= hl_b_lin L.
Hypothesis BOV : 0 <= hl_b_overhead L.
(* [comment removed for export] *)
Variables V S2 : Z.
Hypothesis OBJS0 : PMESA.objs_encA M00 FFrest V S2.
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
Abbreviation AAMBV := (CHV.aambV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV).
Abbreviation AMBXV := (CHV.ambXV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv).
Abbreviation AMBV := (CHV.ambV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv).
Abbreviation LEAFOKV := (CHV.leaf_okV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv CPS K FPI).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Abbreviation curB := (CHA.curB BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).
Definition STR_SCRA : Z := 4368.     (* [comment removed for export] *)
Lemma strx_scra : PMESA.STRX_SCRA = STR_SCRA.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition g_upd (g : eghost) (rep' : PML.srep) (n : Z) : eghost := EG (g_es g) (g_len g + n) rep' (g_sb g) (g_scap g).

(* [comment removed for export] *)
Definition sink_chk (unews : list kentry) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FFi : list (expr * Z * Z)) (BLj : CA.blocks) (FFj : list (expr * Z * Z))
  : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  match split_lit (nth 10 regs (ELit 0)) with
  | (ob, ok) =>
      if (expr_eqb ob OB && Z.eqb ok 0 && CH2.blocks_eqb BLj BLi && CHA.frames_eqb FFj FFi)%bool
      then CHA.custom_chk NF d SCELLS GLO GHI STR_SCRA 0 BLi FFi [(ob, ok, ELit 24)] (STAT ++ unews) None c ps cj BLi FFi BLj FFj
      else None
  end.

Lemma objs_facts : CL5A.ainfr FFrest V 408 /\ V mod 8 = 0 /\ shadow_zero M00 V 51 /\ CL5A.ainfr FFrest S2 24 /\ S2 mod 8 = 0 /\ shadow_zero M00 S2 3 /\ PMLA.apart V 408 S2 24.
Proof.
  destruct OBJS0 as ((A1 & A2 & A3) & (B1 & B2 & B3) & C0). unfold ENC_SIZE in *. change (408 / 8) with 51 in A3. change (24 / 8) with 3 in B3.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma amb_rng : forall g M0c i E A (M : mem) model, AAMBV g M0c i E A M model ->
  CHA.rng_facts L ar LBo FFrest /\ ar_stack_top ar <= 2 ^ 47.
Proof.
  intros g M0c i E A M model (_ & _ & _ & _ & (cr & LK & HH & _) & _).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. split; [|exact (CHA.wf_top _ _ _ _ _ _ _ _ WF)].
  apply (CHA.rng_incl L ar _ _ LBo FFrest (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF)).
  - unfold CHA.curB, CHV.LBr. intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - unfold CHA.curF. apply incl_appr, incl_refl.
Qed.

(* [comment removed for export] *)
Lemma kept_infr_sh : forall o n a, CHA.rng_facts L ar LBo FFrest -> CL5A.ainfr FFrest o n -> 0 < n -> in_shadow_of o n a ->
  CHA.akept L ar LBo FFrest sp0 SCR W a.
Proof.
  intros o n a RF Hfr Hn Ha. destruct (CL5A.infr_sh_wok L ar LBo FFrest sp0 SCR o n a RF Hfr Hn Ha) as (G1 & G2 & _).
  destruct (CL5A.infr_rng L ar LBo FFrest o n RF Hfr Hn) as (_ & _ & X3 & _ & _ & X6 & _). pose proof (CHA.shadow_range o n a X3 Hn X6 Ha) as SR.
  split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|].
  intros w Hw Hin. apply (proj1 (W_app w a Hw Hin)). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Lemma kept_stksh : forall a, CHA.rng_facts L ar LBo FFrest -> ar_stack_top ar <= 2 ^ 47 ->
  S (sp0 - SCR) <= a < S (sp0 - SCR) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp0 - SCR)) / 8 -> CHA.akept L ar LBo FFrest sp0 SCR W a.
Proof.
  intros a RF TOP Ha. destruct (CHA.rf_ceil _ _ _ _ RF) as (CL0 & C8). destruct (CHA.rf_sptop _ _ _ _ RF) as (SP1 & _). destruct STK as (S1 & S2' & S3).
  assert (AL : (sp0 - SCR) mod 8 = 0).
  { rewrite Zminus_mod, SCR8. rewrite <- Zminus_mod_idemp_l. rewrite Z.sub_0_r.
    pose proof (Z_div_mod_eq_full sp0 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by lia. rewrite Z_mod_mult. reflexivity. }
  destruct (PTA.stksh_rng ar sp0 SCR a ltac:(lia) AL C8 (proj2 SP1) TOP ltac:(lia) Ha) as (G1 & G2).
  split; [exact G1|]. split; [do 4 right; left; exact G2|].
  intros w Hw Hin. apply (proj1 (W_app w a Hw Hin)). pose proof (CHA.shadow_range (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a ltac:(lia) ltac:(lia) ltac:(lia) G2). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Lemma kept_img : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> CHA.akept L ar LBo FFrest sp0 SCR W a.
Proof.
  intros a Ha. destruct (IMG_RO_ok a Ha) as (I1 & I2). destruct LY_img as (L1 & L2). unfold BIGSHADOW_LO in L2.
  split; [lia|]. split; [do 2 right; left; split; [exact I1 | exact I2]|].
  intros w Hw Hin. exact (proj2 (W_app w a Hw Hin) Ha).
Qed.

(* [comment removed for export] *)
Lemma amb_env : forall g M0c i E A (M : mem) model, OKV M0c -> AAMBV g M0c i E A M model ->
  shadow_zero M V 51 /\ shadow_zero M S2 3 /\ PMSA.stksh ar M sp0 SCR /\ PMLA.img_ro IC M.
Proof.
  intros g M0c i E A M model OKV HA. destruct (CHV.frame00 L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV g M0c i E A M model OKV HA) as [F1 _].
  destruct (amb_rng g M0c i E A M model HA) as [RF TOP]. destruct objs_facts as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  split; [|split; [|split]].
  - apply (CL5A.shadow_zero_same M00 M V 51); [|exact O3]. intros j Hj. apply F1. apply (kept_infr_sh V 408); [exact RF | exact O1 | lia |].
    apply (CL5A.shreg_in_shadow V 51); [exact O2 | lia | unfold S in Hj |- *; lia].
  - apply (CL5A.shadow_zero_same M00 M S2 3); [|exact O6]. intros j Hj. apply F1. apply (kept_infr_sh S2 24); [exact RF | exact O4 | lia |].
    apply (CL5A.shreg_in_shadow S2 3); [exact O5 | lia | unfold S in Hj |- *; lia].
  - apply (PTA.stksh_ag ar M00 M sp0 SCR); [|exact STKSH0]. intros a Ha. apply F1. exact (kept_stksh a RF TOP Ha).
  - intros a Ha. rewrite (F1 a (kept_img a Ha)). exact (IMG0 a Ha).
Qed.

(* [comment removed for export] *)
Lemma enc_inv_grownA : forall (M' M2 : mem) g rep' n LBk FFk spc,
  PMESA.enc_invA L IC EC M' V S2 g -> CHA.ahpres L ar LBk FFk spc STR_SCRA [(S2, 24)] M' M2 ->
  (exists f, In f FFk /\ ff_addr f + 32 <= V /\ V + 408 <= ff_addr f + ff_bytes (ff_class f) - 8) ->
  (S2 + 24 <= BIGSHADOW_LO \/ BIGSHADOW_HI <= S2) ->
  (forall b, In b (stack_blocks (g_sb g) (g_scap g)) -> In b LBk /\ PMLA.apart (fst b) (snd b) S2 24) ->
  PMESA.sink_atA L M2 S2 rep' -> len (PML.srep_chars rep') = g_len g + n ->
  (forall b, In b (PML.srep_blocks rep') -> 0 <= fst b /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47) ->
  PMESA.enc_invA L IC EC M2 V S2 (g_upd g rep' n).
Proof.
  intros M' M2 g rep' n LBk FFk spc INV (HP1 & HP2 & HP3) (f & Hf & Vf1 & Vf2) S2app HSB Hsink Hlen Hnew.
  pose proof INV as (I1 & I2 & I3 & I4 & I5 & I6 & (R1 & R2 & R3 & R4 & RB)). unfold ENC_SIZE in R2.
  pose proof objs_facts as (_ & _ & _ & _ & _ & _ & AP). unfold PMLA.apart in AP.
  assert (KV : forall a, V <= a < V + 408 -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha. apply HP1. split; [lia|]. split; [do 3 right; left; exists f; split; [exact Hf | lia]|].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (AV : forall a n0, V <= a -> a + n0 <= V + 408 -> L5C.agree_on M' M2 a n0) by (intros a n0 H1 H2 i Hi; apply KV; lia).
  assert (STB : forall b, In b (stack_blocks (g_sb g) (g_scap g)) -> In b (g_lbv g)) by (intros b Hb; unfold g_lbv; apply in_or_app; right; exact Hb).
  unfold g_upd. split; [|split; [|split; [|split; [exact Hsink | split; [exact Hlen | split; [exact I6|]]]]]]; cbn [g_es g_len g_rep g_sb g_scap].
  - apply (EKA.enc_obj_agree L IC EC M' M2 V S2 _ R1 ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_COLUMN; lia | apply AV; unfold O_COLON, ENC_SIZE; lia | | exact I1].
    apply (L5C.defined_agree M' M2 (V + O_COLUMN) 8); [apply AV; unfold O_COLUMN; lia|].
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X.
  - apply (EKA.stack_at_agree L M' M2 V _ _ _ R1 ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_STACK; lia | | exact I2].
    intros Hne. assert (Hin : In (g_sb g, g_scap g) (stack_blocks (g_sb g) (g_scap g))).
    { unfold stack_blocks. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (HSB _ Hin) as [HinK HapS]. destruct (RB _ (STB _ Hin)) as (B0 & B1 & B2 & B3). cbn [fst snd] in *.
    split; [lia|]. split; [lia|]. intros i Hi. apply HP1. split; [lia|]. split; [left; exists (g_sb g, g_scap g); split; [exact HinK | cbn [fst snd]; lia]|].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold PMLA.apart in HapS. lia.
  - apply (EKA.stack_sh_agree M' M2 _ _ _); [|exact I3]. intros Hne.
    assert (Hin : In (g_sb g, g_scap g) (stack_blocks (g_sb g) (g_scap g))).
    { unfold stack_blocks. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (HSB _ Hin) as [HinK HapS]. destruct (RB _ (STB _ Hin)) as (B0 & B1 & B2 & B3). cbn [fst snd] in *.
    destruct I2 as (_ & _ & _ & S4 & S5 & _).
    assert (C8 : g_scap g mod 8 = 0) by (destruct S5 as [[E _]|(k & Hk & ->)]; [contradiction | apply EKA.mul32_mod8; lia]).
    assert (B8 : g_sb g mod 8 = 0) by (apply Z.mod_divide in B1; [|lia]; destruct B1 as [q ->]; replace (q * 16) with ((q * 2) * 8) by lia; apply Z_mod_mult).
    split; [exact B8|]. split; [exact C8|]. split; [pose proof (EKA.depth_nonneg (g_es g)); lia|].
    intros j Hj. apply HP1.
    assert (C32 : 32 <= g_scap g) by (destruct S5 as [[E _]|(k & Hk & E)]; [contradiction | pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); nia]).
    assert (G4 : 4 <= g_scap g / 8) by (apply Z.div_le_lower_bound; lia).
    pose proof (CL5A.shreg_in_shadow (g_sb g) (g_scap g / 8) (S (g_sb g) + j) B8 ltac:(lia) ltac:(unfold S; lia)) as SH.
    replace (8 * (g_scap g / 8)) with (g_scap g) in SH by (apply Z.mod_divide in C8; [|lia]; destruct C8 as [q Hq]; rewrite Hq at 1; rewrite Hq; rewrite Z.div_mul; lia).
    pose proof (CHA.shadow_range (g_sb g) (g_scap g) (S (g_sb g) + j) B0 ltac:(lia) B3 SH) as SR.
    split; [lia|]. split; [do 6 right; exists (g_sb g, g_scap g); split; [exact HinK | exact SH]|].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI in S2app. lia.
  - split; [exact R1|]. split; [unfold ENC_SIZE; lia|]. split; [exact R3|]. split; [exact R4|].
    intros b Hb. unfold g_lbv in Hb. cbn [g_rep g_sb g_scap] in Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (Hnew b Hb) | exact (RB b (STB b Hb))].
Qed.

Lemma al16_8 : forall x k, x mod 16 = 0 -> k mod 8 = 0 -> (x - k) mod 8 = 0.
Proof. clear. intros x k Hx Hk. rewrite Zminus_mod, Hk. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16) with ((q * 2) * 8) by lia. rewrite Z_mod_mult. reflexivity. Qed.

(* [comment removed for export] *)
Definition grow_call (pc n : Z) (Xtra : list (Z * Z) -> list fframe -> Z -> Z -> PML.srep -> bvmap 5 word -> mem -> Prop) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o sp r kx' bx' : Z) (rep : PML.srep),
    PMSA.cps_asan L ar HI pc r sp STR_SCRA LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ Xtra LB FF sp o rep R M /\ PMESA.sink_atA L M o rep /\ rep_live rep LB /\ PMSA.fobj M FF o 24 /\ PMSA.stksh ar M sp STR_SCRA /\
                  PMESA.screditA L CL cr rep kx' bx' /\ len (PML.srep_chars rep) + n <= CL)
      (fun R M R' M' LB' cr' LBk Wc => exists rep' s', len s' = len (PML.srep_chars rep) + n /\ PMESA.x_grownA L ar LB FF M' o rep s' LB' LBk rep' /\
                                       PMESA.screditA L CL cr' rep' kx' bx' /\ Wc = [(o, 24)]).

Lemma pushb_grow : forall pc, PMESA.str_push_back_x_specA L ar HI CL pc -> grow_call pc 1 (fun _ _ _ _ _ R _ => exists c, PMSA.a1 R c /\ 0 <= c < 256).
Proof.
  intros pc SPEC LB FF LK cr A o sp r kx' bx' rep fx R M model KK HH Hmo HK HFP Hra Hraok Hsp Htp Hstk Hroom Hffrs (P0 & (c & P1 & Hc) & P2 & P3 & P4 & P5 & P6 & P7) Hk.
  apply (SPEC LB FF LK cr A o c sp r kx' bx' rep fx R M model KK HH Hmo HK HFP Hra Hraok Hsp Htp); [rewrite strx_scra; exact Hstk | exact Hroom | exact Hffrs | |].
  - rewrite strx_scra. split; [exact P0|]. split; [exact P1|]. split; [exact Hc|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6 | exact P7].
  - intros fx' R' M' model' LB' cr' LBk Wc LK' A' HFP' (rep' & Hg & Hcr & HW) HRP HP Hrt HA Hmo' HLK HH'.
    apply (Hk fx' R' M' model' LB' cr' LBk Wc LK' A' HFP'); [| exact HRP | rewrite <- strx_scra; exact HP | exact Hrt | exact HA | exact Hmo' | exact HLK | exact HH'].
    exists rep', (PML.srep_chars rep ++ [c]). split; [unfold len; rewrite length_app; cbn [length]; lia|]. split; [exact Hg | split; [exact Hcr | exact HW]].
Qed.

Lemma append_grow : forall pc n, PMESA.str_append_x_specA L ar HI IC CL pc ->
  grow_call pc n (fun LB FF sp o rep R M => exists q (src : list Z), PMSA.a1 R q /\ PMSA.a2 R (len src) /\ len src = n /\ L5.bytes_at (hl_segs L) M q src /\
                                                               PMESA.src_okA ar HI IC M LB FF sp o rep q (len src)).
Proof.
  intros pc n SPEC LB FF LK cr A o sp r kx' bx' rep fx R M model KK HH Hmo HK HFP Hra Hraok Hsp Htp Hstk Hroom Hffrs (P0 & (q & src & P1 & P1b & Hn & P1c & P1d) & P2 & P3 & P4 & P5 & P6 & P7) Hk.
  subst n.
  apply (SPEC LB FF LK cr A o q sp r kx' bx' rep src fx R M model KK HH Hmo HK HFP Hra Hraok Hsp Htp); [rewrite strx_scra; exact Hstk | exact Hroom | exact Hffrs | |].
  - rewrite strx_scra. split; [exact P0|]. split; [exact P1|]. split; [exact P1b|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
    split; [exact P1c|]. split; [exact P1d|]. split; [exact P6 | exact P7].
  - intros fx' R' M' model' LB' cr' LBk Wc LK' A' HFP' (rep' & s' & Hl & Hg & Hcr & HW) HRP HP Hrt HA Hmo' HLK HH'.
    apply (Hk fx' R' M' model' LB' cr' LBk Wc LK' A' HFP'); [| exact HRP | rewrite <- strx_scra; exact HP | exact Hrt | exact HA | exact Hmo' | exact HLK | exact HH'].
    exists rep', s'. split; [exact Hl|]. split; [exact Hg | split; [exact Hcr | exact HW]].
Qed.

(* [comment removed for export] *)
Lemma den_app_nodup : forall (own : list (Z * Z)) rep FF LK cr A (M : mem) VM, ri_inv HI (own ++ LBo ++ PML.srep_blocks rep ++ GR) FF LK cr A M VM ->
  lb_drop rep (own ++ LBo ++ PML.srep_blocks rep ++ GR) = own ++ LBo ++ GR.
Proof.
  intros own rep FF LK cr M VM A HH. destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as [Hnd _].
  destruct rep as [s|cap p s]; cbn [lb_drop PML.srep_blocks app] in *; [reflexivity|].
  rewrite app_assoc. rewrite EKA.lb_remove_app.
  - cbn [lb_remove fst]. rewrite Z.eqb_refl. rewrite <- app_assoc. reflexivity.
  - rewrite app_assoc, map_app in Hnd. apply (EKA.nodup_app_l' _ _ p Hnd). cbn [map fst In]. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grow_leaf_okA : forall (pc n : Z) Xtra (unews : list kentry) i c k ps j cj ci g M0c,
  grow_call pc n Xtra ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  sink_chk unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  0 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' (cr : credit) LK R2 (M2 : mem) model2 LB' (cr' : credit) LK2 A2,
     CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI (CH2.den E' (nth i BLS []) ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR) (curF i E) LK cr A M' (vml_of model') ->
     regs_preserved R' R2 -> CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) STR_SCRA [(S2, 24)] M' M2 ->
     ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) -> incl (CH2.den E' (nth i BLS []) ++ LBo ++ GR) LB' ->
     forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [] R2) (CCA.vis A2 model2 M2) X) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     PMESA.enc_invA L IC EC M' V S2 g /\ incl (stack_blocks (g_sb g) (g_scap g)) (CH2.den E' (nth i BLS []) ++ LBo ++ GR) /\ 0 <= n /\ g_len g + n <= CL /\
     Xtra (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) (curF i E) (sp0 + CH2.ci_csp ci) S2 (g_rep g) R' M') ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' E2 A2 (M2 : mem) model2 g', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model ->
     XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) STR_SCRA [(S2, 24)] M' M2 ->
     PMESA.enc_invA L IC EC M2 V S2 g' -> g_es g' = g_es g -> g_sb g' = g_sb g -> g_scap g' = g_scap g -> g_len g' = g_len g + n ->
     XIv g' j E2 A2 M2 model2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc n Xtra unews i c k ps j cj ci g M0c GC HOKV IL Hret Hcj Hpc Hchk Hdc UNEWS XILEAF XIRET.
  intros fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  unfold sink_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. subst ob ok.
  apply CH2.blocks_eqb_eq in B3. pose proof (CHA.frames_eqb_eq _ _ B4) as B4e.
  set (BLi := nth i BLS []) in *. set (FFi := nth i FFS []) in *.
  apply (CHV.callee_leafV L ar C HI HIok LY_img LY_ro NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W Wo BLS FFS D0 eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
           CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok K_nil g M0c pc STR_SCRA 0%nat BLi [(OB, 0, ELit 24)] (STAT ++ unews) None 0 i c ps j cj ci HOKV Hcj Hchk Hpc B4 Hdc
           fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH).
  intros cr LK CF HH1 HLK1 HC1.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  destruct (XILEAF E R A M model E' R' M1 model1 HAt HA HXI Hag HLF CF) as (HINV & HST & Hn0 & HROOM & HXTRA).
  destruct (amb_env g M0c i E A M1 model1 HOKV HA') as (ZV & ZS & ZSTK & ZIMG).
  destruct (amb_rng g M0c i E A M1 model1 HA') as [RF TOP].
  destruct objs_facts as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof STK as (S1 & S2' & S3).
  destruct (CHA.rf_ceil _ _ _ _ RF) as (CL0 & C8). destruct (CHA.rf_sptop _ _ _ _ RF) as (SP1 & _).
  set (own := CH2.den E' BLi) in *.
  assert (HcB : CHA.curB (CHV.LBr LBo eghost gB g) BLS i E = own ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR).
  { unfold CHA.curB, CHV.LBr, gB, own. fold BLi. fold BLi in HdenB. rewrite <- HdenB. reflexivity. }
  fold BLi in HdenB. fold FFi in HdenF.
  rewrite HcB in HH1 |- *.
  assert (Ho : estart E' (SA OB 0) = S2).
  { unfold estart. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP NF E0 E' OB HagE' OB_frozen). rewrite OADDR. lia. }
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 S2).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). rewrite <- Ho. unfold estart. cbn [a_base a_off]. rewrite Z.add_0_r. reflexivity. }
  set (kx' := kx + kv_st (g_scap g) * hl_k_per_malloc L). set (bx' := bx + PMESA.bpot_st L (g_scap g)).
  eexists _, _. split; [exact (GC (own ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR) (curF i E) LK cr A S2 (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) kx' bx' (g_rep g))|].
  split.
  { (* [comment removed for export] *)
    pose proof HINV as (_ & _ & _ & Hsink & Hlen & _).
    split; [exact Ga0|]. split; [exact HXTRA|]. split; [exact Hsink|].
    split; [destruct (g_rep g) as [s|cap p s]; cbn [rep_live PML.srep_blocks]; [exact I | apply in_or_app; right; apply in_or_app; right; left; reflexivity]|].
    split; [split; [destruct O4 as (f & Hf & F1 & F2); exists f; split; [unfold CHA.curF; apply in_or_app; right; exact Hf | exact (conj F1 F2)] | split; [exact O5 | exact ZS]]|].
    split.
    { destruct Hstk as (A1 & _). apply (PTA.stksh_mono ar M1 sp0 SCR (sp0 + CH2.ci_csp ci) STR_SCRA ZSTK (al16_8 _ _ S1 SCR8) (al16_8 _ 4368 A1 eq_refl)). lia. }
    split; [exact (EKA.scredit_of_ecredit L CL KPM BLIN BOV cr g kx bx HC1)|].
    rewrite Hlen. exact HROOM. }
  (* [comment removed for export] *)
  intros R2 M2 model2 LB' cr' LBk Wc LK2 A2 (rep' & s' & Hls' & Hgrown & HCR' & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  pose proof (fun LBKE INCL => UNEWS E R A M model E' R' M1 model1 cr LK R2 M2 model2 LB' cr' LK2 A2 HAt HA HXI HagE' Hag HLF CF HH1 HRP LBKE HH2 INCL) as UN.
  pose proof (den_app_nodup own (g_rep g) _ _ _ _ _ _ HH1) as Hdrop.
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { clear - Hchk. unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d STR_SCRA 0 c ps cj BLi FFi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    do 6 (apply andb_prop in Hb as [Hb _]). apply andb_prop in Hb as [_ Hb]. exact Hb. }
  pose proof HINV as (_ & _ & _ & _ & _ & _ & (R1 & R2' & R3 & R4 & RB)).
  assert (FACTS : PMESA.sink_atA L M2 S2 rep' /\ len (PML.srep_chars rep') = g_len g + n /\ LBk = own ++ LBo ++ GR /\
                  Permutation LB' (own ++ LBo ++ PML.srep_blocks rep' ++ GR) /\
                  (forall b, In b (PML.srep_blocks rep') -> 0 <= fst b /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47)).
  { pose proof HINV as (_ & _ & _ & _ & Hlen & _).
    destruct Hgrown as [(F & -> & Hs & -> & ->)|(NFt & p' & Gx)].
    - split; [exact Hs|]. split; [destruct (g_rep g); cbn [same_rep PML.srep_chars] in Hls', Hlen |- *; lia|]. split; [exact Hdrop|].
      split; [destruct (g_rep g); cbn [same_rep PML.srep_blocks]; apply Permutation_refl|].
      intros b Hb. apply RB. unfold g_lbv. apply in_or_app. left. destruct (g_rep g); cbn [same_rep PML.srep_blocks] in Hb |- *; exact Hb.
    - cbv zeta in Gx. destruct Gx as (-> & Hs & FB & -> & ->). split; [exact Hs|]. split; [destruct (g_rep g); cbn [PML.srep_chars] in Hls', Hlen |- *; lia|]. split; [exact Hdrop|].
      rewrite Hdrop. split; [exact (CHV.perm_ghost_in own LBo [] GR _)|].
      intros b [<-|[]]. cbn [fst snd]. destruct FB as ((Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & _). lia. }
  clear Hgrown. destruct FACTS as (Hsink2 & Hlen2 & -> & Hperm & Hnew).
  exists [], (g_upd g rep' n). split; [reflexivity|]. cbv zeta.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  split; [exact I|].
  split; [rewrite app_assoc; apply incl_appl; apply incl_refl|].
  split.
  { intros w a [<-|[]] Hin. exists (OB, 0, ELit 24). split; [left; reflexivity|].
    unfold CHA.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia. }
  split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko (S2, 24) W_S2 Hin)|].
  assert (Hcur : CHA.curB (CHV.LBr LBo eghost gB (g_upd g rep' n)) BLS j E2 = own ++ LBo ++ PML.srep_blocks rep' ++ GR).
  { unfold CHA.curB, CHV.LBr, gB, g_upd. cbn [g_rep]. rewrite B3. unfold own. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
  split; [rewrite Hcur; exact (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH2 Hperm)|].
  split.
  { unfold CredV. apply (EKA.ecredit_of_scredit L CL cr' g kx bx rep' (g_upd g rep' n) eq_refl eq_refl HCR'); [exact (proj1 HC1) | exact (proj1 (proj2 (proj2 HC1)))]. }
  assert (HINV2 : PMESA.enc_invA L IC EC M2 V S2 (g_upd g rep' n)).
  { apply (enc_inv_grownA M1 M2 g rep' n (own ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) HINV HP).
    - destruct O1 as (f & Hf & F1 & F2). exists f. split; [unfold CHA.curF; apply in_or_app; right; exact Hf | exact (conj F1 F2)].
    - destruct (CL5A.infr_rng L ar LBo FFrest S2 24 RF O4 ltac:(lia)) as (_ & _ & _ & _ & X5 & _). exact X5.
    - intros b Hb. split; [exact (HST b Hb)|].
      pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as WF1.
      assert (HbL : In b (own ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR)).
      { pose proof (HST b Hb) as HbK. apply in_app_or in HbK as [X|X]; [apply in_or_app; left; exact X|]. apply in_or_app; right.
        apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X | right; apply in_or_app; right; exact X]. }
      destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF1 b HbL) as (_ & _ & _ & _ & FA).
      destruct O4 as (f & Hf & F1 & F2). specialize (FA f ltac:(apply in_or_app; left; unfold CHA.curF; apply in_or_app; right; exact Hf)). unfold PMLA.apart. lia.
    - exact Hsink2.
    - exact Hlen2.
    - exact Hnew. }
  split.
  { apply (XIRET E R A M model E' R' M1 model1 E2 A2 M2 model2 (g_upd g rep' n) HAt HA HXI HagE' Hag HLF Hag2 V3 CF HP HINV2); reflexivity. }
  (* [comment removed for export] *)
  intros X HX HXj. apply in_app_or in HX. destruct HX as [HX|HX].
  - rewrite forallb_forall in STAT_ok.
    exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 (STAT_ok X HX)).
  - unfold E2. apply (UN HP); [|exact HX | exact HXj].
    intros bb Hbb. apply (Permutation_in bb (Permutation_sym Hperm)). apply in_app_or in Hbb as [Hbb|Hbb]; apply in_or_app; [left; exact Hbb|]. right.
    apply in_app_or in Hbb as [Hbb|Hbb]; apply in_or_app; [left; exact Hbb | right; apply in_or_app; right; exact Hbb].
Qed.

(* [comment removed for export] *)
Definition pushb_chk (unews : list kentry) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FFi : list (expr * Z * Z)) (BLj : CA.blocks) (FFj : list (expr * Z * Z))
  : option CH2.cinfo :=
  if APC.fact_ok (SR.ps_cells ps) (KRange (nth 11 (CA.ps_reglist ps) (ELit 0)) 0 255) then sink_chk unews c ps cj BLi FFi BLj FFj else None.

Lemma pushb_leaf_ok : forall pc (unews : list kentry) i c k ps j cj ci g M0c,
  PMESA.str_push_back_x_specA L ar HI CL pc ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  pushb_chk unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  0 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' (cr : credit) LK R2 (M2 : mem) model2 LB' (cr' : credit) LK2 A2,
     CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI (CH2.den E' (nth i BLS []) ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR) (curF i E) LK cr A M' (vml_of model') ->
     regs_preserved R' R2 -> CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) STR_SCRA [(S2, 24)] M' M2 ->
     ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) -> incl (CH2.den E' (nth i BLS []) ++ LBo ++ GR) LB' ->
     forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [] R2) (CCA.vis A2 model2 M2) X) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     PMESA.enc_invA L IC EC M' V S2 g /\ incl (stack_blocks (g_sb g) (g_scap g)) (CH2.den E' (nth i BLS []) ++ LBo ++ GR) /\ g_len g + 1 <= CL) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' E2 A2 (M2 : mem) model2 g', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model ->
     XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) STR_SCRA [(S2, 24)] M' M2 ->
     PMESA.enc_invA L IC EC M2 V S2 g' -> g_es g' = g_es g -> g_sb g' = g_sb g -> g_scap g' = g_scap g -> g_len g' = g_len g + 1 ->
     XIv g' j E2 A2 M2 model2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc unews i c k ps j cj ci g M0c PUSHB HOKV IL Hret Hcj Hpc Hchk Hdc UNEWS XILEAF XIRET.
  unfold pushb_chk in Hchk. destruct (APC.fact_ok (SR.ps_cells ps) (KRange (nth 11 (CA.ps_reglist ps) (ELit 0)) 0 255)) eqn:B5; [|discriminate].
  apply (grow_leaf_okA pc 1 _ unews i c k ps j cj ci g M0c (pushb_grow pc PUSHB) HOKV IL Hret Hcj Hpc Hchk Hdc UNEWS); [|exact XIRET].
  intros E R A M model E' R' M' model' HAt HA HXI Hag HLF CF.
  destruct (XILEAF E R A M model E' R' M' model' HAt HA HXI Hag HLF CF) as (HINV & HST & HROOM).
  split; [exact HINV|]. split; [exact HST|]. split; [lia|]. split; [exact HROOM|].
  pose proof CF as [_ HR Hreq _ HK _ _ _ _ _ _ _ _].
  pose proof (APS.fact_ok_sound (hl_segs L) E' _ _ _ HK B5) as Hc. cbn [kentry_ok] in Hc.
  set (cv := bv_unsigned (edenot E' (nth 11 (CA.ps_reglist ps) (ELit 0)))) in *.
  exists cv. split; [|lia].
  unfold PMSA.a1. rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
  unfold cv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma append_leaf_ok : forall pc (unews : list kentry) (n : Z) i c k ps j cj ci g M0c,
  PMESA.str_append_x_specA L ar HI IC CL pc ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  sink_chk unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  0 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' (cr : credit) LK R2 (M2 : mem) model2 LB' (cr' : credit) LK2 A2,
     CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI (CH2.den E' (nth i BLS []) ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR) (curF i E) LK cr A M' (vml_of model') ->
     regs_preserved R' R2 -> CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) STR_SCRA [(S2, 24)] M' M2 ->
     ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) -> incl (CH2.den E' (nth i BLS []) ++ LBo ++ GR) LB' ->
     forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [] R2) (CCA.vis A2 model2 M2) X) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     PMESA.enc_invA L IC EC M' V S2 g /\ incl (stack_blocks (g_sb g) (g_scap g)) (CH2.den E' (nth i BLS []) ++ LBo ++ GR) /\ 0 <= n /\ g_len g + n <= CL /\
     exists q src, PMSA.a1 R' q /\ PMSA.a2 R' (len src) /\ len src = n /\ L5.bytes_at (hl_segs L) M' q src /\
                   PMESA.src_okA ar HI IC M' (CH2.den E' (nth i BLS []) ++ LBo ++ gB g) (curF i E) (sp0 + CH2.ci_csp ci) S2 (g_rep g) q (len src)) ->
  (forall E R A (M : mem) model E' R' (M' : mem) model' E2 A2 (M2 : mem) model2 g', CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model ->
     XIv g i E A M model -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 STR_SCRA 0 c ps cj ci i E E' R' A M' model' ->
     CHA.ahpres L ar (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (curF i E) (sp0 + CH2.ci_csp ci) STR_SCRA [(S2, 24)] M' M2 ->
     PMESA.enc_invA L IC EC M2 V S2 g' -> g_es g' = g_es g -> g_sb g' = g_sb g -> g_scap g' = g_scap g -> g_len g' = g_len g + n ->
     XIv g' j E2 A2 M2 model2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc unews n i c k ps j cj ci g M0c APPEND HOKV IL Hret Hcj Hpc Hchk Hdc UNEWS XILEAF XIRET.
  apply (grow_leaf_okA pc n _ unews i c k ps j cj ci g M0c (append_grow pc n APPEND) HOKV IL Hret Hcj Hpc Hchk Hdc UNEWS); [|exact XIRET].
  intros E R A M model E' R' M' model' HAt HA HXI Hag HLF CF.
  destruct (XILEAF E R A M model E' R' M' model' HAt HA HXI Hag HLF CF) as (HINV & HST & Hn & HROOM & SRC).
  split; [exact HINV|]. split; [exact HST|]. split; [exact Hn|]. split; [exact HROOM | exact SRC].
Qed.

End Inst.
End EBA.
