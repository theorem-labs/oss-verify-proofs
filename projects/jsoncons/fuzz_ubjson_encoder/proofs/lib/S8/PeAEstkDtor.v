(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceANull IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PeSpecsAa PgSrc PgV8 PgSrcA PgV8A PnModel PnModelFacts PnRun PeRunBA PeSpecsAX PmModelFactsA PmStep PeStepA PeASrcKit PeAReset1 PeAEmbKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCSinkA PeCModel PeCModelA PeCDtorSpecsA PeASnkAnn PeAEstkAnn PeAEstkHP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b14b8_b14bc Ea0_code_b1430_b1438.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PEAEKD.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Definition nsh (a n : Z) : Prop := a + n <= 2147446784 \/ 17594333495296 <= a.
Lemma nsh_not a n x : nsh a n -> a <= x < a + n -> ~ (BIGSHADOW_LO <= x < BIGSHADOW_HI).
Proof. unfold nsh, BIGSHADOW_LO, BIGSHADOW_HI. intros [X|X] H Y; lia. Qed.

Lemma lbr_iff B m (LB : list (Z * Z)) : NoDup (map fst LB) -> In (B, m) LB -> forall x, In x LB <-> In x ((B, m) :: lb_remove B LB).
Proof.
  induction LB as [|y LB IH]; intros ND Hin x; [destruct Hin|]. cbn [map] in ND. apply stdpp.list_relations.list.NoDup_cons in ND as (NI & ND'). cbn [lb_remove].
  destruct (Z.eqb_spec (fst y) B) as [E|E].
  - destruct Hin as [<-|Hin]; [reflexivity|]. exfalso. apply NI. rewrite E. apply list_elem_of_In. exact (in_map fst LB (B, m) Hin).
  - destruct Hin as [->|Hin]; [exfalso; apply E; reflexivity|]. specialize (IH ND' Hin x). cbn [In] in *. tauto.
Qed.
Lemma lbr_nodup B (LB : list (Z * Z)) : NoDup (map fst LB) -> NoDup (map fst (lb_remove B LB)) /\ B ∉ map fst (lb_remove B LB).
Proof.
  induction LB as [|y LB IH]; intros ND; [split; [constructor| intros X; inversion X]|]. cbn [map] in ND. apply stdpp.list_relations.list.NoDup_cons in ND as (NI & ND'). cbn [lb_remove].
  destruct (Z.eqb_spec (fst y) B) as [E|E].
  - split; [exact ND'| rewrite <- E; exact NI].
  - destruct (IH ND') as (N1 & N2). cbn [map]. split.
    + apply stdpp.list_relations.list.NoDup_cons. split; [|exact N1]. intros X. apply NI. apply list_elem_of_In. apply list_elem_of_In in X.
      apply in_map_iff in X as (z & Ez & Hz). apply in_map_iff. exists z. split; [exact Ez| exact (L5C.in_lb_remove B z LB Hz)].
    + intros X. apply stdpp.list_basics.list.elem_of_cons in X as [X|X]; [apply E; symmetry; exact X| exact (N2 X)].
Qed.

Lemma aobjA_sub FF o n o' n' : PMSPA.aobjA FF o n -> o <= o' -> o' + n' <= o + n -> PMSPA.aobjA FF o' n'.
Proof. intros (f & Hf & X1 & X2) H1 H2. exists f. split; [exact Hf|]. lia. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Lemma ri_front LB FF LK cr Aw M V B m : ri_inv HI LB FF LK cr Aw M V -> In (B, m) LB -> ri_inv HI ((B, m) :: lb_remove B LB) FF LK cr Aw M V.
Proof.
  intros HH Hin. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ ((B, m) :: lb_remove B LB) FF FF LK cr Aw M V HH).
  - exact (lbr_iff B m LB ND Hin).
  - destruct (lbr_nodup B LB ND) as (N1 & N2). cbn [map fst]. apply stdpp.list_relations.list.NoDup_cons. split; [exact N2| exact N1].
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.

Lemma stk_keep LB FF sp scr W M M' a n : L5SAR.ek L ar LB FF sp scr W M M' -> 0 <= ahl_ceil ar <= a -> sp <= a -> a + n <= 2 ^ 47 ->
  (forall i, a <= i < a + n -> L5.outside W i) -> L5C.agree_on M M' a n.
Proof.
  intros E H1 H2 H3 OW i Hi. apply E. split; [lia|]. split; [| apply OW; lia].
  unfold aclient, aclient_g. right; left. split; [lia| intros X; lia].
Qed.
Lemma stk_sh_keep LB FF sp scr W M M' a n : L5SAR.ek L ar LB FF sp scr W M M' -> PMKA.wapp W -> 0 <= ahl_ceil ar <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M' a n.
Proof.
  intros E WA H1 H2 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
  apply E. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split.
  - unfold aclient, aclient_g. do 4 right; left. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
  - exact (PMKA.wapp_outside_shadow W (S x) WA SX).
Qed.

Lemma stk_shz_vis (H0 : word -> bool) (M : word -> option byte) t :
  (forall a n, (forall i, 0 <= i < n -> in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) (a + i)) -> L5A.avis H0 a n) ->
  PMSPA.accA M t 8 -> t mod 8 = 0 -> 0 <= ahl_ceil ar <= t -> t + 8 <= ar_sptop ar -> L5KA.zeros_at (mrestrict H0 M) (t / 8 + SB) 1.
Proof.
  intros VSH TC T8 H1 H2. pose proof (PMKA.zeros_of_aacc M t 8 TC T8 ltac:(reflexivity) ltac:(lia)) as Z0. change (8 / 8) with 1 in Z0.
  assert (V : L5A.avis H0 (t / 8 + SB) 1).
  { apply VSH. intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r. unfold in_shadow_of, S. split.
    - apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    - apply Z.add_le_mono_r. apply Z.div_le_mono; lia. }
  apply (proj2 (L5A.zeros_at_vis H0 M (t / 8 + SB) 1 V)). exact Z0.
Qed.

Lemma estk_dtor_null : forall (fx : FPState) R M model K LB FF LK Aw cr t v sp r,
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> PMSPA.entryA AD L ar R M sp r 1 ->
    PMSPA.ffroomA 1 FF LK -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> PMSPA.accA M t 8 -> L5.u64_at RSEGS M t v ->
    PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> PMSPA.accA M v 24 ->
    L5.u64_at RSEGS M v 0 ->
    (forall (fx' : FPState) R' M' model' LK' Aw',
        regs_preserved R R' ->
        L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI LB FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb140c M model) K.
Proof.
  intros fx R M model K LB FF LK Aw cr t v sp r HH AM K0 ENT FRM FRS A10 Tsp Ttop T8 TC Tv AOv V8 VD VC VEC KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in *. change (14336 / 8) with 1792 in STKSH.
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & ND & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (OtVIS : L5A.avis H t 8) by (apply VIS; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model v 24 sp 14336 HH (PMKA.aobj_of_aobjA FF v 24 AOv V8) ltac:(lia) ltac:(reflexivity))
    as ((Ov1 & Ov2 & Ov3 & Ov4 & Ov5) & OvBIG & OvDEF & OvVIS & OvSHV & OvCL & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (HO : bv_unsigned (getr R (reg 10)) = t) by (rewrite A10; apply L5.unsigned_lit; lia).
  pose proof VEC as W0.
  assert (OTN : nsh t 8) by (unfold nsh; right; clear - Tsp SLO SPT; lia).
  assert (OVN : nsh v 24) by (unfold nsh; destruct OvBIG as [X|X]; [right| left]; lia).
  assert (OPS : v + 24 + 4096 + 14336 <= sp) by (clear - Ov2 SLO; lia).
  assert (ZT : L5KA.zeros_at MV (t / 8 + SB) 1) by exact (stk_shz_vis H M t VSTSH TC T8 ltac:(lia) Ttop).
  assert (ZV : L5KA.zeros_at MV (v / 8 + SB) 3) by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model v 24 HH AOv V8 ltac:(lia) ltac:(reflexivity) VC).
  assert (VSW : L5.writable RSEGS MV (sp - 32) 32).
  { apply (proj2 (L5A.writable_vis H M (sp - 32) 32 (VIS (sp - 32) 32 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]| lia| lia]. }
  assert (IC0 : L5.img_clear MV 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1317368 2147450880 (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (Tvv : L5.u64_at RSEGS MV t v) by (apply (proj2 (L5A.u64_at_vis H M t v OtVIS ltac:(lia) ltac:(lia))); exact Tv).
  assert (W0v : L5.u64_at RSEGS MV v 0) by (apply (proj2 (L5A.u64_at_vis H M v 0 (L5A.avis_sub H v 24 v 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact W0).

  pose proof (PEAEHP.hkeN_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | _ => 0 end)) as PP.
  cbn beta iota in PP. rewrite HO in PP.
  assert (Q1 : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
  assert (Q2 : 0 <= v < 2 ^ 64) by (clear - Ov1 Ov3; lia).
  assert (Q9 : 140735332487200 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (Q10 : 6914048 <= t <= 140737488355320) by (clear - Tsp Ttop SLO SPT; lia).
  assert (Q11 : PEAEHP.aligned t 8) by exact T8.
  assert (Q12 : 2147446784 + 17592186048512 <= t \/ t + 8 <= 2147446784) by (clear - OTN; unfold nsh in OTN; lia).
  assert (Q13 : L5KA.zeros_at MV ((t / 8) + 2147450880) 1) by exact ZT.
  assert (Q14 : ((sp - 32) + 32 <= t \/ t + 8 <= (sp - 32))) by (left; clear - Tsp; lia).
  assert (Q15 : 6914048 <= v <= 140737488355304) by (clear - Ov1 Ov3; lia).
  assert (Q16 : PEAEHP.aligned v 8) by exact V8.
  assert (Q17 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - OVN; unfold nsh in OVN; lia).
  assert (Q18 : L5KA.zeros_at MV ((v / 8) + 2147450880) 3) by exact ZV.
  assert (Q19 : ((sp - 32) + 32 <= v \/ v + 24 <= (sp - 32))) by (clear - OPS; lia).
  assert (Q20 : (t + 8 <= v \/ v + 24 <= t)) by (right; clear - Ov2 Tsp SLO; lia).
  L5SAR.feed PP ltac:(first [assumption | unfold PEAEHP.aligned; assumption]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & _).
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xb1508 W_b14b8 r F_b14b8 eq_refl D_b14b8 R1ra ltac:(lia) Hr2) as MS2.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb140c R1 r M1v (fun a => sp - 32 <= a < sp - 32 + 32) K HH AM
           ltac:(eapply msteps_trans; [exact MS1| exact MS2]) MG1).
  { intros a Ha Hnw. apply FRZ1; [exact Ha| exact Hnw]. }
  { intros a Ha Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  apply (KONT fx1 R1 M1 model1 LK Aw).
  - apply L5SAR.preserved_by_index. intros k0 Hk. apply KS1. revert Hk. unfold L5SAR.cs_all.
    intros Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]; inl.
  - apply (L5SAR.ahpres_of L ar LB FF sp 14336 _ M M1).
    + intros a (Ha & Hc & Ho). apply FR1; [exact Ha|].
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 14336 a HH SPT Hc) as [Z1|Z1]; lia.
    + apply (L5.defined_grows M M1 _ _ MGM1). exact SDEF.
    + intros a Ha Hc HM. apply MGM1. exact HM.
  - exact MRT1.
  - intros f Hf. exact Hf.
  - intros q Hq. exact Hq.
  - exact AM1.
  - exact HH1.
Qed.

Lemma v_mul_magic24 m : 0 <= m <= 2 ^ 60 -> v_mul (Z_to_bv 64 (24 * m / 8)) (Z_to_bv 64 12297829382473034411) = Z_to_bv 64 m.
Proof.
  intros Hm. unfold v_mul. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (24 * m / 8) with (3 * m) by lia. rewrite (Z.mod_small (3 * m)) by lia. rewrite (Z.mod_small 12297829382473034411) by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (3 * m * 12297829382473034411) with (m + (2 * m) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Theorem estk_dtor_ok : PEAEKAN.ann_shrink_e_spec RSEGS AD L ar HI 0xaeb80 -> PEASKAN.ann_delete_b_spec RSEGS AD L ar HI 0xaeef8 -> PMSPA.opdel_spec RSEGS AD L ar HI ->
  PECDTA.estk_dtor_spec RSEGS AD EE L ar HI 0xb140c.
Proof.
  intros ASH ADL OPD. unfold PECDTA.estk_dtor_spec.
  intros fx R M model K LB FF LK Aw cr t ov fb sp r en HH AM K0 ENT FRM FRS A10 TCELL AOov OV8 EAT Ib BASE KONT.
  destruct TCELL as (T8 & TDEF & TC & Tv & Tsp & Ttop).
  pose proof EAT as (EVT & ESNK & EMAX & KU0 & KU8 & KU16 & EDEPTH & OVD & OVC & HK & HLEN & HDEP & Hc0 & ELIVE & EITEMS).
  change PEC.ESZ with 24 in KU8, KU16, HLEN, ELIVE, EITEMS, KONT, Ib.
  set (eln := Z.of_nat (length (PEC.en_stk en))) in *.
  assert (Hm0 : 0 <= eln) by (subst eln; clear; lia).
  set (v := ov + 24) in *.
  replace (ov + 32) with (v + 8) in KU8 by (subst v; clear; lia). replace (ov + 40) with (v + 16) in KU16 by (subst v; clear; lia).
  assert (AOv : PMSPA.aobjA FF v 24) by (apply (aobjA_sub FF ov 56 v 24 AOov); subst v; clear; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (V8 : v mod 8 = 0) by (subst v; clear - OV8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VD : L5.defined M v 24) by (apply (L5.defined_sub M ov 56 v 24 OVD); subst v; clear; lia).
  assert (VC : PMSPA.accA M v 24) by (intros x Hx; apply OVC; subst v; clear - Hx; lia).
  destruct (Z.eq_dec (PEC.en_k en) 0) as [C0|C0].
  {
    pose proof (Hc0 C0) as B0. unfold PECDTA.estk_rest in KONT. rewrite (proj2 (Z.eqb_eq _ _) C0) in KONT. rewrite B0 in KU0.
    replace (ov + 24 + 24) with (v + 24) in KONT by (subst v; clear; lia).
    apply (estk_dtor_null fx R M model K LB FF LK Aw cr t v sp r HH AM K0 ENT FRM FRS A10 Tsp Ttop T8 TC Tv AOv V8 VD VC KU0 KONT). }

  unfold PECDTA.estk_rest in KONT. rewrite (proj2 (Z.eqb_neq _ _) C0) in KONT.
  assert (Ibc : In (PEC.en_b en, 24 * PEC.ecap (PEC.en_k en)) LB) by (apply Ib; unfold PEC.enc_own; rewrite (proj2 (Z.eqb_neq _ _) C0); left; reflexivity). clear Ib. rename Ibc into Ib.
  destruct (ELIVE ltac:(clear - C0 HK; lia)) as (B8 & DB & BR & CB & AN).
  pose proof BR as (B4096 & _ & Hal & Cpos & _ & _).
  replace (ov + 24 + 24) with (v + 24) in KONT by (subst v; clear; lia).
  set (b := PEC.en_b en) in *. set (c := 24 * PEC.ecap (PEC.en_k en)) in *. set (n := 24 * eln) in *.
  assert (En : n = 24 * eln) by reflexivity.
  assert (C27 : 1 <= c) by (clear - Cpos; lia). assert (NC : 0 <= n <= c) by (clear - HLEN Hm0 En; subst n c; lia).
  assert (Hm : 0 <= eln <= 2 ^ 43).
  { split; [exact Hm0|]. apply (Z.le_trans _ _ _ HLEN). unfold PEC.ecap. rewrite (proj2 (Z.eqb_neq _ _) C0).
    apply (Z.le_trans _ (2 ^ 11)); [apply Z.pow_le_mono_r; clear - HK; lia| clear; lia]. }
  pose proof KU0 as W0. pose proof KU8 as W8. pose proof KU16 as W16.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in *. change (14336 / 8) with 1792 in STKSH.
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & ND & _).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). clear - X1 X2 FSAPP. unfold app_mem, FS_BYTES in *. lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (OtVIS : L5A.avis H t 8) by (apply VIS; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model v 24 sp 14336 HH (PMKA.aobj_of_aobjA FF v 24 AOv V8) ltac:(lia) ltac:(reflexivity))
    as ((Ov1 & Ov2 & Ov3 & Ov4 & Ov5) & OvBIG & OvDEF & OvVIS & OvSHV & OvCL & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (HO : bv_unsigned (getr R (reg 10)) = t) by (rewrite A10; apply L5.unsigned_lit; lia).
  pose proof (WB _ Ib) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _ & _ & _ & _ & FAb & _). cbn [fst snd] in Bb0, Bb1, Bb2, Bb3, Bb4, Bb5, FAb.
  assert (Bb47 : b + c <= 2 ^ 47) by (unfold app_mem in Bb5; destruct Bb5 as (_ & _ & X); exact X).
  assert (BBN : nsh b (c)) by (destruct Bb5 as (_ & X & _); unfold nsh; unfold BIGSHADOW_LO, BIGSHADOW_HI in X; destruct X; [left|right]; lia).
  assert (OTN : nsh t 8) by (unfold nsh; right; clear - Tsp SLO SPT; lia).
  assert (OVN : nsh v 24) by (unfold nsh; destruct OvBIG as [X|X]; [right| left]; lia).
  clear OvBIG Bb1 Bb5 FSAPP.
  assert (OPS : v + 24 + 4096 + 14336 <= sp) by (clear - Ov2 SLO; lia).
  set (LBX := lb_remove b LB).

  assert (ZT : L5KA.zeros_at MV (t / 8 + SB) (8 / 8)) by exact (stk_shz_vis H M t VSTSH TC T8 ltac:(lia) Ttop).
  assert (ZV : L5KA.zeros_at MV (v / 8 + SB) (24 / 8)) by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model v 24 HH AOv V8 ltac:(lia) ltac:(reflexivity) VC).
  change (8 / 8) with 1 in ZT. change (24 / 8) with 3 in ZV.
  assert (VSW : L5.writable RSEGS MV (sp - 32) 32).
  { apply (proj2 (L5A.writable_vis H M (sp - 32) 32 (VIS (sp - 32) 32 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]| lia| lia]. }
  assert (IC0 : L5.img_clear MV 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1317368 2147450880 (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (Tvv : L5.u64_at RSEGS MV t v) by (apply (proj2 (L5A.u64_at_vis H M t v OtVIS ltac:(lia) ltac:(lia))); exact Tv).
  assert (W0v : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b (L5A.avis_sub H v 24 v 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact W0).
  assert (W8v : L5.u64_at RSEGS MV (v + 8) (b + n))
    by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ (L5A.avis_sub H v 24 (v + 8) 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact W8).
  assert (WV8 : L5.writable RSEGS MV (v + 8) 8).
  { apply (proj2 (L5A.writable_vis H M (v + 8) 8 (L5A.avis_sub H v 24 (v + 8) 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M v 24); [exact VD| lia| lia]| lia| lia]. }

  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (IC065 & _ & _).
  pose proof (PEAEHP.hkeA1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => b | 36%nat => b + n | _ => 0 end)) as PP.
  cbn beta iota in PP. rewrite HO in PP.
  assert (Q1 : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
  assert (Q2 : 0 <= v < 2 ^ 64) by (clear - Ov1 Ov3; lia).
  assert (Q3 : 0 <= b < 2 ^ 64) by (clear - Bb0 Bb47 C27; lia).
  assert (Q4 : 0 <= b + n < 2 ^ 64) by (clear - Bb0 Bb47 NC C27; lia).
  assert (Q9 : 140735332487200 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (Q10 : 6914048 <= t <= 140737488355320) by (clear - Tsp Ttop SLO SPT; lia).
  assert (Q11 : PEAEHP.aligned t 8) by exact T8.
  assert (Q12 : 2147446784 + 17592186048512 <= t \/ t + 8 <= 2147446784) by (clear - OTN; unfold nsh in OTN; lia).
  assert (Q13 : L5KA.zeros_at MV ((t / 8) + 2147450880) 1) by exact ZT.
  assert (Q14 : ((sp - 32) + 32 <= t \/ t + 8 <= (sp - 32))) by (left; clear - Tsp; lia).
  assert (Q15 : 6914048 <= v <= 140737488355304) by (clear - Ov1 Ov3; lia).
  assert (Q16 : PEAEHP.aligned v 8) by exact V8.
  assert (Q17 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - OVN; unfold nsh in OVN; lia).
  assert (Q18 : L5KA.zeros_at MV ((v / 8) + 2147450880) 3) by exact ZV.
  assert (Q19 : ((sp - 32) + 32 <= v \/ v + 24 <= (sp - 32))) by (clear - OPS; lia).
  assert (Q20 : (t + 8 <= v \/ v + 24 <= t)) by (right; clear - Ov2 Tsp SLO; lia).
  assert (Q21 : 4096 <= b <= 140737488355327) by (clear - Bb0 Bb47 C27; lia).
  assert (Q22 : PEAEHP.aligned b 16) by exact Hal.
  assert (Q23 : 0 <= (b + n) - b <= 140737488355328) by (clear - NC Bb47 Bb0; lia).
  L5SAR.feed PP ltac:(first [assumption | unfold PEAEHP.aligned; assumption]).
  destruct PP as (fx1 & R1 & M1a & MGa & _ & FRZa & MSa & KSa & Aa2 & Aa8 & Aa9 & Aa10 & Aa11 & Aa12 & Aa13 & Aa18 & C32 & C24 & C16 & C8s).

  pose proof (PMARS1.srai_to fx1 R1 M1a 0xb1480 W_b1430 _ _ _ F_b1430 eq_refl D_b1430 eq_refl ltac:(lia) ltac:(lia)) as MSR.
  set (R1t := regupd R1 11%bv (v_srai (getr R1 11%bv) (bv_unsigned (3%bv : bv 6)))) in MSR.
  assert (R11 : (11%bv : bv 5) <> 0%bv) by (intros X; discriminate X).
  assert (E11 : getr R1 11%bv = Z_to_bv 64 (24 * eln)) by (rewrite L5K.rl11, Aa11; f_equal; clear - En; lia).
  assert (T11t : getr R1t (reg 11) = Z_to_bv 64 (24 * eln / 8)).
  { unfold R1t. rewrite <- L5K.rl11. rewrite (getr_same R1 11%bv _ R11). rewrite E11. change (bv_unsigned (3%bv : bv 6)) with 3.
    rewrite PNAEK.v_srai3_small by (clear - Hm; lia). reflexivity. }
  assert (TOt : forall j, j <> 11%nat -> (j < 32)%nat -> getr R1t (reg j) = getr R1 (reg j)).
  { intros j Hj Hl. unfold R1t. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
    rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (11%bv : bv 5)) with 11 in E.
    rewrite Z.mod_small in E by lia. lia. }
  pose proof (PNAEK.mul_to fx1 R1t M1a 0xb1484 W_b1434 _ _ _ F_b1434 eq_refl D_b1434 eq_refl ltac:(lia) ltac:(lia)) as MSM.
  set (R1m := regupd R1t 11%bv (v_mul (getr R1t 11%bv) (getr R1t 13%bv))) in MSM.
  assert (T11 : getr R1m (reg 11) = Z_to_bv 64 eln).
  { unfold R1m. rewrite <- L5K.rl11. rewrite (getr_same R1t 11%bv _ R11). rewrite L5K.rl11, T11t. rewrite L5K.rl13, (TOt 13%nat) by lia. rewrite Aa13.
    apply v_mul_magic24. clear - Hm; lia. }
  assert (TOm : forall j, j <> 11%nat -> (j < 32)%nat -> getr R1m (reg j) = getr R1 (reg j)).
  { intros j Hj Hl. unfold R1m. rewrite getr_other; [apply TOt; [exact Hj| exact Hl]|]. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
    rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (11%bv : bv 5)) with 11 in E.
    rewrite Z.mod_small in E by lia. lia. }

  pose proof (PEAEHP.hkeA2_conc fx1 R1m M1a (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => b | 35%nat => eln | _ => 0 end)) as PP. cbn beta iota in PP.
  assert (Ua2 : getr R1m (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (TOm 2%nat) by lia; exact Aa2).
  assert (Ua10 : getr R1m (reg 10) = Z_to_bv 64 v) by (rewrite (TOm 10%nat) by lia; exact Aa10).
  assert (Ua12 : getr R1m (reg 12) = Z_to_bv 64 b) by (rewrite (TOm 12%nat) by lia; exact Aa12).
  assert (Um : 0 <= eln < 2 ^ 64) by (clear - Hm; lia).
  assert (UW : L5.writable RSEGS M1a (sp - 32) 32) by exact (L5.writable_grows RSEGS MV M1a (sp - 32) 32 MGa VSW).
  assert (UZV : L5KA.zeros_at M1a ((v / 8) + 2147450880) 3).
  { intros j Hj. unfold L5KA.zeros_at in ZV. rewrite <- (ZV j Hj). unfold byte_at. rewrite FRZa; [reflexivity| |].
    - pose proof (PNAEK.S_range v ltac:(clear - Ov1 Ov3; lia)) as SR. unfold S, SB in SR. clear - SR Hj. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - pose proof (PNAEK.S_range v ltac:(clear - Ov1 Ov3; lia)) as SR. unfold S, SB in SR. clear - SR Hj Q9. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (UV0 : L5.u64_at RSEGS M1a v b).
  { apply (L5C.u64_at_agree RSEGS MV M1a v b); [| clear - Q15; lia| clear - Q15; lia| exact W0v]. intros i Hi. apply FRZa; [clear - Hi Q15; lia| clear - Hi Q19; lia]. }
  assert (UW8 : L5.writable RSEGS M1a (v + 8) 8) by exact (L5.writable_grows RSEGS MV M1a (v + 8) 8 MGa WV8).
  L5SAR.feed PP ltac:(first [assumption | unfold PEAEHP.aligned; assumption]).
  destruct PP as (fx2 & R2 & M1v & MGb & FRZbw & FRZb & MS2 & KS2b & A2ra & C8). clear Q3 Q4 Q12 Q13 Q17 Q18 Q21 Q22 Q23.
  pose proof (mem_grows_trans MV M1a M1v MGa MGb) as MG1.
  assert (FRZ1 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (v + 8 <= i < v + 8 + 8) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi N1 N2. rewrite (FRZb i Hi N2). exact (FRZa i Hi N1). }
  assert (KS2 : forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x)).
  { intros x Hx. rewrite (KS2b x) by (revert Hx; clear; intros Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx).
    rewrite (TOm x) by (revert Hx; clear; intros Hx; repeat (destruct Hx as [<-|Hx]; [lia|]); destruct Hx).
    apply KSa. revert Hx; clear; intros Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx. }
  assert (A12 : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (KS2b 2%nat) by inl; exact Ua2).
  assert (A18 : getr R2 (reg 8) = getr R (reg 10)) by (rewrite (KS2b 8%nat) by inl; rewrite (TOm 8%nat) by lia; exact Aa8).
  assert (A19 : getr R2 (reg 9) = Z_to_bv 64 2147450880) by (rewrite (KS2b 9%nat) by inl; rewrite (TOm 9%nat) by lia; exact Aa9).
  assert (A110 : getr R2 (reg 10) = Z_to_bv 64 v) by (rewrite (KS2b 10%nat) by inl; exact Ua10).
  assert (A111 : getr R2 (reg 11) = Z_to_bv 64 eln) by (rewrite (KS2b 11%nat) by inl; exact T11).
  assert (A118 : getr R2 (reg 18) = Z_to_bv 64 ((t / 8) + 2147450880)) by (rewrite (KS2b 18%nat) by inl; rewrite (TOm 18%nat) by lia; exact Aa18).
  assert (CSV : forall a w, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1a a w -> L5.u64_at RSEGS M1v a w).
  { intros a w Ha Ha' X. apply (L5C.u64_at_agree RSEGS M1a M1v a w); [| clear - Ha Q9; lia| clear - Ha' Q9; lia| exact X]. intros i Hi. apply FRZb; [clear - Hi Ha Ha' Q9; lia| clear - Hi Ha Ha' OPS; lia]. }
  apply (CSV (sp - 32) _ ltac:(lia) ltac:(lia)) in C32. apply (CSV (sp - 24) _ ltac:(lia) ltac:(lia)) in C24.
  apply (CSV (sp - 16) _ ltac:(lia) ltac:(lia)) in C16. apply (CSV (sp - 8) _ ltac:(lia) ltac:(lia)) in C8s.
  pose proof A111 as T11'.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx2 R 0xb140c R2 0xaeb80 M1v
           (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (v + 8 <= a < v + 8 + 8)) K HH AM
           ltac:(eapply msteps_trans; [exact MSa| eapply msteps_trans; [exact MSR| eapply msteps_trans; [exact MSM| exact MS2]]]) MG1).
  { intros a Ha Hnw. apply FRZ1; [exact Ha| intros X; apply Hnw; left; exact X| intros X; apply Hnw; right; exact X]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|X]; unfold aclientw, aclient_g.
      + right; left. split; [lia| intros Y; lia].
      + do 3 right; left. destruct AOv as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. split; [lia| intros Y; lia].
    - destruct Wa as [X|X]; lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.

  set (P1 := fun a => (sp - 32 <= a < sp - 32 + 32) \/ (v + 8 <= a < v + 8 + 8)) in FR1.
  assert (P1sh : forall x, BIGSHADOW_LO <= x < BIGSHADOW_HI -> ~ P1 x).
  { intros x Hx [Y|Y]; [clear - Hx Y SLO SPT; unfold BIGSHADOW_LO, BIGSHADOW_HI in Hx; lia| exact (nsh_not v 24 x OVN ltac:(lia) Hx)]. }
  assert (SHM1 : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> PMFA.agsh M M1 a m).
  { intros a m Ha Hn x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. apply FR1; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| apply P1sh; exact SX]. }
  assert (SZk : forall lo g, lo mod 8 = 0 -> 0 <= lo -> lo + 8 * g <= 2 ^ 47 -> 0 <= g -> shadow_zero M lo g -> shadow_zero M1 lo g).
  { intros lo g Hlo H0 H1 Hg SZ j Hj. pose proof (SZ j Hj) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule lo j Hlo ltac:(lia)) in *.
    pose proof (PMKA.S_in_shadow (lo + 8 * j) ltac:(lia)) as SX. rewrite FR1; [exact Z1| unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| apply P1sh; exact SX]. }
  assert (SP16 : forall j, (sp - 16 * j) mod 8 = 0) by (intros j; apply PMKA.mod16_8'; replace (sp - 16 * j) with (sp + (- j) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
  assert (SZ1 : shadow_zero M1 (sp - 12320) 1536).
  { apply SZk; [replace (sp - 12320) with (sp - 16 * 770) by lia; apply SP16| lia| lia| lia|].
    apply (PMKA.shadow_zero_sub M (sp - 14336) 1792); [replace (sp - 14336) with (sp - 16 * 896) by lia; apply SP16| replace (sp - 12320) with (sp - 16 * 770) by lia; apply SP16| lia| lia| lia| exact STKSH]. }
  assert (ASTK1 : L5CA.astk ar M1 sp 14336) by exact (L5SAR.astk_grows ar M M1 sp 14336 ASTK MGM1).
  assert (ASTK1c : L5CA.astk ar M1 (sp - 32) 12288).
  { apply (L5SAR.astk_sub ar M M1 sp 14336 32 12288 ASTK MGM1); [lia|lia|lia|]. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof (ri_front _ _ _ _ _ _ _ _ _ HH1 Ib) as HH1s. change (ri_inv HI ([(b, c)] ++ LBX) FF LK cr Aw M1 (vml_of model1)) in HH1s.

  unfold PEAEKAN.ann_shrink_e_spec in ASH.
  apply (ASH fx2 R2 M1 model1 K LBX FF LK Aw cr v eln b 0 c (sp - 32) 726160 HH1s AM1 K0).
  { split; [rewrite L5K.rl1; exact A2ra|]. split; [split; [lia| reflexivity]|].
    split; [rewrite L5K.rl2; exact A12|].
    split; [rewrite L5K.rl3, (KS2 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS2 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK1c|]. change (12288 / 8) with 1536. replace (sp - 32 - 12288) with (sp - 12320) by lia. exact SZ1. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact A110. }
  { rewrite L5K.rl11. exact T11'. }
  { exact AOv. }
  { exact V8. }
  { apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact VC]. }
  {
    split. { intros i Hi. apply MGM1. apply VD. exact Hi. }
    split. { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [lia| intros [Y|Y]; lia]| lia| lia| exact W0]. }
    split. { replace (b + 0) with b by lia.
             apply (proj1 (L5A.u64_at_vis H M1 (v + 8) b (L5A.avis_sub H v 24 (v + 8) 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact C8. }
    split. { apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [lia| intros [Y|Y]; lia]| lia| lia| exact W16]. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal|].
    intros i Hi. apply MGM1. apply DB. exact Hi. }
  { clear - NC En; lia. }
  { rewrite <- En. split.
    - apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact CB].
    - apply (PNAEK.ann_agree M M1 b n c); [| lia| lia| exact AN]. intros j Hj. rewrite (PNAEK.S_add8 b j).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply (SHM1 b (8 * ((c + 7) / 8))); clear - Bb0 Bb47 Hal Hj C27; Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  intros fx3 R3 M3 model3 LK3 Aw3 RP3 VEC3 KEPT3 HP3 MRT3 INCLK3 INCAw3 AM3 HH3.
  assert (ACC3 : PMSPA.accA M3 v 24) by (destruct VEC3 as (_ & X & _); exact X).
  change (PMSPA.pm_scr 0) with 12288 in HP3.

  set (Wv8 := [(v + 8, 8)]).
  assert (WAPP8 : PMKA.wapp Wv8).
  { unfold Wv8. apply PMKA.wapp_cons; [|apply PMKA.wapp_nil]. cbn [fst snd]. unfold nsh in OVN. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct OVN; [left|right]; lia. }
  assert (FRBX : forall x, In x LBX -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. destruct (proj1 (WB x (L5C.in_lb_remove b x LB Hx))) as (X0 & _ & _ & _ & _ & X5). clear - X0 X5. unfold app_mem in X5. lia. }
  assert (EK01 : L5SAR.ek L ar LBX FF sp 14336 Wv8 M M1).
  { apply (L5SAR.ek_piece L ar LBX FF sp 14336 Wv8 M M1 P1 FR1). intros a Ha Hc Ho [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M1 _ sp 14336 a HH1s SPT (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 14336 a Hc))
        as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
    - apply (Ho (v + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (EK13 : L5SAR.ek L ar LBX FF sp 14336 Wv8 M1 M3).
  { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 14336 (sp - 32) 12288 Wv8 [] M1 M3 HP3); [lia| lia| intros a _ _ r0 []]. }
  pose proof (L5SAR.ek_trans L ar LBX FF sp 14336 Wv8 M M1 M3 EK01 EK13) as EK03.
  assert (ASTK3 : L5CA.astk ar M3 sp 14336) by (apply (PMKA.astk_after_ahpres L ar LBX FF M1 M3 sp 14336 (sp - 32) 12288 [] ASTK1 HP3); lia).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK3 cr Aw3 M3 model3 HH3) as (_ & VIS3 & _ & _ & _ & _ & _ & VSTSH3).
  set (H3 := ahid Aw3 model3) in *. set (MV3 := mrestrict H3 M3) in *.
  assert (OtVIS3 : L5A.avis H3 t 8) by (apply VIS3; lia).
  assert (TC3 : PMSPA.accA M3 t 8) by exact (PMFA.accA_agree M M3 t 8 (stk_sh_keep LBX FF sp 14336 Wv8 M M3 t 8 EK03 WAPP8 ltac:(lia) ltac:(lia)) TC).
  assert (G2 : getr R3 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (L5SAR.cs_of_preserved R2 R3 2 RP3) by inl; exact A12).
  assert (G8 : getr R3 (reg 8) = Z_to_bv 64 t) by (rewrite (L5SAR.cs_of_preserved R2 R3 8 RP3) by inl; rewrite A18; exact A10).
  assert (G9 : getr R3 (reg 9) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R2 R3 9 RP3) by inl; exact A19).
  assert (G18 : getr R3 (reg 18) = Z_to_bv 64 ((t / 8) + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R2 R3 18 RP3) by inl; exact A118).
  assert (W3 : L5.writable RSEGS MV3 (sp - 32) 32).
  { pose proof ASTK3 as (_ & _ & _ & _ & SDEF3 & _).
    apply (proj2 (L5A.writable_vis H3 M3 (sp - 32) 32 (VIS3 (sp - 32) 32 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M3 (sp - 14336) 14336); [exact SDEF3| lia| lia]| lia| lia]. }
  assert (ZT3 : L5KA.zeros_at MV3 ((t / 8) + 2147450880) 1)
    by exact (stk_shz_vis H3 M3 t VSTSH3 TC3 T8 ltac:(lia) Ttop).
  assert (Tv3 : L5.u64_at RSEGS MV3 t v).
  { apply (proj2 (L5A.u64_at_vis H3 M3 t v OtVIS3 ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M3); [| lia| lia| exact Tv].
    apply (stk_keep LBX FF sp 14336 Wv8 M M3 t 8 EK03); [lia| lia| lia|]. intros i Hi r0 [<-|[]]. unfold L5.in_rng; cbn [fst snd]. lia. }

  pose proof (PEAEHP.hkeC_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => v | 40%nat => t | _ => 0 end)) as PP. cbn beta iota in PP.
  assert (U0 : 0 <= t < 2 ^ 64) by (clear - Q10; lia).
  assert (Q12 : 2147446784 + 17592186048512 <= t \/ t + 8 <= 2147446784) by (clear - OTN; unfold nsh in OTN; lia).
  L5SAR.feed PP ltac:(first [assumption | unfold PEAEHP.aligned; assumption]). clear Q12.
  destruct PP as (fx4 & R4 & M4v & MG4 & FR4w & FRZ4 & MS4 & KS4 & A4ra & A4a0).
  assert (E4 : M4v = MV3) by (apply functional_extensionality; exact FR4w). subst M4v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK3 cr Aw3 M3 model3 fx3 fx4 R3 726160 R4 0xaeef8 MV3 K HH3 AM3 MS4 MG4 FRZ4).
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4.
  assert (E34 : M4 = M3) by exact (L5SAR.mem_eq_of_agree M3 M4 FR4). subst M4.
  assert (ASTK4 : L5CA.astk ar M3 sp 14336) by exact ASTK3.
  assert (SZ3 : shadow_zero M3 (sp - 12320) 1536).
  { apply (PMKA.stksh_keepA L ar LBX FF sp 14336 Wv8 M1 M3 EK13 WAPP8 (sp - 12320) 1536); [lia|lia|lia| replace (sp - 12320) with (sp - 16 * 770) by lia; apply SP16| lia| exact SZ1]. }

  unfold PEASKAN.ann_delete_b_spec in ADL.
  apply (ADL fx4 R4 M3 model4 K LBX FF LK3 Aw3 cr v b 0 c (sp - 32) 726176 HH4 AM4 K0).
  { split; [rewrite L5K.rl1; exact A4ra|]. split; [split; [lia| reflexivity]|].
    split; [rewrite L5K.rl2, (KS4 2%nat) by inl; exact G2|].
    split; [rewrite L5K.rl3, (KS4 3%nat) by inl; rewrite (L5SAR.cs_of_preserved R2 R3 3 RP3) by inl; rewrite (KS2 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS4 4%nat) by inl; rewrite (L5SAR.cs_of_preserved R2 R3 4 RP3) by inl; rewrite (KS2 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split.
    { apply (L5SAR.astk_sub ar M3 M3 sp 14336 32 12288 ASTK3 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    change (12288 / 8) with 1536. replace (sp - 32 - 12288) with (sp - 12320) by lia. exact SZ3. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact A4a0. }
  { exact AOv. }
  { exact V8. }
  { exact ACC3. }
  { exact VEC3. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 HDR5 C5 CB5 EL5 HP5 MRT5 INCLK5 INCAw5 AM5 HH5.
  change (PMSPA.pm_scr 0) with 12288 in HP5.
  assert (EK35 : L5SAR.ek L ar LBX FF sp 14336 Wv8 M3 M5).
  { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 14336 (sp - 32) 12288 Wv8 [] M3 M5 HP5); [lia| lia| intros a _ _ r0 []]. }
  pose proof (L5SAR.ek_trans L ar LBX FF sp 14336 Wv8 M M3 M5 EK03 EK35) as EK05.
  assert (ASTK5 : L5CA.astk ar M5 sp 14336) by (apply (PMKA.astk_after_ahpres L ar LBX FF M3 M5 sp 14336 (sp - 32) 12288 [] ASTK3 HP5); lia).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK5 cr Aw5 M5 model5 HH5) as (_ & VIS5 & _ & _ & _ & _ & _ & VSTSH5).
  set (H5 := ahid Aw5 model5) in *. set (MV5 := mrestrict H5 M5) in *.
  assert (OtVIS5 : L5A.avis H5 t 8) by (apply VIS5; lia).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK5 cr Aw5 M5 model5 v 24 sp 14336 HH5 (PMKA.aobj_of_aobjA FF v 24 AOv V8) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & _ & OvVIS5 & _ & _ & _).
  assert (TC5 : PMSPA.accA M5 t 8) by exact (PMFA.accA_agree M M5 t 8 (stk_sh_keep LBX FF sp 14336 Wv8 M M5 t 8 EK05 WAPP8 ltac:(lia) ltac:(lia)) TC).
  assert (VC5 : PMSPA.accA M5 v 24) by exact (PMKA.acc_keepA' L ar LBX FF sp 14336 Wv8 M M5 EK05 WAPP8 FRB v 24 AOv VC).
  assert (H2 : getr R5 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (L5SAR.cs_of_preserved R4 R5 2 RP5) by inl; rewrite (KS4 2%nat) by inl; exact G2).
  assert (H8 : getr R5 (reg 8) = Z_to_bv 64 t) by (rewrite (L5SAR.cs_of_preserved R4 R5 8 RP5) by inl; rewrite (KS4 8%nat) by inl; exact G8).
  assert (H9 : getr R5 (reg 9) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R4 R5 9 RP5) by inl; rewrite (KS4 9%nat) by inl; exact G9).
  assert (H18 : getr R5 (reg 18) = Z_to_bv 64 ((t / 8) + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R4 R5 18 RP5) by inl; rewrite (KS4 18%nat) by inl; exact G18).
  assert (W5 : L5.writable RSEGS MV5 (sp - 32) 32).
  { pose proof ASTK5 as (_ & _ & _ & _ & SDEF5 & _).
    apply (proj2 (L5A.writable_vis H5 M5 (sp - 32) 32 (VIS5 (sp - 32) 32 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M5 (sp - 14336) 14336); [exact SDEF5| lia| lia]| lia| lia]. }
  assert (ZT5 : L5KA.zeros_at MV5 ((t / 8) + 2147450880) 1)
    by exact (stk_shz_vis H5 M5 t VSTSH5 TC5 T8 ltac:(lia) Ttop).
  assert (ZV5 : L5KA.zeros_at MV5 ((v / 8) + 2147450880) 3)
    by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK5 cr Aw5 M5 model5 v 24 HH5 AOv V8 ltac:(lia) ltac:(reflexivity) VC5).
  assert (OUT8 : forall a m, (a + m <= v + 8 \/ v + 16 <= a) -> forall i, a <= i < a + m -> L5.outside Wv8 i).
  { intros a m Ha i Hi r0 [<-|[]]. unfold L5.in_rng; cbn [fst snd]. lia. }
  assert (Tv5 : L5.u64_at RSEGS MV5 t v).
  { apply (proj2 (L5A.u64_at_vis H5 M5 t v OtVIS5 ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M5); [| lia| lia| exact Tv].
    apply (stk_keep LBX FF sp 14336 Wv8 M M5 t 8 EK05); [lia| lia| lia| apply OUT8; lia]. }
  assert (W0v5 : L5.u64_at RSEGS MV5 v b).
  { apply (proj2 (L5A.u64_at_vis H5 M5 v b (L5A.avis_sub H5 v 24 v 8 OvVIS5 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (PMKA.u64_keepA RSEGS L ar LBX FF sp 14336 Wv8 M M5 EK05 WAPP8 FRB v b (aobjA_sub FF v 24 v 8 AOv ltac:(lia) ltac:(lia))); [apply OUT8; lia| exact W0]. }
  assert (W16v5 : L5.u64_at RSEGS MV5 (v + 16) (b + c)).
  { apply (proj2 (L5A.u64_at_vis H5 M5 (v + 16) _ (L5A.avis_sub H5 v 24 (v + 16) 8 OvVIS5 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (PMKA.u64_keepA RSEGS L ar LBX FF sp 14336 Wv8 M M5 EK05 WAPP8 FRB (v + 16) _ (aobjA_sub FF v 24 (v + 16) 8 AOv ltac:(lia) ltac:(lia))); [apply OUT8; lia| exact W16]. }

  assert (FRAME15 : forall a, sp - 32 <= a < sp -> M5 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP5 as (P5 & _). destruct HP3 as (P3 & _).
    assert (CLa : forall LBz FFz, aclient L ar LBz FFz (sp - 32) 12288 a) by (intros LBz FFz; unfold aclient, aclient_g; right; left; split; [lia| intros X; lia]).
    rewrite P5; [| split; [lia|]; split; [apply CLa| intros r0 []]]. apply P3. split; [lia|]. split; [apply CLa| intros r0 []]. }
  assert (SVV : forall j w, 1 <= j <= 4 -> L5.u64_at RSEGS M1v (sp - 8 * j) w -> L5.u64_at RSEGS MV5 (sp - 8 * j) w).
  { intros j w Hj SV. apply (proj2 (L5A.u64_at_vis H5 M5 (sp - 8 * j) w (VIS5 (sp - 8 * j) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    rewrite <- VIS1 in SV. apply (proj1 (L5A.u64_at_vis H M1 (sp - 8 * j) w (VIS (sp - 8 * j) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) in SV.
    apply (L5C.u64_at_agree RSEGS M1 M5); [intros i Hi; apply FRAME15; lia| lia| lia| exact SV]. }
  assert (Y8 : L5.u64_at RSEGS MV5 (sp - 8) (bv_unsigned (getr R (reg 1)))) by (replace (sp - 8) with (sp - 8 * 1) by lia; apply SVV; [lia| exact C8s]).
  assert (Y16 : L5.u64_at RSEGS MV5 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (replace (sp - 16) with (sp - 8 * 2) by lia; apply SVV; [lia| exact C16]).
  assert (Y24 : L5.u64_at RSEGS MV5 (sp - 24) (bv_unsigned (getr R (reg 9)))) by (replace (sp - 24) with (sp - 8 * 3) by lia; apply SVV; [lia| exact C24]).
  assert (Y32 : L5.u64_at RSEGS MV5 (sp - 32) (bv_unsigned (getr R (reg 18)))) by (replace (sp - 32) with (sp - 8 * 4) by lia; apply SVV; [lia| exact C32]).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as Hs1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as Hs18.
  change (bv_modulus 64) with (2 ^ 64) in Hs1, Hs8, Hs9, Hs18.

  pose proof (PEAEHP.hkeD_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => b | 35%nat => b + c
                                              | 38%nat => bv_unsigned (getr R (reg 1)) | 39%nat => bv_unsigned (getr R (reg 8)) | 40%nat => t
                                              | 41%nat => bv_unsigned (getr R (reg 9)) | 42%nat => bv_unsigned (getr R (reg 18)) | _ => 0 end)) as PP. cbn beta iota in PP.
  assert (Q3 : 0 <= b < 2 ^ 64) by (clear - Bb0 Bb47 C27; lia).
  assert (Q3b : 0 <= b + c < 2 ^ 64) by (clear - Bb0 Bb47 C27; lia).
  assert (Q12 : 2147446784 + 17592186048512 <= t \/ t + 8 <= 2147446784) by (clear - OTN; unfold nsh in OTN; lia).
  assert (Q17 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - OVN; unfold nsh in OVN; lia).
  L5SAR.feed PP ltac:(first [assumption | unfold PEAEHP.aligned; assumption]). clear Q12 Q17 Q14 Q19 Q20.
  destruct PP as (fx6 & R6 & M6v & MG6 & FR6w & FRZ6 & MS6 & KS6 & A61 & A62 & A68 & A69 & A610 & A611 & A612 & A618).
  assert (E6 : M6v = MV5) by (apply functional_extensionality; exact FR6w). subst M6v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK5 cr Aw5 M5 model5 fx5 fx6 R5 726176 R6 0xd4a60 MV5 K HH5 AM5 MS6 MG6 FRZ6).
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6.
  assert (E56 : M6 = M5) by exact (L5SAR.mem_eq_of_agree M5 M6 FR6). subst M6.

  unfold PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PeCLayoutA.CADDR_A] in OPD.
  assert (R6ra : getr R6 (reg 1) = Z_to_bv 64 r) by (rewrite A61, Z_to_bv_bv_unsigned; exact Rra).
  apply (OPD fx6 R6 M5 model6 K ([(b, c)] ++ LBX) FF LK5 Aw5 cr b c sp r HH6 AM6 K0 (or_introl eq_refl)).
  { rewrite L5K.rl10. exact A610. }
  { rewrite L5K.rl1. exact R6ra. }
  { exact RAok. }
  { rewrite L5K.rl2. exact A62. }
  { rewrite L5K.rl4, (KS6 4%nat) by inl. rewrite (L5SAR.cs_of_preserved R4 R5 4 RP5) by inl. rewrite (KS4 4%nat) by inl.
    rewrite (L5SAR.cs_of_preserved R2 R3 4 RP3) by inl. rewrite (KS2 4%nat) by inl. exact Rtp. }
  { pose proof (L5SAR.astk_sub ar M5 M5 sp 14336 0 PMSPA.OPDEL_SCR ASTK5 (fun _ X => X)) as X. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in *.
    replace (sp - 0) with sp in X by lia. apply X; [lia| lia| lia| replace (sp - 0) with sp by lia; exact A16]. }
  intros fx7 R7 M7 model7 Aw7 RP7 HP7 MRT7 INCAw7 AM7 HH7.
  cbn [app lb_remove fst] in HH7, HP7. rewrite Z.eqb_refl in HH7, HP7.
  unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HP7.
  apply (KONT fx7 R7 M7 model7 LK5 Aw7).
  - apply (L5SAR.regs_preserved_trans R R6 R7); [| exact RP7].
    apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj];
      [ first [ rewrite A62; exact (eq_sym Rsp)
              | rewrite A68; apply Z_to_bv_bv_unsigned | rewrite A69; apply Z_to_bv_bv_unsigned | rewrite A618; apply Z_to_bv_bv_unsigned
              | rewrite (KS6 _) by inl; rewrite (L5SAR.cs_of_preserved R4 R5 _ RP5) by inl; rewrite (KS4 _) by inl;
                rewrite (L5SAR.cs_of_preserved R2 R3 _ RP3) by inl; rewrite (KS2 _) by inl; reflexivity ] |]).
    destruct Hj.
  - change (PMSPA.pm_scr 1) with 14336.
    assert (EK57 : L5SAR.ek L ar LBX FF sp 14336 Wv8 M5 M7).
    { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 14336 sp 4096 Wv8 [] M5 M7 HP7); [lia| lia| intros a _ _ r0 []]. }
    apply (L5SAR.ahpres_of L ar LBX FF sp 14336 [(v, 24)] M M7).
    + apply (L5SAR.ek_W L ar LBX FF sp 14336 [(v, 24)] Wv8 M M7 (L5SAR.ek_trans L ar LBX FF sp 14336 Wv8 M M5 M7 EK05 EK57)).
      intros a O r0 [<-|[]] X. apply (O (v, 24)); [left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia].
    + pose proof (PMKA.astk_after_ahpres L ar LBX FF M5 M7 sp 14336 sp 4096 [] ASTK5 HP7 ltac:(lia) ltac:(lia) ltac:(lia) STOP) as (_ & _ & _ & _ & D7 & _). exact D7.
    + apply (L5SAR.dk_trans L ar LBX FF sp 14336 M M5 M7).
      * apply (L5SAR.dk_trans L ar LBX FF sp 14336 M M3 M5).
        -- apply (L5SAR.dk_trans L ar LBX FF sp 14336 M M1 M3); [apply L5SAR.dk_grows; exact MGM1|].
           apply (L5SAR.dk_callee L ar LBX [] FF [] sp 14336 (sp - 32) 12288 [] M1 M3 HP3); lia.
        -- apply (L5SAR.dk_callee L ar LBX [] FF [] sp 14336 (sp - 32) 12288 [] M3 M5 HP5); lia.
      * apply (L5SAR.dk_callee L ar LBX [] FF [] sp 14336 sp 4096 [] M5 M7 HP7); lia.
  - apply (L5LZ.model_rt_trans model model6 model7); [|exact MRT7].
    apply (L5LZ.model_rt_trans model model5 model6); [|exact MRT6].
    apply (L5LZ.model_rt_trans model model4 model5); [|exact MRT5].
    apply (L5LZ.model_rt_trans model model3 model4); [|exact MRT4].
    apply (L5LZ.model_rt_trans model model1 model3); [exact MRT1| exact MRT3].
  - intros x Hx. apply INCLK3. apply INCLK5. exact Hx.
  - intros x Hx. apply INCAw7. apply INCAw5. apply INCAw3. exact Hx.
  - exact AM7.
  - exact HH7.
Qed.
End WithHeap.
End PEAEKD.
