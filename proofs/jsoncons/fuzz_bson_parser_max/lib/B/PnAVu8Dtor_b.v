(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnSpecsAX_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnASrcKit_b PnAReset1_b PnAEmbKit_b PnAVu8DtorP_b Ba0_code_ab014_ab018_b PnSpecsAXC_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PNAV8D.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition nsh (a n : Z) : Prop := a + n <= 2147446784 \/ 17594333495296 <= a.
Lemma nsh_not a n x : nsh a n -> a <= x < a + n -> ~ (BIGSHADOW_LO <= x < BIGSHADOW_HI).
Proof. unfold nsh, BIGSHADOW_LO, BIGSHADOW_HI. intros [X|X] H Y; lia. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
(* [comment removed for export] *)
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


(* [comment removed for export] *)
Lemma vu8_dtor_null : forall (fx : FPState) R M model K LB FF LK Aw cr t v sp r,
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] -> PMSPA.entryA PMA.AD L ar R M sp r 1 ->
    PGSA.ffroomB PNRA.FCB 1 FF LK -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= ar_sptop ar -> t mod 8 = 0 -> PMSPA.accA M t 8 -> L5.u64_at RSEGS M t v ->
    PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> L5.defined M v 24 -> PMSPA.accA M v 24 ->
    PGV8.v8_at RSEGS PMSPA.accA PMSPA.annA M v PGV8.V8Null ->
    (forall (fx' : FPState) R' M' model' LK' Aw',
        regs_preserved R R' ->
        L5CA.ahpres L ar (PNRA.lb_remove_v8 PGV8.V8Null LB) FF sp (PMSPA.pm_scr 1) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PNRA.lb_remove_v8 PGV8.V8Null LB) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xab9e0 M model) K.
Proof.
  intros fx R M model K LB FF LK Aw cr t v sp r HH AM K0 ENT FRM FRS A10 Tsp Ttop T8 TC Tv AOv V8 VD VC VEC KONT. cbn [PNRA.lb_remove_v8] in KONT.
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
  pose proof VEC as (_ & _ & W0 & W8 & W16).
  assert (OTN : nsh t 8) by (unfold nsh; right; clear - Tsp SLO SPT; lia).
  assert (OVN : nsh v 24) by (unfold nsh; destruct OvBIG as [X|X]; [right| left]; lia).
  assert (OPS : v + 24 + 4096 + 14336 <= sp) by (clear - Ov2 SLO; lia).
  assert (ZT : L5KA.zeros_at MV (t / 8 + SB) 1) by exact (stk_shz_vis H M t VSTSH TC T8 ltac:(lia) Ttop).
  assert (ZV : L5KA.zeros_at MV (v / 8 + SB) 3) by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model v 24 HH AOv V8 ltac:(lia) ltac:(reflexivity) VC).
  assert (VSW : L5.writable RSEGS MV (sp - 32) 32).
  { apply (proj2 (L5A.writable_vis H M (sp - 32) 32 (VIS (sp - 32) 32 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]| lia| lia]. }
  assert (IC0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (Tvv : L5.u64_at RSEGS MV t v) by (apply (proj2 (L5A.u64_at_vis H M t v OtVIS ltac:(lia) ltac:(lia))); exact Tv).
  assert (W0v : L5.u64_at RSEGS MV v 0) by (apply (proj2 (L5A.u64_at_vis H M v 0 (L5A.avis_sub H v 24 v 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact W0).
  (* [comment removed for export] *)
  pose proof (PNAV8DP.azwN_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | _ => 0 end)) as P.
  cbn beta iota in P. rewrite HO in P.
  assert (Q1 : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
  assert (Q2 : 0 <= v < 2 ^ 64) by (clear - Ov1 Ov3; lia).
  assert (Q9 : 140735332487200 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (Q10 : 6905856 <= t <= 140737488355320) by (clear - Tsp Ttop SLO SPT; lia).
  assert (Q11 : PNAV8DP.aligned t 8) by exact T8.
  assert (Q12 : 2147446784 + 17592186048512 <= t \/ t + 8 <= 2147446784) by (clear - OTN; unfold nsh in OTN; lia).
  assert (Q13 : L5KA.zeros_at MV ((t / 8) + 2147450880) 1) by exact ZT.
  assert (Q14 : ((sp - 32) + 32 <= t \/ t + 8 <= (sp - 32))) by (left; clear - Tsp; lia).
  assert (Q15 : 6905856 <= v <= 140737488355304) by (clear - Ov1 Ov3; lia).
  assert (Q16 : PNAV8DP.aligned v 8) by exact V8.
  assert (Q17 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - OVN; unfold nsh in OVN; lia).
  assert (Q18 : L5KA.zeros_at MV ((v / 8) + 2147450880) 3) by exact ZV.
  assert (Q19 : ((sp - 32) + 32 <= v \/ v + 24 <= (sp - 32))) by (clear - OPS; lia).
  assert (Q20 : (t + 8 <= v \/ v + 24 <= t)) by (right; clear - Ov2 Tsp SLO; lia).
  L5SAR.feed P ltac:(first [assumption | unfold PNAV8DP.aligned; assumption]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & _).
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0xabad0 W_ab014 r F_ab014 eq_refl D_ab014 R1ra ltac:(lia) Hr2) as MS2.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xab9e0 R1 r M1v (fun a => sp - 32 <= a < sp - 32 + 32) K HH AM
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

Theorem vu8_dtor_ok : PNSAXC.clear_v8_spec RSEGS PMA.AD L ar HI 0xabb00 -> PNSAX.ann_delete_v8_spec RSEGS PMA.AD L ar HI 0xabb8c -> PMA.opdel_spec L ar HI ->
  PNSAX.vu8_dtor_spec RSEGS PMA.AD L ar HI 0xab9e0.
Proof.
  intros ASH ADL OPD. unfold PNSAX.vu8_dtor_spec.
  intros fx R M model K LB FF LK Aw cr t v sp r x HH AM K0 ENT FRM FRS A10 Tsp Ttop T8 TC Tv AOv V8 VD VC VEC Ib KONT.
  destruct x as [|b n c].
  { apply (vu8_dtor_null fx R M model K LB FF LK Aw cr t v sp r HH AM K0 ENT FRM FRS A10 Tsp Ttop T8 TC Tv AOv V8 VD VC VEC KONT). }
  cbn [PNRA.lb_remove_v8] in KONT. cbn [PGV8.v8_own] in Ib. assert (Ibc : In (b, c) LB) by (apply Ib; left; reflexivity). clear Ib. rename Ibc into Ib.
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
  pose proof VEC as (_ & _ & W0 & W8 & W16 & NC & C27 & B4096 & Hal & DB & CB & AN).
  pose proof (WB _ Ib) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _ & _ & _ & _ & FAb & _). cbn [fst snd] in Bb0, Bb1, Bb2, Bb3, Bb4, Bb5, FAb.
  assert (Bb47 : b + c <= 2 ^ 47) by (unfold app_mem in Bb5; destruct Bb5 as (_ & _ & X); exact X).
  assert (BBN : nsh b (c)) by (destruct Bb5 as (_ & X & _); unfold nsh; unfold BIGSHADOW_LO, BIGSHADOW_HI in X; destruct X; [left|right]; lia).
  assert (OTN : nsh t 8) by (unfold nsh; right; clear - Tsp SLO SPT; lia).
  assert (OVN : nsh v 24) by (unfold nsh; destruct OvBIG as [X|X]; [right| left]; lia).
  clear OvBIG Bb1 Bb5 FSAPP.
  assert (OPS : v + 24 + 4096 + 14336 <= sp) by (clear - Ov2 SLO; lia).
  set (LBX := lb_remove b LB).
  (* [comment removed for export] *)
  assert (ZT : L5KA.zeros_at MV (t / 8 + SB) (8 / 8)) by exact (stk_shz_vis H M t VSTSH TC T8 ltac:(lia) Ttop).
  assert (ZV : L5KA.zeros_at MV (v / 8 + SB) (24 / 8)) by exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model v 24 HH AOv V8 ltac:(lia) ltac:(reflexivity) VC).
  change (8 / 8) with 1 in ZT. change (24 / 8) with 3 in ZV.
  assert (VSW : L5.writable RSEGS MV (sp - 32) 32).
  { apply (proj2 (L5A.writable_vis H M (sp - 32) 32 (VIS (sp - 32) 32 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]| lia| lia]. }
  assert (IC0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (Tvv : L5.u64_at RSEGS MV t v) by (apply (proj2 (L5A.u64_at_vis H M t v OtVIS ltac:(lia) ltac:(lia))); exact Tv).
  assert (W0v : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b (L5A.avis_sub H v 24 v 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact W0).
  assert (W8v : L5.u64_at RSEGS MV (v + 8) (b + n))
    by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ (L5A.avis_sub H v 24 (v + 8) 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact W8).
  assert (WV8 : L5.writable RSEGS MV (v + 8) 8).
  { apply (proj2 (L5A.writable_vis H M (v + 8) 8 (L5A.avis_sub H v 24 (v + 8) 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M v 24); [exact VD| lia| lia]| lia| lia]. }
  (* [comment removed for export] *)
  pose proof (PNAV8DP.azwA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => b | 36%nat => b + n | _ => 0 end)) as P.
  cbn beta iota in P. rewrite HO in P.
  assert (Q1 : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
  assert (Q2 : 0 <= v < 2 ^ 64) by (clear - Ov1 Ov3; lia).
  assert (Q3 : 0 <= b < 2 ^ 64) by (clear - Bb0 Bb47 C27; lia).
  assert (Q4 : 0 <= b + n < 2 ^ 64) by (clear - Bb0 Bb47 NC C27; lia).
  assert (Q9 : 140735332487200 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (Q10 : 6905856 <= t <= 140737488355320) by (clear - Tsp Ttop SLO SPT; lia).
  assert (Q11 : PNAV8DP.aligned t 8) by exact T8.
  assert (Q12 : 2147446784 + 17592186048512 <= t \/ t + 8 <= 2147446784) by (clear - OTN; unfold nsh in OTN; lia).
  assert (Q13 : L5KA.zeros_at MV ((t / 8) + 2147450880) 1) by exact ZT.
  assert (Q14 : ((sp - 32) + 32 <= t \/ t + 8 <= (sp - 32))) by (left; clear - Tsp; lia).
  assert (Q15 : 6905856 <= v <= 140737488355304) by (clear - Ov1 Ov3; lia).
  assert (Q16 : PNAV8DP.aligned v 8) by exact V8.
  assert (Q17 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - OVN; unfold nsh in OVN; lia).
  assert (Q18 : L5KA.zeros_at MV ((v / 8) + 2147450880) 3) by exact ZV.
  assert (Q19 : ((sp - 32) + 32 <= v \/ v + 24 <= (sp - 32))) by (clear - OPS; lia).
  assert (Q20 : (t + 8 <= v \/ v + 24 <= t)) by (right; clear - Ov2 Tsp SLO; lia).
  assert (Q21 : 4096 <= b <= 140737488355327) by (clear - Bb0 Bb47 C27; lia).
  assert (Q22 : PNAV8DP.aligned b 16) by exact Hal.
  assert (Q23 : 0 <= (b + n) - b <= 134217728) by (clear - NC C27; lia).
  L5SAR.feed P ltac:(first [assumption | unfold PNAV8DP.aligned; assumption]).
  clear Q3 Q4 Q12 Q13 Q17 Q18 Q21 Q22 Q23.
  destruct P as (fx2 & R2 & M1v & MG1 & _ & FRZ1 & MS2 & KS2 & A2ra & A12 & A18 & A19 & A110 & A111 & A112 & A113 & A118 & C8 & C32 & C24 & C16 & C8s).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx2 R 0xab9e0 R2 0xabb00 M1v
           (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (v + 8 <= a < v + 8 + 8)) K HH AM MS2 MG1).
  { intros a Ha Hnw. apply FRZ1; [exact Ha| intros X; apply Hnw; left; exact X| intros X; apply Hnw; right; exact X]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|X]; unfold aclientw, aclient_g.
      + right; left. split; [lia| intros Y; lia].
      + do 3 right; left. destruct AOv as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. split; [lia| intros Y; lia].
    - destruct Wa as [X|X]; lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  (* [comment removed for export] *)
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
  pose proof (ri_front _ _ _ _ _ _ _ _ _ HH1 Ib) as HH1s. change (ri_inv HI (PGV8.v8_own (PGV8.V8Blk b n c) ++ LBX) FF LK cr Aw M1 (vml_of model1)) in HH1s.
  (* [comment removed for export] *)
  unfold PNSAXC.clear_v8_spec in ASH.
  apply (ASH fx2 R2 M1 model1 K LBX FF LK Aw cr v (PGV8.V8Blk b n c) (sp - 32) 703040 HH1s AM1 K0).
  { split; [rewrite L5K.rl1; exact A2ra|]. split; [split; [lia| reflexivity]|].
    split; [rewrite L5K.rl2; exact A12|].
    split; [rewrite L5K.rl3, (KS2 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS2 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK1c|]. change (12288 / 8) with 1536. replace (sp - 32 - 12288) with (sp - 12320) by lia. exact SZ1. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact A110. }
  { exact AOv. }
  { exact V8. }
  { apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact VC]. }
  { (* [comment removed for export] *)
    unfold PGV8.v8_at. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
    - intros i Hi. apply MGM1. apply VD. exact Hi.
    - apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact VC].
    - apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [lia| intros [Y|Y]; lia]| lia| lia| exact W0].
    - apply (proj1 (L5A.u64_at_vis H M1 (v + 8) (b + n) (L5A.avis_sub H v 24 (v + 8) 8 OvVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact C8.
    - apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply FR1; [lia| intros [Y|Y]; lia]| lia| lia| exact W16].
    - lia.
    - lia.
    - lia.
    - exact Hal.
    - intros i Hi. apply MGM1. apply DB. exact Hi.
    - apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact CB].
    - apply (PNAEK.ann_agree M M1 b n c); [| lia| lia| exact AN]. intros j Hj. rewrite (PNAEK.S_add8 b j).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply (SHM1 b (8 * ((c + 7) / 8))); clear - Bb0 Bb47 Hal Hj C27; Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  intros fx3 R3 M3 model3 LK3 Aw3 RP3 VEC3 KEPT3 HP3 MRT3 INCLK3 INCAw3 AM3 HH3. cbn [PGV8.v8_clear] in VEC3.
  assert (ACC3 : PMSPA.accA M3 v 24) by (destruct VEC3 as (_ & X & _); exact X).
  change (PMSPA.pm_scr 0) with 12288 in HP3.
  (* [comment removed for export] *)
  set (Wv8 := [(v + 8, 8)]).
  assert (WAPP8 : PMKA.wapp Wv8).
  { unfold Wv8. apply PMKA.wapp_cons; [|apply PMKA.wapp_nil]. cbn [fst snd]. unfold nsh in OVN. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct OVN; [left|right]; lia. }
  assert (FRBX : forall x, In x LBX -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
  { intros x Hx. destruct (proj1 (WB x (L5C.in_lb_remove b x LB Hx))) as (X0 & _ & _ & _ & _ & X5). clear - X0 X5. unfold app_mem in X5. lia. }
  assert (EK01 : L5SAR.ek L ar LBX FF sp 14336 Wv8 M M1).
  { apply (L5SAR.ek_piece L ar LBX FF sp 14336 Wv8 M M1 P1 FR1). intros a Ha Hc Ho [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M1 _ sp 14336 a HH1s SPT (L5SAR.aclient_appb L ar LBX (PGV8.v8_own (PGV8.V8Blk b 0 c)) FF sp 14336 a Hc))
        as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
    - apply (Ho (v + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (EK13 : L5SAR.ek L ar LBX FF sp 14336 Wv8 M1 M3).
  { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 14336 (sp - 32) 12288 Wv8 Wv8 M1 M3 HP3); [lia| lia| intros a _ X; exact X]. }
  pose proof (L5SAR.ek_trans L ar LBX FF sp 14336 Wv8 M M1 M3 EK01 EK13) as EK03.
  assert (ASTK3 : L5CA.astk ar M3 sp 14336) by (apply (PMKA.astk_after_ahpres L ar LBX FF M1 M3 sp 14336 (sp - 32) 12288 Wv8 ASTK1 HP3); lia).
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
  (* [comment removed for export] *)
  idtac.
  assert (U0 : 0 <= t < 2 ^ 64) by (clear - Q10; lia).
  assert (Q12 : 2147446784 + 17592186048512 <= t \/ t + 8 <= 2147446784) by (clear - OTN; unfold nsh in OTN; lia).
  LeanFeed.pfeed P (PNAV8DP.azwC_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => v | 40%nat => t | _ => 0 end)) ltac:(first [assumption | unfold PNAV8DP.aligned; assumption]). clear Q12.
  destruct P as (fx4 & R4 & M4v & MG4 & FR4w & FRZ4 & MS4 & KS4 & A4ra & A4a0 & _).
  assert (E4 : M4v = MV3) by (apply functional_extensionality; exact FR4w). subst M4v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK3 cr Aw3 M3 model3 fx3 fx4 R3 703040 R4 0xabb8c MV3 K HH3 AM3 MS4 MG4 FRZ4).
  intros M4 model4 HH4 AM4 MRT4 HID4 VIS4 MGM4 FR4.
  assert (E34 : M4 = M3) by exact (L5SAR.mem_eq_of_agree M3 M4 FR4). subst M4.
  assert (ASTK4 : L5CA.astk ar M3 sp 14336) by exact ASTK3.
  assert (SZ3 : shadow_zero M3 (sp - 12320) 1536).
  { apply (PMKA.stksh_keepA L ar LBX FF sp 14336 Wv8 M1 M3 EK13 WAPP8 (sp - 12320) 1536); [lia|lia|lia| replace (sp - 12320) with (sp - 16 * 770) by lia; apply SP16| lia| exact SZ1]. }
  (* [comment removed for export] *)
  unfold PNSAX.ann_delete_v8_spec in ADL.
  apply (ADL fx4 R4 M3 model4 K LBX FF LK3 Aw3 cr v (PGV8.V8Blk b 0 c) (sp - 32) 703068 HH4 AM4 K0).
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
  (* [comment removed for export] *)
  assert (FRAME15 : forall a, sp - 32 <= a < sp -> M5 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP5 as (P5 & _). destruct HP3 as (P3 & _).
    assert (CLa : forall LBz FFz, aclient L ar LBz FFz (sp - 32) 12288 a) by (intros LBz FFz; unfold aclient, aclient_g; right; left; split; [lia| intros X; lia]).
    rewrite P5; [| split; [lia|]; split; [apply CLa| intros r0 []]]. apply P3. split; [lia|]. split; [apply CLa| intros r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia]. }
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
  assert (Q3 : 0 <= b < 2 ^ 64) by (clear - Bb0 Bb47 C27; lia).
  assert (Q3b : 0 <= b + c < 2 ^ 64) by (clear - Bb0 Bb47 C27; lia).
  assert (Q12 : 2147446784 + 17592186048512 <= t \/ t + 8 <= 2147446784) by (clear - OTN; unfold nsh in OTN; lia).
  assert (Q17 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by (clear - OVN; unfold nsh in OVN; lia).
  LeanFeed.pfeed P (PNAV8DP.azwD_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => b | 35%nat => b + c
                                              | 38%nat => bv_unsigned (getr R (reg 1)) | 39%nat => bv_unsigned (getr R (reg 8)) | 40%nat => t
                                              | 41%nat => bv_unsigned (getr R (reg 9)) | 42%nat => bv_unsigned (getr R (reg 18)) | _ => 0 end)) ltac:(first [assumption | unfold PNAV8DP.aligned; assumption]). clear Q12 Q17 Q14 Q19 Q20.
  destruct P as (fx6 & R6 & M6v & MG6 & FR6w & FRZ6 & MS6 & KS6 & A61 & A62 & A68 & A69 & A610 & A611 & A612 & A618).
  assert (E6 : M6v = MV5) by (apply functional_extensionality; exact FR6w). subst M6v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK5 cr Aw5 M5 model5 fx5 fx6 R5 703068 R6 0xd39ac MV5 K HH5 AM5 MS6 MG6 FRZ6).
  intros M6 model6 HH6 AM6 MRT6 HID6 VIS6 MGM6 FR6.
  assert (E56 : M6 = M5) by exact (L5SAR.mem_eq_of_agree M5 M6 FR6). subst M6.
  (* [comment removed for export] *)
  unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in OPD. cbn [pa_opdel PMA.AD ADDR_A] in OPD.
  assert (R6ra : getr R6 (reg 1) = Z_to_bv 64 r) by (rewrite A61, Z_to_bv_bv_unsigned; exact Rra).
  apply (OPD fx6 R6 M5 model6 K (PGV8.v8_own (PGV8.V8Blk b 0 c) ++ LBX) FF LK5 Aw5 cr b c sp r HH6 AM6 K0 (or_introl eq_refl)).
  { rewrite L5K.rl10. exact A610. }
  { rewrite L5K.rl1. exact R6ra. }
  { exact RAok. }
  { rewrite L5K.rl2. exact A62. }
  { rewrite L5K.rl4, (KS6 4%nat) by inl. rewrite (L5SAR.cs_of_preserved R4 R5 4 RP5) by inl. rewrite (KS4 4%nat) by inl.
    rewrite (L5SAR.cs_of_preserved R2 R3 4 RP3) by inl. rewrite (KS2 4%nat) by inl. exact Rtp. }
  { pose proof (L5SAR.astk_sub ar M5 M5 sp 14336 0 PMSPA.OPDEL_SCR ASTK5 (fun _ X => X)) as X. unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in *.
    replace (sp - 0) with sp in X by lia. apply X; [lia| lia| lia| replace (sp - 0) with sp by lia; exact A16]. }
  intros fx7 R7 M7 model7 Aw7 RP7 HP7 MRT7 INCAw7 AM7 HH7.
  unfold PGV8.v8_own in HH7, HP7. cbn [app lb_remove fst] in HH7, HP7. rewrite Z.eqb_refl in HH7, HP7.
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
           apply (L5SAR.dk_callee L ar LBX [] FF [] sp 14336 (sp - 32) 12288 [(v + 8, 8)] M1 M3 HP3); lia.
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
End PNAV8D.
