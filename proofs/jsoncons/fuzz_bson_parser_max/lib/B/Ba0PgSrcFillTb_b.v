(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnAFillP_b Ba0_code_raf6e0_af6e4_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PGSFBTA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Ltac vis64 OAV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis32 OAV := lazymatch goal with |- L5.u32_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u32_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem fill_buffer_tb_okG : PMA.xsgetn_spec L ar HI -> PGSA.fill_buffer_tb_specG RSEGS PMA.AD L ar HI PNRA.FCB.
Proof.
  intros XS. unfold PGSA.fill_buffer_tb_specG, PGSA.src_specG.
  intros O OK fx R M model K OB LBX FF LK Aw cr sp r src str sm Wextra HH AM K0 ENT FRM FRS OFR A10 FARGS WX PA IA BASE INCS KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  unfold PGSA.tbfill_args in FARGS. destruct FARGS as (p & A11 & A12 & WINp). unfold PMTXS.tbfill_W in WX. destruct WX as (p' & A11' & Hp' & ->).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12. unfold PM.CHUNK in A12.
  change (PMSPA.pm_scr 3) with 18432 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M src OB PA) as (PSRC & PNI & SDEF0).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own src ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M model os _ _ src sp 18432 HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M model ois str sm sp 18432 HH AOI I8 IA ASTK)
    as ((I1 & _ & IBIG) & IZ & IW & ICE & IAV & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 18432 48 HH ASTK ltac:(lia)) as (SL48 & SH48 & V3).
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x135118 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x135080 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
  cbn in VT1, VT2.
  destruct src as [qc de rem]. destruct sm as [g eg st].
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof PSRC as PSRC0.
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  pose proof IA as (H0i & _ & _ & H16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & E1 & E2).
  destruct IOSB as (I0 & I32 & I36 & I40 & _ & _ & _ & _ & IST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD ADDR_A] in *.
  replace (ois + 120 + 32) with (ois + 152) in I32 by lia. replace (ois + 120 + 36) with (ois + 156) in I36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in I40 by lia.
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4.
  pose proof (PGSA.oo_win _ _ _ _ _ _ OK M _ OB p PM.CHUNK PA WINp) as (_ & DEFp & WIN & CBt). unfold PM.CHUNK in DEFp, CBt.
  destruct WIN as [(qt & ct & OIN & Dq1 & Dq2)|WFR]; [| exfalso; unfold PM.CHUNK in WFR; clear - WFR; lia]. unfold PM.CHUNK in Dq2.
  pose proof (OBIN qt ct OIN) as TIN.
  destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, T4, TAPP. unfold app_mem in TAPP.
  assert (Ep : p' = p).
  { rewrite A11 in A11'. apply (f_equal bv_unsigned) in A11'. rewrite !L5.unsigned_lit in A11' by (clear - Hp' T0 T4 Dq1 Dq2 SLO SHI SPT; lia). clear - A11'; lia. }
  subst p'. clear A11'.
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (HO : bv_unsigned (getr R (reg 10)) = os) by (rewrite A10; apply L5.unsigned_lit; lia).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (ND : NoDup (map fst LB)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (APQO : forall o n, PMSPA.aobjA FF o n -> qc + 16384 <= o \/ o + n <= qc).
  { intros o n AOo. exact (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 o n HH QIN AOo). }
  assert (APTO : forall o n, PMSPA.aobjA FF o n -> qt + ct <= o \/ o + n <= qt).
  { intros o n AOo. exact (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qt ct o n HH TIN AOo). }
  pose proof (APTO ois 272 AOI) as TAO.
  (* [comment removed for export] *)
  set (WS := PGS.W_srcG os ois (PM.SRC qc de rem) ++ [(p, 16384)]).
  assert (WAPPS : PMKA.wapp WS).
  { unfold WS, PGS.W_srcG, PGS.W_srcfG. cbn [PM.sr_qc app]. destruct (WB _ QIN) as ((_ & _ & _ & _ & _ & QAPP) & _). cbn [fst snd] in QAPP. unfold app_mem in QAPP.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - OBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in *; clear - QAPP; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - TAPP Dq1 Dq2; Lia.lia| apply PMKA.wapp_nil]. }
  assert (OWA : Forall (fun b => fst b + snd b <= lo \/ hi <= fst b) (PM.src_own (PM.SRC qc de rem) ++ OB)).
  { apply Forall_forall. intros [B m] Hin. cbn [fst snd].
    assert (HB : In (B, m) LB) by (unfold LB; rewrite app_assoc; apply in_or_app; left; exact Hin).
    destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m lo (hi - lo) HH HB OFR) as [X|X]; [left; exact X| right; clear - X; lia]. }
  assert (OWB : forall b, In b OB -> fst b + snd b <= PM.sr_qc (PM.SRC qc de rem) \/ PM.sr_qc (PM.SRC qc de rem) + PM.CHUNK <= fst b).
  { intros [B m] Hin. cbn [fst snd PM.sr_qc]. unfold PM.CHUNK.
    assert (NE : B <> qc).
    { intros E. apply (PMASK.fst_neq_appA [(qc, 16384)] (OB ++ LBX) qc 16384 B m); [exact ND| left; reflexivity| apply in_or_app; left; exact Hin| symmetry; exact E]. }
    destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m qc 16384 HH (OBIN B m Hin) QIN NE) as [X|X]; clear - X; lia. }
  assert (OWK : forall M3, L5SAR.ek L ar LB FF sp 18432 WS M M3 -> L5SAR.dk L ar LB FF sp 18432 M M3 -> L5CA.astk ar M3 sp 18432 ->
      PMFA.agA M M3 os 296 -> PGS.ow_at O M3 (PM.SRC qc de rem) OB).
  { intros M3 EK DK ASTK3 AG.
    apply (PGSA.oo_upd _ _ _ _ _ _ OK LBX sp 18432 [(p, 16384)] M M3 (PM.SRC qc de rem) (PM.SRC qc de rem) OB FF LK Aw cr (vml_of model) OFR PA HH OWA OWB);
      [constructor; [right; cbn [fst snd]; exact WINp| constructor]| | | reflexivity].
    - apply (L5SAR.ahpres_of L ar LB FF sp 18432 WS M M3 EK); [pose proof ASTK3 as (_ & _ & _ & _ & DS3 & _); exact DS3| exact DK].
    - apply (PGSKA.src_fields_keepG M M3 os ois (ois + 16) (PM.SRC qc de rem) PSRC0); cbn [PM.sr_qc]; unfold PM.CHUNK.
      + clear - O1; lia.
      + clear - O1; lia.
      + exact AG.
      + apply (PMASK.agsh_blk L ar LB FF sp 18432 WS M M3 qc 16384 EK WAPPS QIN); [clear - Q0; lia| clear - Q4 SLO SHI SPT; lia].
      + apply (PMASK.defined_dk L ar LB FF sp 18432 M M3 qc 16384 DK); [| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH].
        intros i Hi. apply (L5SAR.block_client L ar LB FF sp 18432 qc 16384 i QIN Hi). }
  assert (INWS : forall r0, In r0 [(ois + 40, 8); (p, 16384); (ois + 152, 4)] -> In r0 WS).
  { intros r0 Hr. unfold WS, PGS.W_srcG, PGS.W_srcfG. cbn [PM.sr_qc app].
    destruct Hr as [<-|[<-|[<-|[]]]]; [right; left; reflexivity| right; right; right; right; left; reflexivity| right; right; left; reflexivity]. }
  destruct IST as [ST0|ST2].
  2:{ (* [comment removed for export] *)
    subst st.
    LeanFeed.pfeed P (PMAFBP.afbE_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => p | 36%nat => os | 37%nat => ois | _ => 0 end)) ltac:(first [assumption | exact Rsp | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- L5.u64_at _ _ (ois + _) _ => unfold MV; vis64 IAV
        | |- L5.u64_at _ _ ois _ => unfold MV; apply (proj2 (L5A.u64_at_vis _ M ois _ ltac:(apply IAV; lia) ltac:(lia) ltac:(lia))); assumption
        | |- L5.u32_at _ _ (ois + _) _ => unfold MV; vis32 IAV
        | |- PMAFBP.aligned _ _ => unfold PMAFBP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PP). pdestr PP.
    unfold PMSPA.cfg, PMSP.cfg. cbn [pa_fill_buffer PMA.AD ADDR_A].
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb29f8 R1 0xb2c80 M1v (fun a => sp - 48 <= a < sp - 48 + 48) K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
    { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK01 : L5SAR.ek L ar LB FF sp 18432 [] M M1).
    { apply (PMKA.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 18432 [] (sp - 48) (sp - 48 + 48) HH SPT); [lia|lia|lia|].
      intros a Ha Hn. apply FR1; [exact Ha| exact Hn]. }
    assert (ASTK1 : L5CA.astk ar M1 sp 18432) by (apply (L5SAR.astk_grows ar M M1 sp 18432 ASTK MGM1)).
    assert (Rr : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    apply (PMASK.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K LB FF LK cr Aw 0xb2c80 r W_b1708 HH1 AM1 F_b1708 eq_refl D_b1708 Rr ltac:(lia) Hr2).
    intros model2 MRT2 AM2 HH2.
    apply (KONT fx1 R1 M1 model2 LK Aw (PM.SRC qc de rem) (PM.STRM g eg 2)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk]; [ first [ rewrite (KS1 _) by inl; reflexivity ] |]). destruct Hk.
    + apply (OWK M1); [apply (L5SAR.ek_W L ar LB FF sp 18432 WS [] M M1 EK01); intros a _ r0 []| apply L5SAR.dk_grows; exact MGM1| exact ASTK1|].
      apply (PMKA.agA_obj L ar LB FF sp 18432 [] M M1 EK01 PMKA.wapp_nil FRB os 296 AO). intros i _ r0 [].
    + apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 18432 [] M M1 EK01 PMKA.wapp_nil FRB BRB _ _ _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
    + unfold PMSP.src_step, PM.unread. cbn. lia.
    + split.
      { unfold PMPS.fill_res. split; [reflexivity|]. exists 0. cbn [PM.sm_g PM.sm_st].
        split; [rewrite L5K.rl10; match goal with H : getr R1 (reg 10) = _ |- _ => exact H end|].
        split; [unfold PM.CHUNK; lia|]. split; [lia|]. split; [intros X; discriminate X| intros _; split; reflexivity]. }
      exists p, 0. split; [rewrite L5SAR.r11; exact A11|]. split; [rewrite L5K.rl10; match goal with H : getr R1 (reg 10) = _ |- _ => exact H end|]. intros i Hi. lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 18432 _ M M1).
      * apply (L5SAR.ek_W L ar LB FF sp 18432 _ [] M M1 EK01). intros a _ r0 [].
      * pose proof ASTK1 as (_ & _ & _ & _ & DS1 & _). exact DS1.
      * apply L5SAR.dk_grows. exact MGM1.
    + eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    + apply incl_refl.
    + apply incl_refl.
    + exact AM2.
    + exact HH2. }
  subst st.
  LeanFeed.pfeed P (PMAFBP.afbA_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => p | 36%nat => os | 37%nat => ois | _ => 0 end)) ltac:(first [assumption | exact Rsp | lazymatch goal with
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.u64_at _ _ (ois + _) _ => unfold MV; vis64 IAV
      | |- L5.u64_at _ _ ois _ => unfold MV; apply (proj2 (L5A.u64_at_vis _ M ois _ ltac:(apply IAV; lia) ltac:(lia) ltac:(lia))); assumption
      | |- L5.u32_at _ _ (ois + _) _ => unfold MV; vis32 IAV
      | |- PMAFBP.aligned _ _ => unfold PMAFBP.aligned; lia
      | |- _ => lia end]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T13 & T14 & T19 & T20 & C48 & C40 & C32 & C24 & C16 & C8).
  unfold PMSPA.cfg, PMSP.cfg. cbn [pa_fill_buffer PMA.AD ADDR_A].
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb29f8 R1 0xda800 M1v (fun a => sp - 48 <= a < sp - 48 + 48) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (EK01 : L5SAR.ek L ar LB FF sp 18432 [] M M1).
  { apply (PMKA.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 18432 [] (sp - 48) (sp - 48 + 48) HH SPT); [lia|lia|lia|].
    intros a Ha Hn. apply FR1; [exact Ha| exact Hn]. }
  assert (ASTK1 : L5CA.astk ar M1 sp 18432) by (apply (L5SAR.astk_grows ar M M1 sp 18432 ASTK MGM1)).
  assert (BASE1 : PMSTA.base_okA RSEGS PMA.AD M1) by (apply (PMASK.base_keep L ar C LY LB FF sp 18432 [] M M1 EK01); [intros a _ r0 []| exact BASE]).
  assert (IA1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg 0)).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 18432 [] M M1 EK01 PMKA.wapp_nil FRB BRB _ _ _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
  assert (TS1 : forall k v, 8 <= k <= 48 -> L5.u64_at RSEGS M1v (sp - k) v -> L5.u64_at RSEGS M1 (sp - k) v).
  { intros k v Hk X. rewrite <- VIS1, <- HID1 in X.
    apply (proj1 (L5A.u64_at_vis _ M1 (sp - k) v (VIS1s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (STK1 : shadow_zero M1 (sp - 48 - 16384) (16384 / 8)).
  { change (16384 / 8) with 2048. change (18432 / 8) with 2304 in STKSH.
    assert (M8a : (sp - 18432) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 18432) with (sp + (-1152) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (sp - 48 - 16384) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 48 - 16384) with (sp + (-1027) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    apply (PMKA.shadow_zero_sub M1 (sp - 18432) 2304); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKA.stksh_keepA L ar LB FF sp 18432 [] M M1 EK01 PMKA.wapp_nil (sp - 18432) 2304); [lia|lia|lia| exact M8a| lia| exact STKSH]. }
  (* [comment removed for export] *)
  assert (APART : p + 16384 <= g \/ eg <= p).
  { pose proof (PMASK.iss_unread_whereA M ois str _ IA) as [(Y1 & Y2)|(c0 & n0 & p0 & -> & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *.
    - clear - TAO Y1 Y2 Dq1 Dq2; lia.
    - assert (PIN : In (p0, c0) LBX) by (apply INCS; left; reflexivity).
      assert (NEQ : qt <> p0).
      { apply (PMASK.fst_neq_appA ((qc, 16384) :: OB) LBX qt ct p0 c0); [exact ND| right; exact OIN| exact PIN]. }
      destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ qt ct p0 c0 HH TIN (SOWN _ (or_introl eq_refl)) NEQ) as [Z1|Z1]; lia. }
  (* [comment removed for export] *)
  assert (ACH1 : PMSPA.accA M1 p 16384).
  { pose proof (BRB _ TIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
    apply (PMFA.accA_agree M M1 p 16384); [| exact CBt].
    intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply FR1; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia| unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia]. }
  (* [comment removed for export] *)
  unfold PMA.xsgetn_spec, PMSPA.xsgetn_spec in XS. cbn [pa_xsgetn PMA.AD ADDR_A] in XS.
  apply (XS fx1 R1 M1 model1 K LB FF LK Aw cr (sp - 48) 731892 ois p str (PM.STRM g eg 0) HH1 AM1 K0).
  { split; [rewrite L5K.rl1; exact T1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
    split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 2) with 16384. split; [|exact STK1].
    apply (L5SAR.astk_sub ar M1 M1 sp 18432 48 16384 ASTK1 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { intros k Hk. specialize (FRM k Hk). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact T10. }
  { rewrite L5SAR.r11. rewrite (KS1 11%nat) by inl. exact A11. }
  { rewrite L5SAR.r12. rewrite (KS1 12%nat) by inl. exact A12. }
  { exact AOI. }
  { exact I8. }
  { exact IA1. }
  { exact BASE1. }
  { exact SOWN. }
  { exists qt, ct. split; [exact TIN| unfold PM.CHUNK; split; lia]. }
  { unfold PM.CHUNK. exact ACH1. }
  { cbn [PM.sm_g PM.sm_eg]. unfold PM.CHUNK. exact APART. }
  intros fx2 R2 M2 model2 LK2 Aw2 c RP2 A10c Hc IA2 D2 HP2 MRT2 INC2 INCA2 AM2 HH2.
  rewrite L5K.rl10 in A10c. change (PMSPA.pm_scr 2) with 16384 in HP2. cbn [PM.sm_g PM.sm_eg PM.sm_st] in IA2. unfold PM.CHUNK in Hc. cbn [PM.sm_g PM.sm_eg PM.sm_st] in Hc.
  pose proof (PMASK.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
  assert (Hcm := Hc). assert (C0 : 0 <= c <= 16384) by (rewrite Hc; destruct (Z.min_spec 16384 (eg - g)) as [[X1 X2]|[X1 X2]]; rewrite X2; split; lia).
  set (WX := [(ois + 40, 8); (p, 16384)]) in *.
  assert (EK12 : L5SAR.ek L ar LB FF sp 18432 WX M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 18432 (sp - 48) 16384 _ _ M1 M2 HP2); [lia|lia|]. intros a _ Oq. exact Oq. }
  assert (DK12 : L5SAR.dk L ar LB FF sp 18432 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 18432 (sp - 48) 16384 _ M1 M2 HP2); lia).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP2 & _).
  assert (ASTK2 : L5CA.astk ar M2 sp 18432).
  { apply (PMKA.astk_after_ahpres L ar LB FF M1 M2 sp 18432 (sp - 48) 16384 _ ASTK1 HP2); lia. }
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ qt ct HH TIN) as QIMG.
  destruct (WB _ QIN) as ((_ & _ & _ & _ & _ & QAPP) & _). cbn [fst snd] in QAPP. unfold app_mem in QAPP.
  assert (OUTW : forall a, 65536 <= a < 6905856 -> L5.outside WX a).
  { intros a Ha r0 Hr. unfold WX in Hr. unfold L5.in_rng. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; [clear - Ha I1; lia| clear - Ha QIMG Dq1 Dq2; lia]. }
  assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2) by (apply (PMASK.base_keep L ar C LY LB FF sp 18432 _ M1 M2 EK12 OUTW BASE1)).
  assert (KF2 : forall a, sp - 48 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (E & _). apply E. split; [lia|]. split.
    - apply (L5SAR.stack_client L ar LB FF (sp - 48) 16384 a); [lia| lia].
    - intros r0 Hr. unfold WX in Hr. unfold L5.in_rng. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; unfold PM.CHUNK; lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
  set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
  assert (TS2 : forall k v, 8 <= k <= 48 -> L5.u64_at RSEGS M1 (sp - k) v -> L5.u64_at RSEGS MV2 (sp - k) v).
  { intros k v Hk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - k) v (VIS2s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; lia| lia| lia| exact X]. }
  assert (EK02 : L5SAR.ek L ar LB FF sp 18432 WX M M2).
  { apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M1 M2); [apply (L5SAR.ek_W L ar LB FF sp 18432 _ [] M M1 EK01); intros a _ r0 []| exact EK12]. }
  assert (DK02 : L5SAR.dk L ar LB FF sp 18432 M M2) by (apply (L5SAR.dk_trans L ar LB FF sp 18432 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]).
  assert (WSX : PMKA.wapp WX).
  { unfold WX.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct TAPP as (_ & [X|X] & _); [left; lia| right; lia]| apply PMKA.wapp_nil]. }
  assert (OUTO : forall i, os <= i < os + 296 -> L5.outside WX i).
  { intros i Hi r0 Hr. unfold WX in Hr. unfold L5.in_rng. destruct (APTO os 296 AO) as [Z1|Z1]; destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; clear - Hi Z1 LYD Dq1 Dq2; lia. }
  assert (PA2 : PGS.ow_at O M2 (PM.SRC qc de rem) OB).
  { apply (OWK M2); [| exact DK02| exact ASTK2| apply (PMKA.agA_obj L ar LB FF sp 18432 WX M M2 EK02 WSX FRB os 296 AO OUTO)].
    apply (L5SAR.ek_W L ar LB FF sp 18432 WS WX M M2 EK02). intros a Oq r0 Hr X. apply (Oq r0); [| exact X].
    apply INWS. unfold WX in Hr. destruct Hr as [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]. }
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 os _ _ _ sp 18432 HH2 AO O8 (proj1 (PGSA.oo_src _ _ _ _ _ _ OK M2 _ OB PA2)) (proj1 (proj2 (PGSA.oo_src _ _ _ _ _ _ OK M2 _ OB PA2))) ASTK2)
    as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 ois str _ sp 18432 HH2 AOI I8 IA2 ASTK2)
    as ((J1 & J8 & JBIG) & JZ & JW & JCE & JAV & _).
  fold os ois in P1, P8, PBIG, PZ, PW, PCE, PAV, J1, J8, JBIG, JZ, JW, JCE, JAV.
  pose proof (proj1 (PGSA.oo_src _ _ _ _ _ _ OK _ _ _ PA2)) as PSRC2.
  destruct PSRC2 as (S240b & S248b & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _). cbn [PM.p_src] in S240b, S248b. fold os ois in S240b, S248b.
  pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 HH2 BASE2) as (W0 & W1' & W2').
  pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 sp 18432 48 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3').
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK2 cr Aw2 M2 model2 0x135118 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as WT1.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK2 cr Aw2 M2 model2 0x135080 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as WT2.
  cbn in WT1, WT2. fold MV2 in W0, W1', W2', W3', WT1, WT2.
  pose proof IA2 as (K0i & _ & _ & K16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB2 & _ & _).
  destruct IOSB2 as (K0' & K32 & K36 & K40 & _ & _ & _ & _ & _).
  cbn [pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD ADDR_A] in *.
  replace (ois + 120 + 32) with (ois + 152) in K32 by lia. replace (ois + 120 + 36) with (ois + 156) in K36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in K40 by lia.
  set (WALL := [(ois + 40, 8); (p, 16384); (ois + 152, 4)]).
  assert (OUTO3 : forall i, os <= i < os + 296 -> L5.outside WALL i).
  { intros i Hi r0 Hr. unfold WALL in Hr. unfold L5.in_rng. destruct (APTO os 296 AO) as [Z1|Z1]; destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; clear - Hi Z1 LYD Dq1 Dq2; lia. }
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20. change (bv_modulus 64) with (2 ^ 64) in *.
  set (VS := fun j => match j with 2%nat => sp | 35%nat => c | 36%nat => os | 37%nat => ois | 40%nat => bv_unsigned (getr R (reg 1))
                                | 41%nat => bv_unsigned (getr R (reg 8)) | 42%nat => bv_unsigned (getr R (reg 9)) | 43%nat => bv_unsigned (getr R (reg 18))
                                | 44%nat => bv_unsigned (getr R (reg 19)) | 45%nat => bv_unsigned (getr R (reg 20)) | _ => 0 end).
  assert (RG2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact T2).
  assert (RG8 : getr R2 (reg 8) = Z_to_bv 64 (os + 240)) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; exact T8).
  assert (RG9 : getr R2 (reg 9) = Z_to_bv 64 16384) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; exact T9).
  assert (RG19 : getr R2 (reg 19) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 19 RP2) by inl; exact T19).
  assert (RG20 : getr R2 (reg 20) = Z_to_bv 64 ((os + 240) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R1 R2 20 RP2) by inl; exact T20).
  destruct (Z.eq_dec c 16384) as [CEQ|CNE].
  { (* [comment removed for export] *)
    assert (HcmX : 16384 = Z.min 16384 (eg - g)) by (rewrite <- Hc; symmetry; exact CEQ). clear Hc Hcm. subst c.
    (let T := type of (PMAFBP.afbB1_conc fx2 R2 MV2 VS) in let T := eval unfold VS in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMAFBP.afbB1_conc fx2 R2 MV2 VS) T ltac:(try (unfold VS); cbn beta iota) ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- L5.u64_at _ _ (ois + _) _ => unfold MV2; vis64 JAV
        | |- L5.u64_at _ _ ois _ => unfold MV2; apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))); assumption
        | |- L5.u32_at _ _ (ois + _) _ => unfold MV2; vis32 JAV
        | |- PMAFBP.aligned _ _ => unfold PMAFBP.aligned; lia
        | |- _ => lia end])).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb2af4 R3 0xb2c80 M3v (fun a => sp - 48 <= a < sp - 48 + 48) K HH2 AM2 MS3 MG3).
    { intros a Ha N. apply FRZ3; [exact Ha| exact N]. }
    { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 18432 [] M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 18432 [] M2 M3 (fun a => sp - 48 <= a < sp - 48 + 48) FR3). intros a Ha CL Oq X. destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 18432 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia]. }
    assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end; rewrite Z_to_bv_bv_unsigned; exact Rra).
    apply (PMASK.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 0xb2c80 r W_b1708 HH3 AM3 F_b1708 eq_refl D_b1708 Rr ltac:(lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    assert (EK03 : L5SAR.ek L ar LB FF sp 18432 WALL M M3).
    { apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M2 M3).
      - apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M1 M2); [apply (L5SAR.ek_W L ar LB FF sp 18432 _ [] M M1 EK01); intros a _ r0 []|].
        apply (L5SAR.ek_W L ar LB FF sp 18432 _ _ M1 M2 EK12). intros a Oq r0 Hr X. apply (Oq r0); [unfold WALL; destruct Hr as [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]| exact X].
      - apply (L5SAR.ek_W L ar LB FF sp 18432 _ _ M2 M3 EK23). intros a Oq r0 Hr X. apply (Oq r0); [unfold WALL; destruct Hr| exact X]. }
    assert (DK03 : L5SAR.dk L ar LB FF sp 18432 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3).
    assert (WSALL : PMKA.wapp WALL).
    { unfold WALL. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct TAPP as (_ & [X|X] & _); [left; lia| right; lia]|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]| apply PMKA.wapp_nil]. }
    apply (KONT fx3 R3 M3 model4 LK2 Aw2 (PM.SRC qc de rem) (PM.STRM (g + 16384) eg 0)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ match goal with H : getr R3 (reg ?x) = Z_to_bv 64 (bv_unsigned (getr R (reg ?x))) |- getr R3 (reg ?x) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
      destruct Hk.
    + apply (OWK M3); [| exact DK03| apply (L5SAR.astk_grows ar M2 M3 sp 18432 ASTK2 MGM3)| apply (PMKA.agA_obj L ar LB FF sp 18432 WALL M M3 EK03 WSALL FRB os 296 AO OUTO3)].
      apply (L5SAR.ek_W L ar LB FF sp 18432 WS WALL M M3 EK03). intros a Oq r0 Hr X. apply (Oq r0); [apply INWS; exact Hr| exact X].
    + apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 18432 [] M2 M3 EK23 PMKA.wapp_nil FRB BRB _ _ _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA2].
    + unfold PMSP.src_step, PM.unread. cbn. lia.
    + split.
      { unfold PMPS.fill_res. split; [reflexivity|]. exists 16384. cbn [PM.sm_g PM.sm_st PM.sm_eg].
        split; [rewrite L5K.rl10; match goal with H : getr R3 (reg 10) = _ |- _ => exact H | _ => rewrite (KS3 10%nat) by inl; exact A10c end|].
        split; [unfold PM.CHUNK; lia|]. split; [lia|]. split; [intros _; split; [unfold PM.CHUNK in *; exact HcmX| reflexivity]| intros X; discriminate X]. }
      exists p, 16384. split; [rewrite L5SAR.r11; exact A11|].
      split; [rewrite L5K.rl10; match goal with H : getr R3 (reg 10) = _ |- _ => exact H | _ => rewrite (KS3 10%nat) by inl; exact A10c end|].
      apply (L5C.defined_agree M2 M3 p 16384); [intros i Hi; rewrite FR3; [reflexivity| lia|]; intros X; lia| exact D2].
    + apply (L5SAR.ahpres_of L ar LB FF sp 18432 _ M M3).
      * apply (L5SAR.ek_W L ar LB FF sp 18432 _ WALL M M3 EK03). intros a Oq r0 Hr X. apply (Oq r0); [unfold WALL; destruct Hr as [<-|[<-|[<-|[]]]]; unfold PGS.W_srcG, PGS.W_srcfG; cbn [app PM.sr_qc]; [right; left; reflexivity| right; right; right; right; left; reflexivity| right; right; left; reflexivity]| exact X].
      * pose proof (L5SAR.astk_grows ar M2 M3 sp 18432 ASTK2 MGM3) as (_ & _ & _ & _ & DS3 & _). exact DS3.
      * apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3); [apply (L5SAR.dk_trans L ar LB FF sp 18432 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]|].
        apply L5SAR.dk_grows. exact MGM3.
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC2.
    + exact INCA2.
    + exact AM4.
    + exact HH4. }
  assert (CLT : c < 16384) by lia.
  { (* [comment removed for export] *)
    (let T := type of (PMAFBP.afbB2_conc fx2 R2 MV2 VS) in let T := eval unfold VS in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PMAFBP.afbB2_conc fx2 R2 MV2 VS) T ltac:(try (unfold VS); cbn beta iota) ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- L5.u64_at _ _ (ois + _) _ => unfold MV2; vis64 JAV
        | |- L5.u64_at _ _ ois _ => unfold MV2; apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))); assumption
        | |- L5.u32_at _ _ (ois + _) _ => unfold MV2; vis32 JAV
        | |- PMAFBP.aligned _ _ => unfold PMAFBP.aligned; lia
        | |- _ => lia end])).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb2af4 R3 0xb2c80 M3v (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (ois + 152 <= a < ois + 152 + 4)) K HH2 AM2 MS3 MG3).
    { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha Wa. split; [|intros X; lia]. destruct Wa as [Wa|Wa]; [unfold aclientw, aclient_g; right; left; split; [lia| intros X; lia]|]. unfold aclientw, aclient_g. do 3 right. left. destruct AOI as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 18432 [(ois + 152, 4)] M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 18432 [(ois + 152, 4)] M2 M3 (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (ois + 152 <= a < ois + 152 + 4)) FR3). intros a Ha CL Oq X. destruct X as [X|X]; [destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 18432 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia]|]. apply (Oq (ois + 152, 4)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end; rewrite Z_to_bv_bv_unsigned; exact Rra).
    apply (PMASK.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 0xb2c80 r W_b1708 HH3 AM3 F_b1708 eq_refl D_b1708 Rr ltac:(lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    assert (EK03 : L5SAR.ek L ar LB FF sp 18432 WALL M M3).
    { apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M2 M3).
      - apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M1 M2); [apply (L5SAR.ek_W L ar LB FF sp 18432 _ [] M M1 EK01); intros a _ r0 []|].
        apply (L5SAR.ek_W L ar LB FF sp 18432 _ _ M1 M2 EK12). intros a Oq r0 Hr X. apply (Oq r0); [unfold WALL; destruct Hr as [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]| exact X].
      - apply (L5SAR.ek_W L ar LB FF sp 18432 _ _ M2 M3 EK23). intros a Oq r0 Hr X. apply (Oq r0); [unfold WALL; destruct Hr as [<-|[]]; right; right; left; reflexivity| exact X]. }
    assert (DK03 : L5SAR.dk L ar LB FF sp 18432 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3).
    assert (WSALL : PMKA.wapp WALL).
    { unfold WALL. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct TAPP as (_ & [X|X] & _); [left; lia| right; lia]|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]| apply PMKA.wapp_nil]. }
    apply (KONT fx3 R3 M3 model4 LK2 Aw2 (PM.SRC qc de rem) (PM.STRM (g + c) eg 2)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ match goal with H : getr R3 (reg ?x) = Z_to_bv 64 (bv_unsigned (getr R (reg ?x))) |- getr R3 (reg ?x) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
      destruct Hk.
    + apply (OWK M3); [| exact DK03| apply (L5SAR.astk_grows ar M2 M3 sp 18432 ASTK2 MGM3)| apply (PMKA.agA_obj L ar LB FF sp 18432 WALL M M3 EK03 WSALL FRB os 296 AO OUTO3)].
      apply (L5SAR.ek_W L ar LB FF sp 18432 WS WALL M M3 EK03). intros a Oq r0 Hr X. apply (Oq r0); [apply INWS; exact Hr| exact X].
    + assert (TJ3 : forall a v, ois <= a -> a + 4 <= ois + 272 -> L5.u32_at RSEGS M3v a v -> L5.u32_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u32_at_vis _ M3 a v ltac:(rewrite HID3 || idtac; apply JAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      assert (WS23 : PMKA.wapp [(ois + 152, 4)]).
      { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]| apply PMKA.wapp_nil]. }
      apply (PMASK.iss_st_updA M2 M3 ois str (g + c) eg 0 2 IA2); [lia| lia| | | | exact MGM3| | | right; reflexivity].
      -- apply (PMKA.agA_obj L ar LB FF sp 18432 _ M2 M3 EK23 WS23 FRB ois 152 ltac:(destruct AOI as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia])).
         intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
      -- apply (PMKA.agA_obj L ar LB FF sp 18432 _ M2 M3 EK23 WS23 FRB (ois + 156) 116 ltac:(destruct AOI as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia])).
         intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
      -- apply (PMKA.agsh_obj L ar LB FF sp 18432 _ M2 M3 EK23 WS23 FRB (ois + 152) 4 ltac:(destruct AOI as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia])).
      -- intros c0 n0 p0 E. subst str.
         assert (SIN : In (p0, c0) LB) by (apply SOWN; cbn; left; reflexivity).
         apply (PMKA.agA_blk L ar LB FF sp 18432 _ M2 M3 EK23 WS23 BRB p0 c0 SIN).
         intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
         destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ p0 c0 _ 272 HH SIN AOI) as [Z1|Z1]; lia.
      -- apply TJ3; [lia|lia| assumption].
    + unfold PMSP.src_step, PM.unread. cbn. lia.
    + split; [| exists p, c; split; [rewrite L5SAR.r11; exact A11|];
                split; [rewrite L5K.rl10; match goal with H : getr R3 (reg 10) = _ |- _ => exact H | _ => rewrite (KS3 10%nat) by inl; exact A10c end|];
                apply (L5C.defined_agree M2 M3 p c); [intros i Hi; rewrite FR3; [reflexivity| lia|]; intros [X|X]; [clear - X Hi Dq2 T4 SLO C0; lia| clear - X Hi Dq1 Dq2 TAO C0; lia]| exact D2]].
      unfold PMPS.fill_res. split; [reflexivity|]. exists c. cbn [PM.sm_g PM.sm_st PM.sm_eg].
      split; [rewrite L5K.rl10; match goal with H : getr R3 (reg 10) = _ |- _ => exact H | _ => rewrite (KS3 10%nat) by inl; exact A10c end|].
      split; [unfold PM.CHUNK; lia|]. split; [lia|]. split; [intros _; split; [unfold PM.CHUNK in *; exact Hcm| unfold PM.CHUNK; cbn [PM.sm_st]; rewrite (proj2 (Z.ltb_lt c 16384)) by lia; reflexivity]| intros X; discriminate X].
    + apply (L5SAR.ahpres_of L ar LB FF sp 18432 _ M M3).
      * apply (L5SAR.ek_W L ar LB FF sp 18432 _ WALL M M3 EK03). intros a Oq r0 Hr X. apply (Oq r0); [unfold WALL; destruct Hr as [<-|[<-|[<-|[]]]]; unfold PGS.W_srcG, PGS.W_srcfG; cbn [app PM.sr_qc]; [right; left; reflexivity| right; right; right; right; left; reflexivity| right; right; left; reflexivity]| exact X].
      * pose proof (L5SAR.astk_grows ar M2 M3 sp 18432 ASTK2 MGM3) as (_ & _ & _ & _ & DS3 & _). exact DS3.
      * apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3); [apply (L5SAR.dk_trans L ar LB FF sp 18432 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]|].
        apply L5SAR.dk_grows. exact MGM3.
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC2.
    + exact INCA2.
    + exact AM4.
    + exact HH4. }
Qed.

End WithHeap.
End PGSFBTA.
