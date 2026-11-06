(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "pair"; "prod"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "SVar"; "sprop_below"; "swf"; "holds"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "land"; "modulo"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "SSa_S"; "F_sgen"; "SS0"; "SSb_S"; "V_NS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "neededx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "J_alloc_preT"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma round_up_ge' : ltac2:(tb__ "0|1|
S0S0S17Z0R1A2S2S16R3S1dR3R2A2M0A2S16G0S1cS18R3R2A2Z1A2A2A2F_;Fm;Fz;").
Proof.
  intros z m Hm. unfold round_up. pose proof (Z.div_mod (z + m - 1) m ltac:(lia)) as D. pose proof (Z.mod_pos_bound (z + m - 1) m Hm) as B. nia.
Qed.
Lemma round_up_mod : ltac2:(tb__ "0|1|
S0S0S17Z0M0R1A2S1S0S1aS1dR3R2A2R2A2G0A3F_;Fm;Fz;").
Proof. intros z m Hm. unfold round_up. apply Z_mod_mult. Qed.
Lemma land_page : ltac2:(tb__ "0|0|
S0S2S16Z0R1A2S17R1S1bZ2Z40A2A2A2S1S0S19R2Zfffffffffffff000A2S1cR2S1aR2Z1000A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_high_mask by lia. reflexivity. Qed.
Lemma round_up_land : ltac2:(tb__ "0|1|
S0S16Z0R1A2S17S18R2ZfffM0A2S1bZ2Z40A2A2S1S0S1dR3Z1000A2S19S18R3G0A2Zfffffffffffff000A2A3F_;F_;Fx;").
Proof.
  intros x H0 H1. rewrite land_page by lia. unfold round_up.
  pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D. replace (x + 4096 - 1) with (x + 4095) by lia. lia.
Qed.

Lemma SPA_add_facts' : ltac2:(tb__ "0|0|
S3S2bA1S15SeS20S3ScA1S3S29Q40A1A1S1eS2aScS12R5A1R3A3S1S4S28ScS10S13S1fR5A1A1A1R4A3S5A3S14R9R8R6R7R4R3A6S14RaR9S2dR6R7A2R8R5R4A6F_;F_;F_;Fw;Ftp;FFs;FA;Frho;FJx;Fsegs;").
Proof. intros segs Jx rho A Fs tp w HF HB [Hsm HJ]. split; [exact (smatchA_add_facts segs rho tp Fs A w Hsm HF HB) | exact HJ]. Qed.

Section SEC.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S31VAInv;VW;Vst;VA;VKc;SfPcA1A6").

Hypothesis Wa : ltac2:(tb__ "0|0|
S1S4S11S22VW;Vst;Vtmax;A3A1S5A3").
Hypothesis Da : ltac2:(tb__ "0|6|
S1SbS9S3S9SdSdA2M0A1M1S3ScA1M2A2M3A1S2cS1fS21VW;Vst;Vtmax;Z8M4A4A1S22VW;Vst;Vtmax;A3A2SaG3S8G1G2S6G0S8SdSdS30G4A1SfS26A1A4M5S6G0G5S7G0A1A3A3S7ScA1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S1S4S11S25VW;Vst;Vtmax;A3A1S5A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S1S4S28ScS10S2fA1S23A3S5A3").

Theorem sec_inst : ltac2:(tb__ "0|0|
S34S32SeS3S29Q40A1A1S1eSeS2eVW;Vst;A2S35VW;Vst;A2S33R7A1S14Vsegs;S27VW;Vst;R9R8R7A5S21VW;Vst;Vtmax;Z8A4R4R6R5A6S14Vsegs;S27VW;Vst;RaR9R8A5S24VW;Vst;Vtmax;A3R5R7R6A6F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE HW HUS HKc H.
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN |- *.
  assert (E141 : rw rhoE 141%positive = Z_to_bv 64 (secneeded nv)). { rewrite <- (Hagw 141%positive) by (unfold GW; lia). reflexivity. }
  assert (E142 : rw rhoE 142%positive = Z_to_bv 64 (secmapsize nv)). { rewrite <- (Hagw 142%positive) by (unfold GW; lia). reflexivity. }
  assert (E145 : rw rhoE 145%positive = Z_to_bv 64 (ag_pab (aa_geom A))). { rewrite <- (Hagw 145%positive) by (unfold GW; lia). reflexivity. }
  assert (E146 : rw rhoE 146%positive = Z_to_bv 64 (aa_ptr_committed A / 8)). { rewrite <- (Hagw 146%positive) by (unfold GW; lia). reflexivity. }
  assert (E147 : rw rhoE 147%positive = Z_to_bv 64 (Z.of_nat (length (aa_sec A)))). { rewrite <- (Hagw 147%positive) by (unfold GW; lia). reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (Erm : rm rhoE = rm rho). { apply functional_extensionality. intros a. symmetry. exact (Hagm a). }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_fam tmax 8)) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p Hp). }
  assert (Hnv : 64513 <= nv < 2 ^ 39).
  { pose proof (HFX (SPUle (SLit (rzf_lo 8)) (SVar 12)) ltac:(apply in_or_app; right; unfold F_fam; cbn; tauto)) as F. cbn [holds eval rzf_lo] in F.
    rewrite E12, u64_lit in F by lia. lia. }
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof HG as HG0.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21. pose proof G24 as ACV.
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CIw & _). unfold IMG_LO, IMG_HI in TI, CIw.

  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_mod nv 8 ltac:(lia)) as RM1.
  pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2. pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2.
  unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BNS : 68616 <= secneeded nv < 2 ^ 39 + 4104 /\ secneeded nv mod 8 = 0).
  { rewrite NS. split; [lia|]. rewrite Z.add_mod, RM1 by lia. reflexivity. }
  assert (BMS : secneeded nv + 4096 <= secmapsize nv <= secneeded nv + 8191 /\ secmapsize nv mod 4096 = 0 /\ secmapsize nv < 2 ^ 40).
  { rewrite MS. split; [lia|]. split; [rewrite Z.add_mod, RM2 by lia; reflexivity | lia]. }

  assert (ENX : eval rhoE (neededx 8) = eval rhoE (SVar V_NS)).
  { replace (neededx 8) with (SAlu ALU_ADD rup8 (SLit 4096)) by reflexivity. unfold rup8. cbn [eval]. unfold V_NS. rewrite E141. rewrite E12. apply bv_eq.
    rewrite add_val, and_val, add_val, !u64_lit by lia. rewrite (Z.mod_small (nv + 7)) by lia.
    change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia. change (2 ^ 3) with 8.
    rewrite NS. unfold round_up. replace (nv + 8 - 1) with (nv + 7) by lia.
    pose proof (Z.div_mod (nv + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 7) 8 ltac:(lia)). rewrite Z.mod_small; lia. }
  assert (H1 : SPA segs (JG W st A Kc rho) (SSa W st tmax) rhoE tp w).
  { unfold SSa. eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H].
    constructor; [exact ENX|]. constructor; [exact ENX|]. constructor. }
  clear H HsmA.

  destruct HRest as (Hsep & _ & _ & Hsec & _ & _ & _ & HTH & HMI). unfold thread_inv in HTH. destruct HTH as [_ HTS].
  destruct Hsec as (_ & _ & SC2 & SC3 & SC45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).

  pose proof (dyn_ok_big _ _ _ SC45 ltac:(unfold kPtrArrayReserve; clear; lia)) as SC4. destruct SC45 as [_ (_ & _ & SC5 & _ & _)]. unfold IMG_HI in SC4.
  destruct HMI as (HMIc & HMIp & HMIe).
  assert (IMG : forall z, z < 0x646000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG0 | exact Hz]. }
  assert (CI : forall a k v, a + Z.of_nat k <= 0x646000 -> cell_ok (maskv (fs_footb (aa_geom A)) (view segs (rm rhoE))) (mkACell a k v) ->
               cell_ok (view segs (rm rhoE)) (mkACell (0 + a) k v)).
  { intros a k v Ha Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc, Hj |- *. rewrite Z.add_0_l. rewrite IMG in Hc; [exact Hc | lia]. }
  unfold SEC_INST in I1, I2, I3, I4, I5, I6, I7, I8, I9.
  assert (C1 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xeddd8) 8 PG)) by (apply CI; [cbn; lia | exact I1]).
  assert (C2 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xedde0) 8 (ag_pab (aa_geom A)))) by (apply CI; [cbn; lia | exact I2]).
  assert (C3 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xedde8) 8 (ag_pab (aa_geom A)))) by (apply CI; [cbn; lia | exact I3]).
  assert (C4 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xeddf0) 8 kPtrArrayReserve)) by (apply CI; [cbn; lia | exact I4]).
  assert (C5 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xede08) 8 (aa_ptr_committed A / 8))) by (apply CI; [cbn; lia | exact I5]).
  assert (C6 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xede10) 8 (Z.of_nat (length (aa_sec A))))) by (apply CI; [cbn; lia | exact I6]).
  assert (C8 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xee040) 4 0)) by (apply CI; [cbn; lia | exact I8]).

  pose proof (Forall_inv HMIc) as HMRN. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HMIc))))) as HSAN.
  assert (C9 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0x173661) 1 1)) by (apply CI; [cbn; lia | exact HMRN]).
  assert (C10 : cell_ok (view segs (rm rhoE)) (mkACell (0 + 0xe9b28) 8 0x1a36f)) by (apply CI; [cbn; lia | exact HSAN]).

  assert (PRES : forall off, 2768 <= off < 3168 -> wok_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = true
                                       /\ exists x, rd_of segs (rm rhoE) (Z_to_bv 64 (ag_thread (aa_geom A) + off)) = Some x).
  { intros off Hoff. destruct (HTS (ag_thread (aa_geom A) + off) ltac:(lia)) as [b Hb].
    rewrite maskv_out in Hb by (apply fs_footb_thread; [exact HG0 | lia]). rewrite view_in in Hb by lia.
    eapply wok_rd_off_image2; [| |exact Hb]; [clear TI CIw; lia | clear CIw; lia]. }

  assert (Hhigh : holds rhoE F_sp_high) by (apply HFX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; cbn; tauto).
  pose proof (proj1 H1) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  destruct (sw_range_gen _ rhoE _ _ sw_s1 Hsm1 ltac:(cbn; left; reflexivity) eq_refl Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoE sw_s1)) by (rewrite (sw_lo_gen rhoE sw_s1 eq_refl); exact Htop).
  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
    assert (Hp' : In p (unwind_factsS W st)).
    { destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp). }
    apply HFX. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp'. }

  assert (H2 : SPA segs (JG W st A Kc rho) (SSb W st tmax) rhoE tp w).
  { unfold SSb. change (SSb_S W st tmax) with
      (let S := ax_S (SSa W st tmax) in mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj N_sec) (ss_facts S) NW2 (ss_lenient S)).
    eapply SPA_carve_list; [exact H1 | exact Wb | cbv; discriminate | | |].
    -
      unfold N_sec. unfold vT. unfold SEC_INST, ERRNO_A, PG, kPtrArrayReserve.
      repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: match goal with
           | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; rewrite Z.add_0_l; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
           | |- forall off, _ -> wok_of _ _ _ = true /\ _ => intros off Hoff; apply PRES; lia
           | |- cells_in_view _ _ _ [] => unfold cells_in_view; apply Forall_nil
           | _ => idtac end.

      1: { unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
           - exact (civ_cell rhoE (rm rhoE) 0 0xeddd8 8 PG (SLit 4096) C1 eq_refl ltac:(lia) ltac:(lia)).
           - exact (civ_cell rhoE (rm rhoE) 0 0xedde0 8 (ag_pab (aa_geom A)) (SVar V_PAB) C2 ltac:(cbn [eval]; unfold V_PAB; rewrite E145; reflexivity) ltac:(lia) ltac:(lia)).
           - exact (civ_cell rhoE (rm rhoE) 0 0xedde8 8 (ag_pab (aa_geom A)) (SVar V_PAB) C3 ltac:(cbn [eval]; unfold V_PAB; rewrite E145; reflexivity) ltac:(lia) ltac:(lia)).
           - exact (civ_cell rhoE (rm rhoE) 0 0xeddf0 8 kPtrArrayReserve (SLit (2 ^ 23)) C4 eq_refl ltac:(lia) ltac:(lia)).
           - exact (civ_cell rhoE (rm rhoE) 0 0xede08 8 (aa_ptr_committed A / 8) (SVar V_NRES) C5 ltac:(cbn [eval]; unfold V_NRES; rewrite E146; reflexivity) ltac:(lia) ltac:(lia)).
           - exact (civ_cell rhoE (rm rhoE) 0 0xede10 8 (Z.of_nat (length (aa_sec A))) (SVar V_NCH) C6 ltac:(cbn [eval]; unfold V_NCH; rewrite E147; reflexivity) ltac:(lia) ltac:(lia)). }
      1: { unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
           exact (civ_cell rhoE (rm rhoE) 0 0xee040 4 0 (SLit 0) C8 eq_refl ltac:(lia) ltac:(lia)). }
      1: { unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
           exact (civ_cell rhoE (rm rhoE) 0 0xe9b28 8 0x1a36f (SLit 0x1a36f) C10 eq_refl ltac:(lia) ltac:(lia)). }
      1: { unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
           exact (civ_cell rhoE (rm rhoE) 0 0x173661 1 1 (SLit 1) C9 eq_refl ltac:(lia) ltac:(lia)). }
    -
      cbn [ss_objs ax_S SSa SSa_S ax_setS]. unfold N_sec. cbn [map carve_obj]. unfold carved, vT, SEC_INST, ERRNO_A.
      unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
             O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
      unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS. unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      repeat (apply Forall_cons;
        [ apply Forall_cons;
          [ unfold ranges_disjoint; rewrite ?obj_range_mk by (clear; lia); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (clear -G5 G6 ACV; lia);
            clear -SW0 SW1 SW2 SW3 G5 G6 ACV; cbn [fst snd] in *; lia
          | apply Forall_app; split;
            [ apply Forall_app; split;
              [ eapply Forall_impl; [|exact LNK]; intros [ob olo ohi ocs od] (B & L & Hh); cbn [ob_base ob_lo ob_hi] in B, L, Hh; subst olo ohi;
                unfold ranges_disjoint; rewrite !obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 ACV B; lia | clear - G5 G6 G8 G9 G24 ACV B TI; lia | clear - G5 G6 G8 G9 G24 ACV B CIw; lia | clear - G5 G6 G8 G9 G24 ACV B G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 ACV B; lia | clear - G5 G6 G8 G9 G24 ACV B TI; lia | clear - G5 G6 G8 G9 G24 ACV B CIw; lia | clear - G5 G6 G8 G9 G24 ACV B G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 ACV B; lia | clear - G5 G6 G8 G9 G24 ACV B TI; lia | clear - G5 G6 G8 G9 G24 ACV B CIw; lia | clear - G5 G6 G8 G9 G24 ACV B G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ])
              | repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]) ]
            | repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]) ] ] | ]).
      apply Forall_nil.
    -
      unfold N_sec. cbn [map carve_obj pairwise_disjoint]. unfold carved, vT, SEC_INST, ERRNO_A.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?u64_lit by (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]); (first [ clear - G5 G6 G8 G9 G24 ACV; lia | clear - G5 G6 G8 G9 G24 ACV TI; lia | clear - G5 G6 G8 G9 G24 ACV CIw; lia | clear - G5 G6 G8 G9 G24 ACV G19; lia | clear TI CIw G19; lia | clear CIw G19; lia | clear TI G19; lia | clear TI CIw; lia | lia ]). }
  clear H1.

  unfold SS0. apply SPA_add_facts'; [|exact FB|exact H2].
  pose proof (proj1 H2) as (Hsm2 & _). unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm2.
  destruct (sw_range_gen _ rhoE _ _ sw_s1 Hsm2 ltac:(cbn; left; reflexivity) eq_refl Hhigh) as (SWa & SWb & SWc). clear Hsm2 H2.
  assert (SPC : 140735332483072 <= bv_unsigned (rw rhoE 10%positive)) by (rewrite <- SWb; lia).
  pose proof (urange (rw rhoE 10%positive)) as U10.
  assert (EMSX : bv_unsigned (eval rhoE msx) = secmapsize nv).
  { unfold msx, V_NS. cbn [eval]. rewrite E141. rewrite add_val, and_val, add_val, !u64_lit by lia. rewrite (Z.mod_small (secneeded nv + 4095)) by lia.
    rewrite <- round_up_land by lia. rewrite MS. rewrite Z.mod_small by lia. reflexivity. }
  unfold kPtrArrayReserve, kPtrArrayCommit in SC2, SC3, SC5.
  assert (HNRES : 0 <= aa_ptr_committed A / 8 <= 2 ^ 20) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HNCH : Z.of_nat (length (aa_sec A)) <= aa_ptr_committed A / 8) by (apply Z.div_le_lower_bound; lia).
  clear - E141 E142 E145 E146 E147 BNS BMS EMSX SC4 SC5 HNRES HNCH U10 SPC ACV Hnv NS MS.
  unfold F_sgen, V_NS, V_MS, V_PAB, V_NRES, V_NCH. unfold IMG_HI, kPtrArrayReserve.
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E141, ?E142, ?E145, ?E146, ?E147.
  -   rewrite u64_lit by lia. split; [lia|]. change (2 ^ 3) with 8. exact (proj2 BNS).
  - rewrite !u64_lit by lia. lia.
  - rewrite !u64_lit by lia. lia.
  -   rewrite u64_lit by lia. split; [lia|]. change (2 ^ 12) with 4096. exact (proj1 (proj2 BMS)).
  - rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  - rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  - rewrite !u64_lit by lia. lia.
  -   cbn [branch_taken]. replace (eval rhoE msx) with (Z_to_bv 64 (secmapsize nv)) by (apply bv_eq; rewrite u64_lit by lia; symmetry; exact EMSX).
    unfold bv_eqb. apply Z.eqb_refl.
  - rewrite !u64_lit by lia. lia.
  - rewrite !u64_lit by lia. lia.
  - rewrite !u64_lit by lia. lia.
  - rewrite !u64_lit by lia. lia.
  - rewrite u64_lit by lia. rewrite EMSX. lia.
  - rewrite EMSX. rewrite u64_lit by lia. lia.
  -   intros E. cbn [branch_taken] in E. unfold bv_eqb in E. rewrite add_val in E.
    replace (bv_unsigned (Z_to_bv 64 (-2504))) with (2 ^ 64 - 2504) in E by reflexivity. rewrite (u64_lit 0) in E by lia.
    replace (bv_unsigned (rw rhoE 10%positive) + (2 ^ 64 - 2504)) with ((bv_unsigned (rw rhoE 10%positive) - 2504) + 1 * 2 ^ 64) in E by lia.
    rewrite Z.mod_add in E by lia. rewrite Z.mod_small in E by lia. apply Z.eqb_eq in E. lia.
Qed.
End SEC.
