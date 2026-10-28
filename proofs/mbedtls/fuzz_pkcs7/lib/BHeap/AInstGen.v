(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AKinvM AVmScar AInstDepot AInstPop AVstT.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AInstGen () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinv.kinv"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.Kd"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstPop.vp"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.sane"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vranges_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_eb"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vnb"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstPop.RES_POP"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_cb20"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_cb23"; "Corelib.Init.Datatypes.list"; "ARUN_1.InstGen.CSg"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.hull64"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_got"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"; "stdpp.bitvector.definitions.bv"; "ARUN_1.InstGen.Kg"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.fixrw_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinvM.scar_site"; "ARUN_1.InstGen.Gn"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.InstGen.Gs"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "Stdlib.Lists.List.fold_right"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vst"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_lazy"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_eager"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Peano.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.HKv"; "ARUN_1.InstGen.vexit"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "ARUN_1.unit_if"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "Corelib.Init.Datatypes.fst"; "ARUN_1.H.HB"; "ARUN_1.H.UAh"; "Corelib.Init.Datatypes.snd"; "ARUN_1.H.FAh"; "ARUN_1.H.UOKh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "ARUN_1.H.Kh"; "ARUN_1.R_gen"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "ARUN_1.H.CSh"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"].

Section ARUN_1. Context {hAR : arun}.
Definition RES_GEN : Z := RES_POP + RES_DEPOT.

(* [comment removed for export] *)
#[using="Type"] Lemma kinv_iff : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "PAL,$0.PP,P,$1.SpPQ,P,$1.SpPK,P,$2.SpPK',P,$2.SpP,Px,$1.P,A1.R4.R1.A1.R6.R2.P,Pmo,$2.P,A1.R3.R1.A1.R5.R2.P,Pmo,$2.P,A1.R5.R1.A1.R5.R2.P,(3.VhAR,R8.R7.R5.)(3.VhAR,R9.R7.R5.)")
(* [comment removed for export] *).
Proof.
  intros AL P Q K K' QP K'K KK' KI. split.
  - intros mo Hm. apply (ki_halted KI). apply K'K. exact Hm.
  - intros mo Hm. apply (ki_top KI). apply K'K. exact Hm.
  - intros mo acc Hm OK. destruct (ki_mat KI mo acc (K'K mo Hm) (acc_ok_mono AL _ _ acc QP OK)) as (mo' & E & HK' & MM).
    exists mo'. split; [exact E|]. split; [apply KK'; exact HK'| exact MM].
Qed.

Section InstGen.
  Variable AL : asan_layout.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis IML : al_img_lo AL <= 0x10000.
  Hypothesis IMH : al_img_hi AL = 0x65f000.
  Hypothesis GOT64 : al_img_lo AL + 64 <= al_got AL /\ al_got AL + 128 <= al_img_hi AL /\ al_got AL mod 8 = 0.
  Hypothesis GSB64 : al_img_lo AL + 64 <= al_gsb AL /\ al_gsb AL + 128 <= al_img_hi AL /\ al_gsb AL mod 8 = 0.

  Variable v0 : vst.
  Variable H : Z * Z.
  Variables UA FAA : Z.
  Variables nb0 bl0 : list Z.
  Hypothesis VR0 : vranges_ok AL v0.
  Hypothesis VWF0 : vwf AL v0.
  Hypothesis HH : In H (v_hulls v0).
  Hypothesis H68 : 0x65f000 <= fst H.
  Hypothesis HU : fst H <= UA /\ UA + 2^18 <= fst H + snd H /\ UA mod 4096 = 0.
  Hypothesis HF : fst H <= FAA /\ FAA + 2^18 <= fst H + snd H /\ FAA mod 4096 = 0.
  Variable UOK : Prop.     (* [comment removed for export] *)
  Hypothesis UF : UOK -> UA + 2^18 <= FAA \/ FAA + 2^18 <= UA.
  Hypothesis APT_U : UOK -> forall t, In t (v_tr v0) -> UA + 2^18 <= t_lo t \/ t_hi t <= UA.
  Hypothesis APT_F : forall t, In t (v_tr v0) -> FAA + 2^18 <= t_lo t \/ t_hi t <= FAA.
  Hypothesis UUN : UOK -> v_unit v0 UA (2^18).   (* [comment removed for export] *)
  Hypothesis FUN : v_unit v0 FAA (2^18).         (* [comment removed for export] *)
  Hypothesis SLACK : v_eb v0 + 4096 * vnb v0 + RES_GEN <= VLIMIT.
  Hypothesis CB20 : v_cb20 v0 < J20.
  Hypothesis CB23 : v_cb23 v0 + (2^20 / 2^23 + 2) < J23.
  Hypothesis HC : In H (v_cover v0).             (* [comment removed for export] *)

  Local Notation vp := (AInstPop.vp v0 UA FAA).
  Local Notation Kp := (AInstPop.Kp AL v0 UA FAA UOK).
  Local Notation CSp := (AInstPop.CSp AL v0 UA FAA).

  Definition Kg (u f : option bool) (nb bl : list Z) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "(4.(5.(6.(7.$8.)O5.(9.$8.$:.)))(4.(5.(6.(7.$8.)O4.(9.$8.$:.)))(4.P,(6.(7.$8.)O5.(9.$8.$;.))VUOK,(<.VhAR,VAL,(=.Vv0,VUA,VFAA,O5.O4.)Vnb0,Vbl0,O3.O2.O1.))))")
(* [comment removed for export] *).
  Definition Dnew (nb bl : list Z) (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "(>.(?.$1.Lb,$1.(4.(10.$1.R1.(11.$1.(12.$1.Vnb0,)O3.))(4.(13.VhAR,(14.+2.+14.)R1.)(4.(15.R1.O1.)(16.O1.(17.R1.(14.+2.+14.)))))))(?.$1.Lb,$1.(4.(10.$1.R1.(11.$1.(12.$1.Vbl0,)O2.))(4.(13.VhAR,(14.+2.+17.)R1.)(4.(15.R1.O1.)(16.O1.(17.R1.(14.+2.+17.))))))))")
(* [comment removed for export] *).
  Definition CSg (u f : option bool) (nb bl : list Z) (x : Z) : Prop := CSp u f x \/ Dnew nb bl x.
  Definition Gn (u f : option bool) (nb bl : list Z) : Prop := nb = nb0 /\ bl = bl0.
  Definition Gs (u f : option bool) (nb bl : list Z) : Prop := bl = bl0 /\ (nb = nb0 \/ exists x, nb = nb0 ++ [x]).

  #[using="hAR AL v0 H FAA VWF0 HH H68 HU HF"] Lemma HU0 : 0 <= UA.  Proof. dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH). lia. Qed.
  #[using="hAR AL v0 H UA VWF0 HH H68 HU HF"] Lemma HF0 : 0 <= FAA. Proof. dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH). lia. Qed.
  #[using="SLACK"] Lemma SLACK_P : v_eb v0 + 4096 * vnb v0 + RES_POP <= VLIMIT.
  Proof. unfold RES_GEN, RES_DEPOT in SLACK. clear - SLACK. lia. Qed.
  (* [comment removed for export] *)
  Ltac pfacts := first [ exact ASB | exact IML | exact IMH | exact GOT64 | exact GSB64 | exact VR0 | exact VWF0 | exact HH | exact H68 | exact HU | exact HF
                       | exact UF | exact APT_U | exact APT_F | exact UUN | exact FUN | exact SLACK_P | exact HC | eassumption ].

  (* [comment removed for export] *)
  #[using="hAR H VR0 VWF0 HH H68 HU HF"] Lemma vp_facts : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pf,(7.$8.)(4.(18.VAL,(=.Vv0,VUA,VFAA,R2.R1.))(4.(15.(17.(19.(=.Vv0,VUA,VFAA,R2.R1.))(1:.+1000.(1;.(=.Vv0,VUA,VFAA,R2.R1.))))(17.(17.(19.Vv0,)(1:.+1000.(1;.Vv0,)))$1<.))(4.(6.$1.(1=.(=.Vv0,VUA,VFAA,R2.R1.))(1=.Vv0,))(6.$1.(1>.(=.Vv0,VUA,VFAA,R2.R1.))(1>.Vv0,)))))")
(* [comment removed for export] *).
  Proof.
    pose proof HU0. pose proof HF0.
    intros [[|]|] [[|]|]; cbn [AInstPop.vp]; unfold vF, vU; rewrite ?vnb_add_sub; cbn [v_eb v_cb20 v_cb23 v_add_sub]; unfold RES_POP;
      rewrite ?vnb_add_sub;
      (split; [repeat (apply vranges_ok_sub; [| lia| lia]); exact VR0|]); (split; [lia|]); split; reflexivity.
  Qed.
  #[using="hAR H VR0 VWF0 HH H68 HU HF"] Lemma vp_VR : forall u f, vranges_ok AL (vp u f). Proof. intros u f. exact (proj1 (vp_facts u f)). Qed.
  #[using="hAR AL H VR0 VWF0 HH H68 HU HF SLACK"] Lemma vp_SLACK : forall u f, v_eb (vp u f) + 4096 * vnb (vp u f) + RES_DEPOT <= VLIMIT.
  Proof. intros u f. pose proof (proj1 (proj2 (vp_facts u f))). unfold RES_GEN in SLACK. lia. Qed.
  #[using="hAR AL H VR0 VWF0 HH H68 HU HF CB20"] Lemma vp_CB20 : forall u f, v_cb20 (vp u f) < J20. Proof. intros u f. rewrite (proj1 (proj2 (proj2 (vp_facts u f)))). exact CB20. Qed.
  #[using="hAR AL H VR0 VWF0 HH H68 HU HF CB23"] Lemma vp_CB23 : forall u f, v_cb23 (vp u f) + (2^20 / 2^23 + 2) < J23. Proof. intros u f. rewrite (proj2 (proj2 (proj2 (vp_facts u f)))). exact CB23. Qed.

  (* [comment removed for export] *)
  Definition nz (o : option bool) : option bool := match o with Some false => None | _ => o end.
  #[using="Type"] Lemma CSp_nz : forall u f x, CSp u f x <-> CSp (nz u) (nz f) x.
  Proof. intros [[|]|] [[|]|] x; cbn [nz]; unfold AInstPop.CSp; split; intros A; decompose [and or] A; auto; try discriminate. Qed.
  #[using="Type"] Lemma vp_nz : forall u f, vp u f = vp (nz u) (nz f).
  Proof. intros [[|]|] [[|]|]; reflexivity. Qed.
  #[using="Type"] Lemma CSp_vp : forall u f x, CSp u f x <-> vcs AL (vp u f) x.
  Proof.
    intros u f x. rewrite CSp_nz, vp_nz. destruct u as [[|]|], f as [[|]|]; cbn [nz AInstPop.vp]; unfold AInstPop.CSp, vF, vU; rewrite ?vcs_sub.
    all: split; intros A; decompose [and or] A; auto 6; try discriminate.
  Qed.
  #[using="GOT64 GSB64 H HU HF"] Lemma CSg_CSd : forall u f nb bl x, CSg u f nb bl x <-> CSd AL (vp u f) nb0 bl0 nb bl x.
  Proof. intros u f nb bl x. unfold CSg, CSd, Dnew. rewrite CSp_vp. tauto. Qed.

  #[using="Type"] Lemma Kg_nb0 : forall u f mo, Kg u f nb0 bl0 mo <-> Kp u f mo.
  Proof.
    intros u f mo. unfold Kg, Kd. split.
    - (intros dd_H; ddestruct dd_H as (NU & NF & UK & [(_ & _ & K)|[(x & E & _)|[(y & _ & E & _)|(x & y & E & _)]]])); [| exfalso; symmetry in E; exact (app_cons_neq _ _ E)..].
      destruct u as [[|]|], f as [[|]|]; cbn [AInstPop.vp AInstPop.Kp] in *; try exact K; try exact (conj (UK eq_refl) K); exfalso; first [apply NF; reflexivity| apply NU; reflexivity].
    - intros K. destruct u as [[|]|], f as [[|]|]; cbn [AInstPop.vp AInstPop.Kp] in *; try contradiction;
        lazymatch type of K with UOK /\ _ => destruct K as [OK K] | _ => idtac end;
        (split; [discriminate|]); (split; [discriminate|]); (split; [intros E; first [exact OK| discriminate E]|]); left; auto.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma CSg_nb0 : forall u f x, CSg u f nb0 bl0 x -> CSp u f x.
  Proof. intros u f x [A|[(b & Hb & _)|(b & Hb & _)]]; [exact A| |]; rewrite skipn_all in Hb; destruct Hb. Qed.
  #[using="ALWF IML IMH GOT64 GSB64 H VWF0 HH H68 HU HF"] Lemma CSg_range : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pf,(7.$8.)Pnb,(1?.$1.)Pbl,(1?.$1.)Px,$1.P,(20.R5.R4.R3.R2.R1.)(4.(4.(15.=R2.)(16.R2.(14.+2.+2?.)))(4.(>.(15.(17.R2.+1.)+7???7000.)(15.+10007???8000.R2.))(4.(5.(4.(15.(21.(22.VAL,))R2.)(16.R2.(17.(21.(17.(22.VAL,)+7.))+40.))))(5.(4.(15.(21.(23.VAL,))R2.)(16.R2.(17.(21.(17.(23.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Proof.
    intros u f nb bl x [A|[(b & _ & SB & R)|(b & _ & SB & R)]]; [exact (CSp_range AL ALWF IML IMH GOT64 GSB64 v0 H UA FAA VWF0 HH H68 HU HF u f x A)| |].
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *).

    - dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). rewrite IMH in *. unfold sane in SB. aceilb. lia.
    - dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). rewrite IMH in *. unfold sane in SB. aceilb. lia.
  Qed.

  #[using="ALWF ASB IML IMH GOT64 GSB64 H VWF0 HH H68 HU HF"] Theorem G_CSOK : forall u f nb bl, cs_ok AL (CSg u f nb bl).
  Proof.
    intros u f nb bl. split; [| split; [| split]].
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *).
    - intros c Hc. dpose (CSg_range u f nb bl c Hc) as (R1 & R2 & R3 & R4). unfold shadow_of. rewrite ASB.
      pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). assert (c / 8 <= 2^47 / 8) by (apply Z.div_le_mono; lia). change (2^47 / 8) with 17592186044416 in *.
      split; [lia|]. split; [lia|]. split; [lia|]. intros Hs. pose proof (CSg_range u f nb bl _ Hs) as (S1 & S2 & _). lia.
    - intros i Hi. split; intros Hc; pose proof (CSg_range u f nb bl _ Hc) as (R1 & R2 & R3 & R4); lia.
    - intros c i Hc Hi. pose proof (CSg_range u f nb bl c Hc) as (R1 & _). dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). rewrite IMH in *.
      unfold shadow_of. rewrite ASB. pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). lia.
    - rewrite ASB. lia.
  Qed.
  #[using="ALWF IML IMH GOT64 GSB64 H VWF0 HH H68 HU HF"] Theorem G_noshadow : forall u f nb bl x, CSg u f nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  Proof. intros u f nb bl x Hx. dpose (CSg_range u f nb bl x Hx) as (_ & R & _). lia. Qed.
  #[using="Type"] Theorem G_CSmono_u : forall b f y, CSg None f nb0 bl0 y -> CSg (Some b) f nb0 bl0 y.
  Proof. intros b f y [A|A]; [left; apply P_CSmono_u; exact A| right; exact A]. Qed.
  #[using="Type"] Theorem G_CSmono_f : forall u b y, CSg u None nb0 bl0 y -> CSg u (Some b) nb0 bl0 y.
  Proof. intros u b y [A|A]; [left; apply P_CSmono_f; exact A| right; exact A]. Qed.
  #[using="Type"] Theorem G_CSmono_n : forall u f nb bl a x, CSg u f nb bl x -> CSg u f (nb ++ [a]) bl x.
  Proof.
    intros u f nb bl a x [A|[(b & Hb & SB & R)|A]]; [left; exact A| right; left| right; right; exact A].
    exists b. split; [| auto]. rewrite skipn_app. apply in_app_iff. left. exact Hb.
  Qed.
  #[using="Type"] Theorem G_CSmono_s : forall u f nb bl a x, CSg u f nb bl x -> CSg u f nb (bl ++ [a]) x.
  Proof.
    intros u f nb bl a x [A|[A|(b & Hb & SB & R)]]; [left; exact A| right; left; exact A| right; right].
    exists b. split; [| auto]. rewrite skipn_app. apply in_app_iff. left. exact Hb.
  Qed.
  #[using="Type"] Theorem G_CSUz : forall f, crange (CSg (Some true) f nb0 bl0) UA (2^18).
  Proof. intros f x Hx. left. apply P_CSUz. exact Hx. Qed.
  #[using="Type"] Theorem G_CSFz : forall u, crange (CSg u (Some true) nb0 bl0) FAA (2^18).
  Proof. intros u x Hx. left. apply P_CSFz. exact Hx. Qed.
  
  (* [comment removed for export] *)
  #[using="GOT64 GSB64 H VR0 VWF0 HH H68 HU HF"] Theorem G_KL : forall u f nb bl, kinv AL (CSg u f nb bl) (Kg u f nb bl).
  Proof.
    intros u f nb bl.
    assert (EMP : forall u' f', (u' = Some false \/ f' = Some false) -> kinv AL (CSg u' f' nb bl) (Kg u' f' nb bl)).
    { intros u' f' E. split; [(intros mo dd_H; ddestruct dd_H as (NU & NF & _))| (intros mo dd_H; ddestruct dd_H as (NU & NF & _))| (intros mo acc dd_H; ddestruct dd_H as (NU & NF & _); intros _)]; exfalso; (destruct E as [E|E]; [exact (NU E)| exact (NF E)]). }
    assert (GEN : u <> Some false -> f <> Some false -> kinv AL (CSg u f nb bl) (Kg u f nb bl)).
    { intros NU NF. apply (kinv_iff AL (CSd AL (vp u f) nb0 bl0 nb bl) _ (fun mo => (u = Some true -> UOK) /\ Kd AL (vp u f) nb0 bl0 nb bl mo)).
      - intros x Hx. apply CSg_CSd. exact Hx.
      - (intros mo dd_H; ddestruct dd_H as (_ & _ & UK & K)). exact (conj UK K).
      - intros mo [UK K]. split; [exact NU| split; [exact NF| exact (conj UK K)]].
      - pose proof (D_KL AL (vp u f) nb0 bl0 (vp_VR u f) nb bl) as KI. split.
        + intros mo [_ K]. exact (ki_halted KI mo K).
        + intros mo [_ K]. exact (ki_top KI mo K).
        + intros mo acc [UK K] OK. ddestruct (ki_mat KI mo acc K OK) as (mo' & E & K' & MM). exists mo'. auto. }
    destruct u as [[|]|]; [| apply EMP; left; reflexivity|]; (destruct f as [[|]|]; [| apply EMP; right; reflexivity|]); apply GEN; discriminate.
  Qed.

  #[using="GOT64 GSB64 H HU HF"] Theorem G_apart : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pf,(7.$8.)Pnb,(1?.$1.)Pbl,(1?.$1.)Pmo,$2.Pa,(24.&40.)Pn,(24.&40.)P,(25.R7.R6.R5.R4.R3.)P,(6.$8.(26.(27.(28.(24.&40.)(24.&40.))(29.(2:.R4.))(2;.(2:.R4.)))R3.R2.)$;.)P,(15.+10000.(2<.&40.R3.))P,(15.(17.(2<.&40.R5.)(2<.&40.R4.))(2=.VhAR,))Px,$1.P,(>.(20.R<.R;.R:.R9.R1.)(4.(15.(2>.VAL,)R1.)(16.R1.(2?.VAL,))))(5.(4.(15.(2<.&40.R8.)R2.)(16.R2.(17.(2<.&40.R8.)(2<.&40.R7.)))))")
(* [comment removed for export] *).
  Proof.
    (intros u f nb bl mo a n dd_H; ddestruct dd_H as (_ & _ & _ & K); intros RF N16 CE x Hx).
    apply (D_apart AL (vp u f) nb0 bl0 nb bl mo a n K RF N16 CE x). destruct Hx as [Hx|Hx]; [left; apply CSg_CSd; exact Hx| right; exact Hx].
  Qed.

  (* [comment removed for export] *)
  #[using="ASB IMH H VR0 HH H68 HU HF APT_U UUN SLACK"] Theorem G_LEDGER_U : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pmo,$2.P,VUOK,P,(25.(30.$8.)(30.$8.)Vnb0,Vbl0,R2.)(4.(6.$8.(26.(29.(2:.R3.))(31.&40.VUA,)(31.&40.(14.+2.+12.)))$;.)(>.(6.$8.(32.(2;.(2:.R3.))(31.&40.VUA,)(31.&40.(14.+2.+12.)))$;.)(6.$8.(26.(27.(28.(24.&40.)(24.&40.))(29.(2:.R3.))(2;.(2:.R3.)))(31.&40.VUA,)(31.&40.(14.+2.+12.)))$;.)))")
(* [comment removed for export] *).
  Proof. intros mo OK K. apply Kg_nb0 in K. eapply (P_LEDGER_U AL) in K; [exact K| pfacts ..]. Qed.
  #[using="ASB IMH H VR0 HH H68 HU HF APT_U UUN SLACK"] Theorem G_TU_commit : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pmo,$2.P,VUOK,P,(25.(30.$8.)(30.$8.)Vnb0,Vbl0,R2.)P,(6.$8.(32.(2;.(2:.R3.))(31.&40.VUA,)(31.&40.(14.+2.+12.)))$;.)(25.(9.$8.$;.)(30.$8.)Vnb0,Vbl0,(33.+32.VUA,(14.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof. intros mo OK K MC. apply Kg_nb0 in K. apply Kg_nb0. eapply (P_TU_commit AL) in K; [exact K| pfacts ..]. Qed.
  #[using="H HH H68 HU HF"] Theorem G_TU_fresh : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pmo,$2.P,VUOK,P,(25.(30.$8.)(30.$8.)Vnb0,Vbl0,R2.)P,(6.$8.(26.(27.(28.(24.&40.)(24.&40.))(29.(2:.R3.))(2;.(2:.R3.)))(31.&40.VUA,)(31.&40.(14.+2.+12.)))$;.)(25.(9.$8.$;.)(30.$8.)Vnb0,Vbl0,(34.+32.VUA,(14.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof. intros mo OK K RF. apply Kg_nb0 in K. apply Kg_nb0. eapply (P_TU_fresh AL) in K; [exact K| pfacts ..]. Qed.
  #[using="ASB IMH H VR0 HH H68 HU HF APT_U UUN SLACK"] Theorem G_ROOM_U : forall mo, UOK -> Kg None None nb0 bl0 mo -> fixrw_grantable 0x32 UA (2^18) mo.
  Proof. intros mo OK K. apply Kg_nb0 in K. eapply (P_ROOM_U AL) in K; [exact K| pfacts ..]. Qed.
  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN SLACK"] Theorem G_LEDGER_F : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pmo,$2.P,(>.(6.(7.$8.)R2.(30.$8.))(6.(7.$8.)R2.(9.$8.$;.)))P,(25.R3.(30.$8.)Vnb0,Vbl0,R2.)(4.(6.$8.(26.(29.(2:.R3.))(31.&40.VFAA,)(31.&40.(14.+2.+12.)))$;.)(>.(6.$8.(32.(2;.(2:.R3.))(31.&40.VFAA,)(31.&40.(14.+2.+12.)))$;.)(6.$8.(26.(27.(28.(24.&40.)(24.&40.))(29.(2:.R3.))(2;.(2:.R3.)))(31.&40.VFAA,)(31.&40.(14.+2.+12.)))$;.)))")
(* [comment removed for export] *).
  Proof. intros u mo Hu K. apply Kg_nb0 in K. eapply (P_LEDGER_F AL) in K; [exact K| pfacts ..]. Qed.
  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN SLACK"] Theorem G_TF_commit : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pmo,$2.P,(>.(6.(7.$8.)R2.(30.$8.))(6.(7.$8.)R2.(9.$8.$;.)))P,(25.R3.(30.$8.)Vnb0,Vbl0,R2.)P,(6.$8.(32.(2;.(2:.R3.))(31.&40.VFAA,)(31.&40.(14.+2.+12.)))$;.)(25.R5.(9.$8.$;.)Vnb0,Vbl0,(33.+32.VFAA,(14.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof. intros u mo Hu K MC. apply Kg_nb0 in K. apply Kg_nb0. eapply (P_TF_commit AL) in K; [exact K| pfacts ..]. Qed.
  #[using="H HH H68 HF"] Theorem G_TF_fresh : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pmo,$2.P,(>.(6.(7.$8.)R2.(30.$8.))(6.(7.$8.)R2.(9.$8.$;.)))P,(25.R3.(30.$8.)Vnb0,Vbl0,R2.)P,(6.$8.(26.(27.(28.(24.&40.)(24.&40.))(29.(2:.R3.))(2;.(2:.R3.)))(31.&40.VFAA,)(31.&40.(14.+2.+12.)))$;.)(25.R5.(9.$8.$;.)Vnb0,Vbl0,(34.+32.VFAA,(14.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof. intros u mo Hu K RF. apply Kg_nb0 in K. apply Kg_nb0. eapply (P_TF_fresh AL) in K; [exact K| pfacts ..]. Qed.
  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN SLACK"] Theorem G_ROOM_F : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pmo,$2.P,(>.(6.(7.$8.)R2.(30.$8.))(6.(7.$8.)R2.(9.$8.$;.)))P,(25.R3.(30.$8.)Vnb0,Vbl0,R2.)(35.+32.VFAA,(14.+2.+12.)R3.)")
(* [comment removed for export] *).
  Proof. intros u mo Hu K. apply Kg_nb0 in K. eapply (P_ROOM_F AL) in K; [exact K| pfacts ..]. Qed.

  (* [comment removed for export] *)
  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF APT_U UUN HC"] Theorem G_SCAR_U : UOK -> scar_site AL (CSg None None nb0 bl0) (Kg None None nb0 bl0) UA (2^18).
  Proof.
    intros OK. eapply scar_site_iff; [| intros mo; symmetry; apply Kg_nb0].
    eapply scar_site_mono; [| intros x Hx; apply CSg_nb0; exact Hx].
    eapply (P_SCAR_U AL); pfacts.
  Qed.
  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN HC"] Theorem G_SCAR_F : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)P,(>.(6.(7.$8.)R1.(30.$8.))(6.(7.$8.)R1.(9.$8.$;.)))(36.VhAR,VAL,(20.R2.(30.$8.)Vnb0,Vbl0,)(25.R2.(30.$8.)Vnb0,Vbl0,)VFAA,(14.+2.+12.))")
(* [comment removed for export] *).
  Proof.
    intros u Hu. eapply scar_site_iff; [| intros mo; symmetry; apply Kg_nb0].
    eapply scar_site_mono; [| intros x Hx; apply CSg_nb0; exact Hx].
    eapply (P_SCAR_F AL); pfacts.
  Qed.

  (* [comment removed for export] *)
  #[using="ASB IML IMH GOT64 GSB64 H VR0 VWF0 HH H68 HU HF SLACK"] Theorem G_T_node : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pf,(7.$8.)Pnb,(1?.$1.)Pbl,(1?.$1.)Pmo,$2.Pa,(24.&40.)P,(37.R6.R5.R4.R3.)P,(25.R7.R6.R5.R4.R3.)P,(6.$1.(38.(2<.&40.R3.)+1000.)=)P,(16.=(2<.&40.R4.))P,(15.(17.(2<.&40.R5.)(14.+2.+14.))(2=.VhAR,))P,(6.$8.(26.(27.(28.(24.&40.)(24.&40.))(29.(2:.R7.))(2;.(2:.R7.)))R6.(31.&40.(14.+2.+14.)))$;.)(4.(25.R<.R;.(27.$1.R:.(39.$1.(2<.&40.R7.)(3:.$1.)))R9.(3;.+22.R7.(14.+2.+14.)R8.))(3<.(20.R<.R;.(27.$1.R:.(39.$1.(2<.&40.R7.)(3:.$1.)))R9.)(2<.&40.R7.)(14.+2.+14.)))")
(* [comment removed for export] *).
  Proof.
    (intros u f nb bl mo a G dd_H; ddestruct dd_H as (NU & NF & UK & K); intros AAL A0 ACE RF).
    destruct (D_T_node AL ASB IML IMH (vp u f) nb0 bl0 (vp_SLACK u f) nb bl mo a G K AAL A0 ACE RF) as [K' C'].
    split; [exact (conj NU (conj NF (conj UK K')))|]. intros x Hx. apply CSg_CSd. apply C'. exact Hx.
  Qed.
  #[using="ASB IML IMH GOT64 GSB64 H VR0 VWF0 HH H68 HU HF SLACK"] Theorem G_T_store : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pf,(7.$8.)Pnb,(1?.$1.)Pbl,(1?.$1.)Pmo,$2.Pa,(24.&40.)P,(3=.R6.R5.R4.R3.)P,(25.R7.R6.R5.R4.R3.)P,(6.$1.(38.(2<.&40.R3.)+1000.)=)P,(16.=(2<.&40.R4.))P,(15.(17.(2<.&40.R5.)(14.+2.+17.))(2=.VhAR,))P,(6.$8.(26.(27.(28.(24.&40.)(24.&40.))(29.(2:.R7.))(2;.(2:.R7.)))R6.(31.&40.(14.+2.+17.)))$;.)(4.(25.R<.R;.R:.(27.$1.R9.(39.$1.(2<.&40.R7.)(3:.$1.)))(3;.+4022.R7.(14.+2.+17.)R8.))(3<.(20.R<.R;.R:.(27.$1.R9.(39.$1.(2<.&40.R7.)(3:.$1.))))(2<.&40.R7.)(14.+2.+17.)))")
(* [comment removed for export] *).
  Proof.
    (intros u f nb bl mo a G dd_H; ddestruct dd_H as (NU & NF & UK & K); intros AAL A0 ACE RF).
    destruct (D_T_store AL ASB IML IMH (vp u f) nb0 bl0 (vp_SLACK u f) nb bl mo a G K AAL A0 ACE RF) as [K' C'].
    split; [exact (conj NU (conj NF (conj UK K')))|]. intros x Hx. apply CSg_CSd. apply C'. exact Hx.
  Qed.
  #[using="H VR0 VWF0 HH H68 HU HF SLACK CB20"] Theorem G_ROOM_n : forall u f nb bl mo, Gn u f nb bl -> Kg u f nb bl mo -> exists a, anon_grantable 0x22 (2^20) mo a.
  Proof. (intros u f nb bl mo G dd_H; ddestruct dd_H as (_ & _ & _ & K)). exact (D_ROOM_n AL (vp u f) nb0 bl0 (vp_VR u f) (vp_SLACK u f) (vp_CB20 u f) nb bl mo G K). Qed.
  #[using="H VR0 VWF0 HH H68 HU HF CB23"] Theorem G_ROOM_s : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pf,(7.$8.)Pnb,(1?.$1.)Pbl,(1?.$1.)Pmo,$2.P,(3=.R5.R4.R3.R2.)P,(25.R6.R5.R4.R3.R2.)(?.(24.&40.)La,(24.&40.)(3>.VhAR,+4022.(14.+2.+17.)R4.R1.))")
(* [comment removed for export] *).
  Proof. (intros u f nb bl mo G dd_H; ddestruct dd_H as (_ & _ & _ & K)). exact (D_ROOM_s AL (vp u f) nb0 bl0 (vp_VR u f) (vp_CB23 u f) nb bl mo G K). Qed.

  (* [comment removed for export] *)
  Definition vexit (u f : option bool) (sn sb : list Z) : vst := ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "(3?.$40.$1.Lb,$1.Lv,$40.(41.R1.R2.(14.+2.+17.))(3?.$40.$1.La,$1.Lv,$40.(42.R1.R2.(14.+2.+14.)$;.)(=.Vv0,VUA,VFAA,O4.O3.)O2.)O1.)")
(* [comment removed for export] *).

  #[using="GOT64 GSB64 H VR0 VWF0 HH H68 HU HF"] Theorem Kg_exit : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pf,(7.$8.)Pnb,(1?.$1.)Pbl,(1?.$1.)Pmo,$2.P,(25.R5.R4.R3.R2.R1.)(?.(1?.$1.)Lsn,(1?.$1.)(?.(1?.$1.)Lsb,(1?.$1.)(4.(6.(1?.$1.)R6.(27.$1.Vnb0,R2.))(4.(6.(1?.$1.)R5.(27.$1.Vbl0,R1.))(4.(43.$1.(13.VhAR,(14.+2.+14.))R2.)(4.(43.$1.(13.VhAR,(14.+2.+17.))R1.)(4.(44.(12.$1.R2.)#1.)(4.(44.(12.$1.R1.)#1.)(4.(5.(6.(7.$8.)R8.(9.$8.$:.)))(4.(5.(6.(7.$8.)R7.(9.$8.$:.)))(4.P,(6.(7.$8.)R8.(9.$8.$;.))VUOK,(4.(45.VhAR,VAL,(46.R8.R7.R2.R1.)R4.)(4.(18.VAL,(46.R8.R7.R2.R1.))Px,$1.(47.(20.R9.R8.R7.R6.R1.)(48.VAL,(46.R9.R8.R3.R2.)R1.)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    (intros u f nb bl mo dd_H; ddestruct dd_H as (NU & NF & UK & K)). pose proof HU0. pose proof HF0.
    ddestruct (Kd_cases AL (vp u f) nb0 bl0 nb bl mo K) as (v & HK & EQ & CASE).
    assert (G : forall sn sb, nb = nb0 ++ sn -> bl = bl0 ++ sb -> Forall (sane (2^20)) sn -> Forall (sane (2^23)) sb -> (length sn <= 1)%nat -> (length sb <= 1)%nat ->
                 v = vexit u f sn sb -> vranges_ok AL v ->
                 exists sn sb, nb = nb0 ++ sn /\ bl = bl0 ++ sb /\ Forall (sane (2^20)) sn /\ Forall (sane (2^23)) sb
                   /\ (length sn <= 1)%nat /\ (length sb <= 1)%nat /\ u <> Some false /\ f <> Some false /\ (u = Some true -> UOK)
                   /\ HKv AL (vexit u f sn sb) mo /\ vranges_ok AL (vexit u f sn sb) /\ (forall x, CSg u f nb bl x <-> vcs AL (vexit u f sn sb) x)).
    { intros sn sb E1 E2 F1 F2 L1 L2 EV VR. dexists sn, sb. rewrite <- EV.
      split; [exact E1|]. split; [exact E2|]. split; [exact F1|]. split; [exact F2|]. split; [exact L1|]. split; [exact L2|].
      split; [exact NU|]. split; [exact NF|]. split; [exact UK|]. split; [exact HK|]. split; [exact VR|].
      intros x. rewrite CSg_CSd. apply EQ. }
    destruct CASE as [(-> & -> & ->)|[(a & -> & -> & SA & ->)|[(b & -> & -> & SB & ->)|(a & b & -> & -> & SA & SB & ->)]]].
    - apply (G [] []); rewrite ?app_nil_r; auto; apply vp_VR.
    - apply (G [a] []); rewrite ?app_nil_r; auto. unfold vN, sane in *. apply vranges_ok_eager; [apply vp_VR| lia| lia].
    - apply (G [] [b]); rewrite ?app_nil_r; auto. unfold vS, sane in *. apply vranges_ok_lazy; [apply vp_VR| lia| lia].
    - apply (G [a] [b]); auto. unfold vNS, vN, sane in *. apply vranges_ok_lazy; [apply vranges_ok_eager; [apply vp_VR| lia| lia]| lia| lia].
  Qed.
End InstGen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unit_if (o : option bool) : Z := match o with Some true => 1 | _ => 0 end.
Definition R_gen (h : ahst) (c : Z) (u f : option bool) (sn sb : list Z) (h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "(4.(6.$49.(4:.O1.)(4:.O7.))(4.Pc',$1.P,(5.(6.$1.R1.O6.))(6.$1.(4;.(4<.O1.R2.))(4;.(4<.O7.R2.)))(4.(6.$1.(4;.(4<.O1.O6.))(17.(4;.(4<.O7.O6.))(1:.(4=.O5.)$4>.)))(4.Pc',$1.P,(5.(6.$1.R1.O6.))(6.$1.(4?.(4<.O1.R2.))(4?.(4<.O7.R2.)))(4.(6.$1.(4?.(4<.O1.O6.))(17.(4?.(4<.O7.O6.))(1:.(4=.O4.)$50.)))(4.(6.(1?.$1.)(51.(52.O1.))(27.$1.(51.(52.O7.))O3.))(4.(6.(1?.$1.)(53.(52.O1.))(27.$1.(53.(52.O7.))O2.))(4.(6.(1?.$54.)(55.(56.O1.))(55.(56.O7.)))(4.(6.(1?.(28.$1.$1.))(57.(58.O1.))(57.(58.O7.)))(4.(6.$1.(59.O1.)(59.O7.))(6.$1.(5:.(58.O1.))(5:.(58.O7.)))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

Section H.
  Variable AL : asan_layout.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis IML : al_img_lo AL <= 0x10000.
  Hypothesis IMH : al_img_hi AL = 0x65f000.
  Hypothesis GOT64 : al_img_lo AL + 64 <= al_got AL /\ al_got AL + 128 <= al_img_hi AL /\ al_got AL mod 8 = 0.
  Hypothesis GSB64 : al_img_lo AL + 64 <= al_gsb AL /\ al_gsb AL + 128 <= al_img_hi AL /\ al_gsb AL mod 8 = 0.

  Variable h : ahst.
  Variable c : Z.
  Variable mo0 : Model.
  Hypothesis K0 : HK AL h mo0.
  Hypothesis B : bwf h.
  Hypothesis HV : h_havol h <= AVOL_MAX.
  Hypothesis Hc : 1 <= c <= 31.
  Hypothesis ROOMF : r_mapped_fa (h_reg h c) + kFreeArrayMapSize <= kFreeArraySize.
  (* [comment removed for export] *)
  Definition UOKh : Prop := r_mapped_user (h_reg h c) + kUserMapSize <= kUserLimit.

  Definition HB : Z * Z := (l_b6 (h_L h), kPrimHullLen).
  Definition UAh : Z := region_beg (h_L h) c + r_mapped_user (h_reg h c).
  Definition FAh : Z := fa_beg (h_L h) c + r_mapped_fa (h_reg h c).

  #[using="hAR mo0 K0"] Lemma h_VR0 : vranges_ok AL (vst_of h). Proof. exact (proj2 K0). Qed.
  #[using="mo0 K0"] Lemma h_VWF0 : vwf AL (vst_of h). Proof. exact (HK_vwf AL h mo0 K0). Qed.
  #[using="Type"] Lemma h_HH : In HB (v_hulls (vst_of h)). Proof. left. reflexivity. Qed.
  #[using="hAR AL B Hc ROOMF"] Lemma h_facts : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "(4.(15.+65?000.(5;.$1.$1.$5<.))(4.(4.(15.(5;.$1.$1.$5<.)$5=.)(4.(15.(17.$5=.(14.+2.+12.))(17.(5;.$1.$1.$5<.)(5>.$1.$1.$5<.)))(6.$1.(38.$5=.+1000.)=)))(4.(4.(15.(5;.$1.$1.$5<.)$5?.)(4.(15.(17.$5?.(14.+2.+12.))(17.(5;.$1.$1.$5<.)(5>.$1.$1.$5<.)))(6.$1.(38.$5?.+1000.)=)))P,$60.(>.(15.(17.$5=.(14.+2.+12.))$5?.)(15.(17.$5?.(14.+2.+12.))$5=.)))))")
(* [comment removed for export] *).
  Proof.
    pose proof (bwf_L h B) as WL. pose proof (bwf_breg h B) as BR. pose proof (wfL_facts _ WL) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    dpose (BR c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    unfold HB, UAh, FAh, UOKh. cbn [fst snd]. unfold fa_beg, region_beg, kRegionSize, kUserMapSize, kUserLimit, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kPrimHullLen, kHighMemBeg in *.
    pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)) as Q1. rewrite F3 in Q1.
    pose proof (Z.div_mod (r_mapped_user (h_reg h c)) (2^18) ltac:(lia)) as Q2. rewrite MUAL in Q2.
    pose proof (Z.div_mod (r_mapped_fa (h_reg h c)) (2^18) ltac:(lia)) as Q3. rewrite MFAL in Q3.
    split; [clear - F5; lia|]. split; [| split].
    - split; [clear - F1 Hc MU0; lia|]. split; [clear - F2 Hc MULIM; lia|].
      replace (l_sb (h_L h) + c * 2^32 + r_mapped_user (h_reg h c)) with ((16 * (l_sb (h_L h) / 2^16) + c * 2^20 + 64 * (r_mapped_user (h_reg h c) / 2^18)) * 4096) by (clear - Q1 Q2; lia). apply Z_mod_mult.
    - split; [clear - F1 Hc MFAB; lia|]. split; [clear - F2 Hc ROOMF; lia|].
      replace (l_sb (h_L h) + c * 2^32 + 3758096384 + r_mapped_fa (h_reg h c)) with ((16 * (l_sb (h_L h) / 2^16) + c * 2^20 + 917504 + 64 * (r_mapped_fa (h_reg h c) / 2^18)) * 4096) by (clear - Q1 Q3; lia). apply Z_mod_mult.
    - intros ROOMU. left. clear - ROOMU MFAB. lia.
  Qed.
  #[using="hAR AL c B Hc ROOMF"] Lemma h_H68 : 0x65f000 <= fst HB. Proof. exact (proj1 h_facts). Qed.
  #[using="hAR AL B Hc ROOMF"] Lemma h_HU : fst HB <= UAh /\ UAh + 2^18 <= fst HB + snd HB /\ UAh mod 4096 = 0. Proof. exact (proj1 (proj2 h_facts)). Qed.
  #[using="hAR AL B Hc ROOMF"] Lemma h_HF : fst HB <= FAh /\ FAh + 2^18 <= fst HB + snd HB /\ FAh mod 4096 = 0. Proof. exact (proj1 (proj2 (proj2 h_facts))). Qed.
  #[using="hAR AL B Hc ROOMF"] Lemma h_UF : UOKh -> UAh + 2^18 <= FAh \/ FAh + 2^18 <= UAh. Proof. exact (proj2 (proj2 (proj2 h_facts))). Qed.
  #[using="hAR AL mo0 K0 B Hc"] Lemma h_APT_U : UOKh -> forall t, In t (v_tr (vst_of h)) -> UAh + 2^18 <= t_lo t \/ t_hi t <= UAh.
  Proof. intros ROOMU t Ht. exact (uunit_new_apart AL h mo0 c t K0 (bwf_L h B) (bwf_breg h B) (proj1 (bwf_pa h B)) Hc ROOMU Ht). Qed.
  #[using="hAR AL mo0 K0 B Hc ROOMF"] Lemma h_APT_F : forall t, In t (v_tr (vst_of h)) -> FAh + 2^18 <= t_lo t \/ t_hi t <= FAh.
  Proof. intros t Ht. exact (funit_new_apart AL h mo0 c t K0 (bwf_L h B) (bwf_breg h B) (proj1 (bwf_pa h B)) Hc ROOMF Ht). Qed.
  #[using="hAR AL B HV"] Lemma h_SLACK : v_eb (vst_of h) + 4096 * vnb (vst_of h) + RES_GEN <= VLIMIT.
  Proof. apply vst_slack; [exact B| exact HV| unfold RES_GEN, RES_POP, RES_DEPOT; cbn; lia]. Qed.
  #[using="hAR AL B HV"] Lemma h_CB20 : v_cb20 (vst_of h) < J20. Proof. pose proof (vst_cb20' h B HV). lia. Qed.
  (* [comment removed for export] *)
        #[using="hAR AL B HV"] Lemma h_CB23 : v_cb23 (vst_of h) + (2^20 / 2^23 + 2) < J23. Proof. pose proof (vst_cb23' h B HV). change (2^20 / 2^23 + 2) with 2. lia. Qed.

  (* [comment removed for export] *)
  Definition Kh := Kg AL (vst_of h) UAh FAh (d_nb (h_dep h)) (d_bl (h_dep h)) UOKh.
  Definition CSh := CSg AL (vst_of h) UAh FAh (d_nb (h_dep h)) (d_bl (h_dep h)).
  Definition Gnh := Gn (d_nb (h_dep h)) (d_bl (h_dep h)).
  Definition Gsh := Gs (d_nb (h_dep h)) (d_bl (h_dep h)).

  (* [comment removed for export] *)
  #[using="Type"] Theorem Kh_entry : forall mo, HK AL h mo -> Kh None None (d_nb (h_dep h)) (d_bl (h_dep h)) mo.
  Proof. intros mo [K _]. unfold Kh. apply Kg_nb0. cbn. exact K. Qed.
  #[using="Type"] Theorem CSh_entry : forall x, CSh None None (d_nb (h_dep h)) (d_bl (h_dep h)) x <-> vcs AL (vst_of h) x.
  Proof.
    intros x. unfold CSh, CSg, Dnew. rewrite !skipn_all. cbn [In]. unfold AInstPop.CSp.
    split; [intros A; decompose [and or ex] A; auto; try discriminate; contradiction| intros A; left; left; exact A].
  Qed.

  (* [comment removed for export] *)
  #[using="GOT64 GSB64 mo0 K0 B Hc ROOMF"] Theorem HK_gen_exit : ltac2:(CDefT.buildp (gd_tbl_AInstGen ()) "Pu,(7.$8.)Pf,(7.$8.)Pnb,(1?.$1.)Pbl,(1?.$1.)Pmo,$2.Ph',$61.P,(62.R6.R5.R4.R3.R2.)(?.(1?.$1.)Lsn,(1?.$1.)(?.(1?.$1.)Lsb,(1?.$1.)(4.(6.(1?.$1.)R7.(27.$1.(51.(52.Vh,))R2.))(4.(6.(1?.$1.)R6.(27.$1.(53.(52.Vh,))R1.))(4.(43.$1.(13.VhAR,(14.+2.+14.))R2.)(4.(43.$1.(13.VhAR,(14.+2.+17.))R1.)(4.(44.(12.$1.R2.)#1.)(4.(44.(12.$1.R1.)#1.)(4.(5.(6.(7.$8.)R9.(9.$8.$:.)))(4.(5.(6.(7.$8.)R8.(9.$8.$:.)))(4.P,(6.(7.$8.)R9.(9.$8.$;.))$60.P,(63.Vh,Vc,R9.R8.R2.R1.R4.)(4.(64.VhAR,VAL,R5.R6.)Px,$1.(47.(65.R;.R:.R9.R8.R1.)(48.VAL,(66.R6.)R1.))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros u f nb bl mo h' K.
    ddestruct (Kg_exit AL GOT64 GSB64 (vst_of h) HB UAh FAh (d_nb (h_dep h)) (d_bl (h_dep h)) h_VR0 h_VWF0 h_HH h_H68 h_HU h_HF UOKh u f nb bl mo K)
      as (sn & sb & E1 & E2 & F1 & F2 & L1 & L2 & NU & NF & UK & HK' & VR' & EQ).
    dexists sn, sb. repeat (split; [assumption|]). intros R.
    (* [comment removed for export] *)
    dpose (bwf_breg h B c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    ddestruct R as (EL & EU & EUc & EF & EFc & ENB & EBL & ESC & EGH & EPA & EEM).
    set (mu' := r_mapped_user (h_reg h c) + unit_if u * kUserMapSize). set (mfa' := r_mapped_fa (h_reg h c) + unit_if f * kFreeArrayMapSize).
    set (h1 := AH (h_L h) (fun c' => if c' =? c then RG mu' (r_alloc_user (h_reg h c)) (r_mapped_fa (h_reg h c)) (r_fa (h_reg h c)) else h_reg h c')
                  (h_cache h) (h_cinit h) (h_chunks h) (h_tq h) (h_gq h) (h_sec h) (h_dep h) (h_ia h) (h_fake h) (h_pa_committed h) (h_havol h) (h_acct h)).
    set (h2 := AH (h_L h) (fun c' => if c' =? c then RG mu' (r_alloc_user (h_reg h c)) mfa' (r_fa (h_reg h c)) else h_reg h c')
                  (h_cache h) (h_cinit h) (h_chunks h) (h_tq h) (h_gq h) (h_sec h) (h_dep h) (h_ia h) (h_fake h) (h_pa_committed h) (h_havol h) (h_acct h)).
    assert (P1 : vperm (AInstPop.vp (vst_of h) UAh FAh u None) (vst_of h1)).
    { destruct u as [[|]|]; cbn [AInstPop.vp].
      - unfold vU. apply (vst_of_ugrow h c h1 Hc MU0 MUAL). subst h1 mu'. unfold R_ugrow. cbn [h_L h_reg h_dep h_sec h_acct h_pa_committed].
        split; [reflexivity|]. split; [intros c' NE; destruct (Z.eqb_spec c' c) as [->|]; [exfalso; apply NE; reflexivity| reflexivity]|].
        split; [rewrite Z.eqb_refl; cbn [r_mapped_user unit_if]; lia|]. split; [intros c'; destruct (Z.eqb_spec c' c) as [->|]; reflexivity|].
        repeat split; reflexivity.
      - replace (vst_of h1) with (vst_of h); [apply vperm_refl|]. symmetry. apply vst_of_ext; subst h1 mu'; cbn; try reflexivity; intros c'; destruct (Z.eqb_spec c' c) as [->|]; cbn; try reflexivity. lia.
      - replace (vst_of h1) with (vst_of h); [apply vperm_refl|]. symmetry. apply vst_of_ext; subst h1 mu'; cbn; try reflexivity; intros c'; destruct (Z.eqb_spec c' c) as [->|]; cbn; try reflexivity. lia. }
    assert (P2 : vperm (AInstPop.vp (vst_of h) UAh FAh u f) (vst_of h2)).
    { assert (EFA : FAh = fa_beg (h_L h1) c + r_mapped_fa (h_reg h1 c)) by (subst h1; cbn; rewrite Z.eqb_refl; reflexivity).
      destruct f as [[|]|].
      - assert (P1' : vperm (vF FAh (AInstPop.vp (vst_of h) UAh FAh u None)) (vF FAh (vst_of h1))) by (apply vperm_add_sub; exact P1).
        assert (EQV : AInstPop.vp (vst_of h) UAh FAh u (Some true) = vF FAh (AInstPop.vp (vst_of h) UAh FAh u None)) by (destruct u as [[|]|]; reflexivity).
        rewrite EQV. eapply vperm_trans; [exact P1'|]. unfold vF. rewrite EFA. apply (vst_of_fgrow h1 c h2 Hc); subst h1 h2 mu' mfa'; cbn; rewrite ?Z.eqb_refl; cbn; [clear - MFAB; lia| exact MFAL|].
        unfold R_fgrow. cbn. rewrite Z.eqb_refl. cbn. repeat split; try reflexivity; intros c'; destruct (Z.eqb_spec c' c) as [->|NE]; cbn; try reflexivity; intros X; exfalso; apply X; reflexivity.
      - replace (AInstPop.vp (vst_of h) UAh FAh u (Some false)) with (AInstPop.vp (vst_of h) UAh FAh u None) by (destruct u as [[|]|]; reflexivity).
        replace (vst_of h2) with (vst_of h1); [exact P1|]. apply vst_of_ext; subst h1 h2 mu' mfa'; cbn; try reflexivity; intros c'; destruct (Z.eqb_spec c' c); cbn; try reflexivity; lia.
      - replace (vst_of h2) with (vst_of h1); [exact P1|]. apply vst_of_ext; subst h1 h2 mu' mfa'; cbn; try reflexivity; intros c'; destruct (Z.eqb_spec c' c); cbn; try reflexivity; lia. }
    assert (DG : dgrow h2 sn sb h').
    { subst h2 mu' mfa'. unfold dgrow. cbn. rewrite EL, ENB, EBL, ESC, EGH, EPA, EEM. repeat split; try reflexivity;
        intros c'; destruct (Z.eqb_spec c' c) as [->|NE]; cbn; [exact EUc| exact (EU c' NE)| exact EFc| exact (EF c' NE)]. }
    pose proof (vst_of_grow h2 h' sn sb DG) as P3.
    assert (P : vperm (vexit (vst_of h) UAh FAh u f sn sb) (vst_of h')).
    { eapply vperm_trans; [| exact P3]. unfold vexit. apply vperm_fold_lazy. apply vperm_fold_eager. exact P2. }
    split.
    - exact (HK_perm AL h' _ mo P HK' VR').
    - intros x. rewrite (EQ x). apply vcs_perm. exact P.
  Qed.
End H.

End ARUN_1.
