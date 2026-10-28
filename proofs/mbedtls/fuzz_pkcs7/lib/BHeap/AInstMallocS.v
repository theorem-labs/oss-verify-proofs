(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AKinvM AVmScar AInstDepot AInstPop AVstT AInstGen AInstSec AInstMallocG.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_DepotB AW_DepotTop AW_MallocB HMLib HM HMFrame AHeapR APopSec AW_DepotCfg AW_PoisonBig AW_PoisonBigCfg AInstFree.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AInstMallocS () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.S.CSsh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "ARUN_1.S.KsF"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.not"; "ARUN_1.S.Glh"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "ARUN_1.S.Gph"; "ARUN_1.S.U0h"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPrimHullLen"; "ARUN_1.S.Gnh"; "Stdlib.ZArith.BinInt.Z.pow"; "ARUN_1.S.Gsh"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBigCfg.poison0_siteS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstDepot.sane"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "ARUN_1.S.r0h"; "ARUN_1.S.mszh"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstSec.saneL"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "ARUN_1.S.R_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"].

Section ARUN_1. Context {hAR : arun}.

Section S.
  Variables (h : ahst) (n : Z) (mo0 : Model).
  Hypothesis K0 : HK AL0 h mo0.
  Hypothesis B : bwf h.
  Hypothesis HV : h_havol h <= AVOL_MAX.
  Hypothesis NB : 0 <= n < 2^28.
  Hypothesis FP : from_primary n = false.
  Hypothesis ROOMS : h_pa_committed h + kPaSlice <= kPaHullLen.
  Hypothesis CSPAh : crange (vcs AL0 (vst_of h)) (l_pa (h_L h)) (h_pa_committed h).
  Set Default Proof Using "K0 B HV NB FP ROOMS CSPAh".

  Local Notation nb0 := (d_nb (h_dep h)).
  Local Notation bl0 := (d_bl (h_dep h)).
  Local Notation v0 := (vst_of h).
  Definition HP : Z * Z := (l_pa (h_L h), kPaHullLen).
  Definition U0h : Z := l_pa (h_L h) + h_pa_committed h.
  Definition r0h : Z := h_pa_committed h / kPaSlice.
  Definition mszh : Z := sec_map_size n.

  (* [comment removed for export] *)
  Definition Ksh := Ks AL0 v0 U0h r0h mszh nb0 bl0.
  Definition CSsh := CSs AL0 v0 HP U0h mszh nb0 bl0.
  Definition KsF (sc : list (Z * Z)) (r : Z) (nb bl : list Z) (mo : Model) : Prop := Ksh sc r nb bl mo /\ mo_frame mo0 mo.
  Definition Glh := Gl r0h mszh.
  Definition Gph := Gp r0h.
  Definition Gnh (sc : list (Z * Z)) (r : Z) (nb bl : list Z) : Prop := nb = nb0 /\ bl = bl0.
  Definition Gsh (sc : list (Z * Z)) (r : Z) (nb bl : list Z) : Prop := bl = bl0 /\ (nb = nb0 \/ exists x, nb = nb0 ++ [x]).

  (* [comment removed for export] *)
  Lemma VR0 : vranges_ok AL0 v0. Proof. exact (proj2 K0). Qed.
  Lemma VWF0 : vwf AL0 v0. Proof. exact (HK_vwf AL0 h mo0 K0). Qed.
  Lemma HH : In HP (v_hulls v0). Proof. right. left. reflexivity. Qed.
  Lemma PAF : 0 <= h_pa_committed h <= kPaHullLen /\ h_pa_committed h mod kPaSlice = 0. Proof. exact (bwf_pa h B). Qed.
  Lemma WLF : 0x1000 <= l_T (h_L h) /\ 0x65f000 <= l_pa (h_L h) /\ l_pa (h_L h) mod 4096 = 0.
  Proof. pose proof (bwf_L h B) as WL. pose proof (wfL_facts _ WL) as F. unfold wf_L, lowhigh in WL. unfold lowhigh in F. decompose [and] WL. decompose [and] F. repeat split; try assumption; lia. Qed.
  Lemma H68 : 0x65f000 <= fst HP. Proof. pose proof WLF. cbn. lia. Qed.
  Lemma HU : fst HP <= U0h /\ U0h + 0x20000 <= fst HP + snd HP /\ U0h mod 4096 = 0.
  Proof.
    pose proof PAF as [[P0 P1] PAL]. dpose WLF as (_ & _ & AL4). unfold HP, U0h, kPaSlice, kPaHullLen in *. cbn [fst snd].
    split; [lia|]. split; [lia|]. rewrite Z.add_mod, AL4, Z.add_0_l by lia. rewrite Z.mod_mod by lia.
    pose proof (Z.div_mod (h_pa_committed h) 131072 ltac:(lia)) as D. rewrite PAL, Z.add_0_r in D. rewrite D.
    replace (131072 * (h_pa_committed h / 131072)) with ((32 * (h_pa_committed h / 131072)) * 4096) by lia. apply Z_mod_mult.
  Qed.
  Lemma EU0 : U0h = fst HP + 0x20000 * r0h.
  Proof. pose proof PAF as [_ PAL]. unfold U0h, r0h, HP, kPaSlice in *. cbn [fst]. pose proof (Z.div_mod (h_pa_committed h) 131072 ltac:(lia)). lia. Qed.
  Lemma APT_P : forall t, In t (v_tr v0) -> U0h + 0x20000 <= t_lo t \/ t_hi t <= U0h.
  Proof.
    intros t Ht. pose proof PAF as [[P0 _] PAL]. unfold U0h.
    exact (pa_new_apart AL0 h mo0 t K0 (bwf_L h B) (bwf_breg h B) P0 ROOMS PAL Ht).
  Qed.
  (* [comment removed for export] *)
  Lemma UN0 : v_unit v0 U0h 0x20000.
  Proof.
    pose proof PAF as [[P0 P1] PAL]. cbn [vst_of v_unit]. unfold U0h.
    pose proof (Z.div_mod (h_pa_committed h) kPaSlice ltac:(unfold kPaSlice; lia)) as Q. rewrite PAL, Z.add_0_r in Q.
    rewrite Q at 1. rewrite (Z.mul_comm kPaSlice). change 0x20000 with kPaSlice. apply pa_unit. unfold kPaHullLen, kPaSlice in *.
    change (8388608 / 131072) with 64. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; [lia|]]. clear - ROOMS Q P0 P1. lia.
  Qed.
  Lemma MSZ : 0x11000 <= mszh /\ mszh mod 4096 = 0.
  Proof. dpose (sec_req_facts n NB FP) as (NLO & _ & N2 & RN & MS & MAL). unfold mszh. split; [lia| exact MAL]. Qed.
  Lemma MSZH : mszh <= 2^28 + 12288.
  Proof. dpose (sec_req_facts n NB FP) as (NLO & _ & N2 & RN & MS & MAL). unfold mszh. lia. Qed.
  Lemma SLACK : v_eb v0 + 4096 * vnb v0 + RES_SEC mszh <= VLIMIT.
  Proof.
    apply vst_slack; [exact B| exact HV|]. pose proof MSZ as [M0 _]. pose proof MSZH.
    unfold RES_SEC, RES_MAP, RES_SLICE, RES_DEPOT. pose proof (Z.div_le_mono mszh (2^28 + 12288) 32768 ltac:(lia) ltac:(lia)). cbn in *. lia.
  Qed.
  Lemma CB20 : v_cb20 v0 + (mszh / 2^20 + 2) < J20.
  Proof.
    pose proof (vst_cb h (2^20) 0 B HV ltac:(left; reflexivity) ltac:(lia)) as X. unfold vst_of. cbn [v_cb20].
    pose proof B as ([WL _] & _). unfold wf_L in WL. assert (E : l_ctxlen (h_L h) = 65536) by (decompose [and] WL; assumption). rewrite E in X.
    pose proof MSZH as MH. pose proof (Z.div_le_mono mszh (2^28 + 12288) (2^20) ltac:(lia) MH) as DM.
    unfold kPrimHullLen, kPaHullLen, kFakeBytes, AVOL_MAX, J20 in *. clear - X DM.
    match type of X with _ <= ?r => let r' := eval vm_compute in r in change r with r' in X end.
    match type of DM with _ <= ?r => let r' := eval vm_compute in r in change r with r' in DM end. lia.
  Qed.
  Lemma CB23 : v_cb23 v0 + (mszh / 2^23 + 2) + (2^20 / 2^23 + 2) < J23.
  Proof.
    pose proof (vst_cb h (2^23) 0 B HV ltac:(right; reflexivity) ltac:(lia)) as X. unfold vst_of. cbn [v_cb23].
    pose proof B as ([WL _] & _). unfold wf_L in WL. assert (E : l_ctxlen (h_L h) = 65536) by (decompose [and] WL; assumption). rewrite E in X.
    pose proof MSZH as MH. pose proof (Z.div_le_mono mszh (2^28 + 12288) (2^23) ltac:(lia) MH) as DM.
    unfold kPrimHullLen, kPaHullLen, kFakeBytes, AVOL_MAX, J23 in *. clear - X DM. change (2^20 / 2^23 + 2) with 2.
    match type of X with _ <= ?r => let r' := eval vm_compute in r in change r with r' in X end.
    match type of DM with _ <= ?r => let r' := eval vm_compute in r in change r with r' in DM end. lia.
  Qed.
  Lemma CSPA0 : crange (vcs AL0 v0) (fst HP) (0x20000 * r0h).
  Proof. intros x Hx. apply CSPAh. pose proof EU0 as E. unfold U0h, HP in *. cbn [fst] in *. lia. Qed.
  Lemma HLEN : snd HP = 0x800000. Proof. reflexivity. Qed.
    
  Ltac sfacts := first [ exact AL0_wf | exact AL0_sb | exact AL0_IML | exact AL0_IMH | exact AL0_GOT64 | exact AL0_GSB64
                       | exact VR0 | exact VWF0 | exact HH | exact H68 | exact HU | exact EU0 | exact APT_P | exact UN0 | exact MSZ
                       | exact SLACK | exact CB20 | exact CB23 | exact CSPA0 | exact HLEN | eassumption ].

  (* [comment removed for export] *)
  Lemma MS_CSOK : forall sc r nb bl, cs_ok AL0 (CSsh sc r nb bl).
  Proof. intros. unfold CSsh. eapply (S_CSOK AL0); sfacts. Qed.
  Lemma MS_KL : forall sc r nb bl, kinv AL0 (CSsh sc r nb bl) (KsF sc r nb bl).
  Proof. intros. unfold KsF, Ksh, CSsh. apply kinv_KF. eapply (S_KL AL0); sfacts. Qed.
  Lemma MS_noshadow : forall sc r nb bl x, CSsh sc r nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  Proof. intros sc r nb bl x Hx. unfold CSsh in Hx. eapply (S_noshadow AL0) in Hx; sfacts. Qed.
  Lemma MS_CSmono_l : forall sc r p y, CSsh sc r nb0 bl0 y -> CSsh (sc ++ [p]) r nb0 bl0 y.
  Proof. intros. unfold CSsh in *. apply S_CSmono_l. assumption. Qed.
  Lemma MS_CSmono_p : forall sc r y, CSsh sc r nb0 bl0 y -> CSsh sc (r + 1) nb0 bl0 y.
  Proof. intros sc r y Hy. unfold CSsh in *. exact (S_CSmono_p AL0 v0 HP U0h mszh nb0 bl0 VWF0 HH H68 HU MSZ sc r y Hy). Qed.
  Lemma MS_CSmono_n : forall sc r nb bl b x, CSsh sc r nb bl x -> CSsh sc r (nb ++ [b]) bl x.
  Proof. intros. unfold CSsh in *. apply S_CSmono_n. assumption. Qed.
  Lemma MS_CSmono_s : forall sc r nb bl b x, CSsh sc r nb bl x -> CSsh sc r nb (bl ++ [b]) x.
  Proof. intros. unfold CSsh in *. apply S_CSmono_s. assumption. Qed.
  Lemma MS_CSlift : forall sc r nb bl a k, crange (vcs AL0 v0) a k -> crange (CSsh sc r nb bl) a k.
  Proof. intros. unfold CSsh. apply S_CSlift. assumption. Qed.
  Lemma MS_CSPA : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)P,(3.=R3.)P,(3.(4.+20000.R4.)+800000.)(5.(6.R6.R5.R4.R3.)(7.(8.Vh,))(4.+20000.R5.))")
(* [comment removed for export] *).
  Proof. intros sc r nb bl R0 RB. unfold CSsh. change (l_pa (h_L h)) with (fst HP). exact (S_CSPA AL0 v0 HP U0h r0h mszh nb0 bl0 EU0 CSPA0 HLEN sc r nb bl R0 RB). Qed.

  Lemma MS_apart_l : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pmo,$9.Pa,(:.&40.)Pw,(:.&40.)P,(;.R5.R4.(<.(=.Vh,))(>.(=.Vh,))R3.)P,(?.$10.(11.(12.(1.(:.&40.)(:.&40.))(13.(14.R4.))(15.(14.R4.)))R3.R2.)$16.)P,(3.+10000.(17.&40.R3.))P,(3.(18.(17.&40.R5.)(17.&40.R4.))(19.VhAR,))Py,$2.P,(1:.(6.R:.R9.(<.(=.Vh,))(>.(=.Vh,))R1.)(1:.(1;.(3.(1<.$1=.)R1.)(1>.R1.(1?.$1=.)))(1:.(1;.(3.+7???7000.R1.)(1>.R1.+10007???8000.))(1;.(3.(7.(8.Vh,))R1.)(1>.R1.(18.(7.(8.Vh,))+800000.))))))(20.(1;.(3.(17.&40.R8.)R2.)(1>.R2.(18.(17.&40.R8.)(17.&40.R7.)))))")
(* [comment removed for export] *).
  Proof. intros sc r mo a w [K _] RF W16 CE y Hy. unfold Ksh, CSsh in *. change (l_pa (h_L h)) with (fst HP) in Hy. exact (S_apart_l AL0 AL0_GOT64 AL0_GSB64 v0 HP U0h r0h mszh nb0 bl0 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23 HLEN sc r mo a w K RF W16 CE y Hy). Qed.
  Lemma MS_T_large : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pm,$2.Pmo,$9.Pa,(:.&40.)P,(21.R5.R4.R3.)P,(;.R6.R5.(<.(=.Vh,))(>.(=.Vh,))R3.)P,(?.$2.(22.(17.&40.R3.)+1000.)=)P,(1>.=(17.&40.R4.))P,(3.(18.(17.&40.R5.)R7.)(19.VhAR,))P,(?.$10.(11.(12.(1.(:.&40.)(:.&40.))(13.(14.R7.))(15.(14.R7.)))R6.(23.&40.R8.))$16.)(1;.(;.(12.(1.$2.$2.)R;.(24.(1.$2.$2.)(25.$2.$2.(17.&40.R7.)R9.)(26.(1.$2.$2.))))R:.(<.(=.Vh,))(>.(=.Vh,))(27.+22.R7.R9.R8.))(5.(6.(12.(1.$2.$2.)R;.(24.(1.$2.$2.)(25.$2.$2.(17.&40.R7.)R9.)(26.(1.$2.$2.))))R:.(<.(=.Vh,))(>.(=.Vh,)))(17.&40.R7.)R9.))")
(* [comment removed for export] *).
  Proof.
    intros sc r m mo a G [K FR] AAL A0 ACE RF. unfold KsF, Ksh, CSsh, Glh in *.
    destruct (S_T_large AL0 AL0_sb AL0_IML AL0_IMH v0 HP U0h r0h mszh nb0 bl0 H68 HU MSZ SLACK sc r m mo a G K AAL A0 ACE RF) as [K' C'].
    split; [| exact C']. split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_anon_grant].
  Qed.
  Lemma MS_LEDGER_P : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pmo,$9.P,(28.R3.R2.)P,(;.R4.R3.(<.(=.Vh,))(>.(=.Vh,))R2.)(1;.(?.$10.(11.(13.(14.R3.))(23.&40.$29.)(23.&40.+20000.))$16.)(1:.(?.$10.(2:.(15.(14.R3.))(23.&40.$29.)(23.&40.+20000.))$16.)(?.$10.(11.(12.(1.(:.&40.)(:.&40.))(13.(14.R3.))(15.(14.R3.)))(23.&40.$29.)(23.&40.+20000.))$16.)))")
(* [comment removed for export] *).
  Proof. intros sc r mo G [K _]. unfold Ksh, Gph in *. exact (S_LEDGER_P AL0 AL0_sb AL0_IMH v0 HP U0h r0h mszh nb0 bl0 VR0 HH H68 HU APT_P UN0 MSZ SLACK sc r mo G K). Qed.
  Lemma MS_TP_commit : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pmo,$9.P,(28.R3.R2.)P,(;.R4.R3.(<.(=.Vh,))(>.(=.Vh,))R2.)P,(?.$10.(2:.(15.(14.R3.))(23.&40.$29.)(23.&40.+20000.))$16.)(1;.(;.R6.(18.R5.+1.)(<.(=.Vh,))(>.(=.Vh,))(2;.+32.$29.+20000.R4.))(5.(6.R6.(18.R5.+1.)(<.(=.Vh,))(>.(=.Vh,)))$29.+20000.))")
(* [comment removed for export] *).
  Proof.
    intros sc r mo G [K FR] MC. unfold KsF, Ksh, CSsh, Gph in *.
    destruct (S_TP_commit AL0 AL0_sb AL0_IMH v0 HP U0h r0h mszh nb0 bl0 VR0 HH H68 HU EU0 APT_P UN0 MSZ SLACK sc r mo G K MC) as [K' C'].
    split; [| exact C']. split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_fixrw_commit].
  Qed.
  Lemma MS_TP_fresh : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pmo,$9.P,(28.R3.R2.)P,(;.R4.R3.(<.(=.Vh,))(>.(=.Vh,))R2.)P,(?.$10.(11.(12.(1.(:.&40.)(:.&40.))(13.(14.R3.))(15.(14.R3.)))(23.&40.$29.)(23.&40.+20000.))$16.)(1;.(;.R6.(18.R5.+1.)(<.(=.Vh,))(>.(=.Vh,))(2<.+32.$29.+20000.R4.))(5.(6.R6.(18.R5.+1.)(<.(=.Vh,))(>.(=.Vh,)))$29.+20000.))")
(* [comment removed for export] *).
  Proof.
    intros sc r mo G [K FR] RF. unfold KsF, Ksh, CSsh, Gph in *.
    destruct (S_TP_fresh AL0 v0 HP U0h r0h mszh nb0 bl0 VWF0 HH H68 HU MSZ sc r mo G K RF) as [K' C'].
    split; [| exact C']. split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_fixrw_fresh].
  Qed.
  Lemma MS_ROOM_P : forall sc r mo, Gph sc r -> KsF sc r nb0 bl0 mo -> fixrw_grantable 0x32 U0h 0x20000 mo.
  Proof. intros sc r mo G [K _]. unfold Ksh, Gph in *. exact (S_ROOM_P AL0 AL0_sb AL0_IMH v0 HP U0h r0h mszh nb0 bl0 VR0 HH H68 HU APT_P UN0 MSZ SLACK sc r mo G K). Qed.
  (* [comment removed for export] *)
  Lemma MS_SCAR_P : forall sc r, Gph sc r -> hole_site AL0 (CSsh sc r nb0 bl0) (KsF sc r nb0 bl0) U0h 0x20000.
  Proof. intros sc r G. unfold KsF, Ksh, CSsh, Gph in *. apply (hole_site_KF AL0). exact (S_SCAR_P AL0 AL0_sb AL0_IMH v0 HP U0h r0h mszh nb0 bl0 VR0 VWF0 HH H68 HU EU0 APT_P UN0 MSZ sc r G). Qed.
  Lemma MS_SEC_APART : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)Pmo,$9.Pp,(1.$2.$2.)P,(;.R6.R5.R4.R3.R2.)P,(2=.(1.$2.$2.)R2.R7.)(1:.(3.(18.(2>.$2.$2.R3.)(2?.$2.$2.R3.))(30.(8.Vh,)))(3.(18.(30.(8.Vh,))$31.)(2>.$2.$2.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl mo p [K _] Hp. unfold Ksh in K.
    exact (S_SEC_APART AL0 v0 U0h r0h mszh nb0 bl0 sc r nb bl mo p (l_b6 (h_L h), kPrimHullLen) K Hp ltac:(left; reflexivity)).
  Qed.
  Lemma MS_apart : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)Pmo,$9.Pa,(:.&40.)Pw,(:.&40.)P,(;.R7.R6.R5.R4.R3.)P,(?.$10.(11.(12.(1.(:.&40.)(:.&40.))(13.(14.R4.))(15.(14.R4.)))R3.R2.)$16.)P,(3.+10000.(17.&40.R3.))P,(3.(18.(17.&40.R5.)(17.&40.R4.))(19.VhAR,))Px,$2.P,(1:.(6.R<.R;.R:.R9.R1.)(1;.(3.(1<.$1=.)R1.)(1>.R1.(1?.$1=.))))(20.(1;.(3.(17.&40.R8.)R2.)(1>.R2.(18.(17.&40.R8.)(17.&40.R7.)))))")
(* [comment removed for export] *).
  Proof. intros sc r nb bl mo a w [K _] RF W16 CE x Hx. unfold Ksh, CSsh in *. exact (S_apart AL0 AL0_GOT64 AL0_GSB64 v0 HP U0h r0h mszh nb0 bl0 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23 sc r nb bl mo a w K RF W16 CE x Hx). Qed.
  Lemma MS_T_node : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)Pmo,$9.Pa,(:.&40.)P,(32.R6.R5.R4.R3.)P,(;.R7.R6.R5.R4.R3.)P,(?.$2.(22.(17.&40.R3.)+1000.)=)P,(1>.=(17.&40.R4.))P,(3.(18.(17.&40.R5.)(33.+2.+14.))(19.VhAR,))P,(?.$10.(11.(12.(1.(:.&40.)(:.&40.))(13.(14.R7.))(15.(14.R7.)))R6.(23.&40.(33.+2.+14.)))$16.)(1;.(;.R<.R;.(12.$2.R:.(24.$2.(17.&40.R7.)(26.$2.)))R9.(27.+22.R7.(33.+2.+14.)R8.))(5.(6.R<.R;.(12.$2.R:.(24.$2.(17.&40.R7.)(26.$2.)))R9.)(17.&40.R7.)(33.+2.+14.)))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl mo a G [K FR] AAL A0 ACE RF. unfold KsF, Ksh, CSsh, Gnh in *.
    destruct (S_T_node AL0 AL0_sb AL0_IML AL0_IMH AL0_GOT64 AL0_GSB64 v0 HP U0h r0h mszh nb0 bl0 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23 sc r nb bl mo a G K AAL A0 ACE RF) as [K' C'].
    split; [| exact C']. split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_anon_grant].
  Qed.
  Lemma MS_T_store : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)Pmo,$9.Pa,(:.&40.)P,(34.R6.R5.R4.R3.)P,(;.R7.R6.R5.R4.R3.)P,(?.$2.(22.(17.&40.R3.)+1000.)=)P,(1>.=(17.&40.R4.))P,(3.(18.(17.&40.R5.)(33.+2.+17.))(19.VhAR,))P,(?.$10.(11.(12.(1.(:.&40.)(:.&40.))(13.(14.R7.))(15.(14.R7.)))R6.(23.&40.(33.+2.+17.)))$16.)(1;.(;.R<.R;.R:.(12.$2.R9.(24.$2.(17.&40.R7.)(26.$2.)))(27.+4022.R7.(33.+2.+17.)R8.))(5.(6.R<.R;.R:.(12.$2.R9.(24.$2.(17.&40.R7.)(26.$2.))))(17.&40.R7.)(33.+2.+17.)))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl mo a G [K FR] AAL A0 ACE RF. unfold KsF, Ksh, CSsh, Gsh in *.
    destruct (S_T_store AL0 AL0_sb AL0_IML AL0_IMH AL0_GOT64 AL0_GSB64 v0 HP U0h r0h mszh nb0 bl0 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23 sc r nb bl mo a G K AAL A0 ACE RF) as [K' C'].
    split; [| exact C']. split; [exact K'|]. eapply mo_frame_trans; [exact FR| apply mo_frame_anon_grant].
  Qed.
  Lemma MS_ROOM_n : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)Pmo,$9.P,(32.R5.R4.R3.R2.)P,(;.R6.R5.R4.R3.R2.)(35.(:.&40.)La,(:.&40.)(36.VhAR,+22.(33.+2.+14.)R4.R1.))")
(* [comment removed for export] *).
  Proof. intros sc r nb bl mo G [K _]. unfold Ksh, Gnh in *. exact (S_ROOM_n AL0 AL0_GOT64 AL0_GSB64 v0 HP U0h r0h mszh nb0 bl0 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23 sc r nb bl mo G K). Qed.
  Lemma MS_ROOM_s : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)Pmo,$9.P,(34.R5.R4.R3.R2.)P,(;.R6.R5.R4.R3.R2.)(35.(:.&40.)La,(:.&40.)(36.VhAR,+4022.(33.+2.+17.)R4.R1.))")
(* [comment removed for export] *).
  Proof. intros sc r nb bl mo G [K _]. unfold Ksh, Gsh in *. exact (S_ROOM_s AL0 AL0_GOT64 AL0_GSB64 v0 HP U0h r0h mszh nb0 bl0 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23 sc r nb bl mo G K). Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma MS_entry : KsF [] r0h nb0 bl0 mo0.
  Proof. split; [| apply mo_frame_refl]. exists v0. split; [left; auto| left; split; [reflexivity| split; [reflexivity| exact (proj1 K0)]]]. Qed.
    Lemma MS_Gp : forall p, Gph ([] ++ [p]) r0h. Proof. intros p. split; reflexivity. Qed.
  Lemma MS_Gn : forall sc r, Gnh sc r nb0 bl0. Proof. intros. split; reflexivity. Qed.
  Lemma MS_Gs : forall sc r, Gsh sc r nb0 bl0. Proof. intros. split; [reflexivity| left; reflexivity]. Qed.
  Lemma MS_Gsx : forall sc r x, Gsh sc r (nb0 ++ [x]) bl0. Proof. intros. split; [reflexivity| right; exists x; reflexivity]. Qed.


  (* [comment removed for export] *)
  Lemma MS_PZ : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Pcan,(:.&40.)Pdd,(:.&8.)Pmadv,(:.&8.)Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)PA,$2.Pw,$2.P,(?.$2.(22.R2.+8.)=)P,(?.$2.(22.R2.+8.)=)P,(3.+8.R3.)P,(3.R4.(33.+2.+28.))P,(1:.(1;.(3.+8.R6.)(1;.(3.R6.+7???7??8.)(3.(18.R6.R5.)+7???8000.)))(1;.(3.+10007???8000.R6.)(1;.(3.+10007???8008.(18.R6.R5.))(1;.(3.R6.+7??????????8.)(3.(18.R6.R5.)+800000000000.)))))(37.VhAR,(6.R;.R:.R9.R8.)(;.R;.R:.R9.R8.)R7.R6.R>.R=.R<.)")
(* [comment removed for export] *).
  Proof.
    intros can dd madv sc r nb bl A w AAL WAL W8 WMAX RNG.
    exact (poison0_S AL0 AL0_img AL0_wf (CSsh sc r nb bl) (MS_CSOK sc r nb bl) AL0_sb (KsF sc r nb bl) A w can dd madv
             (MS_KL sc r nb bl) AAL WAL ltac:(clear - W8; lia) RNG).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition R_sec (sc : list (Z * Z)) (r : Z) (sn sb : list Z) (h' : ahst) : Prop :=
    h_L h' = h_L h /\ (forall c, r_mapped_user (h_reg h' c) = r_mapped_user (h_reg h c)) /\ (forall c, r_mapped_fa (h_reg h' c) = r_mapped_fa (h_reg h c))
    /\ d_nb (h_dep h') = nb0 ++ sn /\ d_bl (h_dep h') = bl0 ++ sb /\ a_sech (h_acct h') = a_sech (h_acct h)
    /\ match sc with
       | [] => s_chunks (h_sec h') = s_chunks (h_sec h) /\ r = r0h
       | _ => exists a sz, sc = [(a, mszh)] /\ Permutation (s_chunks (h_sec h')) (SH a mszh sz :: s_chunks (h_sec h))
       end
    /\ h_pa_committed h' = h_pa_committed h + (r - r0h) * kPaSlice
    /\ a_emb (h_acct h') = a_emb (h_acct h).   (* [comment removed for export] *)

  Let with_sec (h0 : ahst) (cks : list shdr) (pa : Z) : ahst :=
    AH (h_L h0) (h_reg h0) (h_cache h0) (h_cinit h0) (h_chunks h0) (h_tq h0) (h_gq h0) (SE cks (s_nres (h_sec h0))) (h_dep h0) (h_ia h0) (h_fake h0) pa (h_havol h0) (h_acct h0).

  Theorem MS_exit : ltac2:(CDefT.buildp (gd_tbl_AInstMallocS ()) "Psc,(0.(1.$2.$2.))Pr,$2.Pnb,(0.$2.)Pbl,(0.$2.)Pmo,$9.Ph',$38.P,(;.R6.R5.R4.R3.R2.)(35.(0.$2.)Lsn,(0.$2.)(35.(0.$2.)Lsb,(0.$2.)(1;.(?.(0.$2.)R7.(12.$2.(<.(=.Vh,))R2.))(1;.(?.(0.$2.)R6.(12.$2.(>.(=.Vh,))R1.))(1;.(39.$2.(3:.VhAR,(33.+2.+14.))R2.)(1;.(39.$2.(3:.VhAR,(33.+2.+17.))R1.)(1;.(3;.(3<.$2.R2.)#1.)(1;.(3;.(3<.$2.R1.)#1.)(1;.(1:.(1;.(?.(0.(1.$2.$2.))R9.(26.(1.$2.$2.)))(?.$2.R8.$3=.))(35.$2.La,$2.(1;.(?.(0.(1.$2.$2.))R:.(24.(1.$2.$2.)(25.$2.$2.R1.$3>.)(26.(1.$2.$2.))))(1;.(3?.VhAR,$1=.(40.Vh,)$3>.R1.)(1:.(?.$2.R9.$3=.)(?.$2.R9.(18.$3=.+1.)))))))(1;.(41.Vmo0,R5.)P,(42.R9.R8.R2.R1.R4.)(1;.(43.VhAR,$1=.R5.R6.)Px,$2.(44.(6.R;.R:.R9.R8.R1.)(45.$1=.(40.R6.)R1.)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros sc r nb bl mo h' [K FR]. unfold Ksh in K.
    ddestruct (Ks_exit AL0 AL0_GOT64 AL0_GSB64 v0 HP U0h r0h mszh nb0 bl0 VR0 VWF0 HH H68 HU EU0 MSZ SLACK CB20 CB23 sc r nb bl mo K)
      as (v & sn & sb & BS & E1 & E2 & F1 & F2 & L1 & L2 & HK' & VR' & EQ).
    dexists sn, sb. split; [exact E1|]. split; [exact E2|]. split; [exact F1|]. split; [exact F2|]. split; [exact L1|]. split; [exact L2|].
    split. { destruct BS as [(-> & -> & _)|(a & -> & SA & CS)]; [left; auto| right; exists a]. split; [reflexivity|]. split; [exact SA|]. destruct CS as [[-> _]|[-> _]]; auto. }
    split; [exact FR|].
    (intros dd_H; ddestruct dd_H as (EL & EU & EF & ENB & EBL & EGH & ESC & EPA & EEM)). pose proof PAF as [[P0 _] PAL].
    (* [comment removed for export] *)
    assert (MAIN : vperm (vexit_s v sn sb) (vst_of h')).
    { destruct BS as [(-> & -> & ->)|(a & -> & SA & CS)].
      - destruct ESC as [ESC _]. apply (vst_of_grow h h' sn sb). unfold dgrow. rewrite EPA. repeat split; try assumption. lia.
      - ddestruct ESC as (a' & sz & Ea & PERM). injection Ea as <-.
        set (h1 := with_sec h (s_chunks (h_sec h')) (h_pa_committed h)).
        assert (P1 : vperm (vL v0 mszh a) (vst_of h1)).
        { unfold vL. apply (vst_of_secadd h (SH a mszh sz) h1). unfold R_secadd. subst h1. cbn. repeat split; try reflexivity. exact PERM. }
        destruct CS as [[-> ->]|[-> ->]].
        + eapply vperm_trans; [| apply (vst_of_grow h1 h' sn sb); unfold dgrow; subst h1; cbn; rewrite EPA; repeat split; try assumption; lia].
          unfold vexit_s. apply vperm_fold_lazy. apply vperm_fold_eager. exact P1.
        + set (h2 := with_sec h (s_chunks (h_sec h')) (h_pa_committed h + kPaSlice)).
          assert (P2 : vperm (vLP v0 U0h mszh a) (vst_of h2)).
          { unfold vLP. eapply vperm_trans; [apply vperm_add_sub; exact P1|].
            unfold U0h. change (l_pa (h_L h) + h_pa_committed h) with (l_pa (h_L h1) + h_pa_committed h1). change 0x20000 with kPaSlice.
            apply (vst_of_pa h1 h2); [exact P0| exact PAL|]. unfold R_pa. subst h1 h2. cbn. repeat split; reflexivity. }
          eapply vperm_trans; [| apply (vst_of_grow h2 h' sn sb); unfold dgrow; subst h1 h2; cbn; rewrite EPA; repeat split; try assumption; lia].
          unfold vexit_s. apply vperm_fold_lazy. apply vperm_fold_eager. exact P2. }
    split.
    - exact (HK_perm AL0 h' _ mo MAIN HK' VR').
    - intros x. unfold CSsh. rewrite (EQ x). apply vcs_perm. exact MAIN.
  Qed.
End S.

End ARUN_1.
