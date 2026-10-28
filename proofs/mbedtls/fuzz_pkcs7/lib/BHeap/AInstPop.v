(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AJ AVm AKinvM AVmScar AInstDepot.
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
Ltac2 gd_tbl_AInstPop () : Init.string Init.list := ["Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.hull64"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_got"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"; "ARUN_1.InstPop.CSp"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.HKv"; "ARUN_1.InstPop.vU"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.fixrw_grantable"; "ARUN_1.InstPop.vF"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vst"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_hulls"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.app"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.False"; "ARUN_1.InstPop.Kp"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"].

Section ARUN_1. Context {hAR : arun}.
Definition RES_POP : Z := 2 * (2^18 + 4096 * (2^18 / 32768 + 3)).

Section InstPop.
  Variable AL : asan_layout.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis IML : al_img_lo AL <= 0x10000.
  Hypothesis IMH : al_img_hi AL = 0x65f000.
  Hypothesis GOT64 : al_img_lo AL + 64 <= al_got AL /\ al_got AL + 128 <= al_img_hi AL /\ al_got AL mod 8 = 0.
  Hypothesis GSB64 : al_img_lo AL + 64 <= al_gsb AL /\ al_gsb AL + 128 <= al_img_hi AL /\ al_gsb AL mod 8 = 0.

  Variable v0 : vst.
  Variable H : Z * Z.          (* [comment removed for export] *)
  Variables UA FAA : Z.        (* [comment removed for export] *)
  Hypothesis VR0 : vranges_ok AL v0.
  Hypothesis VWF0 : vwf AL v0.
  Hypothesis HH : In H (v_hulls v0).
  Hypothesis H68 : 0x65f000 <= fst H.
  Hypothesis HU : fst H <= UA /\ UA + 2^18 <= fst H + snd H /\ UA mod 4096 = 0.
  Hypothesis HF : fst H <= FAA /\ FAA + 2^18 <= fst H + snd H /\ FAA mod 4096 = 0.
  Variable UOK : Prop.
  Hypothesis UF : UOK -> UA + 2^18 <= FAA \/ FAA + 2^18 <= UA.
  Hypothesis APT_U : UOK -> forall t, In t (v_tr v0) -> UA + 2^18 <= t_lo t \/ t_hi t <= UA.
  Hypothesis APT_F : forall t, In t (v_tr v0) -> FAA + 2^18 <= t_lo t \/ t_hi t <= FAA.
  (* [comment removed for export] *)
  Hypothesis UUN : UOK -> v_unit v0 UA (2^18).
  Hypothesis FUN : v_unit v0 FAA (2^18).
  Hypothesis SLACK : v_eb v0 + 4096 * vnb v0 + RES_POP <= VLIMIT.
  Hypothesis HC : In H (v_cover v0).   (* [comment removed for export] *)

  Definition vU : vst := v_add_sub v0 UA (2^18) true.
  Definition vF (v : vst) : vst := v_add_sub v FAA (2^18) true.

  Definition Kp (u f : option bool) (mo : Model) : Prop :=
    match u, f with
    | None, None => HKv AL v0 mo
    | Some true, None => UOK /\ HKv AL vU mo
    | None, Some true => HKv AL (vF v0) mo
    | Some true, Some true => UOK /\ HKv AL (vF vU) mo
    | _, _ => False
    end.

  Definition CSp (u f : option bool) (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "(0.(1.VAL,Vv0,O1.)(0.(2.(3.(4.$5.)O3.(6.$5.$7.))(2.(8.VUA,O1.)(9.O1.(:.VUA,(;.+2.+12.)))))(2.(3.(4.$5.)O2.(6.$5.$7.))(2.(8.VFAA,O1.)(9.O1.(:.VFAA,(;.+2.+12.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="AL UA FAA"] Lemma vnb_sub : forall v lo, vnb (v_add_sub v lo (2^18) true) = vnb v + (2^18 / 32768 + 3).
  Proof. intros v lo. unfold vnb, csranges, lazyranges. cbn [v_stk v_img v_tr v_ghost v_add_sub List.filter is_lazy_cs t_kind t_cs map app zsum]. cbn [t_lo t_len]. unfold npages_shadow at 3. cbn [snd]. lia. Qed.
  #[using="Type"] Lemma veb_sub : forall v lo, v_eb (v_add_sub v lo (2^18) true) = v_eb v + 2^18.  Proof. reflexivity. Qed.
  #[using="UA FAA"] Lemma vranges_ok_add_sub : forall v lo n, vranges_ok AL v -> 0 <= lo -> 0 <= n -> vranges_ok AL (v_add_sub v lo n true).
  Proof.
    (intros v lo n dd_H; ddestruct dd_H as (A & B & C); intros H0 H1). split; [exact A|]. split.
    - unfold csranges in *. cbn [v_stk v_img v_tr v_ghost v_add_sub List.filter t_cs map]. inversion B as [|? ? B1 B2]; subst.
      constructor; [exact B1|]. inversion B2 as [|? ? B3 B4]; subst. constructor; [exact B3|]. cbn [app]. constructor; [cbn; lia| exact B4].
    - unfold lazyranges in *. cbn [v_tr v_add_sub List.filter is_lazy_cs t_kind map]. exact C.
  Qed.

  #[using="Type"] Lemma vcs_sub : forall v lo x, vcs AL (v_add_sub v lo (2^18) true) x <-> vcs AL v x \/ lo <= x < lo + 2^18.
  Proof.
    intros v lo x. unfold vcs. cbn [v_stk v_img v_tr v_add_sub]. split.
    - intros [A|[A|(t & [<-|Ht] & TC & R)]]; [left; left; exact A| left; right; left; exact A| right; unfold t_hi in R; cbn in R; exact R|].
      left. right. right. exists t. split; [exact Ht| split; [exact TC| exact R]].
    - intros [[A|[A|(t & Ht & TC & R)]]|R]; [left; exact A| right; left; exact A| right; right; exists t; split; [right; exact Ht| split; [exact TC| exact R]]|].
      right. right. eexists. split; [left; reflexivity|]. unfold t_hi. cbn [t_cs t_lo t_len]. split; [reflexivity| exact R].
  Qed.

  #[using="hAR AL v0 H FAA VWF0 HH H68 HU HF"] Lemma HU0 : 0 <= UA.   Proof. dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH). lia. Qed.
  #[using="hAR AL v0 H UA VWF0 HH H68 HU HF"] Lemma HF0 : 0 <= FAA.  Proof. dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH). lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma CSp_00 : forall x, CSp None None x <-> vcs AL v0 x.
  Proof. intros x. unfold CSp. split; [intros [A|[[E _]|[E _]]]; [exact A| discriminate| discriminate]| intros A; left; exact A]. Qed.
  #[using="Type"] Lemma CSp_U0 : forall x, CSp (Some true) None x <-> vcs AL vU x.
  Proof. intros x. unfold CSp, vU. rewrite vcs_sub. split; [intros [A|[[_ R]|[E _]]]; [left; exact A| right; exact R| discriminate]| intros [A|R]; [left; exact A| right; left; auto]]. Qed.
    
  
  (* [comment removed for export] *)

  #[using="hAR ALWF IML IMH GOT64 GSB64 H UA FAA VWF0 H68 HU HF"] Lemma vcs0_range' : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Px,$<.P,(1.VAL,Vv0,R1.)(2.(2.(8.=R2.)(9.R2.(;.+2.+2?.)))(2.(0.(8.(:.R2.+1.)+7???7000.)(8.+10007???8000.R2.))(2.(=.(2.(8.(>.(?.VAL,))R2.)(9.R2.(:.(>.(:.(?.VAL,)+7.))+40.))))(=.(2.(8.(>.(10.VAL,))R2.)(9.R2.(:.(>.(:.(10.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. dpose VWF0 as (TWF & _ & _ & _ & _ & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & _ & BANDCS & _).
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *).
    dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). pose proof GOT64 as G64. pose proof GSB64 as S64.
    aceilb. rewrite IMH in *.
    destruct Hx as [Y|[(Y & G1 & G2)|(t & Ht & TC & R)]].
    - lia.
    - rewrite IMG0, IMG1 in Y. lia.
    - pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & _ & _ & _ & T6). pose proof (BANDCS t Ht TC) as B.
      unfold t_hi in *. lia.
  Qed.

  #[using="hAR ALWF IML IMH GOT64 GSB64 H VWF0 HH H68 HU HF"] Lemma CSp_range : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pu,(4.$5.)Pf,(4.$5.)Px,$<.P,(11.R3.R2.R1.)(2.(2.(8.=R2.)(9.R2.(;.+2.+2?.)))(2.(0.(8.(:.R2.+1.)+7???7000.)(8.+10007???8000.R2.))(2.(=.(2.(8.(>.(?.VAL,))R2.)(9.R2.(:.(>.(:.(?.VAL,)+7.))+40.))))(=.(2.(8.(>.(10.VAL,))R2.)(9.R2.(:.(>.(:.(10.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Proof.
    clear UF APT_U APT_F SLACK. intros u f x [A|R]; [exact (vcs0_range' x A)|].
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *).
    dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH) as (W0 & W1 & W2 & W3 & W4 & W5).
    dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). rewrite IMH in *.
    aceilb. 
    dpose HU as (U0 & U1 & U2). dpose HF as (F0 & F1 & F2).
    destruct R as [[_ R]|[_ R]]; clear - R W0 W1 W2 W5 U0 U1 F0 F1 GOT64 GSB64 H68 HG1 HG3 HS1 HS3; lia.
  Qed.

  
  
  #[using="Type"] Theorem P_CSmono_u : forall b f y, CSp None f y -> CSp (Some b) f y.
  Proof. intros b f y [A|[[E _]|A]]; [left; exact A| discriminate| right; right; exact A]. Qed.
  #[using="Type"] Theorem P_CSmono_f : forall u b y, CSp u None y -> CSp u (Some b) y.
  Proof. intros u b y [A|[A|[E _]]]; [left; exact A| right; left; exact A| discriminate]. Qed.
    #[using="Type"] Theorem P_CSUz : forall f, crange (CSp (Some true) f) UA (2^18).
  Proof. intros f x Hx. right. left. auto. Qed.
  #[using="Type"] Theorem P_CSFz : forall u, crange (CSp u (Some true)) FAA (2^18).
  Proof. intros u x Hx. right. right. auto. Qed.

  
  
  (* [comment removed for export] *)
  #[using="ASB IMH H FAA VR0 HH H68 HU HF APT_U UUN SLACK"] Lemma commit_U : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pmo,$12.P,VUOK,P,(13.VhAR,VAL,Vv0,R2.)(2.(13.VhAR,VAL,$14.(15.+32.VUA,(;.+2.+12.)R3.))(2.(3.$5.(16.(17.(18.R3.))(19.&40.VUA,)(19.&40.(;.+2.+12.)))$7.)(2.(3.$5.(1:.(1;.(18.R3.))(19.&40.VUA,)(19.&40.(;.+2.+12.)))$7.)(1<.+32.VUA,(;.+2.+12.)R3.))))")
(* [comment removed for export] *).
  Proof.
    intros mo OK K. unfold vU. apply (HKv_commit_sub AL v0 mo H UA (2^18) true VR0 K ASB ltac:(rewrite IMH; lia) HH); try lia.
    - exact (UUN OK).
    - exact (APT_U OK).
    - rewrite vnb_sub. unfold RES_POP in SLACK. lia.
  Qed.

  #[using="ASB IMH H UA VR0 HH H68 HU HF APT_F FUN SLACK"] Lemma commit_F0 : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pmo,$12.P,(13.VhAR,VAL,Vv0,R1.)(2.(13.VhAR,VAL,(1=.Vv0,)(15.+32.VFAA,(;.+2.+12.)R2.))(2.(3.$5.(16.(17.(18.R2.))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)(2.(3.$5.(1:.(1;.(18.R2.))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)(1<.+32.VFAA,(;.+2.+12.)R2.))))")
(* [comment removed for export] *).
  Proof.
    intros mo K. unfold vF. apply (HKv_commit_sub AL v0 mo H FAA (2^18) true VR0 K ASB ltac:(rewrite IMH; lia) HH); try lia.
    - exact FUN.
    - exact APT_F.
    - rewrite vnb_sub. unfold RES_POP in SLACK. lia.
  Qed.

  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN SLACK"] Lemma commit_FU : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pmo,$12.P,VUOK,P,(13.VhAR,VAL,$14.R2.)(2.(13.VhAR,VAL,(1=.$14.)(15.+32.VFAA,(;.+2.+12.)R3.))(2.(3.$5.(16.(17.(18.R3.))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)(2.(3.$5.(1:.(1;.(18.R3.))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)(1<.+32.VFAA,(;.+2.+12.)R3.))))")
(* [comment removed for export] *).
  Proof.
    pose proof HU0.
    intros mo OK K. unfold vF. apply (HKv_commit_sub AL vU mo H FAA (2^18) true ltac:(unfold vU; apply vranges_ok_add_sub; [exact VR0| lia| lia]) K ASB ltac:(rewrite IMH; lia)); try lia.
    - unfold vU. cbn. exact HH.
    - unfold vU. cbn [v_unit v_add_sub]. exact FUN.
    - intros t [<-|Ht]; [unfold t_hi; cbn; pose proof (UF OK); lia| apply APT_F; exact Ht].
    - rewrite vnb_sub. unfold vU. rewrite vnb_sub, veb_sub. unfold RES_POP in SLACK. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="UA FAA H68 HF"] Lemma hull_sub_not_free : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pv,$1>.Pmo,$12.PU,$<.P,(13.VhAR,VAL,R3.R2.)P,(1?.(20.$<.$<.)VH,(21.R4.))P,(8.(22.$<.$<.VH,)R3.)P,(8.(:.R4.(;.+2.+12.))(:.(22.$<.$<.VH,)(23.$<.$<.VH,)))P,(8.=(22.$<.$<.VH,))P,(3.$5.(1:.(24.(20.(25.&40.)(25.&40.))(1;.(18.R7.))(17.(18.R7.)))(19.&40.R6.)(19.&40.(;.+2.+12.)))$7.)$26.")
(* [comment removed for export] *).
  Proof.
    intros v mo U K HHv U0 U1 F0 RF.
    dpose K as (_ & _ & _ & _ & _ & _ & _ & _ & TBL & _ & _ & _ & VW & AT).
    dpose VW as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HHv) as (W0 & W1 & W2 & W3 & W4 & W5).
    aceilb. 
    rewrite region_free_app in RF. apply andb_prop in RF. destruct RF as [_ RF].
    assert (N18 : bv_unsigned (Z_to_bv 64 (2^18)) = 2^18) by (apply u64_lit; lia).
    assert (NU : bv_unsigned (Z_to_bv 64 U) = U) by (apply u64_lit; lia).
    pose proof (region_free_clear _ _ _ ltac:(rewrite N18; lia) RF) as CL. rewrite N18, NU in CL.
    (* [comment removed for export] *)
    destruct (hull_fresh_apart AL v _ _ _ H U (U + 2^18) TBL VW HHv CL ltac:(lia)); lia.
  Qed.

  #[using="ASB IMH H VR0 HH H68 HU HF APT_U UUN SLACK"] Theorem P_LEDGER_U : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pmo,$12.P,VUOK,P,(27.(28.$5.)(28.$5.)R2.)(2.(3.$5.(1:.(1;.(18.R3.))(19.&40.VUA,)(19.&40.(;.+2.+12.)))$7.)(0.(3.$5.(16.(17.(18.R3.))(19.&40.VUA,)(19.&40.(;.+2.+12.)))$7.)(3.$5.(1:.(24.(20.(25.&40.)(25.&40.))(1;.(18.R3.))(17.(18.R3.)))(19.&40.VUA,)(19.&40.(;.+2.+12.)))$7.)))")
(* [comment removed for export] *).
  Proof. intros mo OK K. cbn [Kp] in K. ddestruct (commit_U mo OK K) as (_ & MC & RF & _). auto. Qed.

  #[using="ASB IMH H VR0 HH H68 HU HF APT_U UUN SLACK"] Theorem P_TU_commit : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pmo,$12.P,VUOK,P,(27.(28.$5.)(28.$5.)R2.)P,(3.$5.(16.(17.(18.R3.))(19.&40.VUA,)(19.&40.(;.+2.+12.)))$7.)(27.(6.$5.$7.)(28.$5.)(15.+32.VUA,(;.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof. intros mo OK K _. cbn [Kp] in K |- *. exact (conj OK (proj1 (commit_U mo OK K))). Qed.

  #[using="H HH H68 HU HF"] Theorem P_TU_fresh : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pmo,$12.P,VUOK,P,(27.(28.$5.)(28.$5.)R2.)P,(3.$5.(1:.(24.(20.(25.&40.)(25.&40.))(1;.(18.R3.))(17.(18.R3.)))(19.&40.VUA,)(19.&40.(;.+2.+12.)))$7.)(27.(6.$5.$7.)(28.$5.)(29.+32.VUA,(;.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof. intros mo OK K RF. cbn [Kp] in K. exfalso. pose proof HU. eapply (hull_sub_not_free v0 mo UA K HH); try lia. exact RF. Qed.

  #[using="ASB IMH H VR0 HH H68 HU HF APT_U UUN SLACK"] Theorem P_ROOM_U : forall mo, UOK -> Kp None None mo -> fixrw_grantable 0x32 UA (2^18) mo.
  Proof. intros mo OK K. cbn [Kp] in K. exact (proj2 (proj2 (proj2 (commit_U mo OK K)))). Qed.

  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN SLACK"] Theorem P_LEDGER_F : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pu,(4.$5.)Pmo,$12.P,(0.(3.(4.$5.)R2.(28.$5.))(3.(4.$5.)R2.(6.$5.$7.)))P,(27.R3.(28.$5.)R2.)(2.(3.$5.(1:.(1;.(18.R3.))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)(0.(3.$5.(16.(17.(18.R3.))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)(3.$5.(1:.(24.(20.(25.&40.)(25.&40.))(1;.(18.R3.))(17.(18.R3.)))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)))")
(* [comment removed for export] *).
  Proof.
    intros u mo [-> | ->] K; cbn in K.
    - ddestruct (commit_F0 mo K) as (_ & MC & RF & _). auto.
    - destruct K as [OK K]. ddestruct (commit_FU mo OK K) as (_ & MC & RF & _). auto.
  Qed.

  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN SLACK"] Theorem P_TF_commit : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pu,(4.$5.)Pmo,$12.P,(0.(3.(4.$5.)R2.(28.$5.))(3.(4.$5.)R2.(6.$5.$7.)))P,(27.R3.(28.$5.)R2.)P,(3.$5.(16.(17.(18.R3.))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)(27.R5.(6.$5.$7.)(15.+32.VFAA,(;.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros u mo [-> | ->] K _; cbn [Kp] in K |- *.
    - exact (proj1 (commit_F0 mo K)).
    - destruct K as [OK K]. exact (conj OK (proj1 (commit_FU mo OK K))).
  Qed.

  #[using="H HH H68 HF"] Theorem P_TF_fresh : ltac2:(CDefT.buildp (gd_tbl_AInstPop ()) "Pu,(4.$5.)Pmo,$12.P,(0.(3.(4.$5.)R2.(28.$5.))(3.(4.$5.)R2.(6.$5.$7.)))P,(27.R3.(28.$5.)R2.)P,(3.$5.(1:.(24.(20.(25.&40.)(25.&40.))(1;.(18.R3.))(17.(18.R3.)))(19.&40.VFAA,)(19.&40.(;.+2.+12.)))$7.)(27.R5.(6.$5.$7.)(29.+32.VFAA,(;.+2.+12.)R4.))")
(* [comment removed for export] *).
  Proof.
    pose proof HF.
    intros u mo [-> | ->] K RF; cbn [Kp] in K; exfalso.
    - eapply (hull_sub_not_free v0 mo FAA K HH); try lia. exact RF.
    - destruct K as [OK K]. eapply (hull_sub_not_free vU mo FAA K); try lia; [unfold vU; cbn; exact HH| exact RF].
  Qed.

  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN SLACK"] Theorem P_ROOM_F : forall u mo, (u = None \/ u = Some true) -> Kp u None mo -> fixrw_grantable 0x32 FAA (2^18) mo.
  Proof.
    intros u mo [-> | ->] K; cbn in K.
    - exact (proj2 (proj2 (proj2 (commit_F0 mo K)))).
    - destruct K as [OK K]. exact (proj2 (proj2 (proj2 (commit_FU mo OK K)))).
  Qed.

  (* [comment removed for export] *)
  #[using="hAR AL v0 UA FAA VWF0 HH H68 HU HF"] Lemma H_band : forall U, fst H <= U -> U + 2^18 <= fst H + snd H -> U + 2^18 <= 0x7fff7000 \/ 0x10007fff8000 <= U.
  Proof.
    intros U A B. dpose VWF0 as (_ & _ & HWF & _). pose proof (proj1 (Forall_forall _ _) HWF H HH) as (_ & _ & _ & _ & _ & BND). lia.
  Qed.

  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF APT_U UUN HC"] Theorem P_SCAR_U : UOK -> scar_site AL (CSp None None) (Kp None None) UA (2^18).
  Proof.
    intros OK. dpose HU as (U0 & U1 & U2).
    eapply scar_site_mono; [| intros x Hx; exact (proj1 (CSp_00 x) Hx)]. cbn [Kp].
    apply (HKv_scar_site AL ASB ltac:(rewrite IMH; lia) v0 UA (2^18) VR0 (UUN OK) ltac:(lia) (H_band UA U0 U1) ltac:(unfold JW; lia) (APT_U OK)).
    - exists H. split; [exact HC| lia].
    - exists H. split; [exact HH| lia].
  Qed.

  #[using="ASB IMH H VR0 VWF0 HH H68 HU HF UF APT_F FUN HC"] Theorem P_SCAR_F : forall u, (u = None \/ u = Some true) -> scar_site AL (CSp u None) (Kp u None) FAA (2^18).
  Proof.
    pose proof HU0. dpose HF as (F0 & F1 & F2). intros u [-> | ->]; cbn [Kp].
    - eapply scar_site_mono; [| intros x Hx; exact (proj1 (CSp_00 x) Hx)].
      apply (HKv_scar_site AL ASB ltac:(rewrite IMH; lia) v0 FAA (2^18) VR0 FUN ltac:(lia) (H_band FAA F0 F1) ltac:(unfold JW; lia) APT_F).
      + exists H. split; [exact HC| lia].
      + exists H. split; [exact HH| lia].
    - eapply scar_site_mono; [| intros x Hx; exact (proj1 (CSp_U0 x) Hx)].
      apply (HKv_scar_site_guard AL ASB ltac:(rewrite IMH; lia) UOK vU FAA (2^18)).
      + intros _. unfold vU. apply vranges_ok_add_sub; [exact VR0| lia| lia].
      + intros _. unfold vU. cbn [v_unit v_add_sub]. exact FUN.
      + lia.
      + exact (H_band FAA F0 F1).
      + unfold JW; lia.
      + intros OK t [<-|Ht]; [unfold t_hi; cbn; pose proof (UF OK); lia| apply APT_F; exact Ht].
      + exists H. unfold vU. cbn [v_cover v_add_sub]. split; [exact HC| lia].
      + exists H. unfold vU. cbn [v_hulls v_add_sub]. split; [exact HH| lia].
  Qed.

  (* [comment removed for export] *)
  Definition vp (u f : option bool) : vst :=
    match u, f with
    | Some true, Some true => vF vU | Some true, _ => vU | _, Some true => vF v0 | _, _ => v0 end.
  End InstPop.

End ARUN_1.
