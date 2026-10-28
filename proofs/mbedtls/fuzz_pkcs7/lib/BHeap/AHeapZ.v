(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame AW_DepotB AW_DepotTop AW_MallocB
     AW_Refill AW_FakeDefs AW_FakeRep AHeapR AHeapB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AHeapZ () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "ARUN_1.ranges_cover_b"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ro_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.rwstat_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.dep_zone"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.quar_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.sec_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ia_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.emb_ranges"; "ARUN_1.IMGZ"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.in_rangesZ"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.shad"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_alloc_user"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_errno"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.iagree"].

Section ARUN_1. Context {hAR : arun}.
Definition IMGZ : list (Z * Z) :=
  (0x10000, 0x0fa360) :: RT ++ [(0x65dab0, 0x65f000); (0x7fffa000, 0x800c3e00)].   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ranges_cover_b (l c : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | (lo, hi) :: l' => range_in_b c lo (hi - lo) && ranges_cover_b l' c
  end.

#[using="Type"] Lemma ranges_cover_b_sound : forall l c a, ranges_cover_b l c = true -> in_rangesZ l a -> in_rangesZ c a.
Proof.
  induction l as [|[lo hi] l IH]; intros c a H Ha; [destruct Ha|]. cbn in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct Ha as [Ha|Ha]; [| exact (IH c a H2 Ha)]. eapply range_in_b_sound; [exact H1| lia].
Qed.

#[using="Type"] Lemma hm_img_cover : ltac2:(CDefT.buildp (gd_tbl_AHeapZ ()) "(0.$1.(2.(3.(4.$5.$5.)$6.(3.(4.$5.$5.)$7.(3.(4.$5.$5.)$8.(3.(4.$5.$5.)$9.(3.(4.$5.$5.)$:.(3.(4.$5.$5.)$;.$<.))))))$=.)$>.)")
(* [comment removed for export] *).
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition rtc_cells_in_b : bool :=
  forallb (fun c : rtc_cell => let '(a, n, v) := c in range_in_b IMGZ a (Z.of_nat (cells_size [rtc_mkcell n v]))) rtc_cells.
#[using="Type"] Lemma rtc_cells_cover : rtc_cells_in_b = true. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma rtc_prist_cover : ranges_cover_b rtc_pristine IMGZ = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rzone (h : ahst) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapZ ()) "ZL,$?.(10.O2.)(11.(12.$=.O1.)(11.(13.(14.(15.R1.)O1.)(16.O1.(17.(15.R1.)+1000.)))(11.(13.(14.(18.R1.)O1.)(16.O1.(17.(18.R1.)(19.R1.))))(11.(1:.$5.Lb,$5.(13.(1;.$5.R1.(1<.(1=.O2.)))(13.(14.R1.O1.)(16.O1.(17.R1.(1>.+2.+14.))))))(11.(1:.$5.Lb,$5.(13.(1;.$5.R1.(1?.(1=.O2.)))(13.(14.R1.O1.)(16.O1.(17.R1.(1>.+2.+17.))))))(11.(1:.$20.Lk,$20.(13.(1;.$20.R1.(21.O2.))(13.(14.(22.R1.)O1.)(16.O1.(23.R1.)))))(11.(1:.$20.Lk,$20.(13.(1;.$20.R1.(21.O2.))(13.(0.$5.(24.R1.)$25.)(13.(14.(26.(23.R1.))O1.)(16.O1.(17.(26.(23.R1.))(27.(17.(28.(29.R1.))+7.)+8.)))))))(11.(1:.$20.Lk,$20.(13.(1;.$20.R1.(21.O2.))(13.(2:.(0.$5.(24.R1.)$25.))(13.(14.(23.R1.)O1.)(16.O1.(17.(23.R1.)+8.))))))(11.(1:.$5.Lc,$5.(13.(13.(14.+1.R1.)(14.R1.+1?.))(13.(14.(2;.R2.R1.)O1.)(16.O1.(17.(2;.R2.R1.)+60.)))))(11.(1:.$5.Lc,$5.(13.(13.(14.+1.R1.)(14.R1.+1?.))(13.(14.(2<.R2.R1.)O1.)(16.O1.(17.(2<.R2.R1.)(2=.(2>.O2.R1.)))))))(11.(1:.$5.Lc,$5.(13.(13.(14.+1.R1.)(14.R1.+1?.))Zr,$2?.(2>.O2.R1.)(13.(14.(26.(17.(30.R3.R2.)(31.R1.)))O1.)(16.O1.(17.(26.(17.(30.R3.R2.)(31.R1.)))(27.(32.(33.R1.)(31.R1.))+8.))))))(11.(1:.$5.Lc,$5.(1:.$5.Lk,$5.(13.(13.(14.+1.R2.)(14.R2.+1?.))(13.(13.(14.=R1.)(16.R1.(27.(31.(2>.O2.R2.))(34.R2.))))(0.$5.O1.(26.(35.R3.R2.R1.)))))))(11.(1:.$36.Lb,$36.(13.(1;.$36.R1.(3.$36.(37.(38.O2.))(37.(39.O2.))))(13.(14.(3:.R1.)O1.)(16.O1.(17.(3:.R1.)+2000.)))))(11.(13.(14.(3;.R1.)O1.)(16.O1.(17.(3;.R1.)(3<.O2.))))(11.(1:.$3=.Lsh,$3=.(13.(1;.$3=.R1.(3>.(3?.O2.)))(13.(14.(40.R1.)O1.)(16.O1.(17.(40.R1.)+20.)))))(13.(14.(41.R1.)O1.)(16.O1.(17.(41.R1.)+1000.))))))))))))))))))")
(* [comment removed for export] *).

Definition fzone (h : ahst) (LF : list blk) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapZ ()) "(11.(13.(14.(42.(10.O3.))O1.)(16.O1.(17.(42.(10.O3.))+9000.)))(1:.$43.Lfb,$43.(13.(1;.$43.R1.O2.)(13.(14.(32.(17.(44.$5.$5.R1.)(45.$5.$5.R1.))+8.)O1.)(16.O1.(17.(44.$5.$5.R1.)(45.$5.$5.R1.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition zagree (P : Z -> Prop) (m m' : mem) : Prop := forall x : word, P (bv_unsigned x) -> m' x = m x.

#[using="Type"] Lemma kept_of_zagree : forall P m m' A n, zagree P m m' -> (forall a, A <= a < A + n -> P a) -> kept m m' A n.
Proof. intros P m m' A n AG H x Hx. apply AG, H, Hx. Qed.

#[using="Type"] Lemma iagree_of_zagree : forall P RS m m', zagree P m m' -> (forall a, in_rangesZ RS a -> P a) -> iagree RS m m'.
Proof. intros P RS m m' AG H x Hx. apply AG, H, Hx. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFrame.
  Variable STKLO : Z.
  Local Notation hok := (hok STKLO).
  Variables (h : ahst) (m m' : mem).
  Hypothesis HOK : hok h.
  Hypothesis WM : wmono asegs m m'.
  Hypothesis AG : zagree (rzone h) m m'.

  #[using="Type"] Lemma in_rangesZ_app : forall l1 l2 a, in_rangesZ (l1 ++ l2) a <-> in_rangesZ l1 a \/ in_rangesZ l2 a.
  Proof. induction l1 as [|[lo hi] l1 IH]; intros l2 a; cbn; [tauto|]. rewrite IH. tauto. Qed.

  #[using="h AG"] Lemma zimg_sub : ltac2:(CDefT.buildp (gd_tbl_AHeapZ ()) "PRS,(46.(4.$5.$5.))P,Pa,$5.P,(12.R2.R1.)(12.(3.(4.$5.$5.)$6.(3.(4.$5.$5.)$7.(3.(4.$5.$5.)$8.(3.(4.$5.$5.)$9.(3.(4.$5.$5.)$:.(3.(4.$5.$5.)$;.$<.))))))R2.)(47.R2.Vm,Vm',)")
(* [comment removed for export] *).
  Proof.
    intros RS SUB. eapply (iagree_of_zagree _ RS m m' AG). intros a Ha. left. apply (ranges_cover_b_sound _ IMGZ a hm_img_cover). apply SUB, Ha.
  Qed.

  #[using="AG"] Lemma kz : forall A n, (forall a, A <= a < A + n -> rzone h a) -> kept m m' A n.
  Proof. intros A n H. eapply kept_of_zagree; [exact AG| exact H]. Qed.

  #[using="STKLO HOK WM AG"] Theorem HMc_zframe : forall LB LF LF', HMc h LB LF m -> hm_fake h LF' m' -> HMc h LB LF' m'.
  Proof.
    intros LB LF LF' HM0 GF'. dpose HOK as (EL & AW & VW).
    dpose HM0 as (HP & GM & (GRO & GRW) & GT & GD & GC & GR & GQ & GS & GF & GI & GE).
    dpose AW as ([WL _] & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    assert (TLO : Timg (l_T (h_L h)) /\ 0 <= l_fs (h_L h)) by (unfold wf_L, lowhigh, kHighMemBeg in WL; clear - WL; lia).
    dpose GM as (_ & _ & _ & WRT & _).
    split; [exact HP|]. split; [exact (hm_maps_frame _ _ _ GM WM)|].
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [exact GF'| split]]]]]]]].
    - (* [comment removed for export] *) split.
      + eapply hm_ro_frame; [exact GRO| | | | |].
        * apply zimg_sub. intros a Ha. rewrite !in_rangesZ_app. tauto.
        * apply kz. intros a Ha. right; left. clear - Ha. lia.
        * apply kz. intros a Ha. right; right; left. unfold wf_L in WL. clear - Ha WL. lia.
        * apply kz. intros a Ha. right; right; left. unfold wf_L in WL. clear - Ha WL. lia.
        * apply kz. intros a Ha. do 15 right. clear - Ha. lia.
      + eapply hm_rwstat_frame; [exact WM| exact GRW|]. apply zimg_sub. intros a Ha. rewrite !in_rangesZ_app. tauto.
    - (* [comment removed for export] *) eapply hm_thread_frame; [exact WM| exact GT| | | | exact WRT| clear - TLO; lia].
      + apply kz. intros a Ha. right; left. clear - Ha. lia.
      + intros c Hc. apply kz. intros a Ha. right; left. clear - Ha Hc. lia.
      + apply kz. intros a Ha. right; left. clear - Ha. lia.
    - (* [comment removed for export] *) eapply hm_depot_frame; [exact GD| exact WM| | |].
      + apply zimg_sub. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + intros b Hb. apply kz. intros a Ha. do 3 right; left. exists b. auto.
      + intros b Hb. apply kz. intros a Ha. do 4 right; left. exists b. auto.
    - (* [comment removed for export] *) eapply hm_chunks_frame; [exact WM| exact GC| exact AW|]. intros k Hk. split; [| split].
      + apply kz. intros a Ha. do 5 right; left. exists k. split; [exact Hk|]. unfold ck_user. clear - Ha. lia.
      + intros ST. apply kz. intros a Ha. do 6 right; left. exists k. auto.
      + intros ST. apply kz. intros a Ha. do 7 right; left. exists k. auto.
    - (* [comment removed for export] *) eapply hm_regions_frame; [exact WM| exact GR| exact WR|]. intros c Hc. split; [| split; [| split]].
      + apply kz. intros a Ha. do 8 right; left. exists c. auto.
      + apply kz. intros a Ha. do 9 right; left. exists c. auto.
      + apply kz. intros a Ha. do 10 right; left. exists c. split; [exact Hc|]. cbn zeta. exact Ha.
      + intros k Hk. apply kz. intros a Ha. do 11 right; left. dexists c, k. split; [exact Hc|]. split; [exact Hk|]. clear - Ha. lia.
    - (* [comment removed for export] *) eapply hm_quar_frame; [exact WM| exact GQ| | |].
      + apply zimg_sub. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + apply kz. intros a Ha. right; left. clear - Ha. lia.
      + intros b Hb. apply kz. intros a Ha. do 12 right; left. exists b. auto.
    - (* [comment removed for export] *) eapply hm_sec_frame; [exact WM| exact GS| exact WS| | |].
      + apply zimg_sub. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + apply kz. intros a Ha. do 13 right; left. exact Ha.
      + intros sh Hsh. apply kz. intros a Ha. do 14 right; left. exists sh. auto.
    - (* [comment removed for export] *) eapply hm_ia_frame; [exact WM| exact GI|]. apply zimg_sub. intros a Ha. rewrite !in_rangesZ_app. tauto.
    - (* [comment removed for export] *) eapply hm_emb_frame_i; [exact WM| exact GE| reflexivity| reflexivity|]. apply zimg_sub. intros a Ha. rewrite !in_rangesZ_app. tauto.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR STKLO HOK WM"] Lemma hm_fake_zframe : forall LF, hm_fake h LF m -> zagree (fzone h LF) m m' -> hm_fake h LF m'.
  Proof.
    intros LF GF AGF. dpose HOK as (EL & AW & VW). pose proof AW as ([WL _] & _).
    eapply hm_fake_frame; [exact WM| exact GF| unfold wf_L, lowhigh, kHighMemBeg in WL; clear - WL; lia| |].
    - eapply kept_of_zagree; [exact AGF|]. intros a Ha. left. exact Ha.
    - intros FB n HIn. eapply kept_of_zagree; [exact AGF|]. intros a Ha. right. exists (FB, n). split; [exact HIn|]. cbn [fst snd]. clear - Ha. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="h AG"] Lemma XR_zframe : XR m -> XR m'.
  Proof.
    (intros dd_H; ddestruct dd_H as ([RC PR] & ISH & XF)). split; [split| split].
    - apply Forall_forall. intros [[a n] v] Hin. pose proof (proj1 (Forall_forall _ _) RC _ Hin) as H. unfold rtc_holds in H |- *.
      pose proof rtc_cells_cover as CV. unfold rtc_cells_in_b in CV. rewrite forallb_forall in CV. specialize (CV _ Hin). cbn beta iota in CV.
      eapply keep_ro; [exact H|]. apply kz. intros x Hx. left. eapply range_in_b_sound; [exact CV| exact Hx].
    - intros a Ha. pose proof (PR a Ha) as E. unfold rtc_prist in Ha.
      assert (IN : in_rangesZ rtc_pristine a).
      { clear - Ha. unfold rtc_pristine in *. apply Exists_exists in Ha. ddestruct Ha as ([lo hi] & Hin & R). cbn in R.
        cbn in Hin. cbn. destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as <- <-; unfold AGLOB_LO, AGLOB_HI in *; lia. }
      pose proof (ranges_cover_b_sound _ _ a rtc_prist_cover IN) as INZ.
      assert (RA : 0 <= a < 2^64).
      { clear - INZ. unfold IMGZ, RT in INZ. cbn in INZ. lia. }
      rewrite <- E. pose proof (AG (wa a)) as X. rewrite wa_unsigned in X by exact RA. apply X. left. exact INZ.
    - intros g Hg NR. pose proof (ISH g Hg NR) as B.
      eapply (bytes_at_transport _ _ m m'); [exact B| apply (kept_munch m m' (shadow_of AL0 (8 * g)) 1); [unfold shadow_of, AL0; cbn; clear - Hg; unfold IMG_GLO in Hg; lia|]|].
      + apply kz. intros a Ha. left. unfold shadow_of, AL0, IMG_GLO, IMG_GHI in *. cbn [al_sb] in Ha.
        rewrite Z.mul_comm, Z.div_mul in Ha by lia. unfold IMGZ, RT. cbn. clear - Ha Hg. lia.
      + cbn [disjoint_from length Z.of_nat Pos.of_succ_nat]. unfold shadow_of. clear. repeat split; lia.
    - unfold xf_cells in *. eapply keep_ro; [exact XF|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      apply kz. intros a Ha. left. unfold A_FLAGS in Ha. unfold IMGZ, RT. cbn [in_rangesZ app]. clear - Ha. lia.
  Qed.
End ZFrame.

End ARUN_1.
