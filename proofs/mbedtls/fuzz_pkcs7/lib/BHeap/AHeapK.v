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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM AHeapR.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
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
Ltac2 gd_tbl_AHeapK () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.fixed_of"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.lkind"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_kind"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_len"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_extra"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KLazy"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_cs"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.gxok"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.in_ghost"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base_of"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vgood"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcsA"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vranges_ok"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.ainv_std"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.APOTv"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HK_i"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"].

Section ARUN_1. Context {hAR : arun}.
Section K.
  Variable STKLO : Z.
  Local Notation hok := (hok STKLO).

  (* [comment removed for export] *)
  #[using="Type"] Lemma units_of_kind : forall h t, In t (units_of h) -> t_kind t = KEager.
  Proof.
    intros h t Ht. unfold units_of in Ht. apply in_flat_map in Ht. ddestruct Ht as (c & _ & Ht). apply in_app_iff in Ht.
    destruct Ht as [Ht|Ht]; apply in_map_iff in Ht; ddestruct Ht as (j & <- & _); reflexivity.
  Qed.

  #[using="Type"] Lemma fixed_of_kinds : ltac2:(CDefT.buildp (gd_tbl_AHeapK ()) "PL,$0.Pt,$1.P,(2.$1.R1.(3.R2.))(4.(5.$6.(7.R2.)$8.)(4.(9.(:.+7???7000.(;.R2.))(:.(<.R2.)$=.))(2.(>.$?.$?.)(10.$?.$?.(;.R2.)(11.R2.))(12.R3.))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Proof.
    intros L t Ht. unfold fixed_of in Ht. apply in_app_iff in Ht. destruct Ht as [Ht|Ht].
    - destruct Ht as [<-|[<-|[<-|[<-|[]]]]]; left; reflexivity.
    - apply in_app_iff in Ht. destruct Ht as [Ht|Ht].
      + apply in_map_iff in Ht. ddestruct Ht as ([b1 b2] & <- & Hb). right. right. cbn [t_lo t_len fst snd]. exact Hb.   (* [comment removed for export] *)
      + destruct Ht as [<-|[<-|[<-|[]]]]; right; left; unfold t_hi, kHighMemBeg; cbn; split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma tr_of_kinds : ltac2:(CDefT.buildp (gd_tbl_AHeapK ()) "Ph,$13.Pt,$1.P,(2.$1.R1.(14.R2.))(4.(5.$6.(7.R2.)$8.)(4.(9.(5.$6.(7.R2.)$15.)(5.$16.(17.R2.)$18.))(4.(9.(:.+7???7000.(;.R2.))(:.(<.R2.)$=.))(2.(>.$?.$?.)(10.$?.$?.(;.R2.)(11.R2.))(12.(19.R3.))))))")
(* [comment removed for export] *).
  Proof.
    intros h t Ht. unfold tr_of in Ht.
    apply in_app_iff in Ht. destruct Ht as [Ht|Ht]. { apply in_map_iff in Ht. ddestruct Ht as (b & <- & _). left. reflexivity. }
    apply in_app_iff in Ht. destruct Ht as [Ht|Ht]. { apply in_map_iff in Ht. ddestruct Ht as (b & <- & _). right. left. split; reflexivity. }
    apply in_app_iff in Ht. destruct Ht as [Ht|Ht]. { apply in_map_iff in Ht. ddestruct Ht as (b & <- & _). left. reflexivity. }
    apply in_app_iff in Ht. destruct Ht as [Ht|Ht]. { left. exact (units_of_kind h t Ht). }
    apply in_app_iff in Ht. destruct Ht as [Ht|Ht]. { destruct Ht as [<-|[]]. left. reflexivity. }
    apply in_app_iff in Ht. destruct Ht as [Ht|Ht]. { apply in_map_iff in Ht. ddestruct Ht as (b & <- & _). left. reflexivity. }
    apply in_app_iff in Ht. destruct Ht as [Ht|Ht].
    2:{ (* [comment removed for export] *)
        unfold emb_tr in Ht. destruct (a_emb (h_acct h) =? 0); [destruct Ht| destruct Ht as [<-|[]]; left; reflexivity]. }
    destruct (fixed_of_kinds (h_L h) t Ht) as [E|[E|E]]; [left; exact E| right; right; left; exact E| right; right; right; exact E].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ghost_lazy_good : ltac2:(CDefT.buildp (gd_tbl_AHeapK ()) "Ph,$13.Pmo,$1:.Px,$?.P,(1;.VhAR,VSTKLO,R3.)P,(1<.VhAR,$1=.R4.R3.)P,(1>.R5.)P,(1?.R6.R4.)P,(5.$16.(20.(21.R5.)(22.R6.))$18.)(23.$1=.(24.R8.)(21.R6.))")
(* [comment removed for export] *).
  Proof.
    (intros h mo x HOK [K VR] GX dd_H; ddestruct dd_H as (g & Hg & Rg); intros PL).
    dpose (ghost_wf STKLO h g HOK Hg) as (G0 & G1 & G2 & G3 & G4 & G5). unfold kHighMemBeg in G0.
    dpose HOK as (EL & AW & VW). dpose AW as ([WL _] & _ & _ & _ & _ & _ & _ & _ & _ & _ & WG).
    pose proof (proj1 (Forall_forall _ _) WG g Hg) as (_ & _ & _ & _ & _ & AP6 & APA).
    ddestruct K as (Hh & ND & GD & LZ & LIM & EB & BUD & WF & TB & _).
    ddestruct TB as (TF & NC & LC & HL & (UNC & MPOS & LZK & _) & NDM & MA & NZN & NZL & BAND).
    dpose VW as (TWF & _ & HWF & _).
    ddestruct (page_base_of_facts x ltac:(clear - G0 G2 Rg; lia)) as (P1 & P2 & P3).
    set (p := bv_unsigned (page_base_of x)) in *.
    apply page_in_ranges_true in PL. ddestruct PL as (e & He & E1 & E2). fold p in E1, E2. unfold page_size in E2.
    pose proof (NZL e He) as EZ.
    (* [comment removed for export] *)
    destruct (LZK e He p ltac:(clear - E1 E2 EZ; lia)) as [(t & Ht & TL & ET)|(U9 & n9 & HU9 & RU)].
    - pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & T3 & T4 & _).
      assert (XT : t_lo t <= x < t_hi t).
      { unfold t_hi in *. pose proof (Z.div_mod (t_lo t) 4096 ltac:(lia)). pose proof (Z.div_mod (t_len t) 4096 ltac:(lia)). pose proof (Z.div_mod p 4096 ltac:(lia)).
        clear - ET P1 P2 P3 T3 T4 H H0 H1. lia. }
      destruct (tr_of_kinds h t Ht) as [KE|[[KL TC]|[LOW|EXT]]].
      + (* [comment removed for export] *)
        exfalso. pose proof (proj1 (Forall_forall _ _) TF t Ht) as (_ & _ & KF). rewrite KE in KF. destruct KF as [_ CL].
        destruct (CL e He) as [X|X]; unfold t_hi in X, ET; clear - X E1 E2 ET P1 P2 EZ; lia.
      + (* [comment removed for export] *)
        unfold vgood, vgood_b. apply Bool.orb_true_iff. right. apply existsb_exists.
        exists (t_lo t, t_len t). split.
        { unfold lazyranges. apply in_map_iff. exists t. split; [reflexivity|]. apply filter_In. split; [exact Ht|]. unfold is_lazy_cs. rewrite KL. exact TC. }
        unfold pg_inside_b. cbn [fst snd]. fold p.
        apply andb_true_intro; split; [apply andb_true_intro; split; apply Z.leb_le| apply Z.eqb_eq; exact P3].
        * clear - ET. lia.
        * pose proof (Z.div_mod (t_lo t) 4096 ltac:(lia)). pose proof (Z.div_mod (t_len t) 4096 ltac:(lia)). pose proof (Z.div_mod p 4096 ltac:(lia)).
          unfold t_hi in ET. clear - ET P1 P2 P3 T3 T4 H H0 H1. lia.
      + exfalso. unfold kHighMemBeg in LOW, G5. clear - LOW XT G0 G5 Rg. lia.   (* [comment removed for export] *)
      + (* [comment removed for export] *)
        exfalso. unfold gxok in GX. pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) GX g Hg) _ EXT) as AP. cbn [fst snd] in AP.
        unfold t_hi in XT. clear - AP XT Rg. lia.
    - (* [comment removed for export] *)
      exfalso. cbn [vst_of v_unit] in HU9.
      pose proof (units_of_L_inside (h_L h) U9 n9 WL HU9) as INS. dpose (units_of_L_wf (h_L h) U9 n9 WL HU9) as (_ & _ & _ & UA9 & NA9).
      assert (XU : U9 <= x < U9 + n9).
      { pose proof (Z.div_mod U9 4096 ltac:(lia)). pose proof (Z.div_mod n9 4096 ltac:(lia)). pose proof (Z.div_mod p 4096 ltac:(lia)).
        clear - RU P1 P2 P3 UA9 NA9 H H0 H1. lia. }
      unfold kPrimHullLen, kPaHullLen in INS. clear - INS XU AP6 APA Rg. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ghost_shadow_good : forall h x, hok h -> in_ghost h x -> vgood AL0 (vst_of h) (page_base_of (shadow_of AL0 x)).
  Proof.
    (intros h x HOK dd_H; ddestruct dd_H as (g & Hg & Rg)). dpose (ghost_wf STKLO h g HOK Hg) as (G0 & G1 & G2 & G3 & G4 & G5). unfold kHighMemBeg in G0.
    unfold vgood, vgood_b. apply Bool.orb_true_iff. left. apply existsb_exists.
    exists g. split. { unfold csranges. right. right. apply in_app_iff. right. cbn [vst_of v_ghost]. apply in_app_iff. left. exact Hg. }
    destruct g as [lo len]. cbn [fst snd] in *. apply pg_shadow_hit; [cbn; lia| clear - G0; lia| exact Rg|].
    unfold shadow_of, AL0. cbn [al_sb]. clear - G0 G2 Rg. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
  Qed.

  #[using="Type"] Lemma HK_lz : ltac2:(CDefT.buildp (gd_tbl_AHeapK ()) "Ph,$13.Pmo,$1:.Px,$?.P,(1;.VhAR,VSTKLO,R3.)P,(1<.VhAR,$1=.R4.R3.)P,(1>.R5.)P,(25.$1=.(26.R6.)R4.)P,(5.$16.(20.(21.R5.)(22.R6.))$18.)(23.$1=.(24.R8.)(21.R6.))")
(* [comment removed for export] *).
  Proof.
    intros h mo x HOK HKK GX AOK PL. pose proof HKK as [(Hh & ND & GD & LZ & _) VR].
    destruct AOK as [[V|G]|[(c & [V|G] & ->)|I]].
    - apply LZ; [left; exact V| exact PL].
    - exact (ghost_lazy_good h mo x HOK HKK GX G PL).
    - apply LZ; [right; left; exists c; split; [exact V| reflexivity]| exact PL].
    - exact (ghost_shadow_good h c HOK G).
    - apply LZ; [right; right; exact I| exact PL].
  Qed.

  #[using="Type"] Lemma HK_ainv : ltac2:(CDefT.buildp (gd_tbl_AHeapK ()) "Ph,$13.Pmo,$1:.PW,(27.$1=.(24.R2.))P,(1;.VhAR,VSTKLO,R3.)P,(1<.VhAR,$1=.R4.R3.)P,(1>.R5.)(28.$1=.(29.$1=.(24.R6.)R4.)(26.R6.)R5.)")
(* [comment removed for export] *).
  Proof.
    intros h mo W HOK HKK GX. pose proof HKK as [(Hh & ND & GD & LZ & LIM & EB & BUD & _) VR].
    split; [exact Hh|]. split; [exact ND|]. split; [exact GD|]. split; [intros x AOK PL; exact (HK_lz h mo x HOK HKK GX AOK PL)|].
    cbn [ap_nb APOTv]. rewrite LIM. unfold page_size. clear - EB BUD. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma hk_halted_i : forall (s : hst STKLO) mo, HK_i STKLO s mo -> m_halted mo = None.
  Proof. (intros s mo dd_H; ddestruct dd_H as [[(Hh & _) _] _]). exact Hh. Qed.

  #[using="Type"] Lemma hk_mat_i : ltac2:(CDefT.buildp (gd_tbl_AHeapK ()) "Ps,(2:.VhAR,VSTKLO,)Pmo,$1:.Pacc,(2;.(>.(2<.&40.)$2=.))P,(2>.VhAR,VSTKLO,R3.R2.)P,(2?.$1=.(30.VhAR,VSTKLO,R4.)R2.)(31.$1:.Lmo',$1:.(9.(5.(32.$1:.)(33.R5.R4.)(34.$1:.R1.))(9.(2>.VhAR,VSTKLO,R6.R1.)(35.R5.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] mo acc [HKK GX] OK. unfold HK_i, hcs_i in *. cbn [hh] in *. pose proof HKK as [K VR].
    ddestruct (ai_mat (ainv_std_laws AL0 (APOTv AL0 (vst_of h) VR)) (hcsA h) mo acc (HK_ainv h mo VR HOK HKK GX) OK) as (mo' & E & AI' & MM).
    exists mo'. split; [exact E|]. split; [| exact MM].
    ddestruct AI' as (Hh' & ND' & GD' & _). split; [| exact GX]. split; [exact (HKv_mat_back AL0 (vst_of h) mo mo' K MM Hh' ND' GD')| exact VR].
  Qed.

  #[using="Type"] Lemma hk_vmonly_i : ltac2:(CDefT.buildp (gd_tbl_AHeapK ()) "Ps,(2:.VhAR,VSTKLO,)Pmo,$1:.Pmo',$1:.P,(2>.VhAR,VSTKLO,R3.R2.)P,(5.$36.(37.R2.)(37.R3.))P,(5.(2;.(>.(2<.&40.)(2<.&40.)))(22.R3.)(22.R4.))P,(5.(2;.(2<.&40.))(38.R4.)(38.R5.))P,(5.(32.(2<.&40.))(39.R5.)(39.R6.))(2>.VhAR,VSTKLO,R8.R6.)")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] mo mo' [[K VR] GX] E1 E2 E3 E4. unfold HK_i in *. cbn [hh] in *. split; [| exact GX]. split; [| exact VR].
    ddestruct K as (Hh & ND & GD & LZ & LIM & EB & BUD & WF & TB & CE & RS & RC & VW & AT).
    unfold HKv. unfold eager_bytes, model_ivs_wf in *. rewrite E1, E2, E3, E4.
    repeat (split; [assumption|]). exact AT.
  Qed.
End K.

End ARUN_1.
