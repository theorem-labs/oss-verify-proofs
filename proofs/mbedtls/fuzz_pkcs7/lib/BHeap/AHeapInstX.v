(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame AHeapR AHeapB AHeapM.
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
Ltac2 gd_tbl_AHeapInstX () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HM_i"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hstkhi_i"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "Corelib.Init.Datatypes.None"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Lists.ListDef.map"; "Stdlib.Lists.List.filter"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "Stdlib.Lists.List.find"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_hdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.htop_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hflag_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.havol_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hfr_i"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HK_i"].

Section ARUN_1. Context {hAR : arun}.
Section SSMAP.
  Variable STKLO : Z.

  #[using="Type"] Lemma ssmap_i : ltac2:(CDefT.buildp (gd_tbl_AHeapInstX ()) "Ps,(0.VhAR,VSTKLO,)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(4.(3.&8.))Pg,$5.P,(6.VhAR,VSTKLO,R5.R4.R3.R2.)P,(7.(8.VSTKLO,R2.)(9.R2.(:.VhAR,VSTKLO,R6.)))(;.(<.(4.(3.&8.))A1.R4.(=.(>.$?.R3.))(10.(3.&8.))))")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] LB LF m g HM G. unfold hstkhi_i in G. cbn [hh] in G.
    dpose (hok_L STKLO h HOK) as (EL & SL16 & SLLO & SHHI & SK4K & _ & _).
    set (g' := g - g mod 8).
    pose proof (Z.div_mod g 8 ltac:(lia)) as DG. pose proof (Z.mod_pos_bound g 8 ltac:(lia)) as MG.
    assert (E : shadow_of AL0 g = shadow_of AL0 g').
    { unfold shadow_of. f_equal. subst g'. replace (g - g mod 8) with (g / 8 * 8) by lia. rewrite Z_div_mult by lia. reflexivity. }
    assert (G8 : g' mod 8 = 0).
    { subst g'. replace (g - g mod 8) with (g / 8 * 8) by lia. apply Z_mod_mult. }
    assert (LO : STKLO <= g').
    { rewrite EL in SL16. pose proof (Z.div_mod STKLO 16 ltac:(lia)) as DS. subst g'. lia. }
    assert (HI : g' + 8 <= l_stk_hi (h_L h)).
    { pose proof (Z.div_mod (l_stk_hi (h_L h)) 4096 ltac:(lia)) as DH. subst g'. lia. }
    dpose (hm_stack_shadow_w_i STKLO (HS STKLO h HOK) LB LF m g' HM LO HI G8) as (W0 & W1 & W).
    specialize (W 0 ltac:(lia)). rewrite Z.add_0_r in W. rewrite E.
    rewrite wview_high in W; [exact W|].
    unfold shadow_of, AL0 in *. cbn [al_sb] in *. rewrite wa_unsigned; [|lia].
    pose proof aceil_min_le as AMIN. unfold ACEIL_MIN in AMIN. rewrite EL in SLLO.
    pose proof (Z.mod_pos_bound STKLO 64 ltac:(lia)) as M64. lia.
  Qed.
End SSMAP.
End ARUN_1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PermLift.
  Variables (A B : Type) (f : A -> B) (p : A -> bool).

  #[using="Type"] Lemma perm_filter_split : forall l : list A, Permutation l (List.filter p l ++ List.filter (fun x => negb (p x)) l).
  Proof.
    induction l as [|a l IH]; cbn; [constructor|].
    destruct (p a); cbn.
    - constructor. exact IH.
    - eapply Permutation_trans; [apply perm_skip; exact IH|]. apply Permutation_middle.
  Qed.

  #[using="Type"] Lemma filter_all : forall l : list A, (forall x, In x l -> p x = true) -> List.filter p l = l.
  Proof.
    induction l as [|a l IH]; cbn; intros H; [reflexivity|].
    rewrite (H a (or_introl eq_refl)). f_equal. apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  #[using="Type"] Lemma filter_none : forall l : list A, (forall x, In x l -> p x = false) -> List.filter p l = [].
  Proof.
    induction l as [|a l IH]; cbn; intros H; [reflexivity|].
    rewrite (H a (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  #[using="Type"] Lemma perm_filter_map_lift : ltac2:(CDefT.buildp (gd_tbl_AHeapInstX ()) "Pl,(1.VA,)PL',(1.VB,)P,(11.VB,(12.VA,VB,Vf,(13.VA,Vp,R2.))R1.)(14.(1.VA,)Ll',(1.VA,)(7.(11.VA,R4.R1.)(<.(1.VB,)(12.VA,VB,Vf,(13.VA,Vp,R1.))R3.)))")
(* [comment removed for export] *).
  Proof.
    intros l L' HP.
    destruct (Permutation_map_inv f _ (Permutation_sym HP)) as (l1' & E & P1).
    exists (l1' ++ List.filter (fun x => negb (p x)) l). split.
    - eapply Permutation_trans; [apply perm_filter_split|]. apply Permutation_app_tail.
      first [exact P1 | exact (Permutation_sym P1)].
    - rewrite filter_app. rewrite (filter_all l1'), (filter_none (List.filter _ l)), app_nil_r; [symmetry; exact E| |].
      + intros x Hx. apply filter_In in Hx. destruct Hx as [_ Hx]. destruct (p x); [discriminate|reflexivity].
      + intros x Hx. assert (Hx' : In x (List.filter p l)) by (first [exact (Permutation_in x P1 Hx) | exact (Permutation_in x (Permutation_sym P1) Hx)]).
        apply filter_In in Hx'. exact (proj2 Hx').
  Qed.
End PermLift.

Section FindPerm.
  Variables (A : Type) (q : A -> bool).
  #[using="Type"] Lemma find_perm : ltac2:(CDefT.buildp (gd_tbl_AHeapInstX ()) "Pl,(1.VA,)Pl',(1.VA,)P,(11.VA,R2.R1.)P,Px,VA,Py,VA,P,(15.VA,R2.R5.)P,(15.VA,R2.R6.)P,(<.$16.A1.Vq,R4.$17.)P,(<.$16.A1.Vq,R4.$17.)(<.VA,R6.R5.)(<.(4.VA,)(18.VA,Vq,R4.)(18.VA,Vq,R3.))")
(* [comment removed for export] *).
  Proof.
    intros l l' HP. induction HP as [| a l l' HP IH | a b l | l1 l2 l3 H12 IH12 H23 IH23]; intros U.
    - reflexivity.
    - cbn. destruct (q a); [reflexivity|]. apply IH. intros x y Hx Hy. apply U; right; assumption.
    - cbn. destruct (q a) eqn:Ea, (q b) eqn:Eb; try reflexivity.
      f_equal. symmetry. apply U; [right; left; reflexivity| left; reflexivity| exact Ea| exact Eb].
    - rewrite IH12 by exact U. apply IH23. intros x y Hx Hy. apply U; eapply Permutation_in; try eassumption; apply Permutation_sym; exact H12.
  Qed.
End FindPerm.

Lemma NoDup_map_inj_in : ltac2:(CDefT.buildp (gd_tbl_AHeapInstX ()) "PA,StPB,StPf,P,R2.R2.Pl,(1.R3.)Px,R4.Py,R5.P,(19.R5.(12.R6.R5.R4.R3.))P,(15.R7.R3.R4.)P,(15.R8.R3.R5.)P,(<.R8.A1.R7.R5.A1.R7.R4.)(<.R:.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [->|Hx], Hy as [->|Hy]; [reflexivity| | |exact (IH x y ND' Hx Hy E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma cnt24_perm : forall L1 L2 : list blk, Permutation L1 L2 -> cnt24 L1 = cnt24 L2.
Proof.
  intros L1 L2 HP. unfold cnt24. f_equal. apply Permutation_length.
  induction HP as [| a l l' HP IH | a b l | l1 l2 l3 H12 IH12 H23 IH23]; cbn.
  - constructor.
  - destruct (win24 (snd a)); [constructor|]; exact IH.
  - destruct (win24 (snd a)), (win24 (snd b)); try apply Permutation_refl. constructor.
  - eapply Permutation_trans; eassumption.
Qed.
Section ARUN_2. Context {hAR : arun}.
Section HMPERM.
  Variable STKLO : Z.

  Definition set_chunks (h : ahst) (l : list chunk) : ahst := ltac2:(CDefT.buildp (gd_tbl_AHeapInstX ()) "(1:.(1;.O2.)(1<.O2.)(1=.O2.)(1>.O2.)O1.(1?.O2.)(20.O2.)(21.O2.)(22.O2.)(23.O2.)(24.O2.)(25.O2.)(26.O2.)(27.O2.))")
(* [comment removed for export] *).

  #[using="Type"] Lemma hdr_unique : ltac2:(CDefT.buildp (gd_tbl_AHeapInstX ()) "Ph,$28.Pk1,$29.Pk2,$29.P,(2:.VhAR,VSTKLO,R3.)P,(15.$29.R3.(2;.R4.))P,(15.$29.R3.(2;.R5.))P,(<.$5.(2<.R5.)(2<.R4.))(<.$29.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros h k1 k2 HOK H1 H2 E. dpose HOK as (EL & AW & VW). dpose AW as (_ & _ & _ & (_ & NDAB & _) & _).
    apply (NoDup_map_inj_in _ _ ck_ab (h_chunks h) k1 k2 NDAB H1 H2).
    destruct (Z.eq_dec (ck_ab k1) (ck_ab k2)) as [EQ|NE]; [exact EQ|exfalso].
    ddestruct (chunk_ext h k1 AW H1) as (_ & A1 & A2 & A3 & A4 & _).
    ddestruct (chunk_ext h k2 AW H2) as (_ & B1 & B2 & B3 & B4 & _).
    apply (ext_apart STKLO h k1 k2 (ck_hdr k1) HOK H1 H2 NE); clear - E A1 A2 A4 B1 B2 B4; lia.
  Qed.

  #[using="Type"] Lemma awf'_perm : forall h l', hok STKLO h -> Permutation (h_chunks h) l' -> awf' (set_chunks h l').
  Proof.
    intros h l' HOK HP. dpose HOK as (EL & AW & VW).
    ddestruct AW as (WL & WC & WR & WK & WQ & WS & WD & WB & WG & WX & WGH).
    unfold awf'.
    split; [exact WL|]. split; [exact WC|].
    assert (CS : forall c, Permutation (chunk_set h c) (chunk_set (set_chunks h l') c)).
    { intros c. unfold chunk_set. cbn [set_chunks h_chunks h_L]. apply Permutation_map.
      clear - HP. induction HP as [| a l1 l2 HP IH | a b l1 | l1 l2 l3 H12 IH12 H23 IH23]; cbn.
      - constructor.
      - destruct (ck_prim a && (ck_cls a =? c)); [constructor|]; exact IH.
      - destruct (ck_prim a && (ck_cls a =? c)), (ck_prim b && (ck_cls b =? c)); try apply Permutation_refl. constructor.
      - eapply Permutation_trans; eassumption. }
    assert (OW : forall c, Permutation (owned h c) (owned (set_chunks h l') c)).
    { intros c. unfold owned. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_tail. exact (CS c). }
    split.
    { intros c Hc. specialize (WR c Hc). cbn zeta in WR |- *.
      ddestruct WR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
      repeat (split; [assumption|]). split.
      - exact (Permutation_NoDup (OW c) R11).
      - intros k. rewrite (R12 k). split; intros HI; [exact (Permutation_in _ (OW c) HI)| exact (Permutation_in _ (Permutation_sym (OW c)) HI)]. }
    split.
    { ddestruct WK as (K1 & K2 & K3). split; [|split].
      - cbn [set_chunks h_chunks]. apply Forall_forall. intros k Hk.
        exact (proj1 (Forall_forall _ _) K1 k (Permutation_in _ (Permutation_sym HP) Hk)).
      - cbn [set_chunks h_chunks]. exact (Permutation_NoDup (Permutation_map ck_ab HP) K2).
      - intros i sh NTH. ddestruct (K3 i sh NTH) as (k & Hk & Q). exists k. split; [exact (Permutation_in _ HP Hk)| exact Q]. }
    assert (FND : forall e, find (fun k => ck_hdr k =? e) l' = find (fun k => ck_hdr k =? e) (h_chunks h)).
    { intros e. symmetry. apply find_perm; [exact HP|]. intros x y Hx Hy Ex Ey. apply Z.eqb_eq in Ex, Ey.
      apply (hdr_unique h x y HOK Hx Hy). congruence. }
    assert (WBT : forall b, wf_batch h b -> wf_batch (set_chunks h l') b).
    { (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). split; [exact B1|]. split; [|split; [|exact B4]].
      - cbn [set_chunks h_chunks]. rewrite B2. f_equal. f_equal. apply map_ext. intros e. rewrite (FND e). reflexivity.
      - cbn [set_chunks h_chunks]. apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k & Hk & Q).
        exists k. split; [exact (Permutation_in _ HP Hk)| exact Q]. }
    assert (WQC : forall q cap, wf_qcache h q cap -> wf_qcache (set_chunks h l') q cap).
    { (intros q cap dd_H; ddestruct dd_H as (Q1 & Q2 & Q3)). split; [|split; [exact Q2| exact Q3]].
      apply Forall_forall. intros b Hb. apply WBT. exact (proj1 (Forall_forall _ _) Q1 b Hb). }
    split.
    { ddestruct WQ as (Q1 & Q2 & Q3 & Q4). split; [exact (WQC _ _ Q1)|]. split; [exact (WQC _ _ Q2)|]. split; [exact Q3|].
      intros k Hk ST. cbn [set_chunks h_chunks] in Hk. exact (Q4 k (Permutation_in _ (Permutation_sym HP) Hk) ST). }
    split; [exact WS|]. split; [exact WD|]. split; [exact WB|]. split; [exact WG|].
    assert (BL : Permutation (AModel.blocks h) (AModel.blocks (set_chunks h l'))).
    { unfold AModel.blocks, live. cbn [set_chunks h_chunks]. apply Permutation_map.
      clear - HP. induction HP as [| a l1 l2 HP IH | a b l1 | l1 l2 l3 H12 IH12 H23 IH23]; cbn.
      - constructor.
      - destruct (ck_st a =? CHUNK_ALLOCATED); [constructor|]; exact IH.
      - destruct (ck_st a =? CHUNK_ALLOCATED), (ck_st b =? CHUNK_ALLOCATED); try apply Permutation_refl. constructor.
      - eapply Permutation_trans; eassumption. }
    split; [|exact WGH].
    ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    repeat (split; [assumption|]).
    rewrite <- (cnt24_perm _ _ BL). exact X9.
  Qed.
  #[using="Type"] Lemma hmperm_i : ltac2:(CDefT.buildp (gd_tbl_AHeapInstX ()) "Ps,(0.VhAR,VSTKLO,)PLB,(1.$2.)PLB',(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(4.(3.&8.))P,(6.VhAR,VSTKLO,R5.R4.R2.R1.)P,(11.$2.R5.R4.)(14.(0.VhAR,VSTKLO,)Ls',(0.VhAR,VSTKLO,)(7.(6.VhAR,VSTKLO,R1.R6.R5.R4.)(7.(<.P,$5.Sp(2=.VhAR,VSTKLO,R1.)(2=.VhAR,VSTKLO,R8.))(7.(<.$5.(2>.VhAR,VSTKLO,R1.)(2>.VhAR,VSTKLO,R8.))(7.(<.$5.(:.VhAR,VSTKLO,R1.)(:.VhAR,VSTKLO,R8.))(7.(<.$5.(2?.VhAR,VSTKLO,R1.)(2?.VhAR,VSTKLO,R8.))(7.(<.$5.(30.VhAR,VSTKLO,R1.)(30.VhAR,VSTKLO,R8.))(7.(<.$5.(31.VhAR,VSTKLO,R1.)(31.VhAR,VSTKLO,R8.))Pmo,$32.(33.(34.VhAR,VSTKLO,R2.R1.)(34.VhAR,VSTKLO,R9.R1.))))))))))")
(* [comment removed for export] *).
  Proof.
    intros [h HOK] LB LB' LF m [HM0 [XR0 HA0]] HP. cbn [hh] in HM0, HA0.
    ddestruct HM0 as ((AW & ELB) & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
    subst LB. unfold AModel.blocks, live in HP.
    destruct (perm_filter_map_lift _ _ (fun k => (ck_user k, ck_n k)) (fun k => ck_st k =? CHUNK_ALLOCATED) (h_chunks h) LB' HP) as (l' & PL & EL').
    assert (HOK' : hok STKLO (set_chunks h l')).
    { ddestruct HOK as (E1 & E2 & E3). split; [exact E1|]. split; [exact (awf'_perm h l' (conj E1 (conj E2 E3)) PL)| exact E3]. }
    exists (HS STKLO (set_chunks h l') HOK').
    split; [| split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
              intros mo; split; intros HK0; exact HK0].
    split; [| split; [exact XR0| cbn [hh]; exact (hm_absent_ext h (set_chunks h l') m eq_refl eq_refl HA0)]]. cbn [hh].
    split; [split; [exact (awf'_perm h l' HOK PL)| symmetry; exact EL']|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [|split; [exact G6|]; split; [exact G7|]; split; [exact G8|]; split; [exact G9|]; split; [exact G10| exact G11]].
    unfold hm_chunks in *. cbn [set_chunks h_chunks]. apply Forall_forall. intros k Hk.
    exact (proj1 (Forall_forall _ _) G5 k (Permutation_in _ (Permutation_sym PL) Hk)).
  Qed.
End HMPERM.
End ARUN_2.
