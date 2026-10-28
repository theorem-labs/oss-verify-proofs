(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes ACanary ARep ARepKit ARepFrame ALayout AHeapP ARepExt
     AMalloc_iface ADepot_iface APoisonR_iface AQConst ARepQ ARepQP ASec ASecFacts ASecFrame ASecStore
     F_adepot AFake_iface AFake_arep AInstance F_apoison_remap F_amalloc_arep AMallocS ADriver_iface AShChunks F_aalloc3g AFreeGeo AFreeRead.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition aci_I : list (Z * Z) := drv_img_ranges ++ cli_img_ranges.

Lemma aci_ok : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) aci_I.
Proof. unfold aci_I, drv_img_ranges, cli_img_ranges, AIMG_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
Lemma aci_ok2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) aci_I.
Proof. unfold aci_I, drv_img_ranges, cli_img_ranges, AINSTANCE. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
Lemma aci_img : forall iv, In iv aci_I -> snd iv <= AIMG_HI.
Proof. intros iv Hin. pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as (_ & _ & H). exact H. Qed.
Lemma aci_ok1 : forall iv, In iv aci_I -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Proof. intros iv Hin. pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as (H1 & _ & H). split; [clear -H1; lia| exact H]. Qed.
Lemma aci_lo : forall iv, In iv aci_I -> 0 <= fst iv.   (* [comment removed for export] *)
Proof. intros iv Hin. pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as (H1 & _). lia. Qed.
Lemma drv_aci : forall iv, In iv drv_img_ranges -> In iv aci_I.
Proof. intros iv H. unfold aci_I. apply in_app_iff. left. exact H. Qed.
Lemma uri_aci : forall iv, In iv cli_img_ranges -> In iv aci_I.
Proof. intros iv H. unfold aci_I. apply in_app_iff. right. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation AHEAP_I := (AHEAP_P AHI).

Section CANSEC2. Context {rc : runConstT}.
Lemma AHI_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP_I L RNG st LB m -> AHEAP_I L RNG' st LB m.
Proof.
  intros L RNG RNG' st LB m LE (ALO & ARNG & XB & HFK). split; [exact ALO|]. split; [eapply arng_mono; [exact LE| exact ARNG]|]. split; [exact XB| exact HFK].
Qed.

Lemma hb_ids_perm : forall LB LB', Permutation LB LB' -> Permutation (hb_ids LB) (hb_ids LB').
Proof.
  intros LB LB' P. unfold hb_ids. induction P; cbn.
  - constructor.
  - apply Permutation_app_head. exact IHP.
  - rewrite !app_assoc. apply Permutation_app_tail. destruct (ab_kind y), (ab_kind x); cbn; try apply Permutation_refl. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma AHI_perm : forall L RNG st LB LB' m, Permutation LB LB' -> AHEAP_I L RNG st LB m -> AHEAP_I L RNG st LB' m.
Proof.
  intros L RNG st LB LB' m P (ALO & ARNG & [X [AR (B1 & B2 & B3 & B4)]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [exact AR|]. split; [| split; [| split]].
    + intros p A n Hin. apply (B1 p A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + intros cls A n Hin. apply (B2 cls A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + eapply Permutation_NoDup; [apply hb_ids_perm; exact P| exact B3].
    + eapply Permutation_NoDup; [exact P| exact B4].
  - cbn [AHI ah_fake] in *. eapply afake_blocks; [exact HFK|]. intros c F n. split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact P| exact P].
Qed.

Lemma AHI_blocks_nodup : forall L RNG st LB m, AHEAP_I L RNG st LB m -> List.NoDup LB.
Proof. intros L RNG st LB m (_ & _ & [X [_ (_ & _ & _ & B4)]] & _). exact B4. Qed.
Lemma AHI_hb_ids : forall L RNG st LB m, AHEAP_I L RNG st LB m -> List.NoDup (hb_ids LB).
Proof. intros L RNG st LB m (_ & _ & [X [_ (_ & _ & B3 & _)]] & _). exact B3. Qed.

Lemma AHI_layout : forall L RNG st LB m, AHEAP_I L RNG st LB m ->
  al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936)
  /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
  /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP.
Proof.
  intros L RNG st LB m (ALO & _ & [X [AR _]] & _).
  pose proof (ao_stack L ALO) as (S1 & S2 & S3 & S4). pose proof (ao_U L ALO) as U. pose proof (ao_fake L ALO) as FK.
  pose proof (aobj_img _ _ FK ltac:(clear; lia)) as FKI.   (* [comment removed for export] *)
  unfold aobj, AIMG_HI in *.
  destruct AR as ((SBE & _) & _).
  repeat lazymatch goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

Lemma AHI_relro : forall L RNG st LB m, AHEAP_I L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros L RNG st LB m H. eapply AHEAP_P_relro. exact H. Qed.

Lemma AHI_rtcells : forall L RNG st LB m, AHEAP_I L RNG st LB m -> artcells m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _).
  destruct AR as (_ & RT & _ & _ & _ & _ & _ & _ & _ & RT2 & _ & RT3).
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  destruct RT2 as (Q1 & Q2 & Q3).
  destruct RT3 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17).
  unfold artcells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_cases : forall L st X LB m p A n,
  alayout_ok L -> AREP AHI L st X m -> ablocks L st X LB -> In (HB p A n) LB ->
  (exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_user L b = A /\ xb_n b = n
      /\ 1 <= xb_class b < K_NUM_CLASSES /\ 1 <= n <= AREQMAX /\ rounded_size n + rz_size n <= size_of_class (xb_class b)
      /\ (a_live st) !! p = Some (CPrim (xb_class b) n) /\ is_primary n = true
      /\ 0 <= xb_slot b < ndist st (xb_class b)
      /\ aregion L (xb_class b) <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= aregion L (xb_class b) + c_allocated_user (get_cls st (xb_class b))
      /\ al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104)
  \/ (exists mb ms, (a_live st) !! p = Some (CSec mb ms n) /\ A = mb + SEC_UOFF /\ sec_wf1 L (CSec mb ms n) /\ is_primary n = false
      /\ In (CSec mb ms n) (sec_chunks_of st)).
Proof.
  intros L st X LB m p A n ALO AR BL Hin.
  pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (proj1 BL p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
  - left. exists b. destruct (BUSY b Hb) as [CLB M]. rewrite Sb in M. destruct M as (N0 & FIT & _ & _ & _ & LV).
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    pose proof (ao_space L ALO) as RSP. subst n.
    repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear -CLB N0 KB; lia).
    all: try (unfold is_primary, needed0, K_MAX_SIZE; apply Z.leb_le; clear -FIT QS; lia).
    all: unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *; clear -P5 P4 Q1 Q2 CLB RSP; lia.
  - right. exists mb, ms. pose proof G as G0. cbn [sec_wf1] in G0. destruct G0 as (_ & _ & _ & _ & _ & G6 & _).
    repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
    apply in_map_iff. exists (p, CSec mb ms n). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp.
Qed.

Lemma AHI_block_bounds : forall L RNG st LB m b,
  AHEAP_I L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
Proof.
  intros L RNG st LB m b AH Hin. destruct b as [[p|cls] A n]; cbn [ab_addr ab_size].
  - pose proof (AHEAP_P_hb_range _ L RNG st LB m p A n AH Hin) as (R1 & R2 & R3 & R4). apply ablk_lin in R1. unfold AIMG_HI in *. clear -R1 R2 R3. lia.   (* [comment removed for export] *)
  - destruct AH as (ALO & _ & [X [_ (_ & BF & _)]] & _). destruct (BF cls A n Hin) as (K1 & K2 & K3).
    pose proof (ao_fake L ALO) as FK. pose proof (aobj_img _ _ FK ltac:(clear; lia)) as FKI.   (* [comment removed for export] *)
    unfold aobj, AIMG_HI in *. clear -K1 K2 K3 FK FKI. lia.
Qed.

(* [comment removed for export] *)
Lemma nodup_map_inj : forall {A B} (f : A -> B) (l : list A) x y,
  List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | |].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

Lemma nodup_filter_map_inj : forall {A B} (g : B -> bool) (f : A -> B) (l : list A) x y,
  List.NoDup (List.filter g (map f l)) -> In x l -> In y l -> f x = f y -> g (f x) = true -> x = y.
Proof.
  intros A B g f l. induction l as [|a l IH]; intros x y ND Hx Hy E G; [destruct Hx|].
  cbn in ND.
  destruct Hx as [Hx|Hx], Hy as [Hy|Hy].
  - subst. reflexivity.
  - subst a. exfalso. rewrite G in ND. inversion ND as [|a' l' NI ND']; subst. apply NI. apply List.filter_In. split; [rewrite E; apply in_map; exact Hy| exact G].
  - subst a. exfalso. rewrite <- E, G in ND. inversion ND as [|a' l' NI ND']; subst. apply NI. apply List.filter_In. split; [apply in_map; exact Hx| exact G].
  - apply IH; try assumption. destruct (g (f a)); [inversion ND; assumption| exact ND].
Qed.

Lemma AHI_blocks_disjoint : forall L RNG st LB m b1 b2,
  AHEAP_I L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
  ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1.
Proof.
  intros L RNG st LB m b1 b2 AH H1 H2 NE.
  pose proof AH as (ALO & _ & [X [AR BL]] & HFK). cbn [AHI ah_fake] in HFK.
  pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ad_fake_res L ALO) as D_f_res. unfold aobj, adisj in ORS, OFK, D_f_res.
  destruct b1 as [[p1|c1] A1 n1]; destruct b2 as [[p2|c2] A2 n2]; cbn [ab_addr ab_size].
  - (* [comment removed for export] *)
    assert (NEP : p1 <> p2).
    { intros <-. pose proof BL as (_ & _ & NDI & _).
      assert (E : HB p1 A1 n1 = HB p1 A2 n2).
      { apply (nodup_filter_map_inj (fun k => match k with ABHeap _ => true | _ => false end) ab_kind LB); try assumption; try reflexivity.
        unfold hb_ids in NDI. clear -NDI. induction LB as [|b LB IH]; cbn; [constructor|]. cbn in NDI.
        destruct b as [[q|c] B k]; cbn in NDI |- *; [| apply IH; exact NDI]. inversion NDI as [|q' l' NI ND']; subst. constructor; [| apply IH; exact ND'].
        intros Hin. apply NI. apply List.filter_In in Hin. destruct Hin as [Hin _]. apply in_map_iff in Hin. destruct Hin as (b' & Eb & Hb').
        apply in_flat_map. exists b'. split; [exact Hb'|]. destruct b' as [[q''|c''] B' k']; cbn in Eb |- *; [| discriminate]. injection Eb as ->. left; reflexivity. }
      exact (NE E). }
    destruct (hb_cases L st X LB m p1 A1 n1 ALO AR BL H1) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & _ & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & _ & INC)];
    destruct (hb_cases L st X LB m p2 A2 n2 ALO AR BL H2) as [(b' & Hb' & Sb' & Ub' & Nb' & CLB' & NB' & FIT' & LV' & _ & KB' & P5' & P4' & R1' & R2')|(mb' & ms' & Lp' & EA' & G' & _ & INC')].
    + (* [comment removed for export] *)
      destruct AR as (WF & _). pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
      assert (NEB : b <> b') by (intros <-; apply NEP; rewrite Sb in Sb'; injection Sb' as E; exact E).
      pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
      pose proof (rounded_size_ge (xb_n b')) as RG'. pose proof (rz_size_ge16 (xb_n b')) as RZ'.
      pose proof (size_of_class_facts (xb_class b) CLB) as [QS _]. pose proof (size_of_class_facts (xb_class b') CLB') as [QS' _].
      assert (SL : xb_alloc L b + size_of_class (xb_class b) <= xb_alloc L b' \/ xb_alloc L b' + size_of_class (xb_class b') <= xb_alloc L b).
      { destruct (Z.eq_dec (xb_class b) (xb_class b')) as [EC|NC].
        - (* [comment removed for export] *)
          destruct (PERC (xb_class b) CLB) as (Q1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
          assert (NK : xb_slot b <> xb_slot b').
          { intros EK. apply NEB. apply (nodup_map_inj xb_slot (List.filter (fun x => xb_class x =? xb_class b) (x_busy X))).
            - apply List.NoDup_app_remove_l in ND. apply List.NoDup_app_remove_l in ND. exact ND.
            - apply List.filter_In. split; [exact Hb| apply Z.eqb_refl].
            - apply List.filter_In. split; [exact Hb'| rewrite EC; apply Z.eqb_refl].
            - exact EK. }
          unfold xb_alloc. rewrite <- EC. apply slots_disjoint; [clear -KB; lia| clear -KB'; lia| exact NK| clear -QS; lia].
        - (* [comment removed for export] *)
          destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _). destruct (PERC (xb_class b') CLB') as (Q1' & Q2' & _).
          unfold K_FREEARR_OFF in Q2, Q2'.
          destruct (Z.lt_ge_cases (xb_class b) (xb_class b')) as [LT|GE].
          + left. pose proof (regions_sep L (xb_class b) (xb_class b') LT) as RS. unfold K_REGION in RS. clear -RS P4 P5' Q1 Q2. lia.
          + right. pose proof (regions_sep L (xb_class b') (xb_class b) ltac:(clear -GE NC; lia)) as RS. unfold K_REGION in RS. clear -RS P4' P5 Q1' Q2'. lia. }
      subst A1 n1 A2 n2. unfold xb_user. clear -SL FIT FIT' RG RZ RG' RZ' NB NB'. lia.
    + cbn [sec_wf1] in G'. destruct G' as (G1 & G2 & G3 & G4 & G5 & G6 & (_ & _ & Cr & _)).
      pose proof (sec_facts n2 ltac:(clear -G5; lia) G6) as SF. subst A2. unfold SEC_UOFF, xb_user in *. subst A1 n1.
      pose proof (rounded_size_ge (xb_n b)) as RG. pose proof (rz_size_ge16 (xb_n b)) as RZ.
      clear -R1 R2 FIT RG RZ Cr G3 G4 G5 SF NB. lia.
    + cbn [sec_wf1] in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & (_ & _ & Cr & _)).
      pose proof (sec_facts n1 ltac:(clear -G5; lia) G6) as SF. subst A1. unfold SEC_UOFF, xb_user in *. subst A2 n2.
      pose proof (rounded_size_ge (xb_n b')) as RG. pose proof (rz_size_ge16 (xb_n b')) as RZ.
      clear -R1' R2' FIT' RG RZ Cr G3 G4 G5 SF NB'. lia.
    + (* [comment removed for export] *)
      destruct AR as (WF & _ & _ & _ & _ & _ & HS & _). cbn [AHI ah_sec] in HS. unfold ASEC_of in HS.
      destruct HS as ((_ & _ & _ & _ & _ & _ & [ND PW]) & _).
      cbn [sec_wf1] in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & _). cbn [sec_wf1] in G'. destruct G' as (G1' & G2' & G3' & G4' & G5' & G6' & _).
      pose proof (sec_facts n1 ltac:(clear -G5; lia) G6) as SF. pose proof (sec_facts n2 ltac:(clear -G5'; lia) G6') as SF'.
      assert (NEC : CSec mb ms n1 <> CSec mb' ms' n2).
      { intros EC. apply NEP.
        assert (E : (p1, CSec mb ms n1) = (p2, CSec mb' ms' n2)); [| injection E as E1 _ _ _; exact E1].
        apply (nodup_filter_map_inj is_sec snd (map_to_list (a_live st))).
        - unfold sec_chunks_of, achunks in ND. rewrite filter_is_sec_app in ND. apply List.NoDup_app_remove_r in ND. exact ND.
        - apply list_elem_of_In. apply elem_of_map_to_list. exact Lp.
        - apply list_elem_of_In. apply elem_of_map_to_list. exact Lp'.
        - cbn. exact EC.
        - reflexivity. }
      pose proof (PW _ _ INC INC' NEC) as D. cbn [sec_mb sec_ms] in D. subst A1 A2. unfold SEC_UOFF. clear -D G4 G4' G5 G5' SF SF'. lia.
  - (* [comment removed for export] *)
    pose proof (AHEAP_P_hb_fake _ L RNG st LB m p1 A1 n1 AH H1) as D1.
    destruct (afake_lb L LB m c2 A2 n2 HFK H2) as (_ & _ & K3 & _ & K5 & K6 & _). unfold FAKESZ in K6. clear -D1 K3 K5 K6. lia.
  - pose proof (AHEAP_P_hb_fake _ L RNG st LB m p2 A2 n2 AH H2) as D2.
    destruct (afake_lb L LB m c1 A1 n1 HFK H1) as (_ & _ & K3 & _ & K5 & K6 & _). unfold FAKESZ in K6. clear -D2 K3 K5 K6. lia.
  - (* [comment removed for export] *) eapply afake_lb_disjoint; [exact HFK| exact H1| exact H2| exact NE].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wr_at_join : forall m A a b, wr_at bsegs m A a -> wr_at bsegs m (A + a) b -> 0 <= a -> 0 <= b -> wr_at bsegs m A (a + b).
Proof.
  intros m A a b (W0 & W1 & W) (V0 & V1 & V) Ha Hb. split; [exact W0|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i a) as [L|G]; [apply W; lia|]. replace (A + i) with (A + a + (i - a)) by lia. apply V. lia.
Qed.
Lemma wr_at_nil : forall m A, 0 <= A <= 2^64 -> wr_at bsegs m A 0.
Proof. intros m A H. split; [lia|]. split; [lia|]. intros i Hi. lia. Qed.
Lemma wr_of_cells : forall m A cs, rw_cells bsegs m A cs -> wr_at bsegs m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [_ W]. exact W. Qed.
Lemma wr_of_junk : forall m A n, 0 <= n -> junk_at m A n -> wr_at bsegs m A n.
Proof. intros m A n Hn [bs H]. pose proof (wr_of_cells _ _ _ H) as W. cbn [cells_size csize] in W. rewrite Nat.add_0_r, Z2Nat.id in W by exact Hn. exact W. Qed.
Lemma wr_of_fill : forall m A n v, 0 <= n -> fill_at m A n v -> wr_at bsegs m A n.
Proof. intros m A n v Hn H. apply (wr_of_junk m A n Hn). eapply fill_is_junk. exact H. Qed.
Lemma wr_of_azero : forall m A n, azero m A n -> wr_at bsegs m A n.
Proof. intros m A n [_ W]. exact W. Qed.

Lemma region_shadow_wr : forall L st X m c,
  AREP AHI L st X m -> 1 <= c < K_NUM_CLASSES -> wr_at bsegs m (shad (aregion L c)) (shlen K_REGION).
Proof.
  intros L st X m c AR Hc.
  pose proof AR as ((SBE & PAE & SAL & SLO & SHI & PERC & _) & _ & _ & _ & CLS & _ & _ & _ & _ & _ & AVL & _).
  destruct (CLS c Hc) as (_ & (_ & _ & FAS) & _ & [SSH SFILL]). destruct (AVL c Hc) as [AZ1 AZ2].
  destruct (PERC c Hc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
  pose proof (size_of_class_facts c Hc) as [QS QS16].
  set (r := get_cls st c) in *. set (S := size_of_class c) in *.
  pose proof (aregion_mod L c SAL) as RM.
  assert (AL8 : c_allocated_user r mod 8 = 0) by (apply (mod16_of_class _ S); [exact A3| exact QS16| clear -QS; lia]).
  (* [comment removed for export] *)
  assert (SL : forall k : nat, Z.of_nat k <= ndist st c -> wr_at bsegs m (shad (aregion L c)) (shlen (Z.of_nat k * S))).
  { induction k as [|k IH]; intros Hk.
    - cbn [Z.of_nat]. rewrite Z.mul_0_l. unfold shlen; cbn. apply wr_at_nil. rewrite shad_div. unfold ASHOFF. pose proof (alayout_space L) as _.
      unfold aregion, K_REGION. unfold K_NUM_CLASSES in Hc. clear -SLO SHI Hc. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. Z.div_mod_to_equations. nia.
    - replace (shlen (Z.of_nat (Datatypes.S k) * S)) with (shlen (Z.of_nat k * S) + shlen S)
        by (rewrite !shlen_div; clear -QS16 QS; Z.div_mod_to_equations; nia).
      apply wr_at_join; [apply IH; lia| | rewrite shlen_div; clear -QS; Z.div_mod_to_equations; nia| rewrite shlen_div; clear -QS; Z.div_mod_to_equations; lia].
      pose proof (SSH (Z.of_nat k) ltac:(lia)) as CK. apply wr_of_cells in CK. cbn [cells_size csize] in CK. rewrite Nat.add_0_r, Z2Nat.id in CK by (rewrite shlen_div; clear -QS; Z.div_mod_to_equations; lia).
      replace (shad (aregion L c) + shlen (Z.of_nat k * S)) with (shad (aslot_addr L c (Z.of_nat k))); [exact CK|].
      unfold aslot_addr. fold S. rewrite shad_add_shlen; [reflexivity|]. clear -RM. Z.div_mod_to_equations. lia. }
  assert (ND : Z.of_nat (Z.to_nat (ndist st c)) = ndist st c /\ ndist st c * S = c_allocated_user r).
  { unfold ndist. fold r S. split; [| clear -A1 A3 QS; Z.div_mod_to_equations; nia]. apply Z2Nat.id. apply Z.div_pos; clear -A1 QS; lia. }
  destruct ND as [ND1 ND2].
  pose proof (SL (Z.to_nat (ndist st c)) ltac:(rewrite ND1; lia)) as W1. rewrite ND1, ND2 in W1. clear SL.
  (* [comment removed for export] *)
  pose proof SFILL as W2. apply wr_of_fill in W2; [| apply shlen_nonneg; clear -A1; lia].
  pose proof (wr_of_azero _ _ _ AZ1) as W3. pose proof FAS as W4. apply wr_of_junk in W4; [| apply shlen_nonneg; clear -A5 A6; lia]. pose proof (wr_of_azero _ _ _ AZ2) as W5.
  fold r in W2, W3, W4, W5.
  assert (E2 : shad (aregion L c + c_allocated_user r) = shad (aregion L c) + shlen (c_allocated_user r)) by (apply shad_add_shlen; clear -RM; Z.div_mod_to_equations; lia).
  assert (E3 : shad (aregion L c + c_mapped_user r) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r))).
  { rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. clear -AL8 A4. unfold K_USER_MAP in A4. Z.div_mod_to_equations. lia. }
  assert (E4 : shad (afreearr L c) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r))).
  { unfold afreearr. rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. unfold K_FREEARR_OFF, K_USER_MAP in *. clear -AL8 A4. Z.div_mod_to_equations. lia. }
  assert (E5 : shad (afreearr L c + c_mapped_free_array r) = shad (aregion L c) + (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r) + shlen (c_mapped_free_array r))).
  { unfold afreearr. rewrite <- Z.add_assoc. rewrite shad_add_shlen by (clear -RM; Z.div_mod_to_equations; lia). rewrite !shlen_div. unfold K_FREEARR_OFF, K_USER_MAP, K_FREEARR_MAP in *. clear -AL8 A4 A7. Z.div_mod_to_equations. lia. }
  replace (shlen K_REGION) with (shlen (c_allocated_user r) + shlen (c_mapped_user r - c_allocated_user r) + shlen (K_FREEARR_OFF - c_mapped_user r) + shlen (c_mapped_free_array r) + shlen (K_FREEARR_MAX - c_mapped_free_array r))
    by (rewrite !shlen_div; unfold K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP in *; clear -AL8 A4 A7; Z.div_mod_to_equations; lia).
  apply wr_at_join; [| rewrite <- E5; exact W5| rewrite !shlen_div; unfold K_FREEARR_OFF in *; clear -A1 A2 A5 A6; Z.div_mod_to_equations; lia| apply shlen_nonneg; clear -A6; unfold K_FREEARR_MAX in *; lia].
  apply wr_at_join; [| rewrite <- E4; exact W4| rewrite !shlen_div; unfold K_FREEARR_OFF in *; clear -A1 A2; Z.div_mod_to_equations; lia| apply shlen_nonneg; clear -A5 A6; lia].
  apply wr_at_join; [| rewrite <- E3; exact W3| rewrite !shlen_div; clear -A1; Z.div_mod_to_equations; lia| apply shlen_nonneg; unfold K_FREEARR_OFF in *; clear -A2; lia].
  apply wr_at_join; [exact W1| rewrite <- E2; exact W2| apply shlen_nonneg; clear -A1; lia| apply shlen_nonneg; clear -A1; lia].
Qed.

(* [comment removed for export] *)
Lemma busy_of_of_In : forall L st X b, awf L st X -> In b (x_busy X) -> busy_of X (xb_class b) (xb_slot b) = Some b.
Proof.
  intros L st X b WF Hb. pose proof WF as (_ & _ & _ & _ & _ & PERC & _ & BUSY & _).
  destruct (BUSY b Hb) as [CLB _]. destruct (PERC (xb_class b) CLB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
  apply List.NoDup_app_remove_l in ND. apply List.NoDup_app_remove_l in ND. unfold busy_slots in ND.
  unfold busy_of. destruct (List.find (fun b0 => (xb_class b0 =? xb_class b) && (xb_slot b0 =? xb_slot b)) (x_busy X)) as [b'|] eqn:E.
  - apply find_some in E. destruct E as [HIn HP]. apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
    f_equal. apply (nodup_map_inj xb_slot (List.filter (fun x => xb_class x =? xb_class b) (x_busy X)) b' b ND).
    + apply List.filter_In. split; [exact HIn| rewrite HP1; apply Z.eqb_refl].
    + apply List.filter_In. split; [exact Hb| apply Z.eqb_refl].
    + exact HP2.
  - exfalso. pose proof (find_none _ _ E b Hb) as F. cbn beta in F. rewrite !Z.eqb_refl in F. discriminate.
Qed.

(* [comment removed for export] *)
Lemma block_shadow_of_cb : forall m A n,
  0 < n -> A mod 8 = 0 -> 0 <= A -> A + n <= 2^47 ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  ablock_shadow m A n.
Proof.
  intros m A n Hn AL A0 AH H.
  assert (LB : length (block_shadow_bytes n) = Z.to_nat (granules n)) by (apply length_block_shadow_bytes; lia).
  assert (GE : granules n = n / 8 + (if n mod 8 =? 0 then 0 else 1)).
  { rewrite (ASec.granules_eq n) by lia. rewrite shlen_div. reflexivity. }
  unfold block_shadow_bytes in H. rewrite shlen_div in H.
  destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
  - rewrite app_nil_r in H. rewrite GE, Z.add_0_r in H. eapply chunks_ablock_shadow; [exact Hn| exact AL| exact A0| exact AH| exact H|].
    intros NE. exfalso. exact (NE M0).
  - rewrite GE in H. replace (Z.to_nat (n / 8 + 1)) with (Z.to_nat (n / 8) + 1)%nat in H by (Z.div_mod_to_equations; lia).
    destruct (cb_take m (shad A) (n / 8 + 1) (n / 8) _ ltac:(rewrite Z2Nat.inj_add by (Z.div_mod_to_equations; lia); cbn [Z.to_nat Pos.to_nat]; exact H) ltac:(Z.div_mod_to_equations; lia)) as [H1 H2].
    rewrite firstn_app, repeat_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in H1 by (rewrite repeat_length; lia).
    rewrite skipn_app, repeat_length, Nat.sub_diag, skipn_O, skipn_all2 in H2 by (rewrite repeat_length; lia). cbn [app] in H2.
    replace (n / 8 + 1 - n / 8) with 1 in H2 by lia.
    eapply chunks_ablock_shadow; [exact Hn| exact AL| exact A0| exact AH| exact H1|].
    intros _. eapply rw_cells_recast; [exact H2| cbn; tauto| reflexivity| reflexivity].
Qed.

Theorem AHI_block : forall L RNG st LB m p A n,
  AHEAP_I L RNG st LB m -> In (HB p A n) LB ->
  1 <= n <= AREQMAX /\
  ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7)) /\ ablock_shadow m A n
  /\ wr_at bsegs m A n
  /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
  /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO)).
Proof.
  intros L RNG st LB m p A n AH Hin.
  pose proof (AHEAP_P_hb_range _ L RNG st LB m p A n AH Hin) as BR.
  pose proof AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  pose proof AR as (WF & _ & _ & _ & CLS & _ & HS & _). pose proof WF as (SBE & PAE & SAL & SLO & SHI & PERC & _).
  cbn [AHI ah_sec] in HS. unfold ASEC_of in HS. pose proof HS as ((_ & _ & _ & _ & _ & WF1 & _) & (order & PO & _ & _ & PER) & _ & PZ & _).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - (* [comment removed for export] *)
    set (c := xb_class b) in *. set (k := xb_slot b) in *. set (S := size_of_class c) in *.
    pose proof (size_of_class_facts c CLB) as [QS QS16].
    destruct (PERC c CLB) as (A1 & A2 & A3 & A4 & _). destruct (RCLS c CLB) as (RREG & RSREG & _). cbv zeta in RREG, RSREG.
    pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ16. pose proof (rz_size_facts n ltac:(clear -NB; lia)) as [_ RZM].
    pose proof (aregion_mod L c SAL) as RM. pose proof (slot_aligned L c k SAL ltac:(exact CLB)) as AL16.
    assert (EAB : xb_alloc L b = aslot_addr L c k) by reflexivity.
    subst A. unfold xb_user in *. rewrite EAB in *. rewrite Nb in *.
    assert (A8 : (aslot_addr L c k + rz_size n) mod 8 = 0) by (clear -AL16 RZM; Z.div_mod_to_equations; lia).
    unfold K_FREEARR_OFF, K_NUM_CLASSES in *.
    split; [exact NB|]. split; [exact BR|].
    split. { eapply rng_sub'; [exact RREG|]. clear -P5 P4 A1 FIT RG RZ16. lia. }
    split. { eapply rng_sub'; [exact RSREG|]. rewrite !shad_div, !shlen_div. unfold K_USER_MAP in A4. clear -P5 P4 A1 FIT RG RZ16 RM A4 A8. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    destruct (CLS c CLB) as (_ & _ & [SL _] & [SSH _]).
    pose proof (SSH k KB) as SH. rewrite (busy_of_of_In L st X b WF Hb : busy_of X c k = Some b) in SH. cbn [slot_shadow_bytes] in SH. rewrite Sb, Nb in SH. fold S in SH.
    pose proof (chunk_shadow_geo L st X c k n ALO WF CLB KB ltac:(clear -NB; lia) FIT) as (SE & G2 & GEq & G0 & GF & _).
    pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
    assert (LBS : length (block_shadow_bytes n) = Z.to_nat (granules n)) by (apply length_block_shadow_bytes; lia).
    replace (Z.to_nat (shlen S)) with (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen (rz_size n) - granules n))%nat in SH
      by (generalize SRZ SG7 GF; subst S; clear; unfold granules; intros; lia).
    destruct (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) LBS ltac:(apply repeat_length) SH) as (_ & SHU & _).
    rewrite Z2Nat.id in SHU by lia. rewrite <- SE in SHU.
    split. { eapply block_shadow_of_cb; [clear -NB; lia| exact A8| destruct BR as (B1 & _); apply ablk_lin in B1; clear -B1; lia| destruct BR as (_ & _ & B3 & _); clear -B3; lia| exact SHU]. }
    (* [comment removed for export] *)
    pose proof (SL k KB) as SLK. rewrite (busy_of_of_In L st X b WF Hb : busy_of X c k = Some b) in SLK. unfold aslot_busy in SLK. cbv zeta in SLK. rewrite Sb in SLK.
    destruct SLK as (_ & _ & UJ). rewrite EAB, Nb in UJ. fold S in UJ.
    split. { eapply wr_at_sub'; [apply (wr_of_junk m _ (S - rz_size n)); [clear -FIT RG NB; lia| exact UJ]| destruct BR as (B1 & _); apply ablk_lin in B1; clear -B1; lia| clear; lia| clear -FIT RG NB; lia]. }
    split. { exists (CPrim c n). split; [exact LV|]. split; [reflexivity|]. intros P. rewrite PRIM in P. discriminate. }
    (* [comment removed for export] *)
    exists (aregion L (c - 1)), (aregion L (c + 1)).
    assert (GEO : aregion L (c - 1) + K_REGION = aregion L c /\ aregion L c + K_REGION = aregion L (c + 1) /\ aregion L 0 = al_space_beg L
                  /\ aregion L (c - 1) mod 4096 = 0 /\ 0 <= aregion L (c - 1)).
    { unfold aregion, K_REGION. unfold K_ALIGN in SAL. clear -SAL SP1 CLB. repeat split; first [nia | Z.div_mod_to_equations; nia]. }
    destruct GEO as (GE1 & GE2 & GE0 & GAL & GNN). unfold K_REGION in GE1, GE2.
    split; [exact GAL|]. split; [rewrite <- GE2, <- GE1; clear -GAL; Z.div_mod_to_equations; lia|].
    split; [clear -GE1 P5 RZ16; lia|]. split; [clear -GE2 P4 A1 A2 FIT RG; lia|].
    rewrite <- GE2, <- GE1. replace (aregion L (c - 1) + 2^32 + 2^32 - aregion L (c - 1)) with (4294967296 + 4294967296) by (clear; lia).
    split.
    + eapply rng_sub'; [exact RPSH|]. rewrite !shad_div, !shlen_div. unfold K_SPACE_SIZE. unfold aregion, K_REGION in *.
      clear -CLB SP3. unfold K_ALIGN in SP3. Z.div_mod_to_equations. nia.
    + replace (shlen (4294967296 + 4294967296)) with (shlen K_REGION + shlen K_REGION) by reflexivity.
      apply wr_at_join; [| | apply shlen_nonneg; unfold K_REGION; clear; lia| apply shlen_nonneg; unfold K_REGION; clear; lia].
      * destruct (Z.eq_dec c 1) as [C1|C1].
        { rewrite C1. change (1 - 1) with 0. rewrite GE0. exact (wr_of_azero _ _ _ PZ). }
        eapply region_shadow_wr; [exact AR| unfold K_NUM_CLASSES; clear -CLB C1; lia].
      * rewrite <- shad_add_shlen by (rewrite <- GAL; clear -GAL; Z.div_mod_to_equations; lia). unfold K_REGION. rewrite GE1.
        eapply region_shadow_wr; [exact AR| unfold K_NUM_CLASSES; exact CLB].
  - (* [comment removed for export] *)
    pose proof G as G0. cbn [sec_wf1] in G0. destruct G0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
    apply ablk_lin in G2.   (* [comment removed for export] *)
    pose proof (sec_facts n ltac:(clear -G5; lia) G6) as (NBg & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB). rewrite <- G4 in MSE, MSR, MSM, MSB.
    pose proof (proj1 (Forall_forall _ _) RSECS _ INC) as [RC RSC]. cbn [sec_mb sec_ms] in RC, RSC.
    (* [comment removed for export] *)
    pose proof (Permutation_in _ (Permutation_sym PO) INC) as INO. apply In_nth_error in INO. destruct INO as [i Hi].
    destruct (PER i _ Hi) as (lv & LVE & CH).
    assert (LVT : lv = true) by (apply (proj2 LVE); exists p; exact Lp). subst lv.
    cbn [asec_chunk] in CH. destruct CH as (_ & _ & _ & _ & _ & UJ & SF1 & SU & SF2). unfold SEC_UOFF, K_HIGH_MEM in *. subst A.
    assert (SG : shad (mb + 6144) = shad mb + 768 /\ shad mb + ms / 8 = shad (mb + ms) /\ 768 + granules n <= ms / 8 /\ 0 <= granules n /\ shlen ms = ms / 8
                 /\ (mb + 6144) mod 8 = 0 /\ 0 <= shad mb).
    { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -G1 G2 NBg RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
    destruct SG as (SG1 & SG2 & SG3 & SG4 & SG5 & SG6 & SG7).
    split; [clear -G5; lia|]. split; [exact BR|].
    split; [eapply rng_sub'; [exact RC|]; clear -NSE RSR MSR NBg; lia|].
    split; [eapply rng_sub'; [exact RSC|]; rewrite !shad_div, !shlen_div; rewrite shad_div in SG2; unfold ASHOFF in *; clear -G1 NSE RSR MSR NBg; Z.div_mod_to_equations; lia|].
    split. { eapply block_shadow_of_cb; [clear -NBg; lia| exact SG6| clear -G2; lia| clear -G3 NSE RSR MSR NBg; lia| unfold sec_user_shadow in SU; exact SU]. }
    split. { eapply wr_at_sub'; [apply (wr_of_junk m _ (ms - 6144)); [clear -MSR NSE RSR NBg; lia| exact UJ]| clear -G2; lia| clear; lia| clear -MSR NSE RSR NBg; lia]. }
    split. { exists (CSec mb ms n). split; [exact Lp|]. split; [reflexivity|]. intros _. cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
    exists mb, (mb + ms). split; [exact G1|]. split; [clear -G1 MSM; Z.div_mod_to_equations; lia|]. split; [clear; lia|]. split; [clear -MSR NSE RSR NBg; lia|].
    replace (mb + ms - mb) with ms by (clear; lia). rewrite SG5.
    split; [exact RSC|].
    pose proof SF1 as W1. apply wr_of_fill in W1; [| clear; lia].
    pose proof SF2 as W3. apply wr_of_fill in W3; [| clear -SG3 SG4; lia].
    pose proof (wr_of_cells _ _ _ SU) as W2. cbn [cells_size csize] in W2. rewrite Nat.add_0_r, Z2Nat.id in W2 by exact SG4.
    replace (ms / 8) with (768 + (granules n + (ms / 8 - 768 - granules n))) by (clear -SG3; lia).
    apply wr_at_join; [exact W1| | clear; lia| clear -SG3 SG4; lia].
    rewrite <- SG1. apply wr_at_join; [exact W2| exact W3| exact SG4| clear -SG3 SG4; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition achunk_kind_ok (ch : achunk) (n : Z) : Prop :=
  match ch with CPrim _ _ => is_primary n = true | CSec _ _ _ => is_primary n = false end.

Lemma AHI_chunk : forall L RNG st LB m p A n, AHEAP_I L RNG st LB m -> In (HB p A n) LB ->
  exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
Proof.
  intros L RNG st LB m p A n AH Hin. pose proof AH as (ALO & _ & [X [AR BL]] & _).
  destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(b & _ & _ & _ & _ & _ & _ & _ & LV & PRIM & _)|(mb & ms & Lp & EA & G & PRIM & _)].
  - exists (CPrim (xb_class b) n). split; [exact LV|]. split; [reflexivity|]. split; [intros P; rewrite PRIM in P; discriminate| exact PRIM].
  - exists (CSec mb ms n). split; [exact Lp|]. split; [reflexivity|]. split; [| exact PRIM].
    intros _. cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & G5 & G6 & _). pose proof (sec_facts n ltac:(clear -G5; lia) G6) as (_ & RZ & _).
    subst A. cbn [chunk_user_beg]. unfold SEC_UOFF, PG. rewrite RZ. clear; lia.
Qed.

Lemma AHI_premap : forall L RNG st LB m, AHEAP_I L RNG st LB m -> premap_cells m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _). destruct AR as (_ & RT & _ & _ & _ & _ & _ & _ & _ & RT2 & _ & RT3).
  eapply premap_of_rt'; [exact RT| exact RT2| exact RT3].
Qed.
End CANSEC2.
