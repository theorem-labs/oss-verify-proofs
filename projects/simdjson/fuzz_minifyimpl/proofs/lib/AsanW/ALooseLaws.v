(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg AProto ABase ABytes ACanary ARep ARepKit ARepFrame ALayout AHeapP ARepExt AMalloc_iface ADepot_iface APoisonR_iface AQConst ARepQ ARepQP ASec ASecFacts ASecFrame ASecStore F_adepot AFake_iface AFake_arep AInstance F_apoison_remap F_amalloc_arep AMallocS ADriver_iface AU_iface AU_parts_iface AAnnot_iface F_aalloc3g AFreeGeo AFreeRead ALoose AInstanceM AInstanceF ALooseInst ALooseSet.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Set Keyed Unification.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma AHL_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP_L L RNG st LB m -> AHEAP_L L RNG' st LB m.
Proof.
  intros L RNG RNG' st LB m LE (ALO & ARNG & XB & HFK). split; [exact ALO|]. split; [eapply arng_mono; [exact LE| exact ARNG]|]. split; [exact XB| exact HFK].
Qed.


Lemma AHL_perm : forall L RNG st LB LB' m, Permutation LB LB' -> AHEAP_L L RNG st LB m -> AHEAP_L L RNG st LB' m.
Proof.
  intros L RNG st LB LB' m P (ALO & ARNG & [X [AR (B1 & B2 & B3 & B4)]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [exact AR|]. split; [| split; [| split]].
    + intros p A n Hin. apply (B1 p A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + intros cls A n Hin. apply (B2 cls A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + eapply Permutation_NoDup; [apply hb_ids_perm; exact P| exact B3].
    + eapply Permutation_NoDup; [exact P| exact B4].
  - cbn [AHL ah_fake] in *. eapply afake_blocks; [exact HFK|]. intros c F n. split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact P| exact P].
Qed.

Lemma AHL_blocks_nodup : forall L RNG st LB m, AHEAP_L L RNG st LB m -> List.NoDup LB.
Proof. intros L RNG st LB m (_ & _ & [X [_ (_ & _ & _ & B4)]] & _). exact B4. Qed.
Lemma AHL_hb_ids : forall L RNG st LB m, AHEAP_L L RNG st LB m -> List.NoDup (hb_ids LB).
Proof. intros L RNG st LB m (_ & _ & [X [_ (_ & _ & B3 & _)]] & _). exact B3. Qed.

Lemma AHL_layout : forall L RNG st LB m, AHEAP_L L RNG st LB m ->
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

Lemma AHL_relro : forall L RNG st LB m, AHEAP_L L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.
Proof. intros L RNG st LB m H. eapply AHEAP_P_relro. exact H. Qed.

Lemma AHL_rtcells : forall L RNG st LB m, AHEAP_L L RNG st LB m -> artcells m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _).
  destruct AR as (_ & RT & _ & _ & _ & _ & _ & _ & _ & RT2 & _ & RT3).
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28 & _).
  destruct RT2 as (Q1 & Q2 & Q3).
  destruct RT3 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17).
  unfold artcells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.


Lemma AHL_block_bounds : forall L RNG st LB m b,
  AHEAP_L L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP.
Proof.
  intros L RNG st LB m b AH Hin. destruct b as [[p|cls] A n]; cbn [ab_addr ab_size].
  - pose proof (AHEAP_P_hb_range _ L RNG st LB m p A n AH Hin) as (R1 & R2 & R3 & R4). apply ablk_lin in R1. unfold AIMG_HI in *. clear -R1 R2 R3. lia.   (* [comment removed for export] *)
  - destruct AH as (ALO & _ & [X [_ (_ & BF & _)]] & _). destruct (BF cls A n Hin) as (K1 & K2 & K3).
    pose proof (ao_fake L ALO) as FK. pose proof (aobj_img _ _ FK ltac:(clear; lia)) as FKI.   (* [comment removed for export] *)
    unfold aobj, AIMG_HI in *. clear -K1 K2 K3 FK FKI. lia.
Qed.


Lemma AHL_blocks_disjoint : forall L RNG st LB m b1 b2,
  AHEAP_L L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
  ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1.
Proof.
  intros L RNG st LB m b1 b2 AH H1 H2 NE.
  pose proof AH as (ALO & _ & [X [AR BL]] & HFK). cbn [AHL ah_fake] in HFK.
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
      destruct AR as (WF & _ & _ & _ & _ & _ & HS & _). cbn [AHL ah_sec] in HS. unfold ASEC_of in HS.
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


Theorem AHL_block : forall L RNG st LB m p A n,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB ->
  1 <= n <= AREQMAX /\
  ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7))
  /\ rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) (live_pat (blk_entry L p A n) n)]      (* [comment removed for export] *)
  /\ wr_at asegs m A n
  /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
  /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO)).
Proof.
  intros L RNG st LB m p A n AH Hin.
  pose proof (AHEAP_P_hb_range _ L RNG st LB m p A n AH Hin) as BR.
  pose proof AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  pose proof AR as (WF & _ & _ & _ & CLS & _ & HS & _). pose proof WF as (SBE & PAE & SAL & SLO & SHI & PERC & _).
  cbn [AHL ah_sec] in HS. unfold ASEC_of in HS. pose proof HS as ((_ & _ & _ & _ & _ & WF1 & _) & (order & PO & _ & _ & PER) & _ & PZ & _).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - (* [comment removed for export] *)
    set (c := xb_class b) in *. set (k := xb_slot b) in *. set (S := size_of_class c) in *.
    pose proof (size_of_class_facts c CLB) as [QS QS16].
    destruct (PERC c CLB) as (A1 & A2 & A3 & A4 & _). destruct (RCLS c CLB) as (RREG & RSREGw & _). cbv zeta in RREG, RSREGw.
    pose proof (win_core _ _ _ RSREGw) as RSREG.   (* [comment removed for export] *)
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
    pose proof (SSH k KB) as SH. rewrite (busy_of_of_In L st X b WF Hb) in SH. cbn [slot_shadow_bytes] in SH. rewrite Sb, Nb in SH. fold S in SH.
    pose proof (chunk_shadow_geo L st X c k n ALO WF CLB KB ltac:(clear -NB; lia) FIT) as (SE & G2 & GEq & G0 & GF & _).
    pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
    assert (LBS : length (live_pat (al_pat L p) n) = Z.to_nat (granules n)) by (apply live_pat_length; lia).
    replace (Z.to_nat (shlen S)) with (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen (rz_size n) - granules n))%nat in SH
      by (generalize SRZ SG7 GF; subst S; clear; unfold granules; intros; lia).
    destruct (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) LBS ltac:(apply repeat_length) SH) as (_ & SHU & _).
    rewrite Z2Nat.id in SHU by lia. rewrite <- SE in SHU.
    split. { unfold blk_entry. rewrite PRIM. exact SHU. }
    (* [comment removed for export] *)
    pose proof (SL k KB) as SLK. rewrite (busy_of_of_In L st X b WF Hb) in SLK. unfold aslot_busy in SLK. cbv zeta in SLK. rewrite Sb in SLK.
    destruct SLK as (_ & _ & UJ). rewrite EAB, Nb in UJ. fold S in UJ.
    split. { eapply wr_at_sub'; [apply (wr_of_junk m _ (S - rz_size n)); [clear -FIT RG NB; lia| exact UJ]| destruct BR as (B1 & _); apply ablk_lin in B1; clear -B1; lia| clear; lia| clear -FIT RG NB; lia]. }
    split. { exists (CPrim c n). split; [exact LV|]. split; [reflexivity|]. intros P. rewrite PRIM in P. discriminate. }
    (* [comment removed for export] *)
    set (mu := c_mapped_user (get_cls st c)) in *.
    exists (aregion L c - 32768), (aregion L c + mu + 32768).
    assert (GEO : aregion L (c - 1) + K_REGION = aregion L c /\ aregion L 0 = al_space_beg L
                  /\ aregion L c mod 65536 = 0 /\ 0 <= aregion L (c - 1) /\ mu mod 32768 = 0 /\ 0 <= mu <= 3758096384).
    { unfold aregion, K_REGION. unfold K_ALIGN in SAL. unfold K_USER_MAP in A4. clear -SAL SP1 CLB A1 A2 A4.
      repeat split; first [lia | nia | Z.div_mod_to_equations; nia]. }
    destruct GEO as (GE1 & GE0 & GAL & GNN & MAL & MUR). unfold K_REGION in GE1.
    split; [clear -GAL; Z.div_mod_to_equations; lia|]. split; [clear -GAL MAL; Z.div_mod_to_equations; lia|].
    split; [clear -P5 RZ16; lia|]. split; [subst mu; clear -P4 A1 FIT RG; lia|].
    replace (aregion L c + mu + 32768 - (aregion L c - 32768)) with (mu + 65536) by (clear; lia).
    assert (SHW : shad (aregion L c - 32768) = shad (aregion L c) - 4096 /\ shlen (mu + 65536) = 4096 + (shlen mu + 4096)
                  /\ shad (aregion L c) - 4096 = shad (aregion L (c - 1)) + (shlen K_REGION - 4096) /\ 0 <= shlen mu
                  /\ shlen mu + 4096 <= shlen K_REGION /\ 0 <= shad (aregion L (c - 1)) /\ shlen K_REGION = 536870912
                  /\ 0 <= shad (aregion L c)).
    { rewrite !shad_div, !shlen_div. unfold K_REGION, ASHOFF. clear -GAL GNN MAL MUR GE1. Z.div_mod_to_equations. lia. }
    destruct SHW as (SW1 & SW2 & SW3 & SW4 & SW5 & SW6 & SW7 & SW8). rewrite SW1, SW2.
    split.
    + (* [comment removed for export] *) replace (4096 + (shlen mu + 4096)) with (shlen mu + 8192) by (clear; lia). exact RSREGw.
    + assert (W1 : wr_at asegs m (shad (aregion L (c - 1))) (shlen K_REGION)).
      { (* [comment removed for export] *)
        destruct (Z.eq_dec c 1) as [C1|C1].
        { rewrite C1. change (1 - 1) with 0. rewrite GE0. exact (wr_of_azero _ _ _ PZ). }
        eapply region_shadow_wr; [exact AR| unfold K_NUM_CLASSES; clear -CLB C1; lia]. }
      assert (W2 : wr_at asegs m (shad (aregion L c)) (shlen K_REGION)) by (eapply region_shadow_wr; [exact AR| unfold K_NUM_CLASSES; exact CLB]).
      apply wr_at_join; [| | clear; lia| clear -SW4; lia].
      * eapply wr_at_sub'; [exact W1| | |]; rewrite ?SW3; clear -SW6 SW7; lia.
      * replace (shad (aregion L c) - 4096 + 4096) with (shad (aregion L c)) by (clear; lia).
        eapply wr_at_sub'; [exact W2| | |]; clear -SW4 SW5 SW8; lia.
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
    split. { unfold blk_entry. rewrite PRIM. replace (mb + 6144 - 6144) with mb by (clear; lia). unfold sec_user_shadow in SU. exact SU. }
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


Lemma AHL_chunk : forall L RNG st LB m p A n, AHEAP_L L RNG st LB m -> In (HB p A n) LB ->
  exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
Proof.
  intros L RNG st LB m p A n AH Hin. pose proof AH as (ALO & _ & [X [AR BL]] & _).
  destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(b & _ & _ & _ & _ & _ & _ & _ & LV & PRIM & _)|(mb & ms & Lp & EA & G & PRIM & _)].
  - exists (CPrim (xb_class b) n). split; [exact LV|]. split; [reflexivity|]. split; [intros P; rewrite PRIM in P; discriminate| exact PRIM].
  - exists (CSec mb ms n). split; [exact Lp|]. split; [reflexivity|]. split; [| exact PRIM].
    intros _. cbn [sec_wf1] in G. destruct G as (_ & _ & _ & _ & G5 & G6 & _). pose proof (sec_facts n ltac:(clear -G5; lia) G6) as (_ & RZ & _).
    subst A. cbn [chunk_user_beg]. unfold SEC_UOFF, PG. rewrite RZ. clear; lia.
Qed.

Lemma AHL_premap : forall L RNG st LB m, AHEAP_L L RNG st LB m -> premap_cells m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _). destruct AR as (_ & RT & _ & _ & _ & _ & _ & _ & _ & RT2 & _ & RT3).
  eapply premap_of_rt'; [exact RT| exact RT2| exact RT3].
Qed.

Theorem AHL_xr : forall L RNG st LB m, AHEAP_L L RNG st LB m -> icpt_tab_at m (al_xr L).
Proof.
  intros L RNG st LB m (ALO & _ & [X [AR _]] & _).
  destruct AR as (_ & RT & _).
  do 28 (destruct RT as [_ RT]). destruct RT as (X1 & X2 & X3).
  pose proof (alayout_xr L (al_xr L) 3727360 ALO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (XR1 & XR2 & _).
  pose proof (ao_xr L ALO) as (PG & _).
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
  split; [clear -XR1; unfold AIMG_HI in *; lia|]. split; [exact XR2| exact PG].
Qed.


Theorem AHL_xr_blocks : forall L RNG st LB m p A n,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB -> A + n <= al_xr L \/ al_xr L + 3727360 <= A.
Proof.
  intros L RNG st LB m p A n (ALO & _ & [X [AR BL]] & _) Hin.
  pose proof (alayout_xr L (al_xr L) 3727360 ALO ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as (XR1 & XR2 & XRt & XRc & XRr & XRn & XRs & XRf & XRp & XRd).
  pose proof (ao_space L ALO) as RSP.
  destruct (hb_where L st X LB m ALO AR BL p A n Hin) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - pose proof (hb_prim_span L st X LB m AR p A n c Hin Hc Q1 Q2) as (S1 & S2 & S3).
    unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -S1 S2 XRr RSP. lia.
  - cbn [sec_wf1] in Q3. destruct Q3 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Cx)). clear -Cx Q1 Q2. lia.
Qed.


Lemma AHL_lsan : forall L RNG st LB m, AHEAP_L L RNG st LB m -> rw_cells asegs m 0x6a4df8 [C4 (Z_to_bv 64 0)].
Proof.
  intros L RNG st LB m (ALO & ARNG & [X [AR BL]] & HFK). destruct AR as (_ & RT & _). unfold arep_rt in RT. decompose [and] RT. assumption.
Qed.

End CANSEC1.
