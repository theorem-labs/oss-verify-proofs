(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Refund.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Restrict OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Fixej5z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.EvtAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund.Madv3tp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocI AMalmys ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ABudget ASecB3 AFreeB6 ANodijx APgGeo AFreeX1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@G1; @BIG; @Q4; @MSZ; @Q1; @Q2; @X1; @X2; @G6; @A3; @B1; @Q3; @G5; @A1; @H5; @B3; @LEN; @G8; @G7; @G4; @Hx; @NQB; @X3; @G3; @C1; @C2; @SIDE; @HHI; @CE; @NM; @N6; @A2; @A4; @B2; @B4; @SHA; @M2; @M3; @M4; @G2])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma list_set_app_mid : forall {X} (l1 : list X) x l2 y, list_set (l1 ++ x :: l2) (length l1) y = l1 ++ y :: l2.
Proof. intros X l1. induction l1 as [|a l1 IH]; intros x l2 y; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma swap_remove_perm : forall {X} (l : list X) i x d, nth_error l i = Some x -> Permutation (x :: swap_remove l i d) l.
Proof.
  intros X l i x d H. (first [ pose proof ((@nth_error_split _ l i x H)) as dR_1; dex2 dR_1 as l1 l2; destruct dR_1 as [-> LEN] | pose proof ((@nth_error_split _ l i x H)) as dR_1; dand4 dR_1 as l1 l2 -> LEN | destruct (@nth_error_split _ l i x H) as (l1 & l2 & -> & LEN) ]). unfold swap_remove. rewrite <- LEN, list_set_app_mid.
  destruct l2 as [|c l2t].
  - rewrite (List.last_last l1 x d). rewrite List.removelast_last. apply Permutation_cons_append.
  - assert (NE : c :: l2t <> []) by discriminate.
    pose proof (List.app_removelast_last d NE) as E. set (R := removelast (c :: l2t)) in *. set (z := List.last (c :: l2t) d) in *. rewrite E.
    replace (l1 ++ x :: R ++ [z]) with ((l1 ++ x :: R) ++ [z]) by (rewrite <- app_assoc; reflexivity). rewrite (List.last_last (l1 ++ x :: R) z d).
    replace (l1 ++ z :: R ++ [z]) with ((l1 ++ z :: R) ++ [z]) by (rewrite <- app_assoc; reflexivity). rewrite List.removelast_last.
    rewrite <- app_assoc. cbn [app].
    (* [comment removed for export] *)
    apply (Permutation_trans (l' := l1 ++ x :: z :: R)); [apply Permutation_middle|].
    apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append.
Qed.

Lemma flat_map_perm : forall {X Y} (f : X -> list Y) l l', Permutation l l' -> Permutation (flat_map f l) (flat_map f l').
Proof.
  intros X Y f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2].
  - apply Permutation_refl.
  - cbn. apply Permutation_app_head. exact IH.
  - cbn. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - exact (Permutation_trans IH1 IH2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma existsb_perm : forall {X} (f : X -> bool) l l', Permutation l l' -> existsb f l = existsb f l'.
Proof.
  intros X f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn; [reflexivity| rewrite IH; reflexivity| | congruence].
  destruct (f y), (f x); reflexivity.
Qed.
Lemma hull_bytes_perm : forall A A', Permutation A A' -> hull_bytes A = hull_bytes A'.
Proof.
  intros A A' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [hull_bytes]; [reflexivity| rewrite IH; reflexivity| lia| congruence].
Qed.
Lemma page_hullb_perm : forall A A' p, Permutation A A' -> page_hullb A p = page_hullb A' p.
Proof. intros A A' p P. unfold page_hullb. apply existsb_perm. exact P. Qed.
Lemma in_hullb_perm : forall A A' x, Permutation A A' -> in_hullb A x = in_hullb A' x.
Proof. intros A A' x P. unfold in_hullb. apply existsb_perm. exact P. Qed.
Lemma hidc_perm : forall A A', Permutation A A' -> hidc A = hidc A'.
Proof. intros A A' P. apply functional_extensionality. intros a. unfold hidc. rewrite (in_hullb_perm A A' _ P). reflexivity. Qed.
(* [comment removed for export] *)
Lemma hull_cover_perm : forall A A' AL AL' lz, Permutation A A' -> Permutation AL AL' -> hull_cover A AL lz -> hull_cover A' AL' lz.
Proof.
  intros A A' AL AL' lz PA PL C lo hi Hin. destruct (C lo hi (Permutation_in _ (Permutation_sym PA) Hin)) as [(l & h & Hlh & B1 & B2)|F]; [left| right; exact F].
  exists l, h. split; [exact (Permutation_in _ PL Hlh)| split; assumption].
Qed.
Lemma MInv_perm : forall A A' AL AL' E md, Permutation A A' -> Permutation AL AL' -> MInv A AL E md -> MInv A' AL' E md.
Proof.
  intros A A' AL AL' E md P PL HI. apply (MInv_rehull A AL A' AL' E E md HI).
  - intros p Hp. rewrite <- (page_hullb_perm AL AL' _ PL). exact (minv_hull HI p Hp).
  - exact (hull_cover_perm A A' AL AL' _ P PL (minv_cover HI)).
  - lia.
  - rewrite <- (hull_bytes_perm AL AL' PL). exact (minv_budget HI).
Qed.
Lemma in_firstn_skipn_S : forall {X} (l : list X) i x, In x (firstn i l ++ skipn (S i) l) -> In x l.
Proof.
  intros X l i x H. rewrite <- (firstn_skipn i l). apply in_app_iff in H as [H|H]; apply in_app_iff; [left; exact H| right].
  replace (S i) with (1 + i)%nat in H by lia. rewrite <- skipn_skipn in H. destruct (skipn i l) as [|y l']; cbn in H; [destruct H| right; exact H].
Qed.
Lemma lsec_regions_perm : forall l l', Permutation l l' -> Permutation (lsec_regions_ l) (lsec_regions_ l').
Proof. intros. unfold lsec_regions_. apply Permutation_map. assumption. Qed.
Lemma lsec_regions_app : forall l l', lsec_regions_ (l ++ l') = lsec_regions_ l ++ lsec_regions_ l'.
Proof. intros. unfold lsec_regions_. apply map_app. Qed.
Lemma lsec_regions_cons : forall c l, lsec_regions_ (c :: l) = [shadow_region (cs_map c) (map_size (cs_n c))] ++ lsec_regions_ l.
Proof. reflexivity. Qed.
Lemma H_off_segments_perm : forall segs A A', Permutation A A' -> H_off_segments segs (hidc A) -> H_off_segments segs (hidc A').
Proof. intros segs A A' P H. rewrite <- (hidc_perm A A' P). exact H. Qed.

Lemma hull_of_perm : forall R R', Permutation R R' -> Permutation (hull_of R) (hull_of R').
Proof. intros R R' P. unfold hull_of. apply Permutation_map. exact P. Qed.
Lemma sec_regions_perm : forall l l', Permutation l l' -> Permutation (sec_regions_ l) (sec_regions_ l').
Proof. intros l l' P. unfold sec_regions_. apply flat_map_perm. exact P. Qed.
Lemma sec_regions_app : forall l l', sec_regions_ (l ++ l') = sec_regions_ l ++ sec_regions_ l'.
Proof. intros l l'. unfold sec_regions_. apply flat_map_app. Qed.
Lemma sec_regions_cons : forall c l, sec_regions_ (c :: l) = [(cs_map c, map_size (cs_n c)); shadow_region (cs_map c) (map_size (cs_n c))] ++ sec_regions_ l.
Proof. intros c l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pg_facts : forall x, x - 4095 <= pg_dn x <= x /\ pg_dn x mod 4096 = 0 /\ x <= pg_up x <= x + 4095 /\ pg_up x mod 4096 = 0.
Proof. intros x. pose proof (pg_dn_bounds x). pose proof (pg_up_bounds x). tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Hulls.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (i : nat).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQB : kQuarantineMaxSize < n0.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some (CS (p - 6144) n0).

  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).

  Let NQ' : kMaxPrimaryUser < n0. Proof. unfold kQuarantineMaxSize, kMaxPrimaryUser in *. lia. Qed.
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.

  (* [comment removed for export] *)
  Definition e1 : Z * Z := (sh h, pbeg).
  Definition emid : Z * Z := (pbeg, pend).
  Definition e2 : Z * Z := (pend, sh h + msz / 8).
  Definition dead2 : list (Z * Z) := [e1; e2].
  (* [comment removed for export] *)
  Definition REST : hull :=
    pa_image_ivs ++ hull_of (fixed_regions_ AL_pasan P ++ classes_regions_ sb (a_reg A) 31 ++ sec_regions_ (firstn i chunks ++ skipn (S i) chunks))
    ++ a_deadsh A ++ p_extra P.
  Definition H0p : hull := (h, h + msz) :: (sh h, sh h + msz / 8) :: REST.
  Definition H0s : hull := (h, h + msz) :: e1 :: emid :: e2 :: REST.
  Definition H1 : hull := (h, h + msz) :: e1 :: e2 :: REST.
  Definition H2 : hull := e1 :: e2 :: REST.
  (* [comment removed for export] *)
  Definition LREST : hull :=
    hull_of (lfixed_regions_ AL_pasan P ++ lclasses_regions_ sb (a_reg A) 31 ++ lsec_regions_ (firstn i chunks ++ skipn (S i) chunks))
    ++ a_deadsh A ++ p_extra P.
  Definition L0p : hull := (sh h, sh h + msz / 8) :: LREST.
  Definition L0s : hull := e1 :: emid :: e2 :: LREST.
  Definition L1 : hull := e1 :: e2 :: LREST.

  (* [comment removed for export] *)
  #[using="NQ' NQB HL AI md m A Clg"] Lemma a8_geo : pg_dn (sh h) <= sh h <= pbeg /\ pbeg < pg_dn (sh h) + 4096 + 1 /\ sh h < pg_dn (sh h) + 4096 /\ pbeg <= sh h + 4095 /\
                 pbeg + 0xE000 <= pend /\ pend <= sh h + msz / 8 <= pg_up (sh h + msz / 8) /\ sh h + msz / 8 < pend + 4096 /\
                 pg_up (sh h + msz / 8) <= sh h + msz / 8 + 4095 /\
                 pg_dn (sh h) mod 4096 = 0 /\ pbeg mod 4096 = 0 /\ pend mod 4096 = 0 /\ pg_up (sh h + msz / 8) mod 4096 = 0 /\
                 sh (h + msz) = sh h + msz / 8 /\ 0x10000 <= msz / 8 /\
                 ((kHighShadowMapBeg <= pg_dn (sh h) /\ pg_up (sh h + msz / 8) <= kHighMemBeg /\ kHighMemBeg <= h) \/
                  (kLowShadowBeg <= pg_dn (sh h) /\ pg_up (sh h + msz / 8) <= kShadowGapBeg /\ h + msz <= kLowShadowMapBeg)).
  Proof.
    (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_2; dand11 dR_2 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]).
    (first [ pose proof ((sk_shr A m md p n0 AI HL NQ')) as dR_3; dand4 dR_3 as SHA M512 D512 SIDE | pose proof (sk_shr A m md p n0 AI HL NQ') as (SHA & M512 & D512 & SIDE) ]).
    (first [ pose proof ((pg_facts (sh h))) as dR_4; dand4 dR_4 as A1 A2 A3 A4 | pose proof (pg_facts (sh h)) as (A1 & A2 & A3 & A4) ]). (first [ pose proof ((pg_facts (sh h + msz / 8))) as dR_5; dand4 dR_5 as B1 B2 B3 B4 | pose proof (pg_facts (sh h + msz / 8)) as (B1 & B2 & B3 & B4) ]).
    unfold a8_pbeg, a8_pend.
    assert (BIG : 0x10000 <= msz / 8).
    { apply Z.div_le_lower_bound; [lia|]. unfold kQuarantineMaxSize in NQB. lia. }
    pose proof (Z_div_mod_eq_full (pg_dn (sh h)) 4096) as Q1. rewrite A2, Z.add_0_r in Q1.
    pose proof (Z_div_mod_eq_full (pg_up (sh h)) 4096) as Q2. rewrite A4, Z.add_0_r in Q2.
    pose proof (Z_div_mod_eq_full (pg_dn (sh h + msz / 8)) 4096) as Q3. rewrite B2, Z.add_0_r in Q3.
    pose proof (Z_div_mod_eq_full (pg_up (sh h + msz / 8)) 4096) as Q4. rewrite B4, Z.add_0_r in Q4.
    repeat (split; [lia|]).
    unfold kHighShadowMapBeg, kHighMemBeg, kLowShadowBeg, kShadowGapBeg, kLowShadowMapBeg in *.
    destruct SIDE as [(X1 & X2 & X3)|(X1 & X2 & X3)]; [left| right]; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="NQ' NTH NQB HL AI md m"] Lemma hull_perm0 : Permutation (pa_hull A) H0p.
  Proof.
    (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_6; dand5 dR_6 as HLO HAL MSZ MSZAL _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & HAL & MSZ & MSZAL & _) ]).
    (first [ pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_7; dex2 dR_7 as l1 l2; destruct dR_7 as [E LEN] | pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_7; dand4 dR_7 as l1 l2 E LEN | destruct (@nth_error_split _ chunks i _ NTH) as (l1 & l2 & E & LEN) ]).
    assert (F1 : firstn i chunks = l1) by (rewrite E, <- LEN; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
    assert (F2 : skipn (S i) chunks = l2).
    { rewrite E, <- LEN. rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
    unfold H0p, REST. rewrite F1, F2. unfold pa_hull, ahull_of, ahull_of_, aregions_. change (p_sb P) with sb.
    rewrite E at 1. rewrite sec_regions_app, sec_regions_cons. cbn [cs_map cs_n].
    rewrite (shadow_region_aligned h msz) by first [apply (mod0_down _ 4096 64); [exists 64; reflexivity| assumption] | lia].
    rewrite sec_regions_app, !hull_of_app. cbn [hull_of map fst snd app].
    (* [comment removed for export] *)
    apply Permutation_sym.
    lazymatch goal with |- Permutation (?a :: ?b :: ?img ++ (?X ++ ?Y ++ ?Z1 ++ ?Z2) ++ ?D ++ ?EX) _ =>
      apply (Permutation_trans (l' := (img ++ X ++ Y ++ Z1) ++ [a; b] ++ (Z2 ++ D ++ EX)));
      [ replace (a :: b :: img ++ (X ++ Y ++ Z1 ++ Z2) ++ D ++ EX) with ([a; b] ++ (img ++ X ++ Y ++ Z1) ++ (Z2 ++ D ++ EX)) by (repeat rewrite <- app_assoc; reflexivity);
        apply Permutation_app_swap_app
      | repeat rewrite <- app_assoc; apply Permutation_refl ]
    end.
  Qed.

  (* [comment removed for export] *)
  #[using="NQ' NTH NQB HL AI md m"] Lemma lhull_perm0 : Permutation (pa_lhull A) L0p.
  Proof.
    (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_6; dand5 dR_6 as HLO HAL MSZ MSZAL _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & HAL & MSZ & MSZAL & _) ]).
    (first [ pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_7; dex2 dR_7 as l1 l2; destruct dR_7 as [E LEN] | pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_7; dand4 dR_7 as l1 l2 E LEN | destruct (@nth_error_split _ chunks i _ NTH) as (l1 & l2 & E & LEN) ]).
    assert (F1 : firstn i chunks = l1) by (rewrite E, <- LEN; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
    assert (F2 : skipn (S i) chunks = l2).
    { rewrite E, <- LEN. rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
    unfold L0p, LREST. rewrite F1, F2. unfold pa_lhull, alhull_of, alhull_of_, alregions_. change (p_sb P) with sb.
    rewrite E at 1. rewrite lsec_regions_app, lsec_regions_cons. cbn [cs_map cs_n].
    rewrite (shadow_region_aligned h msz) by first [apply (mod0_down _ 4096 64); [exists 64; reflexivity| assumption] | lia].
    rewrite lsec_regions_app, !hull_of_app. cbn [hull_of map fst snd app].
    apply Permutation_sym.
    lazymatch goal with |- Permutation (?b :: (?X ++ ?Y ++ ?Z1 ++ ?Z2) ++ ?DD ++ ?EX) _ =>
      apply (Permutation_trans (l' := (X ++ Y ++ Z1) ++ [b] ++ (Z2 ++ DD ++ EX)));
      [ replace (b :: (X ++ Y ++ Z1 ++ Z2) ++ DD ++ EX) with ([b] ++ (X ++ Y ++ Z1) ++ (Z2 ++ DD ++ EX)) by (repeat rewrite <- app_assoc; reflexivity);
        apply Permutation_app_swap_app
      | repeat rewrite <- app_assoc; apply Permutation_refl ]
    end.
  Qed.
  (* [comment removed for export] *)
  #[using="NQ' NTH NQB HL AI md m W"] Lemma cover_REST : forall mdx,
    alzfree_ AL_pasan P (a_reg A) mdx ->
    Forall (fun sc => eager_map (wz (cs_map sc)) (wz (map_size (cs_n sc))) mdx) (firstn i chunks ++ skipn (S i) chunks) ->
    hull_cover REST LREST (m_vm_lazy mdx).
  Proof.
    intros mdx Z9 EM. unfold REST, LREST. change sb with (p_sb P).
    apply (ahull_cover_ P (a_reg A) (SR (firstn i chunks ++ skipn (S i) chunks) 0) (a_deadsh A) mdx Z9 EM).
    cbn [sr_chunks]. intros sc Hsc.
    pose proof (in_firstn_skipn_S chunks i sc Hsc) as Hin.
    (first [ pose proof ((sec_chunk_bounds A sc W Hin)) as dR; dand5 dR as B1 _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W Hin) as (B1 & _ & B3 & B4 & _) ]).
    apply app_facts in B3. pose proof alloc_ceiling_val as CE'. clear - B1 B3 CE'. Zify.zify; xlia zchecker.
  Qed.

  #[using="NQ' NQB HL AI md m"] Lemma hull_bytes_H0s : hull_bytes H0s = hull_bytes H0p.
  Proof.
    (first [ pose proof (a8_geo) as dR_8; dand15 dR_8 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG _ | pose proof a8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & _) ]).
    unfold H0s, H0p, e1, emid, e2. rewrite !hull_bytes_cons.
    unfold hull_npages, page_size. cbn [fst snd].
    set (x := sh h + msz / 8) in *. set (u := pg_up x) in *. set (dn := pg_dn (sh h)) in *.
    set (K := 4096 * Z.of_nat (Z.to_nat ((h + msz - 1) / 4096 - h / 4096 + 1))). clearbody K.
    pose proof (Z_div_mod_eq_full dn 4096) as Q1. rewrite M1, Z.add_0_r in Q1.
    pose proof (Z_div_mod_eq_full pbeg 4096) as Q2. rewrite M2, Z.add_0_r in Q2.
    pose proof (Z_div_mod_eq_full pend 4096) as Q3. rewrite M3, Z.add_0_r in Q3.
    pose proof (Z_div_mod_eq_full u 4096) as Q4. rewrite M4, Z.add_0_r in Q4.
    assert (E0 : (x - 1) / 4096 = u / 4096 - 1) by (clear - G6 G8 Q4; lia).
    assert (E1 : sh h / 4096 = dn / 4096) by (clear - G1 G3 Q1; lia).
    assert (E2 : (pbeg - 1) / 4096 = pbeg / 4096 - 1) by (clear - Q2; lia).
    assert (E3 : (pend - 1) / 4096 = pend / 4096 - 1) by (clear - Q3; lia).
    assert (E4 : (u - 1) / 4096 = u / 4096 - 1) by (clear - Q4; lia).
    rewrite ?E0, ?E1, ?E2, ?E3, ?E4.
    set (qa := dn / 4096) in *. set (qb := pbeg / 4096) in *. set (qc := pend / 4096) in *. set (qd := u / 4096) in *.
    clearbody qa qb qc qd. clear - G1 G5 G6 Q1 Q2 Q3 Q4. lia.
  Qed.

  #[using="NQ' NQB HL AI md m"] Lemma lhull_bytes_H0s : hull_bytes L0s = hull_bytes L0p.
  Proof.
    pose proof hull_bytes_H0s as X. unfold H0s, H0p in X. unfold L0s, L0p. cbn [hull_bytes] in X |- *.
    set (KR := hull_bytes REST) in X. set (KL := hull_bytes LREST). clearbody KR KL. clear - X. Zify.zify; xlia zchecker.
  Qed.
  (* [comment removed for export] *)
  Lemma cover_H0s : forall mdx, hull_cover REST LREST (m_vm_lazy mdx) -> lazy_free (m_vm_lazy mdx) h (h + msz) ->
    hull_cover H0s L0s (m_vm_lazy mdx).
  Proof.
    intros mdx CR LZC. unfold H0s, L0s.
    apply hull_cover_cons; [right; cbn [fst snd]; exact LZC|].
    apply hull_cover_cons; [left; apply iv_sub_In; cbn [fst snd In]; left; destruct e1; reflexivity|].
    apply hull_cover_cons; [left; apply iv_sub_In; cbn [fst snd In]; right; left; destruct emid; reflexivity|].
    apply hull_cover_cons; [left; apply iv_sub_In; cbn [fst snd In]; right; right; left; destruct e2; reflexivity|].
    change (e1 :: emid :: e2 :: LREST) with ([e1; emid; e2] ++ LREST). intros lo hi Hin. destruct (CR lo hi Hin) as [S|F]; [left; apply iv_sub_app_r; exact S| right; exact F].
  Qed.
  #[using="NQ' NQB HL AI md m"] Lemma MInv_H0s : forall E mdx, MInv H0p L0p E mdx ->
    hull_cover REST LREST (m_vm_lazy mdx) -> lazy_free (m_vm_lazy mdx) h (h + msz) -> MInv H0s L0s E mdx.
  Proof.
    intros E mdx HI CR LZC. (first [ pose proof (a8_geo) as dR_9; dand13 dR_9 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 _ | pose proof a8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & _) ]).
    apply (MInv_rehull H0p L0p H0s L0s E E mdx HI).
    - intros q Hq. pose proof (minv_hull HI q Hq) as X. unfold L0p, L0s in *.
      cbn [page_hullb existsb] in X |- *. set (RR := existsb (page_meets_ivb (bv_unsigned q)) LREST) in *. clearbody RR.
      unfold e1, emid, e2, page_meets_ivb in *. cbn [fst snd] in *. unfold page_size in *.
      apply Bool.orb_true_iff in X as [X|X]; [| rewrite X, !Bool.orb_true_r; reflexivity].
      apply andb_true_iff in X as [X1 X2]. apply Z.ltb_lt in X1. apply Z.ltb_lt in X2.
      clear - X1 X2 G1 G5 G6.
      destruct (Z.lt_ge_cases (bv_unsigned q) pbeg) as [C1|C1]; [apply Bool.orb_true_iff; left; apply andb_true_iff; split; apply Z.ltb_lt; lia|].
      apply Bool.orb_true_iff; right.
      destruct (Z.lt_ge_cases (bv_unsigned q) pend) as [C2|C2]; [apply Bool.orb_true_iff; left; apply andb_true_iff; split; apply Z.ltb_lt; lia|].
      apply Bool.orb_true_iff; right. apply Bool.orb_true_iff; left. apply andb_true_iff; split; apply Z.ltb_lt; lia.
    - exact (cover_H0s mdx CR LZC).
    - lia.
    - rewrite lhull_bytes_H0s. exact (minv_budget HI).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="NQ' NQB HL AI md m"] Lemma MInv_H1 : forall E mdx, MInv H0s L0s E mdx ->
    hull_cover REST LREST (m_vm_lazy mdx) -> lazy_free (m_vm_lazy mdx) h (h + msz) ->
    MInv H1 L1 E (madvise_model (wz pbeg) (wz (pend - pbeg)) mdx).
  Proof.
    intros E mdx HI CR LZC. (first [ pose proof (a8_geo) as dR_10; dand15 dR_10 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof a8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]). pose proof alloc_ceiling_val as CE.
    assert (R1 : bv_unsigned (wz pbeg) = pbeg) by (apply unsigned_lit; kung_all; lia).
    assert (R2 : bv_unsigned (wz (pend - pbeg)) = pend - pbeg) by (apply unsigned_lit; kung_all; lia).
    replace H1 with ([(h, h + msz); e1] ++ e2 :: REST) by reflexivity. replace L1 with ([e1] ++ e2 :: LREST) by reflexivity.
    apply (MInv_madvise_remove [(h, h + msz); e1] [emid] (e2 :: REST) [e1] (e2 :: LREST) E (wz pbeg) (wz (pend - pbeg)) mdx).
    - exact HI.
    - rewrite R1. exact M2.
    - intros l hh Hin. destruct Hin as [EQ|[]]. unfold emid in EQ. injection EQ as <- <-. rewrite R1, R2. lia.
    - (* [comment removed for export] *)
      intros lo hi Hin _. cbn [app In] in Hin. destruct Hin as [EQ|[EQ|[EQ|Hin]]].
      + injection EQ as <- <-. right. exact LZC.
      + left. apply iv_sub_In. rewrite <- EQ. cbn [app In]. left. reflexivity.
      + left. apply iv_sub_In. rewrite <- EQ. cbn [app In]. right. left. reflexivity.
      + destruct (CR lo hi Hin) as [S|F]; [left| right; exact F]. change ([e1] ++ e2 :: LREST) with ([e1; e2] ++ LREST). apply iv_sub_app_r. exact S.
  Qed.

  (* [comment removed for export] *)
  #[using="NQ' NQB HL AI md m"] Lemma MInv_H2 : forall E mdx, MInv H1 L1 E mdx -> map_has (vm_maps (m_vmmaps mdx)) (wz h) (wz msz) = true -> eager_map (wz h) (wz msz) mdx ->
    MInv H2 L1 (E - msz) (munmap_modelL (wz h) (wz msz) mdx).   (* [comment removed for export] *)
  Proof.
    intros E mdx HI HAS EM. (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_11; dand11 dR_11 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]). pose proof alloc_ceiling_val as CE.
    assert (R1 : bv_unsigned (wz h) = h) by (apply unsigned_lit; lia). assert (R2 : bv_unsigned (wz msz) = msz) by (apply unsigned_lit; lia).
    pose proof (MInv_munmap_refund H1 L1 E (wz h) (wz msz) mdx HI HAS EM) as HI'. rewrite R2 in HI'.
    change H2 with ([] ++ e1 :: e2 :: REST). exact (MInv_hull_remove_all [] [(h, h + msz)] (e1 :: e2 :: REST) L1 (E - msz) _ HI').
  Qed.

  (* [comment removed for export] *)
  #[using="NTH"] Lemma lhull_permF : forall D' ia', Permutation L1 (pa_lhull (freeS A p i D' ia' dead2)).
  Proof.
    intros D' ia'. unfold L1, LREST, dead2, pa_lhull, alhull_of, alhull_of_, alregions_.
    cbn [freeS a_pl a_reg a_sec a_deadsh sec_remove sr_chunks]. change (p_sb (a_pl A)) with sb.
    assert (PR : Permutation (swap_remove chunks i (CS 0 0)) (firstn i chunks ++ skipn (S i) chunks)).
    { apply (Permutation_cons_inv (a := CS h n0)). apply (Permutation_trans (swap_remove_perm chunks i (CS h n0) (CS 0 0) NTH)).
      (first [ pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_12; dex2 dR_12 as l1 l2; destruct dR_12 as [E LEN] | pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_12; dand4 dR_12 as l1 l2 E LEN | destruct (@nth_error_split _ chunks i _ NTH) as (l1 & l2 & E & LEN) ]).
      assert (F1 : firstn i chunks = l1) by (rewrite E, <- LEN; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
      assert (F2 : skipn (S i) chunks = l2).
      { rewrite E, <- LEN. rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
      rewrite F1, F2. rewrite E at 1. apply Permutation_sym. apply Permutation_middle. }
    set (CH' := swap_remove chunks i (CS 0 0)) in *. set (CH := firstn i chunks ++ skipn (S i) chunks) in *.
    set (X := lfixed_regions_ AL_pasan P). set (Y := lclasses_regions_ sb (a_reg A) 31). set (DD := a_deadsh A). set (EX := p_extra P).
    rewrite !hull_of_app.
    apply (Permutation_trans (l' := [e1; e2] ++ (hull_of X ++ hull_of Y ++ hull_of (lsec_regions_ CH')) ++ DD ++ EX)).
    - cbn [app]. apply perm_skip. apply perm_skip. apply Permutation_app_tail. apply Permutation_app_head. apply Permutation_app_head.
      apply hull_of_perm. apply lsec_regions_perm. apply Permutation_sym. exact PR.
    - rewrite <- (app_assoc DD [e1; e2] EX).
      apply (Permutation_trans (l' := ((hull_of X ++ hull_of Y ++ hull_of (lsec_regions_ CH')) ++ DD) ++ [e1; e2] ++ EX)).
      + replace ([e1; e2] ++ (hull_of X ++ hull_of Y ++ hull_of (lsec_regions_ CH')) ++ DD ++ EX)
          with ([e1; e2] ++ ((hull_of X ++ hull_of Y ++ hull_of (lsec_regions_ CH')) ++ DD) ++ EX) by (rewrite <- !app_assoc; reflexivity).
        apply Permutation_app_swap_app.
      + rewrite <- !app_assoc. apply Permutation_refl.
  Qed.
  (* [comment removed for export] *)
  #[using="NTH"] Lemma hull_permF : forall D' ia', Permutation H2 (pa_hull (freeS A p i D' ia' dead2)).
  Proof.
    intros D' ia'. unfold H2, REST, dead2, pa_hull, ahull_of, ahull_of_, aregions_.
    cbn [freeS a_pl a_reg a_sec a_deadsh sec_remove sr_chunks]. change (p_sb (a_pl A)) with sb.
    (* [comment removed for export] *)
    assert (PR : Permutation (swap_remove chunks i (CS 0 0)) (firstn i chunks ++ skipn (S i) chunks)).
    { apply (Permutation_cons_inv (a := CS h n0)). apply (Permutation_trans (swap_remove_perm chunks i (CS h n0) (CS 0 0) NTH)).
      (first [ pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_12; dex2 dR_12 as l1 l2; destruct dR_12 as [E LEN] | pose proof ((@nth_error_split _ chunks i _ NTH)) as dR_12; dand4 dR_12 as l1 l2 E LEN | destruct (@nth_error_split _ chunks i _ NTH) as (l1 & l2 & E & LEN) ]).
      assert (F1 : firstn i chunks = l1) by (rewrite E, <- LEN; rewrite firstn_app, firstn_all, Nat.sub_diag; cbn; rewrite app_nil_r; reflexivity).
      assert (F2 : skipn (S i) chunks = l2).
      { rewrite E, <- LEN. rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
      rewrite F1, F2. rewrite E at 1. apply Permutation_sym. apply Permutation_middle. }
    set (CH' := swap_remove chunks i (CS 0 0)) in *. set (CH := firstn i chunks ++ skipn (S i) chunks) in *.
    set (X := fixed_regions_ AL_pasan P). set (Y := classes_regions_ sb (a_reg A) 31). set (D := a_deadsh A). set (EX := p_extra P).
    rewrite !hull_of_app.
    apply (Permutation_trans (l' := [e1; e2] ++ pa_image_ivs ++ (hull_of X ++ hull_of Y ++ hull_of (sec_regions_ CH')) ++ D ++ EX)).
    - cbn [app]. apply perm_skip. apply perm_skip. apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_app_head. apply Permutation_app_head.
      apply hull_of_perm. apply sec_regions_perm. apply Permutation_sym. exact PR.
    - (* [comment removed for export] *)
      rewrite <- (app_assoc D [e1; e2] EX).
      apply (Permutation_trans (l' := (pa_image_ivs ++ (hull_of X ++ hull_of Y ++ hull_of (sec_regions_ CH')) ++ D) ++ [e1; e2] ++ EX)).
      + replace ([e1; e2] ++ pa_image_ivs ++ (hull_of X ++ hull_of Y ++ hull_of (sec_regions_ CH')) ++ D ++ EX)
          with ([e1; e2] ++ (pa_image_ivs ++ (hull_of X ++ hull_of Y ++ hull_of (sec_regions_ CH')) ++ D) ++ EX) by (rewrite <- !app_assoc; reflexivity).
        apply Permutation_app_swap_app.
      + rewrite <- !app_assoc. apply Permutation_refl.
  Qed.

  (* [comment removed for export] *)
  #[using="NQ' NQB HL AI md m A Clg"] Lemma dead2_ok :
    Forall (fun lh => ((kHighShadowMapBeg <= fst lh /\ snd lh <= kHighMemBeg) \/ (kLowShadowBeg <= fst lh /\ snd lh <= kShadowGapBeg))
                      /\ fst lh <= snd lh <= fst lh + kDeadShadowBytes /\ fst lh mod 8 = 0 /\ snd lh mod 8 = 0) dead2 /\
    (length dead2 <= 2)%nat /\ hull_bytes dead2 <= kDeadShadowBytes.
  Proof.
    (first [ pose proof (a8_geo) as dR_13; dand15 dR_13 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof a8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
    (first [ pose proof ((sk_shr A m md p n0 AI HL NQ')) as dR_14; dand4 dR_14 as _ M512 D512 SIDE' | pose proof (sk_shr A m md p n0 AI HL NQ') as (_ & M512 & D512 & SIDE') ]).
    assert (A1 : sh h mod 8 = 0) by (apply (mod0_down _ 512 8); [exists 64; reflexivity| exact M512]).
    assert (A2 : pbeg mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M2]).
    assert (A3 : pend mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M3]).
    assert (A4 : (sh h + msz / 8) mod 8 = 0).
    { rewrite Z.add_mod by lia. rewrite A1, (mod0_down _ 512 8 ltac:(exists 64; reflexivity) D512). reflexivity. }
    unfold dead2, e1, e2, kDeadShadowBytes. split; [| split; [cbn; lia|]].
    - constructor; [| constructor; [| constructor]]; cbn [fst snd];
        (split; [destruct SIDE' as [(X1 & X2 & X3)|(X1 & X2 & X3)]; [left| right]; unfold kLowShadowBeg in *; lia| split; [lia| split; assumption]]).
    - rewrite !hull_bytes_cons. cbn [hull_bytes]. unfold hull_npages, page_size. cbn [fst snd].
      pose proof (Z_div_mod_eq_full (pg_dn (sh h)) 4096) as Q1. rewrite M1, Z.add_0_r in Q1.
      pose proof (Z_div_mod_eq_full pbeg 4096) as Q2. rewrite M2, Z.add_0_r in Q2.
      pose proof (Z_div_mod_eq_full pend 4096) as Q3. rewrite M3, Z.add_0_r in Q3.
      pose proof (Z_div_mod_eq_full (pg_up (sh h + msz / 8)) 4096) as Q4. rewrite M4, Z.add_0_r in Q4.
      set (x := sh h + msz / 8) in *. set (u := pg_up x) in *. set (dn := pg_dn (sh h)) in *.
      assert (E0 : (x - 1) / 4096 = u / 4096 - 1) by (clear - G6 G8 Q4; lia).
      assert (E1 : sh h / 4096 = dn / 4096) by (clear - G1 G3 Q1; lia).
      assert (E2 : (pbeg - 1) / 4096 = pbeg / 4096 - 1) by (clear - Q2; lia).
      rewrite E0, E1, E2.
      set (qa := dn / 4096) in *. set (qb := pbeg / 4096) in *. set (qc := pend / 4096) in *. set (qd := u / 4096) in *.
      clearbody qa qb qc qd. clear - G1 G2 G3 G5 G6 G7 G8 Q1 Q2 Q3 Q4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma off_segments_H : forall X, Permutation X H0s \/ Permutation X H1 \/ Permutation X H2 \/ Permutation X H0p -> H_off_segments rsegs (hidc X).
  Proof.
    intros X PX.
    assert (GEN : forall front, H_off_segments rsegs (hidc (front ++ REST))).
    { intros front. unfold REST. apply (H_off_segments_perm rsegs (pa_image_ivs ++ (front ++ hull_of (fixed_regions_ AL_pasan P ++ classes_regions_ sb (a_reg A) 31 ++ sec_regions_ (firstn i chunks ++ skipn (S i) chunks)) ++ a_deadsh A ++ p_extra P))).
      - rewrite (app_assoc pa_image_ivs front). rewrite (app_assoc front pa_image_ivs) || idtac.
        apply (Permutation_trans (l' := (front ++ pa_image_ivs) ++ hull_of (fixed_regions_ AL_pasan P ++ classes_regions_ sb (a_reg A) 31 ++ sec_regions_ (firstn i chunks ++ skipn (S i) chunks)) ++ a_deadsh A ++ p_extra P)).
        + rewrite <- !app_assoc. rewrite (app_assoc pa_image_ivs front), (app_assoc front pa_image_ivs). apply Permutation_app_tail. apply Permutation_app_comm.
        + rewrite <- !app_assoc. apply Permutation_refl.
      - apply pa_hull_off_segments. }
    destruct PX as [PX|[PX|[PX|PX]]]; apply (H_off_segments_perm rsegs _ X (Permutation_sym PX));
      [exact (GEN [(h, h + msz); e1; emid; e2])| exact (GEN [(h, h + msz); e1; e2])| exact (GEN [e1; e2])| exact (GEN [(h, h + msz); (sh h, sh h + msz / 8)])].
  Qed.

  (* [comment removed for export] *)
  #[using="NQ' NTH NQB HL AI md m"] Lemma hidc_H0p : hidc (pa_hull A) = hidc H0p.
  Proof. apply hidc_perm. exact hull_perm0. Qed.
  #[using="NTH"] Lemma hidc_H2 : forall D' ia', hidc (pa_hull (freeS A p i D' ia' dead2)) = hidc H2.
  Proof. intros D' ia'. symmetry. apply hidc_perm. apply hull_permF. Qed.

  (* [comment removed for export] *)
  #[using="NQ' NQB HL AI md m"] Lemma vis_H1 : forall x, in_hullb H0p x = true -> ~ (pbeg <= x < pend) -> in_hullb H1 x = true.
  Proof.
    intros x Hx NM. (first [ pose proof (a8_geo) as dR_15; dand7 dR_15 as G1 G2 G3 G4 G5 G6 _ | pose proof a8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & _) ]). unfold H0p, H1 in *. cbn [in_hullb existsb] in Hx |- *.
    set (RR := existsb (in_ivb x) REST) in *. clearbody RR. unfold e1, e2, in_ivb in *. cbn [fst snd] in *.
    destruct RR; [rewrite !Bool.orb_true_r; reflexivity|]. rewrite !Bool.orb_false_r in Hx |- *.
    rewrite !Bool.orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt in Hx |- *. clear - Hx NM G1 G2 G3 G4 G5 G6. lia.
  Qed.
  Lemma vis_H2 : forall x, in_hullb H1 x = true -> ~ (h <= x < h + msz) -> in_hullb H2 x = true.
  Proof.
    intros x Hx NM. unfold H1, H2 in *. cbn [in_hullb existsb] in Hx |- *.
    set (RR := existsb (in_ivb x) REST) in *. clearbody RR. unfold e1, e2, in_ivb in *. cbn [fst snd] in *.
    destruct RR; [rewrite !Bool.orb_true_r; reflexivity|]. rewrite !Bool.orb_false_r in Hx |- *.
    rewrite !Bool.orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt in Hx |- *. clear - Hx NM. lia.
  Qed.
  #[using="NQ' NQB HL AI md m"] Lemma vis_H1_H0p : forall x, in_hullb H1 x = true -> in_hullb H0p x = true.
  Proof.
    intros x Hx. (first [ pose proof (a8_geo) as dR_16; dand7 dR_16 as G1 G2 G3 G4 G5 G6 _ | pose proof a8_geo as (G1 & G2 & G3 & G4 & G5 & G6 & _) ]). unfold H0p, H1 in *. cbn [in_hullb existsb] in Hx |- *.
    set (RR := existsb (in_ivb x) REST) in *. clearbody RR. unfold e1, e2, in_ivb in *. cbn [fst snd] in *.
    destruct RR; [rewrite !Bool.orb_true_r; reflexivity|]. rewrite !Bool.orb_false_r in Hx |- *.
    rewrite !Bool.orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt in Hx |- *. clear - Hx G1 G2 G3 G4 G5 G6. lia.
  Qed.
  Lemma vis_H2_H1 : forall x, in_hullb H2 x = true -> in_hullb H1 x = true.
  Proof. intros x Hx. unfold H1, H2 in *. cbn [in_hullb existsb] in Hx |- *. rewrite Hx. apply Bool.orb_true_r. Qed.
End Hulls.
