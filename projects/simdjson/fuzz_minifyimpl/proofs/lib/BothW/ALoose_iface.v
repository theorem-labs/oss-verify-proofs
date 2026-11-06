(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg AProto ABase ABytes ARep ARepKit ARepFrame ALayout AHeapP ARepExt AMalloc_iface ADepot_iface
     APoisonR_iface ARepQ ARepQP ASec ASecFacts ASecFrame ASecStore F_adepot AFake_iface AFake_arep AInstance AInstanceM AInstanceF
     AMalloc AHolesD ASF_kit AFreeAll AFreeNull F_apoison_remap AU_kit ALoose ALooseInst ALooseSet ALooseLaws.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma AHL_laws' : ahole_laws (AH adepot_iface_raw AQUAR ASEC_of).
Proof. exact AHL_laws. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AI_of_L : forall FREE L RNG st LB m, AHEAP (AI_of FREE) L RNG st LB m -> AHEAP_L L RNG st LB m /\ al_tight L.
Proof. intros FREE L RNG st LB m H. rewrite AI_of_E in H. apply AHEAP_I_iff. exact H. Qed.
Lemma AI_of_of_L : forall FREE L RNG st LB m, AHEAP_L L RNG st LB m -> al_tight L -> AHEAP (AI_of FREE) L RNG st LB m.
Proof. intros FREE L RNG st LB m H T. rewrite AI_of_E. apply AHEAP_I_iff. split; assumption. Qed.
(* [comment removed for export] *)
Lemma AI_E_L : forall (AI : AMallocIface) L RNG st LB m, AHEAP AI = AHEAP_P (AH adepot_iface AQUAR ASEC_of) ->
  AHEAP AI L RNG st LB m <-> AHEAP_L L RNG st LB m /\ al_tight L.
Proof. intros AI L RNG st LB m E. rewrite E. apply AHEAP_I_iff. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem AHL_frame : forall L RNG st LB m m' (W : list ivl),
  AHEAP_L L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
  AHEAP_L L RNG st LB m'.
Proof.
  intros L RNG st LB m m' W (ALO & ARNG & [X [AR BL]] & HFK) MU WM CW. cbn [AHL ah_fake] in HFK.
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [eapply (@AREP_client _ adepot_iface_raw AHL_laws'); eauto| exact BL].
  - cbn [AHL ah_fake]. eapply (@afake_client _ adepot_iface_raw); eauto.
Qed.

Theorem AHL_frame_L : forall L RNG st LB m m' (W_L : list ivl),
  AHEAP_L L RNG st LB m -> munch W_L m m' -> wmono bsegs m m' ->
  Forall (fun iv => aclient_range aci_L LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W_L ->
  rw_cells bsegs m' 0x6b1eb8 [C4 (Z_to_bv 64 0)] ->
  AHEAP_L L RNG st LB m'.
Proof.
  intros L RNG st LB m m' W_L (ALO & ARNG & [X [AR BL]] & HFK) MU WM CW LS. cbn [AHL ah_fake] in HFK.
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [eapply (@AREP_client_L _ adepot_iface_raw AHL_laws'); eauto| exact BL].
  - cbn [AHL ah_fake]. eapply (@afake_client_L _ adepot_iface_raw); eauto.
Qed.

(* [comment removed for export] *)
Lemma AHL_frame_lsan' : forall L RNG st LB m m' (W : list ivl),
  AHEAP_L L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ iv = (0x6b1eb8, 0x6b1eb8 + 4)) W ->
  rw_cells bsegs m' 0x6b1eb8 [C4 (Z_to_bv 64 0)] ->
  AHEAP_L L RNG st LB m'.
Proof.
  intros L RNG st LB m m' W AH MU WM CW LS. eapply AHL_frame_L; [exact AH | exact MU | exact WM | | exact LS].
  eapply Forall_impl; [| exact CW]. cbn beta. intros iv [C| ->].
  - destruct C as [C|[C|C]]; [left; exact (aclient_app_range_L _ _ _ _ C)| right; left; exact C| right; right; exact (aclient_app_range_L _ _ _ _ C)].
  - left. right; left. exists LSAN_IV. split; [unfold aci_L; apply in_or_app; right; left; reflexivity| unfold LSAN_IV; cbn [fst snd]; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mmix (m m' : amem) (lo hi : Z) : amem :=
  fun a => if (lo <=? bv_unsigned a) && (bv_unsigned a <? hi) then m' a else m a.

Lemma mmix_in : forall m m' lo hi a, lo <= bv_unsigned a < hi -> mmix m m' lo hi a = m' a.
Proof. intros m m' lo hi a H. unfold mmix. destruct (Z.leb_spec lo (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) hi); cbn; try reflexivity; lia. Qed.
Lemma mmix_out : forall m m' lo hi a, ~ (lo <= bv_unsigned a < hi) -> mmix m m' lo hi a = m a.
Proof. intros m m' lo hi a H. unfold mmix. destruct (Z.leb_spec lo (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) hi); cbn; try reflexivity; lia. Qed.

Lemma wview_mmix_in : forall m m' lo hi a, lo <= bv_unsigned a < hi -> wview bsegs (mmix m m' lo hi) a = wview bsegs m' a.
Proof. intros m m' lo hi a H. unfold wview. rewrite (mmix_in _ _ _ _ _ H). reflexivity. Qed.
Lemma wview_mmix_out : forall m m' lo hi a, ~ (lo <= bv_unsigned a < hi) -> wview bsegs (mmix m m' lo hi) a = wview bsegs m a.
Proof. intros m m' lo hi a H. unfold wview. rewrite (mmix_out _ _ _ _ _ H). reflexivity. Qed.

Theorem AHL_set : forall L RNG st LB m m' p A n e (Wc : list ivl),
  AHEAP_L L RNG st LB m -> In (HB p A n) LB ->
  munch ((shad A, shad A + granules n) :: Wc) m m' -> wmono bsegs m m' ->
  Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) Wc ->
  rw_cells bsegs m' (shad A) [CB (Z.to_nat (granules n)) (live_pat e n)] ->
  AHEAP_L (set_blk L p A n e) RNG st LB m'.
Proof.
  intros L RNG st LB m m' p A n e Wc AH Hin MU WM CW NEW.
  set (m1 := mmix m m' (shad A) (shad A + granules n)).
  assert (MU1 : munch [(shad A, shad A + granules n)] m m1).
  { intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. subst m1. apply mmix_out. exact Hx. }
  assert (WM1 : wmono bsegs m m1).
  { intros x Hx. subst m1. destruct (Z_le_gt_dec (shad A) (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (shad A + granules n)) as [L2|L2]|].
    - rewrite wview_mmix_in by lia. apply WM. exact Hx.
    - rewrite wview_mmix_out by lia. exact Hx.
    - rewrite wview_mmix_out by lia. exact Hx. }
  assert (MU2 : munch Wc m1 m').
  { intros x Hx. subst m1. destruct (Z_le_gt_dec (shad A) (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (shad A + granules n)) as [L2|L2]|].
    - rewrite mmix_in by lia. reflexivity.
    - rewrite mmix_out by lia. apply MU. cbn [outside]. split; [lia| exact Hx].
    - rewrite mmix_out by lia. apply MU. cbn [outside]. split; [lia| exact Hx]. }
  assert (WM2 : wmono bsegs m1 m').
  { intros x Hx. subst m1. destruct (Z_le_gt_dec (shad A) (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (shad A + granules n)) as [L2|L2]|].
    - rewrite wview_mmix_in in Hx by lia. exact Hx.
    - rewrite wview_mmix_out in Hx by lia. apply WM. exact Hx.
    - rewrite wview_mmix_out in Hx by lia. apply WM. exact Hx. }
  assert (NEW1 : rw_cells bsegs m1 (shad A) [CB (Z.to_nat (granules n)) (live_pat e n)]).
  { pose proof (AHL_block L RNG st LB m p A n AH Hin) as (NB & BR & _).
    assert (G0 : 0 <= granules n) by (unfold granules; apply shlen_nonneg; lia).
    assert (SR : 0 <= shad A /\ shad A + granules n <= 2^64).
    { destruct BR as (B1 & _). apply ablk_lin in B1. atop_facts. unfold granules. rewrite shad_div, shlen_div. unfold ASHOFF. clear -B1 NB H. Z.div_mod_to_equations. lia. }
    destruct NEW as [[WF (B0 & B1 & BB)] (W0 & W1 & WW)]. cbn [cells_bytes cbytes cells_size csize app] in *. rewrite app_nil_r in *.
    assert (LEN : Z.of_nat (length (live_pat e n)) = granules n) by (rewrite live_pat_length by lia; lia).
    split; [split; [exact WF|]|].
    - cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (BB i Hi). unfold mrd. subst m1. rewrite mmix_in; [reflexivity|].
      rewrite wa_unsigned by lia. lia.
    - cbn [cells_size csize]. split; [exact W0|]. split; [exact W1|]. intros i Hi. rewrite Nat.add_0_r in Hi. subst m1. rewrite wview_mmix_in; [apply WW; rewrite Nat.add_0_r; exact Hi|].
      rewrite wa_unsigned by lia. lia. }
  pose proof (AHEAP_L_set1 L RNG st LB m m1 p A n e AH Hin MU1 WM1 NEW1) as AH1.
  eapply AHL_frame; [exact AH1| exact MU2| exact WM2| exact CW].
Qed.

(* [comment removed for export] *)
Theorem AHL_set_annot : forall L RNG st LB m m' p A n (bs : list byte) slo shi glo ghi,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB ->
  munch [(slo, shi); (glo, ghi)] m m' -> wmono bsegs m m' ->
  ATOP + 4096 <= slo -> shi <= 2^47 -> shad A <= glo -> ghi <= shad A + granules n ->
  rw_cells bsegs m' (shad A) [CB (Z.to_nat (granules n)) bs] ->
  AHEAP_L (set_blk L p A n (Some bs)) RNG st LB m'.
Proof.
  intros until ghi. intros AH Hin MU WM SLO SHI GLO GHI NEW.
  assert (LEN : length bs = Z.to_nat (granules n)) by (destruct NEW as [[[WF _] _] _]; cbn in WF; lia).
  eapply (AHL_set L RNG st LB m m' p A n (Some bs) [(slo, shi)]); [exact AH| exact Hin| | exact WM| |].
  - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside fst snd] in Hx |- *. clear - Hx GLO GHI. lia.
  - constructor; [| constructor]. cbn [fst snd]. unfold aclient_range, aclient_app_range. left. left. clear - SLO SHI. lia.
  - unfold live_pat. rewrite (fit_pat_exact _ _ LEN). exact NEW.
Qed.
(* [comment removed for export] *)
Theorem AHL_set_annot_tight : forall L RNG st LB m m' p A n slo shi glo ghi,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB ->
  munch [(slo, shi); (glo, ghi)] m m' -> wmono bsegs m m' ->
  ATOP + 4096 <= slo -> shi <= 2^47 -> shad A <= glo -> ghi <= shad A + granules n ->
  rw_cells bsegs m' (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  AHEAP_L (set_blk L p A n None) RNG st LB m'.
Proof.
  intros until ghi. intros AH Hin MU WM SLO SHI GLO GHI NEW.
  eapply (AHL_set L RNG st LB m m' p A n None [(slo, shi)]); [exact AH| exact Hin| | exact WM| |].
  - eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside fst snd] in Hx |- *. clear - Hx GLO GHI. lia.
  - constructor; [| constructor]. cbn [fst snd]. unfold aclient_range, aclient_app_range. left. left. clear - SLO SHI. lia.
  - cbn [live_pat]. exact NEW.
Qed.
(* [comment removed for export] *)
Corollary AHL_set_annot_restore : forall L RNG st LB m m' p A n e slo shi glo ghi,
  al_tight L ->
  AHEAP_L (set_blk L p A n e) RNG st LB m -> In (HB p A n) LB ->
  munch [(slo, shi); (glo, ghi)] m m' -> wmono bsegs m m' ->
  ATOP + 4096 <= slo -> shi <= 2^47 -> shad A <= glo -> ghi <= shad A + granules n ->
  rw_cells bsegs m' (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  AHEAP_L L RNG st LB m'.
Proof.
  intros until ghi. intros TI AH Hin MU WM SLO SHI GLO GHI NEW.
  rewrite <- (set_blk_restore L p A n e TI). eapply AHL_set_annot_tight; eassumption.
Qed.

(* [comment removed for export] *)
Lemma AHL_block_cell : forall L RNG st LB m p A n,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (granules n)) (live_pat (blk_entry L p A n) n)].
Proof. intros L RNG st LB m p A n AH Hin. pose proof (AHL_block L RNG st LB m p A n AH Hin) as (_ & _ & _ & _ & SH & _). exact SH. Qed.
Lemma AHL_block_cell_tight : forall L RNG st LB m p A n,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB -> blk_entry L p A n = None ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Proof. intros L RNG st LB m p A n AH Hin E. pose proof (AHL_block_cell L RNG st LB m p A n AH Hin) as SH. rewrite E in SH. exact SH. Qed.
Lemma AHL_block_cell_some : forall L RNG st LB m p A n bs,
  AHEAP_L L RNG st LB m -> In (HB p A n) LB -> blk_entry L p A n = Some bs -> length bs = Z.to_nat (granules n) ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (granules n)) bs].
Proof.
  intros L RNG st LB m p A n bs AH Hin E LEN. pose proof (AHL_block_cell L RNG st LB m p A n AH Hin) as SH. rewrite E in SH.
  unfold live_pat in SH. rewrite (fit_pat_exact _ _ LEN) in SH. exact SH.
Qed.
(* [comment removed for export] *)
Lemma blk_entry_set_blk_other2 : forall L p A n e q B k, q <> p -> B <> A -> blk_entry (set_blk L p A n e) q B k = blk_entry L q B k.
Proof.
  intros L p A n e q B k NP NA. unfold blk_entry, set_blk, set_pat1, set_spat1, remapL.
  destruct (is_primary n); destruct (is_primary k); cbn [al_pat al_spat]; try reflexivity.
  - apply upd_pat_ne. exact NP.
  - apply upd_spat_ne. intros E. apply NA. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem AHL_free : afree_stmt aci_I AHEAP_L.
Proof.
  exact (afree_total adepot_iface_raw AFAKE AHL_laws aci_I aci_okQ aci_ok2 ltac:(cbn [ADEPOT adepot_iface_raw]; exact adepot_frameD) afake_frameD).
Qed.
Theorem AHL_free_null : afree_null_stmt aci_I AHEAP_L.
Proof. exact (afree_nullP adepot_iface_raw ASEC_of AFAKE AHL_laws aci_I aci_okQ). Qed.

(* [comment removed for export] *)
Theorem AHL_malloc : amalloc_stmtG aci_I AHEAP_L.
Proof. exact (amalloc_all adepot_iface_raw AQUAR AFAKE AHL_laws poison_remap_proof aci_I aci_ok aci_ok2). Qed.

(* [comment removed for export] *)
Definition lpat_okB (L : alayout) (LB : list ablock) : Prop :=
     (forall q, al_pat L q <> None -> exists A n, In (HB q A n) LB /\ is_primary n = true)
  /\ (forall mb, al_spat L mb <> None -> exists q n, In (HB q (mb + SEC_UOFF) n) LB /\ is_primary n = false).

Lemma lpat_okB_tight : forall L LB, al_tight L -> lpat_okB L LB.
Proof. intros L LB [H1 H2]. split; [intros q NE; rewrite H1 in NE| intros mb NE; rewrite H2 in NE]; exfalso; apply NE; reflexivity. Qed.
Lemma lpat_okB_mono : forall L LB LB', lpat_okB L LB -> (forall b, In b LB -> In b LB') -> lpat_okB L LB'.
Proof.
  intros L LB LB' [H1 H2] SUB. split.
  - intros q NE. destruct (H1 q NE) as (A & n & Hin & P). exists A, n. split; [apply SUB; exact Hin| exact P].
  - intros mb NE. destruct (H2 mb NE) as (q & n & Hin & P). exists q, n. split; [apply SUB; exact Hin| exact P].
Qed.
Lemma lpat_okB_perm : forall L LB LB', Permutation LB LB' -> lpat_okB L LB -> lpat_okB L LB'.
Proof. intros L LB LB' P H. eapply lpat_okB_mono; [exact H|]. intros b Hb. eapply Permutation_in; [exact P| exact Hb]. Qed.
Lemma lpat_okB_set_blk : forall L LB p A n e, lpat_okB L LB -> In (HB p A n) LB -> lpat_okB (set_blk L p A n e) LB.
Proof.
  intros L LB p A n e [H1 H2] Hin. rewrite set_blk_remapL. split; cbn [al_pat al_spat remapL].
  - intros q NE. destruct (is_primary n) eqn:P; [| exact (H1 q NE)].
    unfold upd_pat in NE. destruct (N.eqb_spec q p) as [->|]; [exists A, n; split; [exact Hin| exact P]| exact (H1 q NE)].
  - intros mb NE. destruct (is_primary n) eqn:P; [exact (H2 mb NE)|].
    unfold upd_spat in NE. destruct (Z.eqb_spec mb (A - SEC_UOFF)) as [->|]; [| exact (H2 mb NE)].
    exists p, n. replace (A - SEC_UOFF + SEC_UOFF) with A by lia. split; [exact Hin| exact P].
Qed.
(* [comment removed for export] *)
Lemma In_hb_ids : forall LB p A n, In (HB p A n) LB -> In p (hb_ids LB).
Proof. intros LB p A n H. unfold hb_ids. apply in_flat_map. exists (HB p A n). split; [exact H| left; reflexivity]. Qed.
Lemma hb_ids_inj : forall LB p A n A' n', List.NoDup (hb_ids LB) -> In (HB p A n) LB -> In (HB p A' n') LB -> HB p A n = HB p A' n'.
Proof.
  induction LB as [|b LB IH]; intros p A n A' n' ND H1 H2; [destruct H1|].
  destruct b as [[q|c] B k]; cbn in ND.
  - inversion ND as [|q' l' NI ND']; subst. destruct H1 as [E1|H1], H2 as [E2|H2].
    + rewrite <- E1, <- E2. reflexivity.
    + exfalso. injection E1 as -> _ _. apply NI. exact (In_hb_ids _ _ _ _ H2).
    + exfalso. injection E2 as -> _ _. apply NI. exact (In_hb_ids _ _ _ _ H1).
    + exact (IH p A n A' n' ND' H1 H2).
  - destruct H1 as [E1|H1]; [discriminate|]. destruct H2 as [E2|H2]; [discriminate|]. exact (IH p A n A' n' ND H1 H2).
Qed.
(* [comment removed for export] *)
Lemma lpat_okB_remove : forall L LB p A n, lpat_okB L LB -> In (HB p A n) LB -> List.NoDup (hb_ids LB) -> blk_entry L p A n = None ->
  lpat_okB L (lb_remove p LB).
Proof.
  intros L LB p A n [H1 H2] Hin ND BE. unfold blk_entry in BE. split.
  - intros q NE. destruct (H1 q NE) as (A' & n' & Hin' & P'). exists A', n'. split; [| exact P'].
    apply (proj2 (AFreeRep.In_lb_remove p LB _)). split; [exact Hin'|]. cbn [ab_kind]. intros EQ. injection EQ as ->.
    pose proof (hb_ids_inj LB p A n A' n' ND Hin Hin') as E. injection E as <- <-. rewrite P' in BE. exact (NE BE).
  - intros mb NE. destruct (H2 mb NE) as (q & n' & Hin' & P'). exists q, n'. split; [| exact P'].
    apply (proj2 (AFreeRep.In_lb_remove p LB _)). split; [exact Hin'|]. cbn [ab_kind]. intros EQ. injection EQ as ->.
    pose proof (hb_ids_inj LB p A n _ n' ND Hin Hin') as E. injection E as EA <-. rewrite P', EA in BE.
    replace (mb + SEC_UOFF - SEC_UOFF) with mb in BE by lia. exact (NE BE).
Qed.

Theorem AHL_pat_malloc_ok : forall L RNG st LB m, AHEAP_L L RNG st LB m -> lpat_okB L LB -> pat_malloc_ok L st.
Proof.
  intros L RNG st LB m AH [H1 H2]. pose proof AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as (WF & _). pose proof WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & LIVE & FRESH & _).
  split.
  - destruct (al_pat L (a_next st)) eqn:E; [| reflexivity]. exfalso.
    destruct (H1 (a_next st) ltac:(rewrite E; discriminate)) as (A & n & Hin & _).
    destruct (hb_casesH AHL L st X LB m _ A n ALO AR BL Hin) as [(b & Hb & Sb & _)|(mb & ms & Lp & _)].
    + destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & LV). exact (N.lt_irrefl _ (FRESH _ _ LV)).
    + exact (N.lt_irrefl _ (FRESH _ _ Lp)).
  - intros mb NE. destruct (H2 mb NE) as (q & n & Hin & NP).
    destruct (hb_casesH AHL L st X LB m q _ n ALO AR BL Hin) as [(b & _ & _ & _ & _ & P)|(mb' & ms & Lp & EA & _)]; [rewrite NP in P; discriminate|].
    exists q, ms, n. replace mb with mb' by lia. exact Lp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem AHL_fake_flag : forall L RNG st LB m cls F N,
  AHEAP_L L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges aci_I (fflag L cls F).
Proof. exact (fake_flag_P adepot_iface_raw AQUAR ASEC_of aci_I aci_ok1). Qed.
Theorem AHL_fake_release : forall L RNG st LB m cls F N,
  AHEAP_L L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP_L L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof. exact (fake_release_P adepot_iface_raw AQUAR ASEC_of AHL_laws'). Qed.
Lemma set_blk_fflag : forall L p A n e cls F, fflag (set_blk L p A n e) cls F = fflag L cls F.
Proof. intros. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_afake_rng : forall L p A n e RNG, afake_rng (set_blk L p A n e) RNG = afake_rng L RNG.
Proof. intros. rewrite set_blk_remapL. reflexivity. Qed.
Lemma set_blk_AFAKE : forall L p A n e LB m, AFAKE (set_blk L p A n e) LB m = AFAKE L LB m.
Proof. intros. rewrite set_blk_remapL. reflexivity. Qed.
(* [comment removed for export] *)
Lemma set_blk_aps_ok : forall L p A n e s, aps_ok (set_blk L p A n e) s <-> aps_ok L s.
Proof. intros. unfold aps_ok. rewrite set_blk_aresv_ok. tauto. Qed.
End CANSEC1.
