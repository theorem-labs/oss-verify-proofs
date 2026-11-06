(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import RelSpec RelSpecMremap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv Realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep KInit KOwn PgArith ProgR.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import MallocInv MI_Inv MI_Kit MI_WFree MI_WFree2 MI_Contracts MI_Ledger MI_Realloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocTree A_MallocBlocks A_Realloc A_Realloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require MI_Geom.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require A_MallocFacts_inv2.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma rf_In l a n b k : ranges_free l a n = true -> In (b, k) l -> a + n <= b \/ b + k <= a.
Proof.
  intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
  unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.
Lemma rf_intro l a n : (forall b k, In (b, k) l -> a + n <= b \/ b + k <= a) -> ranges_free l a n = true.
Proof.
  intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
  unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.
Lemma rf_sub l a n a' n' : ranges_free l a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> ranges_free l a' n' = true.
Proof. intros H H1 H2 H3. apply rf_intro. intros b k HI. pose proof (rf_In l a n b k H HI). lia. Qed.

Lemma page_round_up_Z_id x : x mod 4096 = 0 -> page_round_up_Z x = x.
Proof. intros H. rewrite <- round_up_pg_eq. apply round_up_pg_aligned. exact H. Qed.

Lemma page_align_is0_false x : 0 < x -> x mod 4096 = 0 -> x < 2^63 -> page_align_is0_b (Z_to_bv 64 x) = false.
Proof.
  intros H0 Hal Hhi. unfold page_align_is0_b. rewrite w_is0_lit by lia. rewrite unsigned_lit by lia. rewrite page_round_up_Z_id by exact Hal.
  rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbn [orb]. apply Z.leb_gt. unfold two_pow_64. lia.
Qed.

Lemma bv_add_lit a b : 0 <= a -> 0 <= b -> a + b < 2^64 -> (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
  intros Ha Hb Hab. apply bv_eq. rewrite bv_add_unsigned, !unsigned_lit by lia. apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Lemma m_vmmaps_mremap_model_next mo old old_n dst new_n :
  m_vmmaps (mremap_model_next mo old old_n dst new_n) = mremap_maps_next (m_vmmaps mo) old dst new_n.
Proof. unfold mremap_model_next, vm_resize_backing. cbv zeta. destruct (mremap_source_lazy_b _ _ _); reflexivity. Qed.

Definition kcov (maps : list (word * word)) (bl : Z * Z) : Prop :=
  0 < snd bl /\ forall x, fst bl <= x < fst bl + snd bl -> exists e, In e maps /\ elo e <= x < ehi e.

Lemma ranges_free_of_region_free maps a n l :
  region_free maps (Z_to_bv 64 a) (Z_to_bv 64 n) = true -> 0 <= a -> 0 < n -> a + n < 2^64 ->
  Forall (kcov maps) l -> ranges_free l a n = true.
Proof.
  intros RF Ha Hn Han HC. apply rf_intro. intros b k Hin.
  destruct (proj1 (Forall_forall _ _) HC _ Hin) as [Hk Hc]. cbn [fst snd] in Hk, Hc.
  destruct (Z_lt_le_dec b (a + n)) as [L1|]; [| left; lia]. destruct (Z_lt_le_dec a (b + k)) as [L2|]; [| right; lia]. exfalso.
  destruct (Hc (Z.max a b) ltac:(lia)) as (e & He & Hx).
  pose proof (region_free_disj _ _ _ _ RF He) as D. rewrite !unsigned_lit in D by lia. lia.
Qed.

Lemma kcov_mono maps maps' bl : kcov maps bl -> (forall e, In e maps -> In e maps') -> kcov maps' bl.
Proof. intros [Hk Hc] Hm. split; [exact Hk|]. intros x Hx. destruct (Hc x Hx) as (e & He & R). exists e. auto. Qed.

Section DEC.
Variables (oldb oldl needed : Z) (avoidx avoid : list (Z * Z)) (mo : Model).
Let h := m_vmmaps mo.
Let OLD := Z_to_bv 64 oldb.
Let OLDN := Z_to_bv 64 oldl.
Let NEWN := Z_to_bv 64 needed.
Hypotheses (B0 : 0 < oldb) (BA : oldb mod 4096 = 0) (L0 : 0 < oldl) (LA : oldl mod 4096 = 0) (N0 : 0 < needed) (NA : needed mod 4096 = 0)
           (NE : oldl <> needed) (BC : oldb + oldl <= alloc_ceiling) (NC : needed < 2^62)
           (SRC : mremap_source_b h OLD OLDN oldl = true) (BK : mremap_backing_uniform_b mo OLD OLDN = true)
           (CK : ceil_ok h)
           (AVX : Forall (kcov (vm_reserved h ++ map_remove (vm_maps h) OLD)) avoidx)
           (AV : Forall (kcov (vm_reserved h ++ vm_maps h)) avoid).

Lemma dec_nsafe : nsafe (NMremap oldb oldl needed) mo.
Proof.
  pose proof alloc_ceiling_lt as CL.
  unfold nsafe. cbv zeta. fold h OLD. rewrite (unsigned_lit oldl) by lia. rewrite page_round_up_Z_id by exact LA. fold OLDN.
  split; [subst OLD; rewrite unsigned_lit by lia; rewrite page_size_eq; exact BA|].
  split; [apply page_align_is0_false; lia|]. split; [apply page_align_is0_false; lia|]. split; [exact SRC| exact BK].
Qed.

Lemma nstep_dec_mremap : forall rsp mo' evs,
  nstep (NMremap oldb oldl needed) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mremap avoidx avoid oldb oldl needed rsp = Some x /\
  match x with
  | RmErr e => e = ENOMEM /\ mo' = mo
  | RmSame => m_vmmaps mo' = mremap_maps_next h OLD OLD NEWN
      /\ (needed < oldl \/ (oldl < needed /\ oldb + needed <= alloc_ceiling
                            /\ region_free (vm_reserved h ++ map_remove (vm_maps h) OLD) OLD NEWN = true
                            /\ ranges_free avoidx (oldb + oldl) (needed - oldl) = true))
  | RmAt nb => nb <> oldb /\ nb mod 4096 = 0 /\ 0 < nb /\ nb + needed <= alloc_ceiling
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 nb) NEWN = true /\ oldl < needed
      /\ m_vmmaps mo' = mremap_maps_next h OLD (Z_to_bv 64 nb) NEWN /\ ranges_free avoid nb needed = true
  end.
Proof.
  intros rsp mo' evs H. pose proof alloc_ceiling_lt as CL.
  pose proof dec_nsafe as NS. unfold nsafe in NS. cbv zeta in NS. fold h OLD in NS. destruct NS as (S1 & S2 & S3 & S4 & S5).
  apply (nstep_mremap_inv oldb oldl needed mo rsp mo' evs S1 S2 S3 S4 S5) in H as [-> [OUT _]]. split; [reflexivity|].
  unfold mremap_out in OUT. cbv zeta in OUT. fold h OLD in OUT.
  rewrite (unsigned_lit oldl), (unsigned_lit needed) in OUT by lia. rewrite !page_round_up_Z_id in OUT by assumption. fold OLDN NEWN in OUT.
  assert (UO : bv_unsigned OLD = oldb) by (subst OLD; apply unsigned_lit; lia).
  destruct OUT as [[E _]|[_ [(e & He & E)|[[LT E]|[(LT & G & E)|(LT & dst & FR & E)]]]]]; [exfalso; exact (NE E)| | | |];
    apply Ok_inj in E as (-> & -> & _).
  -   cbn in He. destruct He as [<-|[]]. split; [vm_only_done|]. exists (RmErr ENOMEM). split; [| auto].
    unfold dec_mremap. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  -   split; [vm_only_done|]. exists RmSame. split; [| split; [apply m_vmmaps_mremap_model_next| left; exact LT]].
    unfold dec_mremap, mremap_inplace_effect. rewrite (proj2 (Z.ltb_lt _ _) LT). cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    rewrite errno_of_small by (rewrite UO; lia). rewrite UO, Z.eqb_refl. rewrite ?(proj2 (Z.ltb_lt _ _) LT).
    replace (OLD + NEWN)%bv with (wa (oldb + needed)) by (unfold wa; subst OLD NEWN; symmetry; apply bv_add_lit; lia).
    cbn [listNN_eqb]. rewrite !bv_eqb_refl. reflexivity.
  -   split; [vm_only_done|]. exists RmSame.
    unfold mremap_inplace_grow_b in G. fold h in G. apply andb_prop in G as [G BUD]. apply andb_prop in G as [CE RF].
    apply Z.leb_le in CE. rewrite UO in CE.
    assert (CE' : oldb + needed <= alloc_ceiling).
    { apply (ceil_page_le h); [exact CK| rewrite page_size_eq, Z.add_mod, BA, NA by lia; reflexivity| exact CE]. }
    assert (RFX : ranges_free avoidx (oldb + oldl) (needed - oldl) = true).
    { rewrite (rf_sub avoidx oldb needed (oldb + oldl) (needed - oldl)); [reflexivity| | lia| lia| lia].
      apply (ranges_free_of_region_free (vm_reserved h ++ map_remove (vm_maps h) OLD)); [exact RF| lia| lia| lia| exact AVX]. }
    split; [| split; [apply m_vmmaps_mremap_model_next| right; split; [exact LT|]; split; [exact CE'|]; split; [exact RF| exact RFX]]].
    unfold dec_mremap, mremap_inplace_effect. rewrite (proj2 (Z.ltb_ge needed oldl) ltac:(lia)). cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    rewrite errno_of_small by (rewrite UO; lia). rewrite UO, Z.eqb_refl. rewrite ?(proj2 (Z.ltb_ge needed oldl) ltac:(lia)).
    unfold mremap_tail, remap_tail_zs. rewrite (proj2 (Z.ltb_lt _ _) LT).
    replace (OLD + OLDN)%bv with (wa (oldb + oldl)) by (unfold wa; subst OLD OLDN; symmetry; apply bv_add_lit; lia).
    cbn [listNN_eqb]. rewrite !bv_eqb_refl. cbn [andb]. rewrite (proj2 (Z.leb_le _ _) CE'). cbn [andb].
    rewrite RFX. reflexivity.
  -   split; [vm_only_done|].
    unfold mremap_fresh_b in FR. fold h in FR. repeat (apply andb_prop in FR as [FR ?X]).
    rename X into BUD. rename X0 into RF. rename X1 into CE. rename X2 into D0. rename X3 into DA.
    apply Z.leb_le in CE. apply Z.ltb_lt in D0. apply Z.eqb_eq in DA. rewrite page_size_eq in DA.
    assert (CE' : bv_unsigned dst + needed <= alloc_ceiling).
    { apply (ceil_page_le h); [exact CK| rewrite page_size_eq, Z.add_mod, DA, NA by lia; reflexivity| exact CE]. }
    assert (NEQ : bv_unsigned dst <> oldb).
    { intros E. assert (ED : dst = OLD) by (apply bv_eq; rewrite E, UO; reflexivity). rewrite ED, bv_eqb_refl in FR. discriminate. }
    assert (RFA : ranges_free avoid (bv_unsigned dst) needed = true).
    { apply (ranges_free_of_region_free (vm_reserved h ++ vm_maps h)); [rewrite Z_to_bv_bv_unsigned; exact RF| lia| lia| clear - CE' CL; lia| exact AV]. }
    exists (RmAt (bv_unsigned dst)). split.
    + unfold dec_mremap, mremap_move_effect. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
      rewrite errno_of_small by (clear - CE' CL N0; lia). rewrite (proj2 (Z.eqb_neq _ _) NEQ).
      unfold mremap_tail, remap_tail_zs. rewrite (proj2 (Z.ltb_lt _ _) LT).
      replace (dst + OLDN)%bv with (wa (bv_unsigned dst + oldl))
        by (unfold wa; subst OLDN; apply bv_eq; rewrite bv_add_unsigned, !unsigned_lit by lia; symmetry; apply bv_wrap_small; unfold bv_modulus; lia).
      change (wa oldb) with OLD. rewrite ?Z_to_bv_bv_unsigned. fold OLDN. cbn [listNN_eqb]. rewrite !bv_eqb_refl. cbn [andb].
      rewrite (proj2 (Z.eqb_eq _ _) DA), (proj2 (Z.ltb_lt _ _) D0), (proj2 (Z.leb_le _ _) CE'). cbn [andb].
      rewrite RFA. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact NEQ|]. split; [exact DA|]. split; [exact D0|]. split; [exact CE'|]. split; [exact RF|]. split; [exact LT|].
      split; [apply m_vmmaps_mremap_model_next| exact RFA].
Qed.
End DEC.

Lemma region_free_of_disj maps a n :
  (forall e, In e maps -> bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a) ->
  region_free maps a n = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). rewrite andb_true_r.
  specialize (H (e, sz) (or_introl eq_refl)). unfold elo, ehi in H. cbn [fst snd] in H.
  unfold iv_overlap. apply Bool.negb_true_iff. apply Bool.andb_false_iff.
  destruct H as [H|H]; [right| left]; apply Z.ltb_ge; lia.
Qed.

Lemma In_map_remove e maps w : In e maps -> fst e <> w -> In e (map_remove maps w).
Proof.
  intros Hin Hne. unfold map_remove. apply filter_In. split; [exact Hin|].
  destruct (bv_eqb (fst e) w) eqn:E; [| reflexivity]. apply bv_eqb_eq in E. contradiction.
Qed.
Lemma In_map_remove_inv e maps w : In e (map_remove maps w) -> In e maps /\ fst e <> w.
Proof.
  intros H. unfold map_remove in H. apply filter_In in H as [H1 H2]. split; [exact H1|].
  intros E. rewrite E, bv_eqb_refl in H2. discriminate.
Qed.

Section REMAPKL.
Variables (L : mled) (pbrk : Z) (mo mo' : Model) (oldb l0 needed nb : Z).
Let h := m_vmmaps mo.
Let oldl := mmap_len l0.
Let OLD := Z_to_bv 64 oldb.
Let NB := Z_to_bv 64 nb.
Let NEWN := Z_to_bv 64 needed.
Let L' := set_groups ((nb, needed) :: g_remove oldb (ld_groups L)) L.
Hypotheses (HK : KL L pbrk mo) (Hq : brk_quiet L) (Hin : In (oldb, l0) (ld_groups L))
  (N0 : 0 < needed) (NA : needed mod 4096 = 0) (NMAX : needed < LEN_MAX) (NB0 : 0 < nb) (NBA : nb mod 4096 = 0) (NCEIL : nb + needed <= alloc_ceiling)
  (D : forall e, In e (vm_reserved h ++ map_remove (vm_maps h) OLD) -> nb + needed <= elo e \/ ehi e <= nb)
  (BD : brk_disj L nb needed)
  (Evm : m_vmmaps mo' = mremap_maps_next h OLD NB NEWN) (Hmi : minv mo') (Hh : m_halted mo' = None).

Lemma mmap_len_needed : mmap_len needed = needed.
Proof. unfold mmap_len. apply page_round_up_Z_id. exact NA. Qed.

Theorem KL_remap : KL L' pbrk mo'.
Proof.
  pose proof alloc_ceiling_lt as CL. pose proof mmap_len_needed as MLN.
  pose proof (kl_groups _ _ _ HK oldb l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (went_In_bounds _ _ _ oldb l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6). fold oldl in B2, B5, B6, A4, A5, A6.
  assert (UO : bv_unsigned OLD = oldb) by (subst OLD; apply unsigned_lit; lia).
  assert (UN : bv_unsigned NB = nb) by (subst NB; apply unsigned_lit; lia).
  assert (UNN : bv_unsigned NEWN = needed) by (subst NEWN; apply unsigned_lit; lia).
  assert (EOLD : went oldb oldl = (OLD, Z_to_bv 64 oldl)) by reflexivity.
  assert (ENEW : went nb (mmap_len needed) = (NB, NEWN)) by (rewrite MLN; reflexivity).
  pose proof (kl_distinct _ _ _ HK) as Kd.

  assert (KEEP : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> oldb ->
                 In (went b (mmap_len l)) (map_remove (vm_maps h) OLD)).
  { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
    apply In_map_remove; [exact C4|]. cbn [fst went]. intros E. apply Hne. apply (f_equal bv_unsigned) in E. rewrite unsigned_wz, UO in E by lia. exact E. }
  destruct (g_remove_split oldb l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
  pose proof Kd as Kd0. rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
  pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
  assert (Hg' : forall b l, In (b, l) (g_remove oldb (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> oldb).
  { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
    intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (oldb, l). split; [reflexivity| exact H]. }
  assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> oldb).
  { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (oldb, l, k). split; [reflexivity| exact H]. }

  assert (Dk : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> oldb ->
               nb + needed <= b \/ b + mmap_len l <= nb).
  { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
    specialize (D (went b (mmap_len l)) ltac:(apply in_or_app; right; exact (KEEP b l H Hne))). rewrite C5, C6 in D. exact D. }
  assert (RFnew : region_free (map_remove (vm_maps h) OLD) NB NEWN = true).
  { apply region_free_of_disj. intros e He. rewrite UN, UNN. apply D. apply in_or_app. right. exact He. }
  pose proof (kl_wf _ _ _ HK) as [KW KP].
  assert (Hph' : phase_inv (ld_brk L') L' pbrk mo').
  { eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]. }
  subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [mremap_maps_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
  -   apply vmwf_cons; [| rewrite UN, UNN; lia| exact RFnew].
    split; [intros e He; apply KW; exact (proj1 (In_map_remove_inv _ _ _ He))| apply pwdisj_filter; exact KP].
  -   intros b l [E|Hb].
    + injection E as <- <-. rewrite MLN. rewrite MLN in ENEW. rewrite ENEW. splits; try lia; [unfold PGSZ; exact NBA| left; reflexivity| exact BD].
    + destruct (Hg' b l Hb) as [Hb1 Hne]. specialize (Kgr b l Hb1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
      right. exact (KEEP b l (or_introl Hb1) Hne).
  -   intros b l k Hb. pose proof (Hm' b l k Hb) as Hne. specialize (Kme b l k Hb). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
    right. exact (KEEP b l (or_intror (ex_intro _ k Hb)) Hne).
  -   cbn [map fst app]. constructor.
    + intros HinN. apply in_app_or in HinN as [HinN|HinN].
      * apply in_map_iff in HinN as ([b l] & Eb & Hb). cbn in Eb. subst b. destruct (Hg' nb l Hb) as [Hb1 Hne].
        pose proof (Dk nb l (or_introl Hb1) Hne) as X. pose proof (kl_groups _ _ _ (mkKL _ _ _ Kminv Khalt (conj KW KP) Kwfna Kresv Krt Kstart Kgr Kme Kd0 Kreg Kph Knoacc Kceil) nb l Hb1) as (Y & _).
        pose proof (mmap_len_ge l ltac:(lia)). lia.
      * apply in_map_iff in HinN as ([[b l] k] & Eb & Hb). cbn in Eb. subst b.
        pose proof (Dk nb l (or_intror (ex_intro _ k Hb)) (Hm' _ _ _ Hb)) as X. pose proof (kl_metas _ _ _ (mkKL _ _ _ Kminv Khalt (conj KW KP) Kwfna Kresv Krt Kstart Kgr Kme Kd0 Kreg Kph Knoacc Kceil) nb l k Hb) as (Y & _).
        pose proof (mmap_len_ge l ltac:(lia)). lia.
    + rewrite Ezz, map_app, <- app_assoc. exact Kd1.
  -   intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
    intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [| exact Hr]. right. apply In_map_remove; [exact He|].
    intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
    destruct (pwdisj_In _ _ _ KP He A5) as [->|DJ].
    + rewrite B5, B6 in Hr. clear - Hr A6 Hz R3. unfold PGSZ in *. lia.
    + pose proof (KW e He) as W. unfold edisj, elo, ehi in DJ, W. rewrite Efst in DJ, W. cbn [fst snd went] in DJ. unfold wz in DJ. fold OLD in DJ. rewrite UO in DJ, W.
      rewrite ?unsigned_lit in DJ by lia. clear - DJ W B2 A4 CL. lia.
  -   intros e He. destruct (Knoacc e He) as (e' & H1 & H2 & H3 & H4). exists e'.
    assert (Hne : fst e' <> OLD).
    { intros Efst. destruct (pwdisj_In _ _ _ KP H1 A5) as [EQ|DJ]; [exact (H4 oldb l0 Hin EQ)|].
      pose proof (KW e' H1) as W. unfold edisj, elo, ehi in DJ, W. rewrite Efst in DJ, W. cbn [fst snd went] in DJ. unfold wz in DJ. fold OLD in DJ. rewrite UO in DJ, W.
      rewrite ?unsigned_lit in DJ by lia. clear - DJ W B2 A4 CL. lia. }
    split; [right; apply In_map_remove; [exact H1| exact Hne]|]. split; [exact H2|]. split; [exact H3|].
    intros b l [E|Hb].
    + injection E as <- <-. rewrite ENEW. intros E'. pose proof (D e' ltac:(apply in_or_app; right; apply In_map_remove; [exact H1| exact Hne])) as X.
      pose proof (KW e' H1) as W. subst e'. unfold elo, ehi in X, W. cbn [fst snd] in X, W. rewrite UN, UNN in X, W. lia.
    + exact (H4 b l (proj1 (Hg' b l Hb))).
Qed.
End REMAPKL.

Lemma inv_R_transplant X st1 st2 L : strip st1 = strip st2 -> inv_R X st1 L -> inv_R X st2 L.
Proof.
  intros E IR.
  assert (ER : s_regions st2 = s_regions st1) by (rewrite <- (s_regions_strip st2), <- E; reflexivity).
  assert (EC : s_ctx st2 = s_ctx st1) by (rewrite <- (s_ctx_strip st2), <- E; reflexivity).
  assert (EN : s_next_rid st2 = s_next_rid st1) by (change (s_next_rid st2) with (s_next_rid (strip st2)); rewrite <- E; reflexivity).
  assert (EV : s_reserved st2 = s_reserved st1) by (change (s_reserved st2) with (s_reserved (strip st2)); rewrite <- E; reflexivity).
  assert (EG : s_groups st2 = s_groups st1) by (change (s_groups st2) with (s_groups (strip st2)); rewrite <- E; reflexivity).
  assert (EF : forall rid r, frontier st2 rid r = frontier st1 rid r) by (intros; unfold frontier; rewrite EC; reflexivity).
  destruct IR. constructor; unfold ctx in *; rewrite ?ER, ?EC, ?EN, ?EV, ?EG; auto.
  - eapply Permutation_trans; [exact ir_metas|].
    erewrite map_ext; [apply Permutation_refl|]. intros [q rq]. cbn [fst snd]. rewrite EF. reflexivity.
  - intros rid r Hr Hk. rewrite EF. apply ir_metalen; [exact Hr| exact Hk].
  - intros rid r Hr Hk. rewrite EF. apply ir_brkfront; [exact Hr| exact Hk].
Qed.

Lemma INVL_transplant X stK stR L LR BLK BLR LSK LSR :
  strip stK = strip stR -> INVL X stK L BLK LSK -> INVL X stR LR BLR LSR -> INVL X stR L BLR LSR.
Proof.
  intros E (IR & _) (_ & REST). split; [exact (inv_R_transplant X stK stR L E IR)| exact REST].
Qed.

Lemma sim_slots stK stR L LR BLK BLR LSK LSR :
  strip stK = strip stR -> INVL x0 stK L BLK LSK -> INVL x0 stR LR BLR LSR ->
  forall c, In c (map bslot BLK) -> In c (map bslot BLR).
Proof.
  intros E INVK INVR c Hc.
  assert (EG : s_groups stR = s_groups stK) by (change (s_groups stR) with (s_groups (strip stR)); rewrite <- E; reflexivity).
  assert (EM : forall m, MR stR m = MR stK m) by (intros m; unfold MR, get_meta_rec; change (s_metas stR) with (s_metas (strip stR)); rewrite <- E; reflexivity).
  pose proof INVK as (_ & _ & _ & _ & _ & ISK & _). pose proof INVR as (_ & _ & _ & _ & _ & ISR & _).
  pose proof Hc as Hc0. apply in_map_iff in Hc as (k & Ek & Hk).
  destruct (is_blocks _ _ _ ISK k Hk) as (m & i & Hs & _). rewrite Ek in Hs.
  destruct (is_valid _ _ _ ISK _ _ _ Hs) as ((b & ai & Hb) & Hi & Es).
  pose proof (is_part _ _ _ ISK b m ai i Hb Hi) as PK. cbv zeta in PK. rewrite <- Es in PK.
  assert (Hb' : s_groups stR !! b = Some (mkGhdr (Some m) ai)) by (rewrite EG; exact Hb).
  pose proof (is_part _ _ _ ISR b m ai i Hb' ltac:(rewrite EM; exact Hi)) as PR. cbv zeta in PR. rewrite !EM, <- Es, EG in PR.
  unfold one5 in PK, PR. cbn [x_pend x0] in PK, PR.
  destruct PK as (_ & _ & NAC & _ & _ & NBC & _ & _ & NCD & _ & _).
  destruct PR as (ALT & _).
  destruct ALT as [A|[B|[C|[D|E']]]]; [exfalso; apply NAC; split; [exact A| exact Hc0]| exfalso; apply NBC; split; [exact B| exact Hc0]| exact C| exfalso; apply NCD; split; [exact Hc0| exact D]| discriminate].
Qed.

Lemma regions_groups_perm (regs : gmap N region) rid r0 r' :
  let f := fun kr : N * region => (r_base (snd kr), r_len (snd kr)) in
  let isg := fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end in
  regs !! rid = Some r0 -> r_kind r0 = RKGroup -> r_kind r' = RKGroup ->
  exists REST, Permutation (map f (List.filter isg (map_to_list regs))) ((r_base r0, r_len r0) :: REST)
          /\ Permutation (map f (List.filter isg (map_to_list (<[rid:=r']> regs)))) ((r_base r', r_len r') :: REST).
Proof.
  intros f isg H0 K0 K'. exists (map f (List.filter isg (map_to_list (delete rid regs)))). split.
  - eapply Permutation_trans; [apply Permutation_map; apply perm_filter; symmetry; apply map_to_list_delete; exact H0|].
    cbn [List.filter]. unfold isg at 1. cbn [snd]. rewrite K0. cbn [map]. apply Permutation_refl.
  - eapply Permutation_trans; [apply Permutation_map; apply perm_filter; rewrite <- (insert_delete_eq regs rid r'); apply map_to_list_insert; apply lookup_delete_eq|].
    cbn [List.filter]. unfold isg at 1. cbn [snd]. rewrite K'. cbn [map]. apply Permutation_refl.
Qed.

Lemma g_remove_perm gs M a l0 l1 REST :
  List.NoDup (map fst gs ++ M) -> In (a, l0) gs -> Permutation gs ((a, l1) :: REST) -> l1 = l0 /\ Permutation (g_remove a gs) REST.
Proof.
  intros ND Hin P. destruct (g_remove_split a l0 gs M Hin ND) as (g1 & g2 & Eg & Er). rewrite Er. rewrite Eg in P, ND.
  assert (E1 : l1 = l0).
  { assert (Hin1 : In (a, l1) (g1 ++ (a, l0) :: g2)) by (eapply Permutation_in; [symmetry; exact P| left; reflexivity]).
    pose proof (List.NoDup_app_remove_r _ _ ND) as ND1. rewrite map_app in ND1. cbn [map fst] in ND1.
    apply in_app_or in Hin1 as [X|[X|X]]; [| injection X as E; symmetry; exact E|].
    - exfalso. apply List.NoDup_remove_1 in ND1 as ND2. pose proof (List.NoDup_remove_2 _ _ _ ND1) as NI. apply NI. apply in_or_app. left. apply in_map_iff. exists (a, l1). auto.
    - exfalso. pose proof (List.NoDup_remove_2 _ _ _ ND1) as NI. apply NI. apply in_or_app. right. apply in_map_iff. exists (a, l1). auto. }
  subst l1. split; [reflexivity|]. apply (Permutation_cons_inv (a := (a, l0))). eapply Permutation_trans; [| exact P]. apply Permutation_middle.
Qed.

Lemma KL_groups_perm L gl gl' pbrk mo : Permutation gl gl' -> KL (set_groups gl L) pbrk mo -> KL (set_groups gl' L) pbrk mo.
Proof.
  intros P HK. assert (SUB : forall x, In x gl' -> In x gl) by (intros x Hx; eapply Permutation_in; [symmetry; exact P| exact Hx]).
  kl_open HK. constructor; cbn [set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live] in *; auto.
  - eapply Permutation_NoDup; [| exact Kdis]. apply Permutation_app; [apply Permutation_map; exact P| apply Permutation_refl].
  - destruct (ld_brk L); try exact Kph. destruct Kph as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [| exact P8].
    intros b l Hb. exact (P7 b l (SUB _ Hb)).
  - intros e He. destruct (Knoacc e He) as (e' & H1 & H2 & H3 & H4). exists e'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros b l Hb. exact (H4 b l (SUB _ Hb)).
Qed.

Lemma In_live_ranges_except cs rid q rq : (s_regions cs) !! q = Some rq -> q <> rid -> In (region_live_range rq) (live_ranges_except cs rid).
Proof.
  intros Hq NE. unfold live_ranges_except. apply in_or_app. right. apply in_map_iff. exists (q, rq). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply (proj2 (list_elem_of_filter _ _ _)).
  split; [cbn; destruct (N.eqb_spec q rid); [congruence| exact I]| apply elem_of_map_to_list; exact Hq].
Qed.

Section KCOV.
Variables (stK : mstate) (L : mled) (BLK : list blk) (LSK : lhead -> list aptr) (pbrk : Z) (mo : Model) (oldb l0 : Z) (rid : N) (r0 : region).
Let h := m_vmmaps mo.
Let OLD := Z_to_bv 64 oldb.
Hypotheses (INVK : INVL x0 stK L BLK LSK) (HK : KL L pbrk mo) (Hin : In (oldb, l0) (ld_groups L))
           (Hr0 : s_regions stK !! rid = Some r0) (Kr0 : r_kind r0 = RKGroup) (Eb0 : r_base r0 = oldb)
           (RPOS : Forall (fun bk : Z * Z => 0 < snd bk) (s_reserved stK)).

Lemma kcov_resv x : In x (s_reserved stK) -> kcov (vm_reserved h ++ map_remove (vm_maps h) OLD) x.
Proof.
  intros Hx. pose proof INVK as (IR & _). split; [exact (proj1 (Forall_forall _ _) RPOS x Hx)|].
  rewrite <- (ir_resv _ _ _ IR), (kl_resv _ _ _ HK) in Hx. apply in_map_iff in Hx as (e & <- & He). cbn [fst snd wwZ].
  intros y Hy. exists e. split; [apply in_or_app; left; exact He|]. unfold elo, ehi. exact Hy.
Qed.

Lemma live_range_pos q rq : s_regions stK !! q = Some rq -> 0 < snd (region_live_range rq).
Proof.
  intros Hq. pose proof INVK as (IR & _). destruct (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & LEN & _ & _ & MK). pose proof (round_up_pg_ge (r_len rq)) as UP.
  unfold region_live_range, is_metakind in *. destruct (r_kind rq); cbn [snd]; unfold PGSZ in *;
    first [specialize (MK (or_introl eq_refl)); lia| specialize (MK (or_intror eq_refl)); lia| lia].
Qed.

Lemma kcov_region q rq : s_regions stK !! q = Some rq -> q <> rid ->
  kcov (vm_reserved h ++ map_remove (vm_maps h) OLD) (region_live_range rq).
Proof.
  intros Hq NE. pose proof INVK as (IR & _). pose proof alloc_ceiling_lt as CL.
  pose proof (kl_groups _ _ _ HK oldb l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (went_In_bounds _ _ _ oldb l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
  split; [exact (live_range_pos q rq Hq)|].
  pose proof (ir_disj _ _ _ IR q rid rq r0 Hq Hr0 NE) as DJ0. pose proof (live_range_pos q rq Hq) as P2. pose proof (live_range_pos rid r0 Hr0) as P0.
  assert (E0 : region_live_range r0 = (oldb, round_up_pg (r_len r0))) by (unfold region_live_range; rewrite Kr0, Eb0; reflexivity).
  rewrite E0 in DJ0, P0. cbn [snd] in P0.

  assert (OLDlen : mmap_len l0 = round_up_pg (r_len r0)).
  {
    pose proof (Permutation_in _ (ir_groups _ _ _ IR) Hin) as X. apply in_map_iff in X as ([q' rq'] & E & Hf). cbn in E. injection E as E1 E2.
    apply filter_In in Hf as [Hf Kq']. apply (proj1 (In_map_to_list_regions _ _ _)) in Hf. cbn in Kq'. destruct (r_kind rq') eqn:Kq; try discriminate.
    destruct (N.eq_dec q' rid) as [->|NE'].
    - rewrite Hr0 in Hf. injection Hf as ->. rewrite <- E2. unfold mmap_len. symmetry. apply round_up_pg_eq.
    - exfalso. pose proof (ir_disj _ _ _ IR q' rid rq' r0 Hf Hr0 NE') as D. rewrite E0 in D. unfold region_live_range in D. rewrite Kq in D.
      pose proof (live_range_pos q' rq' Hf) as Pq. unfold region_live_range in Pq. rewrite Kq in Pq. cbn [snd] in Pq. lia. }
  assert (NOTOLD : forall e x, In e (vm_maps h) -> elo e <= x < ehi e -> fst (region_live_range rq) <= x < fst (region_live_range rq) + snd (region_live_range rq) -> fst e <> OLD).
  { intros e x He Hx Hrg Efst. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [->|D].
    - rewrite B5, B6, OLDlen in Hx. destruct (region_live_range rq) as [b2 l2]. cbn [fst snd] in Hrg, DJ0. lia.
    - pose proof (proj1 (kl_wf _ _ _ HK) e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold OLD in D.
      assert (UO : bv_unsigned OLD = oldb) by (subst OLD; apply unsigned_lit; lia). rewrite UO in D, W. rewrite ?unsigned_lit in D by lia. lia. }
  assert (INL : In (region_live_range rq) (lranges L)) by (apply (lranges_iff _ _ _ IR); apply (In_live_ranges stK q rq Hq)).
  destruct (In_lranges L _ INL) as [Hres|[(b & l & Hg & E)|[(b & l & k & Hm & E)|(b & l & Hbr & E)]]].
  - rewrite (ir_resv _ _ _ IR) in Hres. exact (proj2 (kcov_resv _ Hres)).
  - pose proof (went_In_bounds _ _ _ b l HK (or_introl Hg)) as (C1 & C2 & C3 & C4 & C5 & C6).
    intros x Hx. exists (went b (mmap_len l)). split; [| rewrite C5, C6; rewrite E in Hx; cbn [fst snd] in Hx; unfold mmap_len; rewrite <- round_up_pg_eq; lia].
    apply in_or_app. right. apply In_map_remove; [exact C4|]. eapply NOTOLD; [exact C4| | exact Hx]. rewrite C5, C6. rewrite E in Hx. cbn [fst snd] in Hx. unfold mmap_len; rewrite <- round_up_pg_eq; lia.
  - pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hm))) as (C1 & C2 & C3 & C4 & C5 & C6).
    intros x Hx. exists (went b (mmap_len l)). split; [| rewrite C5, C6; rewrite E in Hx; cbn [fst snd] in Hx; unfold mmap_len; rewrite <- round_up_pg_eq; lia].
    apply in_or_app. right. apply In_map_remove; [exact C4|]. eapply NOTOLD; [exact C4| | exact Hx]. rewrite C5, C6. rewrite E in Hx. cbn [fst snd] in Hx. unfold mmap_len; rewrite <- round_up_pg_eq; lia.
  - pose proof (kl_brkreg _ _ _ HK b l Hbr) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    intros x Hx. rewrite E in Hx. cbn [fst snd] in Hx. rewrite (round_up_pg_aligned l) in Hx by (unfold PGSZ in R4; exact R4).
    destruct (Rcov x ltac:(lia)) as (e & He & Hr). exists e. split; [| exact Hr].
    apply in_or_app. right. apply In_map_remove; [exact He|]. eapply NOTOLD; [exact He| exact Hr|]. rewrite E. cbn [fst snd]. rewrite (round_up_pg_aligned l) by (unfold PGSZ in R4; exact R4). lia.
Qed.

Lemma kcov_avoidx : Forall (kcov (vm_reserved h ++ map_remove (vm_maps h) OLD)) (live_ranges_except stK rid).
Proof.
  apply Forall_forall. intros x Hx. unfold live_ranges_except in Hx. apply in_app_or in Hx as [Hx|Hx]; [exact (kcov_resv x Hx)|].
  apply in_map_iff in Hx as ([q rq] & <- & Hf). cbn [snd].
  apply (proj2 (list_elem_of_In _ _)) in Hf. apply list_elem_of_filter in Hf as [Pq Hf]. apply elem_of_map_to_list in Hf.
  apply (kcov_region q rq Hf). intros ->. cbn in Pq. rewrite N.eqb_refl in Pq. exact Pq.
Qed.

Lemma kcov_avoid : Forall (kcov (vm_reserved h ++ vm_maps h)) (live_ranges stK).
Proof.
  pose proof (kl_groups _ _ _ HK oldb l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (went_In_bounds _ _ _ oldb l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
  assert (SUB : forall e, In e (vm_reserved h ++ map_remove (vm_maps h) OLD) -> In e (vm_reserved h ++ vm_maps h)).
  { intros e He. apply in_app_or in He as [He|He]; apply in_or_app; [left; exact He| right; exact (proj1 (In_map_remove_inv _ _ _ He))]. }
  apply Forall_forall. intros x Hx. unfold live_ranges in Hx. apply in_app_or in Hx as [Hx|Hx]; [eapply kcov_mono; [exact (kcov_resv x Hx)| exact SUB]|].
  apply in_map_iff in Hx as ([q rq] & <- & Hf). cbn [snd]. apply (proj1 (In_map_to_list_regions _ _ _)) in Hf.
  destruct (N.eq_dec q rid) as [->|NE]; [| eapply kcov_mono; [exact (kcov_region q rq Hf NE)| exact SUB]].
  rewrite Hr0 in Hf. injection Hf as <-. split; [exact (live_range_pos rid r0 Hr0)|].
  unfold region_live_range. rewrite Kr0, Eb0. cbn [fst snd]. intros x Hx. exists (went oldb (mmap_len l0)). split; [apply in_or_app; right; exact A5|].
  rewrite B5, B6. pose proof INVK as (IR & _).
  pose proof (Permutation_in _ (ir_groups _ _ _ IR) Hin) as X. apply in_map_iff in X as ([q' rq'] & E & Hf'). cbn in E. injection E as E1 E2.
  apply filter_In in Hf' as [Hf' Kq']. apply (proj1 (In_map_to_list_regions _ _ _)) in Hf'. cbn in Kq'. destruct (r_kind rq') eqn:Kq; try discriminate.
  destruct (N.eq_dec q' rid) as [->|NE'].
  - rewrite Hr0 in Hf'. injection Hf' as ->. rewrite <- E2. unfold mmap_len. rewrite <- round_up_pg_eq. exact Hx.
  - exfalso. pose proof (ir_disj _ _ _ IR q' rid rq' r0 Hf' Hr0 NE') as D. unfold region_live_range in D. rewrite Kq, Kr0, Eb0 in D.
    pose proof (live_range_pos q' rq' Hf') as Pq. pose proof (live_range_pos rid r0 Hr0) as P0. unfold region_live_range in Pq, P0. rewrite Kq in Pq. rewrite Kr0 in P0. cbn [snd] in Pq, P0. lia.
Qed.
End KCOV.

Lemma KL_same_len L pbrk mo oldb l0 l1 :
  KL L pbrk mo -> brk_quiet L -> In (oldb, l0) (ld_groups L) -> mmap_len l1 = mmap_len l0 -> 0 < l1 < LEN_MAX ->
  KL (set_groups ((oldb, l1) :: g_remove oldb (ld_groups L)) L) pbrk mo.
Proof.
  intros HK Hq Hin EL HL1.
  pose proof (kl_groups _ _ _ HK oldb l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
  pose proof (kl_distinct _ _ _ HK) as Kd.
  destruct (g_remove_split oldb l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
  pose proof Kd as Kd0. rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
  assert (Hg' : forall b l, In (b, l) (g_remove oldb (ld_groups L)) -> In (b, l) (ld_groups L)).
  { intros b l H. rewrite Ezz in H. rewrite Eg. apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]. }
  assert (Hph' : phase_inv (ld_brk (set_groups ((oldb, l1) :: g_remove oldb (ld_groups L)) L)) (set_groups ((oldb, l1) :: g_remove oldb (ld_groups L)) L) pbrk mo).
  { eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]. }
  kl_open HK. constructor; try exact Hph'; cbn [set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
  - intros b l [E|Hb]; [| exact (Kgr b l (Hg' b l Hb))]. injection E as <- <-. rewrite EL. splits; try assumption; lia.
  - eapply Permutation_NoDup; [| exact Kd0]. rewrite Ezz. rewrite Eg. set (M := map _ (ld_metas L)). cbn [map fst]. rewrite !map_app. cbn [map fst].
    rewrite <- !app_assoc. cbn [app]. symmetry.
    replace (oldb :: (map fst g1 ++ map fst g2) ++ M) with (oldb :: map fst g1 ++ map fst g2 ++ M) by (rewrite <- app_assoc; reflexivity).
    apply (Permutation_middle (map fst g1) (map fst g2 ++ M) oldb).
  - intros e He. destruct (Knoacc e He) as (e' & H1 & H2 & H3 & H4). exists e'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros b l [E|Hb]; [| exact (H4 b l (Hg' b l Hb))]. injection E as <- <-. rewrite EL. exact (H4 oldb l0 Hin).
Qed.

Definition RCERT (s : PState) (p : bptr) (A old : Z) : Prop :=
  exists stR LB resv, strip stR = ps_m s /\ AREACH_from resv stR LB /\ In (p, A, old) LB
    /\ (forall rid r, s_regions stR !! rid = Some r -> ranges_free (s_reserved stR) (r_base r) (round_up_pg (r_len r)) = true)
    /\ Forall (fun bk : Z * Z => 0 < snd bk) (s_reserved stR).

Section CORE.
Variables (X : list bptr) (G : PState -> Model -> Prop) (s1 : PState) (mo1 : Model) (p : bptr) (A old n : Z) (L : mled).
Variables (rid : N) (g : aptr) (oldb oldl needed : Z).
Hypotheses (SIM : SIMREL (ps_m s1) L) (HK : KL L (ps_brk s1) mo1) (LIVE : incl (map fst (p :: X)) (ld_live L)) (ND : List.NoDup (map fst (p :: X)))
           (RC0 : RCERT s1 p A old) (Hn : 0 <= n < 2^48)
           (RC : realloc_case (ps_m s1) (fst p) A n = RcRemap rid g oldb oldl needed).

Lemma core_facts : exists (stR : mstate) (LBR : list block) (resv : list (Z * Z)) (off : Z) (LR : mled) (LSR : lhead -> list aptr) (BLR : list blk)
    (r0 : region) (bg : aptr) (idx ai : Z) (a : aptr) (ar : area) (ka : Z),
  strip stR = ps_m s1 /\ AREACH_from resv stR LBR /\ In (p, A, old) LBR
  /\ (forall q rq, s_regions stR !! q = Some rq -> ranges_free (s_reserved stR) (r_base rq) (round_up_pg (r_len rq)) = true)
  /\ Forall (fun bk : Z * Z => 0 < snd bk) (s_reserved stR)
  /\ 0 <= off <= 255 /\ A = conc stR (fst p) + UNIT * off
  /\ INVL x0 stR L BLR LSR /\ In ((fst p, off), old) BLR
  /\ blk_facts stR (fst p) off old g bg idx ai a ar ka /\ m_sizeclass (MR stR g) = 63
  /\ s_regions stR !! rid = Some r0 /\ r_kind r0 = RKGroup /\ oldb = r_base r0 /\ oldl = round_up_pg (r_len r0) /\ rid = fst (fst p)
  /\ needed = remap_needed (UNIT * off) n /\ m_maplen (MR stR g) * 4096 = oldl /\ 0 < r_len r0 /\ MMAP_THRESHOLD <= n
  /\ In (oldb, r_len r0) (ld_groups L).
Proof.
  destruct RC0 as (stR & LBR & resv & ER & AR & HinB & RF & RPOS).
  assert (HOFF : exists off, 0 <= off <= 255 /\ A = conc stR (fst p) + UNIT * off).
  { destruct AR as (L0 & LS0 & BL0 & INV0 & _ & _ & _ & CR0). destruct (Forall2_In_l _ _ _ _ CR0 HinB) as (k & Hk0 & (C1 & C2 & C3)).
    pose proof INV0 as (_ & _ & _ & _ & _ & IS0 & _). destruct (is_blocks _ _ _ IS0 k Hk0) as (m0 & i0 & _ & B0 & _).
    exists (boff k). split; [exact B0|]. cbn [blk_addr blk_slot fst snd] in C1, C3. rewrite <- C1 in C3. exact C3. }
  destruct HOFF as (off & Hoff & HA).
  destruct SIM as (stK & BLK & LSK & EK & INVK & LIVEK).
  destruct (realloc_blk resv stR LBR p A old off AR HinB HA) as (LR & LSR & BLR & INVR & RESV & SEC & CR & Hk).
  pose proof (INVL_transplant x0 stK stR L LR BLK BLR LSK LSR ltac:(rewrite EK, ER; reflexivity) INVK INVR) as INV1.
  destruct (block_facts x0 stR L BLR LSR INV1 (fst p) off old Hk) as (g' & bg & idx & ai & a & ar & ka & BF).
  rewrite <- ER in RC.
  destruct (realloc_remap_facts resv stR LBR p A old n off AR HinB HA rid g oldb oldl needed RC) as (Erid & EN & THR & i & r0 & SL & Hr0 & Kr0 & Eob & Eol & CC & SC63 & EML & LEN).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL'. rewrite SL in SL'. assert (g' = g /\ idx = i) as [-> ->] by (split; congruence).
  exists stR, LBR, resv, off, LR, LSR, BLR, r0, bg, i, ai, a, ar, ka.
  splits; auto; try lia.

  pose proof INV1 as (IR & _). eapply Permutation_in; [apply Permutation_sym; exact (ir_groups _ _ _ IR)|].
  apply in_map_iff. exists (rid, r0). split; [cbn; rewrite Eob; reflexivity|]. apply filter_In. split; [apply (proj2 (In_map_to_list_regions _ _ _)); exact Hr0| cbn; rewrite Kr0; reflexivity].
Qed.

Lemma remap_owns nb mo' :
  0 < nb -> nb mod 4096 = 0 -> nb + needed <= alloc_ceiling ->
  (forall rid2 r2, s_regions (ps_m s1) !! rid2 = Some r2 -> rid2 <> rid -> let '(b2, l2) := region_live_range r2 in nb + needed <= b2 \/ b2 + l2 <= nb) ->
  KL (set_groups ((nb, needed) :: g_remove oldb (ld_groups L)) L) (ps_brk s1) mo' ->
  G (set_m (remap_update (ps_m s1) rid g nb needed) s1) mo' ->
  OWNS (p :: X) G (set_m (remap_update (ps_m s1) rid g nb needed) s1) mo'.
Proof.
  intros NB0 NBA NCEIL DISJ HK' HG'.
  destruct core_facts as (stR & LBR & resv & off & LRr & LSR & BLR & r0 & bg & idx & ai & a & ar & ka
                          & ER & AR & HinB & RF & RPOS & Hoff & HA & INV1 & Hk & BF & SC63 & Hr0 & Kr0 & Eob & Eol & Erid & EN & EML & LEN & THR & HinG).
  destruct SIM as (stK & BLK & LSK & EK & INVK & LIVEK).
  rewrite <- ER in DISJ. subst rid.
  pose proof (remap_INVL x0 stR L BLR LSR (fst p) off old n INV1 Hk eq_refl ltac:(lia) g bg idx ai a ar ka BF SC63 nb NB0 NBA ltac:(rewrite EN in NCEIL; exact NCEIL) ltac:(rewrite EN in DISJ; exact DISJ)) as INV'.
  rewrite <- EN in INV'.
  set (GL := (nb, needed) :: g_remove oldb (ld_groups L)).

  assert (PG : Permutation GL (ld_groups (MI_Realloc2.LR stR L (fst p) off n g nb))).
  { unfold MI_Realloc2.LR, MI_Realloc2.L'. cbn [ld_groups KInv.set_groups].
    pose proof INV1 as (IR & _).
    destruct (regions_groups_perm (s_regions stR) (fst (fst p)) r0 (mkRegion RKGroup nb needed) Hr0 Kr0 eq_refl) as (REST & P1 & P2).
    cbn [r_base r_len] in P2. rewrite <- Eob in P1.
    destruct (g_remove_perm (ld_groups L) _ oldb (r_len r0) (r_len r0) REST (kl_distinct _ _ _ HK) HinG ltac:(eapply Permutation_trans; [exact (ir_groups _ _ _ IR)| exact P1])) as [_ PR].
    eapply Permutation_trans; [| apply Permutation_sym].
    - subst GL. apply perm_skip. exact PR.
    - unfold MI_Realloc2.stR. unfold MI_Realloc2.isgroup.
      match goal with |- context [s_regions (upd_meta ?a ?b (set_regions ?R ?st0))] => change (s_regions (upd_meta a b (set_regions R st0))) with R end.
      change (s_regions (set_tick (N.succ (s_tick stR)) stR)) with (s_regions stR).
      rewrite EN in P2 |- *. exact P2. }
  pose proof (INVL_groups_perm x0 _ _ _ _ GL INV' PG) as INV''.
  change (KInv.set_groups GL (MI_Realloc2.LR stR L (fst p) off n g nb)) with (set_groups GL L) in INV''.
  set (BL' := ((fst p, off), n) :: bl_remove (fst p) BLR) in INV''.
  split; [| split; [exact ND| exact HG']].
  exists (set_live (map bslot BL') (set_groups GL L)). split; [| split].
  - exists (remap_full stR (fst p) off n nb needed), BL', LSR. split; [| split; [apply INVL_set_live; exact INV''| reflexivity]].
    cbn [ps_m set_m]. rewrite strip_remap_full by (eexists; exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)). rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF), ER. reflexivity.
  - cbn [ps_brk set_m]. apply KL_set_live. exact HK'.
  - intros c Hc. cbn [ld_live set_live]. specialize (LIVE c Hc). rewrite LIVEK in LIVE.
    pose proof (sim_slots stK stR L L BLK BLR LSK LSR ltac:(rewrite EK, ER; reflexivity) INVK INV1 c LIVE) as IN'.
    subst BL'. cbn [map bslot fst]. destruct (aptr_eq_dec c (fst p)) as [->|NE]; [left; reflexivity| right].
    rewrite bl_remove_map. apply in_ap_remove; [exact IN'| exact NE].
Qed.
End CORE.

Lemma realloc_move_spec_s X G p n : frame_ok G -> 0 <= n ->
  mspec (OWNS (p :: X) G) (realloc_move p n)
        (fun r s mo => match r with Some p' => OWNS (p' :: X) G s mo | None => OWNS (p :: X) G s mo end).
Proof.
  intros HG Hn. unfold realloc_move.
  eapply mspec_bind; [apply (raw_malloc_spec_s (p :: X) G n HG Hn)|]. intros [p'|]; cbn beta iota.
  - eapply mspec_bind.
    + eapply mspec_pre; [apply (raw_free_spec_s (p' :: X) G p HG)|]. intros s mo [OW _]. eapply OWNS_perm; [| exact OW]. apply perm_swap.
    + intros []. apply mspec_ret. intros s mo H. exact H.
  - apply mspec_ret. intros s mo H. exact H.
Qed.

Theorem raw_realloc_spec_s X G p A old n : frame_ok G -> 0 <= n < 2^48 ->
  mspec (fun s mo => OWNS (p :: X) G s mo /\ RCERT s p A old /\ m_vm_lazy mo = [])
        (raw_realloc p A n)
        (fun r s mo => match r with Some p' => OWNS (p' :: X) G s mo | None => OWNS (p :: X) G s mo end).
Proof.
  intros HG Hn. pose proof alloc_ceiling_lt as CL. unfold raw_realloc.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> (OW & RC0 & LZ)].
  pose proof OW as [(L & SIM & HK & LIVE) [ND HGs]].
  unfold realloc_body. destruct (realloc_case (ps_m s1) (fst p) A n) as [|rid g oldb oldl needed|] eqn:RC.
  -   apply mspec_ret. intros s mo [-> ->]. exact OW.
  -
    destruct (core_facts s1 p A old n L rid g oldb oldl needed SIM RC0 RC)
      as (stR & LBR & resv & off & LRr & LSR & BLR & r0 & bg & idx & ai & a & ar & ka
          & ER & AR & HinB & RF & RPOS & Hoff & HA & INV1 & Hk & BF & SC63 & Hr0 & Kr0 & Eob & Eol & Erid & EN & EML & LEN & THR & HinG).
    pose proof INV1 as (IR & _).
    pose proof (kl_groups _ _ _ HK oldb (r_len r0) HinG) as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (went_In_bounds _ _ _ oldb (r_len r0) HK (or_introl HinG)) as (_ & B2 & _ & _ & B5 & B6).
    assert (EOL : mmap_len (r_len r0) = oldl) by (rewrite Eol; unfold mmap_len; symmetry; apply round_up_pg_eq). rewrite EOL in *.
    pose proof (remap_needed_ge (UNIT * off) n ltac:(lia) ltac:(unfold UNIT; lia)) as NDR. rewrite <- EN in NDR. unfold UNIT, IB in NDR.
    pose proof (remap_needed_pg (UNIT * off) n) as NDA. rewrite <- EN in NDA.
    assert (N0 : 0 < needed) by lia. assert (NMAX : needed < 2^50) by lia.
    assert (QUIET : brk_quiet L).
    { pose proof (ir_brk _ _ _ IR) as HB. unfold brk_quiet. unfold ctx in HB. revert HB. destruct (c_brk (s_ctx stR)); intros HB;
        lazymatch type of HB with _ /\ _ => destruct HB as [EB _]; rewrite EB | _ => rewrite HB end; exact I. }
    assert (E0 : region_live_range r0 = (oldb, oldl)) by (unfold region_live_range; rewrite Kr0, <- Eob, <- Eol; reflexivity).
    assert (LRP : forall q rq, s_regions stR !! q = Some rq -> 0 < snd (region_live_range rq)).
    { intros q rq Hq. exact (live_range_pos stR L BLR LSR INV1 q rq Hq). }
    assert (BDof : forall nb', (forall rid2 r2, s_regions stR !! rid2 = Some r2 -> rid2 <> rid ->
                                  let '(b2, l2) := region_live_range r2 in nb' + needed <= b2 \/ b2 + l2 <= nb') -> brk_disj L nb' needed).
    { intros nb' D b0 l0 Hbr. destruct (proj1 (ir_brkreg _ _ _ IR b0 l0) Hbr) as (ridb & rb & Hrb & Krb & Ebb & Ebl).
      assert (NEb : ridb <> rid) by (intros ->; rewrite Hr0 in Hrb; injection Hrb as ->; rewrite Kr0 in Krb; discriminate).
      specialize (D ridb rb Hrb NEb). unfold region_live_range in D. rewrite Krb, Ebb, Ebl in D. pose proof (round_up_pg_ge l0). unfold PGSZ in *. lia. }
    assert (GFR : forall s mo', vm_only mo1 mo' -> G (set_m s (s1)) mo') by (intros s mo' VO; apply (HG s1 _ mo1 _); [reflexivity| reflexivity| exact VO| exact HGs]).
    set (OLD := Z_to_bv 64 oldb) in *. set (OLDN := Z_to_bv 64 oldl). set (NEWN := Z_to_bv 64 needed).
    assert (UO : bv_unsigned OLD = oldb) by (subst OLD; apply unsigned_lit; lia).
    assert (EOLD : went oldb oldl = (OLD, OLDN)) by reflexivity.
    pose proof (kl_wf _ _ _ HK) as [KW KP].

    assert (Dold : forall e, In e (vm_reserved (m_vmmaps mo1) ++ map_remove (vm_maps (m_vmmaps mo1)) OLD) -> oldb + oldl <= elo e \/ ehi e <= oldb).
    { intros e He. apply in_app_or in He as [He|He].
      - specialize (RF rid r0 Hr0). rewrite <- Eob, <- Eol, <- (ir_resv _ _ _ IR), (kl_resv _ _ _ HK) in RF.
        pose proof (rf_In _ _ _ _ _ RF ltac:(apply in_map_iff; exists e; split; [reflexivity| exact He])) as D. unfold wwZ, elo, ehi in *. cbn [fst snd] in D. lia.
      - apply In_map_remove_inv in He as [He Hne]. destruct (pwdisj_In _ _ _ KP He A5) as [->|D]; [exfalso; apply Hne; rewrite EOLD; reflexivity|].
        pose proof (KW e He) as W. unfold edisj in D. rewrite B5, B6 in D. lia. }
    assert (SRC : mremap_source_b (m_vmmaps mo1) OLD OLDN oldl = true).
    { unfold mremap_source_b. rewrite UO. pose proof (kl_ceil _ _ _ HK) as CK. unfold ceil_ok in CK.
      replace (oldb + oldl <=? alloc_top (m_vmmaps mo1)) with true by (symmetry; apply Z.leb_le; clear - A4 CK; lia).
      rewrite (region_free_of_disj (vm_reserved (m_vmmaps mo1)) OLD OLDN) by (intros e He; subst OLDN; rewrite UO, unsigned_lit by lia; apply Dold; apply in_or_app; left; exact He).
      replace (map_has (vm_maps (m_vmmaps mo1)) OLD OLDN) with true
        by (symmetry; unfold map_has; apply existsb_exists; exists (went oldb oldl); split; [exact A5| rewrite EOLD; cbn [fst snd]; rewrite !bv_eqb_refl; reflexivity]).
      rewrite (region_free_of_disj (vm_noaccess (m_vmmaps mo1)) OLD OLDN); [reflexivity|].
      intros e He. subst OLDN. rewrite UO, unsigned_lit by lia. destruct (kl_noacc _ _ _ HK e He) as (e' & H1 & H2 & H3 & H4).
      destruct (pwdisj_In _ _ _ KP H1 A5) as [EQ|D]; [exfalso; exact (H4 oldb (r_len r0) HinG ltac:(rewrite EOL; exact EQ))|]. unfold edisj in D. rewrite B5, B6 in D. lia. }
    assert (BK : mremap_backing_uniform_b mo1 OLD OLDN = true) by (unfold mremap_backing_uniform_b; rewrite LZ; reflexivity).
    unfold realloc_remap. destruct (Z.eqb_spec oldl needed) as [EQ|NEQ].
    +
      apply (mspec_bind _ _ _ (fun _ s mo => OWNS (p :: X) G s mo)); [apply mspec_upd'; intros s mo [-> ->] | intros []; apply mspec_ret; intros s mo H; exact H]. cbn beta.
      apply (remap_owns X G s1 mo1 p A old n L rid g oldb oldl needed SIM HK LIVE ND RC0 Hn RC oldb mo1); [lia| unfold PGSZ in A3; exact A3| rewrite <- EQ; exact A4| | | apply GFR; apply vm_only_refl].
      * rewrite <- ER. cbn [s_regions strip]. change (s_regions (strip stR)) with (s_regions stR). intros rid2 r2 H2 NE2.
        pose proof (ir_disj _ _ _ IR rid2 rid r2 r0 H2 Hr0 NE2) as D. rewrite E0 in D. destruct (region_live_range r2) as [b2 l2]. lia.
      * apply (KL_same_len L (ps_brk s1) mo1 oldb (r_len r0) needed HK QUIET HinG); [rewrite EOL, <- EQ; unfold mmap_len; apply page_round_up_Z_id; rewrite EQ; exact NDA| unfold LEN_MAX; lia].
    +
      eapply mspec_bind.
      * apply (mspec_sys (NMremap oldb oldl needed) _ _
                 (fun x s mo' => s = s1 /\ vm_only mo1 mo' /\
                    match x with
                    | RmErr _ => mo' = mo1
                    | RmSame => OWNS (p :: X) G (set_m (remap_update (ps_m s1) rid g oldb needed) s1) mo'
                    | RmAt nb => OWNS (p :: X) G (set_m (remap_update (ps_m s1) rid g nb needed) s1) mo'
                    end)).
        intros s mo [-> ->].
        pose proof (kcov_avoidx stR L BLR LSR (ps_brk s1) mo1 oldb (r_len r0) rid r0 INV1 HK HinG Hr0 Kr0 (eq_sym Eob) RPOS) as AVX.
        pose proof (kcov_avoid stR L BLR LSR (ps_brk s1) mo1 oldb (r_len r0) rid r0 INV1 HK HinG Hr0 Kr0 (eq_sym Eob) RPOS) as AV.
        fold OLD in AVX.
        assert (ELX : live_ranges_except (ps_m s1) rid = live_ranges_except stR rid) by (rewrite <- ER; reflexivity).
        assert (ELV : live_ranges (ps_m s1) = live_ranges stR) by (rewrite <- ER; reflexivity).
        rewrite ELX, ELV.
        assert (LA : oldl mod 4096 = 0) by (rewrite <- EOL; apply mmap_len_aligned).
        assert (A3' : oldb mod 4096 = 0) by (unfold PGSZ in A3; exact A3).
        pose proof (dec_nsafe oldb oldl needed mo1 A2 A3' B2 LA N0 NDA NEQ A4 ltac:(lia) SRC BK) as NSAFE.
        split; [exact NSAFE|].
        intros rsp mo' evs ST.
        destruct (nstep_dec_mremap oldb oldl needed (live_ranges_except stR rid) (live_ranges stR) mo1 A2 A3' B2 LA N0 NDA NEQ A4 ltac:(lia) SRC BK (kl_ceil _ _ _ HK) AVX AV rsp mo' evs ST) as (-> & VO & x & Hd & Hx).
        pose proof (minv_preserved _ _ _ _ _ NSAFE (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) ST) as [Hh' Hmi'].
        exists x. split; [exact Hd|]. split; [reflexivity|]. split; [exact VO|].
        assert (REG : s_regions (ps_m s1) = s_regions stR) by (rewrite <- ER; reflexivity).
        destruct x as [e| |nb].
        -- destruct Hx as [-> ->]. reflexivity.
        --
           destruct Hx as (Evm & CASES). fold OLD NEWN in Evm, CASES.
           assert (NCEIL : oldb + needed <= alloc_ceiling) by (destruct CASES as [LT|(LT & CE & _)]; lia).
           assert (DISJ : forall rid2 r2, s_regions (ps_m s1) !! rid2 = Some r2 -> rid2 <> rid ->
                            let '(b2, l2) := region_live_range r2 in oldb + needed <= b2 \/ b2 + l2 <= oldb).
           { rewrite REG. intros rid2 r2 H2 NE2. pose proof (ir_disj _ _ _ IR rid2 rid r2 r0 H2 Hr0 NE2) as D. rewrite E0 in D. pose proof (LRP rid2 r2 H2) as P2.
             destruct CASES as [LT|(LT & CE & RFK & RFX)].
             - destruct (region_live_range r2) as [b2 l2]. lia.
             - pose proof (In_live_ranges_except stR rid rid2 r2 H2 NE2) as IN2. destruct (region_live_range r2) as [b2 l2]. cbn [snd] in P2.
               pose proof (rf_In _ _ _ _ _ RFX IN2). lia. }
           apply (remap_owns X G s1 mo1 p A old n L rid g oldb oldl needed SIM HK LIVE ND RC0 Hn RC oldb mo'); [lia| exact A3'| exact NCEIL| exact DISJ| | apply GFR; exact VO].
           apply (KL_remap L (ps_brk s1) mo1 mo' oldb (r_len r0) needed oldb HK QUIET HinG N0 NDA ltac:(unfold LEN_MAX; lia) A2 A3' NCEIL); [| apply BDof; rewrite <- REG; exact DISJ| exact Evm| exact Hmi'| exact Hh'].
           intros e He. destruct CASES as [LT|(LT & CE & RFK & RFX)].
           ++ pose proof (Dold e He). lia.
           ++ pose proof (region_free_disj _ _ _ _ RFK He) as D. subst NEWN. rewrite UO, unsigned_lit in D by lia. lia.
        --
           destruct Hx as (NEb & NBA' & NB0' & NCEIL' & RFK & LT & Evm & RFA). fold OLD NEWN in Evm, RFK.
           assert (DISJ : forall rid2 r2, s_regions (ps_m s1) !! rid2 = Some r2 -> rid2 <> rid ->
                            let '(b2, l2) := region_live_range r2 in nb + needed <= b2 \/ b2 + l2 <= nb).
           { rewrite REG. intros rid2 r2 H2 NE2. pose proof (In_live_ranges stR rid2 r2 H2) as IN2. destruct (region_live_range r2) as [b2 l2].
             exact (rf_In _ _ _ _ _ RFA IN2). }
           apply (remap_owns X G s1 mo1 p A old n L rid g oldb oldl needed SIM HK LIVE ND RC0 Hn RC nb mo'); [exact NB0'| exact NBA'| exact NCEIL'| exact DISJ| | apply GFR; exact VO].
           apply (KL_remap L (ps_brk s1) mo1 mo' oldb (r_len r0) needed nb HK QUIET HinG N0 NDA ltac:(unfold LEN_MAX; lia) NB0' NBA' NCEIL'); [| apply BDof; rewrite <- REG; exact DISJ| exact Evm| exact Hmi'| exact Hh'].
           intros e He. assert (He' : In e (vm_reserved (m_vmmaps mo1) ++ vm_maps (m_vmmaps mo1))).
           { apply in_app_or in He as [He|He]; apply in_or_app; [left; exact He| right; exact (proj1 (In_map_remove_inv _ _ _ He))]. }
           pose proof (region_free_disj _ _ _ _ RFK He') as D. subst NEWN. rewrite !unsigned_lit in D by lia. lia.
      * intros x. destruct x as [e| |nb]; cbn beta iota.
        -- eapply mspec_pre; [apply realloc_move_spec_s; [exact HG| lia]|]. intros s mo (-> & _ & ->). exact OW.
        -- apply (mspec_bind _ _ _ (fun _ s mo => OWNS (p :: X) G s mo)); [apply mspec_upd'; intros s mo (-> & _ & H); exact H| intros []; apply mspec_ret; intros s mo H; exact H].
        -- apply (mspec_bind _ _ _ (fun _ s mo => OWNS (p :: X) G s mo)); [apply mspec_upd'; intros s mo (-> & _ & H); exact H| intros []; apply mspec_ret; intros s mo H; exact H].
  -   eapply mspec_pre; [apply realloc_move_spec_s; [exact HG| lia]|]. intros s mo [-> ->]. exact OW.
Qed.

Lemma block_in_kernel_map X G s mo p A n :
  OWNS X G s mo ->
  (exists stR LB resv, strip stR = ps_m s /\ AREACH_from resv stR LB /\ In (p, A, n) LB) ->
  exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e + UNIT <= A /\ A + n <= ehi e.
Proof.
  intros [(L & (stK & BLK & LSK & EK & INVK & LIVEK) & HK & _) _] (stR & LB & resv & ER & AR & HinB).
  destruct AR as (LR & LSR & BLR & INVR & LIVER & RESV & SEC & CR).
  pose proof (INVL_transplant x0 stK stR L LR BLK BLR LSK LSR ltac:(rewrite EK, ER; reflexivity) INVK INVR) as INV1.
  pose proof INV1 as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (A_MallocFacts_inv2.LB_geo x0 stR L BLR LSR INV1 LB CR _ HinB)
    as (c2 & off2 & n2 & m2 & bm2 & i2 & r2 & Hk2 & C1 & C2 & Hm2 & Hi2 & Ec2 & NH2 & Hr2 & Kr2 & Ea2 & Ho2 & Hn2 & Fit2).
  cbn [blk_addr blk_size fst snd] in C2, Ea2. subst n2.
  destruct (A_MallocFacts_inv2.group_in_region x0 stR L BLR LSR INV1 _ _ Hm2) as (r2' & Hr2' & _ & B02 & GE2).
  rewrite Hr2 in Hr2'. assert (r2' = r2) as -> by congruence.
  pose proof (MI_Geom.sstart_mono x0 stR LSR IG _ _ (i2 + 1) (m_last_idx (MR stR m2) + 1) Hm2 ltac:(lia)) as SM2. rewrite <- MI_Geom.gend_eq in SM2.
  pose proof (MI_Geom.sstart_succ stR m2 i2) as SS2. pose proof (MI_Geom.sstart0 x0 stR LSR IM _ _ Hm2) as S02.
  pose proof (MI_Geom.sstart_mono x0 stR LSR IG _ _ 0 i2 Hm2 ltac:(lia)) as SMb.
  pose proof (MI_Geom.stride_ge x0 stR LSR IG _ _ Hm2) as [SG _].

  assert (HinG : In (r_base r2, r_len r2) (ld_groups L)).
  { eapply Permutation_in; [apply Permutation_sym; exact (ir_groups _ _ _ IR)|].
    apply in_map_iff. exists (fst bm2, r2). split; [reflexivity|]. apply filter_In. split; [apply (proj2 (In_map_to_list_regions _ _ _)); exact Hr2| cbn; rewrite Kr2; reflexivity]. }
  pose proof (went_In_bounds _ _ _ _ _ HK (or_introl HinG)) as (_ & _ & _ & W4 & W5 & W6).
  exists (went (r_base r2) (mmap_len (r_len r2))). split; [exact W4|]. rewrite W5, W6. unfold mmap_len. rewrite <- round_up_pg_eq.
  unfold UNIT, IB in *. lia.
Qed.

End CEIL.
