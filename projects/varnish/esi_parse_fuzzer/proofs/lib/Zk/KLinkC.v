(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Monad MSafe STree Malloc MProg KInv KNodes KLink.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dest4xs.Prelim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Monad OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MProg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.

Module KLinkR.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import AgentLib RelSpec MmapSim AllocSim RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Monad MSafe STree Malloc MProg KInv KNodes RzImpl KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Ltac kl_open HK := destruct HK as [Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kmr Knc Kgna Kmat Kcpl Kbb Klim Kceil].
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Lemma KL_groups_perm L G' pbrk mo : KL L pbrk mo -> Permutation (ld_groups L) G' -> KL (set_groups G' L) pbrk mo.
Proof.
  intros HK P.
  assert (INP : forall x, In x G' <-> In x (ld_groups L)).
  { intros x. split; intros H; [eapply Permutation_in; [apply Permutation_sym; exact P| exact H]| eapply Permutation_in; [exact P| exact H]]. }
  kl_open HK. constructor; cbn [set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
  - intros b l H. apply Kgr. apply INP. exact H.
  - eapply Permutation_NoDup; [| exact Kdis]. apply Permutation_app_tail. apply Permutation_map. exact P.
  - revert Kph. destruct (ld_brk L); auto. ((first [ intro dR_16; dand8 dR_16 as A1 A2 A3 A4 A5 A6 A7 A8 | intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) ])). split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [| exact A8].
    intros b l H. apply A7. apply INP. exact H.
  - intros b l H. apply Kgna. apply INP. exact H.
  - intros e He. destruct (Kcpl e He) as [(b & l & H & E)|[X|X]]; [left; exists b, l; split; [apply INP; exact H| exact E]| right; left; exact X| right; right; exact X].
Qed.

Lemma m_vmmaps_with_vm_backing l p m : m_vmmaps (with_vm_backing l p m) = m_vmmaps m.
Proof. destruct m; reflexivity. Qed.
Lemma m_vmmaps_mremap_model_next mo old on dst nn :
  m_vmmaps (mremap_model_next mo old on dst nn) = mremap_maps_next (m_vmmaps mo) old dst nn.
Proof. unfold mremap_model_next, vm_resize_backing. rewrite m_vmmaps_with_vm_backing, with_vmmaps_vm. reflexivity. Qed.
Lemma m_halted_mremap_model_next mo old on dst nn :
  m_halted (mremap_model_next mo old on dst nn) = m_halted mo.
Proof. unfold mremap_model_next, vm_resize_backing, with_vm_backing, with_vmmaps. destruct mo; reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_mremap_cases : forall a on nd mo rsp mo',
  0 < a < 2^64 -> 0 < on < 2^64 -> on mod 4096 = 0 -> 0 < nd < 2^64 -> nd mod 4096 = 0 -> a + on <= alloc_ceiling -> a mod 4096 = 0 ->
  minv mo -> m_halted mo = None ->
  ceil_ok mo ->   (* [comment removed for export] *)
  nstep (NMremap a on nd MREMAP_MAYMOVE) mo rsp mo' ->
  let h := m_vmmaps mo in
     (exists e, In e mremap_errnos /\ rsp = mkEffect (errno_ret e) [] [] /\ mo' = mo)
  \/ (on = nd /\ rsp = mkEffect (Z_to_bv 64 a) [] [] /\ mo' = mo)
  \/ (exists dst : word,
        let dZ := bv_unsigned dst in
        0 < dZ /\ dZ mod 4096 = 0 /\ dZ + nd <= alloc_ceiling /\ on <> nd
        /\ m_vmmaps mo' = mremap_maps_next h (Z_to_bv 64 a) dst (Z_to_bv 64 nd)
        /\ minv mo' /\ m_halted mo' = None
        /\ ((dst = Z_to_bv 64 a /\ (nd < on \/ (on < nd /\ region_free (vm_reserved h ++ map_remove (vm_maps h) (Z_to_bv 64 a)) (Z_to_bv 64 a) (Z_to_bv 64 nd) = true))
             /\ rsp = mremap_inplace_effect (Z_to_bv 64 a) (Z_to_bv 64 on) (Z_to_bv 64 nd) on nd)
            \/ (dst <> Z_to_bv 64 a /\ on < nd /\ region_free (vm_reserved h ++ vm_maps h) dst (Z_to_bv 64 nd) = true
                /\ rsp = mremap_move_effect (Z_to_bv 64 a) (Z_to_bv 64 on) dst on nd))).
Proof.
  intros a on nd mo rsp mo' Ha Hon Aon Hnd And AC AA Hmi Hh Hce H h. unfold ceil_ok in Hce.
  pose proof (minv_preserved _ _ _ _ Hmi Hh H) as [Hh' Hmi'].
  cbn -[mremap_model_next mremap_inplace_effect mremap_move_effect mremap_inplace_grow_b mremap_fresh_b w wlen rlen Z.eqb Z.ltb region_free map_remove alloc_ceiling alloc_top] in H.
  assert (Ron : rlen on = on) by (rewrite rlen_eq by lia; apply mmap_len_of_aligned; lia).
  assert (Rnd : rlen nd = nd) by (rewrite rlen_eq by lia; apply mmap_len_of_aligned; lia).
  assert (Won : wlen on = Z_to_bv 64 on) by (unfold wlen; rewrite Ron; reflexivity).
  assert (Wnd : wlen nd = Z_to_bv 64 nd) by (unfold wlen; rewrite Rnd; reflexivity).
  rewrite !Ron, !Rnd, !Won, !Wnd in H. change (w a) with (Z_to_bv 64 a) in H.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  destruct H as [(E & -> & ->)|(NE & H)]; [right; left; auto|].
  destruct H as [(e & He & -> & ->)|[(LT & -> & ->)|[(LT & GB & -> & ->)|(LT & dst & FB & -> & ->)]]].
  - left. exists e. auto.
  - right; right. exists (Z_to_bv 64 a). cbn zeta. rewrite Ua, m_vmmaps_mremap_model_next, m_halted_mremap_model_next.
    splits; try lia; auto 10.
  - right; right. exists (Z_to_bv 64 a). cbn zeta. rewrite Ua, m_vmmaps_mremap_model_next, m_halted_mremap_model_next.
    unfold mremap_inplace_grow_b in GB. apply andb_prop in GB as [GB _]. apply andb_prop in GB as [G1 G2]. apply Z.leb_le in G1. rewrite Ua in G1.
    rewrite Hce in G1.
    splits; try lia; auto 10.
  - right; right. exists dst. cbn zeta. rewrite m_vmmaps_mremap_model_next, m_halted_mremap_model_next.
    unfold mremap_fresh_b in FB. apply andb_prop in FB as [FB F5]. apply andb_prop in FB as [FB F4].   (* [comment removed for export] *)
    apply andb_prop in FB as [FB F3]. apply andb_prop in FB as [FB F2]. apply andb_prop in FB as [F0 F1].
    apply Z.eqb_eq in F1. apply Z.ltb_lt in F2. apply Z.leb_le in F3. rewrite Hce in F3. rewrite page_size_eq in F1.
    assert (NEQ : dst <> Z_to_bv 64 a) by (intros ->; rewrite bv_eqb_refl in F0; discriminate).
    splits; try lia; auto 10.
Qed.

(* [comment removed for export] *)
Lemma KL_regroup_len L G0 pbrk mo a l0 nd :
  KL (set_groups ((a, l0) :: G0) L) pbrk mo -> nd = mmap_len l0 -> KL (set_groups ((a, nd) :: G0) L) pbrk mo.
Proof.
  intros HK ->. (first [ pose proof ((kl_groups _ _ _ HK a l0 ltac:(left; reflexivity))) as dR_1; dand6 dR_1 as A1 A2 A3 A4 A5 A6 | pose proof (kl_groups _ _ _ HK a l0 ltac:(left; reflexivity)) as (A1 & A2 & A3 & A4 & A5 & A6) ]).
  pose proof (mmap_len_ge l0 ltac:(lia)) as ML.
  assert (MM : mmap_len (mmap_len l0) = mmap_len l0) by (apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
  kl_open HK. constructor; cbn [set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live] in *; auto.
  - intros b l [E|H]; [injection E as <- <-| exact (Kgr b l (or_intror H))]. rewrite MM. unfold LEN_MAX in *. splits; auto; try lia.
    pose proof alloc_ceiling_lt. lia.
  - revert Kph. destruct (ld_brk L); auto. ((first [ intro dR_17; dand8 dR_17 as B1 B2 B3 B4 B5 B6 B7 B8 | intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8) ])). splits; auto.
    intros b l [E|H]; [injection E as <- <-| exact (B7 b l (or_intror H))]. rewrite MM. exact (B7 a l0 (or_introl eq_refl)).
  - intros b l [E|H]; [injection E as <- <-| exact (Kgna b l (or_intror H))]. rewrite MM. exact (Kgna a l0 (or_introl eq_refl)).
  - intros e He. destruct (Kcpl e He) as [(b & l & [E|H] & Ee)|[X|X]]; [| | right; left; exact X| right; right; exact X].
    + injection E as <- <-. left. exists a, (mmap_len l0). split; [left; reflexivity| rewrite MM; exact Ee].
    + left. exists b, l. split; [right; exact H| exact Ee].
Qed.

Lemma went_wz b n : went b n = (wz b, wz n). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma KL_mremap : forall L G0 pbrk mo mo' a l0 nd (dst : word),
  KL (set_groups ((a, l0) :: G0) L) pbrk mo -> brk_quiet L ->
  let on := mmap_len l0 in let h := m_vmmaps mo in let dZ := bv_unsigned dst in
  4096 <= nd < LEN_MAX -> nd mod 4096 = 0 ->
  0 < dZ -> dZ mod 4096 = 0 -> dZ + nd <= alloc_ceiling ->
  m_vmmaps mo' = mremap_maps_next h (wz a) dst (wz nd) -> minv mo' -> m_halted mo' = None -> m_vm_materialized mo' = [] ->
  ((dst = wz a /\ (nd < on \/ region_free (vm_reserved h ++ map_remove (vm_maps h) (wz a)) (wz a) (wz nd) = true))
   \/ (dst <> wz a /\ region_free (vm_reserved h ++ vm_maps h) dst (wz nd) = true)) ->
  KL (set_groups ((dZ, nd) :: G0) L) pbrk mo'
  /\ (forall b l, (In (b, l) G0 \/ exists k, In (b, l, k) (ld_metas L)) -> dZ + nd <= b \/ b + mmap_len l <= dZ)
  /\ brk_disj L dZ nd
  /\ region_free (vm_reserved h) dst (wz nd) = true
  /\ (dst <> wz a -> dZ + nd <= a \/ a + on <= dZ).
Proof.
  intros L G0 pbrk mo mo' a l0 nd dst HK Hq on h dZ Hnd And D0 DA DC Evm Hmi' Hh' Hmat' CASE.
  pose proof alloc_ceiling_lt as Hcl.
  (first [ pose proof ((kl_groups _ _ _ HK a l0 ltac:(left; reflexivity))) as dR_2; dand6 dR_2 as A1 A2 A3 A4 A5 A6 | pose proof (kl_groups _ _ _ HK a l0 ltac:(left; reflexivity)) as (A1 & A2 & A3 & A4 & A5 & A6) ]). fold on in A4, A5, A6.
  (first [ pose proof ((went_In_bounds _ _ _ a l0 HK (or_introl (or_introl eq_refl)))) as dR_3; dand6 dR_3 as _ B2 _ _ B5 B6 | pose proof (went_In_bounds _ _ _ a l0 HK (or_introl (or_introl eq_refl))) as (_ & B2 & _ & _ & B5 & B6) ]). fold on in B2, B5, B6.
  pose proof (bv_unsigned_in_range _ dst) as DR. change (bv_modulus 64) with (2^64) in DR. fold dZ in DR.
  assert (Ua : bv_unsigned (wz a) = a) by (apply unsigned_wz; lia).
  assert (Un : bv_unsigned (wz nd) = nd) by (apply unsigned_wz; unfold LEN_MAX in Hnd; lia).
  assert (Uon : bv_unsigned (wz on) = on) by (apply unsigned_wz; lia).
  assert (MMn : mmap_len nd = nd) by (apply mmap_len_of_aligned; lia).
  assert (Ewent : went dZ (mmap_len nd) = (dst, wz nd)) by (rewrite MMn, went_wz; unfold wz; subst dZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (kl_distinct _ _ _ HK) as Kd. cbn [set_groups ld_groups ld_metas map fst app] in Kd.
  inversion Kd as [|? ? Hni Kd1]; subst.
  assert (Hg0 : forall b l, In (b, l) G0 -> b <> a).
  { intros b l H ->. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l). auto. }
  assert (Hm0 : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
  { intros b l k H ->. apply Hni. apply in_or_app. right. apply in_map_iff. exists (a, l, k). auto. }
  (* [comment removed for export] *)
  assert (Dold : forall b l, (In (b, l) G0 \/ exists k, In (b, l, k) (ld_metas L)) ->
                 In (went b (mmap_len l)) (vm_maps h) /\ went b (mmap_len l) <> went a on /\ 0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= alloc_ceiling
                 /\ (b + mmap_len l <= a \/ a + on <= b)).
  { intros b l H.
    assert (H' : In (b, l) (ld_groups (set_groups ((a, l0) :: G0) L)) \/ exists k, In (b, l, k) (ld_metas (set_groups ((a, l0) :: G0) L))).
    { destruct H as [H|H]; [left; right; exact H| right; exact H]. }
    (first [ pose proof ((went_In_bounds _ _ _ b l HK H')) as dR_4; dand6 dR_4 as C1 C2 C3 C4 C5 C6 | pose proof (went_In_bounds _ _ _ b l HK H') as (C1 & C2 & C3 & C4 & C5 & C6) ]).
    assert (Hne : b <> a) by (destruct H as [H|[k H]]; [exact (Hg0 _ _ H)| exact (Hm0 _ _ _ H)]).
    assert (NEQ : went b (mmap_len l) <> went a on) by (intros E; apply Hne; apply (f_equal elo) in E; rewrite C5, B5 in E; exact E).
    split; [exact C4|]. split; [exact NEQ|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D]; [contradiction|].
    unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
  (* [comment removed for export] *)
  assert (SAMEBASE : forall e, In e (vm_maps h) -> fst e = wz a -> e = went a on).
  { intros e He E0. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [EE|D]; [exact EE|]. exfalso.
    assert (EL : elo e = a) by (unfold elo; rewrite E0; exact Ua).
    pose proof (proj1 (kl_wf _ _ _ HK) e He) as W. unfold edisj in D. rewrite B5, B6 in D. lia. }
  (* [comment removed for export] *)
  assert (NEW : forall e, In e (vm_maps h) -> e <> went a on -> dZ + nd <= elo e \/ ehi e <= dZ).
  { intros e He Hne.
    destruct CASE as [[-> [LT|RF]]|[NEd RF]].
    - subst dZ. rewrite Ua. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [E|D]; [contradiction|].
      unfold edisj in D. rewrite B5, B6 in D. lia.
    - pose proof (region_free_app_r _ _ _ _ RF) as RF'.
      assert (He' : In e (map_remove (vm_maps h) (wz a))).
      { unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) (wz a)) eqn:E; [| reflexivity]. exfalso.
        apply bv_eqb_eq in E. exact (Hne (SAMEBASE e He E)). }
      pose proof (region_free_disj _ _ _ _ RF' He') as D. subst dZ. rewrite Un in D. exact D.
    - pose proof (region_free_app_r _ _ _ _ RF) as RF'. pose proof (region_free_disj _ _ _ _ RF' He) as D. rewrite Un in D. exact D. }
  assert (DISJ : forall b l, (In (b, l) G0 \/ exists k, In (b, l, k) (ld_metas L)) -> dZ + nd <= b \/ b + mmap_len l <= dZ).
  { intros b l H. (first [ pose proof ((Dold b l H)) as dR_5; dand6 dR_5 as C4 NEQ _ _ _ C5 | destruct (Dold b l H) as (C4 & NEQ & _ & _ & _ & C5) ]). pose proof (went_In_bounds _ _ _ b l HK) as W.
    destruct (NEW _ C4 NEQ) as [X|X]; rewrite ?elo_went, ?ehi_went in X by (destruct (Dold b l H) as (_ & _ & ? & ? & ? & _); lia); lia. }
  assert (RFR : region_free (vm_reserved h) dst (wz nd) = true).
  { destruct CASE as [[-> [LT|RF]]|[NEd RF]]; [| exact (region_free_app_l _ _ _ _ RF)| exact (region_free_app_l _ _ _ _ RF)].
    eapply region_free_sub; [exact (kl_maps_resv _ _ _ HK _ A5)| cbn [fst went]; unfold KLink.wz; lia| cbn [fst snd went]; unfold KLink.wz; rewrite Un, Uon; lia| rewrite Un; lia]. }
  assert (DBRK : brk_disj L dZ nd).
  { intros b0 lb E. (first [ pose proof ((kl_brkreg _ _ _ HK b0 lb E)) as dR_6; dand6 dR_6 as R1 R2 R3 R4 R5 Rcov | pose proof (kl_brkreg _ _ _ HK b0 lb E) as (R1 & R2 & R3 & R4 & R5 & Rcov) ]).
    destruct (Z_le_gt_dec (dZ + nd) (b0 + PGSZ)) as [|H1]; [left; assumption|].
    destruct (Z_le_gt_dec (b0 + lb) dZ) as [|H2]; [right; assumption|]. exfalso.
    (first [ pose proof ((Rcov (Z.max dZ (b0 + PGSZ)) ltac:(unfold PGSZ in *; lia))) as dR_7; dex1 dR_7 as e; destruct dR_7 as [He Hr] | pose proof ((Rcov (Z.max dZ (b0 + PGSZ)) ltac:(unfold PGSZ in *; lia))) as dR_7; dand3 dR_7 as e He Hr | destruct (Rcov (Z.max dZ (b0 + PGSZ)) ltac:(unfold PGSZ in *; lia)) as (e & He & Hr) ]).
    assert (Hne : e <> went a on).
    { intros ->. rewrite B5, B6 in Hr. pose proof (A6 b0 lb E). unfold PGSZ in *. lia. }
    destruct (NEW e He Hne); unfold PGSZ in *; lia. }
  split; [| split; [exact DISJ| split; [exact DBRK| split; [exact RFR|]]]].
  2:{ intros NEd. destruct CASE as [[E _]|[_ RF]]; [exfalso; exact (NEd E)|].
      pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ RF) A5) as D. rewrite B5, B6, Un in D. subst dZ. lia. }
  (* [comment removed for export] *)
  assert (NA_other : forall e e', In e (vm_noaccess h) -> In e' (vm_maps h) -> elo e' <= elo e -> elo e < ehi e -> ehi e <= ehi e' -> e' <> went a on).
  { intros e e' He He' T1 T0 T2 ->. rewrite B5 in T1. rewrite B6 in T2.
    pose proof (kl_groups_na _ _ _ HK a l0 ltac:(left; reflexivity)) as GNA. fold on in GNA.
    pose proof (region_free_disj _ _ _ _ GNA He) as D. unfold KLink.wz in D. rewrite Ua, Uon in D. lia. }
  assert (INrm : forall e, In e (vm_maps h) -> e <> went a on -> In e (map_remove (vm_maps h) (wz a))).
  { intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) (wz a)) eqn:E; [| reflexivity]. exfalso.
    apply bv_eqb_eq in E. exact (Hne (SAMEBASE e He E)). }
  assert (RMin : forall e, In e (map_remove (vm_maps h) (wz a)) -> In e (vm_maps h) /\ e <> went a on).
  { intros e He. unfold map_remove in He. apply filter_In in He as [He E]. split; [exact He|]. intros ->. cbn [fst went] in E. unfold KLink.wz in E. rewrite bv_eqb_refl in E. discriminate. }
  assert (Hph' : phase_inv (ld_brk (set_groups ((dZ, nd) :: G0) L)) (set_groups ((dZ, nd) :: G0) L) pbrk mo').
  { eapply (phase_quiet (set_groups ((a, l0) :: G0) L)); [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]. }
  kl_open HK. constructor; try exact Hph'; rewrite ?Evm; unfold mremap_maps_next;
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live] in *; auto.
  - (* [comment removed for export] *) apply vmwf_cons; [apply vmwf_remove; exact Kwf| subst dZ; rewrite Un; unfold LEN_MAX in Hnd; lia|].
    apply region_free_intro. intros b s Hin. destruct (RMin _ Hin) as [Hin' Hne]. pose proof (NEW _ Hin' Hne) as D. unfold elo, ehi in D. cbn [fst snd] in D. subst dZ. rewrite Un. lia.
  - (* [comment removed for export] *) intros b l [E|Hin].
    + injection E as <- <-. rewrite MMn. rewrite MMn in Ewent. rewrite Ewent. unfold LEN_MAX in *. unfold PGSZ.
      split; [lia|]. split; [lia|]. split; [exact DA|]. split; [lia|]. split; [left; reflexivity| exact DBRK].
    + (first [ pose proof ((Kgr b l (or_intror Hin))) as dR_8; dand6 dR_8 as G1 G2 G3 G4 G5 G6 | destruct (Kgr b l (or_intror Hin)) as (G1 & G2 & G3 & G4 & G5 & G6) ]). splits; auto; try lia.
      right. apply INrm; [exact G5|]. exact (proj1 (proj2 (Dold b l (or_introl Hin)))).
  - (* [comment removed for export] *) intros b l k Hin. (first [ pose proof ((Kme b l k Hin)) as dR_9; dand9 dR_9 as G1 G2 G3 G4 G5 G6 G7 G8 G9 | destruct (Kme b l k Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9) ]). splits; auto; try lia.
    right. apply INrm; [exact G7|]. exact (proj1 (proj2 (Dold b l (or_intror (ex_intro _ k Hin))))).
  - (* [comment removed for export] *) cbn [map fst app]. constructor; [| exact Kd1]. intros Hin. apply in_app_or in Hin as [Hin|Hin].
    + apply in_map_iff in Hin as ([b l] & E & Hin). cbn in E. subst b. (first [ pose proof ((Dold dZ l (or_introl Hin))) as dR_10; dand5 dR_10 as _ _ _ P0 _ | destruct (Dold dZ l (or_introl Hin)) as (_ & _ & _ & P0 & _) ]).
      destruct (DISJ dZ l (or_introl Hin)); lia.
    + apply in_map_iff in Hin as ([[b l] k] & E & Hin). cbn in E. subst b. (first [ pose proof ((Dold dZ l (or_intror (ex_intro _ k Hin)))) as dR_11; dand5 dR_11 as _ _ _ P0 _ | destruct (Dold dZ l (or_intror (ex_intro _ k Hin))) as (_ & _ & _ & P0 & _) ]).
      destruct (DISJ dZ l (or_intror (ex_intro _ k Hin))); lia.
  - (* [comment removed for export] *) intros b0 lb E. (first [ pose proof ((Kreg b0 lb E)) as dR_12; dand6 dR_12 as R1 R2 R3 R4 R5 Rcov | destruct (Kreg b0 lb E) as (R1 & R2 & R3 & R4 & R5 & Rcov) ]). splits; auto.
    intros x Hx. (first [ pose proof ((Rcov x Hx)) as dR_13; dex1 dR_13 as e; destruct dR_13 as [He Hr] | pose proof ((Rcov x Hx)) as dR_13; dand3 dR_13 as e He Hr | destruct (Rcov x Hx) as (e & He & Hr) ]). exists e. split; [| exact Hr]. right. apply INrm; [exact He|].
    intros ->. rewrite B5, B6 in Hr. pose proof (A6 b0 lb E). unfold PGSZ in *. lia.
  - (* [comment removed for export] *) intros e [<-|He]; [exact RFR| apply Kmr; exact (proj1 (RMin e He))].
  - (* [comment removed for export] *) intros e He. (first [ pose proof ((Knc e He)) as dR_14; dex1 dR_14 as e'; dand4 dR_14 as He' T1 T0 T2 | pose proof ((Knc e He)) as dR_14; dand5 dR_14 as e' He' T1 T0 T2 | destruct (Knc e He) as (e' & He' & T1 & T0 & T2) ]). exists e'. split; [| auto].
    right. apply INrm; [exact He'|]. exact (NA_other e e' He He' T1 T0 T2).
  - (* [comment removed for export] *) intros b l [E|Hin]; [| exact (Kgna b l (or_intror Hin))]. injection E as <- <-. rewrite MMn.
    replace (KLink.wz dZ) with dst by (unfold KLink.wz; subst dZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
    apply region_free_intro. intros b s Hp. (first [ pose proof ((Knc (b, s) Hp)) as dR_15; dex1 dR_15 as e'; dand4 dR_15 as He' T1 T0 T2 | pose proof ((Knc (b, s) Hp)) as dR_15; dand5 dR_15 as e' He' T1 T0 T2 | destruct (Knc (b, s) Hp) as (e' & He' & T1 & T0 & T2) ]).
    pose proof (NA_other _ _ Hp He' T1 T0 T2) as Hne. pose proof (NEW e' He' Hne) as D.
    unfold elo, ehi in T1, T0, T2, D. cbn [fst snd] in T1, T0, T2. subst dZ. unfold KLink.wz. rewrite Un. lia.
  - (* [comment removed for export] *) intros e [<-|He].
    + left. exists dZ, nd. split; [left; reflexivity|]. rewrite MMn. rewrite MMn in Ewent. symmetry. exact Ewent.
    + destruct (RMin e He) as [He' Hne]. destruct (Kcpl e He') as [(b & l & [E|Hin] & Ee)|[X|X]]; [| | right; left; exact X| right; right; exact X].
      * exfalso. injection E as <- <-. apply Hne. exact Ee.
      * left. exists b, l. split; [right; exact Hin| exact Ee].
  - (* [comment removed for export] *) unfold ceil_ok. rewrite Evm. unfold mremap_maps_next. rewrite alloc_top_mkVmMapsFull.
    pose proof Kceil as Kc'. unfold ceil_ok, alloc_top in Kc'. exact Kc'.
Qed.

End CEIL.
End KLinkR.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL.
