(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mremap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_Simrel.
Module KB_Realloc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.NodesSoundDec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_Simrel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_app_In_both {A} : forall (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros l1 l2 x Hnd H1 H2. apply in_split in H1 as (la & lb & ->). rewrite <- app_assoc in Hnd. cbn [app] in Hnd.
  apply (List.NoDup_remove_2 _ _ _ Hnd). apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

Lemma region_free_mono : forall l1 l2 a n, (forall e, In e l1 -> In e l2) -> region_free l2 a n = true -> region_free l1 a n = true.
Proof.
  intros l1 l2 a n Hs Hrf. apply region_free_intro. intros b sz Hin. eapply region_free_In; [exact Hrf| apply Hs; exact Hin].
Qed.

Theorem KL_unmap : forall L pbrk mo mo' b l,
  KL L pbrk mo -> brk_quiet L -> In (b, l) (ld_groups L) ->
  let h := m_vmmaps mo in let n := mmap_len l in
  m_vm_lazy mo' = [] -> m_vm_materialized mo' = [] ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 b)) (vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KL (set_groups (g_remove b (ld_groups L)) L) pbrk mo'
  /\ region_free (vm_reserved h ++ map_remove (vm_maps h) (Z_to_bv 64 b)) (Z_to_bv 64 b) (Z_to_bv 64 n) = true
  /\ (forall e, In e (vm_maps h) -> e = went b n \/ In e (map_remove (vm_maps h) (Z_to_bv 64 b))).
Proof.
  intros L pbrk mo mo' a l0 HK Hq Hin h n Hl' Hm' Evm. pose proof alloc_ceiling_lt as Hcl.
  pose proof (kl_groups _ _ _ HK a l0 Hin) as ([A0 A1] & A2 & A3 & A4 & A5 & A6 & A7).
  pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6). fold n h in A4, A5, A6, A7, B2, B5, B6.
  set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
  pose proof (kl_distinct _ _ _ HK) as Kd.
  destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
  rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
  pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
  assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
  { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
    intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
  assert (Hm'' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
  { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
  assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                   b + mmap_len l <= a \/ a + n <= b).
  { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
    destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
    - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
    - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
  assert (Hph' : phase_inv (ld_brk (set_groups (g_remove a (ld_groups L)) L)) (set_groups (g_remove a (ld_groups L)) L) pbrk mo')
    by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
  assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
  { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_lit, Ua in E by lia. exact E. }
  assert (Hkeep : forall e, In e (vm_maps h) -> fst e <> aw -> In e (map_remove (vm_maps h) aw)).
  { intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction. }
  (* [comment removed for export] *)
  assert (Hsplit : forall e, In e (vm_maps h) -> e = went a n \/ In e (map_remove (vm_maps h) aw)).
  { intros e He. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [->|D]; [left; reflexivity| right].
    apply Hkeep; [exact He|]. intros E.
    pose proof (proj1 (kl_wf _ _ _ HK) e He) as W. unfold edisj in D. rewrite B5, B6 in D. unfold elo, ehi in D, W. rewrite E, Ua in D, W. lia. }
  split; [| split; [| exact Hsplit]].
  2:{ apply region_free_intro_Z. rewrite Ua, Un. intros e He. apply in_app_or in He as [He|He].
      - pose proof (A7 e He). lia.
      - unfold map_remove in He. apply filter_In in He as [He Hne].
        destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He A5) as [->|D].
        + exfalso. cbn [fst went] in Hne. fold aw in Hne. rewrite bv_eqb_refl in Hne. discriminate.
        + unfold edisj in D. rewrite B5, B6 in D. lia. }
  kl_open HK. constructor; try exact Hph'; try assumption; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; try assumption.
  - apply vmwf_remove. exact Kwf.
  - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7). refine (conj (conj G0 G1) (conj G2 (conj G3 (conj G4 (conj _ (conj G6 G7)))))).
    apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge' l1 G0). lia.
  - intros b0 l1 k Hin0. pose proof (Hm'' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    refine (conj (conj G0 G1) (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj _ (conj G8 G9)))))))).
    apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge' l1 G0). lia.
  - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
  - intros b0 l1 E. specialize (Kreg b0 l1 E). destruct Kreg as (R1 & R2 & R3 & R4 & R5 & R6 & Rcov). refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 _)))))).
    intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
    intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
    destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
    + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
    + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. fold aw nw in D. rewrite Un in D. clear -D W B2. lia.  (* [comment removed for export] *)
  - intros e He. destruct (Kna e He) as [W Hc]. split; [exact W|].
    destruct Hc as [(b0 & l9 & k & Hin0 & Hlo & Hhi)|(b0 & l9 & E & Hlo & Hhi & Hin0)].
    + left. exists b0, l9, k. auto.
    + right. exists b0, l9. refine (conj E (conj Hlo (conj Hhi _))).
      apply Hkeep; [exact Hin0|]. intros Efst. unfold brk_disj in A6. specialize (A6 b0 l9 E).
      pose proof (Kreg b0 l9 E) as (R1 & R2 & R3 & R4 & R5 & _).
      destruct (u64_went b0 (2 * PGSZ) ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia)) as [U1 U2].
      destruct (pwdisj_In _ _ _ (proj2 Kwf) Hin0 A5) as [Ee|D].
      * apply (f_equal ehi) in Ee. rewrite B6, U2 in Ee.
        apply (f_equal bv_unsigned) in Efst. change (elo (went b0 (2 * PGSZ)) = bv_unsigned aw) in Efst. rewrite U1, Ua in Efst. clear -Ee Efst A6 R3 B2. unfold PGSZ in *. lia.
      * unfold edisj in D. rewrite U1, U2, B5, B6 in D.
        apply (f_equal bv_unsigned) in Efst. change (elo (went b0 (2 * PGSZ)) = bv_unsigned aw) in Efst. rewrite U1, Ua in Efst. clear -D Efst R3 B2. unfold PGSZ in *. lia.
  - intros e He. unfold map_remove in He. apply filter_In in He as [He Hne].
    destruct (Kcov e He) as [(b0 & l1 & Hin0 & ->)|[(b0 & l1 & k & Hin0 & ->)|B]]; [| right; left; exists b0, l1, k; auto| right; right; exact B].
    left. exists b0, l1. split; [|reflexivity]. rewrite Ezz. rewrite Eg in Hin0. apply in_app_or in Hin0 as [H0|[H0|H0]]; [apply in_or_app; left; exact H0| | apply in_or_app; right; exact H0].
    exfalso. injection H0 as -> ->. cbn [fst went] in Hne. fold aw in Hne. rewrite bv_eqb_refl in Hne. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition L_remap (L : mled) (b d nn : Z) : mled := set_groups ((d, nn) :: g_remove b (ld_groups L)) L.

Theorem KL_remap : forall L pbrk mo mo1 b l d nn,
  KL L pbrk mo -> brk_quiet L -> In (b, l) (ld_groups L) ->
  0 < nn < LEN_MAX -> nn mod 4096 = 0 -> 0 < d -> d mod 4096 = 0 -> d + nn <= alloc_ceiling ->
  let h := m_vmmaps mo in
  region_free (vm_reserved h ++ map_remove (vm_maps h) (Z_to_bv 64 b)) (Z_to_bv 64 d) (Z_to_bv 64 nn) = true ->
  m_vm_lazy mo1 = [] -> m_vm_materialized mo1 = [] ->
  m_vmmaps mo1 = mremap_maps_next h (Z_to_bv 64 b) (Z_to_bv 64 d) (Z_to_bv 64 nn) ->
  KL (L_remap L b d nn) pbrk mo1.
Proof.
  intros L pbrk mo mo1 b l d nn HK Hq Hin Hnn Hnna Hd Hda Hce h Hrf Hl1 Hm1 Evm1.
  set (h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 b)) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
  set (mo' := with_vmmaps h' mo).
  assert (Hl' : m_vm_lazy mo' = []) by (subst mo'; rewrite m_vm_lazy_with_vmmaps; exact (kl_lazy _ _ _ HK)).
  assert (Hm' : m_vm_materialized mo' = []) by (subst mo'; rewrite m_vm_materialized_with_vmmaps; exact (kl_mat _ _ _ HK)).
  assert (Evm' : m_vmmaps mo' = h') by (subst mo'; apply m_vmmaps_with_vmmaps).
  destruct (KL_unmap L pbrk mo mo' b l HK Hq Hin Hl' Hm' Evm') as (HK' & _ & _).
  assert (Hml : mmap_len nn = nn) by (apply NodesSound.mmap_len_of_aligned; exact Hnna).
  destruct (KL_mmap_new (set_groups (g_remove b (ld_groups L)) L) pbrk mo' mo1 d nn false HK') as [HK1 _];
    rewrite ?Evm', ?Hml; try assumption.
  all: try (unfold brk_quiet in *; cbn; exact Hq).
  all: try lia.
  all: try (rewrite Evm1; reflexivity).
  all: try exact HK1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma KL_rf_lranges : forall L pbrk mo a n,
  KL L pbrk mo ->
  let h := m_vmmaps mo in
  0 <= a -> 0 < n -> a + n <= alloc_ceiling ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  ranges_free (lranges L) a n = true.
Proof.
  intros L pbrk mo a n HK h Ha Hn Hce Hrf. pose proof alloc_ceiling_lt as Hcl.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & R6 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (a + n <= lo \/ lo + m <= a) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  pose proof (lranges_rf_disj L pbrk mo lo m (Z_to_bv 64 a) (Z_to_bv 64 n) HK Hrf ltac:(rewrite Un; lia)) as D. rewrite Ua, Un in D.
  apply D; [exact Dbrk| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma region_free_but_self : forall L pbrk mo b l a n,
  KL L pbrk mo -> In (b, l) (ld_groups L) ->
  let h := m_vmmaps mo in let on := mmap_len l in
  0 <= a -> 0 < n -> a + n < 2^64 -> (a + n <= b \/ b + on <= a) ->
  region_free (vm_reserved h ++ map_remove (vm_maps h) (Z_to_bv 64 b)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  intros L pbrk mo b l a n HK Hin h on Ha Hn Han Hd Hrf. pose proof alloc_ceiling_lt as Hcl.
  pose proof (went_In_bounds _ _ _ b l HK (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). fold on h in B2, B3, B4, B5, B6.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  apply region_free_intro_Z. rewrite Ua, Un. intros e He. apply in_app_or in He as [He|He].
  - pose proof (region_free_disj _ _ _ _ Hrf (in_or_app _ _ _ (or_introl He))) as D. rewrite Ua, Un in D. exact D.
  - destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He B4) as [->|D].
    + rewrite B5, B6. lia.
    + assert (Hin' : In e (map_remove (vm_maps h) (Z_to_bv 64 b))).
      { unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) (Z_to_bv 64 b)) eqn:E; [|reflexivity]. exfalso.
        apply bv_eqb_eq in E. pose proof (proj1 (kl_wf _ _ _ HK) e He) as W. unfold edisj in D. rewrite B5, B6 in D.
        unfold elo, ehi in D, W. rewrite E in D, W. change (bv_unsigned (Z_to_bv 64 b)) with (elo (went b on)) in D, W. rewrite B5 in D, W. lia. }
      pose proof (region_free_disj _ _ _ _ Hrf (in_or_app _ _ _ (or_intror Hin'))) as D2. rewrite Ua, Un in D2. exact D2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition remap_post (L : mled) (b on nn : Z) (s0 : PState) (mo0 : Model) : mremap_ans -> PState -> Model -> Prop :=
  fun a s mo => s = s0 /\ vm_only mo0 mo /\
    match a with
    | MrErr e => e = ENOMEM /\ KL L (ps_brk s0) mo
    | MrInPlace => KL (L_remap L b b nn) (ps_brk s0) mo
                   /\ (on < nn -> b + nn <= alloc_ceiling /\ ranges_free (lranges L) (b + on) (nn - on) = true)
    | MrMoved d => d <> b /\ 0 < d /\ d mod PGSZ = 0 /\ d + nn <= alloc_ceiling /\ ranges_free (lranges L) d nn = true
                   /\ KL (L_remap L b d nn) (ps_brk s0) mo
    end.

Theorem remap_node_spec : forall L s0 mo0 b l nn,
  brk_quiet L -> In (b, l) (ld_groups L) ->
  let on := mmap_len l in
  on <> nn -> 0 < nn < LEN_MAX -> nn mod 4096 = 0 ->
  mspec (fun s mo => s = s0 /\ mo = mo0 /\ KL L (ps_brk s) mo)
        (msys (NMremap b on nn Realloc.MREMAP_MAYMOVE) (dec_mremap b on nn []))
        (remap_post L b on nn s0 mo0).
Proof.
  intros L s0 mo0 b l nn Hq Hin on Hne Hnn Hnna. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_sys; [reflexivity|].
  intros s mo (-> & -> & HK).
  pose proof (kl_groups _ _ _ HK b l Hin) as ([A0 A1] & A2 & A3 & A4 & A5 & A6 & A7). fold on in A4, A5, A6, A7.
  pose proof (went_In_bounds _ _ _ b l HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6). fold on in B2, B5, B6.
  set (h := m_vmmaps mo0) in *. set (bw := Z_to_bv 64 b) in *. set (onw := Z_to_bv 64 on) in *. set (nnw := Z_to_bv 64 nn) in *.
  assert (Ub : bv_unsigned bw = b) by (subst bw; apply unsigned_lit; lia).
  assert (Uon : bv_unsigned onw = on) by (subst onw; apply unsigned_lit; lia).
  assert (Unn : bv_unsigned nnw = nn) by (subst nnw; apply unsigned_lit; unfold LEN_MAX in Hnn; lia).
  assert (Hmo : mmap_len on = on) by (apply NodesSound.mmap_len_of_aligned; apply NodesSound.mmap_len_aligned).
  assert (Hmn : mmap_len nn = nn) by (apply NodesSound.mmap_len_of_aligned; exact Hnna).
  assert (Hhas : map_has (vm_maps h) bw onw = true).
  { unfold map_has. apply existsb_exists. exists (went b on). split; [exact A5|]. unfold went. fold bw onw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  assert (Hrfr : region_free (vm_reserved h) bw onw = true).
  { apply region_free_intro_Z. rewrite Ub, Uon. intros e He. exact (A7 e He). }
  assert (Hrfn : region_free (vm_noaccess h) bw onw = true).
  { apply region_free_intro_Z. rewrite Ub, Uon. intros e He. destruct (kl_na _ _ _ HK e He) as [W [(b1 & l1 & k1 & Hin1 & Hlo & Hhi)|(b1 & l1 & E & Hlo & Hhi & Hin1)]].
    - pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k1 Hin1))) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [Ee|D].
      + exfalso. apply (f_equal elo) in Ee. rewrite C5, B5 in Ee. subst b1.
        pose proof (kl_distinct _ _ _ HK) as Kd. apply (NoDup_app_In_both _ _ _ Kd (in_map fst _ _ Hin)).
        apply in_map_iff. exists (b, l1, k1). auto.
      + unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia.
    - unfold brk_disj in A6. specialize (A6 b1 l1 E). pose proof (kl_brkreg _ _ _ HK b1 l1 E) as (R1 & R2 & R3 & R4 & R5 & _).
      assert (Hb1 : 0 <= b1 < 2^64) by (clear -R1 R3 R5 Hcl; unfold PGSZ in *; lia).
      assert (H2p : 0 <= 2 * PGSZ < 2^64) by (unfold PGSZ; lia).
      destruct (u64_went b1 (2 * PGSZ) Hb1 H2p) as [U1 U2].
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) Hin1 A5) as [Ee|D].
      + exfalso. pose proof (f_equal elo Ee) as E1. apply (f_equal ehi) in Ee. rewrite U1, B5 in E1. rewrite U2, B6 in Ee. clear -E1 Ee A6 R3 B2. unfold PGSZ in *. lia.
      + unfold edisj in D. rewrite U1, U2, B5, B6 in D. clear -D Hlo Hhi R3. unfold PGSZ in *. lia. }
  split.
  { cbn [nsafe]. rewrite page_size_eq. change (page_round_up_Z on) with (mmap_len on). change (page_round_up_Z nn) with (mmap_len nn). rewrite Hmo, Hmn, (kl_top _ _ _ HK). fold h bw onw.
    unfold PGSZ in A3. split; [reflexivity|]. split; [lia|]. split; [exact A3|]. split; [lia|]. split; [lia|].
    split; [unfold LEN_MAX in *; lia|]. split; [exact A4|]. exact (conj Hrfr (conj Hhas Hrfn)). }
  intros rsp mo' Hst.
  pose proof (anstep_books _ _ _ _ (kl_lazy _ _ _ HK) (kl_mat _ _ _ HK) Hst) as (Hl' & Hm' & Hvo).
  replace Realloc.MREMAP_MAYMOVE with Uapi.MREMAP_MAYMOVE in Hst by reflexivity.
  pose proof (anstep_dec_mremap mo0 b on nn [] rsp mo' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hmo; exact A4) (Forall_nil _)
                ltac:(rewrite (kl_top _ _ _ HK); lia) Hst) as (x & Hd & Hx).
  rewrite Hmo, Hmn in Hx. fold h bw onw nnw in Hx.
  exists x. split; [exact Hd|]. split; [reflexivity|]. split; [exact Hvo|].
  destruct x as [e| |d].
  - destruct Hx as (-> & -> & _). split; [reflexivity| exact HK].
  - destruct Hx as [[E _]|(_ & Hgrow & Evm)]; [exfalso; exact (Hne E)|].
    (* [comment removed for export] *)
    assert (Hrf : region_free (vm_reserved h ++ map_remove (vm_maps h) bw) bw nnw = true /\ b + nn <= alloc_ceiling).
    { destruct (Z.lt_ge_cases on nn) as [Hlt|Hge].
      - specialize (Hgrow Hlt). unfold mremap_inplace_grow_b in Hgrow. fold h in Hgrow. rewrite Ub in Hgrow.
        apply andb_prop in Hgrow as [Hgrow _]. apply andb_prop in Hgrow as [Hce Hrf]. apply Z.leb_le in Hce. rewrite (kl_top _ _ _ HK) in Hce. auto.
      - split; [| lia].
        set (h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) bw) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
        destruct (KL_unmap L (ps_brk s0) mo0 (with_vmmaps h' mo0) b l HK Hq Hin) as (_ & Hrf0 & _);
          [rewrite m_vm_lazy_with_vmmaps; exact (kl_lazy _ _ _ HK)| rewrite m_vm_materialized_with_vmmaps; exact (kl_mat _ _ _ HK)| apply m_vmmaps_with_vmmaps|].
        fold h on bw onw in Hrf0. apply region_free_intro_Z. rewrite Ub, Unn. intros e He.
        pose proof (region_free_disj _ _ _ _ Hrf0 He) as D. rewrite Ub, Uon in D. lia. }
    destruct Hrf as [Hrf Hce]. split.
    + apply (KL_remap L (ps_brk s0) mo0 mo' b l b nn HK Hq Hin Hnn Hnna ltac:(lia) ltac:(unfold PGSZ in A3; exact A3) Hce Hrf Hl' Hm' Evm).
    + intros Hlt. split; [exact Hce|].
      apply (KL_rf_lranges L (ps_brk s0) mo0 (b + on) (nn - on) HK); [lia| lia| lia|].
      apply (region_free_but_self L (ps_brk s0) mo0 b l (b + on) (nn - on) HK Hin); [lia| lia| lia| right; lia|].
      fold h bw. apply region_free_intro_Z. rewrite !unsigned_lit by lia. intros e He.
      pose proof (region_free_disj _ _ _ _ Hrf He) as D. rewrite Ub, Unn in D. lia.
  - destruct Hx as (Hlt & Hdb & Hok & Hfresh & Evm).
    unfold mremap_fresh_b in Hfresh. fold h in Hfresh.
    apply andb_prop in Hfresh as [Hfresh _]. apply andb_prop in Hfresh as [Hfresh Hrf]. apply andb_prop in Hfresh as [Hfresh Hce].
    apply andb_prop in Hfresh as [Hfresh Hpos]. apply andb_prop in Hfresh as [_ Hal].
    apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Hce. rewrite page_size_eq in Hal. rewrite (kl_top _ _ _ HK) in Hce.
    assert (Ud : bv_unsigned (Z_to_bv 64 d) = d).
    { unfold mmap_addr_ok in Hok. apply andb_prop in Hok as [Hok _]. apply andb_prop in Hok as [Hok Hce']. apply andb_prop in Hok as [_ Hok]. apply Z.ltb_lt in Hok.
      apply Z.leb_le in Hce'. pose proof (NodesSound.mmap_len_ge nn).
      apply unsigned_lit. lia. }
    rewrite Ud in Hal, Hpos, Hce.
    assert (Hrf' : region_free (vm_reserved h ++ map_remove (vm_maps h) bw) (Z_to_bv 64 d) nnw = true).
    { eapply region_free_mono; [| exact Hrf]. intros e He. apply in_app_or in He as [He|He]; apply in_or_app; [left; exact He| right].
      unfold map_remove in He. apply filter_In in He as [He _]. exact He. }
    refine (conj Hdb (conj Hpos (conj _ (conj Hce (conj _ _))))).
    + unfold PGSZ. exact Hal.
    + apply (KL_rf_lranges L (ps_brk s0) mo0 d nn HK); [lia| lia| lia| exact Hrf].
    + apply (KL_remap L (ps_brk s0) mo0 mo' b l d nn HK Hq Hin Hnn Hnna Hpos Hal Hce Hrf' Hl' Hm' Evm).
Qed.


End CeilWrap.
End KB_Realloc.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
Module KRawR.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.NodesSoundDec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.KStep3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_Simrel.
Import KB_Realloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Import Realloc.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation SIMREL := MI_Contracts.SIMREL.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition addr_in_slot (cs : mstate) (c : cptr) (A : Z) : Prop :=
  forall g idx, s_slots cs !! c = Some (g, idx) -> 0 <= A - conc cs c <= get_stride (get_meta_rec cs g).

Definition rr_plan_facts : Prop :=
  forall cs L c A n, SIMREL cs L -> In c (ld_live L) -> 0 <= n < 2^32 -> addr_in_slot cs c A ->
  match rplan_of cs c A n with
  | RPUndef => False
  | RPRemap rid g base on nn =>
      (exists l, In (base, l) (ld_groups L) /\ on = mmap_len l) /\ 0 < nn < LEN_MAX /\ nn mod 4096 = 0
  | _ => True
  end.

Definition rr_remap_facts : Prop :=
  forall cs L c A n rid g base on nn d, SIMREL cs L -> In c (ld_live L) -> 0 <= n < 2^32 -> addr_in_slot cs c A ->
  rplan_of cs c A n = RPRemap rid g base on nn -> on <> nn ->
  0 < d -> d mod PGSZ = 0 -> d + nn <= alloc_ceiling ->
  ((d = base /\ (on < nn -> ranges_free (live_ranges cs) (base + on) (nn - on) = true))
   \/ ranges_free (live_ranges cs) d nn = true) ->
  SIMREL (cs_remap cs rid g d nn) (L_remap L base d nn).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma simrel_brk_quiet : forall cs L, SIMREL cs L -> brk_quiet L.
Proof.
  intros cs L (st & BL & LS & _ & INV & _). pose proof (ir_brk _ _ _ (proj1 INV)) as HB.
  unfold brk_quiet. destruct (c_brk (s_ctx st)).
  - destruct HB as [E _]. rewrite E. exact I.
  - rewrite HB. exact I.
  - destruct HB as [E _]. rewrite E. exact I.
Qed.

Lemma ap_remove_cons_neq : forall c q X, q <> c -> ap_remove c (q :: X) = q :: ap_remove c X.
Proof.
  intros c q X Hne. cbn. destruct (aptr_eqb q c) eqn:E; [|reflexivity]. apply MI_Kit.aptr_eqb_eq in E. contradiction.
Qed.

Lemma perm_cons_ap_remove : forall c X, List.NoDup X -> In c X -> Permutation X (c :: ap_remove c X).
Proof.
  intros c X. induction X as [|y X IH]; intros ND Hin; [destruct Hin|]. inversion ND; subst. cbn.
  destruct (aptr_eqb y c) eqn:E.
  - apply MI_Kit.aptr_eqb_eq in E. subst y. apply Permutation_refl.
  - destruct Hin as [->|Hin]; [rewrite MI_Kit.aptr_eqb_refl in E; discriminate|].
    apply (Permutation_trans (perm_skip y (IH H2 Hin))). apply perm_swap.
Qed.

Lemma AOWN_self : forall X s mo c, AOWN X s mo -> In c X -> AOWN (c :: ap_remove c X) s mo /\ ~ In c (ap_remove c X).
Proof.
  intros X s mo c HO Hin. pose proof (proj2 HO) as ND. split.
  - eapply AOWN_perm; [apply perm_cons_ap_remove; [exact ND| exact Hin]| exact HO].
  - apply ap_remove_notin_self. exact ND.
Qed.

Lemma ld_live_L_remap : forall L b d nn, ld_live (L_remap L b d nn) = ld_live L.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raw_realloc_post (X : list cptr) (s0 : PState) (mo0 : Model) (c : cptr)
  : option bptr -> PState -> Model -> Prop :=
  fun r s' mo' =>
    match r with
    | Some q => AOWN (fst q :: ap_remove c X) s' mo' /\ ~ In (fst q) (ap_remove c X)
    | None => AOWN X s' mo'
    end
    /\ ps_fa s' = ps_fa s0 /\ ps_so s' = ps_so s0 /\ vm_only mo0 mo'.

(* [comment removed for export] *)
Lemma rr_fallback_own : forall X s0 mo0 mo1 (p : bptr) n,
  AOWN X s0 mo1 -> In (fst p) X -> 0 <= n -> vm_only mo0 mo1 ->
  mspec (fun s mo => s = s0 /\ mo = mo1) (rr_fallback p n) (raw_realloc_post X s0 mo0 (fst p)).
Proof.
  intros X s0 mo0 mo1 p n HO Hin Hn Hvo. unfold rr_fallback.
  eapply mspec_bind; [apply (raw_malloc_own X s0 mo1 n HO Hn)|].
  intros [q|]; cbn beta iota.
  - apply mspec_pointwise. intros s2 mo2 ((HO2 & Hni & _ & _) & Hfa & Hso & Hvo2).
    assert (Hin2 : In (fst p) (fst q :: X)) by (right; exact Hin).
    eapply mspec_seq.
    + eapply mspec_post; [apply (raw_free_own (fst q :: X) s2 mo2 p HO2 Hin2)|]. intros a s mo H. exact H.
    + intros []. apply mspec_ret. intros s mo (HO3 & Hni3 & Hfa3 & Hso3 & Hvo3).
      assert (Hne : fst q <> fst p) by (intros E; apply Hni; rewrite E; exact Hin).
      rewrite (ap_remove_cons_neq _ _ _ Hne) in HO3, Hni3.
      split; [split; [exact HO3|]|].
      * intros Hq. apply Hni. eapply ap_remove_In. exact Hq.
      * rewrite Hfa3, Hso3. splits; [exact Hfa| exact Hso|].
        eapply vm_only_trans; [exact Hvo|]. eapply vm_only_trans; [exact Hvo2| exact Hvo3].
  - apply mspec_ret. intros s mo (HO2 & Hfa & Hso & Hvo2). split; [exact HO2|]. splits; [exact Hfa| exact Hso|].
    eapply vm_only_trans; [exact Hvo| exact Hvo2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RawRealloc.
Hypothesis PF : rr_plan_facts.
Hypothesis RF : rr_remap_facts.

Theorem raw_realloc_own : forall X s0 mo0 (p : bptr) A n,
  AOWN X s0 mo0 -> In (fst p) X -> 0 <= n < 2^32 -> addr_in_slot (ps_m s0) (fst p) A ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_realloc p A n) (raw_realloc_post X s0 mo0 (fst p)).
Proof.
  intros X s0 mo0 p A n HO Hin Hn HA. pose proof alloc_ceiling_lt as Hcl.
  pose proof HO as [(L & SR & HK & Hincl) ND].
  assert (Hlive : In (fst p) (ld_live L)) by (apply Hincl; exact Hin).
  pose proof (PF (ps_m s0) L (fst p) A n SR Hlive Hn HA) as HPF.
  unfold raw_realloc.
  eapply mspec_pre with (P := fun s mo => s = s0 /\ mo = mo0); [| intros s mo H; exact H].
  apply (mspec_get_bind_eq s0 (fun _ mo => mo = mo0)).
  destruct (rplan_of (ps_m s0) (fst p) A n) as [|rid g base on nn| |] eqn:EP.
  - (* [comment removed for export] *)
    apply mspec_ret. intros s mo [-> ->]. split; [exact (AOWN_self X s0 mo0 (fst p) HO Hin)|]. splits; [reflexivity| reflexivity| apply vm_only_refl].
  - (* [comment removed for export] *)
    destruct HPF as ((l & Hgl & Hon) & Hnn & Hnna). subst on.
    apply mspec_if; intros Eon.
    { apply mspec_ret. intros s mo [-> ->]. split; [exact (AOWN_self X s0 mo0 (fst p) HO Hin)|]. splits; [reflexivity| reflexivity| apply vm_only_refl]. }
    apply Z.eqb_neq in Eon.
    pose proof (simrel_brk_quiet _ _ SR) as Hq.
    pose proof (kl_groups _ _ _ HK base l Hgl) as ([G0 G1] & G2 & G3 & G4 & _).
    eapply mspec_bind.
    { eapply mspec_pre; [apply (remap_node_spec L s0 mo0 base l nn Hq Hgl); [exact Eon| exact Hnn| exact Hnna]|].
      intros s mo [-> ->]. cbn [ps_brk]. auto. }
    intros a. unfold remap_post. cbn beta.
    destruct a as [e| |d].
    + (* [comment removed for export] *)
      apply mspec_pointwise. intros s mo (-> & Hvo & -> & HK1).
      apply (rr_fallback_own X s0 mo0 mo p n); [| exact Hin| lia| exact Hvo].
      split; [| exact ND]. exists L. auto.
    + (* [comment removed for export] *)
      apply mspec_pointwise. intros s mo (-> & Hvo & HK1 & Hgrow).
      assert (Hok : remap_grow_ok (ps_m s0) base (mmap_len l) nn = true).
      { unfold remap_grow_ok. destruct (Z.leb_spec nn (mmap_len l)) as [Hle|Hlt]; [reflexivity|]. cbn [orb].
        destruct (Hgrow Hlt) as [Hce Hrf]. rewrite (proj2 (Z.leb_le _ _) Hce). cbn [andb].
        rewrite (live_ranges_free_lranges _ _ _ _ SR). exact Hrf. }
      rewrite Hok.
      assert (SR' : SIMREL (cs_remap (ps_m s0) rid g base nn) (L_remap L base base nn)).
      { apply (RF (ps_m s0) L (fst p) A n rid g base (mmap_len l) nn base SR Hlive Hn HA EP Eon G2); [unfold PGSZ; exact G3| |].
        - destruct (Z.lt_ge_cases (mmap_len l) nn) as [Hlt|Hge]; [exact (proj1 (Hgrow Hlt))| lia].
        - left. split; [reflexivity|]. intros Hlt. rewrite (live_ranges_free_lranges _ _ _ _ SR). exact (proj2 (Hgrow Hlt)). }
      eapply mspec_seq with (R := fun s mo' => s = set_m (cs_remap (ps_m s0) rid g base nn) s0 /\ mo' = mo).
      { apply mspec_upd'. intros s mo' [-> ->]. auto. }
      intros []. apply mspec_ret. intros s mo' [-> ->]. cbn [ps_m ps_brk ps_fa ps_so set_m].
      split; [| splits; [reflexivity| reflexivity| exact Hvo]].
      apply (AOWN_self X). 2: exact Hin.
      split; [| exact ND]. exists (L_remap L base base nn). split; [exact SR'|]. split; [exact HK1|]. rewrite ld_live_L_remap. exact Hincl.
    + (* [comment removed for export] *)
      apply mspec_pointwise. intros s mo (-> & Hvo & Hdb & Hd & Hda & Hce & Hrf & HK1).
      assert (Hok : remap_move_ok (ps_m s0) nn d = true).
      { unfold remap_move_ok. rewrite (proj2 (Z.ltb_lt _ _) Hd), (proj2 (Z.leb_le _ _) Hce).
        rewrite (proj2 (Z.eqb_eq _ _) Hda). cbn [andb]. rewrite (live_ranges_free_lranges _ _ _ _ SR). exact Hrf. }
      rewrite Hok.
      assert (SR' : SIMREL (cs_remap (ps_m s0) rid g d nn) (L_remap L base d nn)).
      { apply (RF (ps_m s0) L (fst p) A n rid g base (mmap_len l) nn d SR Hlive Hn HA EP Eon Hd Hda Hce).
        right. rewrite (live_ranges_free_lranges _ _ _ _ SR). exact Hrf. }
      eapply mspec_seq with (R := fun s mo' => s = set_m (cs_remap (ps_m s0) rid g d nn) s0 /\ mo' = mo).
      { apply mspec_upd'. intros s mo' [-> ->]. auto. }
      intros []. apply mspec_ret. intros s mo' [-> ->]. cbn [ps_m ps_brk ps_fa ps_so set_m].
      split; [| splits; [reflexivity| reflexivity| exact Hvo]].
      apply (AOWN_self X). 2: exact Hin.
      split; [| exact ND]. exists (L_remap L base d nn). split; [exact SR'|]. split; [exact HK1|]. rewrite ld_live_L_remap. exact Hincl.
  - (* [comment removed for export] *)
    apply (rr_fallback_own X s0 mo0 mo0 p n HO Hin ltac:(lia) (vm_only_refl _)).
  - (* [comment removed for export] *)
    destruct HPF.
Qed.

Corollary raw_realloc_etwf : forall X s mo (p : bptr) A n,
  AOWN X s mo -> In (fst p) X -> 0 <= n < 2^32 -> addr_in_slot (ps_m s) (fst p) A ->
  etwf (raw_realloc p A n s) mo (fun q mo' => raw_realloc_post X s mo (fst p) (fst q) (snd q) mo').
Proof. intros X s mo p A n HO Hin Hn HA. apply (raw_realloc_own X s mo p A n HO Hin Hn HA). auto. Qed.

End RawRealloc.


End CeilWrap.
(* [comment removed for export] *)
Notation SIMREL := MI_Contracts.SIMREL.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End KRawR.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Decode NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext MI_Contracts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
Import KRawR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Import Realloc.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_m4096 : forall x, Z.land x (-4096) = x - x mod 4096.
Proof.
  intros x. change (-4096) with (Z.lnot (Z.ones 12)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
  pose proof (Z_div_mod_eq_full x 4096). lia.
Qed.

Lemma rr_needed_eq : forall n base, rr_needed n base = (n + base + UNIT + IB + 4095) - (n + base + UNIT + IB + 4095) mod 4096.
Proof. intros n base. unfold rr_needed. apply land_m4096. Qed.

Lemma rr_needed_facts : forall n base, 0 <= n -> 0 <= base ->
  n + base + UNIT + IB <= rr_needed n base < n + base + UNIT + IB + 4096 /\ rr_needed n base mod 4096 = 0 /\ 0 < rr_needed n base.
Proof.
  intros n base Hn Hb. rewrite rr_needed_eq. unfold UNIT, IB.
  pose proof (Z.mod_pos_bound (n + base + 16 + 4 + 4095) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (n + base + 16 + 4 + 4095) 4096) as H2.
  split; [lia|]. split; [| lia].
  set (x := n + base + 16 + 4 + 4095) in *. replace (x - x mod 4096) with (4096 * (x / 4096)) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section LIVE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL x0 st L BL LS.
Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma live_slot_facts : forall k, In k BL ->
  exists m i b ai,
    s_slots st !! (bslot k) = Some (m, i) /\ s_groups st !! b = Some (mkGhdr (Some m) ai) /\ group_ok x0 st LS m b ai
    /\ m_mem (MR st m) = Some b /\ 0 <= i <= m_last_idx (MR st m) /\ bslot k = slot_start' (MR st m) i
    /\ 0 <= boff k /\ 0 <= bsize k /\ UNIT * boff k + bsize k <= get_stride (MR st m) - IB.
Proof.
  intros k Hk.
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & Ho & Hsz & Hfit).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ((b & ai & Hg) & Hi & Es).
  pose proof (ig_ok _ _ _ IG m b ai Hg) as GOK.
  destruct (im_hdr _ _ _ IM b _ Hg) as (m' & Em' & Hmem & _). cbn in Em'. injection Em' as <-.
  exists m, i, b, ai. splits; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma sc63_facts : forall m b ai, s_groups st !! b = Some (mkGhdr (Some m) ai) -> group_ok x0 st LS m b ai ->
  m_mem (MR st m) = Some b -> 48 <= m_sizeclass (MR st m) ->
  m_sizeclass (MR st m) = 63 /\ m_last_idx (MR st m) = 0 /\ m_maplen (MR st m) <> 0 /\ snd b = 0
  /\ get_stride (MR st m) = m_maplen (MR st m) * 4096 - UNIT
  /\ exists r, s_regions st !! (fst b) = Some r /\ r_kind r = RKGroup
       /\ m_maplen (MR st m) * 4096 = mmap_len (r_len r)
       /\ In (r_base r, r_len r) (ld_groups L)
       /\ 0 < r_base r /\ r_base r mod PGSZ = 0 /\ 0 < r_len r < LEN_MAX /\ r_base r + mmap_len (r_len r) <= alloc_ceiling
       /\ conc st b = r_base r.
Proof.
  intros m b ai Hg GOK Hmem Hsc.
  destruct (g_sc _ _ _ _ _ _ GOK) as [[Hlt _]|(E63 & Hli & Hml & _)]; [lia|].
  destruct (g_top _ _ _ _ _ _ GOK Hml) as (Hsnd & r & Hr & Kr & Hlen & _).
  pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & _).
  rewrite round_up_pg_eq in Hlen, S5. fold (mmap_len (r_len r)) in Hlen, S5.
  refine (conj E63 (conj Hli (conj Hml (conj Hsnd (conj _ _))))).
  - unfold get_stride. rewrite Hli, Z.eqb_refl. destruct (Z.eqb_spec (m_maplen (MR st m)) 0); [contradiction| reflexivity].
  - exists r. refine (conj Hr (conj Kr (conj Hlen (conj _ (conj S1 (conj S2 (conj (conj S3 S4) (conj S5 _)))))))).
    + apply (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR))). apply in_map_iff. exists (fst b, r). split; [reflexivity|].
      apply List.filter_In. split; [| rewrite Kr; reflexivity]. apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
    + unfold conc, get_region. rewrite Hr. lia.
Qed.
End LIVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alloc_ceiling_val : alloc_ceiling = ceil_val.
Proof. reflexivity. Qed.

Theorem rr_plan_facts_proof : rr_plan_facts.
Proof.
  intros cs L c A n (st & BL & LS & <- & INV & LIVE) Hc Hn HA.
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & sz & Hk).
  destruct (live_slot_facts st L BL LS INV _ Hk) as (m & i & b & ai & Hs & Hg & GOK & Hmem & Hi & Es & Ho & Hsz & Hfit). cbn [bslot fst snd] in Hs, Es.
  unfold rplan_of. rewrite s_slots_strip, Hs, !get_meta_rec_strip, !conc_strip. fold (MR st m).
  destruct ((n <=? get_stride (MR st m) - IB - (A - conc st c)) && (n <? MMAP_THRESHOLD) && (m_sizeclass (MR st m) <=? size_to_class n + 1)); [exact I|].
  destruct (Z.leb_spec 48 (m_sizeclass (MR st m))) as [Hsc|Hsc]; [| exact I].
  destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hth|Hth]; [| exact I]. cbn [andb].
  destruct (sc63_facts st L BL LS INV m b ai Hg GOK Hmem Hsc) as (E63 & Hli & Hml & Hsnd & Hstr & r & Hr & Kr & Hlen & Hing & S1 & S2 & S3 & S5 & Hconc).
  rewrite E63. cbn [Z.eqb Pos.eqb negb]. rewrite Hmem. rewrite conc_strip, Hconc.
  specialize (HA m i ltac:(rewrite s_slots_strip; exact Hs)). rewrite get_meta_rec_strip, conc_strip in HA. fold (MR st m) in HA. rewrite Hstr in HA.
  destruct (rr_needed_facts n (A - conc st c) ltac:(lia) ltac:(lia)) as (N1 & N2 & N3).
  split; [exists (r_len r); split; [exact Hing| exact Hlen]|].
  split; [| exact N2]. split; [exact N3|].
  rewrite alloc_ceiling_val in S5. pose proof (NodesSound.mmap_len_ge (r_len r)). unfold LEN_MAX, UNIT, IB in *. lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
