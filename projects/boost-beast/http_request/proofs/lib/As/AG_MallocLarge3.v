(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib Require LazyMadvise.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepX AsDepotInv
     SecLazy SecLazy2 AS_AllocSec1 AG_LargeModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition lg_L (L : list (word * word)) (pa nres nch : Z) : list (word * word) :=
  if nch =? nres then maps_subtract L (pa + 8 * nres) (pa + 8 * nres + 0x20000) else L.
(* [comment removed for export] *)
Definition lg_cost (msz : Z) : Z := msz + 0x20000 + (msz / 32768 + 2) * 4096.

Section ModelAfterLarge.
  Variables (s : ast) (mo mo2 : Model) (a size : Z) (d : depot).
  Let st := a_st s.
  Let pa := a_pa s.
  Let r := compute_req size.
  Let needed := rq_needed r.
  Let msz := round_up needed kPageSize + kPageSize.
  Let nch := zlen (as_sec st).
  Let nres := as_n_reserved st.
  Let st2 := large_state st a size.
  Let Wsh : word * word := (wz (sh a), wz (msz / 8)).
  Let L2 := lg_L (a_L s) pa nres nch.
  Let AL2 := a_AL s - lg_cost msz.
  Let s2 := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 (Wsh :: a_S s) (a_Zr s) AL2 (a_top s) (a_bot s).

  Hypothesis AMX : AMODELX s mo.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis SZ : 64512 < size < 2^32.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0.
  Hypothesis FREE : region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true.
  Hypothesis LM : rsub (a_L s) (vm_maps (m_vmmaps mo)).         (* [comment removed for export] *)
  Hypothesis NWL : entries_nowrap (a_L s).                        (* [comment removed for export] *)
  Hypothesis ALLOW : lg_cost msz <= a_AL s.
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil.
  Hypothesis NCH : 0 <= nch <= nres /\ nres + 16384 <= 2^20.
  Hypothesis MO : as_model mo a msz pa nres (nch =? nres) mo2.

  Let ARE : 6811648 <= a /\ a + msz <= aceil. Proof. pose proof (proj1 AR) as X. clear - X. aunf. lia. Qed.   (* [comment removed for export] *)
  Let PAE : 6811648 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let RQ := large_req size SZ.

  Let GEO : size + 8 <= needed - 4088 /\ needed <= size + 4104 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ needed mod 8 = 0 /\ msz mod 4096 = 0 /\ a mod 4096 = 0.
  Proof.
    apply (large_geo st a size SZ). destruct AR as (_ & _ & AL). unfold kPageSize. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. exact AL.
  Qed.
  (* [comment removed for export] *)
  Let BND : 6811648 <= a /\ a + msz <= aceil /\ 73728 <= msz /\ 6811648 <= pa /\ pa + 8388608 <= aceil
            /\ 2148302336 <= sh a /\ sh a + msz / 8 <= (sh aceil) /\ 8 * (msz / 8) = msz.
  Proof.
    destruct AR as (A1 & A2 & A3). pose proof GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7). destruct PAR as [P1 P2].
    pose proof (aapp_sh_env_div _ _ A1 ltac:(clear - G1 G3 SZ; lia)) as ASH.
    apply aapp_env in A1; [| clear - G1 G3 SZ; lia]. apply aapp_env in P1; [| unfold kPtrArrayReserve; clear; lia].
    acb. unfold AHI_LO, kPtrArrayReserve in *. subst pa.
    unfold round_up, round_down, sh, ASHADOW_BASE in *. repeat split; try lia; Z.div_mod_to_equations; lia.
  Qed.
  (* [comment removed for export] *)
  Let PBAND : pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa.
  Proof. pose proof (aapp_lit _ _ (proj1 PAR)) as L. unfold kPtrArrayReserve in L. exact L. Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.False Sort Prop.
Scheme kc__5 := Elimination for Corelib.Init.Logic.ex Sort Prop.

  Theorem amodelx_after : AMODELX s2 mo2 /\ depot_cov d mo2.
  Proof.
    (* LPS revision repair (#38 / 75d69e00, checker 2c6b6db8).  The recorded KReplay body of
       [amodelx_after] was typed against the pre-#38 [akernel], which was a FLAT conjunction.  At
       #38 [akernel mo := akernel_pre mo /\ akernel_resx mo] (Bo/AllocRepX.v:275), so the body's
       final [conj] lands where [akernel_resx] now sits.  Kernel, verbatim, from the retained TAIL
       of the owning action (the [In environment] block is what dune's cut removed):
         "… region_free (vm_noaccess (m_vmmaps mo')) a n = true"
         while it is expected to have type "akernel s2 mo'".
       a farm round at source, and
       independently in BeastAk1Ceiling's round at the same sha, same
       characters 63590-63594.
       That first error is the blob LINE ITSELF, so every line above it is certified by the failing
       round: this file's Section, its [Let] bounds, and [:88 Theorem amodelx_after] all elaborate
       under the new [akernel].  NO STATEMENT MOVES.
       Re-authored as explicit text from the plain-text donor
       openssl/echconfiglist_parser As/AG_MallocLarge3.v:81-209 (214 lines, ZERO blobs, name-for-name
       identical Section), the same donor tree used for AS_MallocLarge and AG_MallocLarge.  Binary
       literals re-keyed from THIS mirror's own [ARE]/[PAE]/[BND]; shared with the donor and left
       alone: 73728, 8388608, 17594333495296, 2147446784, kPtrArrayReserve, AHI_LO.
       The ONE line of the donor's proof that is not transcribed is its numbered 18-way
       [destruct AK]; see the note at that site.  [akernel_resx] is appended LAST and discharged by
       [rewrite VR2] — the repair shape this revision's RESERVED-CEILING-CLASS prescribes, and sound
       because [as_model]'s third component is [vm_reserved h' = vm_reserved h]
       (Bo/AS_AllocSec1.v:73, As/:69) while [akernel_resx] is a predicate of [vm_reserved h] alone.
       Semantics confirmed by BeastAk1Ceiling, who owns [akernel]; nothing is decoded or re-encoded. *)
    destruct AMX as [AM AK]. destruct AM as (AIL & ASV & AB). destruct AIL as (A1 & A2 & A3 & NOV & NW & NWA).
    pose proof MO as M; unfold as_model in M; cbv beta iota zeta in M. destruct M as (NV & VM2 & VR2 & VL2 & VB2 & VK2 & VS2 & VA2 & EAG2).
    pose proof BND as B. destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). acb. pose proof PBAND as PB'.
    assert (SHLO : sh AHI_LO = 0x2008fff7000) by (rewrite <- AHSB_eq; reflexivity). pose proof sh_ceiling_range as SCV.   (* [comment removed for export] *)
    set (h := m_vmmaps mo) in *. set (h2 := m_vmmaps mo2) in *.
    (* [comment removed for export] *)
    assert (NOTL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (a_L s) = false).
    { intros x Hx. destruct (in_rangesb x (a_L s)) eqn:E; [exfalso| reflexivity].
      pose proof (LM x E) as INM. rewrite (region_free_not_in _ _ _ x (region_free_app_r _ _ _ _ FREE)) in INM; [discriminate|].
      unfold wz. rewrite !unsigned_lit by lia. exact Hx. }
    (* [comment removed for export] *)
    assert (SUBL : forall x : word, in_rangesb x L2 = true -> in_rangesb x (a_L s) = true).
    { intros x Hx. subst L2. unfold lg_L in Hx. destruct (nch =? nres); [| exact Hx]. rewrite in_rangesb_zcovb in Hx |- *.
      rewrite zcovb_maps_subtract in Hx by (first [exact NWL| lia]). apply andb_true_iff in Hx. exact (proj1 Hx). }
    assert (BANDL : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L2 = true).
    { intros x Hx. pose proof (ak_lsh s mo AK x Hx) as LX. rewrite SHLO in Hx. subst L2. unfold lg_L.
      destruct (nch =? nres); [| exact LX]. rewrite in_rangesb_zcovb in LX |- *. rewrite zcovb_maps_subtract by (first [exact NWL| lia]).
      rewrite LX. apply andb_true_iff. split; [reflexivity|]. apply negb_true_iff. apply zinb_false. lia. }
    (* [comment removed for export] *)
    assert (BANDL2 : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x L2 = true).
    { intros x Hx. pose proof (ak_lsl s mo AK x Hx) as LX. unfold sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in Hx. subst L2. unfold lg_L.
      destruct (nch =? nres); [| exact LX]. rewrite in_rangesb_zcovb in LX |- *. rewrite zcovb_maps_subtract by (first [exact NWL| lia]).
      rewrite LX. apply andb_true_iff. split; [reflexivity|]. apply negb_true_iff. apply zinb_false. lia. }
    (* [comment removed for export] *)
    assert (NASUB : forall x : word, in_rangesb x (vm_noaccess h) = false -> in_rangesb x (vm_noaccess h2) = false).
    { intros x Hx. rewrite VA2. rewrite in_rangesb_zcovb in Hx |- *.
      destruct (nch =? nres); [apply zcovb_maps_subtract_false; [exact NWA| lia| lia| exact Hx] | exact Hx]. }
    assert (NWA2 : entries_nowrap (vm_noaccess h2)).
    { rewrite VA2. destruct (nch =? nres); [apply maps_subtract_nowrap; [exact NWA| lia| lia] | exact NWA]. }
    assert (INCONS : forall (x : word) e, in_rangesb x (vm_maps h) = true -> in_rangesb x (e :: vm_maps h) = true)
      by (intros x e Hx; rewrite in_rangesb_cons, Hx; apply orb_true_r).
    split; [| (* [comment removed for export] *) intros x Hx; unfold h2 in VM2 |- *; rewrite VM2; apply INCONS; exact (DCOV x Hx)].
    split.
    { (* [comment removed for export] *)
      split.
      { (* [comment removed for export] *)
        unfold amaps_in_ledger. change (m_vmmaps mo2) with h2. change (a_st s2) with st2. change (a_L s2) with L2.
        change (as_maps st2) with (large_maps st a size). change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]).
        unfold large_maps. fold r needed msz nch nres. fold nch. fold nres.
        split.
        { intros mp Hin K1 K2 K3 K4. rewrite VM2. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
          - exfalso. destruct (nch =? nres); [| destruct Hin]. destruct Hin as [<-|[]]. exact (K3 eq_refl).
          - destruct Hin as [<-|Hin]; [split; [intros _; left; reflexivity| cbn [mp_base]; clear - B1 B2 B3; acb; lia]|].
            destruct (A1 mp Hin K1 K2 K3 K4) as [X Y]. exact (conj (fun P => or_intror (X P)) Y). }   (* [comment removed for export] *)
        split.
        { intros mp Hin KK x Hx. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
          - (* [comment removed for export] *)
            destruct (Z.eqb_spec nch nres) as [EC|NE]; [| destruct Hin]. destruct Hin as [<-|[]]. cbn [mp_base mp_size] in Hx.
            assert (SL : pa + 8 * nres <= bv_unsigned x < pa + 8 * nres + 131072) by (change (as_ptr_array st) with pa in Hx; unfold kChunksBlockCount in Hx; fold nres in Hx; lia).
            split.
            + rewrite VA2. rewrite in_rangesb_zcovb. replace (nch =? nres) with true by (symmetry; apply Z.eqb_eq; exact EC).
              assert (N1 : zcovb (maps_subtract (vm_noaccess h) (pa + 8 * nres) (pa + 8 * nres + 131072)) (bv_unsigned x) = false).
              { rewrite zcovb_maps_subtract by (first [exact NWA| lia]). apply andb_false_iff. right. apply negb_false_iff. apply zinb_true. exact SL. }
              exact N1.
            + subst L2. unfold lg_L. replace (nch =? nres) with true by (symmetry; apply Z.eqb_eq; exact EC). rewrite in_rangesb_zcovb.
              assert (N1 : zcovb (maps_subtract (a_L s) (pa + 8 * nres) (pa + 8 * nres + 131072)) (bv_unsigned x) = false).
              { rewrite zcovb_maps_subtract by (first [exact NWL| lia]). apply andb_false_iff. right. apply negb_false_iff. apply zinb_true. exact SL. }
              exact N1.
          - destruct Hin as [<-|Hin]; [exfalso; destruct KK as [K|[[c [K|K]]|K]]; discriminate K|].
            destruct (A2 mp Hin KK x Hx) as [Q1 Q2]. split; [exact (NASUB x Q1)|].
            destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q2. discriminate Q2. }
        split.
        { intros sc x Hin Hx. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]].
          - pose proof (A3 sc x Hin Hx) as Q. destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q. discriminate Q.
          - cbn [sc_map_beg sc_map_size] in Hx. pose proof (NOTL x Hx) as Q. destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q. discriminate Q. }
        rewrite VM2. split; [| split; [| exact NWA2]].
        - apply nooverlap_cons_free; [exact (region_free_app_r _ _ _ _ FREE)| exact NOV].
        - apply entries_nowrap_cons'; [| exact NW]. unfold entry_nowrap, LazyLedger.hi, LazyLedger.lo. cbn [fst snd]. unfold wz. rewrite !unsigned_lit by lia. lia. }
      split.
      { (* [comment removed for export] *)
        destruct ASV as [V1 V2]. unfold ashadow_visible. change (a_st s2) with st2. change (a_S s2) with (Wsh :: a_S s).
        change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]).
        split.
        - intros c x Hc Hx. rewrite in_rangesb_cons. rewrite (V1 c x Hc); [apply orb_true_r|].
          change (RB s2 c) with (RB s c) in Hx. change (get_region st2 c) with (get_region st c) in Hx. exact Hx.
        - intros sc x Hin Hx. rewrite in_rangesb_cons. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]].
          + rewrite (V2 sc x Hin Hx). apply orb_true_r.
          + cbn [sc_map_beg sc_map_size] in Hx. apply orb_true_iff. left. subst Wsh. apply (zin_W (sh a) (msz / 8)); lia. }
      (* [comment removed for export] *)
      destruct AB as [AB0 AB1]. unfold ABUDGET. change (a_AL s2) with AL2. change (a_S s2) with (Wsh :: a_S s). change (m_vmmaps mo2) with h2. rewrite VL2.
      rewrite (aPhi_regions s s2) by reflexivity.   (* [comment removed for export] *)
      rewrite pages_total_cons. pose proof (cl_bounds Wsh) as CB. subst Wsh. cbn [fst snd] in CB. unfold wz in CB. rewrite (unsigned_lit (msz / 8)) in CB by (first [clear - SZ ARE GEO BND B8 ACEILB CB; lia | lia]).
      pose proof (pages_total_nonneg (a_S s)) as PT. unfold page_size in *.
      replace (msz / 8 / 4096) with (msz / 32768) in CB by (rewrite Z.div_div by lia; reflexivity).
      subst AL2. unfold lg_cost in *. split; [lia|]. clear - AB1 CB PT EAG2 ALLOW B3; try acb. unfold wz in *. subst h. destruct (nch =? nres); lia. }
    (* [comment removed for export] *)
    (* #38 RESERVED-CEILING-CLASS.  The donor's single numbered [destruct AK as (K1 & … & K11)]
       is the ONE line of its proof that must not be transcribed: at #38 [akernel mo] is the PAIR
       [akernel_pre mo /\ akernel_resx mo] (Bo/AllocRepX.v:275), so an 18-way positional pattern is
       one level short.  That is exactly the recorded body's defect, which the kernel reported as
       "… region_free (vm_noaccess (m_vmmaps mo')) a n = true" — [akernel_pre]'s LAST conjunct —
       "while it is expected to have type akernel s2 mo'": a flat chain whose final [conj] lands
       where [akernel_resx] now sits.
       The outer level is split by name rather than by position so the next arity move fails HERE
       rather than silently downstream; the inner 18-way pattern is kept because [akernel_pre]'s
       shape is unchanged and the donor's text binds K1..K11 by those names. *)
    unfold akernel in AK. destruct AK as [AKpre AKres].
    destruct AKpre as (K1 & (K2a & K2c) & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11).   (* [comment removed for export] *)
    unfold akernel. split.
    2:{ (* [akernel_resx] is a predicate of [vm_reserved h] ALONE — every occurrence of [mo] in it
           is inside [vm_reserved (m_vmmaps mo)], [bsegs] is a global Definition, and the per-entry
           facts, the length bound and the size bound all quantify over [rx] only.  [as_model]'s
           third component is [vm_reserved h' = vm_reserved h] (Bo/AS_AllocSec1.v:73), so a large
           allocation carries it whole with the SAME witness: it is insensitive to the [vm_maps]
           cons, to [na1] and to [eager_used].  [akernel_resx] is unfolded explicitly because it is
           a constant and would otherwise hide the [m_vmmaps mo2] the rewrite needs.  [cbv beta zeta]
           removes the [let h := … in] that [akernel_resx]'s body carries, and the two [change]s
           re-fold [h]/[h2] because [set] at :118 folded only the occurrences that existed THEN —
           a later [unfold] reintroduces the unfolded spelling and [rewrite VR2] would not find it. *)
        unfold akernel_resx in AKres |- *. cbv beta zeta in AKres |- *.
        change (m_vmmaps mo2) with h2. change (m_vmmaps mo) with h.
        (* #38: [akernel_resx] is no longer a predicate of [vm_reserved h] ALONE -
           it gained the maps-vs-reserved disjointness conjunct (As/AllocRepX.v),
           and a large allocation CONSES [(wz a, wz msz)] onto [vm_maps]
           ([VM2], as_model's second component, As/AS_AllocSec1.v:68).  So the
           witness still transports, but the new conjunct needs the cons case.
           It is discharged from [FREE], which this Section already holds: its
           left half [region_free (vm_reserved h) (wz a) (wz msz) = true] is
           exactly the statement that the newly mapped window misses every
           reserved interval, and [region_free_In] (RefNodes.v:882) turns it into
           the per-entry disjunction the conjunct asks for.  No new hypothesis and
           no new geometry: the allocation could not have been granted otherwise. *)
        rewrite VR2.
        destruct AKres as [rx (Hr & Hok & Hlen & Hsz & HD)]. exists rx.
        split; [exact Hr|]. split; [exact Hok|]. split; [exact Hlen|]. split; [exact Hsz|].
        rewrite VM2. intros iv Hiv e He.
        destruct Hiv as [<-|Hiv]; [| exact (HD iv Hiv e He)].
        destruct e as [b sz]. cbn [fst snd].
        (* The [region_free_In] in scope here is the MODEL's ([State.v:7636]), not
           [RefNodes.v:882]'s - this file imports [LazyNodes], not [RefNodes]. The two
           share a name and differ in conclusion: the model's yields the BOOLEAN
           [iv_overlap lo n a sz = false], measured verbatim by
           a farm round at this line. Converting rather than importing
           [RefNodes]: [iv_overlap a1 n1 a2 n2 := (a1 <? a2+n2) && (a2 <? a1+n1)]
           ([State.v:7622-7624]), so [andb_false_iff] splits it and [Z.ltb_ge] turns each
           arm into one side of the disjunction - the FIRST arm giving the RIGHT disjunct
           and the second the LEFT, which is why the bullets are crossed. *)
        pose proof (region_free_In (vm_reserved h) (wz a) (wz msz) b sz
                      (region_free_app_l _ _ _ _ FREE) He) as D.
        unfold iv_overlap in D. apply andb_false_iff in D.
        destruct D as [D|D]; apply Z.ltb_ge in D; [right | left]; exact D. }
change (m_vmmaps mo2) with h2. change (a_thr s2) with (a_thr s). change (a_ctx s2) with (a_ctx s). change (a_sb s2) with (a_sb s).
    change (a_pa s2) with pa. change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L2.
    rewrite VR2, VL2, VM2.
    split; [exact K1|]. split; [exact (conj K2a (eq_trans (nonvm_same_atop _ _ NV) K2c))|].
    split; [intros x Hx; apply INCONS; exact (K3 x Hx)|].
    split; [intros xa xn c Hc H1 H2; apply map_contains_cons; change (RB s2 c) with (RB s c) in H1, H2; exact (K4a xa xn c Hc H1 H2)|].
    split; [intros xa xn H1 H2; apply map_contains_cons; exact (K4b xa xn H1 H2)|].
    split; [intros xa xn H1 H2 H3; apply map_contains_cons; exact (K4c xa xn H1 H2 H3)|].
    split; [exact K5a|]. split; [exact K5b|].
    split; [intros x Hx; split; [exact (proj1 (K5c x Hx))| exact (BANDL x Hx)]|].
    split.
    { (* [comment removed for export] *) intros x Hx. apply INCONS. apply K6a. destruct (in_rangesb x (vm_noaccess h)) eqn:E. { unfold h in E. first [exact E| reflexivity]. } rewrite (NASUB x E) in Hx. discriminate Hx. }
    split.
    { (* [comment removed for export] *)
      intros sc x Hin Hx. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]) in Hin. apply in_app_iff in Hin.
      assert (E0 : in_rangesb x (vm_noaccess h) = false).
      { destruct Hin as [Hin|[<-|[]]]; [exact (K6b sc x Hin Hx)|]. cbn [sc_map_beg sc_map_size] in Hx.
        destruct (in_rangesb x (vm_noaccess h)) eqn:E; [exfalso| reflexivity].
        pose proof (K6a x E) as INM. rewrite (region_free_not_in _ _ _ x (region_free_app_r _ _ _ _ FREE)) in INM; [discriminate|].
        unfold wz. rewrite !unsigned_lit by lia. exact Hx. }
      destruct (in_rangesb x (vm_noaccess h2)) eqn:E2; [| reflexivity]. rewrite (NASUB x E0) in E2. discriminate E2. }
    split.
    { intros sc Hin. change (as_sec (a_st s2)) with (as_sec st ++ [mkSC a msz needed]) in Hin. apply in_app_iff in Hin.
      destruct Hin as [Hin|[<-|[]]]; [right; exact (K7 sc Hin)| left; reflexivity]. }
    split; [intros x Hx; apply INCONS; exact (K8a x Hx)|].
    split; [intros xa xn H1 H2 H3; apply map_contains_cons; exact (K8b xa xn H1 H2 H3)|].
    split; [intros x Hx; split; [exact (proj1 (K8c x Hx))| exact (BANDL2 x Hx)]|].
    split; [exact K9|].
    split.
    2:{ (* [comment removed for export] *)
        intros xa xn HB. pose proof (K11 xa xn HB) as FR0. rewrite VA2.
        destruct (nch =? nres); [apply LazyMadvise.region_free_maps_subtract; [exact NWA| exact FR0]| exact FR0]. }
    { (* [comment removed for export] *)
      destruct K10 as (C1 & C2 & C3). change (as_sec st2) with (as_sec st ++ [mkSC a msz needed]). unfold hsec in *.
      rewrite hcnt_cons, hlen_cons, zlen_filter_app, zsum_size_filter_app. rewrite (ehigh_wz a msz) by lia.
      assert (SH : forall z, schigh (mkSC a msz z) = (AHI_LO <? a + msz)) by (intros z; reflexivity). rewrite !SH.
      cbn [List.filter snd]. rewrite !SH. replace (bv_unsigned (wz msz)) with msz by (unfold wz; rewrite unsigned_lit by lia; reflexivity).
      split; [| split].
      - destruct (AHI_LO <? a + msz); unfold zlen in *; cbn [length map] in *; clear - C1; subst h st; change (Z.of_nat 1) with 1; change (Z.of_nat 0) with 0; lia.
      - destruct (AHI_LO <? a + msz); cbn [map SecGap.zsum sc_map_size] in *; clear - C2; subst h st; repeat match goal with x := _ |- _ => subst x end; lia.
      - intros sc Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]]; [exact (C3 sc Hin)|].
        cbn [sc_map_size]. unfold ASECMAX. pose proof GEO as (G1 & G2 & G3 & G4 & _). clear - G1 G2 G3 G4 SZ. subst msz needed r. lia. }
  Qed.
End ModelAfterLarge.

End HCW.

