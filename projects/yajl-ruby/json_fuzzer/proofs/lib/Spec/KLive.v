(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesMat Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad MSafe STree Malloc RawAlloc KInv KLink KStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma live_bytes_app : forall A B, live_bytes (A ++ B) = live_bytes A + live_bytes B.
Proof. induction A as [|[a n] A IH]; intros B; cbn; [reflexivity|]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg : forall M, 0 <= live_bytes M.
Proof. induction M as [|[a n] M IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma maps_subtract_app : forall A B lo hi, maps_subtract (A ++ B) lo hi = maps_subtract A lo hi ++ maps_subtract B lo hi.
Proof. induction A as [|[a n] A IH]; intros B lo hi; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma msa_app : forall cuts A B, maps_subtract_all (A ++ B) cuts = maps_subtract_all A cuts ++ maps_subtract_all B cuts.
Proof. induction cuts as [|[a n] cuts IH]; intros A B; cbn; [reflexivity|]. rewrite maps_subtract_app. apply IH. Qed.

Lemma msa_nil : forall cuts, maps_subtract_all [] cuts = [].
Proof. induction cuts as [|[a n] cuts IH]; cbn; [reflexivity| exact IH]. Qed.

Lemma live_bytes_iv_subtract : forall a sz lo hi, lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in Ra, Rs.
  unfold iv_subtract. cbv zeta.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [L|L]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [R|R]; cbn;
    rewrite ?unsigned_lit; try lia.
Qed.

Lemma live_bytes_maps_subtract : forall M lo hi, lo <= hi -> live_bytes (maps_subtract M lo hi) <= live_bytes M.
Proof.
  induction M as [|[a n] M IH]; intros lo hi H; cbn; [lia|]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract a n lo hi H). specialize (IH lo hi H). lia.
Qed.

Lemma live_bytes_msa : forall cuts M, live_bytes (maps_subtract_all M cuts) <= live_bytes M.
Proof.
  induction cuts as [|[a n] cuts IH]; intros M; cbn; [lia|].
  etransitivity; [apply IH|]. apply live_bytes_maps_subtract. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall a sz lo hi, lo <= hi -> 0 < bv_unsigned sz ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) -> iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hlh Hsz D. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in Ra, Rs.
  unfold iv_subtract. cbv zeta.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [L|L]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [R|R]; cbn; try lia.
  - rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia. rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_disjoint : forall M lo hi, lo <= hi ->
  (forall e, In e M -> elo e < ehi e /\ (ehi e <= lo \/ hi <= elo e)) -> maps_subtract M lo hi = M.
Proof.
  induction M as [|[a n] M IH]; intros lo hi Hlh HM; cbn; [reflexivity|].
  destruct (HM (a, n) (or_introl eq_refl)) as [W D]. unfold elo, ehi in W, D. cbn in W, D.
  rewrite iv_subtract_disjoint by lia. cbn. f_equal. apply IH; [exact Hlh|]. intros e He. apply HM. right. exact He.
Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_eq : forall mo, m_vm_lazy mo = [] ->
  vm_backing_used mo = live_bytes (maps_subtract_all (vm_maps (m_vmmaps mo)) (vm_noaccess (m_vmmaps mo)))
                       + Z.of_nat (length (m_vm_materialized mo)) * page_size.
Proof. intros mo Hl. unfold vm_backing_used, vm_backed_maps. rewrite Hl. reflexivity. Qed.

Lemma vm_backing_used_le_live : forall mo, m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  vm_backing_used mo <= live_bytes (vm_maps (m_vmmaps mo)).
Proof. intros mo Hl Hm. rewrite vm_backing_used_eq by exact Hl. rewrite Hm. cbn [length Z.of_nat]. pose proof (live_bytes_msa (vm_noaccess (m_vmmaps mo)) (vm_maps (m_vmmaps mo))). lia. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_frame : forall mo mo',
  m_vm_lazy mo' = m_vm_lazy mo -> m_vm_materialized mo' = m_vm_materialized mo ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_backing_used mo' = vm_backing_used mo.
Proof. intros mo mo' H1 H2 H3 H4. unfold vm_backing_used, vm_backed_maps. rewrite H1, H2, H3, H4. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_cons_map : forall mo mo' e,
  m_vm_lazy mo = [] -> m_vm_lazy mo' = [] -> m_vm_materialized mo' = m_vm_materialized mo ->
  vm_maps (m_vmmaps mo') = e :: vm_maps (m_vmmaps mo) -> vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_backing_used mo' <= vm_backing_used mo + bv_unsigned (snd e).
Proof.
  intros mo mo' e Hl Hl' Hm Hmaps Hna. rewrite !vm_backing_used_eq by assumption. rewrite Hm, Hmaps, Hna.
  change (e :: vm_maps (m_vmmaps mo)) with ([e] ++ vm_maps (m_vmmaps mo)). rewrite msa_app, live_bytes_app.
  pose proof (live_bytes_msa (vm_noaccess (m_vmmaps mo)) [e]) as B. destruct e as [a n]. cbn in B |- *. lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_cons_none : forall mo mo' a n,
  m_vm_lazy mo = [] -> m_vm_lazy mo' = [] -> m_vm_materialized mo' = m_vm_materialized mo ->
  vm_maps (m_vmmaps mo') = (a, n) :: vm_maps (m_vmmaps mo) -> vm_noaccess (m_vmmaps mo') = (a, n) :: vm_noaccess (m_vmmaps mo) ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2^64 ->
  (forall e, In e (vm_maps (m_vmmaps mo)) -> elo e < ehi e /\ (ehi e <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= elo e)) ->
  vm_backing_used mo' = vm_backing_used mo.
Proof.
  intros mo mo' a n Hl Hl' Hm Hmaps Hna Hn Hhi HM. rewrite !vm_backing_used_eq by assumption. rewrite Hm, Hmaps, Hna. cbn [maps_subtract_all maps_subtract].
  assert (E0 : iv_subtract a n (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = []).
  { unfold iv_subtract. cbv zeta. rewrite !Z.ltb_irrefl. reflexivity. }
  rewrite E0. cbn [app]. rewrite maps_subtract_disjoint; [reflexivity| lia|].
  intros e He. destruct (HM e He) as [W D]. split; [exact W|]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_r_ok_same : forall mo req, brk_r_ok mo req (vm_brk (m_vmmaps mo)) = true.
Proof.
  intros mo req. unfold brk_r_ok. cbv zeta.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps mo))))%Z; [apply bv_eqb_refl|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps mo)))%Z; [rewrite bv_eqb_refl; apply orb_true_r|].
  rewrite bv_eqb_refl, orb_true_r. cbn [andb]. unfold brk_grow_ok. cbv zeta. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Definition brk_eff (mo : Model) (req r : word) : resp :=
  mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps mo))) (brk_unmaps r (vm_brk (m_vmmaps mo))) [] [].

Lemma nstep_brk_ex : forall req mo r,
  brk_r_ok mo (Z_to_bv 64 req) r = true ->
  nstep (NBrk req) mo (brk_eff mo (Z_to_bv 64 req) r) (with_brk_next mo (Z_to_bv 64 req) r) [].
Proof.
  intros req mo r Hok. apply nstep_brk_iff. unfold check_brk, brk_eff.
  rewrite Hok, !(proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma brk_unmaps_same : forall b, brk_unmaps b b = [].
Proof. intros b. unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _); reflexivity. Qed.

Lemma with_brk_next_same_vm : forall mo req,
  let mo' := with_brk_next mo req (vm_brk (m_vmmaps mo)) in
  m_vm_lazy mo' = m_vm_lazy mo /\ m_vm_materialized mo' = m_vm_materialized mo
  /\ m_vmmaps mo' = brk_model_next (m_vmmaps mo) req (vm_brk (m_vmmaps mo)).
Proof. intros mo req. unfold with_brk_next. rewrite brk_unmaps_same. cbn. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_brk0_can : forall mo,
  exists rsp mo', nstep (NBrk 0) mo rsp mo' [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
    /\ vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) /\ vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo)
    /\ vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo)
    /\ vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) /\ vm_backing_used mo' = vm_backing_used mo.
Proof.
  intros mo. pose proof (nstep_brk_ex 0 mo (vm_brk (m_vmmaps mo)) (brk_r_ok_same _ _)) as Hst.
  eexists _, _. split; [exact Hst|].
  pose proof (nstep_dec_brk0 mo _ _ _ Hst) as (_ & Hd & Hvo & _). split; [exact Hd|]. split; [exact Hvo|].
  destruct (with_brk_next_same_vm mo (Z_to_bv 64 0)) as (V1 & V2 & V3).
  pose proof (brk_model_next_query (m_vmmaps mo)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite V3. splits; auto.
  all: first [ apply vm_backing_used_frame; rewrite ?V3; auto | rewrite <- Q5 at 2; reflexivity ].
Qed.

Lemma brk_zeros_same : forall req b, brk_zeros req b b = [].
Proof. intros req b. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_brk_refuse_can : forall req mo,
  let h := m_vmmaps mo in let cur := bv_unsigned (vm_brk h) in
  cur <= req < 2^64 ->
  exists rsp mo', nstep (NBrk req) mo rsp mo' [] /\ dec_brk cur req rsp = Some BrkSame /\ vm_only mo mo'
    /\ vm_reserved (m_vmmaps mo') = vm_reserved h /\ vm_maps (m_vmmaps mo') = vm_maps h
    /\ vm_noaccess (m_vmmaps mo') = vm_noaccess h /\ vm_start_brk (m_vmmaps mo') = vm_start_brk h /\ vm_brk (m_vmmaps mo') = vm_brk h
    /\ vm_limit (m_vmmaps mo') = vm_limit h /\ vm_backing_used mo' = vm_backing_used mo.
Proof.
  intros req mo h cur Hreq. pose proof (nstep_brk_ex req mo (vm_brk h) (brk_r_ok_same _ _)) as Hst.
  eexists _, _. split; [exact Hst|].
  pose proof (nstep_mm_vm_only (NBrk req) mo _ _ _ I Hst) as [[Hvo _] _].
  destruct (with_brk_next_same_vm mo (Z_to_bv 64 req)) as (V1 & V2 & V3). fold h in V3.
  pose proof (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
  split.
  { unfold brk_eff. fold h. rewrite brk_zeros_same, brk_unmaps_same. unfold dec_brk. fold cur. rewrite Z.eqb_refl. reflexivity. }
  split; [exact Hvo|]. rewrite V3. splits; auto.
  all: first [ reflexivity | apply vm_backing_used_frame; rewrite ?V3; auto ].
Qed.

(* [comment removed for export] *)
Lemma nstep_brk_grow_can : forall req mo,
  let h := m_vmmaps mo in let cur := bv_unsigned (vm_brk h) in
  0 < cur -> bv_unsigned (vm_start_brk h) <= cur -> cur < req < 2^64 ->
  brk_r_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  m_vm_lazy mo = [] ->
  exists rsp mo', nstep (NBrk req) mo rsp mo' [] /\ dec_brk cur req rsp = Some BrkGrown /\ vm_only mo mo'
    /\ vm_reserved (m_vmmaps mo') = vm_reserved h /\ vm_maps (m_vmmaps mo') = (vm_brk h, Z_to_bv 64 (req - cur)) :: vm_maps h
    /\ vm_noaccess (m_vmmaps mo') = vm_noaccess h /\ vm_start_brk (m_vmmaps mo') = vm_start_brk h /\ vm_brk (m_vmmaps mo') = Z_to_bv 64 req
    /\ vm_limit (m_vmmaps mo') = vm_limit h /\ m_vm_lazy mo' = [] /\ m_vm_materialized mo' = m_vm_materialized mo
    /\ vm_backing_used mo' <= vm_backing_used mo + (req - cur).
Proof.
  intros req mo h cur Hpos Hsb Hreq Hok Hlz. pose proof (nstep_brk_ex req mo (Z_to_bv 64 req) Hok) as Hst.
  eexists _, _. split; [exact Hst|].
  pose proof (nstep_dec_brk req mo _ _ _ Hpos Hsb ltac:(subst cur h; lia) Hst) as (_ & Hvo & a & Hd & Ha).
  assert (V : let mo' := with_brk_next mo (Z_to_bv 64 req) (Z_to_bv 64 req) in
              m_vm_lazy mo' = m_vm_lazy mo /\ m_vm_materialized mo' = m_vm_materialized mo
              /\ m_vmmaps mo' = brk_model_next h (Z_to_bv 64 req) (Z_to_bv 64 req)).
  { unfold with_brk_next, brk_unmaps, brk_page_range. rewrite unsigned_lit by (subst cur h; lia). fold h cur.
    replace (page_round_up_Z req <? page_round_up_Z cur) with false by (symmetry; apply Z.ltb_ge; apply page_round_up_Z_mono; subst cur h; lia).
    destruct (0 <? cur); cbn; repeat split; reflexivity. }
  destruct V as (V1 & V2 & V3).
  pose proof (brk_model_next_grown h req Hpos ltac:(subst cur h; lia)) as (P1 & P2 & P3 & P4 & P5).
  assert (Ea : a = BrkGrown).
  { destruct a; [reflexivity|]. exfalso. rewrite V3, P5 in Ha. apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (subst cur h; lia). subst cur h. lia. }
  subst a. split; [exact Hd|]. split; [exact Hvo|]. rewrite V3. splits; auto.
  all: first [ reflexivity | rewrite V1; exact Hlz
             | eapply Z.le_trans; [apply (vm_backing_used_cons_map mo _ (vm_brk h, Z_to_bv 64 (req - cur))); rewrite ?V3, ?V1; auto|];
               cbn [snd]; rewrite unsigned_lit by (subst cur h; lia); subst cur h; lia ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MMAP.
Variables (len : Z) (mo : Model).
Let h := m_vmmaps mo.
Let n := mmap_len len.
Hypothesis Hlen : 0 < len.
Hypothesis Hn64 : n < 2^64.

Lemma n_facts : len <= n < len + 4096 /\ n mod 4096 = 0.
Proof. pose proof (mmap_len_ge len Hlen). pose proof (mmap_len_aligned len). unfold n. auto. Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_refuse_can : forall prot, (prot = PROT_NONE \/ prot = PROT_RW) ->
  nstep (NMmap 0 len prot MAPF) mo (efferr ENOMEM) mo []
  /\ dec_mmap len [] (efferr ENOMEM) = Some (MmErr ENOMEM) /\ dec_mmap_none len [] (efferr ENOMEM) = Some (MmErr ENOMEM).
Proof.
  intros prot Hprot. pose proof n_facts as [[N1 N2] N3]. assert (Hl64 : 0 <= len < 2^64) by (unfold n in *; lia). split.
  - apply nstep_mmap_iff. unfold check_mmap. change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false. change (negb (mmap_anon_b (Z_to_bv 64 MAPF))) with false. cbv iota.
    rewrite w_is0_lit by exact Hl64. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct Hprot as [-> | ->].
    + change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false.
      change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
      unfold efferr, eff0. replace (errno_ret_in mmap_errnos (errno_ret ENOMEM)) with true; [reflexivity|].
      symmetry. vm_compute. reflexivity.
    + change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
      unfold efferr, eff0. replace (errno_ret_in mmap_errnos (errno_ret ENOMEM)) with true; [reflexivity|].
      symmetry. vm_compute. reflexivity.
  - unfold dec_mmap, dec_mmap_none, efferr, eff0. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). auto.
Qed.
End MMAP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MMAP_GRANT.
Variables (len r : Z) (mo : Model).
Let h := m_vmmaps mo.
Let n := mmap_len len.
(* [comment removed for export] *)
Hypothesis Hminv : minv mo.
Hypothesis Hlen : 0 < len.
Hypothesis Hr : r mod 4096 = 0 /\ 0 < r /\ r + n <= alloc_ceiling.
Hypothesis Hrf : region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 r) (Z_to_bv 64 n) = true.

Lemma g_facts : len <= n < len + 4096 /\ n mod 4096 = 0 /\ 0 <= len < 2^64 /\ 0 < n < 2^64 /\ 0 < r < 2^64.
Proof.
  pose proof (mmap_len_ge len Hlen). pose proof (mmap_len_aligned len). pose proof alloc_ceiling_lt.
  unfold n in *. repeat split; try lia.
Qed.

Let Htop : alloc_top h = alloc_ceiling := minv_alloc_top mo Hminv.

Let HN := Z_to_bv 64 n.
Let HR := Z_to_bv 64 r.
Definition mmap_grant_maps : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((HR, HN) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Definition mmap_grant_maps_none : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((HR, HN) :: vm_maps h) ((HR, HN) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Lemma errno_not_addr : errno_ret_in mmap_errnos HR = false.
Proof.
  apply errno_ret_in_below; [reflexivity|]. subst HR. pose proof g_facts. rewrite unsigned_lit by lia.
  pose proof alloc_ceiling_lt. unfold two_pow_64. unfold n in *. lia.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_grant_can :
  vm_backing_used mo + n <= vm_limit h ->
  let rsp := mkEffectU HR [] [(HR, HN)] [] [] [] in
  let mo' := with_vmmaps mmap_grant_maps mo in
  nstep (NMmap 0 len PROT_RW MAPF) mo rsp mo' [] /\ dec_mmap len [] rsp = Some (MmOk r)
  /\ m_vmmaps mo' = mmap_grant_maps /\ m_vm_lazy mo' = m_vm_lazy mo /\ m_vm_materialized mo' = m_vm_materialized mo /\ vm_only mo mo'.
Proof.
  intros Hbud rsp mo'. pose proof g_facts as (N1 & N2 & N3 & N4 & N5). destruct Hr as (R1 & R2 & R3).
  assert (Hst : nstep (NMmap 0 len PROT_RW MAPF) mo rsp mo' []).
  { apply nstep_mmap_iff. unfold check_mmap. change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false. change (negb (mmap_anon_b (Z_to_bv 64 MAPF))) with false. cbv iota.
    rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
    subst rsp. cbv iota beta. rewrite errno_not_addr. cbv zeta. rewrite (unsigned_lit len) by lia. fold n. fold h HN. unfold HR. rewrite (unsigned_lit r) by lia. fold HR.
    rewrite Htop, page_size_eq, R1, Z.eqb_refl, (proj2 (Z.ltb_lt _ _) R2), (proj2 (Z.leb_le _ _) R3), Hrf. cbn [andb].
    unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbv iota. fold h. rewrite (proj2 (Z.leb_le _ _) Hbud).
    rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). cbn [andb].
    unfold with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbv iota. reflexivity. }
  split; [exact Hst|]. split.
  - subst rsp. unfold dec_mmap. rewrite !bv_eqb_refl. cbn [andb].
    unfold mmap_addr_ok. unfold HR. rewrite (unsigned_lit r) by lia. fold n. rewrite page_size_eq, R1, Z.eqb_refl, (proj2 (Z.ltb_lt _ _) R2), (proj2 (Z.leb_le _ _) R3). reflexivity.
  - subst mo'. rewrite m_vmmaps_with_vmmaps. repeat split; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_mmap_none_grant_can :
  let rsp := mkEffectU HR [] [] [(HR, HN)] [] [] in
  let mo' := with_vmmaps mmap_grant_maps_none mo in
  nstep (NMmap 0 len PROT_NONE MAPF) mo rsp mo' [] /\ dec_mmap_none len [] rsp = Some (MmOk r)
  /\ m_vmmaps mo' = mmap_grant_maps_none /\ m_vm_lazy mo' = m_vm_lazy mo /\ m_vm_materialized mo' = m_vm_materialized mo /\ vm_only mo mo'.
Proof.
  intros rsp mo'. pose proof g_facts as (N1 & N2 & N3 & N4 & N5). destruct Hr as (R1 & R2 & R3).
  assert (Hst : nstep (NMmap 0 len PROT_NONE MAPF) mo rsp mo' []).
  { apply nstep_mmap_iff. unfold check_mmap. change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false. change (negb (mmap_anon_b (Z_to_bv 64 MAPF))) with false. cbv iota.
    rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
    subst rsp. cbv iota beta. rewrite errno_not_addr. cbv zeta. rewrite (unsigned_lit len) by lia. fold n. fold h HN. unfold HR. rewrite (unsigned_lit r) by lia. fold HR.
    rewrite Htop, page_size_eq, R1, Z.eqb_refl, (proj2 (Z.ltb_lt _ _) R2), (proj2 (Z.leb_le _ _) R3), Hrf. cbn [andb].
    fold h. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). cbn [andb].
    unfold with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbv iota. reflexivity. }
  split; [exact Hst|]. split.
  - subst rsp. unfold dec_mmap_none. rewrite !bv_eqb_refl. cbn [andb].
    unfold mmap_addr_ok. unfold HR. rewrite (unsigned_lit r) by lia. fold n. rewrite page_size_eq, R1, Z.eqb_refl, (proj2 (Z.ltb_lt _ _) R2), (proj2 (Z.leb_le _ _) R3). reflexivity.
  - subst mo'. rewrite m_vmmaps_with_vmmaps. repeat split; try reflexivity.
Qed.
End MMAP_GRANT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nstep_mmap_fixed_kept_can : forall a mo,
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  minv mo ->   (* [comment removed for export] *)
  0 < a -> a mod 4096 = 0 -> a + PGSZ <= alloc_ceiling ->
  region_free (vm_reserved h) aw nw = true -> map_contains (vm_maps h) aw nw = true ->
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo (efferr ENOMEM) mo [] /\ dec_mmap_fixed a PGSZ (efferr ENOMEM) = Some (FxKept ENOMEM).
Proof.
  intros a mo h aw nw Hminv Ha Hal Hc Hrf Hmc. pose proof alloc_ceiling_lt as Hcl. pose proof (minv_alloc_top mo Hminv) as Htop. fold h in Htop. split.
  - apply nstep_mmap_iff. unfold check_mmap. change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false. change (negb (mmap_anon_b (Z_to_bv 64 MAPFX))) with false. cbv iota.
    change (w_is0 (Z_to_bv 64 PGSZ)) with false.
    change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
    change (mmap_fixed_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with true. cbv iota beta zeta.
    change (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))) with PGSZ. fold aw. subst aw. rewrite unsigned_lit by (unfold PGSZ in *; lia).
    replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia).
    fold h. rewrite Htop. rewrite (proj2 (Z.leb_le _ _) Hc). cbn [negb]. rewrite page_size_eq, Hal. cbn [Z.eqb negb].
    rewrite (proj2 (Z.ltb_lt _ _) Ha). cbn [negb]. fold nw. fold h. rewrite Hrf, Hmc. cbn [andb]. unfold efferr, eff0.
    replace (errno_ret_in mmap_errnos (errno_ret ENOMEM)) with true; [reflexivity|]. symmetry. vm_compute. reflexivity.
  - unfold dec_mmap_fixed, efferr, eff0. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nstep_munmap_can : forall a len mo,
  let h := m_vmmaps mo in let n := mmap_len len in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  0 < len -> 0 < a -> a mod 4096 = 0 -> a + n <= alloc_ceiling (* [comment removed for export] *) ->
  map_has (vm_maps h) aw nw = true ->
  let rsp := mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] [] in
  let h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
  let mo' := with_mmap_destroyed aw nw h' mo in
  nstep (NMunmap a len) mo rsp mo' [] /\ dec_munmap a len rsp = Some (RgDone true)
  /\ m_vmmaps mo' = h' /\ vm_only mo mo' /\ (m_vm_lazy mo = [] -> m_vm_lazy mo' = []) /\ (m_vm_materialized mo = [] -> m_vm_materialized mo' = []).
Proof.
  intros a len mo h n aw nw Hlen Ha Hal Hhi0 Hhas rsp h' mo'.
  pose proof alloc_ceiling_lt as Hcl. assert (Hhi : a + n < 2^64) by lia.
  pose proof (mmap_len_ge len Hlen) as N1. fold n in N1.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
  assert (Hst : nstep (NMunmap a len) mo rsp mo' []).
  { apply nstep_munmap_iff. unfold check_munmap. fold aw. rewrite Ua, page_size_eq, Hal. rewrite w_is0_lit by lia.
    replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb].
    rewrite (unsigned_lit len) by lia. fold (mmap_len len). fold n.
    replace (TASK_SIZE <? a + n) with false by (symmetry; apply Z.ltb_ge; unfold TASK_SIZE, alloc_ceiling in *; lia). fold nw. fold h. rewrite Hhas.
    subst rsp. cbv iota beta. change (w_is0 (Z_to_bv 64 0)) with true. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). cbn [andb].
    subst mo' h'. rewrite ?Ua, ?Un. reflexivity. }
  split; [exact Hst|]. split.
  - subst rsp. unfold dec_munmap. change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. fold n. fold nw. rewrite !bv_eqb_refl. reflexivity.
  - subst mo'. unfold with_mmap_destroyed, vm_forget_range. split; [| split; [| split]].
    + rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps. reflexivity.
    + exact (proj1 (proj1 (nstep_mm_vm_only (NMunmap a len) mo _ _ _ I Hst))).
    + intros Hl. destruct mo as [? [? ? ?] ? ? ? ? ? ? ?]; cbn in *. rewrite Hl. reflexivity.
    + intros Hm. destruct mo as [? [? ? ?] ? ? ? ? ? ? ?]; cbn in *. rewrite Hm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MPROTECT.
Variables (a : Z) (mo : Model).
Let h := m_vmmaps mo.
Let aw := Z_to_bv 64 a.
Let nw := Z_to_bv 64 PGSZ.
Hypothesis Ha : 0 < a /\ a mod 4096 = 0 /\ a + PGSZ < 2^64.
Hypothesis Hna : map_contains (vm_noaccess h) aw nw = true.
Hypothesis Hmc : map_contains (vm_maps h) aw nw = true.

Lemma mprotect_gates : forall eff,
  check_mprotect aw nw (Z_to_bv 64 PROT_RW) eff mo =
  match eff with
  | mkEffectU r [] zs [] [] [] =>
      if errno_ret_in mprotect_errnos r then match zs with [] => CheckOk mo [] | _ => CheckReject end
      else if mprotect_budget_ok mo aw nw && w_is0 r && listNN_eqb zs [(aw, nw)] then CheckOk (mprotect_model_next mo aw nw) [] else CheckReject
  | _ => CheckReject
  end.
Proof.
  intros eff. destruct Ha as (A1 & A2 & A3). unfold check_mprotect.
  change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false. cbv iota.
  unfold aw at 1. rewrite unsigned_lit by (unfold PGSZ in *; lia). rewrite page_size_eq, A2. cbn [Z.eqb negb].
  change (w_is0 (Z_to_bv 64 PGSZ)) with false. cbv iota.
  change (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))) with PGSZ. unfold aw at 1. rewrite unsigned_lit by (unfold PGSZ in *; lia).
  replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true. cbv iota beta zeta. fold nw. fold h. rewrite Hna, Hmc. reflexivity.
Qed.

Lemma nstep_mprotect_refuse_can :
  nstep (NMprotect a PGSZ PROT_RW) mo (efferr ENOMEM) mo [] /\ dec_mprotect_rw a PGSZ (efferr ENOMEM) = Some (RgErr ENOMEM).
Proof.
  split.
  - apply nstep_mprotect_iff. fold aw nw. rewrite mprotect_gates. unfold efferr, eff0.
    replace (errno_ret_in mprotect_errnos (errno_ret ENOMEM)) with true; [reflexivity|]. symmetry; vm_compute; reflexivity.
  - unfold dec_mprotect_rw, dec_mprotect, efferr, eff0. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
Qed.

Lemma nstep_mprotect_grant_can :
  mprotect_budget_ok mo aw nw = true ->
  let rsp := mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] [] in
  let mo' := mprotect_model_next mo aw nw in
  nstep (NMprotect a PGSZ PROT_RW) mo rsp mo' [] /\ dec_mprotect_rw a PGSZ rsp = Some (RgDone true)
  /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ)) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  /\ m_vm_lazy mo' = m_vm_lazy mo /\ m_vm_materialized mo' = m_vm_materialized mo /\ vm_only mo mo'.
Proof.
  intros Hb rsp mo'. destruct Ha as (A1 & A2 & A3).
  assert (Hst : nstep (NMprotect a PGSZ PROT_RW) mo rsp mo' []).
  { apply nstep_mprotect_iff. fold aw nw. rewrite mprotect_gates. subst rsp. cbv iota beta.
    replace (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false by (symmetry; vm_compute; reflexivity).
    rewrite Hb. change (w_is0 (Z_to_bv 64 0)) with true. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
  split; [exact Hst|]. split.
  - subst rsp. unfold dec_mprotect_rw, dec_mprotect. change (bv_unsigned (Z_to_bv 64 0) =? 0) with true.
    change (mmap_len PGSZ) with PGSZ. fold aw nw. rewrite !bv_eqb_refl. reflexivity.
  - subst mo'. unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. fold h. unfold aw at 2 3, nw. rewrite !unsigned_lit by (unfold PGSZ in *; lia).
    split; [reflexivity|]. split; [apply m_vm_lazy_with_vmmaps|]. split; [apply m_vm_materialized_with_vmmaps|].
    exact (proj1 (proj1 (nstep_mm_vm_only (NMprotect a PGSZ PROT_RW) mo _ _ _ I Hst))).
Qed.
End MPROTECT.
End RC__1.
