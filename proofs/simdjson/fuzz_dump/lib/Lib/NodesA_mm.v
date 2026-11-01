(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import CatSim ShapeAlg AsanAcct AsanAcctShape AsanCeil BackingAlgebra.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma page_in_ranges_cons' : forall p iv l,
  page_in_ranges p (iv :: l)
  = (((bv_unsigned (fst iv) <=? bv_unsigned p) && (bv_unsigned p + page_size <=? bv_unsigned (fst iv) + bv_unsigned (snd iv)))
     || page_in_ranges p l)%bool.
Proof. reflexivity. Qed.

Lemma page_in_ranges_app' : forall p l1 l2,
  page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2)%bool.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

Lemma page_in_ranges_true' : forall p l,
  page_in_ranges p l = true <->
  exists iv, In iv l /\ bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
  - intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_covered : forall p l, page_in_ranges p l = true -> covered l (bv_unsigned p) = true.
Proof.
  intros p l Hp. apply page_in_ranges_true' in Hp as (iv & Hin & H1 & H2).
  unfold covered. apply existsb_exists. exists iv. split; [exact Hin|].
  unfold in_iv, in_rng, B, S. unfold page_size in H2. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma page_in_ranges_subtract_out' : forall (p : word) l lo hi,
  ivs_wf l -> lo <= hi ->
  (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
  page_in_ranges p (maps_subtract l lo hi) = page_in_ranges p l.
Proof.
  intros p l lo hi Hwf Hlh Hout. pose proof (u64_range p) as Rp. unfold page_size in *.
  induction l as [|[a sz] l IH]; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. rewrite page_in_ranges_app', page_in_ranges_cons', (IH Hl). f_equal.
  cbn [fst snd]. unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract. rewrite page_in_ranges_app'.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er];
    cbn [page_in_ranges existsb fst snd app orb]; unfold page_size; rewrite ?unsigned_lit by lia; rewrite ?orb_false_r.
  - destruct Hout as [Hout|Hout].
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.

Lemma page_in_ranges_subtract_in' : forall (p : word) l lo hi,
  ivs_wf l -> lo <= bv_unsigned p < hi ->
  page_in_ranges p (maps_subtract l lo hi) = false.
Proof.
  intros p l lo hi Hwf Hp.
  destruct (page_in_ranges p (maps_subtract l lo hi)) eqn:E; [|reflexivity]. exfalso.
  pose proof (page_in_ranges_covered p _ E) as C.
  destruct (maps_subtract_sem l lo hi Hwf ltac:(lia)) as (_ & _ & Cv). rewrite Cv in C.
  apply andb_prop in C as [_ C]. apply negb_true_iff in C. unfold in_rng in C.
  apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; lia.
Qed.

Lemma page_in_ranges_cons_in' : forall (p a n : word) l,
  bv_unsigned a <= bv_unsigned p -> bv_unsigned p + page_size <= bv_unsigned a + bv_unsigned n ->
  page_in_ranges p ((a, n) :: l) = true.
Proof.
  intros p a n l H1 H2. rewrite page_in_ranges_cons'. cbn [fst snd]. apply orb_true_iff. left.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_cons_out' : forall (p a n : word) l,
  (bv_unsigned p + page_size <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned p) ->
  page_in_ranges p ((a, n) :: l) = page_in_ranges p l.
Proof.
  intros p a n l H. rewrite page_in_ranges_cons'. cbn [fst snd]. unfold page_size in *.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity. exfalso. lia.
Qed.

Lemma page_base_facts' : forall a : word,
  bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
  /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)) as M.
  assert (H0 : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by (split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]|]; lia).
  rewrite unsigned_lit by lia. split; [lia|]. split; [lia|]. apply Z.mod_mul. lia.
Qed.

Lemma page_of_byte_in_aligned' : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= bv_unsigned x < hi ->
  lo <= bv_unsigned (page_base x) /\ bv_unsigned (page_base x) + 4096 <= hi.
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts' x) as (P1 & P2 & P3).
  set (p := bv_unsigned (page_base x)) in *.
  pose proof (Z.div_mod p 4096 ltac:(lia)) as Dp. pose proof (Z.div_mod lo 4096 ltac:(lia)) as Dl.
  pose proof (Z.div_mod hi 4096 ltac:(lia)) as Dh. rewrite P3 in Dp. rewrite Hlo in Dl. rewrite Hhi in Dh.
  split; nia.
Qed.

Lemma page_of_byte_out_aligned' : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
  bv_unsigned (page_base x) + 4096 <= lo \/ hi <= bv_unsigned (page_base x).
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts' x) as (P1 & P2 & P3).
  set (p := bv_unsigned (page_base x)) in *.
  pose proof (Z.div_mod p 4096 ltac:(lia)) as Dp. pose proof (Z.div_mod lo 4096 ltac:(lia)) as Dl.
  pose proof (Z.div_mod hi 4096 ltac:(lia)) as Dh. rewrite P3 in Dp. rewrite Hlo in Dl. rewrite Hhi in Dh.
  destruct Hx as [Hx|Hx]; [left|right]; nia.
Qed.

Lemma aligned_page_out : forall (p : word) lo hi,
  bv_unsigned p mod 4096 = 0 -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> (bv_unsigned p < lo \/ hi <= bv_unsigned p) ->
  bv_unsigned p + 4096 <= lo \/ hi <= bv_unsigned p.
Proof.
  intros p lo hi Hp Hlo Hhi Hx.
  pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)) as Dp. pose proof (Z.div_mod lo 4096 ltac:(lia)) as Dl.
  rewrite Hp in Dp. rewrite Hlo in Dl. destruct Hx as [Hx|Hx]; [left|right]; nia.
Qed.

Lemma zeros_cover_one : forall (a n x : word),
  zeros_cover [(a, n)] x = ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n))%bool.
Proof. intros. unfold zeros_cover. cbn [existsb fst snd]. apply orb_false_r. Qed.

Lemma zeros_cover_nil : forall x, zeros_cover [] x = false.
Proof. reflexivity. Qed.

Lemma apply_zeros_at : forall m zs x, apply_zeros m zs x = if zeros_cover zs x then Some (Z_to_bv 8 0) else m x.
Proof. intros m [|z zs] x; reflexivity. Qed.

Lemma apply_unmaps_at : forall m us x, apply_unmaps m us x = if zeros_cover us x then None else m x.
Proof. intros m [|u us] x; reflexivity. Qed.

Definition lazy_in_maps (mo : Model) : Prop :=
  forall iv, In iv (m_vm_lazy mo) -> 0 < bv_unsigned (snd iv) ->
    exists e, In e (vm_maps (m_vmmaps mo)) /\ bv_unsigned (fst e) <= bv_unsigned (fst iv)
              /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned (fst e) + bv_unsigned (snd e).

Lemma region_free_disjoint : forall l (lo n : word) e, region_free l lo n = true -> In e l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned lo.
Proof.
  induction l as [|[b s] l IH]; intros lo n e Hf Hin; [destruct Hin|].
  cbn [region_free] in Hf. apply andb_true_iff in Hf as [H1 H2]. destruct Hin as [<-|Hin]; [|exact (IH _ _ _ H2 Hin)].
  apply negb_true_iff in H1. unfold iv_overlap in H1. cbn [fst snd].
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

Lemma lazy_off_free : forall mo (a n : word) (x : word),
  lazy_in_maps mo -> region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
  bv_unsigned a mod 4096 = 0 -> bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
  page_in_ranges (page_base x) (m_vm_lazy mo) = false.
Proof.
  intros mo a n x Hlm Hf Hal Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy mo)) eqn:E; [|reflexivity].
  exfalso. apply page_in_ranges_true' in E as (iv & Hin & H1 & H2). unfold page_size in H2.
  destruct (Hlm iv Hin ltac:(lia)) as (e & He & E1 & E2).
  pose proof (region_free_disjoint _ a n e Hf (in_or_app _ _ _ (or_intror He))) as D.
  pose proof (page_base_facts' x) as (P1 & P2 & P3).
  pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as Dp.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as Da. rewrite P3 in Dp. rewrite Hal in Da.
  assert (bv_unsigned a <= bv_unsigned (page_base x)) by nia. lia.
Qed.

Lemma iv_subtract_starts : forall (a sz : word) lo hi q,
  iv_wf (a, sz) -> In q (iv_subtract a sz lo hi) -> bv_unsigned a <= bv_unsigned (fst q).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst]. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst]. rewrite unsigned_lit by lia. lia.
Qed.

Lemma ranges_from_b_subtract : forall L lo hi top, ivs_wf L ->
  ranges_from_b L top = true -> ranges_from_b (maps_subtract L lo hi) top = true.
Proof.
  induction L as [|[a sz] L IH]; intros lo hi top Hwf H; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. unfold ranges_from_b in *. cbn [forallb maps_subtract fst] in *.
  apply andb_true_iff in H as [H1 H2]. rewrite forallb_app. apply andb_true_intro. split; [|exact (IH _ _ _ Hl H2)].
  apply forallb_forall. intros q Hq. apply Z.leb_le. apply Z.leb_le in H1.
  pose proof (iv_subtract_starts a sz lo hi q Ha Hq). lia.
Qed.

Lemma ranges_from_b_cons : forall (a n : word) L top, top <= bv_unsigned a ->
  ranges_from_b L top = true -> ranges_from_b ((a, n) :: L) top = true.
Proof. intros a n L top H1 H2. unfold ranges_from_b in *. cbn [forallb fst]. rewrite H2, (proj2 (Z.leb_le _ _) H1). reflexivity. Qed.

Lemma eager_used_sem' : forall m, ivs_wf (vm_maps (m_vmmaps m)) ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
  intros m Wm. unfold eager_used, vm_backed_maps. rewrite <- maps_subtract_all_app_cuts. exact (proj1 (live_msa _ _ Wm)).
Qed.

Lemma iv_count_le_size : forall P p, iv_count P p <= S p.
Proof. intros P p. unfold iv_count. pose proof (zcount_le_len P (B p) (Z.to_nat (S p))). pose proof (S_range p). lia. Qed.

Lemma sum_count_filter_le' : forall P f l, sum_count P (List.filter f l) <= sum_count P l.
Proof.
  intros P f l. induction l as [|q l IH]; cbn [List.filter sum_count]; [lia|].
  pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))). unfold iv_count in *. destruct (f q); cbn [sum_count]; unfold iv_count; lia.
Qed.

Definition mdl_mmap_rw (mo : Model) (a n : word) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((a, n) :: vm_maps (m_vmmaps mo))
                 (vm_noaccess (m_vmmaps mo)) (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo))
                 (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.

Definition mdl_fixed (flags : word) (mo : Model) (addr n : word) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo).

Definition mdl_munmap (mo : Model) (addr n : word) : Model :=
  with_mmap_destroyed addr n
    (mkVmMapsFull (vm_reserved (m_vmmaps mo)) (map_remove (vm_maps (m_vmmaps mo)) addr)
       (maps_subtract (vm_noaccess (m_vmmaps mo)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo))
       (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.

Definition flags50 : word := Z_to_bv 64 50.
Definition flags16434 : word := Z_to_bv 64 16434.

Lemma noreserve50 : mmap_noreserve_b flags50 = false.
Proof. vm_compute. reflexivity. Qed.
Lemma noreserve16434 : mmap_noreserve_b flags16434 = true.
Proof. vm_compute. reflexivity. Qed.

Section Proj.
Variables (mo : Model) (a n : word).
Let h := m_vmmaps mo.

Lemma mdl_mmap_rw_vmmaps : m_vmmaps (mdl_mmap_rw mo a n) = mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_lazy : m_vm_lazy (mdl_mmap_rw mo a n) = m_vm_lazy mo. Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_mat : m_vm_materialized (mdl_mmap_rw mo a n) = m_vm_materialized mo. Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_fds : m_fds (mdl_mmap_rw mo a n) = m_fds mo. Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_fs : m_fs (mdl_mmap_rw mo a n) = m_fs mo. Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_halted : m_halted (mdl_mmap_rw mo a n) = m_halted mo. Proof. reflexivity. Qed.

Lemma mdl_fixed_vmmaps : forall flags, m_vmmaps (mdl_fixed flags mo a n) = mmap_fixed_rw_next h a n.
Proof. intros flags. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mdl_fixed_lazy50 : m_vm_lazy (mdl_fixed flags50 mo a n) = maps_subtract (m_vm_lazy mo) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. rewrite noreserve50. reflexivity. Qed.
Lemma mdl_fixed_lazy16434 : m_vm_lazy (mdl_fixed flags16434 mo a n)
  = lazy_interior a n ++ maps_subtract (m_vm_lazy mo) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. rewrite noreserve16434. reflexivity. Qed.
Lemma mdl_fixed_mat : forall flags, m_vm_materialized (mdl_fixed flags mo a n)
  = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized mo).
Proof. intros flags. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mdl_fixed_fds : forall flags, m_fds (mdl_fixed flags mo a n) = m_fds mo.
Proof. intros flags. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mdl_fixed_fs : forall flags, m_fs (mdl_fixed flags mo a n) = m_fs mo.
Proof. intros flags. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mdl_fixed_halted : forall flags, m_halted (mdl_fixed flags mo a n) = m_halted mo.
Proof. intros flags. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.

Lemma mdl_munmap_vmmaps : m_vmmaps (mdl_munmap mo a n) = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof. reflexivity. Qed.
Lemma mdl_munmap_lazy : m_vm_lazy (mdl_munmap mo a n) = maps_subtract (m_vm_lazy mo) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma mdl_munmap_mat : m_vm_materialized (mdl_munmap mo a n)
  = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized mo).
Proof. reflexivity. Qed.
Lemma mdl_munmap_fds : m_fds (mdl_munmap mo a n) = m_fds mo. Proof. reflexivity. Qed.
Lemma mdl_munmap_fs : m_fs (mdl_munmap mo a n) = m_fs mo. Proof. reflexivity. Qed.
Lemma mdl_munmap_halted : m_halted (mdl_munmap mo a n) = m_halted mo. Proof. reflexivity. Qed.
End Proj.

Lemma covered_subtract : forall l lo hi x, ivs_wf l -> lo <= hi ->
  covered (maps_subtract l lo hi) x = (covered l x && negb (in_rng lo hi x))%bool.
Proof. intros l lo hi x Wl Hlh. destruct (maps_subtract_sem l lo hi Wl Hlh) as (_ & _ & C). apply C. Qed.

Lemma eager_used_mmap_rw_le : forall mo a n, ivs_wf (vm_maps (m_vmmaps mo)) -> bv_unsigned a + bv_unsigned n <= 2^64 ->
  eager_used (mdl_mmap_rw mo a n) <= eager_used mo + bv_unsigned n.
Proof.
  intros mo a n Wm Han.
  assert (Wm' : ivs_wf (vm_maps (m_vmmaps (mdl_mmap_rw mo a n)))).
  { rewrite mdl_mmap_rw_vmmaps. cbn [vm_maps]. apply ivs_wf_cons; [exact Han| exact Wm]. }
  rewrite (eager_used_sem' _ Wm'), (eager_used_sem' _ Wm). rewrite mdl_mmap_rw_vmmaps, mdl_mmap_rw_lazy. cbn [vm_maps vm_noaccess sum_count].
  pose proof (iv_count_le_size (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (a, n)) as Hle.
  unfold S in Hle. cbn [snd] in Hle. lia.
Qed.

Lemma eager_used_fixed50_le : forall mo a n, model_ivs_wf mo ->
  eager_used (mdl_fixed flags50 mo a n)
  <= eager_used mo + overlap_sum (vm_maps (m_vmmaps mo)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
  intros mo a n (Wm & Wn & Wl & _). pose proof (u64_range n) as Rn.
  remember (bv_unsigned a) as lo eqn:Elo. remember (lo + bv_unsigned n) as hi eqn:Ehi.
  assert (Hlh : lo <= hi) by lia.
  assert (Wm' : ivs_wf (vm_maps (m_vmmaps (mdl_fixed flags50 mo a n)))) by (rewrite mdl_fixed_vmmaps; exact Wm).
  rewrite (eager_used_sem' _ Wm'), (eager_used_sem' _ Wm). rewrite mdl_fixed_vmmaps, mdl_fixed_lazy50.
  unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess]. rewrite <- Elo, <- Ehi. unfold overlap_sum.
  eapply Z.le_trans; [| apply (sum_count_or_le _ (in_rng lo hi))].
  apply sum_count_mono. intros x Hx. rewrite !covered_app in *.
  rewrite (covered_subtract _ lo hi x Wn Hlh), (covered_subtract _ lo hi x Wl Hlh) in Hx.
  destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng lo hi x); cbn in *; congruence.
Qed.

Lemma eager_used_fixed16434_le : forall mo a n, model_ivs_wf mo ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2^64 ->
  eager_used (mdl_fixed flags16434 mo a n) <= eager_used mo.
Proof.
  intros mo a n (Wm & Wn & Wl & _) Hal Hnl Hpos Hend.
  assert (Hli : lazy_interior a n = [(a, n)]) by (apply lazy_interior_aligned; assumption).
  remember (bv_unsigned a) as lo eqn:Elo. remember (lo + bv_unsigned n) as hi eqn:Ehi.
  assert (Hlh : lo <= hi) by lia.
  assert (Wm' : ivs_wf (vm_maps (m_vmmaps (mdl_fixed flags16434 mo a n)))) by (rewrite mdl_fixed_vmmaps; exact Wm).
  rewrite (eager_used_sem' _ Wm'), (eager_used_sem' _ Wm). rewrite mdl_fixed_vmmaps, mdl_fixed_lazy16434.
  rewrite Hli.
  unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess]. rewrite <- Elo, <- Ehi.
  apply sum_count_mono. intros x Hx. rewrite !covered_app in *. cbn [app] in Hx.
  unfold covered at 2 in Hx. cbn [existsb] in Hx. fold (covered (maps_subtract (m_vm_lazy mo) lo hi) x) in Hx.
  rewrite (covered_subtract _ lo hi x Wn Hlh), (covered_subtract _ lo hi x Wl Hlh) in Hx.
  unfold in_iv, B, S in Hx. cbn [fst snd] in Hx. rewrite <- Elo, <- Ehi in Hx.
  destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng lo hi x); cbn in *; congruence.
Qed.

Lemma eager_used_munmap_le : forall mo a n, model_ivs_wf mo ->
  eager_used (mdl_munmap mo a n)
  <= eager_used mo + overlap_sum (map_remove (vm_maps (m_vmmaps mo)) a) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof.
  intros mo a n (Wm & Wn & Wl & _). pose proof (u64_range n) as Rn.
  remember (bv_unsigned a) as lo eqn:Elo. remember (lo + bv_unsigned n) as hi eqn:Ehi.
  assert (Hlh : lo <= hi) by lia.
  assert (Wr : ivs_wf (map_remove (vm_maps (m_vmmaps mo)) a)) by (apply ivs_wf_filter; exact Wm).
  assert (Wm' : ivs_wf (vm_maps (m_vmmaps (mdl_munmap mo a n)))) by (rewrite mdl_munmap_vmmaps; exact Wr).
  rewrite (eager_used_sem' _ Wm'), (eager_used_sem' _ Wm). rewrite mdl_munmap_vmmaps, mdl_munmap_lazy.
  cbn [vm_maps vm_noaccess]. rewrite <- Elo, <- Ehi. unfold overlap_sum.
  eapply Z.le_trans; [| apply Z.add_le_mono_r; apply (sum_count_filter_le' _ (fun p => negb (bv_eqb (fst p) a)))].
  fold (map_remove (vm_maps (m_vmmaps mo)) a).
  eapply Z.le_trans; [| apply (sum_count_or_le _ (in_rng lo hi))].
  apply sum_count_mono. intros x Hx. rewrite !covered_app in *.
  rewrite (covered_subtract _ lo hi x Wn Hlh), (covered_subtract _ lo hi x Wl Hlh) in Hx.
  destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng lo hi x); cbn in *; congruence.
Qed.

Lemma MInv_cut : forall A A' mo mo' lo hi,
  MInv A mo ->
  (forall p, page_allowedb A p = true -> page_allowedb A' p = true) ->
  lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  m_vm_materialized mo' = List.filter (page_outside_range lo hi) (m_vm_materialized mo) ->
  (forall p, bv_unsigned p + 4096 <= lo \/ hi <= bv_unsigned p ->
     page_in_ranges p (m_vm_lazy mo) = true -> page_in_ranges p (m_vm_lazy mo') = true) ->
  eager_used mo' + A_bytes A' <= vm_limit (m_vmmaps mo') ->
  MInv A' mo'.
Proof.
  intros A A' mo mo' lo hi [M1 M2 M3 M4 M5] Hsub Hlo Hhi Hmat Hlz Hb. constructor.
  - rewrite Hmat. apply NoDup_filter. exact M1.
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp _]. exact (M2 p Hp).
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp _]. exact (Hsub p (M3 p Hp)).
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp Ho]. apply Hlz; [|exact (M4 p Hp)].
    apply aligned_page_out; [exact (M2 p Hp)| exact Hlo| exact Hhi|].
    unfold page_outside_range in Ho. apply negb_true_iff in Ho.
    apply andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho; left; lia| apply Z.ltb_ge in Ho; right; lia].
  - exact Hb.
Qed.

Lemma page_in_ranges_subtract_keep : forall l lo hi (p : word), ivs_wf l -> lo <= hi ->
  bv_unsigned p + 4096 <= lo \/ hi <= bv_unsigned p ->
  page_in_ranges p l = true -> page_in_ranges p (maps_subtract l lo hi) = true.
Proof. intros l lo hi p Wl Hlh Ho Hp. rewrite (page_in_ranges_subtract_out' p l lo hi Wl Hlh Ho). exact Hp. Qed.

Lemma HID_cut_in : forall A mo mo' lo hi (x : word), ivs_wf (m_vm_lazy mo) -> lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  hi <= 2^47 ->
  m_vm_lazy mo' = maps_subtract (m_vm_lazy mo) lo hi -> lo <= bv_unsigned x < hi -> HID A mo' x = false.
Proof.
  intros A mo mo' lo hi x Wl Hlo Hhi Htop Hlz Hx. unfold HID, mkH. rewrite Hlz.
  destruct (page_of_byte_in_aligned' x lo hi Hlo Hhi Hx) as [P1 P2]. pose proof (page_base_facts' x) as (_ & P3 & _).
  rewrite (page_in_ranges_subtract_in' (page_base x) _ lo hi Wl ltac:(lia)). cbn.
  apply Z.leb_gt. lia.
Qed.

Lemma HID_cut_out : forall A mo mo' lo hi (x : word), ivs_wf (m_vm_lazy mo) -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  m_vm_lazy mo' = maps_subtract (m_vm_lazy mo) lo hi -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
  mkH (m_vm_lazy mo') A x = mkH (m_vm_lazy mo) A x.
Proof.
  intros A mo mo' lo hi x Wl Hlo Hhi Hlh Hlz Hx. unfold mkH. rewrite Hlz.
  rewrite (page_in_ranges_subtract_out' (page_base x) _ lo hi Wl Hlh); [reflexivity|].
  unfold page_size. exact (page_of_byte_out_aligned' x lo hi Hlo Hhi Hx).
Qed.

Lemma noaccess_cut_out : forall l lo hi (x : word), ivs_wf l -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
  page_in_ranges (page_base x) (maps_subtract l lo hi) = page_in_ranges (page_base x) l.
Proof.
  intros l lo hi x Wl Hlo Hhi Hlh Hx. apply page_in_ranges_subtract_out'; [exact Wl| exact Hlh|].
  unfold page_size. exact (page_of_byte_out_aligned' x lo hi Hlo Hhi Hx).
Qed.

Lemma nretA_mm_mem : forall ms r zs us x,
  ms_mem (nretA ms (mkEffectU r [] zs us [] [])) x
  = if zeros_cover zs x then Some (Z_to_bv 8 0) else if zeros_cover us x then None else ms_mem ms x.
Proof. intros ms r zs us x. unfold nretA, advance_past_svc, apply_effect. cbn. rewrite apply_zeros_at, apply_unmaps_at. reflexivity. Qed.

Lemma restrict_nretA_mm : forall H H' ms r zs us,
  (forall x, zeros_cover zs x = true -> H' x = false) ->
  (forall x, zeros_cover zs x = false -> zeros_cover us x = false -> H' x = H x) ->
  restrict H' (nretA ms (mkEffectU r [] zs us [] [])) = nretA (restrict H ms) (mkEffectU r [] zs us [] []).
Proof.
  intros H H' ms r zs us Hz Hout. destruct ms.
  unfold restrict, nretA, advance_past_svc, apply_effect. cbn. f_equal.
  apply functional_extensionality. intros x. unfold mrestrict. rewrite !apply_zeros_at, !apply_unmaps_at.
  destruct (zeros_cover zs x) eqn:Ez; [rewrite (Hz x Ez); reflexivity|].
  destruct (zeros_cover us x) eqn:Eu; [destruct (H' x); reflexivity|].
  rewrite (Hout x Ez Eu). reflexivity.
Qed.

Section MmNode.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

Lemma node_ok_mm : forall ms mo x8 (I : Type) (eff : I -> SyscallEffect) (mdl : I -> Model),
  m_halted mo = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec_acfg (sys_input segs ms x8) mo (Ok (eff i) (mdl i) [])) ->
  (forall o, syscall_spec_acfg (sys_input segs ms x8) mo o -> exists i, o = Ok (eff i) (mdl i) []) ->
  (forall i, syscall_effect_accesses (eff i) = []) ->
  (forall i, m_halted (mdl i) = None) ->
  node_ok segs (mkCfg ms mo) I (fun _ => []) (fun i => mkCfg (nretA ms (eff i)) (mdl i)).
Proof.
  intros ms mo x8 I eff mdl Live0 Pend Sound Onto NoAcc LiveN. split.
  - intros k.
    assert (Mat : materialize_model_accesses (mdl k) (syscall_effect_accesses (eff k)) = Some (mdl k)).
    { rewrite (NoAcc k). apply materialize_model_accesses_nil. }
    exact (sstep_cfg_syscall_acfg segs ms mo x8 (eff k) (mdl k) (mdl k) [] Live0 Pend (Sound k) (LiveN k) Mat).
  - intros out dest Step.
    pose proof (sstep_cfg_sys_inv_acfg segs ms mo x8 out dest Pend Step) as Cases. cbv zeta in Cases.
    destruct Cases as [Normal|[Exited|[Killed|Unmod]]].
    4: { destruct Unmod as [SpecU _]. destruct (Onto _ SpecU) as [k Bad]. discriminate Bad. }
    3: { destruct Killed as (e1 & m1 & ev1 & sig & Spec1 & Sig1 & _).
         destruct (Onto _ Spec1) as [k Same]. injection Same as _ Em _. subst m1.
         rewrite (m_killed_of_m_halted_none _ (LiveN k)) in Sig1. discriminate Sig1. }
    2: { destruct Exited as (e1 & m1 & ev1 & code & Spec1 & Code1 & _).
         destruct (Onto _ Spec1) as [k Same]. injection Same as _ Em _. subst m1.
         rewrite (LiveN k) in Code1. discriminate Code1. }
    destruct Normal as (e1 & m1 & ev1 & Spec1 & _ & Tail).
    destruct (Onto _ Spec1) as [k Same]. injection Same as Ee Em Ev. subst e1 m1 ev1.
    rewrite (NoAcc k), materialize_model_accesses_nil in Tail. destruct Tail as [Eout Edest].
    exists k. split; [exact Eout|]. rewrite Edest. reflexivity.
Qed.

Theorem ast_node_mm : forall A A' Pm PM (I : Type) (i0 : I) (K : I -> machine_state -> Prop) (KM : I -> Model -> Prop)
    ms mo x8 (r : I -> word) (zs us : I -> list (word * word)) (mdl : I -> Model) T,
  AST segtop A Pm PM (mkCfg ms mo) ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec_acfg (sys_input segs ms x8) mo (Ok (mkEffectU (r i) [] (zs i) (us i) [] []) (mdl i) [])) ->
  (forall o, syscall_spec_acfg (sys_input segs ms x8) mo o -> exists i, o = Ok (mkEffectU (r i) [] (zs i) (us i) [] []) (mdl i) []) ->
  (forall i, macct segtop A' (mdl i)) ->
  (forall i x, zeros_cover (zs i) x = true -> HID A' (mdl i) x = false) ->
  (forall i x, zeros_cover (us i) x = true -> HID A' (mdl i) x = false) ->
  (forall i x, zeros_cover (zs i) x = false -> zeros_cover (us i) x = false -> mkH (m_vm_lazy (mdl i)) A' x = mkH (m_vm_lazy mo) A x) ->
  (forall i x, HID A' (mdl i) x = true ->
     page_in_ranges (page_base x) (vm_noaccess (m_vmmaps (mdl i))) = page_in_ranges (page_base x) (vm_noaccess (m_vmmaps mo))) ->
  (forall i, K i (nretA (restrict (HID A mo) ms) (mkEffectU (r i) [] (zs i) (us i) [] []))) ->
  (forall i, KM i (mdl i)) ->
  (forall i c', AST segtop A' (K i) (KM i) c' -> realizes segs c' T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros A A' Pm PM I i0 K KM ms mo x8 r zs us mdl T Start Pend Sound Onto Acct ZsHid UsHid Outside NoacEq Kpost KMpost Cont.
  destruct Start as (Acct0 & Pre & PreM & Zero0). cbn [cfg_ms cfg_model] in *.
  pose proof Acct0 as (_ & _ & Live0 & _).
  assert (Node : node_ok segs (mkCfg ms mo) I (fun _ => [])
                   (fun k => mkCfg (nretA ms (mkEffectU (r k) [] (zs k) (us k) [] [])) (mdl k))).
  { apply (node_ok_mm ms mo x8 I (fun k => mkEffectU (r k) [] (zs k) (us k) [] []) mdl Live0 Pend Sound Onto).
    - intros k. reflexivity.
    - intros k. destruct (Acct k) as (_ & _ & LiveK & _). exact LiveK. }
  assert (Next : forall k, AST segtop A' (K k) (KM k) (mkCfg (nretA ms (mkEffectU (r k) [] (zs k) (us k) [] [])) (mdl k))).
  { intros k. split; [exact (Acct k)|]. cbn [cfg_ms cfg_model]. split; [|split; [exact (KMpost k)|]].
    - rewrite (restrict_nretA_mm (HID A mo) (HID A' (mdl k)) ms (r k) (zs k) (us k) (ZsHid k)); [exact (Kpost k)|].
      intros x Zoff Uoff. unfold HID. rewrite (Outside k x Zoff Uoff). reflexivity.
    - intros x Hidden Open. cbn [cfg_ms cfg_model] in *. rewrite nretA_mm_mem.
      destruct (zeros_cover (zs k) x) eqn:Zon; [reflexivity|].
      pose proof (HID_of_mkH A' (mdl k) x Hidden) as HidK.
      destruct (zeros_cover (us k) x) eqn:Uon.
      + rewrite (UsHid k x Uon) in HidK. discriminate HidK.
      + rewrite (NoacEq k x HidK) in Open. rewrite (Outside k x Zon Uon) in Hidden. exact (Zero0 x Hidden Open). }
  pose proof (realizes_nonempty segs _ _ (Cont i0 _ (Next i0))) as EmptyOk.
  eapply rz_conseq.
  - apply (rz_node segs _ I (fun _ => []) _ (fun _ => T) i0 Node). intros k. exact (Cont k _ (Next k)).
  - intros tr. split.
    + intros [_ Emit]. exact (proj1 (t_emit_nil_eq T EmptyOk tr) Emit).
    + intros Ttr. exists i0. exact (proj2 (t_emit_nil_eq T EmptyOk tr) Ttr).
Qed.

End MmNode.

Lemma vm_backing_used_le' : forall A mo, A_wf A -> MInv A mo -> vm_backing_used mo <= eager_used mo + A_bytes A.
Proof.
  intros A mo Hwf HM. rewrite vm_backing_used_split. destruct HM as [M1 M2 M3 M4 M5].
  pose proof (allowed_pages_bound A (m_vm_materialized mo) Hwf M1 M2 M3). lia.
Qed.

Lemma A_bytes_nonneg : forall A, A_wf A -> 0 <= A_bytes A.
Proof.
  induction A as [|iv A IH]; intros HA; cbn [A_bytes]; [lia|].
  inversion HA as [|? ? (H1 & _ & _) HA']; subst. pose proof (IH HA'). lia.
Qed.

Lemma noreserve34 : mmap_noreserve_b (Z_to_bv 64 34) = false.
Proof. vm_compute. reflexivity. Qed.

Definition grant_ok34 (mo : Model) (nZ : Z) (a : word) : Prop :=
  (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps mo))%Z
  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true
  /\ mmap_noreserve_backed_ok (Z_to_bv 64 34) mo nZ = true.

Lemma mmap34_char : forall segs ms mo len o,
  0 < len < 2^64 ->
  areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 3 -> areg ms 13 = Z_to_bv 64 34 -> areg ms 15 = Z_to_bv 64 0 ->
  m_halted mo = None ->
  mmap_grant_refusable (Z_to_bv 64 34) mo (page_round_up_Z len) = false ->
  syscall_spec_acfg (sys_input segs ms (Z_to_bv 64 222)) mo o <->
  exists a, grant_ok34 mo (page_round_up_Z len) a
    /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]) (mdl_mmap_rw mo a (Z_to_bv 64 (page_round_up_Z len))) [].
Proof.
  intros segs ms mo len o Len R11 R12 R13 R15 Live0 NotRef.
  assert (Num : bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 222))) = 222).
  { rewrite in_sysno_sys_input. apply unsigned_lit. lia. }
  assert (LenU : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (Backing : forall a, with_mmap_backing (Z_to_bv 64 34) a (Z_to_bv 64 (page_round_up_Z len))
      (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((a, Z_to_bv 64 (page_round_up_Z len)) :: vm_maps (m_vmmaps mo))
         (vm_noaccess (m_vmmaps mo)) (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo))
         (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo)
      = mdl_mmap_rw mo a (Z_to_bv 64 (page_round_up_Z len))).
  { intros a. unfold with_mmap_backing. rewrite noreserve34. reflexivity. }
  assert (Shape : forall o', syscall_spec (sys_input segs ms (Z_to_bv 64 222)) mo o' <->
      mmap_err_out mo o' \/ exists a, grant_ok34 mo (page_round_up_Z len) a /\
        o' = Ok (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]) (mdl_mmap_rw mo a (Z_to_bv 64 (page_round_up_Z len))) []).
  { intros o'. rewrite (syscall_spec_222 _ mo o' Num).
    rewrite in_a1_si, in_a2_si, in_a3_si, in_a5_si, R11, R12, R13, R15.
    assert (Nz : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
    pose proof (mmap_rw_outcome (in_arg (sys_input segs ms (Z_to_bv 64 222)) 0) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 34)
                  (in_arg (sys_input segs ms (Z_to_bv 64 222)) 4) (Z_to_bv 64 0) (sys_input segs ms (Z_to_bv 64 222)) mo o'
                  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Nz ltac:(vm_compute; reflexivity)) as Rw.
    cbv zeta in Rw. rewrite LenU in Rw. rewrite Rw. clear Rw.
    split; (intros [Refuse|(a & Conds & Eo)]; [left; exact Refuse| right; exists a; split; [exact Conds|]]).
    - rewrite Eo, Backing. reflexivity.
    - rewrite Eo, <- Backing. reflexivity. }
  split.
  - intros [Spec Guard]. apply Shape in Spec. destruct Spec as [(e & Ein & Eo)|Granted]; [|exact Granted].
    exfalso. subst o.
    destruct (not_refusable_grant_conj _ _ _ NotRef) as (Backed & a & Aal & Apos & Atop & Afree).
    refine (Guard Live0 _).
    apply (refusal_spurious_of_grant ACFG _ mo _ (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))])
             (mdl_mmap_rw mo a (Z_to_bv 64 (page_round_up_Z len))) []).
    + exact (acfg_family_off_222 _ Num).
    + rewrite (refusal_b_222 _ mo _ Num). exact (ret_in_errnos_errno _ e Ein).
    + apply Shape. right. exists a. split; [|reflexivity].
      exact (conj Aal (conj Apos (conj Atop (conj Afree Backed)))).
    + rewrite (refusal_b_222 _ mo _ Num). exact (ret_in_errnos_ENOMEM_aligned a Aal).
  - intros Granted. pose proof Granted as (a & (Aal & _) & Eo). subst o.
    apply syscall_spec_acfg_nonrefusal.
    + apply Shape. right. exact Granted.
    + rewrite (refusal_b_222 _ mo _ Num). exact (ret_in_errnos_ENOMEM_aligned a Aal).
Qed.

Section Rule1.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

Theorem ast_mmap_anon_rw : forall A Pm PM (G : word -> Prop) (K : word -> machine_state -> Prop) (KM : word -> Model -> Prop) len,
  0 < len < 2^64 ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 34 /\ areg ms 15 = Z_to_bv 64 0
       /\ forall a, G a -> K a (nretA ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo -> model_ivs_wf mo /\ lazy_in_maps mo
       /\ vm_gap_available (m_vmmaps mo) (page_round_up_Z len) = true
       /\ eager_used mo + page_round_up_Z len + A_bytes A <= vm_limit (m_vmmaps mo)
       /\ forall a, grant_ok34 mo (page_round_up_Z len) a -> G a /\ KM a (mdl_mmap_rw mo a (Z_to_bv 64 (page_round_up_Z len)))) ->
  (forall mo, PM mo -> alloc_top (m_vmmaps mo) <= 2^47) ->
  cps segs (AST segtop A Pm PM) (fun c => exists a, G a /\ AST segtop A (K a) (KM a) c).
Proof using All.
  intros A Pm PM G K KM len Len Regs Mods Top T [ms mo] Start Cont.
  pose proof Start as (Acct0 & Pre & PreM & _). cbn [cfg_ms cfg_model] in Pre, PreM.
  pose proof Acct0 as (Awf & Inv0 & Live0 & Above0 & Seg47).
  destruct (Regs _ Pre) as (Pend & R11 & R12 & R13 & R15 & Kgrant).
  rewrite restrict_svc in Pend. rewrite restrict_areg in R11, R12, R13, R15.
  destruct (Mods _ PreM) as ((Wm & _) & Lazy0 & Gap & Budget & Kmod).
  pose proof (Top _ PreM) as Top47.
  pose proof (alloc_top_room (m_vmmaps mo)) as Room. unfold two_pow_64, stack_max_size in Room.
  pose proof (page_round_up_Z_ge_all len) as RoundGe.
  assert (SizeU : bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len).
  { apply unsigned_lit. destruct (proj1 (vm_gap_available_iff _ _) Gap) as (b & _ & _ & Btop & _).
    pose proof (u64_range b). lia. }
  assert (BackOk : mmap_noreserve_backed_ok (Z_to_bv 64 34) mo (page_round_up_Z len) = true).
  { unfold mmap_noreserve_backed_ok. rewrite noreserve34. apply Z.leb_le.
    pose proof (vm_backing_used_le' A mo Awf Inv0). pose proof (A_bytes_nonneg A Awf). lia. }
  assert (NotRef : mmap_grant_refusable (Z_to_bv 64 34) mo (page_round_up_Z len) = false)
    by (apply mmap_grant_refusable_false_iff; split; assumption).
  pose proof (fun o => mmap34_char segs ms mo len o Len R11 R12 R13 R15 Live0 NotRef) as Char.
  destruct (proj1 (vm_gap_available_iff _ _) Gap) as (a0 & Al0 & Pos0 & Top0 & Free0).
  pose (Gr := {a : word | grant_ok34 mo (page_round_up_Z len) a}).
  assert (Seed : Gr) by exact (exist _ a0 (conj Al0 (conj Pos0 (conj Top0 (conj Free0 BackOk))))).
  apply (ast_node_mm segs segtop A A Pm PM Gr Seed (fun g => K (proj1_sig g)) (fun g => KM (proj1_sig g))
           ms mo (Z_to_bv 64 222) (fun g => proj1_sig g) (fun g => [(proj1_sig g, Z_to_bv 64 (page_round_up_Z len))])
           (fun _ => []) (fun g => mdl_mmap_rw mo (proj1_sig g) (Z_to_bv 64 (page_round_up_Z len))) T Start Pend).
  - intros [a Ga]. apply Char. exists a. split; [exact Ga|reflexivity].
  - intros o Spec. apply Char in Spec. destruct Spec as (a & Ga & Eo). exists (exist _ a Ga). exact Eo.
  - intros [a Ga]. cbn [proj1_sig]. destruct Ga as (_ & _ & Atop & _). split; [exact Awf|]. split.
    + apply (MInv_transport A mo); [exact Inv0| apply mdl_mmap_rw_mat| apply mdl_mmap_rw_lazy|].
      pose proof (u64_range a) as Ra.
      pose proof (eager_used_mmap_rw_le mo a (Z_to_bv 64 (page_round_up_Z len)) Wm ltac:(lia)) as Grow.
      rewrite mdl_mmap_rw_vmmaps. cbn [vm_limit]. lia.
    + rewrite mdl_mmap_rw_halted, mdl_mmap_rw_lazy. exact (conj Live0 (conj Above0 Seg47)).
  - intros [a Ga] x Zon. cbn [proj1_sig] in Zon |- *. destruct Ga as (Aal & _ & Atop & Afree & _).
    rewrite zeros_cover_one in Zon. apply andb_prop in Zon as [Lo Hi].
    apply Z.leb_le in Lo. apply Z.ltb_lt in Hi. rewrite SizeU in Hi.
    unfold HID, mkH. rewrite mdl_mmap_rw_lazy.
    rewrite (lazy_off_free mo a (Z_to_bv 64 (page_round_up_Z len)) x Lazy0 Afree Aal) by (rewrite SizeU; lia).
    cbn [andb orb]. apply Z.leb_gt. lia.
  - intros g x Uon. rewrite zeros_cover_nil in Uon. discriminate Uon.
  - intros g x _ _. cbn beta. rewrite mdl_mmap_rw_lazy. reflexivity.
  - intros g x _. cbn beta. rewrite mdl_mmap_rw_vmmaps. reflexivity.
  - intros [a Ga]. exact (Kgrant a (proj1 (Kmod a Ga))).
  - intros [a Ga]. exact (proj2 (Kmod a Ga)).
  - intros [a Ga] c' Post. apply Cont. exists a. exact (conj (proj1 (Kmod a Ga)) Post).
Qed.

End Rule1.

Lemma mmap_fixed_char : forall segs ms mo flags addr len o,
  (flags = flags50 \/ flags = flags16434) ->
  0 < len < 2^64 -> 0 < addr -> addr mod page_size = 0 ->
  addr + page_round_up_Z len <= alloc_top (m_vmmaps mo) ->
  areg ms 10 = Z_to_bv 64 addr -> areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 3 -> areg ms 13 = flags -> areg ms 15 = Z_to_bv 64 0 ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  mmap_fixed_rw_budget_ok flags mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  m_halted mo = None ->
  syscall_spec_acfg (sys_input segs ms (Z_to_bv 64 222)) mo o <->
  o = Ok (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))])
         (mdl_fixed flags mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) [].
Proof.
  intros segs ms mo flags addr len o Fl Len Apos Aal Atop R10 R11 R12 R13 R15 Free Inside Budget Live0.
  assert (Num : bv_unsigned (in_sysno (sys_input segs ms (Z_to_bv 64 222))) = 222).
  { rewrite in_sysno_sys_input. apply unsigned_lit. lia. }
  pose proof (alloc_top_room (m_vmmaps mo)) as Room. unfold two_pow_64, stack_max_size in Room.
  pose proof (page_round_up_Z_ge_all len) as RoundGe.
  assert (AddrU : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply unsigned_lit; lia).
  assert (LenU : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (Nz : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (Gates : mmap_off_aligned_b (Z_to_bv 64 0) = true /\ mmap_anon_b flags = true
     /\ mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false /\ mmap_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
     /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true).
  { destruct Fl as [-> | ->]; vm_compute; repeat constructor. }
  destruct Gates as (Goff & Ganon & Gmod & Gna & Gfna & Gfrw).
  assert (GetM : forall (k : Model -> Sys SyscallEffect) inp o', Monad.bind get_model k inp mo o' <-> k mo inp mo o').
  { intros k inp [y m2 evs|]; cbn [Monad.bind get_model]; split.
    - intros (x & m1 & evs1 & evs2 & Got & Body & Evs). injection Got as -> -> ->. subst evs. exact Body.
    - intros Body. exists mo, mo, [], evs. split; [reflexivity|]. split; [exact Body|reflexivity].
    - intros [Bad|(x & m1 & evs1 & Got & Body)]; [discriminate Bad|]. injection Got as -> -> ->. exact Body.
    - intros Body. right. exists mo, mo, []. split; [reflexivity|exact Body]. }
  assert (Spec : forall o', syscall_spec (sys_input segs ms (Z_to_bv 64 222)) mo o' <->
      o' = Ok (mkEffect (errno_ret ENOMEM) [] []) mo []
      \/ o' = Ok (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))])
                 (mdl_fixed flags mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) []
      \/ o' = Ok (mkEffectU (errno_ret ENOMEM) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] [])
                 (with_mmap_destroyed (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))
                    (mmap_fixed_destroyed_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) mo) []).
  { intros o'. rewrite (syscall_spec_222 _ mo o' Num).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a5_si, R10, R11, R12, R13, R15.
    unfold mmap_spec. rewrite Goff, Ganon, Nz, Gmod, Gna, Gfna, Gfrw. cbn [negb].
    rewrite AddrU, LenU.
    replace (two_pow_64 <=? addr + page_round_up_Z len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
    rewrite GetM.
    replace (addr + page_round_up_Z len <=? alloc_top (m_vmmaps mo)) with true by (symmetry; apply Z.leb_le; lia).
    replace (addr mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; exact Aal).
    replace (0 <? addr) with true by (symmetry; apply Z.ltb_lt; exact Apos).
    rewrite Free, Inside. cbn [negb andb]. sys_unfold. unfold mmap_errnos.
    destruct o' as [y m2 evs|]; split.
    - intros [Plain|[Commit|Gone]].
      + destruct Plain as (e & m1 & evs1 & evs2 & (e0 & Ein & Ee) & Ey & Eevs).
        injection Ee as -> -> ->. injection Ey as -> -> ->. subst evs.
        destruct Ein as [<-|[]]. left. reflexivity.
      + destruct Commit as (u & m1 & evs1 & evs2 & (u0 & _ & Eu) & (u1 & m3 & evs3 & evs4 & Em & Ey & E2) & Eevs).
        injection Eu as -> -> ->. injection Em as -> -> ->. injection Ey as -> -> ->. subst evs evs2.
        right; left. reflexivity.
      + destruct Gone as (e & m1 & evs1 & evs2 & (e0 & Ein & Ee) & (u1 & m3 & evs3 & evs4 & Em & Ey & E2) & Eevs).
        injection Ee as -> -> ->. injection Em as -> -> ->. injection Ey as -> -> ->. subst evs evs2.
        destruct Ein as [<-|[]]. right; right. reflexivity.
    - intros [Plain|[Commit|Gone]]; injection Plain as Ey Em Eevs || injection Commit as Ey Em Eevs || injection Gone as Ey Em Eevs;
        subst y m2 evs.
      + left. exists ENOMEM, mo, [], []. split; [exists ENOMEM; split; [left; reflexivity|reflexivity]|]. split; reflexivity.
      + right; left. exists tt, mo, [], []. split; [exists tt; split; [exact Budget|reflexivity]|]. split; [|reflexivity].
        eexists tt, _, [], []. split; [reflexivity|]. split; reflexivity.
      + right; right. exists ENOMEM, mo, [], []. split; [exists ENOMEM; split; [left; reflexivity|reflexivity]|]. split; [|reflexivity].
        eexists tt, _, [], []. split; [reflexivity|]. split; reflexivity.
    - intros [[(e & _ & Bad)|(e & m1 & evs1 & _ & Bad)]|[[(u & _ & Bad)|(u & m1 & evs1 & _ & [Bad|(u0 & m0 & evs0 & _ & Bad)])]
             |[(e & _ & Bad)|(e & m1 & evs1 & _ & [Bad|(u0 & m0 & evs0 & _ & Bad)])]]]; discriminate Bad.
    - intros [Bad|[Bad|Bad]]; discriminate Bad. }
  assert (CommitSpec : syscall_spec (sys_input segs ms (Z_to_bv 64 222)) mo
      (Ok (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))])
          (mdl_fixed flags mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) []))
    by (apply Spec; right; left; reflexivity).
  assert (Keep : refusal_b (sys_input segs ms (Z_to_bv 64 222)) mo (Z_to_bv 64 addr) = false).
  { rewrite (refusal_b_222 _ mo _ Num). apply ret_in_errnos_ENOMEM_aligned. rewrite AddrU. exact Aal. }
  assert (Refuse : refusal_b (sys_input segs ms (Z_to_bv 64 222)) mo (errno_ret ENOMEM) = true).
  { rewrite (refusal_b_222 _ mo _ Num). apply ret_in_errnos_errno. left. reflexivity. }
  pose proof (acfg_family_off_222 _ Num) as Fam.
  split.
  - intros [Sp Guard]. apply Spec in Sp. destruct Sp as [Plain|[Commit|Gone]]; [exfalso; subst o|exact Commit|exfalso; subst o].
    + exact (Guard Live0 (refusal_spurious_of_grant ACFG _ mo (mkEffect (errno_ret ENOMEM) [] []) _ _ _ Fam Refuse CommitSpec Keep)).
    + exact (Guard Live0 (refusal_spurious_of_grant ACFG _ mo
        (mkEffectU (errno_ret ENOMEM) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] []) _ _ _ Fam Refuse CommitSpec Keep)).
  - intros Commit. subst o. exact (syscall_spec_acfg_nonrefusal _ _ _ _ _ CommitSpec Keep).
Qed.

Section Rules234.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

Lemma req_facts : forall mo addr len, 0 < len < 2^64 -> 0 < addr -> addr mod page_size = 0 ->
  addr + page_round_up_Z len <= alloc_top (m_vmmaps mo) ->
  bv_unsigned (Z_to_bv 64 addr) = addr /\ bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len
  /\ 0 < page_round_up_Z len /\ page_round_up_Z len mod 4096 = 0 /\ addr + page_round_up_Z len < 2^64.
Proof.
  intros mo addr len Hlen Hpos Hal Htop.
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  pose proof (page_round_up_Z_ge_all len). pose proof (page_round_up_Z_aligned' len) as Hnl. unfold page_size in Hnl.
  repeat split; try (apply unsigned_lit); lia.
Qed.

Theorem ast_mmap_fixed_commit : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 < addr -> addr mod page_size = 0 ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 50 /\ areg ms 15 = Z_to_bv 64 0
       /\ K (nretA ms (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo -> model_ivs_wf mo
       /\ addr + page_round_up_Z len <= alloc_top (m_vmmaps mo)
       /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ eager_used mo + overlap_sum (vm_maps (m_vmmaps mo)) addr (addr + page_round_up_Z len) + A_bytes A <= vm_limit (m_vmmaps mo)
       /\ KM (mdl_fixed flags50 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))) ->
  (forall mo, PM mo -> alloc_top (m_vmmaps mo) <= 2^47) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using All.
  intros A Pm PM K KM addr len Len Apos Aal Regs Mods Top T [ms mo] Start Cont.
  pose proof Start as (Acct0 & Pre & PreM & _). cbn [cfg_ms cfg_model] in Pre, PreM.
  pose proof Acct0 as (Awf & Inv0 & Live0 & Above0 & Seg47).
  destruct (Regs _ Pre) as (Pend & R10 & R11 & R12 & R13 & R15 & Kfix).
  rewrite restrict_svc in Pend. rewrite restrict_areg in R10, R11, R12, R13, R15.
  destruct (Mods _ PreM) as (Wf0 & Atop & Free & Inside & Budget & KMfix).
  pose proof (Top _ PreM) as Top47.
  pose proof Wf0 as (_ & _ & Wl & _).
  destruct (req_facts mo addr len Len Apos Aal Atop) as (AddrU & SizeU & SizePos & SizeAl & Below).
  assert (AlignLo : addr mod 4096 = 0) by exact Aal.
  assert (AlignHi : (addr + page_round_up_Z len) mod 4096 = 0).
  { rewrite Zplus_mod, AlignLo, SizeAl. reflexivity. }
  assert (Cut : m_vm_lazy (mdl_fixed flags50 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))
                = maps_subtract (m_vm_lazy mo) addr (addr + page_round_up_Z len)).
  { rewrite mdl_fixed_lazy50, AddrU, SizeU. reflexivity. }
  assert (BudOk : mmap_fixed_rw_budget_ok flags50 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true).
  { apply mmap_fixed_rw_budget_ok_commit_intro; [exact noreserve50| exact Wf0|].
    rewrite AddrU, SizeU. pose proof (vm_backing_used_le' A mo Awf Inv0). pose proof (A_bytes_nonneg A Awf). lia. }
  pose proof (fun o => mmap_fixed_char segs ms mo flags50 addr len o (or_introl eq_refl) Len Apos Aal Atop
                         R10 R11 R12 R13 R15 Free Inside BudOk Live0) as Char.
  apply (ast_node_mm segs segtop A A Pm PM unit tt (fun _ => K) (fun _ => KM) ms mo (Z_to_bv 64 222)
           (fun _ => Z_to_bv 64 addr) (fun _ => [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]) (fun _ => [])
           (fun _ => mdl_fixed flags50 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) T Start Pend).
  - intros _. apply Char. reflexivity.
  - intros o Spec. exists tt. apply Char. exact Spec.
  - intros _. split; [exact Awf|]. split.
    + apply (MInv_cut A A mo _ addr (addr + page_round_up_Z len) Inv0); [tauto| exact AlignLo| exact AlignHi| | |].
      * rewrite mdl_fixed_mat, AddrU, SizeU. reflexivity.
      * intros p Away Lz. rewrite Cut. apply page_in_ranges_subtract_keep; [exact Wl| lia| exact Away| exact Lz].
      * pose proof (eager_used_fixed50_le mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) Wf0) as Grow.
        rewrite AddrU, SizeU in Grow. rewrite mdl_fixed_vmmaps. cbn [mmap_fixed_rw_next vm_limit]. lia.
    + rewrite mdl_fixed_halted, Cut. split; [exact Live0|]. split; [|exact Seg47].
      apply ranges_from_b_subtract; [exact Wl| exact Above0].
  - intros _ x Zon. rewrite zeros_cover_one, AddrU, SizeU in Zon.
    apply andb_prop in Zon as [Lo Hi]. apply Z.leb_le in Lo. apply Z.ltb_lt in Hi.
    apply (HID_cut_in A mo _ addr (addr + page_round_up_Z len) x Wl AlignLo AlignHi ltac:(lia) Cut). lia.
  - intros _ x Uon. rewrite zeros_cover_nil in Uon. discriminate Uon.
  - intros _ x Zoff _. rewrite zeros_cover_one, AddrU, SizeU in Zoff.
    apply (HID_cut_out A mo _ addr (addr + page_round_up_Z len) x Wl AlignLo AlignHi ltac:(lia) Cut).
    destruct (Z.leb_spec addr (bv_unsigned x)) as [Lo|Lo]; [right|left; exact Lo].
    destruct (Z.ltb_spec (bv_unsigned x) (addr + page_round_up_Z len)) as [Hi|Hi]; [discriminate Zoff| exact Hi].
  - intros _ x Hidden. rewrite mdl_fixed_vmmaps. cbn [mmap_fixed_rw_next vm_noaccess]. rewrite AddrU, SizeU.
    pose proof Wf0 as (_ & Wn & _).
    apply noaccess_cut_out; [exact Wn| exact AlignLo| exact AlignHi| lia|].
    destruct (Z.ltb_spec (bv_unsigned x) addr) as [Lo|Lo]; [left; exact Lo|].
    destruct (Z.leb_spec (addr + page_round_up_Z len) (bv_unsigned x)) as [Hi|Hi]; [right; exact Hi|].
    rewrite (HID_cut_in A mo _ addr (addr + page_round_up_Z len) x Wl AlignLo AlignHi ltac:(lia) Cut ltac:(lia)) in Hidden.
    discriminate Hidden.
  - intros _. exact Kfix.
  - intros _. exact KMfix.
  - intros _ c' Post. exact (Cont c' Post).
Qed.

Lemma page_allowedb_cons_in : forall lo hi A (p : word), lo <= bv_unsigned p -> bv_unsigned p + 4096 <= hi ->
  page_allowedb ((lo, hi) :: A) p = true.
Proof.
  intros lo hi A p H1 H2. unfold page_allowedb. cbn [existsb fst snd]. unfold page_size.
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.

Lemma page_allowedb_cons_out : forall lo hi A (p : word), (bv_unsigned p + 4096 <= lo \/ hi <= bv_unsigned p) -> lo < hi ->
  page_allowedb ((lo, hi) :: A) p = page_allowedb A p.
Proof.
  intros lo hi A p H Hlh. unfold page_allowedb. cbn [existsb fst snd]. unfold page_size.
  destruct (Z.leb_spec lo (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) hi); cbn; try reflexivity. lia.
Qed.

Theorem ast_mmap_fixed_remap : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 < addr -> addr mod page_size = 0 -> segtop <= addr ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 16434 /\ areg ms 15 = Z_to_bv 64 0
       /\ K (nretA ms (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo -> model_ivs_wf mo
       /\ addr + page_round_up_Z len <= alloc_top (m_vmmaps mo)
       /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ eager_used mo + page_round_up_Z len + A_bytes A <= vm_limit (m_vmmaps mo)
       /\ KM (mdl_fixed flags16434 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))) ->
  (forall mo, PM mo -> alloc_top (m_vmmaps mo) <= 2^47) ->
  cps segs (AST segtop A Pm PM) (AST segtop ((addr, addr + page_round_up_Z len) :: A) K KM).
Proof using All.
  intros A Pm PM K KM addr len Len Apos Aal Low Regs Mods Top T [ms mo] Start Cont.
  pose proof Start as (Acct0 & Pre & PreM & _). cbn [cfg_ms cfg_model] in Pre, PreM.
  pose proof Acct0 as (Awf & Inv0 & Live0 & Above0 & Seg47).
  destruct (Regs _ Pre) as (Pend & R10 & R11 & R12 & R13 & R15 & Kfix).
  rewrite restrict_svc in Pend. rewrite restrict_areg in R10, R11, R12, R13, R15.
  destruct (Mods _ PreM) as (Wf0 & Atop & Free & Inside & Budget & KMfix).
  pose proof (Top _ PreM) as Top47.
  pose proof Wf0 as (_ & Wn & Wl & _).
  destruct (req_facts mo addr len Len Apos Aal Atop) as (AddrU & SizeU & SizePos & SizeAl & Below).
  assert (AlignLo : addr mod 4096 = 0) by exact Aal.
  assert (AlignHi : (addr + page_round_up_Z len) mod 4096 = 0).
  { rewrite Zplus_mod, AlignLo, SizeAl. reflexivity. }
  assert (Interior : lazy_interior (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))
                     = [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]).
  { apply lazy_interior_aligned; rewrite ?AddrU, ?SizeU; [exact Aal| exact SizeAl| exact SizePos| lia]. }
  assert (Lz : m_vm_lazy (mdl_fixed flags16434 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))
               = (Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len)) :: maps_subtract (m_vm_lazy mo) addr (addr + page_round_up_Z len)).
  { rewrite mdl_fixed_lazy16434, Interior, AddrU, SizeU. reflexivity. }
  assert (Widen : forall p, page_allowedb A p = true -> page_allowedb ((addr, addr + page_round_up_Z len) :: A) p = true).
  { intros p Allow. unfold page_allowedb in *. cbn [existsb]. rewrite Allow. apply orb_true_r. }
  assert (Inner : forall x : word, addr <= bv_unsigned x < addr + page_round_up_Z len ->
            HID ((addr, addr + page_round_up_Z len) :: A) (mdl_fixed flags16434 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) x = false).
  { intros x Within. destruct (page_of_byte_in_aligned' x addr (addr + page_round_up_Z len) AlignLo AlignHi Within) as [P1 P2].
    unfold HID, mkH. rewrite (page_allowedb_cons_in addr (addr + page_round_up_Z len) A (page_base x) P1 P2).
    cbn [negb]. rewrite andb_false_r. cbn [orb]. apply Z.leb_gt. lia. }
  assert (BudOk : mmap_fixed_rw_budget_ok flags16434 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true).
  { apply mmap_fixed_rw_budget_ok_recommit_intro; [exact noreserve16434| exact Wf0| | | | |]; rewrite ?AddrU, ?SizeU;
      [exact Aal| exact SizeAl| exact SizePos| lia|].
    pose proof (vm_backing_used_le' A mo Awf Inv0). pose proof (A_bytes_nonneg A Awf). lia. }
  pose proof (fun o => mmap_fixed_char segs ms mo flags16434 addr len o (or_intror eq_refl) Len Apos Aal Atop
                         R10 R11 R12 R13 R15 Free Inside BudOk Live0) as Char.
  apply (ast_node_mm segs segtop A ((addr, addr + page_round_up_Z len) :: A) Pm PM unit tt (fun _ => K) (fun _ => KM)
           ms mo (Z_to_bv 64 222) (fun _ => Z_to_bv 64 addr) (fun _ => [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))])
           (fun _ => []) (fun _ => mdl_fixed flags16434 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) T Start Pend).
  - intros _. apply Char. reflexivity.
  - intros o Spec. exists tt. apply Char. exact Spec.
  - intros _. split.
    { apply Forall_cons; [|exact Awf]. cbn [fst snd]. split; [lia|]. split; [exact Aal| exact AlignHi]. }
    split.
    + apply (MInv_cut A _ mo _ addr (addr + page_round_up_Z len) Inv0 Widen AlignLo AlignHi).
      * rewrite mdl_fixed_mat, AddrU, SizeU. reflexivity.
      * intros p Away Inl. rewrite Lz, page_in_ranges_cons'. apply orb_true_iff. right.
        apply page_in_ranges_subtract_keep; [exact Wl| lia| exact Away| exact Inl].
      * pose proof (eager_used_fixed16434_le mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) Wf0) as Shrink.
        rewrite AddrU, SizeU in Shrink. specialize (Shrink Aal SizeAl SizePos ltac:(lia)).
        rewrite mdl_fixed_vmmaps. cbn [mmap_fixed_rw_next vm_limit A_bytes fst snd]. lia.
    + rewrite mdl_fixed_halted, Lz. split; [exact Live0|]. split; [|exact Seg47].
      apply ranges_from_b_cons; [rewrite AddrU; exact Low|]. apply ranges_from_b_subtract; [exact Wl| exact Above0].
  - intros _ x Zon. rewrite zeros_cover_one, AddrU, SizeU in Zon.
    apply andb_prop in Zon as [Lo Hi]. apply Z.leb_le in Lo. apply Z.ltb_lt in Hi. apply Inner. lia.
  - intros _ x Uon. rewrite zeros_cover_nil in Uon. discriminate Uon.
  - intros _ x Zoff _. rewrite zeros_cover_one, AddrU, SizeU in Zoff.
    assert (Off : bv_unsigned x < addr \/ addr + page_round_up_Z len <= bv_unsigned x).
    { destruct (Z.leb_spec addr (bv_unsigned x)) as [Lo|Lo]; [right|left; exact Lo].
      destruct (Z.ltb_spec (bv_unsigned x) (addr + page_round_up_Z len)) as [Hi|Hi]; [discriminate Zoff| exact Hi]. }
    pose proof (page_of_byte_out_aligned' x addr (addr + page_round_up_Z len) AlignLo AlignHi Off) as Away.
    unfold mkH. rewrite Lz, page_in_ranges_cons_out' by (rewrite AddrU, SizeU; exact Away).
    rewrite (page_in_ranges_subtract_out' (page_base x) _ addr (addr + page_round_up_Z len) Wl ltac:(lia) Away).
    rewrite (page_allowedb_cons_out addr (addr + page_round_up_Z len) A (page_base x) Away ltac:(lia)). reflexivity.
  - intros _ x Hidden. rewrite mdl_fixed_vmmaps. cbn [mmap_fixed_rw_next vm_noaccess]. rewrite AddrU, SizeU.
    apply noaccess_cut_out; [exact Wn| exact AlignLo| exact AlignHi| lia|].
    destruct (Z.ltb_spec (bv_unsigned x) addr) as [Lo|Lo]; [left; exact Lo|].
    destruct (Z.leb_spec (addr + page_round_up_Z len) (bv_unsigned x)) as [Hi|Hi]; [right; exact Hi|].
    rewrite (Inner x ltac:(lia)) in Hidden. discriminate Hidden.
  - intros _. exact Kfix.
  - intros _. exact KMfix.
  - intros _ c' Post. exact (Cont c' Post).
Qed.

Theorem ast_munmap : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 <= addr -> addr mod page_size = 0 -> addr + page_round_up_Z len <= TASK_SIZE ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 215) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ K (nretA ms (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] []))) ->
  (forall mo, PM mo -> model_ivs_wf mo
       /\ map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ eager_used mo + overlap_sum (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr)) addr (addr + page_round_up_Z len)
            + A_bytes A <= vm_limit (m_vmmaps mo)
       /\ KM (mdl_munmap mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using All.
  intros A Pm PM K KM addr len Len Anneg Aal Task Regs Mods T [ms mo] Start Cont.
  pose proof Start as (Acct0 & Pre & PreM & _). cbn [cfg_ms cfg_model] in Pre, PreM.
  pose proof Acct0 as (Awf & Inv0 & Live0 & Above0 & Seg47).
  destruct (Regs _ Pre) as (Pend & R10 & R11 & Kun).
  rewrite restrict_svc in Pend. rewrite restrict_areg in R10, R11.
  destruct (Mods _ PreM) as (Wf0 & Has & Budget & KMun).
  pose proof Wf0 as (_ & Wn & Wl & _).
  unfold TASK_SIZE in Task.
  pose proof (page_round_up_Z_ge_all len) as RoundGe.
  pose proof (page_round_up_Z_aligned' len) as SizeAl. unfold page_size in SizeAl.
  assert (AddrU : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply unsigned_lit; lia).
  assert (LenU : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (SizeU : bv_unsigned (Z_to_bv 64 (page_round_up_Z len)) = page_round_up_Z len) by (apply unsigned_lit; lia).
  assert (AlignLo : addr mod 4096 = 0) by exact Aal.
  assert (AlignHi : (addr + page_round_up_Z len) mod 4096 = 0).
  { rewrite Zplus_mod, AlignLo, SizeAl. reflexivity. }
  assert (Cut : m_vm_lazy (mdl_munmap mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))
                = maps_subtract (m_vm_lazy mo) addr (addr + page_round_up_Z len)).
  { rewrite mdl_munmap_lazy, AddrU, SizeU. reflexivity. }
  assert (Exact : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 215)) mo o <->
     o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] [])
            (mdl_munmap mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) []).
  { intros o. rewrite syscall_spec_215 by (rewrite in_sysno_sys_input; apply unsigned_lit; lia).
    rewrite in_a0_si, in_a1_si, R10, R11.
    pose proof (munmap_exact_outcome (Z_to_bv 64 addr) (Z_to_bv 64 len) (sys_input segs ms (Z_to_bv 64 215)) mo o) as Ex.
    cbv zeta in Ex. rewrite LenU in Ex. apply Ex.
    - rewrite AddrU. exact Aal.
    - rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
    - rewrite AddrU. unfold TASK_SIZE. lia.
    - exact Has. }
  assert (Char : forall o, syscall_spec_acfg (sys_input segs ms (Z_to_bv 64 215)) mo o <->
     o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] [])
            (mdl_munmap mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) []).
  { intros o. rewrite (syscall_spec_acfg_no segs ms (Z_to_bv 64 215) 215 mo o); [apply Exact| |vm_compute; reflexivity].
    apply unsigned_lit. lia. }
  apply (ast_node_mm segs segtop A A Pm PM unit tt (fun _ => K) (fun _ => KM) ms mo (Z_to_bv 64 215)
           (fun _ => Z_to_bv 64 0) (fun _ => []) (fun _ => [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))])
           (fun _ => mdl_munmap mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) T Start Pend).
  - intros _. apply Char. reflexivity.
  - intros o Spec. exists tt. apply Char. exact Spec.
  - intros _. split; [exact Awf|]. split.
    + apply (MInv_cut A A mo _ addr (addr + page_round_up_Z len) Inv0); [tauto| exact AlignLo| exact AlignHi| | |].
      * rewrite mdl_munmap_mat, AddrU, SizeU. reflexivity.
      * intros p Away Inl. rewrite Cut. apply page_in_ranges_subtract_keep; [exact Wl| lia| exact Away| exact Inl].
      * pose proof (eager_used_munmap_le mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) Wf0) as Grow.
        rewrite AddrU, SizeU in Grow. rewrite mdl_munmap_vmmaps. cbn [vm_limit]. lia.
    + rewrite mdl_munmap_halted, Cut. split; [exact Live0|]. split; [|exact Seg47].
      apply ranges_from_b_subtract; [exact Wl| exact Above0].
  - intros _ x Zon. rewrite zeros_cover_nil in Zon. discriminate Zon.
  - intros _ x Uon. rewrite zeros_cover_one, AddrU, SizeU in Uon.
    apply andb_prop in Uon as [Lo Hi]. apply Z.leb_le in Lo. apply Z.ltb_lt in Hi.
    apply (HID_cut_in A mo _ addr (addr + page_round_up_Z len) x Wl AlignLo AlignHi ltac:(lia) Cut). lia.
  - intros _ x _ Uoff. rewrite zeros_cover_one, AddrU, SizeU in Uoff.
    apply (HID_cut_out A mo _ addr (addr + page_round_up_Z len) x Wl AlignLo AlignHi ltac:(lia) Cut).
    destruct (Z.ltb_spec (bv_unsigned x) addr) as [Lo|Lo]; [left; exact Lo|right].
    destruct (Z.ltb_spec (bv_unsigned x) (addr + page_round_up_Z len)) as [Hi|Hi]; [|exact Hi].
    apply Z.leb_le in Lo. rewrite Lo in Uoff. discriminate Uoff.
  - intros _ x Hidden. rewrite mdl_munmap_vmmaps. cbn [vm_noaccess]. rewrite AddrU, SizeU.
    apply noaccess_cut_out; [exact Wn| exact AlignLo| exact AlignHi| lia|].
    destruct (Z.ltb_spec (bv_unsigned x) addr) as [Lo|Lo]; [left; exact Lo|].
    destruct (Z.leb_spec (addr + page_round_up_Z len) (bv_unsigned x)) as [Hi|Hi]; [right; exact Hi|].
    rewrite (HID_cut_in A mo _ addr (addr + page_round_up_Z len) x Wl AlignLo AlignHi ltac:(lia) Cut ltac:(lia)) in Hidden.
    discriminate Hidden.
  - intros _. exact Kun.
  - intros _. exact KMun.
  - intros _ c' Post. exact (Cont c' Post).
Qed.

End Rules234.

Lemma model_ivs_wf_mmap_rw : forall mo a n, model_ivs_wf mo -> bv_unsigned a + bv_unsigned n <= 2^64 ->
  model_ivs_wf (mdl_mmap_rw mo a n).
Proof.
  intros mo a n Hwf Han. pose proof Hwf as (Wm & Wn & _). unfold mdl_mmap_rw.
  apply model_ivs_wf_with_vmmaps; [exact Hwf| | exact Wn| reflexivity]. cbn [vm_maps]. apply ivs_wf_cons; [exact Han| exact Wm].
Qed.

Lemma model_ivs_wf_fixed : forall flags mo a n, model_ivs_wf mo -> bv_unsigned a + bv_unsigned n <= 2^64 ->
  model_ivs_wf (mdl_fixed flags mo a n).
Proof.
  intros flags mo a n Hwf Han. pose proof Hwf as (Wm & Wn & _). unfold mdl_fixed.
  apply model_ivs_wf_with_mmap_replacement; [exact Han|].
  apply model_ivs_wf_with_vmmaps; [exact Hwf| exact Wm| | reflexivity]. unfold mmap_fixed_rw_next. cbn [vm_noaccess].
  apply maps_subtract_wf; [exact Wn| pose proof (u64_range n); lia].
Qed.

Lemma model_ivs_wf_munmap : forall mo a n, model_ivs_wf mo -> model_ivs_wf (mdl_munmap mo a n).
Proof.
  intros mo a n Hwf. pose proof Hwf as (Wm & Wn & _). unfold mdl_munmap, with_mmap_destroyed.
  apply model_ivs_wf_vm_forget_range; [pose proof (u64_range n); lia|].
  apply model_ivs_wf_with_vmmaps; [exact Hwf| apply ivs_wf_filter; exact Wm| | reflexivity]. cbn [vm_noaccess].
  apply maps_subtract_wf; [exact Wn| pose proof (u64_range n); lia].
Qed.

Lemma iv_subtract_pieces' : forall (a sz : word) lo hi q,
  iv_wf (a, sz) -> In q (iv_subtract a sz lo hi) ->
  bv_unsigned a <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz
  /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite unsigned_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_pieces' : forall l lo hi q, ivs_wf l -> In q (maps_subtract l lo hi) ->
  exists r, In r l /\ bv_unsigned (fst r) <= bv_unsigned (fst q)
            /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst r) + bv_unsigned (snd r)
            /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_pieces' a sz lo hi q Ha Hin).
  - destruct (IH lo hi q Hl Hin) as (r & Hr & H). exists r. split; [right; exact Hr| exact H].
Qed.

Lemma lazy_in_maps_mmap_rw : forall mo a n, lazy_in_maps mo -> lazy_in_maps (mdl_mmap_rw mo a n).
Proof.
  intros mo a n H iv Hin Hpos. rewrite mdl_mmap_rw_lazy in Hin. destruct (H iv Hin Hpos) as (e & He & E1 & E2).
  exists e. rewrite mdl_mmap_rw_vmmaps. cbn [vm_maps]. split; [right; exact He| split; assumption].
Qed.

Lemma lazy_in_maps_fixed50 : forall mo a n, model_ivs_wf mo -> lazy_in_maps mo -> lazy_in_maps (mdl_fixed flags50 mo a n).
Proof.
  intros mo a n (_ & _ & Wl & _) H iv Hin Hpos. rewrite mdl_fixed_lazy50 in Hin.
  destruct (maps_subtract_pieces' _ _ _ iv Wl Hin) as (r & Hr & P1 & P2 & _).
  destruct (H r Hr ltac:(lia)) as (e & He & E1 & E2). exists e. rewrite mdl_fixed_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_maps].
  split; [exact He| lia].
Qed.

Lemma map_contains_true : forall l (lo n : word), map_contains l lo n = true ->
  exists e, In e l /\ bv_unsigned (fst e) <= bv_unsigned lo /\ bv_unsigned lo + bv_unsigned n <= bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
  intros l lo n H. unfold map_contains in H. apply existsb_exists in H as (e & He & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists e. auto.
Qed.

Lemma lazy_in_maps_fixed16434 : forall mo a n, model_ivs_wf mo -> lazy_in_maps mo ->
  map_contains (vm_maps (m_vmmaps mo)) a n = true ->
  lazy_in_maps (mdl_fixed flags16434 mo a n).
Proof.
  intros mo a n (Wm & _ & Wl & _) H Hmc iv Hin Hpos. rewrite mdl_fixed_lazy16434 in Hin. rewrite mdl_fixed_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_maps].
  apply in_app_iff in Hin as [Hin|Hin].
  - unfold lazy_interior in Hin. cbv zeta in Hin.
    destruct (Z.ltb_spec ((bv_unsigned a + page_size - 1) / page_size * page_size) ((bv_unsigned a + bv_unsigned n) / page_size * page_size)) as [El|El];
      [|destruct Hin].
    destruct Hin as [<-|[]]. destruct (map_contains_true _ _ _ Hmc) as (e & He & E1 & E2). exists e. split; [exact He|].
    pose proof (Wm e He) as We. unfold iv_wf, B, S in We.
    cbn [fst snd]. pose proof (u64_range a). pose proof (u64_range n). unfold page_size in *.
    assert (L1 : bv_unsigned a <= (bv_unsigned a + 4096 - 1) / 4096 * 4096).
    { pose proof (Z.div_mod (bv_unsigned a + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a + 4096 - 1) 4096 ltac:(lia)). lia. }
    assert (L2 : (bv_unsigned a + bv_unsigned n) / 4096 * 4096 <= bv_unsigned a + bv_unsigned n).
    { pose proof (Z.div_mod (bv_unsigned a + bv_unsigned n) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a + bv_unsigned n) 4096 ltac:(lia)). lia. }
    assert (L0 : 0 <= (bv_unsigned a + 4096 - 1) / 4096 * 4096) by lia.
    assert (L3 : (bv_unsigned a + bv_unsigned n) / 4096 * 4096 - (bv_unsigned a + 4096 - 1) / 4096 * 4096 < 2^64) by lia.
    rewrite !unsigned_lit by lia. lia.
  - destruct (maps_subtract_pieces' _ _ _ iv Wl Hin) as (r & Hr & P1 & P2 & _).
    destruct (H r Hr ltac:(lia)) as (e & He & E1 & E2). exists e. split; [exact He| lia].
Qed.

Lemma lazy_in_maps_munmap : forall mo a n, model_ivs_wf mo -> lazy_in_maps mo ->
  (forall e, In e (vm_maps (m_vmmaps mo)) -> fst e = a -> snd e = n) ->
  lazy_in_maps (mdl_munmap mo a n).
Proof.
  intros mo a n (_ & _ & Wl & _) H Hbase iv Hin Hpos. rewrite mdl_munmap_lazy in Hin. rewrite mdl_munmap_vmmaps. cbn [vm_maps].
  destruct (maps_subtract_pieces' _ _ _ iv Wl Hin) as (r & Hr & P1 & P2 & P3).
  destruct (H r Hr ltac:(lia)) as (e & He & E1 & E2). exists e. split; [|lia].
  unfold map_remove. apply filter_In. split; [exact He|].
  destruct (bv_eqb (fst e) a) eqn:Eb; [|reflexivity]. exfalso. apply bv_eqb_eq in Eb.
  pose proof (Hbase e He Eb) as Es. rewrite Eb in E1, E2. rewrite Es in E2. lia.
Qed.
