(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import CatSim ShapeAlg AsanAcct AsanAcctShape AsanCeil BackingAlgebra.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes RzCPS NodesA Forced.
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

Section Proj.
Variables (mo : Model) (a n : word).
Let h := m_vmmaps mo.

Lemma mdl_mmap_rw_vmmaps : m_vmmaps (mdl_mmap_rw mo a n) = mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_lazy : m_vm_lazy (mdl_mmap_rw mo a n) = m_vm_lazy mo. Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_fds : m_fds (mdl_mmap_rw mo a n) = m_fds mo. Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_fs : m_fs (mdl_mmap_rw mo a n) = m_fs mo. Proof. reflexivity. Qed.
Lemma mdl_mmap_rw_halted : m_halted (mdl_mmap_rw mo a n) = m_halted mo. Proof. reflexivity. Qed.

Lemma mdl_fixed_vmmaps : forall flags, m_vmmaps (mdl_fixed flags mo a n) = mmap_fixed_rw_next h a n.
Proof. intros flags. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mdl_fixed_lazy50 : m_vm_lazy (mdl_fixed flags50 mo a n) = maps_subtract (m_vm_lazy mo) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. unfold mdl_fixed, with_mmap_replacement, with_mmap_backing. rewrite noreserve50. reflexivity. Qed.
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

Lemma Permutation_filter_k4 : forall {T : Type} (f : T -> bool) (l l' : list T), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros T f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [List.filter].
  - constructor.
  - destruct (f x); [constructor; exact IH | exact IH].
  - destruct (f x); destruct (f y); cbn [List.filter]; [apply perm_swap | apply Permutation_refl | apply Permutation_refl | apply Permutation_refl].
  - exact (Permutation_trans IH1 IH2).
Qed.

Lemma MInv_cut : forall A A' mo mo' lo hi,
  MInv A mo ->

  Z.max 0 (A_bytes (A_neg A)) <= Z.max 0 (A_bytes (A_neg A')) ->
  (forall p, page_allowedb A p = true -> page_allowedb A' p = true) ->
  lo mod 4096 = 0 -> hi mod 4096 = 0 ->
  m_vm_materialized mo' = List.filter (page_outside_range lo hi) (m_vm_materialized mo) ->
  (forall p, bv_unsigned p + 4096 <= lo \/ hi <= bv_unsigned p ->
     page_in_ranges p (m_vm_lazy mo) = true -> page_in_ranges p (m_vm_lazy mo') = true) ->
  eager_used mo' + A_bytes A' <= vm_limit (m_vmmaps mo') ->
  MInv A' mo'.
Proof.
  intros A A' mo mo' lo hi [(G & J & HP & M1 & M2 & M3 & M4 & MJ) M5] Hjunk Hsub Hlo Hhi Hmat Hlz Hb. constructor; [|exact Hb].
  exists (List.filter (page_outside_range lo hi) G), (List.filter (page_outside_range lo hi) J).
  split; [rewrite Hmat, <- filter_app; apply Permutation_filter_k4; exact HP|].
  split; [apply NoDup_filter; exact M1|].
  split; [intros p Hp; apply filter_In in Hp as [Hp _]; exact (M2 p Hp)|].
  split; [intros p Hp; apply filter_In in Hp as [Hp _]; exact (Hsub p (M3 p Hp))|].
  split.
  - intros p Hp. apply filter_In in Hp as [Hp Ho]. apply Hlz; [|exact (M4 p Hp)].
    apply aligned_page_out; [exact (M2 p Hp)| exact Hlo| exact Hhi|].
    unfold page_outside_range in Ho. apply negb_true_iff in Ho.
    apply andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho; left; lia| apply Z.ltb_ge in Ho; right; lia].
  - pose proof (filter_length_le (page_outside_range lo hi) J) as HL. unfold page_size in *. lia.
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

Definition cspec (ms : machine_state) (x8 : word) (mo : Model) (o : outcome SyscallEffect) : Prop :=
  syscall_spec (sys_input segs ms x8) mo o /\
  match o with Ok e _ _ => ~ spurious_refusal_cfg ncfg (sys_input segs ms x8) mo e | Unmodeled => True end.

Lemma cspec_nonalloc : forall ms x8 mo o, ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  (cspec ms x8 mo o <-> syscall_spec (sys_input segs ms x8) mo o).
Proof.
  intros ms x8 mo o Hna. unfold cspec. split; [intros [H _]; exact H|]. intros H. split; [exact H|].
  destruct o; [|exact I]. apply nonspurious_nonalloc. exact Hna.
Qed.

Lemma cspec_of_families : forall ms x8 mo (G R : Type) (og : G -> outcome SyscallEffect) (or_ : R -> outcome SyscallEffect) (g0 : G),
  injected_family_off ncfg (sys_input segs ms x8) = true ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> (exists g, o = og g) \/ (exists r, o = or_ r)) ->
  (forall g, exists e m', og g = Ok e m' [] /\ refusal_b (sys_input segs ms x8) mo (eff_ret e) = false) ->
  (forall r, exists e m', or_ r = Ok e m' [] /\ refusal_b (sys_input segs ms x8) mo (eff_ret e) = true) ->
  forall o, cspec ms x8 mo o <-> exists g, o = og g.
Proof.
  intros ms x8 mo G R og or_ g0 Hoff Hchar Hg Hr o. unfold cspec. split.
  - intros [Hsp Hns]. apply Hchar in Hsp as [Hgo | [r ->]]; [exact Hgo|]. exfalso.
    destruct (Hr r) as (e & m' & E & Href). rewrite E in Hns. apply Hns.
    split; [exact Hoff|]. split; [exact Href|].
    destruct (Hg g0) as (e0 & m0 & E0 & Hnr). exists e0, m0, []. split; [|exact Hnr].
    apply Hchar. left. exists g0. symmetry. exact E0.
  - intros [g ->]. split; [apply Hchar; left; exists g; reflexivity|].
    destruct (Hg g) as (e & m' & E & Hnr). rewrite E. apply spurious_refusal_not_refusal. exact Hnr.
Qed.

Lemma node_ok_mm : forall ms mo x8 (I : Type) (eff : I -> SyscallEffect) (mdl : I -> Model),
  m_halted mo = None -> ms_svc_pending ms = Some x8 ->
  (forall i, cspec ms x8 mo (Ok (eff i) (mdl i) [])) ->
  (forall o, cspec ms x8 mo o -> exists i, o = Ok (eff i) (mdl i) []) ->
  (forall i, syscall_effect_accesses (eff i) = []) ->
  (forall i, m_halted (mdl i) = None) ->
  (forall e m' ev, syscall_spec (sys_input segs ms x8) mo (Ok e m' ev) -> m_halted m' = None) ->
  node_ok segs (mkCfg ms mo) I (fun _ => []) (fun i => mkCfg (nretA ms (eff i)) (mdl i)).
Proof.
  intros ms mo x8 I eff mdl Hh Hsvc Hsound Hcompl Hacc Hnh Hnh_all. split.
  - intros i. destruct (Hsound i) as [Hsp Hns].
    eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | exact Hsp | exact Hns | exact (Hnh i) |].
    rewrite Hacc. apply materialize_model_accesses_nil.
  - intros e st Hss. inversion Hss; subst;
      match goal with
      | Hp : ms_svc_pending ms = None |- _ => rewrite Hsvc in Hp; discriminate
      | Hp : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in Hp; injection Hp as <-
      end.
    + match goal with Hsp : syscall_spec _ _ (Ok ?e0 ?m0 ?ev0), Hn : ~ spurious_refusal_cfg _ _ _ ?e0 |- _ =>
        destruct (Hcompl (Ok e0 m0 ev0) (conj Hsp Hn)) as [i Ei]; injection Ei as -> -> -> end.
      exists i. split; [reflexivity|].
      match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
        rewrite Hacc, materialize_model_accesses_nil in Hm; injection Hm as <- end.
      reflexivity.
    + exfalso.
      match goal with Hsp : syscall_spec _ _ (Ok ?e0 ?m0 ?ev0), Hn : ~ spurious_refusal_cfg _ _ _ ?e0 |- _ =>
        destruct (Hcompl (Ok e0 m0 ev0) (conj Hsp Hn)) as [i Ei]; injection Ei as -> -> -> end.
      match goal with Hm : materialize_model_accesses _ _ = None |- _ =>
        rewrite Hacc, materialize_model_accesses_nil in Hm; discriminate Hm end.
    + exfalso. match goal with Hsp : syscall_spec _ _ (Ok _ ?m0 _), Hc : m_halted ?m0 = Some _ |- _ =>
        rewrite (Hnh_all _ _ _ Hsp) in Hc; discriminate Hc end.
    + exfalso. match goal with Hsp : syscall_spec _ _ (Ok _ ?m0 _), Hk : m_killed ?m0 = Some _ |- _ =>
        rewrite (m_killed_of_m_halted_none _ (Hnh_all _ _ _ Hsp)) in Hk; discriminate Hk end.
    + exfalso. match goal with Hsp : syscall_spec _ _ Unmodeled |- _ =>
        assert (Hcs : cspec ms x8 mo Unmodeled) by (split; [exact Hsp| exact Logic.I]);
        destruct (Hcompl _ Hcs) as [i Ei]; discriminate Ei end.
Qed.

Theorem ast_node_mm : forall A A' Pm PM (I : Type) (i0 : I) (K : I -> machine_state -> Prop) (KM : I -> Model -> Prop)
    ms mo x8 (r : I -> word) (zs us : I -> list (word * word)) (mdl : I -> Model) T,
  AST segtop A Pm PM (mkCfg ms mo) ->
  ms_svc_pending ms = Some x8 ->
  (forall i, cspec ms x8 mo (Ok (mkEffectU (r i) [] (zs i) (us i) [] []) (mdl i) [])) ->
  (forall o, cspec ms x8 mo o -> exists i, o = Ok (mkEffectU (r i) [] (zs i) (us i) [] []) (mdl i) []) ->
  (forall i, macct segtop A' (mdl i)) ->
  (forall i x, zeros_cover (zs i) x = true -> HID A' (mdl i) x = false) ->
  (forall i x, zeros_cover (us i) x = true -> HID A' (mdl i) x = false) ->
  (forall i x, zeros_cover (zs i) x = false -> zeros_cover (us i) x = false -> mkH (m_vm_lazy (mdl i)) A' x = mkH (m_vm_lazy mo) A x) ->
  (forall i x, HID A' (mdl i) x = true ->
     page_in_ranges (page_base x) (vm_noaccess (m_vmmaps (mdl i))) = page_in_ranges (page_base x) (vm_noaccess (m_vmmaps mo))) ->
  (forall i, K i (nretA (restrict (HID A mo) ms) (mkEffectU (r i) [] (zs i) (us i) [] []))) ->
  (forall i, KM i (mdl i)) ->
  (forall i c', AST segtop A' (K i) (KM i) c' -> realizes segs c' T) ->
  (forall e m' ev, syscall_spec (sys_input segs ms x8) mo (Ok e m' ev) -> m_halted m' = None) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros A A' Pm PM I i0 K KM ms mo x8 r zs us mdl T Hc Hsvc Hsound Hcompl Hmc' Hz Hu Hout Hna HK HKM Hk Hnh_all.
  assert (HoutH : forall i x, zeros_cover (zs i) x = false -> zeros_cover (us i) x = false -> HID A' (mdl i) x = HID A mo x).
  { intros i x E1 E2. unfold HID. rewrite (Hout i x E1 E2). reflexivity. }
  destruct Hc as (Hmc & HPm & HPMmo & HZ0). cbn [cfg_ms cfg_model] in *.
  pose proof Hmc as (_ & _ & Hh & _).
  set (eff := fun i => mkEffectU (r i) [] (zs i) (us i) [] []).
  assert (Hnode : node_ok segs (mkCfg ms mo) I (fun _ => []) (fun i => mkCfg (nretA ms (eff i)) (mdl i))).
  { apply (node_ok_mm ms mo x8 I eff mdl Hh Hsvc Hsound Hcompl); [intros i; reflexivity| |exact Hnh_all].
    intros i. exact (proj1 (proj2 (proj2 (Hmc' i)))). }
  assert (Hsucc : forall i, AST segtop A' (K i) (KM i) (mkCfg (nretA ms (eff i)) (mdl i))).
  { intros i. split; [exact (Hmc' i)|]. cbn [cfg_ms cfg_model]. split; [|split; [exact (HKM i)|]].
    - unfold eff. rewrite (restrict_nretA_mm (HID A mo) (HID A' (mdl i)) ms (r i) (zs i) (us i) (Hz i) (HoutH i)). exact (HK i).
    - intros x Hx Hnx. cbn [cfg_ms cfg_model] in *. unfold eff. rewrite nretA_mm_mem.
      pose proof (HID_of_mkH A' (mdl i) x Hx) as HxH.
      destruct (zeros_cover (zs i) x) eqn:Ez; [rewrite (Hz i x Ez) in HxH; discriminate HxH|].
      destruct (zeros_cover (us i) x) eqn:Eu; [rewrite (Hu i x Eu) in HxH; discriminate HxH|].
      rewrite (Hna i x HxH) in Hnx. rewrite (Hout i x Ez Eu) in Hx.
      exact (HZ0 x Hx Hnx). }
  assert (HT0 : T []) by (eapply realizes_nonempty; exact (Hk i0 _ (Hsucc i0))).
  eapply rz_conseq.
  { apply (rz_node segs (mkCfg ms mo) I (fun _ => []) (fun i => mkCfg (nretA ms (eff i)) (mdl i)) (fun _ => T) i0 Hnode).
    intros i. exact (Hk i _ (Hsucc i)). }
  intros tr. split.
  - intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
  - intros HTtr. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) HTtr).
Qed.

End MmNode.

Lemma vm_backing_used_le' : forall A mo, A_wf A -> MInv A mo -> vm_backing_used mo <= eager_used mo + A_bytes A.
Proof.
  intros A mo Hwf HM. rewrite vm_backing_used_split. pose proof (MInv_used_le A mo Hwf HM). lia.
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

Lemma mmap34_stock : forall segs ms mo len o,
  0 < len < 2^64 ->
  areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 3 -> areg ms 13 = Z_to_bv 64 34 -> areg ms 15 = Z_to_bv 64 0 ->
  syscall_spec (sys_input segs ms (Z_to_bv 64 222)) mo o <->
  (exists a, grant_ok34 mo (page_round_up_Z len) a
    /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]) (mdl_mmap_rw mo a (Z_to_bv 64 (page_round_up_Z len))) [])
  \/ (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) mo []).
Proof.
  intros segs ms mo len o Hlen H11 H12 H13 H15.
  rewrite syscall_spec_222 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, H11, H12, H13, H15.
  assert (E1 : mmap_off_aligned_b (Z_to_bv 64 0) = true) by (vm_compute; reflexivity).
  assert (E2 : mmap_anon_b (Z_to_bv 64 34) = true) by (vm_compute; reflexivity).
  assert (E3 : w_is0 (Z_to_bv 64 len) = false).
  { rewrite w_is0_lit by lia. apply Z.eqb_neq. lia. }
  assert (E4 : mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 0) = true) by (vm_compute; reflexivity).
  pose proof (mmap_rw_outcome (areg ms 10) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 34) (areg ms 14) (Z_to_bv 64 0)
                (sys_input segs ms (Z_to_bv 64 222)) mo o E1 E2 E3 E4) as R.
  cbv zeta in R. rewrite unsigned_lit in R by lia. rewrite R. clear R. unfold mmap_err_out. split.
  - intros [He | (a & Ha & ->)]; [right; exact He|].
    left. exists a. split; [exact Ha|]. unfold with_mmap_backing. rewrite noreserve34. reflexivity.
  - intros [(a & Ha & ->) | He]; [|left; exact He]. right. exists a. split; [exact Ha|]. unfold with_mmap_backing. rewrite noreserve34. reflexivity.
Qed.

Lemma mmap34_char : forall segs ms mo len o,
  0 < len < 2^64 ->
  areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 3 -> areg ms 13 = Z_to_bv 64 34 -> areg ms 15 = Z_to_bv 64 0 ->
  mmap_grant_refusable (Z_to_bv 64 34) mo (page_round_up_Z len) = false ->
  cspec segs ms (Z_to_bv 64 222) mo o <->
  exists a, grant_ok34 mo (page_round_up_Z len) a
    /\ o = Ok (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]) (mdl_mmap_rw mo a (Z_to_bv 64 (page_round_up_Z len))) [].
Proof.
  intros segs ms mo len o Hlen H11 H12 H13 H15 Hnr.
  set (nZ := page_round_up_Z len) in *.
  assert (HnZ : 0 <= nZ) by (unfold nZ; pose proof (page_round_up_Z_ge_all len); lia).
  unfold mmap_grant_refusable in Hnr. apply orb_false_elim in Hnr as [Hb Hg].
  apply negb_false_iff in Hb. apply negb_false_iff in Hg.
  apply vm_gap_available_iff in Hg as (a0 & G1 & G2 & G3 & G4).
  assert (Ha0 : grant_ok34 mo nZ a0) by (repeat split; assumption).
  pose (G := {a : word | grant_ok34 mo nZ a}). pose (R := {e : Z | In e mmap_errnos}).
  pose proof (cspec_of_families segs ms (Z_to_bv 64 222) mo G R
                (fun g => Ok (mkEffect (proj1_sig g) [] [(proj1_sig g, Z_to_bv 64 nZ)]) (mdl_mmap_rw mo (proj1_sig g) (Z_to_bv 64 nZ)) [])
                (fun r => Ok (mkEffect (errno_ret (proj1_sig r)) [] []) mo [])
                (exist _ a0 Ha0) eq_refl) as C.
  rewrite C.
  - split; [intros [[a Ha] ->]; exists a; split; [exact Ha| reflexivity]| intros (a & Ha & ->); exists (exist _ a Ha); reflexivity].
  - intros o'. rewrite (mmap34_stock segs ms mo len o' Hlen H11 H12 H13 H15). fold nZ. split.
    + intros [(a & Ha & ->) | (e & He & ->)]; [left; exists (exist _ a Ha)| right; exists (exist _ e He)]; reflexivity.
    + intros [[[a Ha] ->] | [[e He] ->]]; [left; exists a| right; exists e]; split; auto.
  - intros [a Ha]. eexists _, _. split; [reflexivity|]. cbn [eff_ret proj1_sig].
    destruct Ha as (_ & _ & A3 & _). exact (not_errno_below_top mmap_errnos a nZ (m_vmmaps mo) eq_refl HnZ A3).
  - intros [e He]. eexists _, _. split; [reflexivity|]. cbn [eff_ret proj1_sig].
    change (ret_in_errnos mmap_errnos (errno_ret e) = true). unfold ret_in_errnos. apply existsb_exists.
    exists e. split; [exact He| apply bv_eqb_eq; reflexivity].
Qed.

Lemma mmap34_nohalt : forall segs ms mo len,
  0 < len < 2^64 ->
  areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 3 -> areg ms 13 = Z_to_bv 64 34 -> areg ms 15 = Z_to_bv 64 0 ->
  m_halted mo = None ->
  forall e m' ev, syscall_spec (sys_input segs ms (Z_to_bv 64 222)) mo (Ok e m' ev) -> m_halted m' = None.
Proof.
  intros segs ms mo len Hlen H11 H12 H13 H15 Hh e m' ev Hsp.
  apply (mmap34_stock segs ms mo len _ Hlen H11 H12 H13 H15) in Hsp as [(a & _ & E) | (e0 & _ & E)];
    apply Ok_inj in E as (_ & -> & _); [rewrite mdl_mmap_rw_halted|]; exact Hh.
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
Proof using Hwx Hsegs.
  intros A Pm PM G K KM len Hlen Hm HM HAT T [ms mo] Hc Hk.
  pose proof Hc as (Hmc & HPm & HPMmo & _). cbn [cfg_ms cfg_model] in *.
  pose proof Hmc as (HAwf & HMInv & Hh & Hr & Ht).
  destruct (Hm _ HPm) as (Hsvc & H11 & H12 & H13 & H15 & HKa). rewrite restrict_svc in Hsvc. rewrite restrict_areg in H11, H12, H13, H15.
  destruct (HM _ HPMmo) as (Hwf & Hlim & Hgap & Hbud & HKM).
  set (nZ := page_round_up_Z len) in *. set (n := Z_to_bv 64 nZ) in *.
  assert (HnZ : 0 <= nZ) by (unfold nZ; pose proof (page_round_up_Z_ge_all len); lia).
  destruct (proj1 (vm_gap_available_iff _ _) Hgap) as (a0 & G1 & G2 & G3 & G4).
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  assert (Hnsmall : nZ < 2^64) by (pose proof (u64_range a0); lia).
  assert (Hbacked : mmap_noreserve_backed_ok (Z_to_bv 64 34) mo nZ = true).
  { unfold mmap_noreserve_backed_ok. rewrite noreserve34. apply Z.leb_le.
    pose proof (vm_backing_used_le' A mo HAwf HMInv). pose proof (A_bytes_nonneg A HAwf). lia. }
  assert (Hnr : mmap_grant_refusable (Z_to_bv 64 34) mo nZ = false).
  { unfold mmap_grant_refusable. rewrite Hbacked, Hgap. reflexivity. }
  assert (Ha0 : grant_ok34 mo nZ a0) by (repeat split; assumption).
  pose (I := {a : word | grant_ok34 mo nZ a}).
  apply (ast_node_mm segs segtop A A Pm PM I (exist _ a0 Ha0) (fun i => K (proj1_sig i)) (fun i => KM (proj1_sig i))
           ms mo (Z_to_bv 64 222) (fun i => proj1_sig i) (fun i => [(proj1_sig i, n)]) (fun _ => [])
           (fun i => mdl_mmap_rw mo (proj1_sig i) n) T Hc Hsvc).
  - intros [a Ha]. cbn [proj1_sig]. apply (mmap34_char segs ms mo len _ Hlen H11 H12 H13 H15 Hnr). exists a. split; [exact Ha| reflexivity].
  - intros o Ho. apply (mmap34_char segs ms mo len _ Hlen H11 H12 H13 H15 Hnr) in Ho as (a & Ha & ->).
    exists (exist _ a Ha). reflexivity.
  - intros [a Ha]. cbn [proj1_sig]. destruct Ha as (A1 & A2 & A3 & A4 & A5).
    split; [exact HAwf|]. split; [|split; [rewrite mdl_mmap_rw_halted; exact Hh| split; [rewrite mdl_mmap_rw_lazy; exact Hr| exact Ht]]].
    apply (MInv_transport A mo _ HMInv); [reflexivity| reflexivity|].
    pose proof (u64_range a). assert (Hn : bv_unsigned n = nZ) by (unfold n; apply unsigned_lit; lia).
    pose proof (eager_used_mmap_rw_le mo a n (proj1 Hwf) ltac:(lia)) as Hle. rewrite mdl_mmap_rw_vmmaps. cbn [vm_limit]. lia.
  - intros [a Ha] x Hx. cbn [proj1_sig] in *. destruct Ha as (A1 & A2 & A3 & A4 & A5).
    rewrite zeros_cover_one in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    pose proof (u64_range a). assert (Hn : bv_unsigned n = nZ) by (unfold n; apply unsigned_lit; lia).
    unfold HID, mkH. rewrite mdl_mmap_rw_lazy, (lazy_off_free mo a n x Hlim A4 A1 ltac:(lia)). cbn [andb orb].
    apply Z.leb_gt. pose proof (HAT mo HPMmo). lia.
  - intros i x Hx. discriminate Hx.
  - intros i x _ _. reflexivity.
  - intros i x _. reflexivity.
  - intros [a Ha]. cbn [proj1_sig]. apply HKa. exact (proj1 (HKM a Ha)).
  - intros [a Ha]. cbn [proj1_sig]. exact (proj2 (HKM a Ha)).
  - intros [a Ha] c' Hc'. cbn [proj1_sig] in Hc'. apply Hk. exists a. split; [exact (proj1 (HKM a Ha))| exact Hc'].
  - exact (mmap34_nohalt segs ms mo len Hlen H11 H12 H13 H15 Hh).
Qed.

End Rule1.

Lemma mmap_fixed_stock : forall segs ms mo flags addr len o,
  (flags = flags50 \/ flags = flags16434) ->
  0 < len < 2^64 -> 0 < addr -> addr mod page_size = 0 ->
  addr + page_round_up_Z len <= alloc_top (m_vmmaps mo) ->
  areg ms 10 = Z_to_bv 64 addr -> areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 3 -> areg ms 13 = flags -> areg ms 15 = Z_to_bv 64 0 ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (page_round_up_Z len) in
  syscall_spec (sys_input segs ms (Z_to_bv 64 222)) mo o <->
  (mmap_fixed_rw_budget_ok flags mo a n = true /\ o = Ok (mkEffect a [] [(a, n)]) (mdl_fixed flags mo a n) [])
  \/ (exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) mo [])
  \/ (exists e, In e mmap_errnos /\
        o = Ok (mkEffectU (errno_ret e) [] [] [(a, n)] [] [])
               (with_mmap_destroyed a n (mmap_fixed_destroyed_next (m_vmmaps mo) a n) mo) []).
Proof.
  intros segs ms mo flags addr len o Hfl Hlen Hpos Hal Htop H10 H11 H12 H13 H15 Hrf Hmc a n. subst a n.
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  assert (HnZ : len <= page_round_up_Z len) by apply page_round_up_Z_ge_all.
  rewrite syscall_spec_222 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, H10, H11, H12, H13, H15.
  unfold mmap_spec.
  assert (E1 : mmap_off_aligned_b (Z_to_bv 64 0) = true) by (vm_compute; reflexivity).
  assert (E3 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  rewrite E1, E3. cbn [negb].
  assert (Ec : mmap_anon_b flags = true /\ mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
               /\ mmap_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
               /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
               /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true).
  { destruct Hfl as [-> | ->]; vm_compute; repeat split. }
  destruct Ec as (E2 & E4 & E5 & E6 & E7). rewrite E2, E4, E5, E6, E7. cbn [negb].
  rewrite !unsigned_lit by lia.
  rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
  rewrite bind_get_model. cbv zeta.
  rewrite (proj2 (Z.leb_le _ _) Htop), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
  rewrite Hrf, Hmc. cbn [andb].
  sys_unfold. split.
  - intros H. destruct o as [y m2 evs|]; inv_sys.
    all: first [ left; split; [assumption| reflexivity]
               | right; left; eexists; split; [eassumption| reflexivity]
               | right; right; eexists; split; [eassumption| reflexivity] ].
  - intros [(Hb & ->) | [(e & He & ->) | (e & He & ->)]].
    + right. left. exists tt, mo, [], []. split; [exists tt; split; [exact Hb| reflexivity]|]. split; [|reflexivity].
      exists tt, (mdl_fixed flags mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))), [], [].
      split; [reflexivity|]. split; reflexivity.
    + left. exists e, mo, [], []. split; [exists e; split; [exact He| reflexivity]|]. split; reflexivity.
    + right. right. exists e, mo, [], []. split; [exists e; split; [exact He| reflexivity]|]. split; [|reflexivity].
      eexists tt, _, [], []. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma mmap_fixed_char : forall segs ms mo flags addr len o,
  (flags = flags50 \/ flags = flags16434) ->
  0 < len < 2^64 -> 0 < addr -> addr mod page_size = 0 ->
  addr + page_round_up_Z len <= alloc_top (m_vmmaps mo) ->
  areg ms 10 = Z_to_bv 64 addr -> areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 3 -> areg ms 13 = flags -> areg ms 15 = Z_to_bv 64 0 ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  mmap_fixed_rw_budget_ok flags mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  cspec segs ms (Z_to_bv 64 222) mo o <->
  o = Ok (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))])
         (mdl_fixed flags mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len))) [].
Proof.
  intros segs ms mo flags addr len o Hfl Hlen Hpos Hal Htop H10 H11 H12 H13 H15 Hrf Hmc Hbud.
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom. unfold two_pow_64, stack_max_size in Hroom.
  pose proof (page_round_up_Z_ge_all len) as HnZ.
  set (a := Z_to_bv 64 addr) in *. set (n := Z_to_bv 64 (page_round_up_Z len)) in *.
  pose (R := ({e : Z | In e mmap_errnos} + {e : Z | In e mmap_errnos})%type).
  pose proof (cspec_of_families segs ms (Z_to_bv 64 222) mo unit R
                (fun _ => Ok (mkEffect a [] [(a, n)]) (mdl_fixed flags mo a n) [])
                (fun r => match r with
                          | inl e => Ok (mkEffect (errno_ret (proj1_sig e)) [] []) mo []
                          | inr e => Ok (mkEffectU (errno_ret (proj1_sig e)) [] [] [(a, n)] [] [])
                                        (with_mmap_destroyed a n (mmap_fixed_destroyed_next (m_vmmaps mo) a n) mo) []
                          end)
                tt eq_refl) as C.
  rewrite C.
  - split; [intros [[] ->]; reflexivity| intros ->; exists tt; reflexivity].
  - intros o'. rewrite (mmap_fixed_stock segs ms mo flags addr len o' Hfl Hlen Hpos Hal Htop H10 H11 H12 H13 H15 Hrf Hmc).
    cbv zeta. fold a n. split.
    + intros [(_ & ->) | [(e & He & ->) | (e & He & ->)]];
        [left; exists tt; reflexivity| right; exists (inl (exist _ e He)); reflexivity| right; exists (inr (exist _ e He)); reflexivity].
    + intros [[[] ->] | [[[e He] | [e He]] ->]]; [left; split; [exact Hbud| reflexivity]| right; left; exists e; auto| right; right; exists e; auto].
  - intros []. eexists _, _. split; [reflexivity|]. cbn [eff_ret].
    apply (not_errno_below_top mmap_errnos a (page_round_up_Z len) (m_vmmaps mo) eq_refl); [lia|].
    unfold a. rewrite unsigned_lit by lia. exact Htop.
  - intros [[e He] | [e He]]; eexists _, _; (split; [reflexivity|]); cbn [eff_ret proj1_sig];
      change (ret_in_errnos mmap_errnos (errno_ret e) = true); unfold ret_in_errnos; apply existsb_exists;
      exists e; (split; [exact He| apply bv_eqb_eq; reflexivity]).
Qed.

Lemma m_halted_with_mmap_destroyed : forall a n h mo, m_halted (with_mmap_destroyed a n h mo) = m_halted mo.
Proof. intros. unfold with_mmap_destroyed. reflexivity. Qed.

Lemma mmap_fixed_nohalt : forall segs ms mo flags addr len,
  (flags = flags50 \/ flags = flags16434) ->
  0 < len < 2^64 -> 0 < addr -> addr mod page_size = 0 ->
  addr + page_round_up_Z len <= alloc_top (m_vmmaps mo) ->
  areg ms 10 = Z_to_bv 64 addr -> areg ms 11 = Z_to_bv 64 len -> areg ms 12 = Z_to_bv 64 3 -> areg ms 13 = flags -> areg ms 15 = Z_to_bv 64 0 ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  m_halted mo = None ->
  forall e m' ev, syscall_spec (sys_input segs ms (Z_to_bv 64 222)) mo (Ok e m' ev) -> m_halted m' = None.
Proof.
  intros segs ms mo flags addr len Hfl Hlen Hpos Hal Htop H10 H11 H12 H13 H15 Hrf Hmc Hh e m' ev Hsp.
  apply (mmap_fixed_stock segs ms mo flags addr len _ Hfl Hlen Hpos Hal Htop H10 H11 H12 H13 H15 Hrf Hmc) in Hsp.
  cbv zeta in Hsp. destruct Hsp as [(_ & E) | [(e0 & _ & E) | (e0 & _ & E)]]; apply Ok_inj in E as (_ & -> & _).
  - rewrite mdl_fixed_halted. exact Hh.
  - exact Hh.
  - rewrite m_halted_with_mmap_destroyed. exact Hh.
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
Proof using Hwx Hsegs.
  intros A Pm PM K KM addr len Hlen Hpos Hal Hm HM HAT T [ms mo] Hc Hk.
  pose proof Hc as (Hmc & HPm & HPMmo & _). cbn [cfg_ms cfg_model] in *.
  pose proof Hmc as (HAwf & HMInv & Hh & Hr & Ht).
  destruct (Hm _ HPm) as (Hsvc & H10 & H11 & H12 & H13 & H15 & HK). rewrite restrict_svc in Hsvc. rewrite restrict_areg in H10, H11, H12, H13, H15.
  destruct (HM _ HPMmo) as (Hwf & Htop & Hrf & Hmcn & Hbud & HKM).
  destruct (req_facts mo addr len Hlen Hpos Hal Htop) as (Ea & En & HnP & Hnl & Hend).
  set (nZ := page_round_up_Z len) in *. set (a := Z_to_bv 64 addr) in *. set (n := Z_to_bv 64 nZ) in *.
  pose proof Hwf as (Wm & Wn & Wl & _). unfold page_size in Hal.
  assert (Hbok : mmap_fixed_rw_budget_ok flags50 mo a n = true).
  { apply mmap_fixed_rw_budget_ok_commit_intro; [exact noreserve50| exact Hwf|]. rewrite Ea, En.
    pose proof (vm_backing_used_le' A mo HAwf HMInv). lia. }
  assert (Hlo : addr mod 4096 = 0) by exact Hal. assert (Hhi : (addr + nZ) mod 4096 = 0) by (rewrite Zplus_mod, Hlo, Hnl; reflexivity).
  apply (ast_node_mm segs segtop A A Pm PM unit tt (fun _ => K) (fun _ => KM) ms mo (Z_to_bv 64 222)
           (fun _ => a) (fun _ => [(a, n)]) (fun _ => []) (fun _ => mdl_fixed flags50 mo a n) T Hc Hsvc).
  - intros []. apply (mmap_fixed_char segs ms mo flags50 addr len _ (or_introl eq_refl) Hlen Hpos Hal Htop H10 H11 H12 H13 H15 Hrf Hmcn Hbok).
    reflexivity.
  - intros o Ho. exists tt. exact (proj1 (mmap_fixed_char segs ms mo flags50 addr len _ (or_introl eq_refl) Hlen Hpos Hal Htop H10 H11 H12 H13 H15 Hrf Hmcn Hbok) Ho).
  - intros []. split; [exact HAwf|]. split; [|split; [rewrite mdl_fixed_halted; exact Hh|]].
    + apply (MInv_cut A A mo _ addr (addr + nZ) HMInv (Z.le_refl _) (fun p H => H) Hlo Hhi); [rewrite mdl_fixed_mat, Ea, En; reflexivity| |].
      * intros p Hp Hin. rewrite mdl_fixed_lazy50, Ea, En. apply page_in_ranges_subtract_keep; [exact Wl| lia| exact Hp| exact Hin].
      * pose proof (eager_used_fixed50_le mo a n Hwf) as Hle. rewrite Ea, En in Hle.
        rewrite mdl_fixed_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_limit]. lia.
    + split; [rewrite mdl_fixed_lazy50; apply ranges_from_b_subtract; assumption| exact Ht].
  - intros [] x Hx. rewrite zeros_cover_one, Ea, En in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    apply (HID_cut_in A mo _ addr (addr + nZ) x Wl Hlo Hhi); [pose proof (HAT mo HPMmo); lia| rewrite mdl_fixed_lazy50, Ea, En; reflexivity| lia].
  - intros [] x Hx. discriminate Hx.
  - intros [] x Hx _. rewrite zeros_cover_one, Ea, En in Hx. apply andb_false_iff in Hx.
    apply (HID_cut_out A mo _ addr (addr + nZ) x Wl Hlo Hhi ltac:(lia)); [rewrite mdl_fixed_lazy50, Ea, En; reflexivity|].
    destruct Hx as [Hx|Hx]; [apply Z.leb_gt in Hx| apply Z.ltb_ge in Hx]; lia.
  - intros [] x Hx. rewrite mdl_fixed_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite Ea, En.
    apply noaccess_cut_out; [exact Wn| exact Hlo| exact Hhi| lia|].
    destruct (Z.le_gt_cases addr (bv_unsigned x)); [|left; lia]. destruct (Z.lt_ge_cases (bv_unsigned x) (addr + nZ)); [|right; lia].
    exfalso. rewrite (HID_cut_in A mo _ addr (addr + nZ) x Wl Hlo Hhi) in Hx; [discriminate Hx| pose proof (HAT mo HPMmo); lia| |lia].
    rewrite mdl_fixed_lazy50, Ea, En. reflexivity.
  - intros []. exact HK.
  - intros []. exact HKM.
  - intros [] c' Hc'. exact (Hk c' Hc').
  - exact (mmap_fixed_nohalt segs ms mo flags50 addr len (or_introl eq_refl) Hlen Hpos Hal Htop H10 H11 H12 H13 H15 Hrf Hmcn Hh).
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
Proof using Hwx Hsegs.
  intros A Pm PM K KM addr len Hlen Hpos Hal Htask Hm HM T [ms mo] Hc Hk.
  pose proof Hc as (Hmc & HPm & HPMmo & _). cbn [cfg_ms cfg_model] in *.
  pose proof Hmc as (HAwf & HMInv & Hh & Hr & Ht).
  destruct (Hm _ HPm) as (Hsvc & H10 & H11 & HK). rewrite restrict_svc in Hsvc. rewrite restrict_areg in H10, H11.
  destruct (HM _ HPMmo) as (Hwf & Hhas & Hbud & HKM).
  pose proof (page_round_up_Z_ge_all len). pose proof (page_round_up_Z_aligned' len) as Hnl. unfold page_size in Hnl, Hal. unfold TASK_SIZE in Htask.
  set (nZ := page_round_up_Z len) in *. set (a := Z_to_bv 64 addr) in *. set (n := Z_to_bv 64 nZ) in *.
  assert (Ea : bv_unsigned a = addr) by (apply unsigned_lit; lia). assert (En : bv_unsigned n = nZ) by (apply unsigned_lit; lia).
  pose proof Hwf as (Wm & Wn & Wl & _).
  assert (Hlo : addr mod 4096 = 0) by exact Hal. assert (Hhi : (addr + nZ) mod 4096 = 0) by (rewrite Zplus_mod, Hlo, Hnl; reflexivity).
  assert (Hchar : forall o, syscall_spec (sys_input segs ms (Z_to_bv 64 215)) mo o <->
                    o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []) (mdl_munmap mo a n) []).
  { intros o. rewrite syscall_spec_215 by reflexivity. rewrite in_a0_si, in_a1_si, H10, H11.
    pose proof (munmap_exact_outcome a (Z_to_bv 64 len) (sys_input segs ms (Z_to_bv 64 215)) mo o) as R.
    rewrite unsigned_lit in R by lia. apply R; [rewrite Ea; unfold page_size; exact Hlo| rewrite w_is0_lit by lia; apply Z.eqb_neq; lia| rewrite Ea; unfold TASK_SIZE; lia| exact Hhas]. }
  apply (ast_node_mm segs segtop A A Pm PM unit tt (fun _ => K) (fun _ => KM) ms mo (Z_to_bv 64 215)
           (fun _ => Z_to_bv 64 0) (fun _ => []) (fun _ => [(a, n)]) (fun _ => mdl_munmap mo a n) T Hc Hsvc).
  - intros []. apply cspec_nonalloc; [not_alloc|]. apply Hchar. reflexivity.
  - intros o Ho. exists tt. apply cspec_nonalloc in Ho; [|not_alloc]. exact (proj1 (Hchar o) Ho).
  - intros []. split; [exact HAwf|]. split; [|split; [rewrite mdl_munmap_halted; exact Hh|]].
    + apply (MInv_cut A A mo _ addr (addr + nZ) HMInv (Z.le_refl _) (fun p H => H) Hlo Hhi); [rewrite mdl_munmap_mat, Ea, En; reflexivity| |].
      * intros p Hp Hin. rewrite mdl_munmap_lazy, Ea, En. apply page_in_ranges_subtract_keep; [exact Wl| lia| exact Hp| exact Hin].
      * pose proof (eager_used_munmap_le mo a n Hwf) as Hle. rewrite Ea, En in Hle.
        rewrite mdl_munmap_vmmaps. cbn [vm_limit]. lia.
    + split; [rewrite mdl_munmap_lazy; apply ranges_from_b_subtract; assumption| exact Ht].
  - intros [] x Hx. discriminate Hx.
  - intros [] x Hx. rewrite zeros_cover_one, Ea, En in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
    apply (HID_cut_in A mo _ addr (addr + nZ) x Wl Hlo Hhi); [unfold TASK_SIZE in *; lia| rewrite mdl_munmap_lazy, Ea, En; reflexivity| lia].
  - intros [] x _ Hx. rewrite zeros_cover_one, Ea, En in Hx. apply andb_false_iff in Hx.
    apply (HID_cut_out A mo _ addr (addr + nZ) x Wl Hlo Hhi ltac:(lia)); [rewrite mdl_munmap_lazy, Ea, En; reflexivity|].
    destruct Hx as [Hx|Hx]; [apply Z.leb_gt in Hx| apply Z.ltb_ge in Hx]; lia.
  - intros [] x Hx. rewrite mdl_munmap_vmmaps. cbn [vm_noaccess]. rewrite Ea, En.
    apply noaccess_cut_out; [exact Wn| exact Hlo| exact Hhi| lia|].
    destruct (Z.le_gt_cases addr (bv_unsigned x)); [|left; lia]. destruct (Z.lt_ge_cases (bv_unsigned x) (addr + nZ)); [|right; lia].
    exfalso. rewrite (HID_cut_in A mo _ addr (addr + nZ) x Wl Hlo Hhi) in Hx; [discriminate Hx| unfold TASK_SIZE in *; lia| |lia].
    rewrite mdl_munmap_lazy, Ea, En. reflexivity.
  - intros []. exact HK.
  - intros []. exact HKM.
  - intros [] c' Hc'. exact (Hk c' Hc').
  - intros e m' ev Hsp. apply Hchar in Hsp. apply Ok_inj in Hsp as (_ & -> & _). rewrite mdl_munmap_halted. exact Hh.
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

