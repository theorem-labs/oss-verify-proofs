(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning ITree Nodes Decode Ceiling VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import BackingAlgebra.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require LZPages NodesLZMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import LJ ALinkPg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation stwfL := (Bridge.stwf nodeL nstepL nexitL nsafeL).

Lemma bv_eqb_refl : forall (w : word), bv_eqb w w = true.
Proof. intros w. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma resp_eqb_zeros1 : forall r (a n : word),
  resp_eqb (mkEffect r [] [(a, n)]) (mkEffect r [] [(a, n)]) = true.
Proof. intros. cbn. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma dec_fixed_ok : forall addr len rsp,
  strip rsp = fixed_eff addr len -> dec_fixed addr len rsp = Some tt.
Proof. intros addr len rsp E. unfold dec_fixed. rewrite E. unfold fixed_eff. rewrite resp_eqb_zeros1. reflexivity. Qed.

Lemma dec_madv_ok : forall addr len rsp,
  strip rsp = madv_eff addr len -> dec_madv addr len rsp = Some tt.
Proof. intros addr len rsp E. unfold dec_madv. rewrite E. unfold madv_eff. rewrite resp_eqb_zeros1. reflexivity. Qed.

Lemma stwf_ebind {A Bt} : forall (t : itree nodeL (exc A)) (f : A -> itree nodeL (exc Bt)) mo (P : exc Bt -> Model -> Prop),
  stwfL t mo (fun r mo' => match r with Unr => False | Ok a => stwfL (f a) mo' P end) ->
  stwfL (ebind t f) mo P.
Proof.
  intros t f mo P H. unfold ebind. apply Bridge.stwf_bind. eapply Bridge.stwf_mono; [exact H|].
  intros r mo' Hr. destruct r as [|a]; [destruct Hr| exact Hr].
Qed.

Lemma stwf_ret {A} : forall (a : A) mo (P : exc A -> Model -> Prop), P (Ok a) mo -> stwfL (Ret (Ok a)) mo P.
Proof. intros a mo P H. exact H. Qed.

Lemma stwf_commit : forall addr len mo (Q : exc unit -> Model -> Prop),
  nsafeL (LMmapCommit addr len SHADOW_OFF) mo ->
  Q (Ok tt) (lmcommit_post mo addr len SHADOW_OFF) ->
  stwfL (t_commit addr len) mo Q.
Proof.
  intros addr len mo Q HS HQ. unfold t_commit, enode. cbn [Bridge.stwf]. split; [exact HS|]. split.
  - intros code mo' HX. exact HX.
  - intros rsp mo' evs (-> & E & ->). split; [reflexivity|].
    rewrite (dec_fixed_ok addr len rsp E). cbn [Bridge.stwf]. exact HQ.
Qed.

Lemma overlap_sum_disjoint_all : forall l lo hi,
  Forall (fun q => B q + S q <= lo \/ hi <= B q) l -> overlap_sum l lo hi = 0.
Proof.
  induction l as [|q l IH]; intros lo hi HF; [reflexivity|].
  inversion HF as [|q' l' Hq Hl]; subst. rewrite overlap_sum_cons, (IH _ _ Hl), (iv_count_in_rng_disjoint q lo hi Hq). lia.
Qed.

Definition iv_inside (lo hi : Z) (p : word * word) : Prop := B p <= lo /\ hi <= B p + S p.

Lemma map_contains_inside : forall l (lo n : word),
  map_contains l lo n = true -> exists p, In p l /\ iv_inside (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) p.
Proof.
  intros l lo n H. unfold map_contains in H. apply existsb_exists in H as (p & Hin & Hp).
  exists p. split; [exact Hin|]. cbv zeta in Hp. apply andb_true_iff in Hp as [H1 H2].
  apply Z.leb_le in H1, H2. unfold iv_inside, B, S. lia.
Qed.

Lemma overlap_sum_inside_le : forall l lo hi p,
  seps l -> In p l -> iv_inside lo hi p -> lo < hi -> overlap_sum l lo hi <= hi - lo.
Proof.
  intros l lo hi p Hs. induction Hs as [|r l Hr Hl IH]; intros Hin Hp Hlt; [destruct Hin|].
  rewrite overlap_sum_cons. destruct Hin as [<-|Hin].
  - rewrite (overlap_sum_disjoint_all l lo hi).
    + pose proof (iv_count_in_rng_le r lo hi ltac:(lia)). lia.
    + apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) Hr q Hq) as D.
      unfold iv_disjoint, iv_inside, B, S in *. lia.
  - pose proof (proj1 (Forall_forall _ _) Hr p Hin) as D.
    rewrite (iv_count_in_rng_disjoint r lo hi); [pose proof (IH Hin Hp Hlt); lia|].
    unfold iv_disjoint, iv_inside, B, S in *. lia.
Qed.

Definition vmwf (mo : Model) : Prop := model_ivs_wf mo /\ seps (vm_maps (m_vmmaps mo)).

Lemma minvL_vmwf : forall mo, minvL mo -> vmwf mo.
Proof. intros mo (_ & _ & Hw & Hs). split; assumption. Qed.

Section Commit.
Variables (mo : Model) (addr len off : Z).
Let A := Z_to_bv 64 addr.
Let n := lenW len.
Let h := m_vmmaps mo.
Hypothesis Hmc : map_contains (vm_maps h) A n = true.

Let mo1 := vm_forget_range (bv_unsigned A) (bv_unsigned A + bv_unsigned n) (with_vmmaps (mmap_fixed_rw_next h A n) mo).
Let W := pages_of (shw_lo off (addrZ addr)) (shw_hi off (addrZ addr) (lenZ len)).

#[using="Hmc"] Lemma lmcommit_post_eq :
  lmcommit_post mo addr len off = with_vm_backing (m_vm_lazy mo1) (W ++ m_vm_materialized mo1) mo1.
Proof.
  unfold lmcommit_post, lmfixed_next. fold A n h. rewrite Hmc.
  unfold with_mmap_replacement, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 MAPF_FIXED)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

#[using="Hmc mo1 W"] Lemma commit_post_vmmaps : m_vmmaps (lmcommit_post mo addr len off) = mmap_fixed_rw_next h A n.
Proof. rewrite lmcommit_post_eq. reflexivity. Qed.

#[using="A n Hmc mo1 W"] Lemma commit_post_maps : vm_maps (m_vmmaps (lmcommit_post mo addr len off)) = vm_maps h.
Proof. rewrite commit_post_vmmaps. reflexivity. Qed.
#[using="A n Hmc mo1 W"] Lemma commit_post_reserved : vm_reserved (m_vmmaps (lmcommit_post mo addr len off)) = vm_reserved h.
Proof. rewrite commit_post_vmmaps. reflexivity. Qed.
#[using="A n Hmc mo1 W"] Lemma commit_post_limit : vm_limit (m_vmmaps (lmcommit_post mo addr len off)) = vm_limit h.
Proof. rewrite commit_post_vmmaps. reflexivity. Qed.
#[using="A n Hmc mo1 W"] Lemma commit_post_init_sp : vm_init_sp (m_vmmaps (lmcommit_post mo addr len off)) = vm_init_sp h.
Proof. rewrite commit_post_vmmaps. reflexivity. Qed.
#[using="A n h Hmc mo1 W"] Lemma commit_post_fds : m_fds (lmcommit_post mo addr len off) = m_fds mo /\ m_fs (lmcommit_post mo addr len off) = m_fs mo.
Proof. rewrite lmcommit_post_eq. split; reflexivity. Qed.

#[using="Type"] Lemma vm_backing_used_wvb_app : forall Wl m,
  vm_backing_used (with_vm_backing (m_vm_lazy m) (Wl ++ m_vm_materialized m) m)
  = vm_backing_used m + Z.of_nat (length Wl) * page_size.
Proof.
  intros Wl m. unfold vm_backing_used.
  rewrite m_vmmaps_with_vm_backing, m_vm_lazy_with_vm_backing, m_vm_materialized_with_vm_backing.
  rewrite length_app, Nat2Z.inj_add. lia.
Qed.

#[using="A h Hmc mo1"] Lemma commit_post_used : vmwf mo -> 0 < bv_unsigned n ->
  vm_backing_used (lmcommit_post mo addr len off)
  <= vm_backing_used mo + bv_unsigned n + Z.of_nat (length W) * page_size.
Proof.
  intros [Hwf Hs] Hn. rewrite lmcommit_post_eq, vm_backing_used_wvb_app.
  pose proof (backing_forget_commit_le mo (mmap_fixed_rw_next h A n) (bv_unsigned A) (bv_unsigned A + bv_unsigned n)
                Hwf ltac:(lia) eq_refl eq_refl) as Hle. fold mo1 in Hle.
  destruct (map_contains_inside _ _ _ Hmc) as (p & Hin & Hp).
  pose proof (overlap_sum_inside_le _ _ _ p Hs Hin Hp ltac:(lia)) as Ho. unfold h in *. lia.
Qed.
#[using="Hmc mo1 W"] Lemma commit_post_cuts : vmwf mo -> forall x,
  covered (vm_noaccess (m_vmmaps (lmcommit_post mo addr len off)) ++ m_vm_lazy (lmcommit_post mo addr len off)) x
  = covered (vm_noaccess h ++ m_vm_lazy mo) x && negb (in_rng (bv_unsigned A) (bv_unsigned A + bv_unsigned n) x).
Proof.
  intros [(_ & Wn & Wl & _) _] x. pose proof (bv_unsigned_in_range 64 n) as Rn.
  rewrite lmcommit_post_eq. rewrite m_vmmaps_with_vm_backing, m_vm_lazy_with_vm_backing.
  unfold mo1. rewrite m_vmmaps_vm_forget_range, m_vm_lazy_vm_forget_range, m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps.
  cbn [mmap_fixed_rw_next vm_noaccess]. rewrite !covered_app.
  rewrite (proj2 (proj2 (maps_subtract_sem _ (bv_unsigned A) (bv_unsigned A + bv_unsigned n) Wn ltac:(lia)))).
  rewrite (proj2 (proj2 (maps_subtract_sem _ (bv_unsigned A) (bv_unsigned A + bv_unsigned n) Wl ltac:(lia)))).
  unfold h. destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng (bv_unsigned A) (bv_unsigned A + bv_unsigned n) x); reflexivity.
Qed.
End Commit.

Lemma win_pages_bound : forall off a nZ, 0 <= off -> 0 <= a -> 0 <= nZ ->
  Z.of_nat (length (pages_of (shw_lo off a) (shw_hi off a nZ))) * page_size <= nZ / 8 + 2 * page_size.
Proof.
  intros off a nZ Ho Ha Hn. destruct (NodesLZMm.shw_bounds off a nZ Ho Ha Hn) as (W1 & W2 & W3 & W4 & W5 & _).
  rewrite (LZPages.pages_of_length _ _ W1 W2 W4). exact W5.
Qed.

Lemma lenW_unsigned : forall len, 0 <= lenZ len < 2^64 -> bv_unsigned (lenW len) = lenZ len.
Proof. intros len H. unfold lenW. apply fg_lit. exact H. Qed.

Lemma addr_unsigned : forall addr, 0 <= addr < 2^64 -> bv_unsigned (Z_to_bv 64 addr) = addr.
Proof. intros. apply fg_lit. assumption. Qed.

Lemma commit_post_vmwf : forall mo addr len off,
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (lenW len) = true ->
  vmwf mo -> vmwf (lmcommit_post mo addr len off).
Proof.
  intros mo addr len off Hmc [(Wm & Wn & Wl & Wsp) Hs]. split.
  - rewrite (lmcommit_post_eq mo addr len off Hmc).
    pose proof (bv_unsigned_in_range 64 (lenW len)) as Rn.
    split; [| split; [| split]]; cbn.
    + exact Wm.
    + apply maps_subtract_wf; [exact Wn| lia].
    + apply maps_subtract_wf; [exact Wl| lia].
    + exact Wsp.
  - rewrite (commit_post_maps mo addr len off Hmc). exact Hs.
Qed.

Lemma nsafeL_commit : forall mo addr len off,
  vmwf mo -> 0 <= off -> 0 < addr -> 0 < lenZ len -> addr + lenZ len <= 2^47 ->
  addr + lenZ len <= alloc_top (m_vmmaps mo) ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (lenW len) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (lenW len) = true ->
  vm_backing_used mo + lenZ len + (lenZ len / 8 + 2 * page_size) <= vm_limit (m_vmmaps mo) ->
  nsafeL (LMmapCommit addr len off) mo.
Proof.
  intros mo addr len off Hwf Hoff Ha Hn H47 Htop Hrf Hmc Hroom. cbn [nsafeL]. cbv zeta.
  split; [exact Htop|]. split; [exact Hrf|]. split; [exact Hmc|].
  unfold vm_backing_within_limit. apply Z.leb_le. rewrite (commit_post_limit mo addr len off Hmc).
  assert (En : bv_unsigned (lenW len) = lenZ len) by (apply lenW_unsigned; lia).
  pose proof (commit_post_used mo addr len off Hmc Hwf ltac:(lia)) as Hu. rewrite En in Hu.
  assert (Ea : addrZ addr = addr) by (unfold addrZ; apply addr_unsigned; lia). rewrite Ea in Hu.
  pose proof (win_pages_bound off addr (lenZ len) Hoff ltac:(lia) ltac:(lia)) as Hw.
  lia.
Qed.

Lemma region_free_app : forall l1 l2 a n,
  region_free (l1 ++ l2) a n = region_free l1 a n && region_free l2 a n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 a n; [reflexivity|]. cbn [app region_free]. rewrite IH, andb_assoc. reflexivity.
Qed.

Section Anon.
Context {HC : HasCeiling}.
Variables (mo : Model) (len : Z) (avoid : list (Z * Z)).
Let h := m_vmmaps mo.
Let nZ := lenZ len.

Definition place_ok : Prop :=
  forall a : word, mmap_placed mo 0 len MAPF_ANON_PRIVATE a ->
    0x609000 <= bv_unsigned a /\ app_memb (bv_unsigned a) nZ = true /\ bv_unsigned a + nZ <= alloc_ceiling
    /\ avoids_all (bv_unsigned a) nZ avoid = true.

#[using="Type"] Lemma stwf_anon : forall (Q : exc Z -> Model -> Prop),
  lz_room mo nZ (nZ / 8 + 2 * page_size) ->
  vm_gap_available h nZ = true ->
  place_ok ->
  (forall a : word, mmap_placed mo 0 len MAPF_ANON_PRIVATE a -> Q (Ok (bv_unsigned a)) (lmheap_post mo a len SHADOW_OFF)) ->
  stwfL (t_anon len avoid) mo Q.
Proof.
  intros Q Hroom Hgap Hpl HQ. unfold t_anon, enode. cbn [Bridge.stwf]. split; [exact Hroom|]. split.
  - intros code mo' HX. exact HX.
  - intros rsp mo' evs (-> & [(e & He & _) | (a & Hp & E & ->)]).
    + exfalso. fold h nZ in He. rewrite Hgap in He. exact He.
    + split; [reflexivity|].
      destruct (Hpl a Hp) as (P1 & P2 & P3 & P4). pose proof Hp as (Hal & _).
      assert (Er : eff_ret rsp = a) by (change (eff_ret rsp) with (eff_ret (strip rsp)); rewrite E; reflexivity).
      assert (D : dec_anon len avoid rsp = Some (bv_unsigned a)).
      { unfold dec_anon. rewrite Er, E, resp_eqb_zeros1. fold nZ.
        replace (bv_unsigned a mod 4096 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hal).
        replace (6328320 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; lia).
        rewrite P2, P4. replace (bv_unsigned a + nZ <=? alloc_ceiling) with true by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
      rewrite D. cbn [Bridge.stwf]. exact (HQ a Hp).
Qed.
End Anon.

Section AnonPost.
Variables (mo : Model) (len off : Z) (a : word).
Let h := m_vmmaps mo.
Let nZ := lenZ len.
Hypothesis Hp : mmap_placed mo 0 len MAPF_ANON_PRIVATE a.
Hypothesis Hn : 0 < nZ.

Let W := pages_of (shw_lo off (bv_unsigned a)) (shw_hi off (bv_unsigned a) nZ).

#[using="Type"] Lemma anon_post_vmmaps : m_vmmaps (lmheap_post mo a len off) = grant_maps h a (lenW len).
Proof. reflexivity. Qed.
#[using="Type"] Lemma anon_post_maps : vm_maps (m_vmmaps (lmheap_post mo a len off)) = (a, lenW len) :: vm_maps h.
Proof. reflexivity. Qed.
#[using="Type"] Lemma anon_post_fds : m_fds (lmheap_post mo a len off) = m_fds mo /\ m_fs (lmheap_post mo a len off) = m_fs mo.
Proof. split; reflexivity. Qed.

#[using="Hp Hn"] Lemma anon_placed_facts :
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h /\
  region_free (vm_reserved h) a (lenW len) = true /\ region_free (vm_maps h) a (lenW len) = true /\
  bv_unsigned (lenW len) = nZ.
Proof.
  destruct Hp as (P1 & P2 & P3 & P4 & P5). cbv zeta in P3, P4, P5.
  change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with (lenZ len) in *.
  pose proof (alloc_top_lt h) as Ht.
  assert (En : bv_unsigned (lenW len) = nZ).
  { apply lenW_unsigned. unfold nZ, h, two_pow_64 in *. lia. }
  change (Z_to_bv 64 (lenZ len)) with (lenW len) in P4. rewrite region_free_app in P4. apply andb_true_iff in P4 as [P4 P4'].
  repeat split; assumption.
Qed.

#[using="h nZ Hp Hn"] Lemma anon_post_vmwf : vmwf mo -> vmwf (lmheap_post mo a len off).
Proof.
  intros [(Wm & Wn & Wl & Wsp) Hs]. destruct anon_placed_facts as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (alloc_top_lt h) as Ht. unfold two_pow_64 in Ht. split.
  - split; [| split; [| split]]; cbn.
    + apply ivs_wf_cons; [| exact Wm]. unfold iv_wf, B, S. cbn [fst snd]. rewrite F6. lia.
    + exact Wn.
    + exact Wl.
    + exact Wsp.
  - rewrite anon_post_maps. apply LZPages.seps_cons_free; assumption.
Qed.

#[using="h Hp Hn"] Lemma anon_post_used : vmwf mo ->
  vm_backing_used (lmheap_post mo a len off) <= vm_backing_used mo + nZ + Z.of_nat (length W) * page_size.
Proof.
  intros Hwf. pose proof (anon_post_vmwf Hwf) as [(Wm' & _) _]. destruct Hwf as [Hwf Hs].
  destruct anon_placed_facts as (_ & _ & _ & _ & _ & F6).
  rewrite (vm_backing_used_sem_maps _ Wm'), (vm_backing_used_sem _ Hwf).
  unfold lmheap_post. rewrite m_vmmaps_with_vm_backing, m_vm_lazy_with_vm_backing, m_vm_materialized_with_vm_backing.
  rewrite m_vmmaps_with_vmmaps. cbn [grant_maps vm_maps vm_noaccess sum_count].
  rewrite length_app, Nat2Z.inj_add.
  pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (B (a, lenW len)) (Z.to_nat (S (a, lenW len)))) as Hc.
  unfold iv_count. unfold S in Hc at 2. cbn [snd] in Hc. rewrite F6, Z2Nat.id in Hc by lia.
  change (pages_of (shw_lo off (bv_unsigned a)) (shw_hi off (bv_unsigned a) (lenZ len))) with W. lia.
Qed.
End AnonPost.

Lemma dec_unmapu_ok : forall addr len rsp, 0 <= len < 2^64 ->
  strip rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, lenW len)] [] [] ->
  dec_unmapu addr len rsp = Some tt.
Proof.
  intros addr len rsp Hl E. unfold dec_unmapu, Decode.dec_munmap.
  destruct rsp as [r ws zs us cs ci]. unfold strip in E. cbn in E. injection E as -> -> -> -> ->.
  unfold lenW, lenZ, Decode.mmap_len. rewrite (fg_lit len Hl).
  replace (bv_unsigned (Z_to_bv 64 0) =? 0) with true by reflexivity. rewrite !bv_eqb_refl. reflexivity.
Qed.

Definition unmap_post (mo : Model) (addr len : Z) : Model :=
  let h := m_vmmaps mo in let A := Z_to_bv 64 addr in let n := lenW len in
  with_mmap_destroyed A n
    (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) A)
       (maps_subtract (vm_noaccess h) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
       (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo.

Lemma stwf_unmap : forall addr len mo (Q : exc unit -> Model -> Prop), 0 <= len < 2^64 ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (lenW len) = true ->
  Q (Ok tt) (unmap_post mo addr len) ->
  stwfL (t_unmap addr len) mo Q.
Proof.
  intros addr len mo Q Hl HS HQ. unfold t_unmap, enode. cbn [Bridge.stwf]. split; [| split].
  - cbn [nsafeL nsafe]. split; [exact HS| exact I].
  - intros code mo' HX. exact HX.
  - intros rsp mo' evs (-> & E & ->). split; [reflexivity|].
    rewrite (dec_unmapu_ok addr len rsp Hl E). cbn [Bridge.stwf]. exact HQ.
Qed.

Lemma iv_count_nonneg : forall P q, 0 <= iv_count P q.
Proof. intros. unfold iv_count. apply zcount_nonneg. Qed.

Lemma sum_count_filter_remove : forall P (f : word * word -> bool) l e,
  In e l -> f e = false -> sum_count P (List.filter f l) + iv_count P e <= sum_count P l.
Proof.
  intros P f l e. induction l as [|q l IH]; intros Hin Hf; [destruct Hin|].
  cbn [List.filter sum_count]. destruct Hin as [->|Hin].
  - rewrite Hf. clear IH. assert (sum_count P (List.filter f l) <= sum_count P l); [| lia].
    induction l as [|r l IH]; cbn [List.filter sum_count]; [lia|]. pose proof (iv_count_nonneg P r). destruct (f r); cbn [sum_count]; lia.
  - specialize (IH Hin Hf). pose proof (iv_count_nonneg P q). destruct (f q); cbn [sum_count]; lia.
Qed.

Lemma sum_count_ext_in : forall P Q l,
  (forall q x, In q l -> B q <= x < B q + S q -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
  intros P Q l. induction l as [|q l IH]; intros H; [reflexivity|]. cbn [sum_count]. f_equal.
  - unfold iv_count. apply zcount_ext. intros x Hx. pose proof (S_range q). rewrite Z2Nat.id in Hx by lia. apply (H q x); [left; reflexivity| exact Hx].
  - apply IH. intros r x Hr Hx. apply (H r x); [right; exact Hr| exact Hx].
Qed.

Definition fully_backed (mo : Model) (e : word * word) : Prop :=
  forall x, B e <= x < B e + S e -> covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x = false.

Section UnmapPost.
Variables (mo : Model) (addr len : Z).
Let h := m_vmmaps mo.
Let A := Z_to_bv 64 addr.
Let n := lenW len.
Hypothesis Hhas : map_has (vm_maps h) A n = true.

#[using="Type"] Lemma unmap_post_maps : vm_maps (m_vmmaps (unmap_post mo addr len)) = map_remove (vm_maps h) A.
Proof. reflexivity. Qed.
#[using="Type"] Lemma unmap_post_reserved : vm_reserved (m_vmmaps (unmap_post mo addr len)) = vm_reserved h.
Proof. reflexivity. Qed.
#[using="Type"] Lemma unmap_post_limit : vm_limit (m_vmmaps (unmap_post mo addr len)) = vm_limit h.
Proof. reflexivity. Qed.
#[using="Type"] Lemma unmap_post_init_sp : vm_init_sp (m_vmmaps (unmap_post mo addr len)) = vm_init_sp h.
Proof. reflexivity. Qed.
#[using="Type"] Lemma unmap_post_fds : m_fds (unmap_post mo addr len) = m_fds mo /\ m_fs (unmap_post mo addr len) = m_fs mo.
Proof. split; reflexivity. Qed.

#[using="h A"] Lemma unmap_post_vmwf : vmwf mo -> vmwf (unmap_post mo addr len).
Proof.
  intros [(Wm & Wn & Wl & Wsp) Hs]. pose proof (bv_unsigned_in_range 64 (lenW len)) as Rn. split.
  - split; [| split; [| split]]; cbn.
    + apply ivs_wf_filter. exact Wm.
    + apply maps_subtract_wf; [exact Wn| lia].
    + apply maps_subtract_wf; [exact Wl| lia].
    + exact Wsp.
  - rewrite unmap_post_maps. unfold map_remove. apply LZPages.seps_filter. exact Hs.
Qed.

#[using="h Hhas"] Lemma unmap_post_used : vmwf mo -> fully_backed mo (A, n) ->
  vm_backing_used (unmap_post mo addr len) + bv_unsigned n <= vm_backing_used mo.
Proof.
  intros Hwf Hfb. pose proof (unmap_post_vmwf Hwf) as [(Wm' & _) _]. destruct Hwf as [Hwf Hs]. pose proof Hwf as (Wm & Wn & Wl & _).
  pose proof (NodesLZMm.map_has_In _ _ _ Hhas) as Hin.
  pose proof (bv_unsigned_in_range 64 n) as Rn.
  set (lo := bv_unsigned A) in *. set (hi := lo + bv_unsigned n) in *.
  rewrite (vm_backing_used_sem_maps _ Wm'), (vm_backing_used_sem _ Hwf).
  unfold unmap_post, with_mmap_destroyed. fold h A n lo hi.
  rewrite m_vmmaps_vm_forget_range, m_vm_lazy_vm_forget_range, m_vm_materialized_vm_forget_range.
  rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, m_vm_materialized_with_vmmaps. cbn [vm_maps vm_noaccess].
  destruct (maps_subtract_sem _ lo hi Wn ltac:(subst hi; lia)) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl ltac:(subst hi; lia)) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized mo)) as Hlen.
  set (P := fun x => negb (covered (vm_noaccess h ++ m_vm_lazy mo) x)).

  assert (E1 : sum_count (fun x => negb (covered (maps_subtract (vm_noaccess h) lo hi ++ maps_subtract (m_vm_lazy mo) lo hi) x)) (map_remove (vm_maps h) A)
               = sum_count P (map_remove (vm_maps h) A)).
  { apply sum_count_ext_in. intros q x Hq Hx. unfold map_remove in Hq. apply filter_In in Hq as [Hq Hne].
    unfold P. rewrite !covered_app, Cn, Cl.
    destruct (LZPages.seps_in_disjoint _ q (A, n) Hs Hq Hin) as [->|D].
    - cbn [fst] in Hne. rewrite bv_eqb_refl in Hne. discriminate.
    - assert (in_rng lo hi x = false).
      { unfold in_rng. apply andb_false_iff. unfold NodesLZ.iv_disjoint, B, S in *. cbn [fst snd] in D. subst lo hi.
        destruct D; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; lia. }
      rewrite H. rewrite !andb_true_r. reflexivity. }
  rewrite E1.
  pose proof (sum_count_filter_remove P (fun p => negb (bv_eqb (fst p) A)) (vm_maps h) (A, n) Hin
                ltac:(cbn [fst]; rewrite bv_eqb_refl; reflexivity)) as Hrm. fold (map_remove (vm_maps h) A) in Hrm.
  assert (Efull : iv_count P (A, n) = bv_unsigned n).
  { unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_true; [apply Z2Nat.id; lia|].
    intros x Hx. rewrite Z2Nat.id in Hx by lia. unfold P, h. rewrite (Hfb x); [reflexivity|]. unfold B, S. cbn [fst snd]. exact Hx. }
  unfold page_size in *. lia.
Qed.
#[using="Type"] Lemma unmap_post_cuts : vmwf mo -> forall x,
  covered (vm_noaccess (m_vmmaps (unmap_post mo addr len)) ++ m_vm_lazy (unmap_post mo addr len)) x
  = covered (vm_noaccess h ++ m_vm_lazy mo) x && negb (in_rng (bv_unsigned A) (bv_unsigned A + bv_unsigned n) x).
Proof.
  intros [(_ & Wn & Wl & _) _] x. pose proof (bv_unsigned_in_range 64 (lenW len)) as Rn.
  unfold unmap_post, with_mmap_destroyed. fold h A n.
  rewrite m_vmmaps_vm_forget_range, m_vm_lazy_vm_forget_range, m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps.
  cbn [vm_noaccess]. rewrite !covered_app.
  rewrite (proj2 (proj2 (maps_subtract_sem _ (bv_unsigned A) (bv_unsigned A + bv_unsigned n) Wn ltac:(unfold n; lia)))).
  rewrite (proj2 (proj2 (maps_subtract_sem _ (bv_unsigned A) (bv_unsigned A + bv_unsigned n) Wl ltac:(unfold n; lia)))).
  unfold h. destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng (bv_unsigned A) (bv_unsigned A + bv_unsigned n) x); reflexivity.
Qed.
End UnmapPost.

Lemma stwf_madv : forall addr len mo (Q : exc unit -> Model -> Prop),
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (lenW len) = true ->
  Q (Ok tt) (madv_post mo (addrZ addr) (addrZ addr + lenZ len)) ->
  stwfL (t_madv addr len) mo Q.
Proof.
  intros addr len mo Q HS HQ. unfold t_madv, enode. cbn [Bridge.stwf]. split; [exact HS|]. split.
  - intros code mo' HX. exact HX.
  - intros rsp mo' evs (-> & E & ->). split; [reflexivity|].
    rewrite (dec_madv_ok addr len rsp E). cbn [Bridge.stwf]. exact HQ.
Qed.

Lemma madv_post_same : forall mo lo hi,
  m_vmmaps (madv_post mo lo hi) = m_vmmaps mo /\ m_vm_lazy (madv_post mo lo hi) = m_vm_lazy mo /\
  m_fds (madv_post mo lo hi) = m_fds mo /\ m_fs (madv_post mo lo hi) = m_fs mo /\
  m_vm_materialized (madv_post mo lo hi) = cut_pages lo hi (m_vm_materialized mo).
Proof. intros. repeat split; reflexivity. Qed.

Lemma madv_post_vmwf : forall mo lo hi, vmwf mo -> vmwf (madv_post mo lo hi).
Proof. intros mo lo hi H. exact H. Qed.
