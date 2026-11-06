(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import RelSpec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Ceiling.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Section CEIL.
Context {CLG : ceiling}.

Definition ceil_ok (h : VmMaps) : Prop := (alloc_ceiling <= alloc_top h < alloc_ceiling + 4096)%Z.

Lemma ceil_page_le : forall h x, ceil_ok h -> (x mod page_size = 0)%Z -> (x <= alloc_top h)%Z -> (x <= alloc_ceiling)%Z.
Proof.
  intros h x Hc Hx Hle. unfold ceil_ok in Hc. unfold page_size in Hx. pose proof alloc_ceiling_pg as Hpg.
  assert (x < alloc_ceiling + 4096)%Z by lia.
  destruct (Z_le_gt_dec x alloc_ceiling) as [L|G]; [exact L|]. exfalso.
  assert (E1 : (x = 4096 * (x / 4096))%Z) by (pose proof (Z.div_mod x 4096); lia).
  assert (E2 : (alloc_ceiling = 4096 * (alloc_ceiling / 4096))%Z) by (pose proof (Z.div_mod alloc_ceiling 4096); lia).
  nia.
Qed.

Lemma ceil_ok_same_sp : forall h h', vm_init_sp h' = vm_init_sp h -> ceil_ok h -> ceil_ok h'.
Proof. intros h h' E Hc. unfold ceil_ok, alloc_top in *. rewrite E. exact Hc. Qed.

Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
  /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof.
  intros mo rsp mo' evs H.
  apply nstep_brk_inv in H as (r & E1 & _ & -> & -> & ->). split; [reflexivity|].
  unfold brk_r_ok in E1. change (w_is0 (Z_to_bv 64 0)) with true in E1. cbn [orb] in E1. apply bv_eqb_eq in E1. subst r.
  assert (Hzs : brk_zeros (Z_to_bv 64 0) (vm_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) = []).
  { unfold brk_zeros, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. reflexivity. }
  assert (Hus : brk_unmaps (vm_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) = []).
  { unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _)%Z; reflexivity. }
  rewrite Hzs, Hus. split; [unfold dec_brk0; cbn [eff_copies eff_copyins]; reflexivity|].
  split; [vm_only_done|]. rewrite m_vmmaps_with_brk_next. reflexivity.
Qed.

Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => vm_brk (m_vmmaps mo') = vm_brk h
  | BrkGrown => vm_brk (m_vmmaps mo') = Z_to_bv 64 req
  end.
Proof.
  intros req mo rsp mo' evs h Hb Hsb Hreq H.
  apply nstep_brk_inv in H as (r & E1 & _ & -> & -> & ->). split; [reflexivity|]. split; [vm_only_done|].
  fold h in E1 |- *.
  unfold brk_r_ok in E1. rewrite w_is0_lit in E1 by lia.
  replace (req =? 0)%Z with false in E1 by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in E1. rewrite unsigned_lit in E1 by lia. fold h in E1.
  replace (req <? bv_unsigned (vm_start_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  replace (req <? bv_unsigned (vm_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  cbn [orb] in E1. apply andb_prop in E1 as [E1 _].
  assert (Hr : r = Z_to_bv 64 req \/ r = vm_brk h).
  { apply orb_prop in E1 as [E1|E1]; apply bv_eqb_eq in E1; auto. }
  assert (Hus : brk_unmaps r (vm_brk h) = []).
  { unfold brk_unmaps, brk_page_range.
    assert (Hle : (page_round_up_Z (bv_unsigned (vm_brk h)) <= page_round_up_Z (bv_unsigned r))%Z).
    { apply page_round_up_Z_mono. destruct Hr as [-> | ->]; [rewrite unsigned_lit by lia|]; lia. }
    replace (page_round_up_Z (bv_unsigned r) <? page_round_up_Z (bv_unsigned (vm_brk h)))%Z with false
      by (symmetry; apply Z.ltb_ge; lia).
    destruct (0 <? _)%Z; reflexivity. }
  rewrite Hus.
  destruct (Z.eq_dec req (bv_unsigned (vm_brk h))) as [Ereq | Hne].
  -
    assert (Hr' : r = vm_brk h). { destruct Hr as [-> | ->]; [subst req; apply Z_to_bv_bv_unsigned| reflexivity]. }
    subst r. exists BrkSame. split; [|rewrite m_vmmaps_with_brk_next; reflexivity].
    unfold dec_brk; cbn [eff_copies eff_copyins]. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
  - destruct Hr as [-> | ->].
    + exists BrkGrown. split; [|rewrite m_vmmaps_with_brk_next; reflexivity].
      unfold dec_brk; cbn [eff_copies eff_copyins]. rewrite unsigned_lit by lia.
      replace (req =? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [andb]. rewrite Z.eqb_refl.
      unfold brk_zeros, brk_is_grow. rewrite w_is0_lit by lia.
      replace (req =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (0 <? bv_unsigned (vm_brk h))%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite unsigned_lit by lia.
      replace (bv_unsigned (vm_brk h) <? req)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb andb]. unfold brk_page_range, brk_new_pages, zeros_of, wa.
      destruct (_ <? _)%Z; cbn [listNN_eqb]; rewrite ?bv_eqb_refl; reflexivity.
    + exists BrkSame. split; [|rewrite m_vmmaps_with_brk_next; reflexivity].
      unfold dec_brk; cbn [eff_copies eff_copyins]. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
  exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.

Lemma region_free_In : forall maps a n e sz,
  region_free maps a n = true -> In (e, sz) maps ->
  (bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a)%Z.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
  inversion E; subst. unfold iv_overlap in H1.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
  destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma avoids_of_region_free : forall maps a n avoid,
  region_free maps a n = true ->
  Forall (covered maps) avoid ->
  avoids (bv_unsigned a) (bv_unsigned n) avoid = true.
Proof.
  intros maps a n avoid Hrf Hc. unfold avoids. apply forallb_forall. intros [lo hi] Hin.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (e & sz & He & H1 & H2). cbn in H1, H2. cbn [fst snd].
  pose proof (region_free_In _ _ _ _ _ Hrf He) as [H|H].
  - apply orb_true_intro. left. apply Z.leb_le. lia.
  - apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.

Lemma nstep_dec_mmap : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z -> ceil_ok h ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Hceil Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  assert (Hl0 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  apply (nstep_mmap_rw_inv 0 len mo rsp mo' evs Hl0) in H as [-> H]. split; [reflexivity|].
  fold h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H.
  destruct H as [(e & HIn & -> & ->)|(a & (E1 & E2 & E3 & E4 & E5) & -> & ->)].
  -   match type of HIn with In _ (?f ?c) => destruct c end; cbn in HIn; [|destruct HIn]. destruct HIn as [<-|[]]. split; [vm_only_done|].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap; cbn [eff_copies eff_copyins]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - split; [vm_only_done|].
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned a) = true).
    { unfold mmap_addr_ok. assert (E3' : (bv_unsigned a + mmap_len len <= alloc_ceiling)%Z).
      { apply (ceil_page_le h); [exact Hceil| |exact E3]. unfold mmap_len, page_round_up_Z. change page_size with 4096%Z in E1 |- *.
        rewrite Z.add_mod, E1, Z.mod_mul by lia. reflexivity. }
      rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt _ _) E2), (proj2 (Z.leb_le _ _) E3'). cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned a)). split.
    + unfold dec_mmap; cbn [eff_copies eff_copyins]. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|].
      rewrite m_vmmaps_with_mmap_backing. reflexivity.
Qed.

Lemma nstep_dec_mmap_none : forall len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z -> ceil_ok h ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  nstep (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap_none len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h)
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len avoid mo rsp mo' evs h Hlen Hlen2 Hceil Hcov H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  assert (Hl0 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  apply (nstep_mmap_none_inv 0 len mo rsp mo' evs Hl0) in H as [-> H]. split; [reflexivity|].
  fold h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H.
  destruct H as [(e & HIn & -> & ->)|(a & (E1 & E2 & E3 & E4) & -> & ->)].
  -   match type of HIn with In _ (?f ?c) => destruct c end; cbn in HIn; [|destruct HIn]. destruct HIn as [<-|[]]. split; [vm_only_done|].
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap_none; cbn [eff_copies eff_copyins]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - split; [vm_only_done|].
    assert (Hok : mmap_addr_ok len avoid (bv_unsigned a) = true).
    { unfold mmap_addr_ok. assert (E3' : (bv_unsigned a + mmap_len len <= alloc_ceiling)%Z).
      { apply (ceil_page_le h); [exact Hceil| |exact E3]. unfold mmap_len, page_round_up_Z. change page_size with 4096%Z in E1 |- *.
        rewrite Z.add_mod, E1, Z.mod_mul by lia. reflexivity. }
      rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt _ _) E2), (proj2 (Z.leb_le _ _) E3'). cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned a)). split.
    + unfold dec_mmap_none; cbn [eff_copies eff_copyins]. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|].
      rewrite m_vmmaps_with_mmap_backing. reflexivity.
Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->

  (addr mod 4096 = 0)%Z -> (addr + mmap_len len <= TASK_SIZE)%Z -> map_has (vm_maps h) a n = true ->
  nstep (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_munmap addr len rsp = Some x /\
  match x with
  | RgErr e => e = EINVAL /\ mo' = mo
  | RgDone false => mo' = mo /\ map_has (vm_maps h) a n = false
  | RgDone true => map_has (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 Hal Hnw Hhas H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  assert (Hl0 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (Ua : bv_unsigned a = addr) by (subst a; apply unsigned_lit; lia).
  pose proof (nstep_munmap_inv addr len mo rsp mo' evs) as INV. cbv zeta in INV.
  rewrite (unsigned_lit len) in INV by lia. fold (mmap_len len) in INV. fold a n h in INV.
  apply (INV ltac:(rewrite Ua; change page_size with 4096%Z; exact Hal) Hl0 ltac:(rewrite Ua; exact Hnw) Hhas) in H as (-> & -> & ->). clear INV.
  split; [reflexivity|]. split; [vm_only_done|].
  exists (RgDone true). split; [|split; [exact Hhas| rewrite m_vmmaps_with_mmap_destroyed; reflexivity]].
  unfold dec_munmap; cbn [eff_copies eff_copyins]. subst a n. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->

  (addr mod 4096 = 0)%Z -> (addr + mmap_len len < 2^64)%Z ->
  map_contains (vm_noaccess h) a n = true -> map_contains (vm_maps h) a n = true ->
  nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => (e = EINVAL \/ e = ENOMEM) /\ mo' = mo
  | RgDone false => False
  | RgDone true => map_contains (vm_noaccess h) a n = true /\ map_contains (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 Hal Hnw Hcn Hcm H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  assert (Hl0 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (Ua : bv_unsigned a = addr) by (subst a; apply unsigned_lit; lia).
  pose proof (nstep_mprotect_inv addr len (PROT_READ + PROT_WRITE) mo rsp mo' evs) as INV. cbv zeta in INV.
  rewrite (unsigned_lit len) in INV by lia. fold (mmap_len len) in INV. fold a n h in INV.
  apply (INV eq_refl ltac:(rewrite Ua; change page_size with 4096%Z; exact Hal) Hl0 ltac:(rewrite Ua; unfold two_pow_64; lia) eq_refl Hcn Hcm) in H as [-> H]. clear INV.
  split; [reflexivity|].
  destruct H as [(e & HIn & -> & ->)|(Hbud & -> & ->)].
  -   match type of HIn with In _ (?f ?c) => destruct c end; cbn in HIn; [|destruct HIn]. destruct HIn as [<-|[]]. split; [vm_only_done|].
    exists (RgErr ENOMEM). split; [|auto]. unfold dec_mprotect; cbn [eff_copies eff_copyins].
    rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - split; [vm_only_done|].
    exists (RgDone true). split; [| split; [exact Hcn| split; [exact Hcm| rewrite m_vmmaps_mprotect_model_next; reflexivity]]].
    unfold dec_mprotect; cbn [eff_copies eff_copyins]. subst a n. rewrite !bv_eqb_refl. reflexivity.
Qed.

End CEIL.

Ltac ceil_carry :=
  try lazymatch goal with
  | |- ceil_ok _ => eapply ceil_ok_same_sp; [| eassumption];
        first [ reflexivity | assumption | symmetry; assumption
              | eapply vm_only_init_sp; eassumption
              | symmetry; eapply vm_only_init_sp; eassumption ]
  end.
