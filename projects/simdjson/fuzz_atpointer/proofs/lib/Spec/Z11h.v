(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Zg2 MState ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Malloc Prog KInv KStep Relim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition KLIM : Z := 43 * 2 ^ 25.
Definition SMALLREQ : Z := 2 ^ 24.

Definition GK (h : VmMaps) : Prop :=
  (forall e, In e (vm_maps h) -> PGSZ <= bv_unsigned (snd e))
  /\ KLIM + SMALLREQ <= vm_limit h
  /\ bv_unsigned (vm_start_brk h) <= 2 ^ 33.

Lemma GK_ext : forall h h',
  GK h -> incl (vm_maps h') (vm_maps h) -> vm_limit h' = vm_limit h -> vm_start_brk h' = vm_start_brk h -> GK h'.
Proof.
  intros h h' (G1 & G2 & G3) Hi E1 E2. split; [|split; [rewrite E1; exact G2| rewrite E2; exact G3]].
  intros e He. apply G1. apply Hi. exact He.
Qed.

Lemma GK_cons : forall h h' e,
  GK h -> vm_maps h' = e :: vm_maps h -> PGSZ <= bv_unsigned (snd e) ->
  vm_limit h' = vm_limit h -> vm_start_brk h' = vm_start_brk h -> GK h'.
Proof.
  intros h h' e (G1 & G2 & G3) Em He E1 E2. split; [|split; [rewrite E1; exact G2| rewrite E2; exact G3]].
  intros x Hx. rewrite Em in Hx. destruct Hx as [<-|Hx]; [exact He| exact (G1 x Hx)].
Qed.

Lemma u64_lit' : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz.
Qed.

Lemma region_free_false_ex : forall maps lo n,
  region_free maps lo n = false ->
  exists b s, In (b, s) maps /\ iv_overlap lo n b s = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. apply andb_false_iff in H as [H|H].
  - apply negb_false_iff in H. exists b, s. split; [now left|exact H].
  - destruct (IH lo n H) as (b' & s' & Hin & Hov). exists b', s'. split; [now right|exact Hov].
Qed.

Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
  end.

Lemma gap_weight_nonneg : forall nZ l, 0 <= nZ -> 0 <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.

Definition live_at (c : Z) (p : word * word) : bool :=
  c <? bv_unsigned (fst p) + bv_unsigned (snd p).

Lemma gap_weight_filter_le : forall nZ f l, 0 <= nZ ->
  gap_weight nZ (List.filter f l) <= gap_weight nZ l.
Proof.
  induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
  pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
  destruct (f (b, s)); cbn; lia.
Qed.

Lemma live_weight_step : forall nZ l c c' b s,
  0 <= nZ -> c <= c' ->
  In (b, s) l -> live_at c (b, s) = true -> live_at c' (b, s) = false ->
  gap_weight nZ (List.filter (live_at c') l) + (bv_unsigned s + nZ + 4095)
  <= gap_weight nZ (List.filter (live_at c) l)
  /\ (length (List.filter (live_at c') l) < length (List.filter (live_at c) l))%nat.
Proof.
  intros nZ l c c' b s HnZ Hcc'.
  induction l as [|[b0 s0] l IH]; intros Hin Hlive Hdead; [contradiction|].
  assert (Hmono : forall p, live_at c' p = true -> live_at c p = true).
  { intros [x y] H. unfold live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
  assert (Hle : gap_weight nZ (List.filter (live_at c') l) <= gap_weight nZ (List.filter (live_at c) l)
                /\ (length (List.filter (live_at c') l) <= length (List.filter (live_at c) l))%nat).
  { clear IH Hin. induction l as [|[x y] l IHl]; cbn; [split; [lia|constructor]|].
    pose proof (bv_unsigned_in_range 64 y).
    destruct (live_at c' (x, y)) eqn:E'.
    - rewrite (Hmono _ E'). cbn. destruct IHl; split; [lia|]. apply le_n_S. assumption.
    - destruct (live_at c (x, y)); cbn; destruct IHl; split; try lia. }
  destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. cbn. rewrite Hlive, Hdead. cbn.
    destruct Hle as [Hw Hl]. split; [lia|]. apply Nat.lt_succ_r in Hl. exact Hl.
  - destruct (IH Hin Hlive Hdead) as [Hw Hl]. cbn.
    pose proof (bv_unsigned_in_range 64 s0).
    destruct (live_at c' (b0, s0)) eqn:E'.
    + rewrite (Hmono _ E'). cbn. split; [lia|]. apply Nat.succ_lt_mono in Hl. exact Hl.
    + destruct (live_at c (b0, s0)); cbn; split; lia.
Qed.

Lemma vm_round_up_aligned : forall z, (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma vm_round_up_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

Lemma round_up_le_4095 : forall z, 0 <= z -> page_round_up_Z z <= z + 4095.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.mul_div_le (z + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Section Gap.
  Variable L : list (word * word).
  Variables nZ F CEIL : Z.
  Hypothesis HnZ : 0 <= nZ.
  Hypothesis HF : 0 < F.
  Hypothesis HCEIL : CEIL < 2 ^ 64.

  Definition scan_inv (c : Z) : Prop :=
    c mod page_size = 0 /\ F <= c
    /\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= CEIL.

  Definition gap_at (c : Z) : Prop :=
    c mod page_size = 0 /\ F <= c /\ c + nZ <= CEIL
    /\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.

  Lemma scan_ok_or_step : forall c, scan_inv c ->
    gap_at c
    \/ exists c', scan_inv c'
         /\ (length (List.filter (live_at c') L) < length (List.filter (live_at c) L))%nat.
  Proof.
    intros c (Hal & Hfl & Hw).
    pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
    assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply u64_lit'; lia).
    assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit'; lia).
    destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
    - left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
    - right.
      destruct (region_free_false_ex _ _ _ Hfree) as (b & s & Hin & Hov).
      unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
      apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
      set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
      pose proof (bv_unsigned_in_range 64 b) as RB. pose proof (bv_unsigned_in_range 64 s) as RS.
      set (c' := page_round_up_Z (B + S)).
      pose proof (vm_round_up_ge (B + S)) as Hge.
      assert (Hle : c' <= B + S + 4095) by (apply round_up_le_4095; lia).
      assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
      assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
      destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
      exists c'. split; [|exact Hlen].
      split; [apply vm_round_up_aligned|].
      split; lia.
  Qed.

  Lemma scan : forall k c, (length (List.filter (live_at c) L) <= k)%nat -> scan_inv c ->
    exists g, gap_at g.
  Proof.
    induction k as [|k IH]; intros c Hk Hinv.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia].
      exists c. exact Hok.
    - destruct (scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)].
      + exists c. exact Hok.
      + apply (IH c'); [lia|exact Hinv'].
  Qed.

  Theorem gap_exists :
    F mod page_size = 0 -> F + nZ + gap_weight nZ L <= CEIL -> exists g, gap_at g.
  Proof.
    intros HFal Hslack.
    assert (Hinv : scan_inv F).
    { split; [exact HFal|]. split; [lia|].
      pose proof (gap_weight_filter_le nZ (live_at F) L HnZ). lia. }
    exact (scan _ F (le_n _) Hinv).
  Qed.
End Gap.

Lemma gap_weight_sizes : forall nZ l,
  gap_weight nZ l = live_bytes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
  intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.

Lemma count_le_live : forall l, (forall e, In e l -> PGSZ <= bv_unsigned (snd e)) ->
  PGSZ * Z.of_nat (length l) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros H; cbn -[Z.of_nat Z.mul]; [lia|].
  rewrite Nat2Z.inj_succ. pose proof (H (b, s) (or_introl eq_refl)) as Hs. cbn in Hs.
  specialize (IH ltac:(intros e He; apply H; right; exact He)). unfold PGSZ in *. lia.
Qed.

Lemma four_xy_le_sq : forall x y, 0 <= x -> 0 <= y -> 4 * (x * y) <= (x + y) * (x + y).
Proof. intros x y Hx Hy. pose proof (Z.square_nonneg (x - y)). nia. Qed.

Lemma region_free_app_iff : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[a s] l1 IH]; intros l2 lo n; cbn; [reflexivity|].
  rewrite IH. destruct (negb (iv_overlap lo n a s)); reflexivity.
Qed.

Lemma gk_gap : forall {CE : Ceiling} L pbrk mo nZ,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < nZ -> nZ mod page_size = 0 ->
  (nZ <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + nZ <= KLIM) ->
  vm_gap_available (m_vmmaps mo) nZ = true.
Proof.
  intros CE L pbrk mo nZ HK (G1 & G2 & G3) Hlive HnZ HnAl Hreq.
  set (h := m_vmmaps mo) in *.
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). fold h in S1, S2, S3, S4.
  pose proof (kl_top _ _ _ HK) as Htop. fold h in Htop.
  set (F := bv_unsigned (vm_start_brk h)) in *.
  pose proof (count_le_live (vm_maps h) G1) as Hcnt.
  unfold vm_live_bytes in Hlive, Hreq.
  set (N := Z.of_nat (length (vm_maps h))) in *.
  set (LV := live_bytes (vm_maps h)) in *.
  pose proof (live_bytes_nonneg (vm_maps h)) as HLV. fold LV in HLV.
  ceil_bounds.

  assert (HW : F + nZ + gap_weight nZ (vm_maps h) <= alloc_top h).
  { rewrite gap_weight_sizes. fold N LV. rewrite Htop.
    assert (HNn : 0 <= N) by (unfold N; lia).
    unfold PGSZ, KLIM, SMALLREQ in *.
    rewrite Z.mul_add_distr_l.
    assert (HN4 : N * 4095 <= LV) by lia.
    destruct Hreq as [Hs|Hb].
    -
      assert (HN : N <= 2^19) by lia.
      assert (HP : N * nZ <= 2^19 * 2^24) by (apply Z.mul_le_mono_nonneg; lia).
      lia.
    -
      assert (E1 : (4096 * N) * nZ <= LV * nZ) by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite <- Z.mul_assoc in E1.
      pose proof (four_xy_le_sq LV nZ HLV ltac:(lia)) as E2.
      assert (E3 : (LV + nZ) * (LV + nZ) <= (43 * 2^25) * (43 * 2^25)) by (apply Z.mul_le_mono_nonneg; lia).
      set (P := N * nZ) in *. set (Q := LV * nZ) in *. set (SQ := (LV + nZ) * (LV + nZ)) in *.
      lia. }
  destruct (gap_exists (vm_maps h) nZ F (alloc_top h) ltac:(lia) ltac:(unfold PGSZ in *; lia)
              ltac:(rewrite Htop; lia) ltac:(rewrite page_size_eq; exact S2) HW)
    as (g & Hgal & HgF & Hgtop & Hgfree).

  apply (proj2 (vm_gap_available_iff h nZ)). exists (Z_to_bv 64 g).
  split; [|split; [|split]].
  - rewrite u64_lit' by lia. exact Hgal.
  - rewrite u64_lit' by lia. lia.
  - rewrite u64_lit' by lia. exact Hgtop.
  - rewrite region_free_app_iff, Hgfree, Bool.andb_true_r.
    apply region_free_intro. intros a sz Hin.
    pose proof (kl_resv_top _ _ _ HK (a, sz) Hin) as Hr. fold h F in Hr. unfold ehi in Hr. cbn [fst snd] in Hr.
    unfold iv_overlap. rewrite u64_lit' by lia.
    apply andb_false_iff. left. apply Z.ltb_ge. lia.
Qed.

Lemma gk_budget : forall mo nZ,
  vm_clean mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  (nZ <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + nZ <= KLIM) ->
  vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof.
  intros mo nZ Hc (_ & G2 & _) Hl Hreq. pose proof (vm_backing_used_le_live mo Hc).
  unfold KLIM, SMALLREQ in *. lia.
Qed.

Lemma uf_anon_gates : forall len, 0 < len < 2^64 ->
  mmap_off_aligned_b (Z_to_bv 64 0) = true /\ mmap_anon_b (Z_to_bv 64 MAPF) = true
  /\ w_is0 (Z_to_bv 64 len) = false
  /\ mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0) = true
  /\ mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0) = true.
Proof.
  intros len Hl. rewrite w_is0_lit by lia.
  assert (Hz : (len =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hz. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); reflexivity.
Qed.

Lemma uf_if_ok : forall (A : Type) (b : bool) (x y z : A),
  (if b then x else y) = z -> y <> z -> b = true.
Proof. intros A [|] x y z H Hn; [reflexivity|]. exfalso. exact (Hn H). Qed.

Lemma uf_anon_ok_top : forall len prot eff mo mo' evs,
  0 < len -> mmap_len len < 2^64 -> prot = PROT_NONE \/ prot = PROT_RW ->
  check_mmap (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 MAPF)
             (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo = CheckOk mo' evs ->
  errno_ret_in mmap_errnos (eff_ret eff) = false ->
  bv_unsigned (eff_ret eff) + mmap_len len <= alloc_top (m_vmmaps mo).
Proof.
  intros len prot eff mo mo' evs Hlen Hlen2 Hprot H Hr.
  pose proof (mmap_len_ge len Hlen) as Hb.
  destruct (uf_anon_gates len ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G6).
  unfold check_mmap in H. rewrite G1, G2, G3 in H.
  destruct eff as [r ws zs us cs ci]. cbn [eff_ret] in Hr |- *. unfold mmap_len.
  destruct Hprot as [Ep | Ep]; subst prot; [rewrite G4, G5 in H | rewrite G6 in H];
    cbv beta iota zeta delta [negb] in H; rewrite unsigned_lit in H by lia;
    destruct ws, zs, us, cs, ci; try discriminate H;
    cbv beta iota in H; rewrite Hr in H; cbv beta iota in H;
    apply uf_if_ok in H; try discriminate;
    rewrite !andb_true_iff in H; apply Z.leb_le; tauto.
Qed.

Lemma nstep_mmap_anon_noerr : forall {CE : Ceiling} len prot mo rsp mo' evs,
  0 < len -> mmap_len len < 2^64 -> prot = PROT_NONE \/ prot = PROT_RW ->
  (if prot =? PROT_NONE then mmap_reserve_refusable mo (mmap_len len)
   else mmap_grant_refusable (Z_to_bv 64 MAPF) mo (mmap_len len)) = false ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros CE len prot mo rsp mo' evs Hlen Hlen2 Hprot _ Hst.
  pose proof (nstep_mmap_nonrefusal 0 len prot MAPF mo rsp mo' evs eq_refl Hst) as Hnr.
  pose proof (nstep_mmap_check 0 len prot MAPF mo rsp mo' evs eq_refl Hst) as Hck.
  pose proof (uf_anon_ok_top len prot rsp mo mo' evs Hlen Hlen2 Hprot Hck Hnr) as Htop.
  pose proof (mmap_len_ge len Hlen) as Hb. pose proof (alloc_top_room (m_vmmaps mo)) as Hroom.
  apply errno_of_small. unfold stack_max_size, two_pow_64 in Hroom. lia.
Qed.

Lemma uf_lnn_self : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

Lemma unforced_mmap_anon : forall {CE : Ceiling} len prot mo,
  0 < len -> mmap_len len < 2^64 -> prot = PROT_NONE \/ prot = PROT_RW ->
  (if prot =? PROT_NONE then mmap_reserve_refusable mo (mmap_len len)
   else mmap_grant_refusable (Z_to_bv 64 MAPF) mo (mmap_len len)) = false ->
  unforced (NMmap 0 len prot MAPF) mo.
Proof.
  intros CE len prot mo Hlen Hn64 Hprot Href Hkp.
  pose proof (mmap_len_ge len Hlen) as Hb.
  destruct (uf_anon_gates len ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G6).
  assert (Hg : vm_gap_available (m_vmmaps mo) (mmap_len len) = true).
  { destruct Hprot as [Ep | Ep]; subst prot.
    - exact (proj1 (mmap_reserve_refusable_false_iff mo (mmap_len len)) Href).
    - exact (proj2 (proj1 (mmap_grant_refusable_false_iff (Z_to_bv 64 MAPF) mo (mmap_len len)) Href)). }
  apply vm_gap_available_iff in Hg as (a & Hal & Hpos & Htop & Hfree).
  pose proof (ret_in_errnos_ENOMEM_aligned a Hal : errno_ret_in mmap_errnos a = false) as Hna.
  unfold mmap_len in Htop, Hfree. apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  destruct Hprot as [Ep | Ep]; subst prot.
  - exists (mkEffectU a [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] []). do 2 eexists.
    apply nstep_mmap_iff; [reflexivity|]. split; [|exact Hna].
    unfold check_mmap. rewrite G1, G2, G3, G4, G5. cbv beta iota zeta delta [negb].
    rewrite unsigned_lit by lia. rewrite Hna, Hal, Hpos, Htop, Hfree, uf_lnn_self. reflexivity.
  - assert (Hbk : mmap_noreserve_backed_ok (Z_to_bv 64 MAPF) mo (page_round_up_Z len) = true)
      by exact (proj1 (proj1 (mmap_grant_refusable_false_iff (Z_to_bv 64 MAPF) mo (mmap_len len)) Href)).
    exists (mkEffectU a [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [] []). do 2 eexists.
    apply nstep_mmap_iff; [reflexivity|]. split; [|exact Hna].
    unfold check_mmap. rewrite G1, G2, G3, G6. cbv beta iota zeta delta [negb].
    rewrite unsigned_lit by lia. rewrite Hna, Hal, Hpos, Htop, Hfree, Hbk, uf_lnn_self. reflexivity.
Qed.

Lemma gk_refusable_false : forall {CE : Ceiling} L pbrk mo len prot,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < len -> prot = PROT_NONE \/ prot = PROT_RW ->
  (mmap_len len <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + mmap_len len <= KLIM) ->
  (if prot =? PROT_NONE then mmap_reserve_refusable mo (mmap_len len)
   else mmap_grant_refusable (Z_to_bv 64 MAPF) mo (mmap_len len)) = false.
Proof.
  intros CE L pbrk mo len prot HK HG Hl Hlen Hprot Hreq.
  pose proof (mmap_len_ge len Hlen) as Hb. pose proof (mmap_len_aligned len) as Hal.
  assert (Hgap : vm_gap_available (m_vmmaps mo) (mmap_len len) = true).
  { exact (gk_gap L pbrk mo (mmap_len len) HK HG Hl ltac:(lia) ltac:(rewrite page_size_eq; exact Hal) Hreq). }
  destruct Hprot as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb].
  - unfold mmap_reserve_refusable. rewrite Hgap. reflexivity.
  - unfold mmap_grant_refusable. rewrite Hgap, Bool.orb_false_r.
    unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbn iota.
    rewrite (proj2 (Z.leb_le _ _)); [reflexivity|].
    apply gk_budget; [exact (minv_clean _ (kl_minv _ _ _ HK))| exact HG| exact Hl| exact Hreq].
Qed.

Lemma gk_mmap_noerr : forall {CE : Ceiling} L pbrk mo len prot rsp mo' evs,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < len < 2^63 -> prot = PROT_NONE \/ prot = PROT_RW ->
  (mmap_len len <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + mmap_len len <= KLIM) ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros CE L pbrk mo len prot rsp mo' evs HK HG Hl Hlen Hprot Hreq Hst.
  pose proof (mmap_len_ge len ltac:(lia)) as Hb.
  apply (nstep_mmap_anon_noerr len prot mo rsp mo' evs ltac:(lia) ltac:(lia) Hprot); [|exact Hst].
  exact (gk_refusable_false L pbrk mo len prot HK HG Hl ltac:(lia) Hprot Hreq).
Qed.

Lemma gk_mmap_unforced : forall {CE : Ceiling} L pbrk mo len prot,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < len < 2^63 -> prot = PROT_NONE \/ prot = PROT_RW ->
  (mmap_len len <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + mmap_len len <= KLIM) ->
  unforced (NMmap 0 len prot MAPF) mo.
Proof.
  intros CE L pbrk mo len prot HK HG Hl Hlen Hprot Hreq.
  pose proof (gk_refusable_false L pbrk mo len prot HK HG Hl ltac:(lia) Hprot Hreq) as Hnr.
  pose proof (mmap_len_ge len ltac:(lia)) as Hb.
  exact (unforced_mmap_anon len prot mo ltac:(lia) ltac:(lia) Hprot Hnr).
Qed.

Lemma mprotect_page_rw_eq : forall addr eff m,
  0 <= addr -> addr + PGSZ < 2^64 -> addr mod PGSZ = 0 ->
  check_mprotect (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) (Z_to_bv 64 PROT_RW) eff m =
  if map_contains (vm_noaccess (m_vmmaps m)) (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ)
     && map_contains (vm_maps (m_vmmaps m)) (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) then
    match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mprotect_errnos r then match zs with [] => CheckOk m [] | _ => CheckReject end
        else if mprotect_budget_ok m (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) && w_is0 r
                && listNN_eqb zs [(Z_to_bv 64 addr, Z_to_bv 64 PGSZ)]
        then CheckOk (mprotect_model_next m (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ)) []
        else CheckReject
    | _ => CheckReject
    end
  else if map_contains (vm_maps (m_vmmaps m)) (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ)
          && region_free (vm_noaccess (m_vmmaps m)) (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) then
    match eff with
    | mkEffectU r [] [] [] [] [] => if w_is0 r then CheckOk m [] else CheckReject
    | _ => CheckReject
    end
  else CheckUnmodeled.
Proof.
  intros addr eff m H0 H1 Hal. unfold check_mprotect.
  rewrite (u64_lit' addr) by (unfold PGSZ in H1; lia).
  change page_size with PGSZ. rewrite Hal.
  rewrite (proj2 (Z.leb_gt two_pow_64 (addr + page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))))).
  - reflexivity.
  - change (page_round_up_Z (bv_unsigned (Z_to_bv 64 PGSZ))) with PGSZ. unfold two_pow_64. lia.
Qed.

Lemma nstep_mprotect_noerr : forall {CE : Ceiling} addr mo rsp mo' evs,
  0 <= addr -> addr + PGSZ < 2^64 -> addr mod PGSZ = 0 ->
  mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) = true ->
  nstep (NMprotect addr PGSZ PROT_RW) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros CE addr mo rsp mo' evs Ha0 Ha1 Hal _ Hst.
  destruct (proj1 (nstep_mprotect_iff _ _ _ _ _ _ _) Hst) as [Hck Hnr].
  rewrite mprotect_page_rw_eq in Hck by assumption.
  destruct rsp as [r ws zs us cs ci]. cbn [eff_ret] in *.
  destruct (w_is0 r) eqn:Ez.
  - apply errno_of_small. unfold w_is0 in Ez. apply bv_eqb_eq in Ez. rewrite Ez, u64_lit'; lia.
  - exfalso. change (ret_in_errnos mprotect_errnos r) with (errno_ret_in mprotect_errnos r) in Hnr.
    destruct (map_contains _ _ _ && map_contains _ _ _); [|destruct (map_contains _ _ _ && region_free _ _ _)];
      destruct ws, zs, us, cs, ci; cbv beta iota in Hck; try discriminate;
      rewrite ?Hnr, ?Ez, ?andb_false_r, ?andb_false_l in Hck; cbv beta iota in Hck; discriminate.
Qed.

Lemma unforced_mprotect : forall {CE : Ceiling} addr mo,
  0 <= addr -> addr + PGSZ < 2^64 -> addr mod PGSZ = 0 ->
  map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) = true ->
  mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) = true ->
  unforced (NMprotect addr PGSZ PROT_RW) mo.
Proof.
  intros CE addr mo Ha0 Ha1 Hal Hcn Hcm Hbud. hnf.
  assert (Hl : listNN_eqb [(Z_to_bv 64 addr, Z_to_bv 64 PGSZ)] [(Z_to_bv 64 addr, Z_to_bv 64 PGSZ)] = true)
    by (apply listNN_eqb_eq; reflexivity).
  exists (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 PGSZ)]),
    (mprotect_model_next mo (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ)), [].
  apply (proj2 (nstep_mprotect_iff _ _ _ _ _ _ _)). split; [|reflexivity].
  rewrite mprotect_page_rw_eq by assumption. rewrite Hcn, Hcm, Hbud.
  cbv beta iota delta [andb]. rewrite Hl. reflexivity.
Qed.

Lemma gk_mprotect_budget : forall mo a n,
  vm_clean mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  mprotect_budget_ok mo a n = true.
Proof.
  intros mo a n Hc (_ & G2 & _) Hl. unfold mprotect_budget_ok, vm_backing_within_limit.
  apply Z.leb_le.
  pose proof (vm_backing_used_le_live (mprotect_model_next mo a n) (vm_clean_mprotect_model_next mo a n Hc)) as H.
  assert (E : vm_live_bytes (m_vmmaps (mprotect_model_next mo a n)) = vm_live_bytes (m_vmmaps mo)) by reflexivity.
  assert (E2 : vm_limit (m_vmmaps (mprotect_model_next mo a n)) = vm_limit (m_vmmaps mo)) by reflexivity.
  rewrite E2. unfold KLIM, SMALLREQ in *. lia.
Qed.
