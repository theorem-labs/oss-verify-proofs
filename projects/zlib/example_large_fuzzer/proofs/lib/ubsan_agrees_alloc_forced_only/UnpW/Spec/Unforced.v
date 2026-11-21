(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Malloc. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog KInv KStep. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Relim.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO.P04 Require Import Mmap Mprotect MmapComplete.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition KLIM : Z := 2 ^ 30.
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

(* a worker TRIAL sem727: lps names that the FO.P04 imports would otherwise shadow. *)
Module LMm := LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Module LPl := LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.

(* a worker TRIAL sem727: RESTATED conclusion. At an anonymous grant answers exactly Linux's
   placement (Checks/Placement.v linux_place_is l.1012), whose search sees two windows only (lps
   linux_place_exists l.867); a free range below alloc_top is no longer enough. The gap is now searched in the
   bottom-up window [task_unmapped_base, alloc_top) (from max start_brk task_unmapped_base), clear of vm_maps
   and of the vDSO pair, so Linux's placement exists for every thp and hint. *)
Lemma gk_gap : forall {CE : Ceiling} L pbrk mo nZ,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < nZ -> nZ mod page_size = 0 ->
  (nZ <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + nZ <= KLIM) ->
  forall thp hint, exists a, LMm.linux_place (m_vmmaps mo) thp hint nZ a.
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
      assert (HN : N <= 2^18) by lia.
      assert (HP : N * nZ <= 2^18 * 2^24) by (apply Z.mul_le_mono_nonneg; lia).
      lia.
    -
      assert (E1 : (4096 * N) * nZ <= LV * nZ) by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite <- Z.mul_assoc in E1.
      pose proof (four_xy_le_sq LV nZ HLV ltac:(lia)) as E2.
      assert (E3 : (LV + nZ) * (LV + nZ) <= 2^30 * 2^30) by (apply Z.mul_le_mono_nonneg; lia).
      set (P := N * nZ) in *. set (Q := LV * nZ) in *. set (SQ := (LV + nZ) * (LV + nZ)) in *.
      lia. }
  (* a worker TRIAL sem727 (finding 1): at vm_reserved also holds the vDSO pair, high in the
     address space (KLV); every other reserved entry ends below start_brk. So the gap is searched clear of
     vm_maps AND the pair; the pair adds at most 20 pages and two slots to the weight. *)
  destruct (kl_v _ _ _ HK) as (_ & (rest & Vres & Vrest) & _).
  set (V := vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) in *.
  assert (HgV : gap_weight nZ V <= 20 * 4096 + 2 * (nZ + 4095)).
  { unfold V, vdso_reserved. destruct (_ <? page_size)%Z; cbn [gap_weight]; [lia|].
    pose proof (vdso_text_pages_pos (m_kernel mo)). pose proof (vdso_text_pages_le (m_kernel mo)).
    unfold vdso_vvar_pages, page_size in *. rewrite !u64_lit' by lia. lia. }
  assert (Happ : forall l1 l2, gap_weight nZ (l1 ++ l2) = gap_weight nZ l1 + gap_weight nZ l2).
  { induction l1 as [|[b0 s0] l1 IH]; intros l2; cbn [app gap_weight]; [lia| rewrite IH; lia]. }
  set (F' := Z.max F LMm.task_unmapped_base).
  assert (HF'al : F' mod page_size = 0).
  { unfold F'. destruct (Z.max_spec F LMm.task_unmapped_base) as [[_ ->]|[_ ->]];
      [unfold LMm.task_unmapped_base, page_size; reflexivity| rewrite page_size_eq; exact S2]. }
  assert (HW' : F' + nZ + gap_weight nZ (vm_maps h ++ V) <= alloc_top h).
  { (* the HW arithmetic again, from max start_brk task_unmapped_base and with the pair added *)
    unfold F', LMm.task_unmapped_base.
    rewrite Happ, (gap_weight_sizes nZ (vm_maps h)). fold N LV. rewrite Htop.
    assert (HNn : 0 <= N) by (unfold N; lia).
    unfold PGSZ, KLIM, SMALLREQ in *.
    rewrite Z.mul_add_distr_l.
    assert (HN4 : N * 4095 <= LV) by lia.
    clear HW. destruct Hreq as [Hs|Hb].
    -
      assert (HN : N <= 2^18) by lia.
      assert (HP : N * nZ <= 2^18 * 2^24) by (apply Z.mul_le_mono_nonneg; lia).
      lia.
    -
      assert (E1 : (4096 * N) * nZ <= LV * nZ) by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite <- Z.mul_assoc in E1.
      pose proof (four_xy_le_sq LV nZ HLV ltac:(lia)) as E2.
      assert (E3 : (LV + nZ) * (LV + nZ) <= 2^30 * 2^30) by (apply Z.mul_le_mono_nonneg; lia).
      set (P := N * nZ) in *. set (Q := LV * nZ) in *. set (SQ := (LV + nZ) * (LV + nZ)) in *.
      lia. }
  destruct (gap_exists (vm_maps h ++ V) nZ F' (alloc_top h) ltac:(lia) ltac:(unfold F', PGSZ in *; lia)
              ltac:(rewrite Htop; lia) HF'al HW')
    as (g & Hgal & HgF & Hgtop & Hgfree).
  rewrite region_free_app_iff in Hgfree. apply andb_prop in Hgfree as [Hgm HgVf].
  assert (Hrf : region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true).
  { rewrite region_free_app_iff, Hgm, Bool.andb_true_r.
    fold h in Vres. rewrite Vres, region_free_app_iff, HgVf, Bool.andb_true_r.
    apply region_free_intro. intros a sz Hin.
    pose proof (Vrest (a, sz) Hin) as Hr. fold h F in Hr. unfold ehi in Hr. cbn [fst snd] in Hr.
    unfold iv_overlap. rewrite u64_lit' by (unfold F' in *; lia).
    apply andb_false_iff. left. apply Z.ltb_ge. unfold F' in *. lia. }
  intros thp hint. apply LPl.linux_place_exists; [lia| exact HnAl|].
  exists g. right. split; [exact Hgal|]. split; [unfold F' in *; lia|]. split; [exact Hgtop| exact Hrf].
Qed.

Lemma gk_budget : forall mo nZ,
  vm_clean mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  (nZ <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + nZ <= KLIM) ->
  vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof.
  intros mo nZ Hc (_ & G2 & _) Hl Hreq. pose proof (vm_backing_used_le_live mo Hc).
  unfold KLIM, SMALLREQ in *. lia.
Qed.

(** GRANT, anonymous mmap (forced-only port): when the arm's [*_refusable] test is false the unpatched
    spec admits a grant, at the base [vm_find_base] finds, and a grant's address is not an errno.  This
    is what the patch-04 proof read off the patched errno list ([mmap_errnos_when false = []]). *)
(* a worker TRIAL sem727: RESTATED premise. At the grant is Linux's exact placement
   (linux_place_is), so the premise is that placement (for the run's thp, the NULL hint) and, for rw, the
   backing; the old premise (the P04 refusability) read a free range anywhere below alloc_top. *)
Lemma mmap_anon_grant : forall {CE : Ceiling} len prot mo,
  0 < len -> mmap_len len < 2^64 -> prot = PROT_NONE \/ prot = PROT_RW ->
  (exists a0, LMm.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) (mmap_len len) a0) ->
  (prot = PROT_RW -> mmap_noreserve_backed_ok (Z_to_bv 64 MAPF) mo (mmap_len len) = true) ->
  exists eff2 mo2,
    syscall_spec (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 MAPF;
                                  Z_to_bv 64 (-1); Z_to_bv 64 0]) mo
                 (LinuxProcessSemantics.LinuxProcessSem.Monad.Ok eff2 mo2 [])
    /\ errno_ret_in mmap_errnos (eff_ret eff2) = false.
Proof.
  intros CE len prot mo Hlen Hlen2 Hprot (a0 & Hpl) Hbk0.
  pose proof (mmap_len_ge len Hlen) as Hb.
  assert (HnAl : mmap_len len mod page_size = 0) by (rewrite page_size_eq; apply mmap_len_aligned).
  assert (HnPos : 0 < mmap_len len) by lia.
  destruct (LPl.linux_place_admissible _ _ _ _ _ HnPos HnAl Hpl) as (B1 & B2 & B3 & B4).
  pose proof (alloc_top_room (m_vmmaps mo)) as Hroom.
  set (a := Z_to_bv 64 a0).
  assert (Ua : bv_unsigned a = a0) by (apply unsigned_lit; unfold stack_max_size, two_pow_64 in *; lia).
  assert (A4 : LPl.linux_place_is (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) (mmap_len len) a = true)
    by (apply LPl.linux_place_is_iff; [lia| exact HnAl| rewrite Ua; exact Hpl]).
  assert (A3 : bv_unsigned a + mmap_len len <= alloc_top (m_vmmaps mo)) by (rewrite Ua; exact B3).
  assert (HE : errno_ret_in mmap_errnos a = false).
  { destruct (errno_ret_in mmap_errnos a) eqn:E; [exfalso|reflexivity].
    apply errno_ret_in_true in E as (e & HIn & He). cbn in HIn. destruct HIn as [<-|[]].
    apply (f_equal (@bv_unsigned 64)) in He. rewrite errno_ret_unsigned in He by (unfold ENOMEM; lia).
    unfold stack_max_size, two_pow_64, ENOMEM in *. lia. }
  set (n := Z_to_bv 64 (mmap_len len)) in *.
  destruct Hprot as [-> | ->].
  - exists (mkEffectU a [] [] [(a, n)] [] []). eexists. split; [| exact HE].
    apply check_syscall_ok_iff.
    dispatch_pure LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.check_syscall_mmap.
    unfold check_mmap.
    change (mmap_off_aligned_b (Z_to_bv 64 0)) with true.
    change (mmap_anon_b (Z_to_bv 64 MAPF)) with true. cbn [negb].
    rewrite w_is0_lit by lia. replace (len =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true.
    rewrite place_declined_b_null.  (* a worker TRIAL sem727: the NULL-hint decline *)
    cbv iota beta zeta. rewrite unsigned_lit by lia. fold (mmap_len len). fold n.
    rewrite HE, A4.
    rewrite (proj2 (listNN_eqb_eq [(a, n)] [(a, n)]) eq_refl). reflexivity.
  - assert (Hbk : mmap_noreserve_backed_ok (Z_to_bv 64 MAPF) mo (mmap_len len) = true) by (exact (Hbk0 eq_refl)).
    exists (mkEffectU a [] [(a, n)] [] [] []). eexists. split; [| exact HE].
    apply check_syscall_ok_iff.
    dispatch_pure LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.check_syscall_mmap.
    unfold check_mmap.
    change (mmap_off_aligned_b (Z_to_bv 64 0)) with true.
    change (mmap_anon_b (Z_to_bv 64 MAPF)) with true. cbn [negb].
    rewrite w_is0_lit by lia. replace (len =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true.
    rewrite place_declined_b_null.  (* a worker TRIAL sem727: the NULL-hint decline *)
    cbv iota beta zeta. rewrite unsigned_lit by lia. fold (mmap_len len). fold n.
    rewrite HE, A4, Hbk.
    rewrite (proj2 (listNN_eqb_eq [(a, n)] [(a, n)]) eq_refl). reflexivity.
Qed.

(* a worker TRIAL sem727: RESTATED premise, as mmap_anon_grant. *)
Lemma nstep_mmap_anon_noerr : forall {CE : Ceiling} len prot mo rsp mo' evs,
  0 < len -> mmap_len len < 2^64 -> prot = PROT_NONE \/ prot = PROT_RW ->
  (exists a0, LMm.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) (mmap_len len) a0) ->
  (prot = PROT_RW -> mmap_noreserve_backed_ok (Z_to_bv 64 MAPF) mo (mmap_len len) = true) ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros CE len prot mo rsp mo' evs Hlen Hlen2 Hprot Hpl Hbk H.
  pose proof (mmap_len_ge len Hlen) as Hb.
  assert (HnAl : mmap_len len mod page_size = 0) by (rewrite page_size_eq; apply mmap_len_aligned).
  assert (HnPos : 0 < mmap_len len) by lia.
  assert (Hnrs : mmap_noreserve_b (Z_to_bv 64 MAPF) = false) by reflexivity.
  destruct (mmap_anon_grant len prot mo Hlen Hlen2 Hprot Hpl Hbk) as (eff2 & mo2 & Hs2 & Hnr2).
  pose proof H as Hst0.
  apply nstep_mmap_iff in H; [|exact Hnrs]. destruct H as [H _]. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 MAPF)) with true in H. cbn [negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  rewrite unsigned_lit in H by lia. fold (mmap_len len) in H. cbn [eff_ret].
  destruct Hprot as [-> | ->].
  - change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false in H.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true in H.
    rewrite place_declined_b_null in H.  (* a worker TRIAL sem727: the NULL-hint decline *)
    cbn iota beta in H.
    destruct ws; [|discriminate]. destruct zs; [|destruct us; discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    (* Forced-only port: a -ENOMEM answer is a refusal beside the grant, so not a node step. *)
    destruct (errno_ret_in mmap_errnos r) eqn:Herr.
    { exfalso.
      exact (nstep_refusal_no_grant (NMmap 0 len PROT_NONE MAPF) _ mo _ _ _ _ _ _ eq_refl Hst0 eq_refl Herr Hs2 Hnr2). }
    cbv beta iota zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    (* a worker TRIAL sem727: the success test is linux_place_is; its bound from lps admissibility *)
    apply andb_prop in E as [Epl _].
    destruct (LPl.linux_place_is_admissible _ _ _ _ _ HnPos HnAl Epl) as (_ & _ & E3 & _).
    apply errno_of_small. pose proof (alloc_top_room (m_vmmaps mo)).
    unfold stack_max_size, two_pow_64 in *. lia.
  - change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true in H.
    rewrite place_declined_b_null in H.  (* a worker TRIAL sem727: the NULL-hint decline *)
    cbn iota beta in H.
    destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:Herr.
    { exfalso.
      exact (nstep_refusal_no_grant (NMmap 0 len PROT_RW MAPF) _ mo _ _ _ _ _ _ eq_refl Hst0 eq_refl Herr Hs2 Hnr2). }
    cbv beta iota zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [Epl _].
    destruct (LPl.linux_place_is_admissible _ _ _ _ _ HnPos HnAl Epl) as (_ & _ & E3 & _).
    apply errno_of_small. pose proof (alloc_top_room (m_vmmaps mo)).
    unfold stack_max_size, two_pow_64 in *. lia.
Qed.

(* a worker TRIAL sem727: RESTATED as the two premises mmap_anon_grant now takes (was: the P04
   refusability is false); same hypotheses. *)
Lemma gk_refusable_false : forall {CE : Ceiling} L pbrk mo len prot,
  KL L pbrk mo -> GK (m_vmmaps mo) -> vm_live_bytes (m_vmmaps mo) <= KLIM ->
  0 < len -> prot = PROT_NONE \/ prot = PROT_RW ->
  (mmap_len len <= SMALLREQ \/ vm_live_bytes (m_vmmaps mo) + mmap_len len <= KLIM) ->
  (exists a0, LMm.linux_place (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) (mmap_len len) a0)
  /\ (prot = PROT_RW -> mmap_noreserve_backed_ok (Z_to_bv 64 MAPF) mo (mmap_len len) = true).
Proof.
  intros CE L pbrk mo len prot HK HG Hl Hlen Hprot Hreq.
  pose proof (mmap_len_ge len Hlen) as Hb. pose proof (mmap_len_aligned len) as Hal.
  split.
  - exact (gk_gap L pbrk mo (mmap_len len) HK HG Hl ltac:(lia) ltac:(rewrite page_size_eq; exact Hal) Hreq _ _).
  - intros _. unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbn iota.
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
  destruct (gk_refusable_false L pbrk mo len prot HK HG Hl ltac:(lia) Hprot Hreq) as [Hpl Hbk].
  exact (nstep_mmap_anon_noerr len prot mo rsp mo' evs ltac:(lia) ltac:(lia) Hprot Hpl Hbk Hst).
Qed.

Lemma nstep_mprotect_noerr : forall {CE : Ceiling} addr mo rsp mo' evs,
  0 <= addr -> addr + PGSZ < 2^64 -> addr mod PGSZ = 0 ->
  mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ) = true ->
  nstep (NMprotect addr PGSZ PROT_RW) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros CE addr mo rsp mo' evs Ha0 Ha1 Hal Hbud H.
  pose proof H as Hst0.
  apply nstep_mprotect_iff in H. destruct H as [H _]. destruct rsp as [r ws zs us cs ci]. unfold check_mprotect in H. cbn [eff_ret].
  change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false in H.
  rewrite (unsigned_lit addr) in H by (unfold PGSZ in *; lia). rewrite page_size_eq in H.
  unfold PGSZ in Hal. rewrite Hal in H. cbn [negb Z.eqb] in H.
  rewrite w_is0_lit in H by (unfold PGSZ; lia). change (PGSZ =? 0) with false in H.
  rewrite (unsigned_lit PGSZ) in H by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ in H.
  replace (two_pow_64 <=? addr + PGSZ) with false in H by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia).
  change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true in H. cbn [negb] in H. cbv iota zeta in H.
  (* a worker TRIAL sem727: the vDSO test comes first at ; the step is past it (Evd). *)
  match type of H with (if negb ?c then CheckUnmodeled else _) = _ => destruct c eqn:Evd; cbn [negb] in H; [|discriminate] end.
  destruct (map_contains _ _ _ && map_contains _ _ _) eqn:Hc.
  - destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    (* Forced-only port: with the commit charge fitting ([Hbud]) the spec admits the grant, so a
       -ENOMEM answer is a spurious refusal and not a node step. *)
    destruct (errno_ret_in mprotect_errnos r) eqn:Herr.
    { exfalso.
      assert (Hg : syscall_spec (pure_input 226 [Z_to_bv 64 addr; Z_to_bv 64 PGSZ; Z_to_bv 64 PROT_RW]) mo
                     (LinuxProcessSemantics.LinuxProcessSem.Monad.Ok
                        (mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 PGSZ)] [] [] [])
                        (mprotect_model_next mo (Z_to_bv 64 addr) (Z_to_bv 64 PGSZ)) [])).
      { apply check_syscall_ok_iff.
        dispatch_pure LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.DispatchCompute.check_syscall_mprotect.
        unfold check_mprotect.
        change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false.
        rewrite (unsigned_lit addr) by (unfold PGSZ in *; lia). rewrite page_size_eq, Hal. cbn [negb Z.eqb].
        rewrite w_is0_lit by (unfold PGSZ; lia). change (PGSZ =? 0) with false.
        rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ.
        replace (two_pow_64 <=? addr + PGSZ) with false
          by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia).
        change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true. cbn [negb]. cbv iota zeta.
        rewrite Evd. cbn [negb]. cbv iota.
        rewrite Hc. change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false. cbv iota.
        rewrite Hbud. change (w_is0 (Z_to_bv 64 0)) with true.
        rewrite (proj2 (listNN_eqb_eq [(Z_to_bv 64 addr, Z_to_bv 64 PGSZ)] [(Z_to_bv 64 addr, Z_to_bv 64 PGSZ)])
                   eq_refl).
        reflexivity. }
      exact (nstep_refusal_no_grant (NMprotect addr PGSZ PROT_RW) _ mo _ _ _ _ _ _ eq_refl Hst0 eq_refl Herr Hg
               eq_refl). }
    cbv beta iota in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:E; [|discriminate] end.
    apply andb_prop in E as [E _]. apply andb_prop in E as [_ E]. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    apply errno_of_lit. lia.
  - match type of H with context [if ?c then _ else _] => destruct c eqn:E0; [|discriminate] end.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    cbv beta iota in H.
    match type of H with context [if ?c then _ else _] => destruct c eqn:E; [|discriminate] end.
    unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    apply errno_of_lit. lia.
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
