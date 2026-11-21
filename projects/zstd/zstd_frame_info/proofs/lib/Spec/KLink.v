(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (KL's reserved-ledger fields restated: ld_resv is a prefix of the model's ledger, each entry ending at or below the break's start or starting 4 pages above it; new KL fields kl_resv_vdso (the image's entries then the vDSO pair) and kl_maps_resv (every mapping misses the ledger); kl_resv_sub, KL_resv_free_brk, KL_vdso_free, vm_only_kernel and five region_free helpers added). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad STree Malloc KInv PState.
Import ListNotations.
Open Scope Z_scope.

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

(* [comment removed for export] *)
Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

(* [comment removed for export] *)
Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

(* [comment removed for export] *)
Definition brk_disj (L : mled) (b n : Z) : Prop :=
  forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
kl_resv : exists V, map wwZ (vm_reserved (m_vmmaps mo)) = ld_resv L ++ V;
kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) ->
ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo))
\/ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e;
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= ld_atop L;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= ld_atop L
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= ld_atop L
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= ld_atop L
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= ld_atop L
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  kl_atop : ld_atop L = alloc_top (m_vmmaps mo);   (* [comment removed for export] *)
  (* LPS 727298f3: the reserved ledger is the image's entries, each ending at or below the break's
     start, followed by the vDSO/vvar pair the launch reserves (State.init_reserved) *)
  kl_resv_vdso : exists R0, vm_reserved (m_vmmaps mo) = R0 ++ vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))
      /\ (forall e, In e R0 -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo)));
  (* LPS 727298f3: every tracked mapping misses the reserved ledger *)
  kl_maps_resv : forall e, In e (vm_maps (m_vmmaps mo)) -> region_free (vm_reserved (m_vmmaps mo)) (fst e) (snd e) = true }.
Lemma kl_resv_sub : forall L pbrk mo x, KL L pbrk mo -> In x (ld_resv L) -> In x (map wwZ (vm_reserved (m_vmmaps mo))).
Proof. intros L pbrk mo x HK Hx. destruct (kl_resv _ _ _ HK) as (V & E). rewrite E. apply in_or_app. left. exact Hx. Qed.

Lemma region_free_split : forall maps aw nw,
  (forall e, In e maps -> ehi e <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= elo e) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi, elo in H; cbn [fst snd] in H.
  destruct H as [H|H].
  - rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned e) _) H). rewrite andb_false_r. reflexivity.
Qed.

Lemma KL_resv_free_brk : forall L pbrk mo (aw nw : word), KL L pbrk mo ->
  bv_unsigned aw = bv_unsigned (vm_start_brk (m_vmmaps mo)) -> bv_unsigned nw <= 4 * PGSZ ->
  region_free (vm_reserved (m_vmmaps mo)) aw nw = true.
Proof.
  intros L pbrk mo aw nw HK Ha Hn. apply region_free_split. intros e He.
  destruct (kl_resv_top _ _ _ HK e He) as [H|H]; [left|right]; lia.
Qed.

(* LPS 727298f3: a range inside a range free of a ledger is free of it too *)
Lemma region_free_within : forall maps (a n a' n' : word), region_free maps a n = true ->
  bv_unsigned a <= bv_unsigned a' -> bv_unsigned a' + bv_unsigned n' <= bv_unsigned a + bv_unsigned n ->
  region_free maps a' n' = true.
Proof.
  intros maps a n a' n' H H1 H2. apply region_free_split. intros [e sz] Hin.
  pose proof (Decode.region_free_In _ _ _ _ _ H Hin) as D. unfold elo, ehi. cbn [fst snd]. lia.
Qed.

Lemma region_free_suffix : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof.
  induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|].
  cbn [app region_free] in H. apply andb_prop in H as [_ H]. exact (IH _ _ _ H).
Qed.

(* LPS 727298f3: a range inside a tracked mapping misses the vDSO pair (the checker's mprotect gate) *)
Lemma KL_vdso_free : forall L pbrk mo e (aw nw : word), KL L pbrk mo -> In e (vm_maps (m_vmmaps mo)) ->
  elo e <= bv_unsigned aw -> bv_unsigned aw + bv_unsigned nw <= ehi e ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw = true.
Proof.
  intros L pbrk mo [a n] aw nw HK Hin H1 H2.
  destruct (kl_resv_vdso _ _ _ HK) as (R0 & E & _).
  pose proof (kl_maps_resv _ _ _ HK _ Hin) as F. rewrite E in F. cbn [fst snd] in F.
  exact (region_free_within _ _ _ _ _ (region_free_suffix _ _ _ _ F) H1 H2).
Qed.

(* LPS 727298f3: a new entry free of the reserved ledger and the mappings keeps kl_maps_resv *)
Lemma maps_resv_cons : forall R maps (a n : word),
  (forall e, In e maps -> region_free R (fst e) (snd e) = true) ->
  region_free (R ++ maps) a n = true ->
  forall e, In e ((a, n) :: maps) -> region_free R (fst e) (snd e) = true.
Proof.
  intros R maps a n Hm Hrf e [<-|He]; [|exact (Hm e He)].
  cbn [fst snd]. clear -Hrf. revert Hrf. induction R as [|[b s] R IH]; intros Hrf; [reflexivity|].
  cbn [app region_free] in Hrf |- *. apply andb_prop in Hrf as [H1 H2]. rewrite H1. cbn [andb]. exact (IH H2).
Qed.

(* LPS 727298f3: entries each inside an old entry keep kl_maps_resv *)
Lemma maps_resv_within : forall R maps maps',
  (forall e, In e maps -> region_free R (fst e) (snd e) = true) ->
  (forall e', In e' maps' -> exists e, In e maps /\ elo e <= elo e' /\ ehi e' <= ehi e) ->
  forall e', In e' maps' -> region_free R (fst e') (snd e') = true.
Proof.
  intros R maps maps' Hm Hw e' He'. destruct (Hw e' He') as (e & He & W1 & W2).
  exact (region_free_within _ _ _ _ _ (Hm e He) W1 W2).
Qed.


(* [comment removed for export] *)
Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_only_init_sp : forall m m', vm_only m m' -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
Proof. intros m m' (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma vm_only_kernel : forall m m', vm_only m m' -> m_kernel m' = m_kernel m.
Proof. intros m m' (_ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
Lemma vm_only_alloc_top : forall m m', vm_only m m' -> alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).
Proof. intros m m' H. unfold alloc_top. rewrite (vm_only_init_sp _ _ H). reflexivity. Qed.
Lemma alloc_top_of_init_sp : forall h h', vm_init_sp h' = vm_init_sp h -> alloc_top h' = alloc_top h.
Proof. intros h h' H. unfold alloc_top. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma KL_atop_range : forall L pbrk mo, KL L pbrk mo -> alloc_ceiling_lo <= ld_atop L <= alloc_ceiling.
Proof. intros L pbrk mo HK. rewrite (kl_atop _ _ _ HK). apply minv_alloc_top. exact (kl_minv _ _ _ HK). Qed.
Lemma KL_atop_lt : forall L pbrk mo, KL L pbrk mo -> 0 < ld_atop L < 2^63.
Proof. intros L pbrk mo HK. pose proof (KL_atop_range _ _ _ HK). rewrite alloc_ceiling_val, alloc_ceiling_lo_val in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=21490301092.5000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
