(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the kernel ledger record KL reads its reservations as the image's followed by the vDSO pair (kl_resv) and gains the fields kl_mres and kl_vin, with lemmas on the initial ledger and on ranges inside a mapping missing the ledger and the vDSO pair; taken in part from projects/simdjson/fuzz_parser/proofs/lib/Spec/KLink.v, lines 41-48, 82-105, 110-126, 135-152. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree Malloc KInv PState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  (* LPS 08b1429: the ledger is the image's reservations [R0] (what the heap's
     ghost [ld_resv] knows, below [start_brk]) followed by the vDSO pair [rx]
     ([State.init_reserved]): at most two entries and 20 pages. *)
  kl_resv : exists R0 rx, vm_reserved (m_vmmaps mo) = R0 ++ rx /\ ld_resv L = map wwZ R0
      /\ (forall e, In e R0 -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo)))
      /\ (length rx <= 2)%nat /\ live_bytes rx <= 0x14000;
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
  (* LPS 08b1429: every mapping is free of the reserved ledger (placement grants only
     [region_free (vm_reserved ++ vm_maps)] ranges), and the vDSO pair [check_mprotect]
     tests is part of that ledger. Together: a range inside a mapping misses the pair. *)
  kl_mres : forall e, In e (vm_maps (m_vmmaps mo)) -> region_free (vm_reserved (m_vmmaps mo)) (fst e) (snd e) = true;
  kl_vin : incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (vm_reserved (m_vmmaps mo)) }.

Lemma live_bytes_app_kl : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn [app live_bytes]; [lia| rewrite IH; lia]. Qed.

Lemma reserved_top_ge_kl : forall l e, In e l -> ehi e <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; unfold ehi; cbn [fst snd]; [lia|]. specialize (IH e Hin). unfold ehi in IH. lia.
Qed.

Lemma vdso_reserved_size : forall kb top,
  (length (vdso_reserved kb top) <= 2)%nat /\ live_bytes (vdso_reserved kb top) <= 0x14000.
Proof.
  intros kb top. pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
  unfold vdso_reserved. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [length live_bytes]; [lia|].
  rewrite !bv_unsigned_Z_to_bv_u64 by (unfold two_pow_64, vdso_vvar_pages, page_size in *; lia).
  unfold vdso_vvar_pages, page_size. lia.
Qed.

(* The ledger [init_model] starts from: the image's reservations, then the vDSO pair. *)
Lemma KL_resv_init : forall segs brk0 mbase sp lim inp,
  valid_brk segs brk0 ->
  let h := m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp) in
  (exists R0 rx, vm_reserved h = R0 ++ rx /\ map wwZ (segments_reserved segs) = map wwZ R0
      /\ (forall e, In e R0 -> ehi e <= bv_unsigned (vm_start_brk h))
      /\ (length rx <= 2)%nat /\ live_bytes rx <= 0x14000)
  /\ live_bytes (vm_reserved h) <= live_bytes (segments_reserved segs) + 0x14000.
Proof.
  intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) h.
  set (T := page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))).
  assert (ER : vm_reserved h = segments_reserved segs ++ vdso_reserved (in_kernel inp) T)
    by (subst h T; rewrite m_vmmaps_init_model; reflexivity).
  assert (ESB : vm_start_brk h = brk0) by (subst h; rewrite m_vmmaps_init_model; reflexivity).
  assert (HR : forall e, In e (segments_reserved segs) -> ehi e <= bv_unsigned brk0)
    by (intros e He; pose proof (reserved_top_ge_kl _ _ He); lia).
  destruct (vdso_reserved_size (in_kernel inp) T) as [LN LB].
  rewrite ER, ESB. split.
  - exists (segments_reserved segs), (vdso_reserved (in_kernel inp) T).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HR|]. split; assumption.
  - rewrite live_bytes_app_kl. lia.
Qed.

Lemma KL_vin_init : forall reserved brk0 mbase sp lim inp,
  incl (vdso_reserved (m_kernel (init_model reserved brk0 mbase sp lim inp))
                      (vdso_top (m_vmmaps (init_model reserved brk0 mbase sp lim inp))))
       (vm_reserved (m_vmmaps (init_model reserved brk0 mbase sp lim inp))).
Proof.
  intros. rewrite vm_reserved_init_model.
  assert (EK : m_kernel (init_model reserved brk0 mbase sp lim inp) = in_kernel inp) by reflexivity.
  rewrite EK. intros x Hx. apply in_or_app. right. exact Hx.
Qed.

(* The heap's ghost reservations are entries of the model's ledger. *)
Lemma kl_resv_In : forall L pbrk mo x, KL L pbrk mo -> In x (ld_resv L) ->
  exists e, wwZ e = x /\ In e (vm_reserved (m_vmmaps mo)).
Proof.
  intros L pbrk mo x HK Hin. destruct (kl_resv _ _ _ HK) as (R0 & rx & ER & EL & _).
  rewrite EL in Hin. apply in_map_iff in Hin as (e & E & He). exists e. split; [exact E|].
  rewrite ER. apply in_or_app. left. exact He.
Qed.

Lemma region_free_app_l_kl : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof.
  induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [reflexivity|]. cbn [region_free app] in H |- *.
  apply andb_prop in H as [H1 H2]. rewrite H1, (IH _ _ _ H2). reflexivity.
Qed.

Lemma region_free_incl_kl : forall l1 l2 a n, incl l1 l2 -> region_free l2 a n = true -> region_free l1 a n = true.
Proof.
  induction l1 as [|[e sz] l1 IH]; intros l2 a n Hi H; [reflexivity|]. cbn [region_free].
  rewrite (State.region_free_In _ _ _ _ _ H (Hi _ (or_introl eq_refl))). cbn [negb andb].
  apply (IH l2); [intros x Hx; apply Hi; right; exact Hx| exact H].
Qed.

Lemma region_free_sub_kl : forall maps a n a' n', region_free maps a n = true ->
  bv_unsigned a <= bv_unsigned a' -> bv_unsigned a' + bv_unsigned n' <= bv_unsigned a + bv_unsigned n ->
  region_free maps a' n' = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros a n a' n' H H1 H2; [reflexivity|]. cbn [region_free] in H |- *.
  apply andb_prop in H as [Ha Hb]. rewrite (IH _ _ _ _ Hb H1 H2), andb_true_r.
  unfold iv_overlap in *. apply negb_true_iff in Ha. apply negb_true_iff.
  apply andb_false_iff in Ha. apply andb_false_iff.
  destruct Ha as [Ha|Ha]; [left| right]; apply Z.ltb_ge in Ha; apply Z.ltb_ge; lia.
Qed.

(* A range inside a mapping is free of the ledger. *)
Lemma resv_free_of_map : forall L pbrk mo e aw nw, KL L pbrk mo -> In e (vm_maps (m_vmmaps mo)) ->
  elo e <= bv_unsigned aw -> bv_unsigned aw + bv_unsigned nw <= ehi e ->
  region_free (vm_reserved (m_vmmaps mo)) aw nw = true.
Proof.
  intros L pbrk mo e aw nw HK He H1 H2. unfold elo, ehi in H1, H2.
  eapply region_free_sub_kl; [exact (kl_mres _ _ _ HK e He)| exact H1| exact H2].
Qed.

(* A range inside a mapping misses the vDSO pair ([check_mprotect]'s gate). *)
Lemma vdso_free_of_map : forall L pbrk mo e aw nw, KL L pbrk mo -> In e (vm_maps (m_vmmaps mo)) ->
  elo e <= bv_unsigned aw -> bv_unsigned aw + bv_unsigned nw <= ehi e ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw = true.
Proof.
  intros L pbrk mo e aw nw HK He H1 H2. eapply region_free_incl_kl; [exact (kl_vin _ _ _ HK)|].
  exact (resv_free_of_map _ _ _ e aw nw HK He H1 H2).
Qed.

(* The vDSO pair's place reads the kernel build, [vm_mmap_base] and [vm_init_sp] only. *)
Lemma vin_keep : forall kb h R kb' h', incl (vdso_reserved kb (vdso_top h)) R -> kb' = kb ->
  vm_mmap_base h' = vm_mmap_base h -> vm_init_sp h' = vm_init_sp h ->
  incl (vdso_reserved kb' (vdso_top h')) R.
Proof. intros kb h R kb' h' H -> Eb Es. unfold vdso_top, mmap_top, alloc_top. rewrite Eb, Es. exact H. Qed.

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
Lemma vm_only_alloc_top : forall m m', vm_only m m' -> alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).
Proof. intros m m' H. unfold alloc_top. rewrite (vm_only_init_sp _ _ H). reflexivity. Qed.
Lemma alloc_top_of_init_sp : forall h h', vm_init_sp h' = vm_init_sp h -> alloc_top h' = alloc_top h.
Proof. intros h h' H. unfold alloc_top. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma KL_atop_range : forall L pbrk mo, KL L pbrk mo -> alloc_ceiling_lo <= ld_atop L <= alloc_ceiling.
Proof. intros L pbrk mo HK. rewrite (kl_atop _ _ _ HK). apply minv_alloc_top. exact (kl_minv _ _ _ HK). Qed.
Lemma KL_atop_lt : forall L pbrk mo, KL L pbrk mo -> 0 < ld_atop L < 2^63.
Proof. intros L pbrk mo HK. pose proof (KL_atop_range _ _ _ HK). rewrite alloc_ceiling_val, alloc_ceiling_lo_val in *. lia. Qed.
