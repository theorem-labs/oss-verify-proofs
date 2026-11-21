(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Export KLedger.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

Definition brk_disj (L : mled) (b n : Z) : Prop :=
  forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

(* The reserved ledger is the image's entries, each ending at or below start_brk, followed by the vDSO pair
   the launch appends (State.init_reserved).  No step changes the kernel build, the reserved ledger, the
   mmap base, the stack top or start_brk, so the split survives every step. *)
Definition vdso_in_resv (mo : Model) : Prop :=
  exists R, vm_reserved (m_vmmaps mo) = R ++ vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))
            /\ forall e, In e R -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo)).
Arguments vdso_in_resv : simpl never.

Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_ceil : ld_ceil L = alloc_top (m_vmmaps mo);
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  kl_resv : exists V, map wwZ (vm_reserved (m_vmmaps mo)) = ld_resv L ++ V;
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) ->
      ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo))
      \/ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e;
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= ld_ceil L;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= ld_ceil L
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= ld_ceil L
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= ld_ceil L
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= ld_ceil L
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;

  kl_grp_resv : forall b l, In (b, l) (ld_groups L) -> forall e, In e (vm_reserved (m_vmmaps mo)) ->
      b + mmap_len l <= elo e \/ ehi e <= b;

  kl_noacc : forall e, In e (vm_noaccess (m_vmmaps mo)) ->
      elo e < ehi e /\
      exists e', In e' (vm_maps (m_vmmaps mo)) /\ elo e' <= elo e /\ ehi e <= ehi e'
                 /\ (forall b l, In (b, l) (ld_groups L) -> elo e' <> b);

  kl_meta_resv : forall b l k, In (b, l, k) (ld_metas L) -> forall e, In e (vm_reserved (m_vmmaps mo)) ->
      b + mmap_len l <= elo e \/ ehi e <= b;

  kl_vdso : vdso_in_resv mo }.

Lemma kl_resv_sub : forall L pbrk mo x, KL L pbrk mo -> In x (ld_resv L) -> In x (map wwZ (vm_reserved (m_vmmaps mo))).
Proof. intros L pbrk mo x HK Hx. destruct (kl_resv _ _ _ HK) as (V & E). rewrite E. apply in_or_app. left. exact Hx. Qed.

Lemma map_wwZ_app_inv : forall l A B, map wwZ l = A ++ B ->
  exists l1 l2, l = l1 ++ l2 /\ map wwZ l1 = A /\ map wwZ l2 = B.
Proof.
  induction l as [|x l IH]; intros A B E.
  - destruct A as [|a A]; [|discriminate]. exists [], []. split; [reflexivity|]. split; [reflexivity| exact E].
  - destruct A as [|a A].
    + exists [], (x :: l). split; [reflexivity|]. split; [reflexivity| exact E].
    + cbn [map app] in E. injection E as Ea E. destruct (IH A B E) as (l1 & l2 & -> & E1 & E2).
      exists (x :: l1), l2. split; [reflexivity|]. split; [cbn [map]; rewrite E1, Ea; reflexivity| exact E2].
Qed.

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

(* the brk area's first pages miss the reserved ledger: image entries end below start_brk, the vDSO pair is far above *)
Lemma KL_resv_free_brk : forall L pbrk mo (aw nw : word), KL L pbrk mo ->
  bv_unsigned aw = bv_unsigned (vm_start_brk (m_vmmaps mo)) -> bv_unsigned nw <= 4 * PGSZ ->
  region_free (vm_reserved (m_vmmaps mo)) aw nw = true.
Proof.
  intros L pbrk mo aw nw HK Ha Hn. apply region_free_split. intros e He.
  destruct (kl_resv_top _ _ _ HK e He) as [H|H]; [left|right]; lia.
Qed.

Lemma vdso_in_resv_keep : forall mo mo', vdso_in_resv mo ->
  m_kernel mo' = m_kernel mo ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vdso_in_resv mo'.
Proof.
  intros mo mo' H K Rv B S SB. unfold vdso_in_resv in *. destruct H as (R & ER & HR). exists R.
  unfold vdso_top, mmap_top, alloc_top in ER |- *. rewrite K, Rv, B, S, SB. split; [exact ER| exact HR].
Qed.

Lemma kl_vdso_In : forall L pbrk mo e, KL L pbrk mo ->
  In e (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) -> In e (vm_reserved (m_vmmaps mo)).
Proof.
  intros L pbrk mo e HK He. pose proof (kl_vdso _ _ _ HK) as V. unfold vdso_in_resv in V. destruct V as (R & ER & _).
  rewrite ER. apply in_or_app. right. exact He.
Qed.

Lemma vdso_reserved_length : forall kb top, (length (vdso_reserved kb top) <= 2)%nat.
Proof. intros kb top. unfold vdso_reserved. cbv zeta. destruct (_ <? _); cbn [length]; lia. Qed.

Lemma vdso_top_lt : forall h, vdso_top h < two_pow_64.
Proof.
  intros h. unfold vdso_top, mmap_top.
  pose proof (page_round_down_Z_le (Z.min (bv_unsigned (vm_mmap_base h)) (page_round_down_Z (alloc_top h)))) as H1.
  pose proof (Z.le_min_l (bv_unsigned (vm_mmap_base h)) (page_round_down_Z (alloc_top h))) as H2.
  pose proof (bv_unsigned_in_range 64 (vm_mmap_base h)) as H3. unfold bv_modulus in H3. change (2 ^ Z.of_N 64) with (2^64) in H3.
  unfold two_pow_64. lia.
Qed.

(* every entry of the pair ending at the page below [x] starts within twenty-one pages of [x] *)
Lemma vdso_entry_lo : forall kb x a n, 0 <= x < two_pow_64 ->
  In (a, n) (vdso_reserved kb (page_round_down_Z x)) -> x - 21 * 4096 < bv_unsigned a.
Proof.
  intros kb x a n Hx He.
  assert (T1 : page_round_down_Z x <= x) by apply page_round_down_Z_le.
  assert (T2 : x - 4096 < page_round_down_Z x).
  { unfold page_round_down_Z, page_size. pose proof (Z_div_mod_eq_full x 4096). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)). lia. }
  pose proof (vdso_reserved_above kb (page_round_down_Z x) a n ltac:(lia) He) as [A1 _]. pose proof (vdso_len_bounds kb) as [_ VL].
  unfold page_size in VL. lia.
Qed.

Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> mm_frame mo mo' -> G s mo -> G s' mo'.

Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

