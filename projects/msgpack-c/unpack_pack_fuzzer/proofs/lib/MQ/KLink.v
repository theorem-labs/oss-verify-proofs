(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the kernel's start ledger holds the vdso/vvar pair: the allocator's ledger is a prefix of it, the pair is in it, no mapping meets it; the image's reservations lie below the brk start and the pair four pages above it). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import ITree Nodes NodesM Decode DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog.
Import ListNotations.
Local Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

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

Definition noacc_ok (L : mled) (h : VmMaps) : Prop :=
  forall e, In e (vm_noaccess h) ->
    exists e', In e' (vm_maps h) /\ elo e' <= elo e /\ ehi e <= ehi e'
               /\ forall b l, In (b, l) (ld_groups L) -> e' <> went b (mmap_len l).

Lemma noacc_ok_mono : forall L L' h h',
  noacc_ok L h -> (forall e, In e (vm_noaccess h') -> In e (vm_noaccess h)) ->
  (forall e', In e' (vm_maps h) -> In e' (vm_maps h')) ->
  (forall b l, In (b, l) (ld_groups L') -> In (b, l) (ld_groups L)) -> noacc_ok L' h'.
Proof.
  intros L L' h h' H Hna Hm Hg e He. destruct (H e (Hna e He)) as (e' & H1 & H2 & H3 & H4).
  exists e'. split; [apply Hm; exact H1|]. split; [exact H2|]. split; [exact H3|]. intros b l Hb. apply H4. apply Hg. exact Hb.
Qed.

(** At LPS 727298f3 [State.init_model]'s reservation ledger is the image's
    reservations FOLLOWED BY the vdso/vvar pair ([State.init_reserved]); no
    step edits it.  The allocator's ledger keeps the image's part only, so
    [kl_resv] says it is a prefix; [kl_vdso] says the pair is in the kernel's
    ledger, and [kl_mres] that no mapping meets the kernel's ledger (the grant
    gate tests [vm_reserved ++ vm_maps]).  mprotect answers [unmodeled] over
    the pair ([Checks/Sys/Mm/Mprotect.v]), and these two are what show a page
    of a mapping is not in it. *)
Definition mres_ok (h : VmMaps) : Prop :=
  forall e, In e (vm_maps h) -> region_free (vm_reserved h) (fst e) (snd e) = true.
Definition vdso_in (mo : Model) : Prop :=
  incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (vm_reserved (m_vmmaps mo)).

Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  kl_wfna : forall e, In e (vm_noaccess (m_vmmaps mo)) -> elo e < ehi e <= 2^64;
  kl_resv : exists V, map wwZ (vm_reserved (m_vmmaps mo)) = ld_resv L ++ V;
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) ->
      ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo)) \/ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e;
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_ceiling;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;

  kl_noacc : noacc_ok L (m_vmmaps mo);

  kl_ceil : ceil_ok (m_vmmaps mo);

  kl_mres : mres_ok (m_vmmaps mo);

  kl_vdso : vdso_in mo }.

Lemma kl_resv_sub : forall L pbrk mo x, KL L pbrk mo -> In x (ld_resv L) -> In x (map wwZ (vm_reserved (m_vmmaps mo))).
Proof. intros L pbrk mo x HK Hx. destruct (kl_resv _ _ _ HK) as (V & E). rewrite E. apply in_or_app. left. exact Hx. Qed.

Lemma kl_rf_apart : forall maps a n,
  (forall e sz, In (e, sz) maps -> bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a) ->
  region_free maps a n = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' sz' Hin; apply H; right; exact Hin). unfold iv_overlap.
  specialize (H e sz (or_introl eq_refl)).
  repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec0 x y) end; cbn; first [reflexivity | lia].
Qed.

Lemma kl_rf_sub : forall maps a n a' n',
  bv_unsigned a <= bv_unsigned a' -> bv_unsigned a' + bv_unsigned n' <= bv_unsigned a + bv_unsigned n ->
  region_free maps a n = true -> region_free maps a' n' = true.
Proof.
  intros maps a n a' n' H1 H2 H. apply kl_rf_apart. intros e sz Hin.
  pose proof (DecodeM.region_free_In _ _ _ _ _ H Hin). lia.
Qed.

Lemma kl_rf_incl : forall l1 l2 a n, incl l1 l2 -> region_free l2 a n = true -> region_free l1 a n = true.
Proof.
  intros l1 l2 a n Hi H. apply kl_rf_apart. intros e sz Hin. exact (DecodeM.region_free_In _ _ _ _ _ H (Hi _ Hin)).
Qed.

Lemma kl_rf_split : forall maps aw nw,
  (forall e, In e maps -> ehi e <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= elo e) -> region_free maps aw nw = true.
Proof.
  intros maps aw nw H. apply kl_rf_apart. intros e sz Hin. specialize (H (e, sz) Hin). unfold ehi, elo in H; cbn [fst snd] in H. lia.
Qed.

(** a range inside a mapping is free of the kernel's ledger, and so of the vDSO pair *)
Lemma kl_in_map_free : forall L pbrk mo e a n, KL L pbrk mo -> In e (vm_maps (m_vmmaps mo)) ->
  elo e <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= ehi e ->
  region_free (vm_reserved (m_vmmaps mo)) a n = true.
Proof.
  intros L pbrk mo [e sz] a n HK He H1 H2. unfold elo, ehi in *; cbn [fst snd] in *.
  exact (kl_rf_sub _ _ _ _ _ H1 H2 (kl_mres _ _ _ HK _ He)).
Qed.
Lemma kl_vdso_free : forall L pbrk mo a n, KL L pbrk mo ->
  region_free (vm_reserved (m_vmmaps mo)) a n = true ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) a n = true.
Proof. intros L pbrk mo a n HK H. exact (kl_rf_incl _ _ _ _ (kl_vdso _ _ _ HK) H). Qed.

(** what the vDSO pair's place is read from: the kernel build, the ledger, mmap_base and the initial sp *)
Lemma vdso_in_keep : forall mo mo', vdso_in mo ->
  m_kernel mo' = m_kernel mo -> vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) -> vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) ->
  vdso_in mo'.
Proof.
  intros mo mo' H E1 E2 E3 E4. unfold vdso_in, vdso_top, mmap_top, alloc_top in *. rewrite E1, E2, E3, E4. exact H.
Qed.
Lemma vdso_in_vm_only : forall mo mo', vm_only mo mo' -> vdso_in mo -> vdso_in mo'.
Proof.
  intros mo mo' Hv H. destruct (vm_only_consts _ _ Hv) as (E2 & _ & _ & E3 & E4).
  exact (vdso_in_keep mo mo' H (vm_only_kernel _ _ Hv) E2 E3 E4).
Qed.

(** [kl_mres] across a step that keeps the ledger and whose mappings are old ones, sub-ranges of old ones,
    or ranges free of the ledger *)
Lemma mres_keep : forall h h', mres_ok h -> vm_reserved h' = vm_reserved h ->
  (forall e', In e' (vm_maps h') ->
     (exists e, In e (vm_maps h) /\ elo e <= elo e' /\ ehi e' <= ehi e)
     \/ region_free (vm_reserved h) (fst e') (snd e') = true) ->
  mres_ok h'.
Proof.
  intros h h' H Er Hm e' He'. rewrite Er. destruct (Hm e' He') as [(e & He & H1 & H2)|Hf]; [|exact Hf].
  destruct e as [a n]. destruct e' as [a' n']. unfold elo, ehi in *; cbn [fst snd] in *.
  exact (kl_rf_sub _ _ _ _ _ H1 H2 (H _ He)).
Qed.

(** a piece [State.iv_subtract] leaves of a mapping lies inside it *)
Lemma iv_subtract_sub : forall (a sz : word) lo hi e', ehi (a, sz) <= 2^64 -> In e' (iv_subtract a sz lo hi) ->
  elo (a, sz) <= elo e' /\ ehi e' <= ehi (a, sz).
Proof.
  intros a sz lo hi e' Hw Hin. unfold elo, ehi in *; cbn [fst snd] in *.
  pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ sz) as Rs.
  unfold bv_modulus in Ra, Rs. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra, Rs.
  unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. destruct Hin as [<-|[]]. apply Z.ltb_lt in E.
    cbn [fst snd]. rewrite (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState.unsigned_lit (Z.min _ _)) by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. destruct Hin as [<-|[]]. apply Z.ltb_lt in E.
    cbn [fst snd]. rewrite (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState.unsigned_lit (Z.max _ _)), (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState.unsigned_lit (_ - Z.max _ _)) by lia. lia.
Qed.

Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.

Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. exact NodesM.vm_only_refl. Qed.
Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof. exact NodesM.vm_only_trans. Qed.

Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

End CEIL.
