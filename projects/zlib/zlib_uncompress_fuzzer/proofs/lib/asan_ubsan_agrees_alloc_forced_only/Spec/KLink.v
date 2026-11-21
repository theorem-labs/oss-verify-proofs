(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree Malloc KInv PState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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

Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  (* LPS : the ledger is the image's reservations [R0] (what the heap's
     ghost [ld_resv] knows, below [start_brk]) followed by the vDSO pair [rx]
     ([State.init_reserved]): at most two entries and 20 pages, at or above
     [start_brk + 4 pages]. See recipes/artm-vdso-ledger.md. *)
  kl_resv : exists R0 rx, vm_reserved (m_vmmaps mo) = R0 ++ rx /\ ld_resv L = map wwZ R0
      /\ (forall e, In e R0 -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo)))
      /\ (forall e, In e rx -> bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e)
      /\ (length rx <= 2)%nat /\ live_bytes rx <= 0x14000;
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
  kl_atop : ld_atop L = alloc_top (m_vmmaps mo);
  (* LPS : every mapping is free of the reserved ledger (placement grants only
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

(* The ledger [init_model] starts from: the image's reservations, then the vDSO
   pair under [min mbase (sp - stack_max_size)], far above any brk start. *)
Lemma KL_resv_init : forall segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  mmap_base_min <= bv_unsigned mbase -> sp_window_lo <= bv_unsigned sp ->
  let h := m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp) in
  (exists R0 rx, vm_reserved h = R0 ++ rx /\ map wwZ (segments_reserved segs) = map wwZ R0
      /\ (forall e, In e R0 -> ehi e <= bv_unsigned (vm_start_brk h))
      /\ (forall e, In e rx -> bv_unsigned (vm_start_brk h) + 4 * PGSZ <= elo e)
      /\ (length rx <= 2)%nat /\ live_bytes rx <= 0x14000)
  /\ (forall e, In e (vm_reserved h) ->
        ehi e <= bv_unsigned (vm_start_brk h) \/ bv_unsigned (vm_start_brk h) + 4 * PGSZ <= elo e)
  /\ live_bytes (vm_reserved h) <= live_bytes (segments_reserved segs) + 0x14000.
Proof.
  intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hlow Hmb Hsp h.
  set (T := page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))).
  assert (ER : vm_reserved h = segments_reserved segs ++ vdso_reserved (in_kernel inp) T)
    by (subst h T; rewrite m_vmmaps_init_model; reflexivity).
  assert (ESB : vm_start_brk h = brk0) by (subst h; rewrite m_vmmaps_init_model; reflexivity).
  pose proof (vdso_len_bounds (in_kernel inp)) as VL.
  pose proof (bv_unsigned_in_range 64 mbase) as RM. unfold bv_modulus in RM. cbn in RM.
  assert (HT : Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size) - 4096 < T
               <= Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  { subst T. unfold page_round_down_Z, page_size. Z.div_mod_to_equations. lia. }
  assert (HX : forall e, In e (vdso_reserved (in_kernel inp) T) -> bv_unsigned brk0 + 4 * PGSZ <= elo e).
  { intros [a n] Hin. destruct (vdso_reserved_above (in_kernel inp) T a n ltac:(unfold two_pow_64; lia) Hin) as [A1 _].
    unfold elo. cbn [fst]. unfold mmap_base_min, sp_window_lo, PGSZ, page_size, stack_max_size in *. lia. }
  assert (HR : forall e, In e (segments_reserved segs) -> ehi e <= bv_unsigned brk0)
    by (intros e He; pose proof (reserved_top_ge_kl _ _ He); lia).
  destruct (vdso_reserved_size (in_kernel inp) T) as [LN LB].
  rewrite ER, ESB. split; [|split].
  - exists (segments_reserved segs), (vdso_reserved (in_kernel inp) T).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HR|]. split; [exact HX|]. split; assumption.
  - intros e He. apply in_app_or in He as [He|He]; [left; exact (HR e He)| right; exact (HX e He)].
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

(* with_vdso keeps every field KL reads (maps, kernel, halt state); minv does not
   read the vDSO field. The run starts at with_vdso of init_model (TopLevel mo0 at ). *)
Lemma KL_with_vdso : forall L pbrk v mo, KL L pbrk mo -> KL L pbrk (with_vdso v mo).
Proof. intros L pbrk v mo K. destruct K. constructor; assumption. Qed.

(* KL at the launch, from KL_resv_init and KL_vin_init. The one launch proof of
   this lineage's ledger: Spec/ModelInv GI_init and Spec/LB_Init QI_init both apply it. R is the ledger's reserved
   list, given as an equation so that callers can pass Lib/Image reservedZ (which unfolds to map wwZ). *)
Lemma KL_init : forall segs brk0 mbase sp lim inp R atop pbrk,
  R = map wwZ (segments_reserved segs) ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  atop = bv_unsigned sp - stack_max_size ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  mmap_base_min <= bv_unsigned mbase ->
  in_channel_reader inp = true ->
  KL (led_init R atop) pbrk (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros segs brk0 mbase sp lim inp R atop pbrk ER Hvb Hpos Hsp Eatop Hceil Hlow Hmb Hrdr.
  pose proof Hvb as (Hlo & Hhi & Hal).
  pose proof alloc_ceiling_lo_val as Hclo.
  destruct (KL_resv_init segs brk0 mbase sp lim inp Hvb Hlow Hmb (proj1 Hsp)) as (Kres & Ktop & _).
  pose proof (KL_vin_init (segments_reserved segs) brk0 mbase sp lim inp) as Kvin.
  assert (Esb : vm_start_brk (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) = brk0) by reflexivity.
  assert (Ebk : vm_brk (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) = brk0) by reflexivity.
  assert (Emp : vm_maps (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) = []) by reflexivity.
  assert (Esp : vm_init_sp (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) = sp) by reflexivity.
  constructor.
  - apply minv_init; [exact Hsp| exact Hrdr].
  - reflexivity.
  - rewrite Emp. split; [intros e []| apply pwdisj_nil].
  - destruct Kres as (R0 & rx & E1 & E2 & E3 & E4 & E5 & E6). exists R0, rx.
    split; [exact E1|]. split; [cbn [ld_resv led_init]; rewrite ER; exact E2|].
    split; [exact E3|]. split; [exact E4|]. split; [exact E5| exact E6].
  - exact Ktop.
  - cbn [ld_atop led_init]. rewrite Esb, Ebk. unfold PGSZ in *. unfold page_size in Hal.
    unfold alloc_ceiling_lo, sp_window_lo, stack_max_size in *. lia.
  - intros b l [].
  - intros b l k [].
  - apply List.NoDup_nil.
  - intros b l H. discriminate.
  - cbn [ld_brk led_init ld_brkreg]. split; [rewrite Esb, Ebk; reflexivity| reflexivity].
  - cbn [ld_atop led_init]. unfold alloc_top. rewrite Esp. exact Eatop.
  - intros e He. rewrite Emp in He. destruct He.
  - exact Kvin.
Qed.

Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.


Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.


Lemma vm_only_init_sp : forall m m', vm_only m m' -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m).
Proof. intros m m' (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma vm_only_alloc_top : forall m m', vm_only m m' -> alloc_top (m_vmmaps m') = alloc_top (m_vmmaps m).
Proof. intros m m' H. unfold alloc_top. rewrite (vm_only_init_sp _ _ H). reflexivity. Qed.
Lemma alloc_top_of_init_sp : forall h h', vm_init_sp h' = vm_init_sp h -> alloc_top h' = alloc_top h.
Proof. intros h h' H. unfold alloc_top. rewrite H. reflexivity. Qed.

Lemma KL_atop_range : forall L pbrk mo, KL L pbrk mo -> alloc_ceiling_lo <= ld_atop L <= alloc_ceiling.
Proof. intros L pbrk mo HK. rewrite (kl_atop _ _ _ HK). apply minv_alloc_top. exact (kl_minv _ _ _ HK). Qed.
Lemma KL_atop_lt : forall L pbrk mo, KL L pbrk mo -> 0 < ld_atop L < 2^63.
Proof. intros L pbrk mo HK. pose proof (KL_atop_range _ _ _ HK). rewrite alloc_ceiling_val, alloc_ceiling_lo_val in *. lia. Qed.
