(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.Prelim. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.Monad. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import PState.
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
  (* the ledger's reserved entries are entries of the
     WHOLE vm_reserved (image part R0 and, where the package's malloc model reserves it, the vDSO pair rx), not R0
     only. Read only through KEv.KL_resv_in, which this inclusion is. *)
  kl_resv : exists R0 rx, vm_reserved (m_vmmaps mo) = R0 ++ rx /\ incl (ld_resv L) (map wwZ (R0 ++ rx))
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
(* (B1): the launch's ledger may be any sub-list of the launch's whole vm_reserved; KL_init (the image's part, as
   before) and KL_init_full (the image's part and the vDSO pair, end of file) are its two cases. *)
Lemma KL_init_gen : forall segs brk0 mbase sp lim inp R atop pbrk,
  incl R (map wwZ (vm_reserved (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)))) ->
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
    split; [exact E1|]. split; [cbn [ld_resv led_init]; rewrite <- E1; exact ER|].
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
  intros segs brk0 mbase sp lim inp R atop pbrk ER. apply KL_init_gen.
  rewrite vm_reserved_init_model, map_app, ER. apply incl_appl. apply incl_refl.
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

(* port727 route (A): what the kernel ledger says about the vDSO
   pair, exported for the run-level (A1) lift. Every mapping is free of vm_reserved (kl_mres) and the pair is part
   of vm_reserved (kl_vin), so a mapping, and any non-empty range the mappings cover (an mprotect'd range may span
   several entries), misses the pair. kl_resv is unchanged: the pair stays out of the heap's ghost ledger. *)
Lemma kl_map_off_vdso : forall L pbrk mo aw nw,
  KL L pbrk mo -> In (aw, nw) (vm_maps (m_vmmaps mo)) ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw = true.
Proof.
  intros L pbrk mo aw nw K Hin.
  pose proof (kl_mres _ _ _ K (aw, nw) Hin) as HF. cbn [fst snd] in HF.
  apply LinuxProcessSemantics.LinuxProcessSem.State.region_free_intro. intros a sz Ha.
  exact (LinuxProcessSemantics.LinuxProcessSem.State.region_free_In _ _ _ _ _ HF (kl_vin _ _ _ K _ Ha)).
Qed.

Lemma vdso_top_lt_kl : forall h, vdso_top h < two_pow_64.
Proof.
  intros h. unfold vdso_top, mmap_top.
  pose proof (page_round_down_Z_le (Z.min (bv_unsigned (vm_mmap_base h)) (page_round_down_Z (alloc_top h)))).
  pose proof (bv_unsigned_in_range 64 (vm_mmap_base h)) as R. unfold bv_modulus in R. cbn in R.
  unfold two_pow_64. lia.
Qed.

Lemma kl_cov_off_vdso : forall L pbrk mo lo n,
  KL L pbrk mo -> 0 < bv_unsigned n ->
  wcov (vm_maps (m_vmmaps mo)) (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) lo n = true.
Proof.
  intros L pbrk mo lo n K Hn C.
  apply LinuxProcessSemantics.LinuxProcessSem.State.region_free_intro. intros a sz Ha.
  pose proof (vdso_reserved_nonzero _ _ a sz (vdso_top_lt_kl _) Ha) as Hsz.
  destruct (iv_overlap lo n a sz) eqn:O; [|reflexivity]. exfalso.
  unfold iv_overlap in O. apply andb_true_iff in O as [O1 O2]. apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
  destruct (C (Z.max (bv_unsigned lo) (bv_unsigned a)) ltac:(lia)) as [[ea en] [He Hx]].
  pose proof (kl_mres _ _ _ K (ea, en) He) as HF. cbn [fst snd] in HF.
  pose proof (LinuxProcessSemantics.LinuxProcessSem.State.region_free_In _ _ _ _ _ HF (kl_vin _ _ _ K _ Ha)) as HO.
  unfold iv_overlap in HO. unfold elo, ehi in Hx. cbn [fst snd] in Hx.
  apply andb_false_iff in HO as [HO|HO]; apply Z.ltb_ge in HO; lia.
Qed.

Lemma kl_sub_off_vdso : forall L pbrk mo aw nw lo n,
  KL L pbrk mo -> In (aw, nw) (vm_maps (m_vmmaps mo)) -> 0 < bv_unsigned n ->
  bv_unsigned aw <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned aw + bv_unsigned nw ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) lo n = true.
Proof.
  intros L pbrk mo aw nw lo n K Hin Hn H1 H2.
  apply (kl_cov_off_vdso L pbrk mo lo n K Hn).
  intros x Hx. exists (aw, nw). split; [exact Hin|]. unfold elo, ehi. cbn [fst snd]. lia.
Qed.

(* The ledger's own regions: every group and every meta area the heap's ghost ledger records is a mapping
   (kl_groups / kl_metas), so it misses the pair; a sub-range of one (an mprotect'd part) by kl_sub_off_vdso. *)
Lemma kl_group_off_vdso : forall L pbrk mo b l,
  KL L pbrk mo -> In (b, l) (ld_groups L) ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (wz b) (wz (mmap_len l)) = true.
Proof.
  intros L pbrk mo b l K Hin.
  destruct (kl_groups _ _ _ K b l Hin) as (_ & _ & _ & _ & Hm & _).
  exact (kl_map_off_vdso L pbrk mo _ _ K Hm).
Qed.

Lemma kl_meta_off_vdso : forall L pbrk mo b l k,
  KL L pbrk mo -> In (b, l, k) (ld_metas L) ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (wz b) (wz (mmap_len l)) = true.
Proof.
  intros L pbrk mo b l k K Hin.
  destruct (kl_metas _ _ _ K b l k Hin) as (_ & _ & _ & _ & _ & _ & Hm & _).
  exact (kl_map_off_vdso L pbrk mo _ _ K Hm).
Qed.

(* The launch's kernel build, stack top and mmap base, read off the model. KL does not hold them; no node step
   writes them (Lib/Nodes vm_only keeps all three), and init_model sets them from the launch. With them the
   model's [vdso_top] is the run's own top (Run.vdso_segments' [top]), so the lemmas above speak about the
   pair the run's segment list carries. *)
Definition KLaunch (kb : KernelBuild) (sp mb : word) (mo : Model) : Prop :=
  m_kernel mo = kb /\ vm_init_sp (m_vmmaps mo) = sp /\ vm_mmap_base (m_vmmaps mo) = mb.

Lemma KLaunch_init : forall reserved brk0 mbase sp lim inp,
  KLaunch (in_kernel inp) sp mbase (init_model reserved brk0 mbase sp lim inp).
Proof. intros. unfold KLaunch. rewrite m_vmmaps_init_model. repeat split; reflexivity. Qed.

Lemma KLaunch_vm_only : forall kb sp mb mo mo', vm_only mo mo' -> KLaunch kb sp mb mo -> KLaunch kb sp mb mo'.
Proof.
  intros kb sp mb mo mo' (_ & _ & _ & _ & _ & _ & Hsp & _ & Hk & Hmb & _) (E1 & E2 & E3).
  unfold KLaunch. rewrite Hk, Hsp, Hmb. split; [exact E1| split; [exact E2| exact E3]].
Qed.

Lemma KLaunch_with_vdso : forall kb sp mb v mo, KLaunch kb sp mb mo -> KLaunch kb sp mb (with_vdso v mo).
Proof. intros kb sp mb v mo H. exact H. Qed.

Lemma KLaunch_vdso_top : forall kb sp mb mo, KLaunch kb sp mb mo ->
  vdso_top (m_vmmaps mo)
  = page_round_down_Z (Z.min (bv_unsigned mb) (page_round_down_Z (bv_unsigned sp - stack_max_size))).
Proof. intros kb sp mb mo (_ & E2 & E3). unfold vdso_top, mmap_top, alloc_top. rewrite E2, E3. reflexivity. Qed.

(* The run's forms: the pair under the launch's own top. *)
Lemma kl_map_off_vdso_run : forall L pbrk mo kb sp mb aw nw,
  KL L pbrk mo -> KLaunch kb sp mb mo -> In (aw, nw) (vm_maps (m_vmmaps mo)) ->
  region_free (vdso_reserved kb
     (page_round_down_Z (Z.min (bv_unsigned mb) (page_round_down_Z (bv_unsigned sp - stack_max_size))))) aw nw = true.
Proof.
  intros L pbrk mo kb sp mb aw nw K H Hin. rewrite <- (KLaunch_vdso_top kb sp mb mo H).
  destruct H as (E1 & _ & _). rewrite <- E1. exact (kl_map_off_vdso L pbrk mo aw nw K Hin).
Qed.

(* The pair as a decision's avoid list (Lib/Decode [avoids] reads [lo, hi) ranges): the carrier route (A) passes
   through the mmap decision. [kl_vdso_avoid_covered] is the
   premise Lib/Decode nstep_dec_mmap asks of an avoid list: each range lies in the ledger or a mapping. *)
Definition vdso_top_of (sp mb : word) : Z :=
  page_round_down_Z (Z.min (bv_unsigned mb) (page_round_down_Z (bv_unsigned sp - stack_max_size))).
Definition vdso_avoid_of (kb : KernelBuild) (sp mb : word) : list (Z * Z) :=
  map (fun e => (elo e, ehi e)) (vdso_reserved kb (vdso_top_of sp mb)).

Lemma kl_vdso_avoid_covered : forall L pbrk mo kb sp mb,
  KL L pbrk mo -> KLaunch kb sp mb mo ->
  Forall (covered (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) (vdso_avoid_of kb sp mb).
Proof.
  intros L pbrk mo kb sp mb K H.
  apply Forall_forall. intros iv Hiv. unfold vdso_avoid_of in Hiv.
  apply in_map_iff in Hiv as [[a n] [<- Hin]].
  unfold vdso_top_of in Hin. rewrite <- (KLaunch_vdso_top kb sp mb mo H) in Hin.
  destruct H as (E1 & _ & _). rewrite <- E1 in Hin.
  exists a, n. split; [apply in_or_app; left; exact (kl_vin _ _ _ K _ Hin)|].
  unfold elo, ehi. cbn [fst snd]. lia.
Qed.

Lemma kl_cov_off_vdso_run : forall L pbrk mo kb sp mb lo n,
  KL L pbrk mo -> KLaunch kb sp mb mo -> 0 < bv_unsigned n ->
  wcov (vm_maps (m_vmmaps mo)) (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) ->
  region_free (vdso_reserved kb
     (page_round_down_Z (Z.min (bv_unsigned mb) (page_round_down_Z (bv_unsigned sp - stack_max_size))))) lo n = true.
Proof.
  intros L pbrk mo kb sp mb lo n K H Hn C. rewrite <- (KLaunch_vdso_top kb sp mb mo H).
  destruct H as (E1 & _ & _). rewrite <- E1. exact (kl_cov_off_vdso L pbrk mo lo n K Hn C).
Qed.

(* the vDSO pair in the malloc model's own format,
   (base, LENGTH) entries (Spec/Malloc iv_disjoint / ranges_free; wwZ), as the package's ps_init list takes it:
   ps_init (reservedZ psegs ++ vdso_resv_of (in_kernel inp) sp0 mbase). [vdso_avoid_of] above is the (lo, hi)
   form Lib/Decode's [avoids] reads; the two name the same two entries. *)
Definition vdso_resv_of (kb : KernelBuild) (sp mb : word) : list (Z * Z) :=
  map wwZ (vdso_reserved kb (vdso_top_of sp mb)).

Lemma KL_init_full : forall segs brk0 mbase sp lim inp R atop pbrk,
  R = map wwZ (segments_reserved segs) ++ vdso_resv_of (in_kernel inp) sp mbase ->
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
  atop = bv_unsigned sp - stack_max_size ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  mmap_base_min <= bv_unsigned mbase ->
  in_channel_reader inp = true ->
  KL (led_init R atop) pbrk (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros segs brk0 mbase sp lim inp R atop pbrk ER. apply KL_init_gen.
  rewrite vm_reserved_init_model, map_app, ER.
  rewrite (KLaunch_vdso_top _ _ _ _ (KLaunch_init (segments_reserved segs) brk0 mbase sp lim inp)).
  unfold vdso_resv_of, vdso_top_of. apply incl_refl.
Qed.
