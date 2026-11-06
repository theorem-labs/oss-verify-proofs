(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree MallocFacts_A MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import Malloc_fp AllocSlot_iface F_malloc_join MallocHINV.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocKit_A2 F_malloc_bigw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Definition big_final (st3 : mstate) (g : aptr) (rid : N) (n : Z) : mstate :=
  let needed := n + IB + UNIT in
  let st4 := upd_meta g (fun mr =>
               m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
               (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
  let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
  let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).
End FINAL.

Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^32 ->
  malloc_core full_lay st1 n =
    SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
      if is_err r then ret (st1, None) else
      let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
      alloc_meta (step_seq st2) (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
        | Some g => ret (big_final st3 g rid n, Some (g, 0))
        end) (ret (st1, None))).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Hn. unfold malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma unk_agree_transfer st st' o m m' :
  unk_agree st o m ->
  (forall rid r, (s_regions st') !! rid = Some r -> r_kind r = RKGroup ->
     ((s_regions st) !! rid = Some r /\ get_shadow st' rid = get_shadow st rid /\
       (forall off, grp_hdr_cov st rid off -> grp_hdr_cov st' rid off) /\
       (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st rid) off = Unknown h ->
          ~ grp_hdr_cov st' rid off -> m' (wa (r_base r + off)) = m (wa (r_base r + off))))
     \/ (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st' rid) off = Unknown h -> grp_hdr_cov st' rid off)) ->
  unk_agree st' o m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros UA H rid r off h Hr Hk Ho Hc NG.
  destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
  - rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
  - exfalso. apply NG. eapply NEW; eauto.
Qed.

Lemma grp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros EG (b & gh & Hb & E & R). exists b, gh. rewrite EG. auto. Qed.

Lemma munmap_answer_ok_range a : match a with RgErr e => 1 <= e <= 4095 | RgDone _ => True end -> munmap_answer_ok (range_val a) = true.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  destruct a as [e|b]; cbn [range_val]; intros He.
  - unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
    replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (2 ^ 64 - e =? 0); reflexivity.
  - reflexivity.
Qed.

Lemma mmap_answer_ok_err live len e : 1 <= e <= 4095 -> mmap_answer_ok live len (neg_errno e) = true /\ is_err (neg_errno e) = true.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
  - replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - apply Z.ltb_lt. lia.
Qed.

Lemma mmap_answer_ok_addr live len xa : 0 <= len ->
  mmap_addr_ok len [] xa = true -> mmap_answer_ok live len xa = true ->
  0 < xa /\ xa mod 4096 = 0 /\ xa + round_up_pg len <= alloc_ceiling /\ ranges_free live xa (round_up_pg len) = true /\ is_err xa = false.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros L0 A B. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. destruct A as [[[A1 A2] A3] _].
  apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
  change page_size with 4096 in A1.
  unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
  assert (NE : is_errno_form xa = false).
  { unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; unfold OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in A3; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia). reflexivity. }
  destruct B as [B|B]; [rewrite NE in B; discriminate|].
  rewrite !Bool.andb_true_iff in B. destruct B as [[[_ _] _] B4].
  repeat split; auto. unfold is_err, TWO64. apply Z.ltb_ge. unfold OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in A3; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
Qed.

Lemma brk_link_ps_ext st st' s :
  c_brk (ctx st') = c_brk (ctx st) ->
  (forall rid off, c_brk (ctx st) = BrkLive rid off -> conc st' (rid, off) = conc st (rid, off)) ->
  brk_link_ps st s -> brk_link_ps st' s.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
  rewrite (EC rid off eq_refl). exact BL.
Qed.

Lemma munch_of_pointwise (lo hi : Z) (m m' : mem) :
  0 <= lo -> hi <= 2^64 ->
  (forall a, 0 <= a < 2^64 -> (a < lo \/ hi <= a) -> m' (wa a) = m (wa a)) -> munch [(lo, hi)] m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.

Lemma cell_read_hh0 st rid off : (s_shadow st) !! rid = None -> 0 <= off ->
  cell_read (get_shadow (hdr_havoc (rid, 0) st) rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
  destruct (Z.eq_dec (off / 16) 0) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
    replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
  - rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
    replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma round_up_pg_4115 n : 0 <= n -> round_up_pg (n + IB + UNIT) = (n + 4115) / 4096 * 4096.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Section BIG.
End BIG.
End WithCeiling0.
