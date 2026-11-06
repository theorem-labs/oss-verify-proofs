(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Mem Cells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Notation w64 z := (Z_to_bv 64 z) (only parsing).
Notation b8 z := (Z_to_bv 8 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record chunk_hdr := CH { ch_state : Z; ch_b1 : Z; ch_size : Z; ch_ctx : Z }.

Definition size_hi (n : Z) : Z := Z.shiftr n 32.
Definition size_lo (n : Z) : Z := n mod 2^32.

Definition chunk_hdr_cells (h : chunk_hdr) : list cell :=
  [ C1 (b8 (ch_state h)); C1 (b8 (ch_b1 h)); C2 (w64 (size_hi (ch_size h))); C4 (w64 (ch_size h)); C8 (w64 (ch_ctx h)) ].

Lemma chunk_hdr_size : forall h, cells_size (chunk_hdr_cells h) = 16%nat. Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_ctx (tid id : Z) : Z := Z.lor (Z.shiftl tid 32) id.
Definition hdr_live (n id : Z) : chunk_hdr := CH CHUNK_ALLOCATED kHdrByte1Malloc (user_size n) (alloc_ctx kMainTid id).
Definition hdr_quarantined (n id : Z) : chunk_hdr := CH CHUNK_QUARANTINE kHdrByte1Malloc (user_size n) (alloc_ctx kMainTid id).
Definition hdr_recycled (n id : Z) : chunk_hdr := CH CHUNK_INVALID kHdrByte1Malloc (user_size n) (alloc_ctx kMainTid id).
(* [comment removed for export] *)
Definition free_ctx (tid id : Z) : Z := Z.lor (Z.shiftl tid 32) id.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition used_size_decode (hi16 lo32 : Z) : Z := Z.lor (Z.shiftl hi16 32) lo32.
Lemma used_size_roundtrip : forall n, 0 <= n < 2^48 ->
  used_size_decode (size_hi n mod 2^16) (size_lo n) = n.
Proof.
  intros n Hn. unfold used_size_decode, size_hi, size_lo.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (n / 2^32) (2^16)).
  2:{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32*2^16) with (2^48). lia. }
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor.
    + pose proof (Z_div_mod_eq_full n (2^32)). lia.
    + apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.ltb_spec i 32).
      * rewrite Z.mul_pow2_bits_low by lia. reflexivity.
      * rewrite (Z.mod_pow2_bits_high n 32 i) by lia. apply Bool.andb_false_r.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec i 32).
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.mod_pow2_bits_high n 32 i) by lia. apply Bool.andb_false_r.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b1_alloc_type (b : Z) : Z := Z.land b 3.
Definition b1_lsan_tag (b : Z) : Z := Z.land (Z.shiftr b 2) 3.
Definition b1_align_log (b : Z) : Z := Z.land (Z.shiftr b 4) 7.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b1_after_alloc (old : Z) : Z := Z.land (Z.lor (Z.land (Z.lor (Z.land old (Z.lnot 3)) 1) 0x8f) 0x10) (Z.lnot 0xc).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint le_enc (k : nat) (v : Z) : list Z :=
  match k with O => [] | S k' => v mod 256 :: le_enc k' (Z.shiftr v 8) end.
Fixpoint le_dec (bs : list Z) : Z :=
  match bs with [] => 0 | b :: bs' => b + 256 * le_dec bs' end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition chunk_hdr_bytes (h : chunk_hdr) : list Z :=
  [ch_state h mod 256; ch_b1 h mod 256] ++ le_enc 2 (size_hi (ch_size h)) ++ le_enc 4 (ch_size h) ++ le_enc 8 (ch_ctx h).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hdr_dec_state (bs : list Z) : Z := nth 0 bs 0.
Definition hdr_dec_b1 (bs : list Z) : Z := nth 1 bs 0.
Definition hdr_dec_size_hi (bs : list Z) : Z := le_dec (firstn 2 (skipn 2 bs)).
Definition hdr_dec_size_lo (bs : list Z) : Z := le_dec (firstn 4 (skipn 4 bs)).
Definition hdr_dec_size (bs : list Z) : Z := used_size_decode (hdr_dec_size_hi bs) (hdr_dec_size_lo bs).
Definition hdr_dec_ctx (bs : list Z) : Z := le_dec (skipn 8 bs).
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record large_hdr := LH { lh_magic : Z; lh_chunk : Z }.
Definition large_hdr_cells (h : large_hdr) : list cell := [ C8 (w64 (lh_magic h)); C8 (w64 (lh_chunk h)) ].
Definition large_hdr_set (chunk_beg : Z) : large_hdr := LH kAllocBegMagic chunk_beg.
Definition large_hdr_cleared (chunk_beg : Z) : large_hdr := LH 0 chunk_beg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record sec_hdr := SH { sh_map_beg : Z; sh_map_size : Z; sh_size : Z; sh_chunk_idx : Z }.
Definition sec_hdr_cells (h : sec_hdr) : list cell :=
  [ C8 (w64 (sh_map_beg h)); C8 (w64 (sh_map_size h)); C8 (w64 (sh_size h)); C8 (w64 (sh_chunk_idx h)) ].
Lemma sec_hdr_size : forall h, cells_size (sec_hdr_cells h) = 32%nat. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition sec_hdr_of (map_beg n i : Z) : sec_hdr := SH map_beg (map_size n) (needed_size2 n) i.
(* [comment removed for export] *)
Definition sec_map_end (map_beg n : Z) : Z := map_beg + map_size n.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record qbatch := QB { qb_next : Z; qb_size : Z; qb_ptrs : list Z }.
Definition qb_count (b : qbatch) : Z := Z.of_nat (length (qb_ptrs b)).
(* [comment removed for export] *)
Definition qbatch_cells (b : qbatch) : list cell :=
  [ C8 (w64 (qb_next b)); C8 (w64 (qb_size b)); C8 (w64 (qb_count b)) ] ++ map (fun p => C8 (w64 p)) (qb_ptrs b).
Definition off_qb_next : Z := 0.
Definition off_qb_size : Z := 8.
Definition off_qb_count : Z := 16.
Definition off_qb_batch (i : Z) : Z := 24 + 8 * i.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qbatch_inv (b : qbatch) (used_size_of : Z -> Z) : Prop :=
  1 <= qb_count b <= kQuarantineBatchCount /\
  qb_size b = kQuarantineBatchBytes + fold_right (fun p acc => used_size_of p + acc) 0 (qb_ptrs b).

(* [comment removed for export] *)
Record qcache := QC { qc_n : Z; qc_first : Z; qc_last : Z; qc_bytes : Z }.
Definition qcache_cells (q : qcache) : list cell :=
  [ C8 (w64 (qc_n q)); C8 (w64 (qc_first q)); C8 (w64 (qc_last q)); C8 (w64 (qc_bytes q)) ].
Definition qcache_empty : qcache := QC 0 0 0 0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint qlist_linked (addrs : list Z) (bs : list qbatch) : Prop :=
  match addrs, bs with
  | [], [] => True
  | [a], [b] => qb_next b = 0
  | a :: (a' :: _) as addrs', b :: bs' => qb_next b = a' /\ qlist_linked addrs' bs'
  | _, _ => False
  end.
Definition qcache_inv (q : qcache) (addrs : list Z) (bs : list qbatch) : Prop :=
  length addrs = length bs /\ qc_n q = Z.of_nat (length bs) /\
  qc_first q = hd 0 addrs /\ qc_last q = last addrs 0 /\
  qc_bytes q = fold_right (fun b acc => qb_size b + acc) 0 bs /\
  qlist_linked addrs bs.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record region_info := RI {
  ri_mutex : Z; ri_sems : Z; ri_num_freed : Z; ri_mapped_free_array : Z; ri_allocated_user : Z; ri_allocated_meta : Z;
  ri_mapped_user : Z; ri_mapped_meta : Z; ri_rand_state : Z; ri_exhausted : Z;
  ri_n_allocated : Z; ri_n_freed : Z; ri_rtoi0 : Z; ri_rtoi1 : Z; ri_rtoi2 : Z; ri_rtoi3 : Z }.
Definition off_ri_mutex : Z := 0.
Definition off_ri_num_freed : Z := 16.
Definition off_ri_mapped_free_array : Z := 24.
Definition off_ri_allocated_user : Z := 32.
Definition off_ri_allocated_meta : Z := 40.
Definition off_ri_mapped_user : Z := 48.
Definition off_ri_mapped_meta : Z := 56.
Definition off_ri_exhausted : Z := 68.
Definition off_ri_n_allocated : Z := 72.
Definition off_ri_n_freed : Z := 80.
Definition off_ri_rtoi : Z := 88.
Definition region_info_cells (r : region_info) : list cell :=
  [ C8 (w64 (ri_mutex r)); C8 (w64 (ri_sems r)); C8 (w64 (ri_num_freed r)); C8 (w64 (ri_mapped_free_array r));
    C8 (w64 (ri_allocated_user r)); C8 (w64 (ri_allocated_meta r)); C8 (w64 (ri_mapped_user r)); C8 (w64 (ri_mapped_meta r));
    C4 (w64 (ri_rand_state r)); C1 (b8 (ri_exhausted r)); CB 3 [b8 0; b8 0; b8 0];
    C8 (w64 (ri_n_allocated r)); C8 (w64 (ri_n_freed r));
    C8 (w64 (ri_rtoi0 r)); C8 (w64 (ri_rtoi1 r)); C8 (w64 (ri_rtoi2 r)); C8 (w64 (ri_rtoi3 r)); CB 8 (repeat (b8 0) 8) ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition region_info_zero : region_info := RI 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0.
(* [comment removed for export] *)
Definition region_wf (c : Z) (r : region_info) : Prop :=
  ri_mutex r = 0 /\ ri_sems r = 0 /\ ri_allocated_meta r = 0 /\ ri_mapped_meta r = 0 /\ ri_exhausted r = 0 /\
  0 <= ri_allocated_user r <= ri_mapped_user r /\ ri_mapped_user r mod kUserMapSize = 0 /\
  ri_mapped_user r <= kFreeArrayOffset /\
  (ri_mapped_user r - ri_allocated_user r) < class_size c /\      (* [comment removed for export] *)
  ri_allocated_user r mod class_size c = 0 /\
  0 <= ri_num_freed r /\ 4 * ri_num_freed r <= ri_mapped_free_array r /\ ri_mapped_free_array r mod kFreeArrayMapSize = 0 /\
  ri_mapped_free_array r <= kFreeArraySize.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record per_class := PC { pc_count : Z; pc_max_count : Z; pc_class_size : Z; pc_chunks : list Z (* [comment removed for export] *) }.
Definition off_pc_count : Z := 0.
Definition off_pc_max_count : Z := 4.
Definition off_pc_class_size : Z := 8.
Definition off_pc_chunk (i : Z) : Z := 16 + 4 * i.
Definition per_class_cells (p : per_class) : list cell :=
  [ C4 (w64 (pc_count p)); C4 (w64 (pc_max_count p)); C8 (w64 (pc_class_size p)) ] ++ map (fun c => C4 (w64 c)) (pc_chunks p).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition per_class_inited (c : Z) (count : Z) (chunks : list Z) : per_class := PC count (max_count c) (class_size c) chunks.
Definition per_class_wf (c : Z) (p : per_class) : Prop :=
  pc_max_count p = max_count c /\ pc_class_size p = class_size c /\ 0 <= pc_count p <= pc_max_count p /\ length (pc_chunks p) = 16%nat.
(* [comment removed for export] *)
Definition off_cache_stats : Z := 2560.
Definition off_cache_stat_allocated : Z := 2576.   (* [comment removed for export] *)
Definition off_cache_stat_mapped : Z := 2584.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition off_th_context : Z := 0.          (* [comment removed for export] *)
Definition off_th_stack_top : Z := 8.        (* [comment removed for export] *)
Definition off_th_stack_bottom : Z := 16.    (* [comment removed for export] *)
Definition off_th_stack_switching : Z := 40. (* [comment removed for export] *)
Definition off_th_qcache : Z := 80.          (* [comment removed for export] *)
Definition off_th_qcache_n : Z := 80.
Definition off_th_qcache_first : Z := 88.
Definition off_th_qcache_last : Z := 96.
Definition off_th_qcache_bytes : Z := 104.
Definition off_th_alloc_cache : Z := 208.    (* [comment removed for export] *)
Definition off_th_per_class (c : Z) : Z := off_th_alloc_cache + kPerClassSize * c.
Definition off_th_cache_stats : Z := 2768.   (* [comment removed for export] *)
Definition off_th_cache_allocated : Z := 2784.
Definition off_th_cache_mapped : Z := 2792.
Definition off_th_stats : Z := 2800.         (* [comment removed for export] *)
Definition off_st_mallocs : Z := 0.
Definition off_st_malloced : Z := 8.
Definition off_st_malloced_redzones : Z := 16.
Definition off_st_frees : Z := 24.
Definition off_st_freed : Z := 32.
Definition off_st_real_frees : Z := 40.
Definition off_st_really_freed : Z := 48.
Definition off_st_reallocs : Z := 56.
Definition off_st_realloced : Z := 64.
Definition off_st_mmaps : Z := 72.
Definition off_st_mmaped : Z := 80.
Definition off_st_munmaps : Z := 88.
Definition off_st_munmaped : Z := 96.
Definition off_st_malloc_large : Z := 104.
Definition off_st_malloced_by_size (c : Z) : Z := 112 + 8 * c.
Definition off_th_unwinding : Z := 3168.     (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stack_top_of (sp0 : Z) : Z := round_up (sp0 - 0xa0) 4096.
Definition stack_bottom_of (sp0 : Z) : Z := stack_top_of sp0 - 0x800000.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_bst_trace : Z := 0.
Definition off_bst_size : Z := 8.
Definition off_bst_tag : Z := 12.
Definition off_bst_buffer : Z := 16.
Definition off_bst_top_frame_bp : Z := 2056.
(* [comment removed for export] *)
Definition trace2 (icpt_pc ra : Z) : list Z := [icpt_pc; ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record depot_node := DN { dn_hash : Z; dn_link : Z; dn_store_id : Z }.
Definition depot_node_cells (d : depot_node) : list cell := [ C8 (w64 (dn_hash d)); C4 (w64 (dn_link d)); C4 (w64 (dn_store_id d)) ].
(* [comment removed for export] *)
Definition depot_node_addr (map1_block : Z) (id : Z) : Z := map1_block + kDepotNodeSize * (id mod 2^16).
Definition depot_bucket_addr (theDepot h : Z) : Z := theDepot + 4 * (h mod 2^20).
(* [comment removed for export] *)
Definition stack_store_words (size tag : Z) (trace : list Z) : list Z := Z.lor size (Z.shiftl tag 8) :: trace.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shadow_const (sh : Z -> Z) (a len v : Z) : Prop :=
  forall i, 0 <= i < Z.shiftr len 3 -> sh (mem_to_shadow a + i) = v.
(* [comment removed for export] *)
Definition shadow_live_user (sh : Z -> Z) (u n : Z) : Prop :=
  (forall i, 0 <= i < n / 8 -> sh (mem_to_shadow u + i) = 0) /\
  (n mod 8 <> 0 -> sh (mem_to_shadow u + n / 8) = n mod 8).
(* [comment removed for export] *)
Definition shadow_quarantined_user (sh : Z -> Z) (u n : Z) : Prop :=
  forall i, 0 <= i < round_up n 8 / 8 -> sh (mem_to_shadow u + i) = kAsanHeapFreeMagic.
(* [comment removed for export] *)
Definition shadow_poisoned (sh : Z -> Z) (a len : Z) : Prop :=
  forall i, 0 <= i < len / 8 -> sh (mem_to_shadow a + i) = kAsanHeapLeftRedzoneMagic.
