(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateParams DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateInitLib RefDeflSafeI1 RefDeflSafeI4 RefDeflSafeI5b RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel DeflateTaintRelG DeflateTaintBlkG DeflateTaintCallG DeflateTaintCoreG DeflateTaintInit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateParamsDD DeflateParamsZ1 DeflateParamsZ4 DeflateParamsDD1 DeflateParamsT1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState Inflate HarnessSmall HarnessLarge ZApiInst ZApiInstL ZTaint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dinit9_of (g : N -> Z -> Z) : deflate_state :=
  dFg 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) dinit_cs 1 15 8 9 0 8.

(* [comment removed for export] *)
Definition dinit9_zr : ZRet := zret_of_cs (ds_strm (dinit9_of (fun _ => g0))) Z_OK.

Lemma di_bad_9 : di_bad 9 Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY = false.
Proof. reflexivity. Qed.

Lemma dinit9_strm : forall g, ds_strm (dinit9_of g) = ds_strm (dinit9_of (fun _ => g0)).
Proof. intros g. unfold dinit9_of. rewrite !dFg_strm. reflexivity. Qed.

Lemma dinit9_run_safe : forall g,
  DeflateSafe.dpure (deflateInit2_m DeflateSafe.dhooks (zc_none zstrm0) 9 Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY) (dchs g)
  = Some (Some (dinit9_of g), dinit9_zr).
Proof.
  intros g.
  rewrite (RefDeflSafeI5b.dinit_run (zc_none zstrm0) 9 Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY (dchs g) di_bad_9).
  unfold dchs. cbn [ohd otl].
  pose proof (S5og_proj 0%N (g 0%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL
                (Some (1%N, g 1%N)) (Some (2%N, g 2%N)) (Some (3%N, g 3%N)) (Some (4%N, g 4%N))) as PJ.
  cbv zeta in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
  unfold dinit_body, all_some. rewrite Ew, Ep, Eh, Eb. cbn [option_map fst].
  change (S5og 0%N (g 0%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL
               (Some (1%N, g 1%N)) (Some (2%N, g 2%N)) (Some (3%N, g 3%N)) (Some (4%N, g 4%N)))
    with (S5g 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS) DEF_MEM_LEVEL).
  rewrite (reset_S5g 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (cs_init (zc_none zstrm0)) (di_wrap MAX_WBITS) (di_wb9 MAX_WBITS)
             DEF_MEM_LEVEL (di_level 9) Z_DEFAULT_STRATEGY Z_DEFLATED (proj1 (di_wrap_range MAX_WBITS))).
  unfold dinit9_zr. rewrite <- (dinit9_strm g). reflexivity.
Qed.

Theorem dinit9_run_of : forall g, HarnessLarge.dinit9_run (dchs g) zstrm0 = Some (Some (dinit9_of g), dinit9_zr).
Proof. intros g. unfold HarnessLarge.dinit9_run. rewrite hs_dpure_eq, hs_dhooks_eq. exact (dinit9_run_safe g). Qed.

Theorem ds9_of : ds9 = dinit9_of (fun _ => g0).
Proof. unfold ds9, dinit9. rewrite dinit9_run_of. reflexivity. Qed.

Theorem dz9_of : dz9 = zr_strm dinit9_zr.
Proof. unfold dz9, dinit9. rewrite dinit9_run_of. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition DRELL (s_a : deflate_state) (x : dstream) : Prop := DCALLZ s_a (dz_s x).

Local Ltac proj_cbn :=
  cbn [ds_status ds_pending_buf ds_pending_buf_size ds_pending_out ds_pending ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush
       ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift
       ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length
       ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_dyn_ltree_fc ds_dyn_ltree_dl
       ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_l_max_code ds_d_max_code ds_bl_max_code ds_bl_count ds_heap
       ds_heap_len ds_heap_max ds_depth ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf
       ds_bi_valid ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm].

(* [comment removed for export] *)
Lemma ZLS_init9 : forall g, ZLS (dinit9_of g) /\ zl_modes (dinit9_of g).
Proof.
  intros g. unfold ZLS, PQ, PRI, zl_modes, dmode, dinit9_of, dFg. proj_cbn.
  change (9 =? 0) with false. change (0 =? Z_HUFFMAN_ONLY) with false. change (0 =? Z_RLE) with false. change (9 <=? 3) with false. cbv iota.
  split.
  - split; [intros E; discriminate E|]. split; [intros _; left; split; reflexivity|]. intros _. unfold MIN_MATCH. repeat split; reflexivity.
  - split; [right; reflexivity | left; reflexivity].
Qed.

Lemma DCALLZ_init9 : forall g g', DCALLZ (dinit9_of g) (dinit9_of g').
Proof.
  intros g g'. destruct dinit_cs_ok as [Hai Hao].
  assert (Hlv : 0 <= 9 <= 9) by lia.
  pose proof (ZLS_init9 g) as [Z1 M1]. pose proof (ZLS_init9 g') as [Z2 _].
  split; [| exact (conj Z1 (conj Z2 M1))].
  split; [exact (dFg_DQ 0%N 1%N 2%N 3%N 4%N dinit_cs 9 (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N))|].
  split; [apply INVG_of_INV; exact (dFg_INV 0%N 1%N 2%N 3%N 4%N dinit_cs 9 Hlv Hai Hao (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N))|].
  split; [apply INVG_of_INV; exact (dFg_INV 0%N 1%N 2%N 3%N 4%N dinit_cs 9 Hlv Hai Hao (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N))|].
  split; apply dreach_DD.
  - exact (dFg_dreach (zc_none zstrm0) 9 Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY 0%N 1%N 2%N 3%N 4%N
             (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) di_bad_9 ltac:(unfold DEF_MEM_LEVEL; lia)).
  - exact (dFg_dreach (zc_none zstrm0) 9 Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY 0%N 1%N 2%N 3%N 4%N
             (g' 0%N) (g' 1%N) (g' 2%N) (g' 3%N) (g' 4%N) di_bad_9 ltac:(unfold DEF_MEM_LEVEL; lia)).
Qed.

Theorem DRELL_init9 : forall g, DRELL (dinit9_of g) zdl_init9.
Proof. intros g. unfold DRELL, zdl_init9. cbn [dz_s]. rewrite ds9_of. apply DCALLZ_init9. Qed.

(* [comment removed for export] *)
Theorem DCALLZ_deflate : forall s1 s2 zc flush, DCALLZ s1 s2 -> dcall_wf zc -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  snd (deflate_m s1 zc flush) = snd (deflate_m s2 zc flush)
  /\ DCALLZ (fst (deflate_m s1 zc flush)) (fst (deflate_m s2 zc flush)).
Proof.
  intros s1 s2 zc flush (HC & Z1 & Z2 & M1) Hzc Hfl.
  assert (Hfl3 : flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK) by (destruct Hfl as [F|F]; [left; exact F | right; left; exact F]).
  pose proof HC as (Q & _ & _ & D1 & D2).
  pose proof (zl_modes_clean _ _ (DQ_clean _ _ Q) M1) as M2.
  destruct (deflate_m_rel s1 s2 zc flush HC Hzc Hfl3) as [E HC'].
  split; [exact E|]. split; [exact HC'|].
  split; [exact (deflate_ZLS s1 zc flush D1 Z1 Hzc Hfl3 M1)|].
  split; [exact (deflate_ZLS s2 zc flush D2 Z2 Hzc Hfl3 M2)|].
  exact (deflate_zl_modes s1 zc flush D1 Z1 Hzc Hfl3 M1).
Qed.

Theorem DRELL_deflate : forall s_a x zc flush, DRELL s_a x -> dcall_wf zc -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  snd (deflate_m s_a zc flush) = snd (deflate_m (dz_s x) zc flush)
  /\ DRELL (fst (deflate_m s_a zc flush)) (mkDZ (fst (deflate_m (dz_s x) zc flush)) (zr_strm (snd (deflate_m (dz_s x) zc flush)))).
Proof. intros s_a x zc flush R Hz Hf. exact (DCALLZ_deflate s_a (dz_s x) zc flush R Hz Hf). Qed.

(* [comment removed for export] *)
Theorem DRELL_params : forall s_a x zc level strategy,
  DRELL s_a x -> dcall_wf zc -> params_legal level strategy -> (strategy = 0 \/ strategy = 1) -> (cfunc_id level = 0 \/ cfunc_id level = 2) ->
  snd (deflateParams_m s_a zc level strategy) = snd (deflateParams_m (dz_s x) zc level strategy)
  /\ DRELL (fst (deflateParams_m s_a zc level strategy))
           (mkDZ (fst (deflateParams_m (dz_s x) zc level strategy)) (zr_strm (snd (deflateParams_m (dz_s x) zc level strategy)))).
Proof. intros s_a x zc level strategy R Hz Hl Hs Hc. exact (dparams_rel s_a (dz_s x) zc level strategy R Hz Hl Hs Hc). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem DRELL_zdl_deflate : forall s_a inp x aout flush, DRELL s_a x -> dcall_wf (mkZCall inp aout (dz_z x)) -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  let r_a := deflate_m s_a (mkZCall inp aout (dz_z x)) flush in
  let '(x', consumed, bs, rc) := zdl_deflate inp x aout flush in
  DRELL (fst r_a) x' /\ zr_strm (snd r_a) = dz_z x'
  /\ consumed = zr_consumed (snd r_a) /\ bs = zr_output (snd r_a) /\ rc = zr_rc (snd r_a).
Proof.
  intros s_a inp x aout flush R Hz Hf. cbv zeta.
  destruct (DRELL_deflate s_a x (mkZCall inp aout (dz_z x)) flush R Hz Hf) as [E R'].
  unfold zdl_deflate. rewrite E.
  destruct (deflate_m (dz_s x) (mkZCall inp aout (dz_z x)) flush) as [s' zr]. cbn [fst snd] in *.
  split; [exact R'|]. repeat split; reflexivity.
Qed.

Theorem DRELL_zdl_params : forall s_a inp x aout level strategy,
  DRELL s_a x -> dcall_wf (mkZCall inp aout (dz_z x)) -> params_legal level strategy -> (strategy = 0 \/ strategy = 1) ->
  (cfunc_id level = 0 \/ cfunc_id level = 2) ->
  let r_a := deflateParams_m s_a (mkZCall inp aout (dz_z x)) level strategy in
  let '(x', consumed, bs, rc) := zdl_params inp x aout level strategy in
  DRELL (fst r_a) x' /\ zr_strm (snd r_a) = dz_z x'
  /\ consumed = zr_consumed (snd r_a) /\ bs = zr_output (snd r_a) /\ rc = zr_rc (snd r_a).
Proof.
  intros s_a inp x aout level strategy R Hz Hl Hs Hc. cbv zeta.
  destruct (DRELL_params s_a x (mkZCall inp aout (dz_z x)) level strategy R Hz Hl Hs Hc) as [E R'].
  unfold zdl_params. rewrite E.
  destruct (deflateParams_m (dz_s x) (mkZCall inp aout (dz_z x)) level strategy) as [s' zr]. cbn [fst snd] in *.
  split; [exact R'|]. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem DRELL_facts : forall s_a x, DRELL s_a x ->
  DD s_a /\ INVG s_a /\ clean s_a = clean (dz_s x) /\ ZLS s_a /\ zl_modes s_a /\ DD (dz_s x) /\ INVG (dz_s x) /\ ZLS (dz_s x).
Proof.
  intros s_a x ((Q & I1 & I2 & D1 & D2) & Z1 & Z2 & M1).
  split; [exact D1|]. split; [exact I1|]. split; [exact (DQ_clean _ _ Q)|]. split; [exact Z1|]. split; [exact M1|].
  split; [exact D2|]. split; [exact I2 | exact Z2].
Qed.

(* [comment removed for export] *)
Theorem DRELL_dend_rc : forall s_a x, DRELL s_a x -> dend_rc s_a = dend_rc (dz_s x).
Proof.
  intros s_a x R. destruct (DRELL_facts s_a x R) as (_ & _ & EC & _).
  unfold dend_rc. rewrite <- (clean_eq_fieldT deflateStateCheck _ _ EC ltac:(intros; reflexivity)),
    <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)). reflexivity.
Qed.
