(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRelG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_wmask v : 0 <= Z.land v 32767 <= 32767.
Proof. apply land_mask_range. lia. Qed.

Lemma update_hash_rel W C B bnd ms pm s1 s2 h c : REL W C B bnd ms pm s1 s2 -> update_hash s2 h c = update_hash s1 h c.
Proof. intros R. unfold update_hash. rel_fields R. reflexivity. Qed.

Lemma update_hash_range15 s h c : INVG s -> 0 <= update_hash s h c < 32768.
Proof. intros I. unfold update_hash. rewrite (ig_hmask s I). pose proof (land_mask_range (Z.lxor (wrap32 (Z.shiftl h (ds_hash_shift s))) c) 32767). lia. Qed.

Lemma cv_mono (C C' : Z -> Prop) bnd bnd' v : cv C bnd v -> (forall p, C p -> C' p) -> bnd <= bnd' -> cv C' bnd' v.
Proof. intros [A Bq] HC Hb. split; [exact A|]. destruct Bq as [Bq|[B1 B2]]; [left; exact Bq|right; split; [lia|apply HC; exact B2]]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma INVG_insert_string s str : INVG s -> INVG (fst (insert_string s str)).
Proof.
  intros I. unfold insert_string. cbn [fst].
  pose proof (update_hash_range15 s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) I) as Hh.
  set (h := update_hash s _ _) in *. clearbody h.
  destruct I; constructor; dsr; try assumption; try (rewrite ?arr_len_set; assumption).
Qed.

Lemma insert_string_rel W C B bnd ms pm s1 s2 str :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
  0 <= str <= bnd -> str < 65536 -> W (str + 2) -> str + 2 < 65536 ->
  snd (insert_string s1 str) = snd (insert_string s2 str)
  /\ REL W (fun p => C p \/ p = Z.land str 32767) B bnd ms pm (fst (insert_string s1 str)) (fst (insert_string s2 str))
  /\ cv C bnd (snd (insert_string s1 str)).
Proof.
  intros R I1 I2 Hs H16 Hw Hw2. unfold insert_string. cbn [fst snd]. dsr.
  assert (EW : arr_get (ds_window s2) (str + (MIN_MATCH - 1)) = arr_get (ds_window s1) (str + (MIN_MATCH - 1))).
  { symmetry. apply (aeq_get _ _ _ _ (r_win _ _ _ _ _ _ _ _ R)); [rewrite (ig_wl s1 I1); unfold MIN_MATCH; lia | unfold MIN_MATCH; replace (str + (3 - 1)) with (str + 2) by lia; exact Hw]. }
  rewrite EW. rewrite (update_hash_rel _ _ _ _ _ _ _ _ _ _ R). rel_fields R.
  set (h := update_hash s1 (ds_ins_h s1) _).
  assert (Hh : 0 <= h < 32768) by (unfold h; apply update_hash_range15; exact I1).
  dsr.
  assert (EH : arr_get (ds_head s2) h = arr_get (ds_head s1) h).
  { symmetry. apply (aeq_get _ _ _ _ (r_head _ _ _ _ _ _ _ _ R)); [rewrite (ig_hl s1 I1); lia | exact I]. }
  rewrite EH. set (mh := arr_get (ds_head s1) h). rewrite (ig_wmask s1 I1).
  split; [reflexivity|].
  pose proof (r_chain _ _ _ _ _ _ _ _ R) as [CH CP].
  assert (CVmh : cv C bnd mh) by (unfold mh; apply CH; exact Hh).
  refine (conj _ CVmh).
  assert (CVW : forall v, cv C bnd v -> cv (fun p => C p \/ p = Z.land str 32767) bnd v) by (intros v Hv; eapply cv_mono; [exact Hv|intros; left; assumption|lia]).
  eapply rel_set_head.
  - eapply rel_set_prev; [apply rel_set_ins_h; exact R | exact (aeq_set C _ _ (Z.land str 32767) mh (r_prev _ _ _ _ _ _ _ _ R)) |].
    split; dsr.
    + intros h' Hh'. apply CVW. apply CH. exact Hh'.
    + intros p [Cp| ->].
      * destruct (CP p Cp) as [Rp CVp]. split; [exact Rp|]. rewrite arr_get_set. unfold arr_inb. rewrite (ig_pl s1 I1).
        destruct ((Z.land str 32767 =? p) && _); apply CVW; assumption.
      * pose proof (land_wmask str). split; [lia|]. rewrite arr_get_set_same by (rewrite (ig_pl s1 I1); lia). apply CVW. exact CVmh.
  - eapply aeq_mono; [apply aeq_set; exact (r_head _ _ _ _ _ _ _ _ R)|]. intros; left; exact I.
  - dsr. exact (aeq_set C _ _ (Z.land str 32767) mh (r_prev _ _ _ _ _ _ _ _ R)).
  - split; dsr.
    + intros h' Hh'. rewrite arr_get_set. unfold arr_inb. rewrite (ig_hl s1 I1).
      destruct ((h =? h') && _); [|apply CVW; apply CH; exact Hh'].
      unfold cv. rewrite wrap16_id by lia. pose proof (land_wmask str). split; [lia|]. right. split; [lia|]. right. reflexivity.
    + intros p [Cp| ->].
      * destruct (CP p Cp) as [Rp CVp]. split; [exact Rp|]. rewrite arr_get_set. unfold arr_inb. rewrite (ig_pl s1 I1).
        destruct ((Z.land str 32767 =? p) && _); apply CVW; assumption.
      * pose proof (land_wmask str). split; [lia|]. rewrite arr_get_set_same by (rewrite (ig_pl s1 I1); lia). apply CVW. exact CVmh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma clear_hash_get s h : INVG s ->
  arr_get (ds_head (clear_hash s)) h = if (0 <=? h) && (h <? 32768) then 0 else arr_get (ds_head s) h.
Proof.
  intros I. unfold clear_hash. dsr. rewrite (ig_hsize s I). rewrite arr_get_fill, arr_get_set. unfold arr_inb. rewrite arr_len_set, (ig_hl s I). unfold NIL.
  destruct (Z.leb_spec 0 h), (Z.ltb_spec h (0 + Z.max 0 (32768 - 1))), (Z.ltb_spec h 32768), (Z.eqb_spec (32768 - 1) h), (Z.leb_spec 0 (32768-1)), (Z.ltb_spec (32768-1) 32768); cbn [andb]; try reflexivity; lia.
Qed.
Lemma INVG_clear_hash s : INVG s -> INVG (clear_hash s).
Proof.
  intros I. pose proof (clear_hash_get s) as G. unfold clear_hash in *. dsr. rewrite (ig_hsize s I) in *.
  pose proof (arr_len_fill (arr_set (ds_head s) (32768 - 1) NIL) 0 (32768 - 1) 0) as L. rewrite arr_len_set, (ig_hl s I) in L.
  set (a := arr_fill _ 0 (32768 - 1) 0) in *. clearbody a.
  destruct I; constructor; dsr; try assumption.
Qed.
Lemma clear_hash_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> REL W C B bnd ms pm (clear_hash s1) (clear_hash s2).
Proof.
  intros R I1 I2. pose proof (clear_hash_get s1) as G1. unfold clear_hash in *. dsr. rel_fields R. rewrite (ig_hsize s1 I1) in *.
  pose proof (r_chain _ _ _ _ _ _ _ _ R) as [CH CP].
  pose proof (aeq_fill _ _ _ 0 (32768 - 1) 0 (aeq_set_keep _ _ _ (32768 - 1) NIL (r_head _ _ _ _ _ _ _ _ R))) as AH.
  set (a1 := arr_fill (arr_set (ds_head s1) (32768 - 1) NIL) 0 (32768 - 1) 0) in *. clearbody a1.
  set (a2 := arr_fill (arr_set (ds_head s2) (32768 - 1) NIL) 0 (32768 - 1) 0) in *. clearbody a2.
  assert (E : forall s x y, set_head (set_head s x) y = set_head s y) by (intros; reflexivity). rewrite !E.
  eapply rel_set_head; [exact R | eapply aeq_mono; [exact AH|intros; left; exact I] | dsr; exact (r_prev _ _ _ _ _ _ _ _ R) |].
  split; dsr; [|exact CP]. intros h Hh. rewrite (G1 h I1). replace ((0 <=? h) && (h <? 32768)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  split; [lia|left; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_buf_len s dst n : 0 <= n -> 0 <= cs_avail_in (ds_strm s) ->
  0 <= snd (read_buf s dst n) <= n /\ snd (read_buf s dst n) <= cs_avail_in (ds_strm s)
  /\ cs_avail_in (ds_strm (fst (read_buf s dst n))) = cs_avail_in (ds_strm s) - snd (read_buf s dst n).
Proof.
  intros Hn Ha. unfold read_buf, cs_emit. cbv zeta.
  set (len := if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)).
  assert (Hl : 0 <= len <= n /\ len <= cs_avail_in (ds_strm s)) by (unfold len; destruct (Z.ltb_spec n (cs_avail_in (ds_strm s))); lia).
  destruct (Z.eqb_spec len 0); [cbn [fst snd]; lia|].
  destruct dst; dsr; destruct (ds_wrap s =? 1); [|destruct (ds_wrap s =? 2)| |destruct (ds_wrap s =? 2)]; dsr; lia.
Qed.

Lemma INVG_read_buf s dst n : INVG s -> 0 <= n -> INVG (fst (read_buf s dst n)).
Proof.
  intros I Hn. pose proof (read_buf_len s dst n Hn (ig_ain s I)) as (L1 & L2 & L3).
  revert L1 L2 L3. unfold read_buf, cs_emit. cbv zeta.
  set (len := if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)).
  destruct (Z.eqb_spec len 0); [cbn [fst snd]; intros; exact I|].
  set (bytes := arr_slice _ _ len).
  destruct dst; dsr; destruct (ds_wrap s =? 1); [|destruct (ds_wrap s =? 2)| |destruct (ds_wrap s =? 2)]; dsr; intros L1 L2 L3;
  destruct I; constructor; dsr; try assumption; try (rewrite ?arr_len_upd; assumption); try lia.
Qed.

Lemma read_buf_window_rel W C B bnd ms pm s1 s2 off n :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> 0 <= n ->
  let r1 := read_buf s1 (RB_window off) n in let r2 := read_buf s2 (RB_window off) n in
  snd r1 = snd r2 /\ ds_strm (fst r1) = ds_strm (fst r2)
  /\ REL (fun i => W i \/ off <= i < off + snd r1) C B bnd ms pm (fst r1) (fst r2).
Proof.
  intros R I1 Hn. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC.
  unfold read_buf, cs_emit. cbv zeta. dsr. rel_fields R.
  set (len := if n <? cs_avail_in (ds_strm s1) then n else cs_avail_in (ds_strm s1)).
  destruct (Z.eqb_spec len 0) as [L0|L0].
  - cbn [fst snd]. split; [reflexivity|]. split; [rel_fields R; reflexivity|].
    eapply rel_weaken; [exact R| intros i [Hi|Hi]; [exact Hi|lia] | auto | lia].
  - cbn [fst snd]. dsr. set (bytes := arr_slice _ _ len).
    pose proof (ig_ain s1 I1) as AIN.
    assert (Hlen : 0 <= len <= n) by (unfold len; destruct (Z.ltb_spec n (cs_avail_in (ds_strm s1))); lia).
    split; [reflexivity|]. split; [reflexivity|].
    assert (BL : zlength bytes = len) by (unfold bytes; rewrite arr_slice_length; lia).
    set (st' := cset_total_in _ _). clearbody st'.
    apply rel_set_strm. eapply rel_set_window; [exact R|].
    eapply aeq_mono; [apply aeq_upd; exact (r_win _ _ _ _ _ _ _ _ R)|]. intros i [Hi|Hi]; [left; exact Hi|right; rewrite BL; exact Hi].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shm_eq v : 0 <= v < 65536 -> shm 32768 v = (if 32768 <=? v then v - 32768 else 0).
Proof. intros Hv. unfold shm, NIL. destruct (Z.leb_spec 32768 v); rewrite wrap16_id by lia; reflexivity. Qed.

Lemma land_sub_wsize v : 32768 <= v < 65536 -> Z.land (v - 32768) 32767 = Z.land v 32767.
Proof.
  intros Hv. change 32767 with (Z.ones 15). rewrite !Z.land_ones by lia. change (2 ^ 15) with 32768.
  replace v with ((v - 32768) + 1 * 32768) at 2 by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma cv_shm C bnd v : cv C bnd v -> cv C (bnd - 32768) (shm 32768 v).
Proof.
  intros [A Bq]. rewrite shm_eq by exact A. destruct (Z.leb_spec 32768 v).
  - split; [lia|]. destruct Bq as [->|[B1 B2]]; [lia|]. right. split; [lia|]. rewrite land_sub_wsize by lia. exact B2.
  - split; [lia|]. left. reflexivity.
Qed.

Lemma slide_hash_get_head s i : INVG s ->
  arr_get (ds_head (slide_hash s)) i = if (0 <=? i) && (i <? 32768) then shm 32768 (arr_get (ds_head s) i) else arr_get (ds_head s) i.
Proof. intros I. unfold slide_hash. dsr. rewrite (ig_wsize s I), (ig_hsize s I). apply slide_hash_loop_get; [reflexivity|rewrite (ig_hl s I); lia]. Qed.
Lemma slide_hash_get_prev s i : INVG s ->
  arr_get (ds_prev (slide_hash s)) i = if (0 <=? i) && (i <? 32768) then shm 32768 (arr_get (ds_prev s) i) else arr_get (ds_prev s) i.
Proof. intros I. unfold slide_hash. dsr. rewrite (ig_wsize s I). apply slide_hash_loop_get; [reflexivity|rewrite (ig_pl s I); lia]. Qed.

Lemma INVG_slide_hash s : INVG s -> INVG (slide_hash s).
Proof.
  intros I. pose proof (fun i => slide_hash_get_head s i I) as GH. pose proof (fun i => slide_hash_get_prev s i I) as GP.
  unfold slide_hash in *. dsr. rewrite (ig_wsize s I), (ig_hsize s I) in *.
  pose proof (slide_hash_loop_len (Z.to_nat 32768) (ds_head s) 32768 32768) as LH.
  pose proof (slide_hash_loop_len (Z.to_nat 32768) (ds_prev s) 32768 32768) as LP.
  set (H' := slide_hash_loop (Z.to_nat 32768) (ds_head s) 32768 32768) in *. clearbody H'.
  set (P' := slide_hash_loop (Z.to_nat 32768) (ds_prev s) 32768 32768) in *. clearbody P'.
  destruct I; constructor; dsr; try assumption; try (rewrite ?LH, ?LP; assumption).
Qed.

Lemma slide_hash_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> REL W C B (bnd - 32768) ms pm (slide_hash s1) (slide_hash s2).
Proof.
  intros R I1 I2. pose proof (fun i => slide_hash_get_head s1 i I1) as GH1. pose proof (fun i => slide_hash_get_prev s1 i I1) as GP1.
  unfold slide_hash in *. dsr. rel_fields R. rewrite (ig_wsize s1 I1), (ig_hsize s1 I1) in *.
  pose proof (r_chain _ _ _ _ _ _ _ _ R) as [CH CP].
  pose proof (aeq_slide _ _ _ 32768 32768 (r_head _ _ _ _ _ _ _ _ R) ltac:(rewrite (ig_hl s1 I1); reflexivity) ltac:(lia)) as AH.
  pose proof (aeq_slide _ _ _ 32768 32768 (r_prev _ _ _ _ _ _ _ _ R) ltac:(rewrite (ig_pl s1 I1); reflexivity) ltac:(lia)) as AP.
  (* [comment removed for export] *)
  set (H1' := slide_hash_loop (Z.to_nat 32768) (ds_head s1) 32768 32768) in *. clearbody H1'.
  set (H2' := slide_hash_loop (Z.to_nat 32768) (ds_head s2) 32768 32768) in *. clearbody H2'.
  set (P1' := slide_hash_loop (Z.to_nat 32768) (ds_prev s1) 32768 32768) in *. clearbody P1'.
  set (P2' := slide_hash_loop (Z.to_nat 32768) (ds_prev s2) 32768 32768) in *. clearbody P2'.
  assert (CHh : forall h, 0 <= h < 32768 -> cv C (bnd - 32768) (arr_get H1' h)).
  { intros h Hh. rewrite (GH1 h). replace ((0 <=? h) && (h <? 32768)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    apply cv_shm. apply CH. exact Hh. }
  assert (CPp : forall p, C p -> 0 <= p < 32768 /\ cv C (bnd - 32768) (arr_get P1' p)).
  { intros p Cp. destruct (CP p Cp) as [Rp CVp]. split; [exact Rp|]. rewrite (GP1 p).
    replace ((0 <=? p) && (p <? 32768)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    apply cv_shm. exact CVp. }
  eapply rel_set_prev; [eapply rel_set_head; [exact R | exact AH | dsr; exact (r_prev _ _ _ _ _ _ _ _ R) | ] | exact AP | ].
  - split; dsr; [|exact CP]. intros h Hh. eapply cv_mono; [apply CHh; exact Hh|auto|lia].
  - split; dsr; [exact CHh|exact CPp].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fill_window_insert_step f s str :
  fill_window_insert (S f) s str =
  if negb (ds_insert s =? 0) then
    let s' := set_insert (fst (insert_string s str)) (ds_insert (fst (insert_string s str)) - 1) in
    if ds_lookahead s' + ds_insert s' <? MIN_MATCH then s' else fill_window_insert f s' (str + 1)
  else s.
Proof. reflexivity. Qed.

Lemma INVG_fill_window_insert : forall f s str, INVG s -> INVG (fill_window_insert f s str).
Proof.
  induction f as [|f IH]; intros s str I; [exact I|]. rewrite fill_window_insert_step.
  destruct (Z.eqb_spec (ds_insert s) 0) as [Z0|NZ]; cbn [negb]; [exact I|].
  pose proof (INVG_insert_string s str I) as I'. pose proof (ig_ins _ I') as II.
  assert (Ei : ds_insert (fst (insert_string s str)) = ds_insert s) by (unfold insert_string; dsr; reflexivity).
  set (s' := fst (insert_string s str)) in *. clearbody s'.
  pose proof (INVG_set_insert s' (ds_insert s' - 1) ltac:(rewrite Ei in *; lia) I') as I''.
  cbv zeta. destruct (_ <? _); [exact I''|apply IH; exact I''].
Qed.

Lemma fill_window_insert_rel : forall f W C B bnd ms pm s1 s2 str K,
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> str + ds_insert s1 = K -> 0 <= str -> K - 1 <= bnd -> K <= ds_strstart s1 ->
  (forall i, 0 <= i < K + ds_lookahead s1 -> W i) -> MIN_MATCH <= ds_lookahead s1 + ds_insert s1 ->
  exists C', (forall p, C p -> C' p)
    /\ REL W C' B bnd ms pm (fill_window_insert f s1 str) (fill_window_insert f s2 str).
Proof.
  induction f as [|f IH]; intros W C B bnd ms pm s1 s2 str K R I1 I2 HK Hs Kb Kss HW HL.
  - exists C. split; [auto|]. exact R.
  - rewrite !fill_window_insert_step.
    rel_fields R. destruct (Z.eqb_spec (ds_insert s1) 0) as [Z0|NZ]; cbn [negb].
    + exists C. split; [auto|]. exact R.
    + pose proof (ig_ins s1 I1) as II. pose proof (ig_sl s1 I1) as SL. unfold MIN_MATCH in HL.
      destruct (insert_string_rel W C B bnd ms pm s1 s2 str R I1 I2 ltac:(lia) ltac:(lia) ltac:(apply HW; lia) ltac:(lia)) as (_ & R1 & _).
      pose proof (INVG_insert_string s1 str I1) as I1'. pose proof (INVG_insert_string s2 str I2) as I2'.
      set (s1' := fst (insert_string s1 str)) in *. set (s2' := fst (insert_string s2 str)) in *.
      assert (E1 : ds_insert s1' = ds_insert s1 /\ ds_lookahead s1' = ds_lookahead s1 /\ ds_strstart s1' = ds_strstart s1) by (subst s1'; unfold insert_string; dsr; repeat split; reflexivity).
      assert (E2 : ds_insert s2' = ds_insert s1 /\ ds_strstart s2' = ds_strstart s1) by (subst s2'; unfold insert_string; dsr; rel_fields R; repeat split; reflexivity).
      clearbody s1' s2'. destruct E1 as (Ei & El & Es). destruct E2 as (Ei2 & Es2).
      cbv zeta. dsr. rel_fields R1. rewrite Ei, El.
      pose proof (rel_set_insert _ _ _ _ _ _ s1' s2' (ds_insert s1 - 1) R1) as R2.
      pose proof (INVG_set_insert s1' (ds_insert s1 - 1) ltac:(lia) I1') as I1''.
      pose proof (INVG_set_insert s2' (ds_insert s1 - 1) ltac:(lia) I2') as I2''.
      destruct (Z.ltb_spec (ds_lookahead s1 + (ds_insert s1 - 1)) MIN_MATCH).
      * exists (fun p => C p \/ p = Z.land str 32767). split; [auto|]. exact R2.
      * destruct (IH W _ B bnd ms pm _ _ (str + 1) K R2 I1'' I2'') as (C' & HC' & R3); try (dsr; rewrite ?Ei, ?El, ?Es; unfold MIN_MATCH in *; lia).
        { intros i Hi. apply HW. dsr. rewrite El in Hi. lia. }
        exists C'. split; [intros p Cp; apply HC'; left; exact Cp|]. exact R3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma INVG_fill_window_high s : INVG s -> INVG (fill_window_high s).
Proof.
  intros I. pose proof (ig_hw s I) as Hhw. pose proof (ig_sl s I) as Hsl. pose proof (ig_ss s I). pose proof (ig_look s I).
  unfold fill_window_high. rewrite (ig_wsz s I). cbv zeta.
  destruct (Z.ltb_spec (ds_high_water s) 65536) as [L1|L1]; [|exact I].
  destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)) as [L2|L2].
  - set (init := if WIN_INIT <? 65536 - (ds_strstart s + ds_lookahead s) then WIN_INIT else 65536 - (ds_strstart s + ds_lookahead s)).
    assert (Hi : 0 <= init <= 65536 - (ds_strstart s + ds_lookahead s)) by (unfold init, WIN_INIT, MAX_MATCH; destruct (Z.ltb_spec 258 (65536 - (ds_strstart s + ds_lookahead s))); lia).
    rewrite (wrap32_id init) by lia.
    pose proof (arr_len_fill (ds_window s) (ds_strstart s + ds_lookahead s) init 0) as L. rewrite (ig_wl s I) in L.
    set (a1 := arr_fill (ds_window s) _ init 0) in *. clearbody a1.
    apply INVG_set_high_water; [dsr; lia|]. destruct I; constructor; dsr; assumption.
  - destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + WIN_INIT)) as [L3|L3]; [|exact I].
    set (init := if 65536 - ds_high_water s <? ds_strstart s + ds_lookahead s + WIN_INIT - ds_high_water s then 65536 - ds_high_water s else ds_strstart s + ds_lookahead s + WIN_INIT - ds_high_water s).
    assert (Hi : 0 <= init <= 65536 - ds_high_water s) by (unfold init, WIN_INIT, MAX_MATCH in *; destruct (Z.ltb_spec (65536 - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia).
    rewrite (wrap32_id init) by lia.
    pose proof (arr_len_fill (ds_window s) (ds_high_water s) init 0) as L. rewrite (ig_wl s I) in L.
    set (a1 := arr_fill (ds_window s) _ init 0) in *. clearbody a1.
    apply INVG_set_high_water; [dsr; lia|]. destruct I; constructor; dsr; assumption.
Qed.

Lemma fill_window_high_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> (forall i, i < WHI s1 -> W i) ->
  exists W', (forall i, i < WHI (fill_window_high s1) -> W' i)
    /\ REL W' C B bnd ms pm (fill_window_high s1) (fill_window_high s2).
Proof.
  intros R I1 I2 HW.
  pose proof (ig_hw s1 I1) as Hhw. pose proof (ig_sl s1 I1) as Hsl. pose proof (ig_ss s1 I1). pose proof (ig_look s1 I1).
  unfold fill_window_high. rel_fields R. rewrite (ig_wsz s1 I1). cbv zeta.
  destruct (Z.ltb_spec (ds_high_water s1) 65536) as [L1|L1].
  2:{ exists W. split; [exact HW|exact R]. }
  destruct (Z.ltb_spec (ds_high_water s1) (ds_strstart s1 + ds_lookahead s1)) as [L2|L2].
  - set (init := if WIN_INIT <? 65536 - (ds_strstart s1 + ds_lookahead s1) then WIN_INIT else 65536 - (ds_strstart s1 + ds_lookahead s1)).
    assert (Hi : 0 <= init <= 65536 - (ds_strstart s1 + ds_lookahead s1)) by (unfold init, WIN_INIT, MAX_MATCH; destruct (Z.ltb_spec 258 (65536 - (ds_strstart s1 + ds_lookahead s1))); lia).
    rewrite (wrap32_id init) by lia.
    exists (fun i => W i \/ ds_strstart s1 + ds_lookahead s1 <= i < ds_strstart s1 + ds_lookahead s1 + init). split.
    + intros i Hiw. unfold WHI in *. dsr. destruct (Z_lt_le_dec i (ds_strstart s1 + ds_lookahead s1)); [left; apply HW; lia|right; lia].
    + apply rel_set_high_water.
      pose proof (aeq_fill W _ _ (ds_strstart s1 + ds_lookahead s1) init 0 (r_win _ _ _ _ _ _ _ _ R)) as AW.
      set (a1 := arr_fill (ds_window s1) _ init 0) in *. clearbody a1. set (a2 := arr_fill (ds_window s2) _ init 0) in *. clearbody a2.
      eapply rel_set_window; [exact R|exact AW].
  - destruct (Z.ltb_spec (ds_high_water s1) (ds_strstart s1 + ds_lookahead s1 + WIN_INIT)) as [L3|L3].
    2:{ exists W. split; [exact HW|exact R]. }
    set (init := if 65536 - ds_high_water s1 <? ds_strstart s1 + ds_lookahead s1 + WIN_INIT - ds_high_water s1 then 65536 - ds_high_water s1 else ds_strstart s1 + ds_lookahead s1 + WIN_INIT - ds_high_water s1).
    assert (Hi : 0 <= init <= 65536 - ds_high_water s1) by (unfold init, WIN_INIT, MAX_MATCH in *; destruct (Z.ltb_spec (65536 - ds_high_water s1) (ds_strstart s1 + ds_lookahead s1 + 258 - ds_high_water s1)); lia).
    rewrite (wrap32_id init) by lia.
    exists (fun i => W i \/ ds_high_water s1 <= i < ds_high_water s1 + init). dsr. rel_fields R. split.
    + intros i Hiw. unfold WHI in *. dsr. destruct (Z_lt_le_dec i (ds_high_water s1)); [left; apply HW; lia|right; lia].
    + apply rel_set_high_water.
      pose proof (aeq_fill W _ _ (ds_high_water s1) init 0 (r_win _ _ _ _ _ _ _ _ R)) as AW.
      set (a1 := arr_fill (ds_window s1) _ init 0) in *. clearbody a1. set (a2 := arr_fill (ds_window s2) _ init 0) in *. clearbody a2.
      eapply rel_set_window; [exact R|exact AW].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fws (s : deflate_state) (wsize : Z) : deflate_state * Z :=
  let more := wrap32 (ds_window_size s - ds_lookahead s - ds_strstart s) in
  if Z.leb (wsize + (ds_w_size s - MIN_LOOKAHEAD)) (ds_strstart s) then
    let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) wsize (wrap32 (wsize - more))) in
    let s := set_match_start s (wrap32 (ds_match_start s - wsize)) in
    let s := set_strstart s (ds_strstart s - wsize) in
    let s := set_block_start s (ds_block_start s - wsize) in
    let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
    let s := slide_hash s in
    (s, wrap32 (more + wsize))
  else (s, more).

Definition fwr (s : deflate_state) (more : Z) : deflate_state * bool :=
  if Z.eqb (cs_avail_in (ds_strm s)) 0 then (s, true)
  else
    let '(s, n) := read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more in
    let s := set_lookahead s (ds_lookahead s + n) in
    let s :=
      if Z.leb MIN_MATCH (ds_lookahead s + ds_insert s) then
        let str := ds_strstart s - ds_insert s in
        let s := set_ins_h s (arr_get (ds_window s) str) in
        let s := set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 1))) in
        fill_window_insert (Z.to_nat (ds_insert s)) s str
      else s in
    (s, false).

Lemma fill_window_body_eq s w : fill_window_body s w = (let '(s1, more) := fws s w in fwr s1 more).
Proof. unfold fill_window_body, fws, fwr. destruct (Z.leb _ _); reflexivity. Qed.

(* [comment removed for export] *)
Definition fws_s4 (s : deflate_state) (A : arr) (m : Z) : deflate_state :=
  set_block_start (set_strstart (set_match_start (set_window s A) m) (ds_strstart s - 32768)) (ds_block_start s - 32768).
Definition fws_pre (s : deflate_state) (A : arr) (m : Z) : deflate_state :=
  if ds_strstart s - 32768 <? ds_insert s then set_insert (fws_s4 s A m) (ds_strstart s - 32768) else fws_s4 s A m.

Lemma fws_pre_facts s A m : INVG s -> arr_len A = 65536 -> 32768 <= ds_strstart s ->
  let s5 := fws_pre s A m in
  INVG s5 /\ ds_strstart s5 = ds_strstart s - 32768 /\ ds_lookahead s5 = ds_lookahead s /\ ds_high_water s5 = ds_high_water s
  /\ ds_level s5 = ds_level s /\ ds_strm s5 = ds_strm s /\ ds_block_start s5 = ds_block_start s - 32768
  /\ ds_window s5 = A /\ ds_match_start s5 = m /\ ds_prev s5 = ds_prev s /\ ds_head s5 = ds_head s.
Proof.
  intros I LA SS. pose proof (ig_ss s I). pose proof (ig_look s I). pose proof (ig_sl s I). pose proof (ig_ins s I).
  unfold fws_pre, fws_s4. dsr. destruct (Z.ltb_spec (ds_strstart s - 32768) (ds_insert s)); dsr;
      (split; [destruct I; constructor; dsr; first [assumption | lia] | repeat split; reflexivity]).
Qed.

Lemma fws_eq s : INVG s -> fws s 32768 =
  if 65274 <=? ds_strstart s then
    (slide_hash (fws_pre s (arr_blit (ds_window s) 0 (ds_window s) 32768 (ds_strstart s + ds_lookahead s - 32768)) (wrap32 (ds_match_start s - 32768))),
     98304 - (ds_strstart s + ds_lookahead s))
  else (s, 65536 - (ds_strstart s + ds_lookahead s)).
Proof.
  intros I. pose proof (ig_ss s I). pose proof (ig_look s I). pose proof (ig_sl s I).
  unfold fws. rewrite (ig_wsz s I), (ig_wsize s I). unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH.
  rewrite (wrap32_id (65536 - ds_lookahead s - ds_strstart s)) by lia.
  change (32768 + (32768 - (258 + 3 + 1))) with 65274.
  destruct (Z.leb_spec 65274 (ds_strstart s)) as [SL|SL]; [|f_equal; lia].
  rewrite (wrap32_id (32768 - _)) by lia. rewrite (wrap32_id (_ + 32768)) by lia.
  unfold fws_pre, fws_s4. dsr.
  replace (32768 - (65536 - ds_lookahead s - ds_strstart s)) with (ds_strstart s + ds_lookahead s - 32768) by lia.
  f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma fws_facts s : INVG s ->
  let s' := fst (fws s 32768) in let more := snd (fws s 32768) in
  INVG s' /\ more = 65536 - (ds_strstart s' + ds_lookahead s') /\ ds_lookahead s' = ds_lookahead s
  /\ ds_high_water s' = ds_high_water s /\ ds_level s' = ds_level s /\ ds_strm s' = ds_strm s
  /\ ds_block_start s' - ds_strstart s' = ds_block_start s - ds_strstart s
  /\ (ds_strstart s' = ds_strstart s \/ (ds_strstart s' = ds_strstart s - 32768 /\ 65274 <= ds_strstart s)).
Proof.
  intros I. pose proof (ig_ss s I). pose proof (ig_look s I). pose proof (ig_sl s I).
  rewrite (fws_eq s I). destruct (Z.leb_spec 65274 (ds_strstart s)) as [SL|SL]; cbv zeta; cbn [fst snd].
  2:{ split; [exact I|]. repeat split; try reflexivity; try lia. }
  set (A := arr_blit _ 0 _ 32768 _). assert (LA : arr_len A = 65536) by (unfold A; rewrite arr_len_blit; apply (ig_wl s I)). clearbody A.
  set (m := wrap32 _). clearbody m.
  destruct (fws_pre_facts s A m I LA ltac:(lia)) as (I5 & E1 & E2 & E3 & E4 & E5 & E6 & _).
  set (s5 := fws_pre s A m) in *. clearbody s5.
  split; [apply INVG_slide_hash; exact I5|].
  unfold slide_hash. dsr. rewrite E1, E2, E3, E4, E5, E6. repeat split; try reflexivity; try lia.
Qed.

Lemma fws_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> (forall i, i < WHI s1 -> W i) ->
  snd (fws s1 32768) = snd (fws s2 32768)
  /\ REL W C B (bnd - (ds_strstart s1 - ds_strstart (fst (fws s1 32768)))) ms pm (fst (fws s1 32768)) (fst (fws s2 32768))
  /\ WHI (fst (fws s1 32768)) <= WHI s1.
Proof.
  intros R I1 I2 HW. pose proof (ig_ss s1 I1). pose proof (ig_look s1 I1). pose proof (ig_sl s1 I1). pose proof (ig_hw s1 I1).
  rewrite (fws_eq s1 I1), (fws_eq s2 I2). rel_fields R.
  destruct (Z.leb_spec 65274 (ds_strstart s1)) as [SL|SL]; cbn [fst snd].
  2:{ split; [reflexivity|]. split; [|lia]. replace (bnd - (ds_strstart s1 - ds_strstart s1)) with bnd by lia. exact R. }
  split; [reflexivity|].
  pose proof (aeq_blit_self W (ds_window s1) (ds_window s2) 0 32768 (ds_strstart s1 + ds_lookahead s1 - 32768) (r_win _ _ _ _ _ _ _ _ R)
                ltac:(lia) ltac:(lia) ltac:(rewrite (ig_wl s1 I1); lia)) as AW.
  specialize (AW ltac:(intros k Hk; apply HW; unfold WHI; lia)).
  set (A1 := arr_blit (ds_window s1) 0 _ 32768 _) in *. assert (LA1 : arr_len A1 = 65536) by (unfold A1; rewrite arr_len_blit; apply (ig_wl s1 I1)). clearbody A1.
  set (A2 := arr_blit (ds_window s2) 0 _ 32768 _) in *. assert (LA2 : arr_len A2 = 65536) by (unfold A2; rewrite arr_len_blit; apply (ig_wl s2 I2)). clearbody A2.
  assert (R5 : REL W C B bnd ms pm (fws_pre s1 A1 (wrap32 (ds_match_start s1 - 32768))) (fws_pre s2 A2 (wrap32 (ds_match_start s2 - 32768)))).
  { unfold fws_pre, fws_s4. rel_fields R. destruct (Z.ltb_spec (ds_strstart s1 - 32768) (ds_insert s1)).
    all: try apply rel_set_insert; apply rel_set_block_start; apply rel_set_strstart.
    all: apply rel_set_match_start; [|intros Hms; rewrite (r_ms _ _ _ _ _ _ _ _ R Hms); reflexivity].
    all: eapply rel_set_window; [exact R|]; eapply aeq_mono; [exact AW|]; intros i Wi; left; exact Wi. }
  destruct (fws_pre_facts s1 A1 (wrap32 (ds_match_start s1 - 32768)) I1 LA1 ltac:(lia)) as (I51 & E1 & E2 & E3 & _).
  destruct (fws_pre_facts s2 A2 (wrap32 (ds_match_start s2 - 32768)) I2 LA2 ltac:(rel_fields R; lia)) as (I52 & _).
  set (s51 := fws_pre s1 A1 _) in *. clearbody s51. set (s52 := fws_pre s2 A2 _) in *. clearbody s52.
  pose proof (slide_hash_rel _ _ _ _ _ _ _ _ R5 I51 I52) as R6.
  assert (Ess : ds_strstart (slide_hash s51) = ds_strstart s1 - 32768) by (unfold slide_hash; dsr; exact E1).
  rewrite Ess. replace (bnd - (ds_strstart s1 - (ds_strstart s1 - 32768))) with (bnd - 32768) by lia.
  split; [exact R6|]. unfold WHI, slide_hash. dsr. rewrite E1, E2, E3. lia.
Qed.

(* [comment removed for export] *)
Definition lzk (s : deflate_state) : Z * Z * Z * Z * Z * cstrm :=
  (ds_strstart s, ds_lookahead s, ds_high_water s, ds_level s, ds_block_start s, ds_strm s).

Lemma fill_window_insert_lzk : forall f s str, lzk (fill_window_insert f s str) = lzk s.
Proof.
  induction f as [|f IH]; intros s str; [reflexivity|]. rewrite fill_window_insert_step.
  destruct (negb _); [|reflexivity]. cbv zeta. destruct (_ <? _); [|rewrite IH]; unfold insert_string; reflexivity.
Qed.

Lemma fwr_facts s more : INVG s -> more = 65536 - (ds_strstart s + ds_lookahead s) ->
  let s' := fst (fwr s more) in
  INVG s' /\ ds_strstart s' = ds_strstart s /\ ds_high_water s' = ds_high_water s /\ ds_level s' = ds_level s
  /\ ds_block_start s' = ds_block_start s
  /\ ds_lookahead s <= ds_lookahead s' /\ ds_strstart s' + ds_lookahead s' <= 65536
  /\ 0 <= cs_avail_in (ds_strm s') /\ ds_lookahead s' + cs_avail_in (ds_strm s') = ds_lookahead s + cs_avail_in (ds_strm s)
  /\ (snd (fwr s more) = true <-> cs_avail_in (ds_strm s) = 0).
Proof.
  intros I Hm. pose proof (ig_ss s I). pose proof (ig_look s I). pose proof (ig_sl s I). pose proof (ig_ain s I) as AIN.
  unfold fwr. destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0]; cbv zeta; cbn [fst snd].
  { split; [exact I|]. repeat split; try reflexivity; try lia. }
  pose proof (read_buf_len s (RB_window (ds_strstart s + ds_lookahead s)) more ltac:(lia) AIN) as (L1 & L2 & L3).
  pose proof (INVG_read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more I ltac:(lia)) as I'.
  assert (Er : lzk (fst (read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more)) =
              (ds_strstart s, ds_lookahead s, ds_high_water s, ds_level s, ds_block_start s, ds_strm (fst (read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more)))).
  { unfold read_buf, lzk. destruct (_ =? 0); [reflexivity|]. dsr. reflexivity. }
  destruct (read_buf s _ more) as [s' n]. cbn [fst snd] in *.
  unfold lzk in Er.
  pose proof (f_equal (fun p => snd (fst p)) Er) as Ebs. pose proof (f_equal (fun p => snd (fst (fst p))) Er) as Elv.
  pose proof (f_equal (fun p => snd (fst (fst (fst p)))) Er) as Ehw. pose proof (f_equal (fun p => snd (fst (fst (fst (fst p))))) Er) as Elk.
  pose proof (f_equal (fun p => fst (fst (fst (fst (fst p))))) Er) as Ess. cbn [fst snd] in Ebs, Elv, Ehw, Elk, Ess. clear Er.
  pose proof (INVG_set_lookahead s' (ds_lookahead s' + n) ltac:(lia) ltac:(lia) I') as I''.
  match goal with |- INVG ?x /\ _ => set (s'' := x) end.
  assert (F : INVG s'' /\ lzk s'' = lzk (set_lookahead s' (ds_lookahead s' + n))).
  { subst s''. match goal with |- context [if ?c then _ else _] => destruct c end; [|split; [exact I''|reflexivity]].
    rewrite fill_window_insert_lzk. split; [|reflexivity].
    apply INVG_fill_window_insert. apply INVG_set_ins_h, INVG_set_ins_h. exact I''. }
  clearbody s''. destruct F as [F1 F2]. unfold lzk in F2.
  pose proof (f_equal (fun p => snd p) F2) as Est'. pose proof (f_equal (fun p => snd (fst p)) F2) as Ebs'.
  pose proof (f_equal (fun p => snd (fst (fst p))) F2) as Elv'. pose proof (f_equal (fun p => snd (fst (fst (fst p)))) F2) as Ehw'.
  pose proof (f_equal (fun p => snd (fst (fst (fst (fst p))))) F2) as Elk'. pose proof (f_equal (fun p => fst (fst (fst (fst (fst p))))) F2) as Ess'.
  cbn [fst snd] in Est', Ebs', Elv', Ehw', Elk', Ess'. clear F2.
  split; [exact F1|]. dsr. rewrite Est', Ebs', Elv', Ehw', Elk', Ess', Ebs, Elv, Ehw, Ess, Elk, L3.
  repeat split; try reflexivity; try lia.
Qed.

Lemma rel_bnd_up W C B bnd bnd' ms pm s1 s2 : REL W C B bnd ms pm s1 s2 -> bnd <= bnd' -> REL W C B bnd' ms pm s1 s2.
Proof.
  intros R Hb. eapply rel_rebnd; [exact R|]. destruct (r_chain _ _ _ _ _ _ _ _ R) as [CH CP]. split.
  - intros h Hh. eapply cv_mono; [apply CH; exact Hh|auto|exact Hb].
  - intros p Cp. destruct (CP p Cp) as [A X]. split; [exact A|]. eapply cv_mono; [exact X|auto|exact Hb].
Qed.

Definition lz5 (s : deflate_state) : Z * Z * Z * Z * Z :=
  (ds_strstart s, ds_lookahead s, ds_high_water s, ds_level s, ds_block_start s).
Lemma lz5_eqt s' a b c d e : lz5 s' = (a, b, c, d, e) ->
  ds_strstart s' = a /\ ds_lookahead s' = b /\ ds_high_water s' = c /\ ds_level s' = d /\ ds_block_start s' = e.
Proof.
  intros E. unfold lz5 in E.
  pose proof (f_equal (fun p => snd p) E). pose proof (f_equal (fun p => snd (fst p)) E).
  pose proof (f_equal (fun p => snd (fst (fst p))) E). pose proof (f_equal (fun p => snd (fst (fst (fst p)))) E).
  pose proof (f_equal (fun p => fst (fst (fst (fst p)))) E). cbn [fst snd] in *. repeat split; assumption.
Qed.
Lemma lz5_eq s s' : lz5 s' = lz5 s ->
  ds_strstart s' = ds_strstart s /\ ds_lookahead s' = ds_lookahead s /\ ds_high_water s' = ds_high_water s
  /\ ds_level s' = ds_level s /\ ds_block_start s' = ds_block_start s.
Proof.
  intros E. unfold lz5 in E.
  pose proof (f_equal (fun p => snd p) E). pose proof (f_equal (fun p => snd (fst p)) E).
  pose proof (f_equal (fun p => snd (fst (fst p))) E). pose proof (f_equal (fun p => snd (fst (fst (fst p)))) E).
  pose proof (f_equal (fun p => fst (fst (fst (fst p)))) E). cbn [fst snd] in *. repeat split; assumption.
Qed.
Lemma read_buf_lz5 s dst k : lz5 (fst (read_buf s dst k)) = lz5 s.
Proof. unfold read_buf, lz5. destruct (_ =? 0); [reflexivity|]. destruct dst; dsr; reflexivity. Qed.
Lemma read_buf_insert s dst k : ds_insert (fst (read_buf s dst k)) = ds_insert s.
Proof. unfold read_buf. destruct (_ =? 0); [reflexivity|]. destruct dst; dsr; reflexivity. Qed.

Lemma fill_window_insert_lz5 f s str : lz5 (fill_window_insert f s str) = lz5 s.
Proof.
  revert s str. induction f as [|f IH]; intros s str; [reflexivity|]. rewrite fill_window_insert_step.
  destruct (negb _); [|reflexivity]. cbv zeta. destruct (_ <? _); [|rewrite IH]; unfold insert_string; reflexivity.
Qed.

Lemma fwr_rel W C B bnd ms pm s1 s2 more :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> (forall i, i < WHI s1 -> W i) ->
  more = 65536 - (ds_strstart s1 + ds_lookahead s1) -> bnd <= ds_strstart s1 ->
  snd (fwr s1 more) = snd (fwr s2 more)
  /\ exists W' C', (forall p, C p -> C' p) /\ (forall i, i < WHI (fst (fwr s1 more)) -> W' i)
     /\ REL W' C' B (Z.max bnd (ds_strstart s1 - 1)) ms pm (fst (fwr s1 more)) (fst (fwr s2 more)).
Proof.
  intros R I1 I2 HW Hm Hb. pose proof (ig_ss s1 I1). pose proof (ig_look s1 I1). pose proof (ig_sl s1 I1). pose proof (ig_ins s1 I1).
  pose proof (rel_bnd_up _ _ _ bnd (Z.max bnd (ds_strstart s1 - 1)) _ _ _ _ R ltac:(lia)) as R0.
  unfold fwr. rel_fields R.
  destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0) as [A0|A0]; cbv zeta; cbn [fst snd].
  { split; [reflexivity|]. exists W, C. split; [auto|]. split; [exact HW|exact R0]. }
  destruct (read_buf_window_rel _ _ _ _ _ _ _ _ (ds_strstart s1 + ds_lookahead s1) more R0 I1 ltac:(lia)) as (En & Est & R1).
  pose proof (INVG_read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more I1 ltac:(lia)) as I1'.
  pose proof (INVG_read_buf s2 (RB_window (ds_strstart s1 + ds_lookahead s1)) more I2 ltac:(lia)) as I2'.
  pose proof (read_buf_len s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more ltac:(lia) (ig_ain s1 I1)) as (L1 & L2 & L3).
  pose proof (lz5_eq _ _ (read_buf_lz5 s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more)) as (Ess & Elk & Ehw & Elv & Ebs).
  pose proof (read_buf_insert s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more) as Eins.
  destruct (read_buf s1 _ more) as [s1' n]. destruct (read_buf s2 _ more) as [s2' n2]. cbn [fst snd] in *. subst n2.
  split; [reflexivity|].
  set (W' := fun i => W i \/ ds_strstart s1 + ds_lookahead s1 <= i < ds_strstart s1 + ds_lookahead s1 + n) in R1.
  assert (HW' : forall i, i < Z.max (ds_high_water s1) (ds_strstart s1 + ds_lookahead s1 + n) -> W' i).
  { intros i Hi. subst W'. cbv beta. destruct (Z_lt_le_dec i (Z.max (ds_high_water s1) (ds_strstart s1 + ds_lookahead s1))); [left; apply HW; unfold WHI; lia|right; lia]. }
  pose proof (rel_set_lookahead _ _ _ _ _ _ _ _ (ds_lookahead s1' + n) R1) as R2.
  pose proof (INVG_set_lookahead s1' (ds_lookahead s1' + n) ltac:(lia) ltac:(lia) I1') as I1''.
  pose proof (INVG_set_lookahead s2' (ds_lookahead s1' + n) ltac:(lia) ltac:(rel_fields R1; lia) I2') as I2''.
  dsr. rel_fields R1. rewrite Elk, Ess, Eins in *.
  destruct (Z.leb_spec MIN_MATCH (ds_lookahead s1 + n + ds_insert s1)) as [G|G].
  2:{ exists W', C. split; [auto|]. split; [unfold WHI; dsr; rewrite ?Ehw, ?Ess, ?Elk; intros i Hi; apply HW'; lia|exact R2]. }
  unfold MIN_MATCH in G.
  assert (EW0 : arr_get (ds_window s2') (ds_strstart s1 - ds_insert s1) = arr_get (ds_window s1') (ds_strstart s1 - ds_insert s1)).
  { symmetry. apply (aeq_get _ _ _ _ (r_win _ _ _ _ _ _ _ _ R1)); [rewrite (ig_wl _ I1'); lia|]. apply HW'. lia. }
  assert (EW1 : arr_get (ds_window s2') (ds_strstart s1 - ds_insert s1 + 1) = arr_get (ds_window s1') (ds_strstart s1 - ds_insert s1 + 1)).
  { symmetry. apply (aeq_get _ _ _ _ (r_win _ _ _ _ _ _ _ _ R1)); [rewrite (ig_wl _ I1'); lia|]. apply HW'. lia. }
  rewrite EW0, EW1.
  match goal with |- context [fill_window_insert _ (set_ins_h (set_ins_h ?a ?x) _) _] =>
    pose proof (rel_set_ins_h _ _ _ _ _ _ _ _ x R2) as R3;
    pose proof (INVG_set_ins_h _ x I1'') as I13; pose proof (INVG_set_ins_h _ x I2'') as I23 end.
  rewrite (update_hash_rel _ _ _ _ _ _ _ _ _ _ R3).
  match goal with |- context [fill_window_insert _ (set_ins_h (set_ins_h (set_lookahead s1' ?l) ?x) ?y) _] =>
    pose proof (rel_set_ins_h _ _ _ _ _ _ _ _ y R3) as R4;
    pose proof (INVG_set_ins_h _ y I13) as I14; pose proof (INVG_set_ins_h _ y I23) as I24 end.
  match goal with |- context [fill_window_insert ?f ?a (ds_strstart s1 - ds_insert s1)] =>
    destruct (fill_window_insert_rel f W' C B (Z.max bnd (ds_strstart s1 - 1)) ms pm _ _ (ds_strstart s1 - ds_insert s1) (ds_strstart s1) R4 I14 I24)
      as (C' & HC' & R5); try (dsr; unfold MIN_MATCH in *; lia);
    [dsr; intros i Hi; apply HW'; lia|];
    pose proof (lz5_eq _ _ (fill_window_insert_lz5 f a (ds_strstart s1 - ds_insert s1))) as (Fss & Flk & Fhw & Flv & Fbs)
  end.
  exists W', C'. split; [exact HC'|]. split; [|exact R5].
  unfold WHI. rewrite Fss, Flk, Fhw. dsr. rewrite ?Ehw. intros i Hi; apply HW'; lia.
Qed.

(* [comment removed for export] *)
Lemma fill_window_body_facts s : INVG s ->
  let s' := fst (fill_window_body s 32768) in
  INVG s' /\ ds_high_water s' = ds_high_water s /\ ds_level s' = ds_level s
  /\ ds_block_start s' - ds_strstart s' = ds_block_start s - ds_strstart s
  /\ ds_strstart s' + ds_lookahead s' <= 65536.
Proof.
  intros I. rewrite fill_window_body_eq.
  pose proof (fws_facts s I) as (I1 & Em & Elk & Ehw & Elv & Est & Ebs & Ess).
  destruct (fws s 32768) as [s1 more]. cbn [fst snd] in *.
  pose proof (fwr_facts s1 more I1 Em) as (I2 & Ess2 & Ehw2 & Elv2 & Ebs2 & _ & SL & _).
  cbv zeta. set (s2 := fst (fwr s1 more)) in *. clearbody s2.
  split; [exact I2|]. rewrite Ehw2, Elv2, Ebs2, Ess2, Ehw, Elv. repeat split; try reflexivity; lia.
Qed.

Lemma fill_window_body_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> (forall i, i < WHI s1 -> W i) -> bnd <= ds_strstart s1 ->
  snd (fill_window_body s1 32768) = snd (fill_window_body s2 32768)
  /\ exists W' C' bnd', (forall p, C p -> C' p) /\ (forall i, i < WHI (fst (fill_window_body s1 32768)) -> W' i)
     /\ bnd' <= ds_strstart (fst (fill_window_body s1 32768))
     /\ REL W' C' B bnd' ms pm (fst (fill_window_body s1 32768)) (fst (fill_window_body s2 32768)).
Proof.
  intros R I1 I2 HW Hb. rewrite !fill_window_body_eq.
  pose proof (fws_facts s1 I1) as (I1' & Em & Elk & Ehw & Elv & Est & Ebs & Ess).
  pose proof (fws_facts s2 I2) as (I2' & _).
  pose proof (fws_rel _ _ _ _ _ _ _ _ R I1 I2 HW) as (Emore & R1 & WH1).
  destruct (fws s1 32768) as [s1' more]. destruct (fws s2 32768) as [s2' more2]. cbn [fst snd] in *. subst more2.
  assert (HW1 : forall i, i < WHI s1' -> W i) by (intros i Hi; apply HW; lia).
  assert (Hb1 : bnd - (ds_strstart s1 - ds_strstart s1') <= ds_strstart s1') by lia.
  pose proof (fwr_rel _ _ _ _ _ _ _ _ more R1 I1' I2' HW1 Em Hb1) as (Ebrk & W' & C' & HC' & HW' & R2).
  pose proof (fwr_facts s1' more I1' Em) as (_ & Ess2 & _).
  cbv zeta. split; [exact Ebrk|]. exists W', C', (Z.max (bnd - (ds_strstart s1 - ds_strstart s1')) (ds_strstart s1' - 1)).
  split; [exact HC'|]. split; [exact HW'|]. split; [rewrite Ess2; lia|exact R2].
Qed.

Lemma fill_window_loop_facts f : forall s, INVG s ->
  let s' := fill_window_loop f s 32768 in
  INVG s' /\ ds_high_water s' = ds_high_water s /\ ds_level s' = ds_level s
  /\ ds_block_start s' - ds_strstart s' = ds_block_start s - ds_strstart s.
Proof.
  induction f as [|f IH]; intros s I; cbn [fill_window_loop].
  - split; [exact I|]. repeat split; reflexivity.
  - pose proof (fill_window_body_facts s I) as (I1 & Ehw & Elv & Ebs & _).
    destruct (fill_window_body s 32768) as [s1 brk]. cbn [fst] in *.
    destruct brk; [split; [exact I1|repeat split; assumption]|].
    destruct (_ && _); [|split; [exact I1|repeat split; assumption]].
    destruct (IH s1 I1) as (I2 & Ehw2 & Elv2 & Ebs2). cbv zeta. rewrite Ehw2, Elv2, Ebs2. split; [exact I2|repeat split; assumption].
Qed.

Lemma fill_window_loop_rel f : forall W C B bnd ms pm s1 s2,
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> (forall i, i < WHI s1 -> W i) -> bnd <= ds_strstart s1 ->
  exists W' C' bnd', (forall p, C p -> C' p) /\ (forall i, i < WHI (fill_window_loop f s1 32768) -> W' i)
     /\ bnd' <= ds_strstart (fill_window_loop f s1 32768)
     /\ REL W' C' B bnd' ms pm (fill_window_loop f s1 32768) (fill_window_loop f s2 32768).
Proof.
  induction f as [|f IH]; intros W C B bnd ms pm s1 s2 R I1 I2 HW Hb; cbn [fill_window_loop].
  - exists W, C, bnd. split; [auto|]. split; [exact HW|]. split; [exact Hb|exact R].
  - pose proof (fill_window_body_rel _ _ _ _ _ _ _ _ R I1 I2 HW Hb) as (Ebrk & W' & C' & bnd' & HC' & HW' & Hb' & R1).
    pose proof (fill_window_body_facts s1 I1) as (I1' & _). pose proof (fill_window_body_facts s2 I2) as (I2' & _).
    destruct (fill_window_body s1 32768) as [s1' brk]. destruct (fill_window_body s2 32768) as [s2' brk2]. cbn [fst snd] in *. subst brk2.
    destruct brk; [exists W', C', bnd'; split; [exact HC'|]; split; [exact HW'|]; split; [exact Hb'|exact R1]|].
    rel_fields R1. destruct (_ && _); [|exists W', C', bnd'; split; [exact HC'|]; split; [exact HW'|]; split; [exact Hb'|exact R1]].
    destruct (IH _ _ _ _ _ _ _ _ R1 I1' I2' HW' Hb') as (W'' & C'' & bnd'' & HC'' & HW'' & Hb'' & R2).
    exists W'', C'', bnd''. split; [intros p Cp; apply HC'', HC', Cp|]. split; [exact HW''|]. split; [exact Hb''|exact R2].
Qed.

(* [comment removed for export] *)
Lemma fill_window_high_facts s : INVG s ->
  let s' := fill_window_high s in
  INVG s' /\ lz5 s' = (ds_strstart s, ds_lookahead s, ds_high_water s', ds_level s, ds_block_start s)
  /\ ds_high_water s <= ds_high_water s' /\ Z.min (ds_strstart s + ds_lookahead s + 258) 65536 <= ds_high_water s'.
Proof.
  intros I. split; [apply INVG_fill_window_high; exact I|].
  pose proof (ig_hw s I) as Hhw. pose proof (ig_sl s I) as Hsl. pose proof (ig_ss s I). pose proof (ig_look s I).
  unfold fill_window_high, lz5. rewrite (ig_wsz s I). unfold WIN_INIT, MAX_MATCH.
  destruct (Z.ltb_spec (ds_high_water s) 65536) as [L1|L1]; [|dsr; repeat split; try reflexivity; lia].
  destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)) as [L2|L2]; dsr.
  - destruct (Z.ltb_spec 258 (65536 - (ds_strstart s + ds_lookahead s))); repeat split; try reflexivity; lia.
  - destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + 258)) as [L3|L3]; dsr; [|repeat split; try reflexivity; lia].
    destruct (Z.ltb_spec (65536 - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); repeat split; try reflexivity; lia.
Qed.

Lemma fill_window_facts s : INVG s ->
  let s' := fill_window s in
  INVG s' /\ ds_level s' = ds_level s /\ ds_block_start s' - ds_strstart s' = ds_block_start s - ds_strstart s
  /\ ds_high_water s <= ds_high_water s'
  /\ Z.min (ds_strstart s' + ds_lookahead s' + 258) 65536 <= ds_high_water s'.
Proof.
  intros I. unfold fill_window. rewrite (ig_wsize s I).
  pose proof (fill_window_loop_facts 263 s I) as (I1 & Ehw & Elv & Ebs).
  set (s1 := fill_window_loop 263 s 32768) in *. clearbody s1.
  pose proof (fill_window_high_facts s1 I1) as (I2 & E5 & Hhw & Hmin).
  apply lz5_eqt in E5. destruct E5 as (Ess2 & Elk2 & _ & Elv2 & Ebs2). cbv zeta.
  split; [exact I2|]. rewrite Elv2, Ebs2, Ess2, Elk2, Elv, Ebs. repeat split; try reflexivity; lia.
Qed.

Lemma fill_window_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> (forall i, i < WHI s1 -> W i) -> bnd <= ds_strstart s1 ->
  exists W' C' bnd', (forall p, C p -> C' p) /\ (forall i, i < WHI (fill_window s1) -> W' i)
     /\ bnd' <= ds_strstart (fill_window s1)
     /\ REL W' C' B bnd' ms pm (fill_window s1) (fill_window s2).
Proof.
  intros R I1 I2 HW Hb. unfold fill_window. rel_fields R. rewrite (ig_wsize s1 I1).
  pose proof (fill_window_loop_rel 263 _ _ _ _ _ _ _ _ R I1 I2 HW Hb) as (W' & C' & bnd' & HC' & HW' & Hb' & R1).
  pose proof (fill_window_loop_facts 263 s1 I1) as (I1' & _). pose proof (fill_window_loop_facts 263 s2 I2) as (I2' & _).
  set (s1' := fill_window_loop 263 s1 32768) in *. clearbody s1'. set (s2' := fill_window_loop 263 s2 32768) in *. clearbody s2'.
  pose proof (fill_window_high_rel _ _ _ _ _ _ _ _ R1 I1' I2' HW') as (W'' & HW'' & R2).
  pose proof (fill_window_high_facts s1' I1') as (_ & E5 & _). apply lz5_eqt in E5. destruct E5 as (Ess & _).
  exists W'', C', bnd'. split; [exact HC'|]. split; [exact HW''|]. split; [rewrite Ess; exact Hb'|exact R2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LM.
  Variable w1 : arr.
Variable w2 : arr.
  (* [comment removed for export] *)
  Variable lim : Z.
  Hypothesis WEQ : forall i, 0 <= i <= lim -> arr_get w2 i = arr_get w1 i.

  Lemma lm_cmpk_rel k : forall scan mtch,
    0 <= scan -> 0 <= mtch -> scan + Z.of_nat k <= lim -> mtch + Z.of_nat k <= lim ->
    lm_cmpk k w2 scan mtch = lm_cmpk k w1 scan mtch
    /\ (let '(scan', mtch', ok) := lm_cmpk k w1 scan mtch in
        scan < scan' <= scan + Z.of_nat k /\ mtch' - mtch = scan' - scan /\ (ok = true -> scan' = scan + Z.of_nat k) \/ (k = 0%nat /\ scan' = scan /\ mtch' = mtch)).
  Proof.
    induction k as [|k IH]; intros scan mtch Hs Hm Ls Lm; cbn [lm_cmpk].
    - split; [reflexivity|]. right. repeat split; reflexivity.
    - rewrite !WEQ by lia. destruct (Z.eqb _ _).
      + destruct (IH (scan + 1) (mtch + 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [E F]. rewrite E. split; [reflexivity|].
        destruct (lm_cmpk k w1 (scan + 1) (mtch + 1)) as [[scan' mtch'] ok]. left.
        destruct F as [(F1 & F2 & F3)|(F1 & F2 & F3)]; [|subst; cbn; lia]. repeat split; try lia. intros Hok. rewrite (F3 Hok). lia.
      + split; [reflexivity|]. left. repeat split; try lia. all: intros X; discriminate X.
  Qed.

  Lemma lm_cmp_loop_rel f : forall scan mtch strend,
    0 <= scan < strend -> 0 <= mtch -> (strend - scan) mod 8 = 0 -> strend <= lim -> mtch + (strend - scan) <= lim ->
    lm_cmp_loop f w2 scan mtch strend = lm_cmp_loop f w1 scan mtch strend
    /\ scan <= lm_cmp_loop f w1 scan mtch strend <= strend.
  Proof.
    induction f as [|f IH]; intros scan mtch strend Hs Hm M8 Ls Lm; cbn [lm_cmp_loop]; [split; [reflexivity|lia]|].
    assert (D : scan + 8 <= strend) by (Z.to_euclidean_division_equations; lia).
    destruct (lm_cmpk_rel 8 scan mtch ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as [E F]. rewrite E.
    destruct (lm_cmpk 8 w1 scan mtch) as [[scan' mtch'] ok].
    destruct F as [(F1 & F2 & F3)|(F1 & _)]; [|discriminate F1].
    destruct ok; cbn [andb].
    - specialize (F3 eq_refl). cbn in F3. destruct (Z.ltb_spec scan' strend).
      + destruct (IH scan' mtch' strend ltac:(lia) ltac:(lia) ltac:(subst scan'; Z.to_euclidean_division_equations; lia) Ls ltac:(lia)) as [E2 B2].
        rewrite E2. split; [reflexivity|lia].
      + split; [reflexivity|lia].
    - split; [reflexivity|cbn in F1; lia].
  Qed.
End LM.

Definition lmb_out (r : deflate_state * Z * Z * Z * Z * Z * bool) : Z * Z * Z * Z * Z * bool :=
  let '(s, b, e1, e, c, ch, k) := r in (b, e1, e, c, ch, k).
Definition lmb_st (r : deflate_state * Z * Z * Z * Z * Z * bool) : deflate_state :=
  let '(s, b, e1, e, c, ch, k) := r in s.

Lemma window_eq_upto W C B bnd ms pm s1 s2 lim :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> (forall i, 0 <= i <= lim -> W i) -> lim < 65536 ->
  forall i, 0 <= i <= lim -> arr_get (ds_window s2) i = arr_get (ds_window s1) i.
Proof.
  intros R I1 HW Hl i Hi. symmetry. apply (aeq_get _ _ _ _ (r_win _ _ _ _ _ _ _ _ R)); [rewrite (ig_wl s1 I1); lia|apply HW; lia].
Qed.

Lemma longest_match_body_rel W C B bnd ms pm s1 s2 cur chain best nice limit se1 se :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
  (forall i, 0 <= i <= ds_strstart s1 + 258 -> W i) -> ds_strstart s1 + 258 < 65536 ->
  bnd <= ds_strstart s1 -> 0 <= limit -> cv C bnd cur -> cur <> 0 -> 1 <= best <= 258 ->
  (MIN_MATCH <= best -> ms = true) ->
  let r1 := longest_match_body s1 cur chain best nice limit se1 se in
  let r2 := longest_match_body s2 cur chain best nice limit se1 se in
  lmb_out r1 = lmb_out r2
  /\ exists ms', (ms = true -> ms' = true)
     /\ REL W C B bnd ms' pm (lmb_st r1) (lmb_st r2)
     /\ ((lmb_st r1 = s1 /\ lmb_st r2 = s2) \/ (lmb_st r1 = set_match_start s1 cur /\ lmb_st r2 = set_match_start s2 cur))
     /\ (let '(best', e1', e', cur', ch', cont) := lmb_out r1 in
         1 <= best' <= 258 /\ (MIN_MATCH <= best' -> ms' = true) /\ (cont = true -> cv C bnd cur' /\ cur' <> 0)).
Proof.
  intros R I1 I2 HW Hss Hb Hlim Hcv Hc0 Hbest Hg.
  pose proof (ig_ss s1 I1) as SS0. destruct Hcv as [Rg [->|[Cle Cc]]]; [exfalso; exact (Hc0 eq_refl)|].
  pose proof (window_eq_upto _ _ _ _ _ _ _ _ (ds_strstart s1 + 258) R I1 HW Hss) as WE.
  assert (EP : arr_get (ds_prev s2) (Z.land cur 32767) = arr_get (ds_prev s1) (Z.land cur 32767)).
  { symmetry. pose proof (land_wmask cur). apply (aeq_get _ _ _ _ (r_prev _ _ _ _ _ _ _ _ R)); [rewrite (ig_pl s1 I1); lia|exact Cc]. }
  pose proof (r_chain _ _ _ _ _ _ _ _ R) as [CH CP]. destruct (CP _ Cc) as [_ CVn].
  pose proof (ig_wmask s1 I1) as M1. pose proof (ig_wmask s2 I2) as M2.
  unfold longest_match_body. rel_fields R. unfold MAX_MATCH.
  rewrite !(WE (cur + best)), !(WE (cur + best - 1)), !(WE cur), !(WE (cur + 1)), !(WE (ds_strstart s1)), !(WE (ds_strstart s1 + 1)) by lia.
  destruct (lm_cmp_loop_rel (ds_window s1) (ds_window s2) (ds_strstart s1 + 258) WE 33 (ds_strstart s1 + 2) (cur + 2) (ds_strstart s1 + 258)
              ltac:(lia) ltac:(lia) ltac:(replace (ds_strstart s1 + 258 - (ds_strstart s1 + 2)) with 256 by lia; reflexivity) ltac:(lia) ltac:(lia)) as [EL BL].
  rewrite !EL. set (scan' := lm_cmp_loop 33 (ds_window s1) (ds_strstart s1 + 2) (cur + 2) (ds_strstart s1 + 258)) in *. clearbody scan'.
  (* [comment removed for export] *)
  assert (TAIL : forall ms1 t1 t2 b e1 e,
    REL W C B bnd ms1 pm t1 t2 -> (ms = true -> ms1 = true) -> ds_prev t1 = ds_prev s1 -> ds_prev t2 = ds_prev s2 ->
    ds_w_mask t1 = 32767 -> ds_w_mask t2 = 32767 ->
    ((t1 = s1 /\ t2 = s2) \/ (t1 = set_match_start s1 cur /\ t2 = set_match_start s2 cur)) ->
    1 <= b <= 258 -> (MIN_MATCH <= b -> ms1 = true) ->
    let r1 := (let cur_match := arr_get (ds_prev t1) (Z.land cur (ds_w_mask t1)) in
               if limit <? cur_match then let chain_length := wrap32 (chain - 1) in
                 if negb (chain_length =? 0) then (t1, b, e1, e, cur_match, chain_length, true) else (t1, b, e1, e, cur_match, chain_length, false)
               else (t1, b, e1, e, cur_match, chain, false)) in
    let r2 := (let cur_match := arr_get (ds_prev t2) (Z.land cur (ds_w_mask t2)) in
               if limit <? cur_match then let chain_length := wrap32 (chain - 1) in
                 if negb (chain_length =? 0) then (t2, b, e1, e, cur_match, chain_length, true) else (t2, b, e1, e, cur_match, chain_length, false)
               else (t2, b, e1, e, cur_match, chain, false)) in
    lmb_out r1 = lmb_out r2 /\ exists ms', (ms = true -> ms' = true) /\ REL W C B bnd ms' pm (lmb_st r1) (lmb_st r2)
      /\ ((lmb_st r1 = s1 /\ lmb_st r2 = s2) \/ (lmb_st r1 = set_match_start s1 cur /\ lmb_st r2 = set_match_start s2 cur))
      /\ (let '(best', e1', e', cur', ch', cont) := lmb_out r1 in
          1 <= best' <= 258 /\ (MIN_MATCH <= best' -> ms' = true) /\ (cont = true -> cv C bnd cur' /\ cur' <> 0))).
  { intros ms1 t1 t2 b e1 e RT Hms P1 P2 W1 W2 HT Hb' Hg'. cbv zeta. rewrite P1, P2, W1, W2, EP.
    set (nx := arr_get (ds_prev s1) (Z.land cur 32767)) in *.
    destruct (Z.ltb_spec limit nx); [destruct (negb _)|]; cbn [lmb_out lmb_st];
      (split; [reflexivity|]); exists ms1; (split; [exact Hms|]); (split; [exact RT|]); (split; [exact HT|]);
      (split; [exact Hb'|]); (split; [exact Hg'|]); intros X; try discriminate X; split; [exact CVn|lia]. }
  match goal with |- context [if ?c then (s1, best, se1, se, false) else _] => destruct c eqn:Ec end.
  - cbv iota beta. apply (TAIL ms); auto; left; split; reflexivity.
  - destruct (Z.ltb_spec best (258 - (ds_strstart s1 + 258 - scan'))) as [LT|LT].
    + rewrite !(WE (ds_strstart s1 + (258 - (ds_strstart s1 + 258 - scan')) - 1)), !(WE (ds_strstart s1 + (258 - (ds_strstart s1 + 258 - scan')))) by lia.
      assert (R' : REL W C B bnd true pm (set_match_start s1 cur) (set_match_start s2 cur)).
      { eapply rel_flags; [apply rel_set_match_start; [exact R|reflexivity] | dsr; reflexivity | dsr; exact (r_pm _ _ _ _ _ _ _ _ R) | reflexivity | dsr; exact (r_g2 _ _ _ _ _ _ _ _ R) | reflexivity]. }
      destruct (Z.leb_spec nice (258 - (ds_strstart s1 + 258 - scan'))); cbv iota beta.
      * cbn [lmb_out lmb_st]. split; [reflexivity|]. exists true. split; [auto|]. split; [exact R'|]. split; [right; split; reflexivity|].
        split; [lia|]. split; [reflexivity|]. intros X; discriminate X.
      * apply (TAIL true); auto; try reflexivity; try lia.
    + cbv iota beta. apply (TAIL ms); auto; left; split; reflexivity.
Qed.

Lemma longest_match_loop_rel f : forall W C B bnd ms pm s1 s2 cur chain best nice limit se1 se,
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
  (forall i, 0 <= i <= ds_strstart s1 + 258 -> W i) -> ds_strstart s1 + 258 < 65536 ->
  bnd <= ds_strstart s1 -> 0 <= limit -> cv C bnd cur -> cur <> 0 -> 1 <= best <= 258 ->
  (MIN_MATCH <= best -> ms = true) ->
  let r1 := longest_match_loop f s1 cur chain best nice limit se1 se in
  let r2 := longest_match_loop f s2 cur chain best nice limit se1 se in
  snd r1 = snd r2
  /\ exists ms', (ms = true -> ms' = true) /\ REL W C B bnd ms' pm (fst r1) (fst r2)
     /\ INVG (fst r1) /\ INVG (fst r2) /\ lz5 (fst r1) = lz5 s1 /\ clean (fst r1) = clean s1
     /\ 1 <= snd r1 <= 258 /\ (MIN_MATCH <= snd r1 -> ms' = true).
Proof.
  induction f as [|f IH]; intros W C B bnd ms pm s1 s2 cur chain best nice limit se1 se R I1 I2 HW Hss Hb Hlim Hcv Hc0 Hbest Hg; cbn [longest_match_loop].
  - cbn [fst snd]. split; [reflexivity|]. exists ms. split; [auto|]. split; [exact R|]. split; [exact I1|]. split; [exact I2|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbest|exact Hg].
  - pose proof (longest_match_body_rel _ _ _ _ _ _ _ _ cur chain best nice limit se1 se R I1 I2 HW Hss Hb Hlim Hcv Hc0 Hbest Hg) as BR.
    cbv zeta in BR. destruct BR as (Eo & ms' & Hms' & R' & ST & INVS).
    destruct (longest_match_body s1 cur chain best nice limit se1 se) as [[[[[[t1 b1] e11] e1'] c1] ch1] k1].
    destruct (longest_match_body s2 cur chain best nice limit se1 se) as [[[[[[t2 b2] e12] e2'] c2] ch2] k2].
    cbn [lmb_out lmb_st] in *. injection Eo; intros <- <- <- <- <- <-. destruct INVS as (Hb1 & Hg1 & Hk).
    assert (TF : INVG t1 /\ INVG t2 /\ lz5 t1 = lz5 s1 /\ clean t1 = clean s1 /\ ds_strstart t1 = ds_strstart s1).
    { destruct ST as [[-> ->]|[-> ->]]; [split; [exact I1|]; split; [exact I2|]; repeat split; reflexivity|].
      split; [apply INVG_set_match_start; exact I1|]. split; [apply INVG_set_match_start; exact I2|]. repeat split; reflexivity. }
    destruct TF as (J1 & J2 & L5 & CL & Ess).
    destruct k1.
    + destruct (Hk eq_refl) as [Hcv' Hc0'].
      destruct (IH W C B bnd ms' pm t1 t2 c1 ch1 b1 nice limit e11 e1' R' J1 J2 ltac:(rewrite Ess; exact HW) ltac:(rewrite Ess; exact Hss) ltac:(rewrite Ess; exact Hb) Hlim Hcv' Hc0' Hb1 Hg1)
        as (Eo2 & ms'' & Hms'' & R'' & K1 & K2 & L5' & CL' & Hb2 & Hg2).
      split; [exact Eo2|]. exists ms''. split; [auto|]. split; [exact R''|]. split; [exact K1|]. split; [exact K2|].
      split; [rewrite L5'; exact L5|]. split; [rewrite CL'; exact CL|]. split; [exact Hb2|exact Hg2].
    + cbn [fst snd]. split; [reflexivity|]. exists ms'. split; [exact Hms'|]. split; [exact R'|]. split; [exact J1|]. split; [exact J2|].
      split; [exact L5|]. split; [exact CL|]. split; [exact Hb1|exact Hg1].
Qed.

Lemma longest_match_rel W C B bnd ms pm s1 s2 cur :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
  (forall i, 0 <= i <= ds_strstart s1 + 258 -> W i) -> ds_strstart s1 + 258 < 65536 ->
  bnd <= ds_strstart s1 -> cv C bnd cur -> cur <> 0 -> 1 <= ds_prev_length s1 ->
  let r1 := longest_match s1 cur in let r2 := longest_match s2 cur in
  snd r1 = snd r2
  /\ exists ms', (ms = true -> ms' = true) /\ REL W C B bnd ms' pm (fst r1) (fst r2)
     /\ INVG (fst r1) /\ INVG (fst r2) /\ lz5 (fst r1) = lz5 s1 /\ clean (fst r1) = clean s1
     /\ 0 <= snd r1 <= 258 /\ (MIN_MATCH <= snd r1 -> ms' = true) /\ snd r1 <= ds_lookahead s1.
Proof.
  intros R I1 I2 HW Hss Hb Hcv Hc0 Hpl1.
  pose proof (ig_pvl s1 I1) as PL. pose proof (ig_ss s1 I1). pose proof (ig_look s1 I1).
  pose proof (window_eq_upto _ _ _ _ _ _ _ _ (ds_strstart s1 + 258) R I1 HW Hss) as WE.
  unfold longest_match. rel_fields R. rewrite (ig_wsize s1 I1). unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH, NIL.
  rewrite !(WE (ds_strstart s1 + ds_prev_length s1 - 1)), !(WE (ds_strstart s1 + ds_prev_length s1)) by lia.
  set (limit := if 32768 - (258 + 3 + 1) <? ds_strstart s1 then ds_strstart s1 - (32768 - (258 + 3 + 1)) else 0).
  assert (Hlim : 0 <= limit) by (subst limit; destruct (Z.ltb_spec (32768 - (258 + 3 + 1)) (ds_strstart s1)); lia).
  clearbody limit.
  set (chain := if ds_good_match s1 <=? ds_prev_length s1 then Z.shiftr (ds_max_chain_length s1) 2 else ds_max_chain_length s1). clearbody chain.
  set (nice := if ds_lookahead s1 <? ds_nice_match s1 then ds_lookahead s1 else ds_nice_match s1). clearbody nice.
  pose proof (longest_match_loop_rel (Z.to_nat chain) _ _ _ _ _ _ _ _ cur chain (ds_prev_length s1) nice limit
                (arr_get (ds_window s1) (ds_strstart s1 + ds_prev_length s1 - 1)) (arr_get (ds_window s1) (ds_strstart s1 + ds_prev_length s1))
                R I1 I2 HW Hss Hb Hlim Hcv Hc0 ltac:(lia) ltac:(intros Hp; exact (r_g3 _ _ _ _ _ _ _ _ R (r_g2 _ _ _ _ _ _ _ _ R Hp)))) as LR.
  cbv zeta in LR. destruct LR as (Eo & ms' & Hms' & R' & J1 & J2 & L5 & CL & Hb' & Hg').
  destruct (longest_match_loop _ s1 _ _ _ _ _ _ _) as [t1 b1]. destruct (longest_match_loop _ s2 _ _ _ _ _ _ _) as [t2 b2].
  cbn [fst snd] in *. subst b2.
  pose proof (lz5_eq _ _ L5) as (_ & Elk & _). rel_fields R'. rewrite Elk.
  destruct (Z.leb_spec b1 (ds_lookahead s1)); cbn [fst snd].
  - split; [reflexivity|]. exists ms'. repeat (split; [assumption|]). split; [lia|]. split; [exact Hg'|lia].
  - split; [reflexivity|]. exists ms'. repeat (split; [assumption|]). split; [lia|]. split; [intros Hl; apply Hg'; unfold MIN_MATCH; lia|lia].
Qed.
