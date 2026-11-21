(** * Bridge.DMatch.MEntry — group M: pair D1 (deflateInit2 + reset, as the
    harness reaches it), for every level 0-9 and every input.

    Generalises [IProbe.deflate_entry_related] from one input to all inputs.
    The S5 state at the entry is [set_strm (dsC level) cs]: the five
    stream-free clusters of [dst_rel] read only fields of [dsC level], a
    closed term per level, so they are checked by computation once per
    level (as [IProbe] does).  The stream cluster depends on the input and is
    proved for all inputs.  RT's state is [deflate_reset (cf_geom level) 1]
    with the call installed ([m_rt_new]); [defl_wf] and [mt_inv] hold of it
    symbolically. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz Deflate HarnessCompress.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require IProbe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MReadBuf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module HC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.HarnessCompress.

(* ------------------------------------------------------------------------- *)
(* 1.  RT's entry state, symbolically                                        *)
(* ------------------------------------------------------------------------- *)

Lemma m_zdefl_level : forall level, 0 <= level -> RC.zdefl_level level = level.
Proof. intros level H. unfold RC.zdefl_level. destruct (Z.eqb_spec level (-1)); lia. Qed.

Lemma m_rt_new : forall level, 0 <= level <= 9 ->
  RD.defl_new level 8 15 8 0 = Some (RD.deflate_reset (cf_geom level) 1).
Proof.
  intros level Hl. unfold RD.defl_new, RC.defl_init2.
  rewrite m_zdefl_level by lia.
  change (RC.defl_wrap 15) with (Some (1, 15)). cbv beta iota.
  assert (Hok : RC.defl_args_ok level 8 15 8 0 1 = true).
  { unfold RC.defl_args_ok.
    rewrite (proj2 (Z.leb_le 0 level)) by lia. rewrite (proj2 (Z.leb_le level 9)) by lia.
    reflexivity. }
  rewrite Hok. reflexivity.
Qed.

Lemma m_cf_level : forall level, 0 <= level -> RC.dg_level (cf_geom level) = level.
Proof. intros level H. unfold cf_geom, RC.defl_geom_wrap. cbn [RC.dg_level]. apply m_zdefl_level, H. Qed.

Definition rt_call (level : Z) (data : list Z) : RD.DSt :=
  let t0 := RD.deflate_reset (cf_geom level) 1 in
  RD.setD_strm (RD.setZ_availout (SDfl.compressBound_m (zlength data))
                  (RD.setZ_in data (RD.d_strm t0))) t0.

Lemma m_rt_entry : forall level data, 0 <= level <= 9 ->
  IProbe.rt_entry level data = Some (rt_call level data).
Proof. intros level data Hl. unfold IProbe.rt_entry. rewrite m_rt_new by exact Hl. reflexivity. Qed.

Lemma m_rt_call_wf : forall level data, 0 <= level <= 9 -> RD.defl_wf (rt_call level data).
Proof.
  intros level data Hl. unfold rt_call. cbv zeta.
  constructor; cbn [RD.d_wrap RD.d_cfg RD.d_ls RD.d_ts RD.setD_strm RD.deflate_reset].
  - lia.
  - rewrite m_cf_level by lia. unfold cf_geom. f_equal; reflexivity.
  - unfold RD.lm_init, RD.clear_hash. cbn. mgeom. lia.
  - reflexivity.
  - unfold RD.lm_init, RD.clear_hash. cbn. mgeom. lia.
  - unfold cf_geom, RC.defl_geom_wrap. constructor; cbn; mclosed.
Qed.

Lemma m_rt_call_inv : forall level data, 0 <= level <= 9 ->
  zlength data <= 1048573 -> Forall (fun b => 0 <= b < 256) data ->
  mt_inv (rt_call level data).
Proof.
  intros level data Hl Hn Hb.
  assert (Hz : Chunk.zlen data = zlength data) by reflexivity.
  assert (Hz0 : 0 <= zlength data) by apply zlength_nonneg.
  pose proof (RK.ms_init level (RD.deflate_reset (cf_geom level) 1)
                (RD.setZ_availout (SDfl.compressBound_m (zlength data))
                   (RD.setZ_in data (RD.d_strm (RD.deflate_reset (cf_geom level) 1))))
                (m_rt_new level Hl)) as Hms.
  cbv zeta in Hms. destruct Hms as (Hms & Hfa & Hsl).
  unfold rt_call. cbv zeta.
  constructor; [| | | | exact Hms | intros _; exact Hfa | intros _; exact Hsl | ..];
    cbn [RD.d_wrap RD.d_cfg RD.d_ls RD.d_ts RD.d_strm RD.setD_strm RD.deflate_reset
         RD.setZ_availout RD.setZ_in RD.zs_in RD.zs_done RD.zs_totalin].
  all: unfold RD.lm_init, RD.clear_hash.
  all: cbn [RD.setL_insh RD.setL_matchavail RD.setL_prevlen RD.setL_matchlen RD.setL_insert
            RD.setL_lookahead RD.setL_blockstart RD.setL_strstart RD.setL_head RD.setL_windowsize
            RD.ls_window RD.ls_prev RD.ls_head RD.ls_insh RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch
            RD.ls_matchavail RD.ls_strstart RD.ls_matchstart RD.ls_lookahead RD.ls_prevlen RD.ls_insert
            RD.ls_highwater RD.ls_windowsize].
  - rewrite m_cf_level; lia.
  - rewrite m_cf_level by lia. reflexivity.
  - reflexivity.
  - unfold rb_ok. cbn [RD.d_wrap RD.d_strm RD.setD_strm RD.deflate_reset RD.setZ_availout RD.setZ_in
                       RD.zs_in RD.zs_totalin].
    rewrite Hz. split; [right; reflexivity|]. mpow. lia.
  - intros i _. unfold Base.zzero, Base.zconst. lia.
  - left; reflexivity.
  - unfold RC.MIN_MATCH. lia.
  - lia.
  - lia.
  - exists 0. split; [lia|]. split; [reflexivity|]. lia.
  - change (Chunk.zlen []) with 0. rewrite Hz. mpow. lia.
  - lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The stream-free clusters, by computation per level                    *)
(* ------------------------------------------------------------------------- *)

Definition m_core_ok (level : Z) : bool :=
  let s0 := HC.dsC level in
  let t0 := RD.deflate_reset (cf_geom level) 1 in
  geom_relb s0 t0 && lz_relb s0 t0 && bw_relb s0 (RT.ts_bw (RD.d_ts t0)) && sym_relb s0 t0
  && tree_relb s0 t0
  && (RD.zs_totalin (RD.d_strm t0) =? ZIface.zs_total_in (HC.dzC level))
  && (RD.zs_totalout (RD.d_strm t0) =? ZIface.zs_total_out (HC.dzC level))
  && (RD.zs_adler (RD.d_strm t0) =? ZIface.zs_adler (HC.dzC level))
  && (RD.zs_datatype (RD.d_strm t0) =? ZIface.zs_data_type (HC.dzC level)).

(** One [vm_compute] per level (0.4 s each on the box).  Do not use
    [injection] on a list of [m_core_ok] values: it head-reduces each
    [m_core_ok l] lazily, which evaluates S5's deflateInit2 symbolically. *)
Lemma m_core_ok_level : forall level, 0 <= level <= 9 -> m_core_ok level = true.
Proof.
  intros level Hl.
  assert (Hc : level = 0 \/ level = 1 \/ level = 2 \/ level = 3 \/ level = 4 \/ level = 5
               \/ level = 6 \/ level = 7 \/ level = 8 \/ level = 9) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]; vm_compute; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The stream cluster, for every input                                   *)
(* ------------------------------------------------------------------------- *)

Lemma m_arr_get_of_list : forall l i, 0 <= i < zlength l ->
  arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd _ _ _ _ 0).
  unfold arr_inb. rewrite arr_len_make.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (0 + zlength l)); destruct (Z.ltb_spec i (zlength l));
    cbn [andb]; try lia.
  rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma m_slice_of_list : forall l, arr_slice (arr_of_list l) 0 (zlength l) = l.
Proof.
  intros l. apply nth_ext with (d := 0) (d' := 0).
  - unfold arr_slice. rewrite arr_slice_nat_length. unfold zlength. lia.
  - intros k Hk. unfold arr_slice in *. rewrite arr_slice_nat_length in Hk.
    rewrite arr_slice_nat_nth by exact Hk. rewrite Z.add_0_l.
    rewrite m_arr_get_of_list by (unfold zlength in *; lia). f_equal. lia.
Qed.

Lemma m_entry_strm : forall level data,
  0 <= level <= 9 -> Forall (fun b => 0 <= b < 256) data ->
  m_core_ok level = true ->
  strm_rel (IProbe.s5_entry level data) (rt_call level data) [] [].
Proof.
  intros level data Hl Hb Hok.
  unfold m_core_ok in Hok. cbv zeta in Hok. relb_split Hok. relb_atoms.
  unfold strm_rel, IProbe.s5_entry, rt_call. cbv zeta.
  autorewrite with s5f_strm.
  cbn [DS.cstrm_of_call DS.cs_input DS.cs_next_in DS.cs_avail_in DS.cs_out_rev DS.cs_avail_out
       DS.cs_total_in DS.cs_total_out DS.cs_data_type DS.cs_adler
       ZIface.zc_input ZIface.zc_avail_out ZIface.zc_strm
       RD.d_strm RD.setD_strm RD.setZ_availout RD.setZ_in
       RD.zs_in RD.zs_done RD.zs_out RD.zs_availout RD.zs_totalin RD.zs_totalout RD.zs_adler RD.zs_datatype].
  assert (Hz0 : 0 <= zlength data) by apply zlength_nonneg.
  split; [lia|]. split; [exact Hz0|]. split; [rewrite arr_len_of_list; lia|].
  split.
  { intros i Hi. rewrite arr_len_of_list in Hi. rewrite m_arr_get_of_list by exact Hi.
    apply (Forall_nth (fun b => 0 <= b < 256) data); [exact Hb | unfold zlength in Hi; lia]. }
  split; [apply m_slice_of_list|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(** The five stream-free clusters read no stream field (abstract states, so
    the conversion never touches a concrete [dsC level]). *)
Lemma m_geom_strm : forall s t cs z, geom_rel s t -> geom_rel (DS.set_strm s cs) (RD.setD_strm z t).
Proof. intros s t cs z H. exact H. Qed.
Lemma m_lz_strm : forall s t cs z, lz_rel s t -> lz_rel (DS.set_strm s cs) (RD.setD_strm z t).
Proof. intros s t cs z H. exact H. Qed.
Lemma m_bw_strm : forall s t cs z, bw_rel s (RT.ts_bw (RD.d_ts t)) ->
  bw_rel (DS.set_strm s cs) (RT.ts_bw (RD.d_ts (RD.setD_strm z t))).
Proof. intros s t cs z H. exact H. Qed.
Lemma m_sym_strm : forall s t cs z, sym_rel s t -> sym_rel (DS.set_strm s cs) (RD.setD_strm z t).
Proof. intros s t cs z H. exact H. Qed.
Lemma m_tree_strm : forall s t cs z, tree_rel s t -> tree_rel (DS.set_strm s cs) (RD.setD_strm z t).
Proof. intros s t cs z H. exact H. Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  D1                                                                    *)
(* ------------------------------------------------------------------------- *)

Theorem m_entry : forall level data,
  0 <= level <= 9 -> Forall (fun b => 0 <= b < 256) data -> zlength data <= 1048573 ->
  exists t, IProbe.rt_entry level data = Some t
         /\ dst_rel (IProbe.s5_entry level data) t [] []
         /\ RD.defl_wf t /\ mt_inv t.
Proof.
  intros level data Hl Hb Hn.
  exists (rt_call level data).
  split; [apply m_rt_entry, Hl|].
  split; [|split; [apply m_rt_call_wf, Hl | apply m_rt_call_inv; assumption]].
  pose proof (m_core_ok_level level Hl) as Hok.
  pose proof (m_entry_strm level data Hl Hb Hok) as Hst.
  unfold m_core_ok in Hok. cbv zeta in Hok. rewrite !andb_true_iff in Hok.
  destruct Hok as ((((((((Hg & Hz) & Hw) & Hs) & Ht) & _) & _) & _) & _).
  apply geom_relb_sound in Hg. apply lz_relb_sound in Hz. apply bw_relb_sound in Hw.
  apply sym_relb_sound in Hs. apply tree_relb_sound in Ht.
  unfold dst_rel. revert Hst. unfold IProbe.s5_entry, rt_call. cbv zeta. intros Hst.
  split; [apply m_geom_strm; exact Hg|]. split; [apply m_lz_strm; exact Hz|].
  split; [apply m_bw_strm; exact Hw|]. split; [apply m_sym_strm; exact Hs|].
  split; [apply m_tree_strm; exact Ht|exact Hst].
Qed.
