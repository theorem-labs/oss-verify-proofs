(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Stdio ZHarness.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import F_fwritex Z_ikit Z_infl_defs Z_infl_defs2 Z_updwin Zlib_iface Zg_infl_pure Z_inflate_mem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocP Require Import RMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arr_get_of_list_nth' : forall l i, 0 <= i -> arr_get (arr_of_list l) i = nth (Z.to_nat i) l 0.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb. rewrite arr_len_make, arr_get_make. rewrite Z.sub_0_r.
  destruct (Z.ltb_spec i (0 + zlength l)).
  - destruct (Z.leb_spec 0 i); [|lia]. destruct (Z.ltb_spec i (zlength l)); [|lia]. reflexivity.
  - cbn [andb]. rewrite Bool.andb_false_r. symmetry. apply nth_overflow. unfold zlength in *. lia.
Qed.

Lemma av8_of_list : forall l, av8 (arr_of_list l) (zlength l) = to_bytes l.
Proof.
  intros l. apply list_ext_nth.
  - rewrite av8_length. unfold to_bytes, zlength. rewrite length_map. lia.
  - intros k Hk. rewrite av8_length in Hk. unfold to_bytes.
    replace k with (Z.to_nat (Z.of_nat k)) by lia. rewrite (av8_nth _ (zlength l) (Z.of_nat k)) by (unfold zlength in *; lia).
    rewrite Nat2Z.id. rewrite arr_get_of_list_nth' by lia. rewrite Nat2Z.id.
    rewrite nth_error_map. destruct (nth_error l k) as [v|] eqn:E.
    + cbn [option_map]. f_equal. f_equal. exact (nth_error_nth l k 0 E).
    + exfalso. apply nth_error_None in E. unfold zlength in Hk. lia.
Qed.

Lemma iin_of_comprG : forall m C (comprc : list Z) ti ain,
  u8arr psegs m C (to_bytes comprc) -> Forall (fun c => 0 <= c < 256) comprc -> 0 <= ti -> 0 <= ain -> ti + ain <= zlength comprc ->
  u8ro psegs m (C + ti) (av8 (arr_of_list (zfirstn ain (zskipn ti comprc))) (arr_len (arr_of_list (zfirstn ain (zskipn ti comprc)))))
  /\ zlength (zfirstn ain (zskipn ti comprc)) = ain.
Proof.
  intros m C comprc ti ain H HB Hti Hain Hle. unfold zlength in Hle.
  assert (LEN : zlength (zfirstn ain (zskipn ti comprc)) = ain).
  { unfold zlength, zfirstn, zskipn. rewrite length_firstn, length_skipn. lia. }
  split; [|exact LEN].
  pose proof (u8arr_sub_bytes m C _ (Z.to_nat ti) (Z.to_nat ain) H ltac:(unfold to_bytes; rewrite length_map; lia)) as HB'.
  replace (Z.of_nat (Z.to_nat ti)) with ti in HB' by lia.
  rewrite arr_len_of_list. rewrite av8_of_list.
  unfold u8ro, to_bytes, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map. exact HB'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma uncompr_splitG : forall m U (uc : list Z) no aout,
  u8arr psegs m U (to_bytes uc) -> 0 <= no -> 0 <= aout -> no + aout <= zlength uc ->
  let bs := to_bytes uc in
  let rest0 := firstn (Z.to_nat aout) (skipn (Z.to_nat no) bs) in
  length rest0 = Z.to_nat aout
  /\ u8arr psegs m U (firstn (Z.to_nat no) bs)
  /\ u8arr psegs m (U + no) rest0
  /\ u8arr psegs m (U + no + aout) (skipn (Z.to_nat no + Z.to_nat aout) bs).
Proof.
  intros m U uc no aout H Hno Hao Hle. cbv zeta. unfold zlength in Hle.
  assert (LB : length (to_bytes uc) = length uc) by (unfold to_bytes; apply length_map).
  destruct (u8arr_split3 m U _ (Z.to_nat no) (Z.to_nat aout) H ltac:(lia)) as (H1 & H2 & H3).
  replace (Z.of_nat (Z.to_nat no)) with no in H2, H3 by lia. replace (Z.of_nat (Z.to_nat aout)) with aout in H3 by lia.
  split; [rewrite length_firstn, length_skipn; lia|]. split; [exact H1|]. split; [|exact H3].
  apply (u8arr_of_rw_cells psegs m _ (Z.to_nat aout)). exact H2.
Qed.

Lemma upd_nat_app' : forall (pre post : list Z) x b, upd_nat (pre ++ x :: post) (length pre) b = pre ++ b :: post.
Proof. induction pre as [|a pre IH]; intros post x b; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma zstore_split' : forall (bs pre post : list Z), (length bs <= length post)%nat ->
  zstore (pre ++ post) (Z.of_nat (length pre)) bs = pre ++ bs ++ skipn (length bs) post.
Proof.
  induction bs as [|b bs IH]; intros pre post HL; cbn; [reflexivity|].
  destruct post as [|x post]; [cbn in HL; lia|]. cbn in HL.
  unfold zupd. replace (Z.of_nat (length pre) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Nat2Z.id, upd_nat_app'.
  replace (pre ++ b :: post) with ((pre ++ [b]) ++ post) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length (pre ++ [b]))) by (rewrite length_app; cbn; lia).
  rewrite IH by lia. rewrite <- app_assoc. reflexivity.
Qed.
Lemma zstore_at' : forall out o bs, 0 <= o -> (Z.to_nat o + length bs <= length out)%nat ->
  zstore out o bs = firstn (Z.to_nat o) out ++ bs ++ skipn (length bs) (skipn (Z.to_nat o) out).
Proof.
  intros out o bs Ho HL.
  pose proof (zstore_split' bs (firstn (Z.to_nat o) out) (skipn (Z.to_nat o) out) ltac:(rewrite length_skipn; lia)) as E.
  rewrite firstn_skipn, length_firstn, Nat.min_l, Z2Nat.id in E by lia. exact E.
Qed.

#[local] Transparent iout_bytes.
(* [comment removed for export] *)
Lemma uncompr_joinG : forall m U (uc : list Z) no aout c put,
  0 <= no -> 0 <= put <= aout -> no + aout <= zlength uc -> put <= arr_len (ic_outbuf c) ->
  let bs := to_bytes uc in
  let rest0 := firstn (Z.to_nat aout) (skipn (Z.to_nat no) bs) in
  u8arr psegs m U (firstn (Z.to_nat no) bs) ->
  u8arr psegs m (U + no) (iout_bytes rest0 c put) ->
  u8arr psegs m (U + no + aout) (skipn (Z.to_nat no + Z.to_nat aout) bs) ->
  u8arr psegs m U (to_bytes (zstore uc no (arr_slice (ic_outbuf c) 0 put))).
Proof.
  intros m U uc no aout c put Hno Hput Hle Hob. cbv zeta. intros H1 H2 H3. unfold zlength in Hle.
  assert (LB : length (to_bytes uc) = length uc) by (unfold to_bytes; apply length_map).
  assert (L1 : length (firstn (Z.to_nat no) (to_bytes uc)) = Z.to_nat no) by (rewrite length_firstn; lia).
  assert (LR : length (firstn (Z.to_nat aout) (skipn (Z.to_nat no) (to_bytes uc))) = Z.to_nat aout) by (rewrite length_firstn, length_skipn; lia).
  assert (LSL : length (arr_slice (ic_outbuf c) 0 put) = Z.to_nat put) by (unfold arr_slice; apply arr_slice_nat_length).
  pose proof (iout_bytes_length _ c put ltac:(rewrite LR; lia)) as LO. rewrite LR in LO.
  apply rw_cells_of_u8arr in H2. rewrite LO in H2.
  pose proof (u8arr_join3k m U _ _ _ (Z.to_nat no) (Z.to_nat aout) L1 H1 ltac:(replace (Z.of_nat (Z.to_nat no)) with no by lia; exact H2)
                ltac:(replace (Z.of_nat (Z.to_nat no)) with no by lia; replace (Z.of_nat (Z.to_nat aout)) with aout by lia; exact H3)) as HJ.
  rewrite zstore_at' by (rewrite ?LSL; lia).
  unfold to_bytes at 1. rewrite !map_app, <- firstn_map, <- !skipn_map. fold (to_bytes uc). rewrite LSL.
  match type of HJ with u8arr _ _ _ ?l => replace (firstn (Z.to_nat no) (to_bytes uc) ++ map (Z_to_bv 8) (arr_slice (ic_outbuf c) 0 put) ++ skipn (Z.to_nat put) (skipn (Z.to_nat no) (to_bytes uc))) with l; [exact HJ|] end.
  f_equal. unfold iout_bytes. rewrite <- app_assoc. f_equal.
  - rewrite <- (av8_sub (ic_outbuf c) put 0 put) by lia. change (Z.to_nat 0) with 0%nat. cbn [skipn]. rewrite firstn_all2 by (rewrite av8_length; lia). reflexivity.
  - rewrite <- (firstn_skipn (Z.to_nat aout) (skipn (Z.to_nat no) (to_bytes uc))) at 2.
    rewrite skipn_app. rewrite length_firstn, length_skipn.
    replace (Z.to_nat put - Nat.min (Z.to_nat aout) (length (to_bytes uc) - Z.to_nat no))%nat with 0%nat by lia. rewrite skipn_O.
    rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.
