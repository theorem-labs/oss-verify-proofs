(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le2_bytes : forall v : word, le2 v = [Z_to_bv 8 (bv_unsigned v); Z_to_bv 8 (Z.shiftr (bv_unsigned v) 8)].
Proof. intros. reflexivity. Qed.

Lemma rw_cells_read_c2_b0 : forall m A cs k v a,
  rw_cells psegs m A cs -> cell_at cs k = Some (C2 v) -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes psegs m a 1 = Some [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros m A cs k v a [[Hwf Hb] _] Hc ->.
  destruct (cell_at_split _ _ _ (C2 v) Hc) as (pre & post & E & Hsz & _). subst cs.
  apply cells_wf_app in Hwf. destruct Hwf as [Wpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  rewrite (bytes_at_ov_read psegs m A _ k 1 Hb).
  2:{ rewrite !length_app, length_le2, (cells_bytes_length pre Wpre). lia. }
  rewrite skipn_app, skipn_all2 by (rewrite (cells_bytes_length pre Wpre); lia).
  rewrite (cells_bytes_length pre Wpre), Hsz, Nat.sub_diag. cbn [app]. rewrite skipn_O.
  rewrite le2_bytes. reflexivity.
Qed.

Lemma rw_cells_read_c2_b1 : forall m A cs k v a,
  rw_cells psegs m A cs -> cell_at cs k = Some (C2 v) -> a = wa (A + Z.of_nat k + 1) ->
  ov_read_bytes psegs m a 1 = Some [Z_to_bv 8 (Z.shiftr (bv_unsigned v) 8)].
Proof.
  intros m A cs k v a [[Hwf Hb] _] Hc ->.
  destruct (cell_at_split _ _ _ (C2 v) Hc) as (pre & post & E & Hsz & _). subst cs.
  apply cells_wf_app in Hwf. destruct Hwf as [Wpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  replace (A + Z.of_nat k + 1) with (A + Z.of_nat (k + 1)) by lia.
  rewrite (bytes_at_ov_read psegs m A _ (k + 1) 1 Hb).
  2:{ rewrite !length_app, length_le2, (cells_bytes_length pre Wpre). lia. }
  rewrite skipn_app, skipn_all2 by (rewrite (cells_bytes_length pre Wpre); lia).
  rewrite (cells_bytes_length pre Wpre), Hsz. replace (k + 1 - k)%nat with 1%nat by lia. cbn [app].
  rewrite le2_bytes. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac rd_c2 H kn b :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn) in
      lazymatch c with
      | Some (C2 ?v) =>
          let k := eval vm_compute in (Z.of_nat kn) in
          let RD := fresh "RD" in
          lazymatch b with
          | 0 => pose proof (rw_cells_read_c2_b0 m A cs kn v (wa (A + k)) H ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as RD
          | 1 => pose proof (rw_cells_read_c2_b1 m A cs kn v (wa (A + k + 1)) H ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as RD
          end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z8_eqm : forall x y, x mod 2^8 = y mod 2^8 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. exact H.
Qed.

Lemma le1_Z8 : forall (w : word) v, bv_unsigned w mod 2^8 = v mod 2^8 -> le1 w = [Z_to_bv 8 v].
Proof. intros w v H. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z8_eqm. exact H. Qed.

Lemma av8_write_le1 : forall m A a n i (w : word) v,
  u8arr psegs m A (av8 a n) -> 0 <= i < n -> n <= arr_len a -> bv_unsigned w mod 2^8 = v mod 2^8 ->
  u8arr psegs (write_to_mem m (wa (A + i)) (le1 w)) A (av8 (arr_set a i v) n).
Proof.
  intros m A a n i w v ARR Hi Hn E. rewrite (le1_Z8 w v E). apply (av8_write m A a n i _ v ARR Hi Hn eq_refl).
Qed.

Lemma shr8_small : forall X, 0 <= X < 2^16 -> 0 <= Z.shiftr X 8 < 256.
Proof. intros X HX. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with (256 * 2^8) in HX. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. Qed.

(* [comment removed for export] *)
Lemma b0_val : forall X, 0 <= X < 2^16 -> bv_unsigned (wz (bv_unsigned (Z_to_bv 8 X))) mod 2^8 = X mod 2^8.
Proof.
  intros X HX.
  assert (E : bv_unsigned (Z_to_bv 8 X) = X mod 2^8) by (rewrite Z_to_bv_unsigned; reflexivity).
  rewrite E. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound X (2^8) ltac:(lia)); lia). apply Z.mod_mod. lia.
Qed.

Lemma b0_val_w : forall X, 0 <= X < 2^16 -> bv_unsigned (wz (bv_unsigned (Z_to_bv 8 X))) mod 2^8 = wrap8 X mod 2^8.
Proof. intros X HX. rewrite b0_val, wrap8_mod, Z.mod_mod by lia. reflexivity. Qed.
Lemma b0_val_land : forall X, 0 <= X < 2^16 -> bv_unsigned (wz (bv_unsigned (Z_to_bv 8 X))) mod 2^8 = wrap8 (Z.land X 255) mod 2^8.
Proof.
  intros X HX. rewrite b0_val, !wrap8_mod by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma b1_val : forall X, 0 <= X < 2^16 ->
  bv_unsigned (wz (bv_unsigned (Z_to_bv 8 (Z.shiftr X 8)))) mod 2^8 = wrap8 (Z.shiftr (wrap16 X) 8) mod 2^8.
Proof.
  intros X HX. pose proof (shr8_small X HX) as R.
  assert (E : bv_unsigned (Z_to_bv 8 (Z.shiftr X 8)) = Z.shiftr X 8) by (apply Z_to_bv_small; unfold bv_modulus; cbn; lia).
  rewrite E, unsigned_lit by lia. rewrite wrap16_mod, (Z.mod_small X) by lia. rewrite wrap8_mod, Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac pb_store ARR a n A idx v RNG :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok psegs _ A (av8 a n) idx (wa (A + idx)) ARR ltac:(lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av8_write_le1 m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(RNG)) as ARR';
      replace (A + idx) with E in ARR' by lia;
      let LN := fresh "LPB" in pose proof (av8_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNP" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

(* [comment removed for export] *)
Ltac ct_store_fc ARR fc dl n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (avct fc dl n) (2 * idx) (wa (A + 2 * (2 * idx))) ARR ltac:(rewrite avct_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (avct_write_fc m0 A fc dl n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * (2 * idx)) with E in ARR' by lia;
      let LN := fresh "LCT" in pose proof (avct_zlength (arr_set fc idx v) dl n ltac:(lia)) as LN;
      let LA := fresh "LNA" in pose proof (arr_len_set fc idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.
Ltac ct_store_dl ARR fc dl n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (avct fc dl n) (2 * idx + 1) (wa (A + 2 * (2 * idx + 1))) ARR ltac:(rewrite avct_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (avct_write_dl m0 A fc dl n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * (2 * idx + 1)) with E in ARR' by lia;
      let LN := fresh "LCT" in pose proof (avct_zlength fc (arr_set dl idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNA" in pose proof (arr_len_set dl idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

(* [comment removed for export] *)
Ltac close_lens_with LENS U :=
  let l1 := fresh in let l2 := fresh in let l3 := fresh in let l4 := fresh in let l5 := fresh in let l6 := fresh in let l7 := fresh in
  let l8 := fresh in let l9 := fresh in let l10 := fresh in let l11 := fresh in let l12 := fresh in let l13 := fresh in
  destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
  constructor; U; dsred; rewrite ?arr_len_blit, ?arr_len_set, ?arr_len_fill; assumption.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint c2s (ws : list word) : list cell := match ws with [] => [] | w :: r => C2 w :: c2s r end.

Lemma c2s_wf : forall ws, cells_wf (c2s ws).
Proof. induction ws as [|w r IH]; cbn [c2s cells_wf cell_wf]; [exact I| split; [exact I| exact IH]]. Qed.
Lemma c2s_bytes : forall ws, cells_bytes (c2s ws) = u16s ws.
Proof. induction ws as [|w r IH]; cbn [c2s cells_bytes cbytes u16s]; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma c2s_size : forall ws, cells_size (c2s ws) = (2 * length ws)%nat.
Proof. induction ws as [|w r IH]; cbn [c2s cells_size csize length]; [reflexivity| rewrite IH; lia]. Qed.

Lemma u16arr_to_cells : forall m A ws, u16arr psegs m A ws -> rw_cells psegs m A (c2s ws).
Proof.
  intros m A ws [Hb Hw]. split; [split|].
  - apply c2s_wf.
  - rewrite c2s_bytes. exact Hb.
  - rewrite c2s_size, <- u16s_length. exact Hw.
Qed.
Lemma u16arr_of_cells : forall m A ws, rw_cells psegs m A (c2s ws) -> u16arr psegs m A ws.
Proof.
  intros m A ws [[_ Hb] Hw]. rewrite c2s_bytes in Hb. rewrite c2s_size, <- u16s_length in Hw. split; assumption.
Qed.

(* [comment removed for export] *)
Definition ctw_z (fc dl : arr) (n : Z) (k : Z) : word := if Z.even k && (k / 2 <? n) then wz 0 else ctw fc dl k.

Lemma avct_fill : forall fc dl N n, 0 <= n <= N -> N <= arr_len fc ->
  avct (arr_fill fc 0 n 0) dl N = map (ctw_z fc dl n) (zseq (2 * N)).
Proof.
  intros fc dl N n Hn HN. unfold avct. apply list_ext_nth.
  - rewrite !length_map. reflexivity.
  - intros k Hk. rewrite length_map, zseq_length in Hk.
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    rewrite !map_zseq_nth by lia. f_equal. unfold ctw_z, ctw.
    destruct (even_div2_cases (Z.of_nat k) ltac:(lia)) as [[E D]|[E D]]; rewrite E; cbn [andb]; [|reflexivity].
    rewrite arr_get_fill. unfold arr_inb.
    destruct (Z.ltb_spec (Z.of_nat k / 2) n) as [C|C].
    + replace ((0 <=? Z.of_nat k / 2) && (Z.of_nat k / 2 <? 0 + Z.max 0 n) && ((0 <=? Z.of_nat k / 2) && (Z.of_nat k / 2 <? arr_len fc))) with true; [reflexivity|].
      symmetry. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
    + replace ((0 <=? Z.of_nat k / 2) && (Z.of_nat k / 2 <? 0 + Z.max 0 n) && ((0 <=? Z.of_nat k / 2) && (Z.of_nat k / 2 <? arr_len fc))) with false; [reflexivity|].
      symmetry. rewrite !andb_false_iff, !Z.leb_gt, !Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma zseq_122 : ltac:(let v := eval vm_compute in (zseq 122) in exact (zseq 122 = v)).
Proof. vm_compute. reflexivity. Qed.
Lemma zseq_78 : ltac:(let v := eval vm_compute in (zseq 78) in exact (zseq 78 = v)).
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma arr_fill_unfold : forall {X} (a : parr X) ofs n v, arr_fill_nat a ofs (Z.to_nat n) v = arr_fill a ofs n v.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac mv_group LEM H MUx WMx :=
  lazymatch type of MUx with
  | munch ?W ?ma ?mb => apply (LEM ma mb _ _ W) in H; [ | exact MUx | exact WMx | cbn [disjoint_from]; slia ]
  end.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac br_norm := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?signed_wz, ?unsigned_lit by lia.
Ltac br_solve := br_norm; solve_cond_rec.
Ltac br_true :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| symmetry; br_solve]
  end.
Ltac br_false :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| symmetry; br_solve]
  end.
Ltac bool2prop K :=
  repeat first [ rewrite Bool.negb_true_iff in K | rewrite Bool.negb_false_iff in K ];
  first [ apply Z.ltb_lt in K | apply Z.ltb_ge in K | apply Z.leb_le in K | apply Z.leb_gt in K | apply Z.eqb_eq in K | apply Z.eqb_neq in K ].
Ltac br_cases K :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      destruct c eqn:K; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in K; rewrite ?signed_wz, ?unsigned_lit in K by lia; bool2prop K
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma av8_blit : forall dst src N dofs sofs n, 0 <= dofs -> 0 <= n -> dofs + n <= N -> N <= arr_len dst ->
  av8 (arr_blit dst dofs src sofs n) N
  = firstn (Z.to_nat dofs) (av8 dst N) ++ map (Z_to_bv 8) (arr_slice src sofs n) ++ skipn (Z.to_nat (dofs + n)) (av8 dst N).
Proof.
  intros dst src N dofs sofs n Hd Hn HN HL. apply list_ext_nth.
  - rewrite !length_app, length_firstn, length_skipn, length_map, !av8_length, arr_slice_length'. lia.
  - intros k Hk. rewrite av8_length in Hk.
    replace k with (Z.to_nat (Z.of_nat k)) at 1 by lia. rewrite av8_nth by lia.
    rewrite arr_get_blit. unfold arr_inb.
    destruct (Z_lt_le_dec (Z.of_nat k) dofs) as [C1|C1].
    + replace ((dofs <=? Z.of_nat k) && (Z.of_nat k <? dofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len dst))) with false
        by (symmetry; rewrite !andb_false_iff, !Z.leb_gt; lia).
      rewrite nth_error_app1 by (rewrite length_firstn, av8_length; lia).
      rewrite nth_error_firstn. destruct (Nat.ltb_spec k (Z.to_nat dofs)); [|lia].
      replace k with (Z.to_nat (Z.of_nat k)) at 2 by lia. rewrite av8_nth by lia. reflexivity.
    + rewrite nth_error_app2 by (rewrite length_firstn, av8_length; lia).
      rewrite length_firstn, av8_length. replace (Init.Nat.min (Z.to_nat dofs) (Z.to_nat N)) with (Z.to_nat dofs) by lia.
      destruct (Z_lt_le_dec (Z.of_nat k) (dofs + n)) as [C2|C2].
      * replace ((dofs <=? Z.of_nat k) && (Z.of_nat k <? dofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len dst))) with true
          by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
        rewrite nth_error_app1 by (rewrite length_map, arr_slice_length'; lia).
        rewrite nth_error_map. unfold arr_slice. rewrite arr_slice_nat_nth_error by lia. cbn [option_map].
        do 3 f_equal. lia.
      * replace ((dofs <=? Z.of_nat k) && (Z.of_nat k <? dofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len dst))) with false
          by (symmetry; rewrite !andb_false_iff, !Z.leb_gt, !Z.ltb_ge; lia).
        rewrite nth_error_app2 by (rewrite length_map, arr_slice_length'; lia).
        rewrite length_map, arr_slice_length'. rewrite nth_error_skipn.
        replace (Z.to_nat (dofs + n) + (k - Z.to_nat dofs - Z.to_nat n))%nat with (Z.to_nat (Z.of_nat k)) by lia.
        rewrite av8_nth by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma av8_blit' : forall dst src N dofs sofs n, 0 <= dofs -> 0 <= n -> dofs + n <= N -> N <= arr_len dst ->
  firstn (Z.to_nat dofs) (av8 dst N) ++ map (Z_to_bv 8) (arr_slice src sofs n) ++ skipn (Z.to_nat dofs + Z.to_nat n) (av8 dst N)
  = av8 (arr_blit dst dofs src sofs n) N.
Proof. intros. rewrite av8_blit by assumption. rewrite Z2Nat.inj_add by lia. reflexivity. Qed.

Lemma u8arr_join3z : forall m A (b1 b2 b3 : list byte) (k n : Z), 0 <= k -> 0 <= n -> length b1 = Z.to_nat k ->
  u8arr psegs m A b1 -> rw_cells psegs m (A + k) [CB (Z.to_nat n) b2] -> u8arr psegs m (A + k + n) b3 ->
  u8arr psegs m A (b1 ++ b2 ++ b3).
Proof.
  intros m A b1 b2 b3 k n Hk Hn L1 H1 H2 H3. apply (u8arr_join3k m A b1 b2 b3 (Z.to_nat k) (Z.to_nat n) L1 H1).
  - rewrite Z2Nat.id by lia. exact H2.
  - rewrite !Z2Nat.id by lia. exact H3.
Qed.

(* [comment removed for export] *)
Ltac shl_norm :=
  rewrite ?Z.shiftl_mul_pow2 by lia;
  change (2 ^ 1) with 2; change (2 ^ 2) with 4; change (2 ^ 3) with 8.

(* [comment removed for export] *)
Ltac strip32 :=
  repeat match goal with
  | |- context [bv_swrap 32 ?z] => rewrite (Z_dkit.bv_swrap32_id z) by lia
  | |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (Z_dkit.sx32_wz v) by lia
  | |- context [zx32 (Z_to_bv 64 ?v)] => rewrite (Z_dkit.zx32_wz v) by lia
  end.
Ltac zs2 := zstep; strip32.
(* [comment removed for export] *)
Ltac zsb := zstep; cbv beta.

(* [comment removed for export] *)
Ltac reg_as e e' := replace (Z_to_bv 64 e) with (Z_to_bv 64 e') in * by (f_equal; lia).

(* [comment removed for export] *)
Lemma bv_eqb_wz : forall a b, - 2^63 <= a < 2^63 -> - 2^63 <= b < 2^63 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. destruct (Z.eqb_spec a b) as [->|NE]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply NE. apply bv_eq in E. rewrite <- (Z_dkit.signed_wz a Ha), <- (Z_dkit.signed_wz b Hb), E. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac br_cases_s K :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      destruct c eqn:K; rewrite ?bv_eqb_wz in K by lia; bool2prop K
  end.
