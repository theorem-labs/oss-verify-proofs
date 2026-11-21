(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_tr_bt12. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_tr_bt13 Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_pq Z_tr_bt_mid Z_tr_bt1 Z_tr_bt13 Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition UGB_PRE2 : Z := 0x1d1c0.

Definition ugb_pre1_post (L : dlay) (t : tree_id) (T hm dsc mc : Z) (HP : arr)
    (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz (sd_max_length t)) (wz (STP t)) (wz (XP t)) (wz (sd_extra_base t)) a6 a7
                  s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (dl_As L + 5912)) s11 t3 t4 t5 t6)
             F (wz UGB_PRE2) fc None m' (seg_rom usegs)
    /\ munch [(dl_As L + 3008, dl_As L + 5308)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u32arr usegs m' (dl_As L + 3008) (av32 (arr_set HP hm (arr_get HP 1)) 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)].

Lemma ugb_pre1 : forall (L : dlay) (t : tree_id) (T hm dsc mc : Z) (HP : arr) (hh : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells usegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz (hm + 1))] ->
  rw_cells usegs m dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))] -> rw_cells usegs m (SDA t) (sd_cells t) ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L ->
  arr_len HP = 573 -> 0 <= hm <= 570 -> 0 <= arr_get HP 1 < 2^31 -> -1 <= mc < 2^31 -> dsc = dl_As L + bt_desc t ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  evt usegs (ugb_pre1_post L t T hm dsc mc HP ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s4 s5 s6 s7 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) s10 s11 t3 t4 t5 t6)
          F (wz BT_PARTB) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA GC Gdsc Gsd F16 F64 MI LAY LHP Rhm Rh1 Rmc Edsc SEP RSP.
  pose proof (munch_refl [(dl_As L + 3008, dl_As L + 5308)] m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (Bs : dl_As L + 5968 <= 0x10000 \/ 0x5f000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & Bs); exact Bs).
  pose proof (bt_desc_range t) as Rdsc. pose proof (SDA_range t) as RSDA. pose proof (SDA_al8 t) as ASDA. pose proof (STP_range t) as RSTP. pose proof (XP_range t) as RXP.
  assert (RE : 0 <= sd_extra_base t <= 257 /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15)
    by (destruct t; cbn [sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read usegs m _ (av32 HP 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD1.
  unfold BT_PARTB, sd_cells in *.
  zs2. zs2. ustep BT_TRAP.
  zs2. zs2. zstep. ustep BT_TRAP.
  zs2. shl_norm. zs2. ustep BT_TRAP.
  zs2. zs2. zs2. shl_norm. zs2.
  h32_store HPA HP 573 (dl_As L + 3008) hm (arr_get HP 1) ltac:(reflexivity).
  uwalk UGB_PRE2 BT_TRAP.
  apply evt_done. unfold ugb_pre1_post. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA| exact GC].
Qed.


(* [comment removed for export] *)
Lemma av16_fill0 : forall BC, arr_len BC = 16 -> av16 (arr_fill BC 0 16 0) 16 = repeat (wz 0) 16.
Proof.
  intros BC LBC. unfold av16. rewrite uzseq_16. cbn [map]. rewrite !arr_get_fill. unfold arr_inb. rewrite !LBC. cbn. reflexivity.
Qed.
Lemma blc_zero_range : forall BC i, arr_len BC = 16 -> 0 <= i < 16 -> 0 <= arr_get (arr_fill BC 0 16 0) i < 65536.
Proof.
  intros BC i LBC Hi. rewrite arr_get_fill. unfold arr_inb. rewrite LBC.
  replace ((0 <=? i) && (i <? 0 + Z.max 0 16) && ((0 <=? i) && (i <? 16))) with true; [lia|].
  symmetry. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma shl32_shr30 : forall h, 0 <= h < 2^30 -> Z.shiftr (Z.shiftl h 32 mod 18446744073709551616) 30 = 4 * h.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^32) with (4 * 2^30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Definition ugb_pre2_post (L : dlay) (t : tree_id) (T N hm mc : Z) (FC DL BC : arr) (n1 : Z)
    (ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t6 m',
    ms' = MS (ugbR L T (hm + 1) 0 mc (sd_max_length t) (STP t) (XP t) (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 (wz (dl_As L + 5300)) s11 t6)
             F (wz GB1_HEAD) fc None m' (seg_rom usegs)
    /\ munch [(T, T + 4 * N); (dl_As L + 2976, dl_As L + 3008)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC (arr_set DL n1 (wrap16 0)) N))
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 (arr_fill BC 0 16 0) 16)).

Lemma ugb_pre2 : forall (L : dlay) (t : tree_id) (T N hm mc : Z) (FC DL HP7 BC : arr) (n1 : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s4 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP7 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] ->
  rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> T mod 4 = 0 -> arr_len FC = N -> arr_len DL = N -> arr_len HP7 = 573 -> arr_len BC = 16 ->
  0 <= hm <= 570 -> n1 = arr_get HP7 hm -> 0 <= n1 < N -> -1 <= mc < 2^31 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  evt usegs (ugb_pre2_post L t T N hm mc FC DL BC n1 ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz (sd_max_length t)) (wz (STP t)) (wz (XP t)) (wz (sd_extra_base t)) a6 a7
                  s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (dl_As L + 5912)) s11 t3 t4 t5 t6)
          F (wz UGB_PRE2) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA BLC GC F64 MI LAY RT1 RT2 RN AT LFC LDL LHP LBC Rhm En1 Rn1 Rmc SEP RSP.
  pose proof (munch_refl [(T, T + 4 * N); (dl_As L + 2976, dl_As L + 3008)] m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  pose proof (STP_range t) as RSTP. pose proof (XP_range t) as RXP.
  assert (RE : 0 <= sd_extra_base t <= 257 /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15)
    by (destruct t; cbn [sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (av32_zlength HP7 573 ltac:(lia)) as L32. pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  (* [comment removed for export] *)
  change (u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16))) with (u16arr usegs m (dl_As L + 2976) (av16 BC 16)) in BLC.
  apply u16arr_to_cells in BLC. unfold av16 in BLC. rewrite uzseq_16 in BLC. cbn [map c2s] in BLC.
  unfold UGB_PRE2. do 15 (zstep; zstep; gN).
  zs2. zstep. zstep. ustep BT_TRAP.
  zs2. shl_norm. zs2. ustep BT_TRAP. zs2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read usegs mm _ (av32 HP7 573) hm _ (wa (dl_As L + 3008 + 4 * hm)) HPA (av32_nth HP7 573 hm ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDh;
    rewrite <- En1 in RDh end.
  zs2. zs2. shl_norm. zs2.
  do 11 ustep BT_TRAP.
  ct_store_dl ARR FC DL N T n1 (wrap16 0) ltac:(reflexivity).
  zs2. zs2. ustep BT_TRAP. zs2. zstep. br_false.
  zs2. zs2. zs2. zs2. zstep. br_false. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zstep.
  rewrite (zb_lxor_ones T) by lia. rewrite (zb_lxor_ones (dl_As L + 2976)) by lia.
  rewrite (Z.mod_small (hm + 1) 4294967296) by lia. rewrite shl32_shr30 by lia.
  apply evt_done. unfold ugb_pre2_post, ugbR, GB1_HEAD. do 2 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|].
  change (u8arr usegs ?mq ?A (u16s ?ws)) with (u16arr usegs mq A ws). rewrite av16_fill0 by exact LBC.
  apply u16arr_of_cells. cbn [repeat c2s]. exact BLC.
Qed.


(* [comment removed for export] *)
Definition gb_tail (t : tree_id) (mc : Z) (R1 : deflate_state * Z) : deflate_state :=
  let (X10, ovf) := R1 in
  if ovf =? 0 then X10
  else gen_bitlen_loop3 (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) t mc (sd_max_length t) HEAP_SIZE.
Lemma gb_tail_0 : forall t mc X, gb_tail t mc (X, 0) = X.
Proof. intros. reflexivity. Qed.
Lemma gb_tail_nz : forall t mc X ovf, ovf <> 0 ->
  gb_tail t mc (X, ovf) = gen_bitlen_loop3 (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X (sd_max_length t) ovf) t mc (sd_max_length t) 573.
Proof. intros t mc X ovf H. unfold gb_tail. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

(* [comment removed for export] *)
Lemma gen_bitlen_flat : forall s t FC DL HP HL hm DP BC OL SL mc,
  gen_bitlen (bt_upd s t FC DL HP HL hm DP BC OL SL mc) t
  = gb_tail t mc (gen_bitlen_loop1 573 (bt_upd s t FC (arr_set DL (arr_get HP hm) (wrap16 0)) HP HL hm DP (arr_fill BC 0 16 0) OL SL mc) t mc
                    (sd_extra_base t) (sd_max_length t) (hm + 1) 0).
Proof.
  intros. unfold gen_bitlen, gb_tail. rewrite bt_max_code, bt_bl_count, bt_set_bl_count, bt_heap_max, bt_heap_get, bt_set_Len, bt_heap_max.
  change (MAX_BITS + 1) with 16.
  destruct (gen_bitlen_loop1 573 _ t mc _ _ (hm + 1) 0) as [X10 ovf]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shl32_shr31 : forall x, 0 <= x < 2^30 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 31 = x * 2.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^32) with (2 * 2^31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma shl32_shr32 : forall x, 0 <= x < 2^30 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.
