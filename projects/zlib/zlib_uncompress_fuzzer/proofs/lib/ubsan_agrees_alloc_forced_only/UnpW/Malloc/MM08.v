(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MallocKit_A3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A. Import MM11. Import MM11.MallocKit_AB. Import MM14. Import MM14.MallocKit_A2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma bounces_set st i v j :
  bounces (set_bounce i v st) j = if Z.eqb j i then v else bounces st j.
Proof.
  unfold bounces, set_bounce, upd_ctx. cbn [ctx s_ctx c_bounces set_bounces_map].
  destruct (Z.eqb_spec j i); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bouncess_set st i v : 0 <= i < 32 ->
  bouncess (set_bounce i v st) = upd (bouncess st) (Z.to_nat i) (b8 v).
Proof.
  intros Hi. unfold bouncess.
  replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
  apply (map_seq_upd (fun j => b8 (bounces st (Z.of_nat j)))); [|lia].
  intros j Hj. rewrite bounces_set.
  destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.

(* [comment removed for export] *)
Lemma addiw_small v c : 0 <= v < 2^31 -> -2^31 <= v + c < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + c)) = Z_to_bv 64 ((v + c) mod 2^64).
Proof.
  intros Hv Hc. rewrite unsigned_lit by lia. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (v + c))). f_equal.
  rewrite swrap32_eq'.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
  Z.div_mod_to_equations. lia.
Qed.

End CANSEC1.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma set_group_ai_eq st b gh ai :
  get_group st b = Some gh -> set_group_active_idx b ai st = put_group b (g_meta gh) ai (del_group b st).
Proof.
  intros Hb. unfold set_group_active_idx, put_group, del_group. rewrite Hb. cbn [s_groups set_groups].
  rewrite insert_delete_eq. reflexivity.
Qed.

Lemma put_group_del st b mo ai : put_group b mo ai (del_group b st) = put_group b mo ai st.
Proof. unfold put_group, del_group. cbn [s_groups set_groups]. rewrite insert_delete_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. intros MW. rewrite <- (meta_word_last_idx mr MW). change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma sxv_inj a b : 0 <= a < 2^32 -> 0 <= b < 2^32 -> sxv a = sxv b -> a = b.
Proof.
  intros Ha Hb E. pose proof (sxv_mod32 a) as Ea. pose proof (sxv_mod32 b) as Eb. rewrite E in Ea. rewrite Ea in Eb.
  rewrite !Z.mod_small in Eb by lia. exact Eb.
Qed.

Lemma mask_upto_range k : 0 <= k <= 31 -> 0 < mask_upto k < 2^32.
Proof.
  intros Hk. unfold mask_upto. split.
  - assert (2 ^ 1 <= 2 ^ (k + 1)) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in H. lia.
  - assert (2 ^ (k + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.


Lemma land_mask_31 x : 0 <= x -> x mod 32 = Z.land x 31.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lxor_range31 a b : 0 <= a < 2^31 -> 0 <= b < 2^31 -> 0 <= Z.lxor a b < 2^31.
Proof.
  intros Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
  assert (Ha' : Z.log2 a < 31) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  assert (Hb' : Z.log2 b < 31) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia| apply Z.log2_lt_pow2; lia]).
  apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|]. apply Z.max_lub_lt; assumption.
Qed.


Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
  intros MW. pose proof (meta_word_sc mr MW) as E. pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range mr MW) as WR.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. replace (Z.testbit 126 0) with false by reflexivity. apply Bool.andb_false_r.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_even_succ by lia.
    rewrite <- E. rewrite Z.land_spec, Z.shiftr_spec by lia.
    change 126 with (2 * 63). rewrite Z.testbit_even_succ by lia.
    replace (Z.succ (n - 1) + 5) with (n - 1 + 6) by lia. reflexivity.
Qed.

Lemma span_loop_bounds F : forall cnt span size, cnt <= span_loop F cnt span size <= cnt + Z.of_nat F.
Proof.
  induction F as [|F IH]; intros; cbn [span_loop]; [lia|].
  rewrite Nat2Z.inj_succ. destruct (_ <? _); [|lia]. pose proof (IH (cnt + 1) (span + size) size). lia.
Qed.

(* [comment removed for export] *)
Lemma ai_byte_land w v : 0 <= w -> 0 <= v ->
  Z.land ((Z.lor (Z.land w (2^64 - 32)) (Z.land v 31)) mod 256) 31 = Z.land v 31.
Proof.
  intros Hw Hv. apply Z.bits_inj'. intros n Hn.
  change 256 with (2^8). change 31 with (Z.ones 5).
  rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
  replace (2^64 - 32) with (Z.shiftl (2^59 - 1) 5) by reflexivity.
  destruct (Z.ltb_spec n 5).
  - rewrite Z.shiftl_spec_low by lia. replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia).
    replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia). rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_l. reflexivity.
  - replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le1_mod z : le1 (Z_to_bv 64 z) = [b8 (z mod 256)].
Proof.
  unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.

Lemma land31_range x : 0 <= Z.land x 31 <= 31.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 31 n); reflexivity.
Qed.

Lemma swrap32_small z : - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros. rewrite swrap32_eq'.
  change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sraiw1_small v : 0 <= v < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (wz v))) 1)) = wz (Z.shiftr v 1).
Proof.
  intros Hv. rewrite wz_unsigned by lia. rewrite (swrap32_small v) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  rewrite swrap32_small by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma land1_mod2 a : Z.land a 1 = a mod 2.
Proof. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma even_of_land1 a : Z.even a = (Z.land a 1 =? 0).
Proof.
  rewrite land1_mod2, Zeven.Zeven_odd_bool, Zmod_odd. destruct (Z.odd a); reflexivity.
Qed.

End CANSEC2.
End MallocKit_A3.

Module ASlot_W10.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2.
Import MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ag_frame (sc : Z) (j : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (Z_to_bv 64 (sc * 2)); CB 40 j; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section AG1.
Variables (sc lo : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : ATOP <= lo.
End AG1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EPI.
Variables (lo : Z).
Hypothesis CLO : ATOP <= lo.
End EPI.


End CANSEC1.
End ASlot_W10.

Module ASlot_W3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2.
Import MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Section CANSEC1. Context {rc : runConstT}.
Lemma meta_word_upd_af mr a f' : meta_word (m_set_avail a (m_set_freed f' mr)) = meta_word mr.
Proof. reflexivity. Qed.

Lemma decay_bounces_eq sc st :
  decay_bounces sc st =
  if ((7 <=? sc) && (sc <? 39)) && negb (bounces st (sc - 7) =? 0) then set_bounce (sc - 7) (bounces st (sc - 7) - 1) st else st.
Proof. reflexivity. Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
End AVZ.


End CANSEC1.
End ASlot_W3.

Module AllocSlot_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp. Import MM12. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AS_STACK (fuel : nat) : Z := 128 + 96 * Z.of_nat fuel.

Lemma AS_STACK_S f : AS_STACK (S f) = AS_STACK f + 96.
Proof. unfold AS_STACK. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma AS_STACK_ge f : 128 <= AS_STACK f.
Proof. unfold AS_STACK. lia. Qed.

End CANSEC1.
End AllocSlot_iface.

Module F_malloc_bigw.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Section CANSEC1. Context {rc : runConstT}.
Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.
End CANSEC1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp.
Import MM14. Import MM14.MallocKit_A2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require StrFun.

Section CANSEC2. Context {rc : runConstT}.
Definition big_ml (n : Z) : Z := Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1).
Definition big_meta (rid : N) (n : Z) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 1 63 (big_ml n).
Definition big_metaA (rid : N) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 0 0 0.
(* [comment removed for export] *)
Definition big_st (st : mstate) (g : aptr) (rid : N) (n v : Z) : mstate :=
  upd_ctx (set_mmap_counter v)
    (put_meta g (big_meta rid n)
      (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st)))).

Lemma big_ml_eq n : 0 <= n < 2^32 -> big_ml n = (n + 4115) / 4096.
Proof.
  intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
  replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma cell_read_hdr_havoc_fresh : forall st b o,
  (s_shadow st) !! (fst b) = None -> snd b mod 16 = 0 -> 0 <= o < 12 ->
  exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
  intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.

Lemma big_word_eq rid n : 0 <= n < 2^32 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (n + 4115))) 12))) 12))) 4064)
  = wz (meta_word (big_meta rid n)).
Proof.
  intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  rewrite (unsigned_lit (n + 4115)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite (unsigned_lit ((n + 4115) / 2 ^ 12)) by (Z.div_mod_to_equations; lia). rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia). change (2 ^ 12) with 4096.
  rewrite (StrFun.lor_add _ _ 12); [| lia| lia| change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia].
  unfold wz. f_equal. lia.
Qed.

Lemma meta_word_big_range rid n : 0 <= n < 2^32 -> 0 <= meta_word (big_meta rid n) < 2^64.
Proof.
  intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ctr_word c : 0 <= c -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv c)) + 1)) = wz (sxv (u32 (c + 1))).
Proof.
  intros Hc. rewrite addw_word. rewrite wz_unsigned by apply sxv_range. f_equal. apply sxv_congr.
  unfold u32. rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le4_sxv v : le4 (wz (sxv v)) = le4 (wz v).
Proof.
  apply le4_congr. rewrite wz_unsigned by apply sxv_range. rewrite sxv_mod32.
  unfold wz. rewrite Z_to_bv_unsigned. change (bv_modulus 64) with (2^64). symmetry. apply MallocRep.mod_mod_pow2. lia.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : ATOP <= lo.
End SUCC.

End CANSEC2.
End F_malloc_bigw.

Module F_malloc_enf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition enf_off0 (o : mem) (st1 : mstate) (b : aptr) (stride idx : Z) : Z :=
  let q := snd b + (16 + stride * idx) in
  if rdv pans_mem o st1 (fst b, q + -3) =? 0 then Z.land (c_mmap_counter (ctx st1)) 255
  else Z.land (rdv pans_mem o st1 (fst b, q + -2) + 256 * rdv pans_mem o st1 (fst b, q + -2 + 1) + 1) 255.

Definition enf_leaf (o : mem) (st1 : mstate) (g b : aptr) (idx n : Z) (st' : mstate) (p : aptr) : Prop :=
  exists off, 0 <= off /\ 16 * off + n + 4 <= get_stride (get_meta_rec st1 g)
    /\ p = (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx + 16 * off)
    /\ st' = havoc p n (fst (enframe_at st1 g idx n off))
    /\ p = snd (enframe_at st1 g idx n off)
    /\ off = fold_off (enf_off0 o st1 b (get_stride (get_meta_rec st1 g)) idx) ((get_stride (get_meta_rec st1 g) - 4 - n) / 16).

Lemma surj_pair_let {A B C'} (e : A * B) (f : A -> B -> C') : (let '(x, y) := e in f x y) = f (fst e) (snd e).
Proof. destruct e; reflexivity. Qed.

End CANSEC1.
End F_malloc_enf.

Module F_malloc_join.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp. Import F_malloc_enf. Import AllocSlot_iface. Import MM12. Import MM12.Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma unk_agree_ext st st' o m :
  unk_agree st o m -> s_regions st' = s_regions st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_groups st' = s_groups st -> unk_agree st' o m.
Proof.
  intros UA ER ES EG rid r off h Hr Hk Ho Hc NG. rewrite ER in Hr. rewrite ES in Hc.
  apply (UA rid r off h Hr Hk Ho Hc). intros (b & gh & Hb & Hf & Hx). apply NG. exists b, gh. rewrite EG. auto.
Qed.

Lemma unk_agree_munch st o m m' W :
  unk_agree st o m -> munch W m m' ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> disjoint_from W (r_base r) (round_up_pg (r_len r))) ->
  (forall rid r, (s_regions st) !! rid = Some r -> 0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= 2^64) ->
  unk_agree st o m'.
Proof.
  intros UA MU HD HB rid r off h Hr Hk Ho Hc NG.
  rewrite <- (UA rid r off h Hr Hk Ho Hc NG). apply MU.
  destruct (HB rid r Hr) as [B0 B1]. rewrite wa_unsigned by lia.
  eapply disjoint_outside; [apply (HD rid r Hr Hk)| lia].
Qed.

(* [comment removed for export] *)
Lemma unk_agree_write st o m a bs :
  unk_agree st o m ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
     a + Z.of_nat (length bs) <= r_base r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (forall rid r, (s_regions st) !! rid = Some r -> 0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= 2^64) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  unk_agree st o (write_to_mem m (wa a) bs).
Proof.
  intros UA HD HB A0 A1 rid r off h Hr Hk Ho Hc NG.
  rewrite <- (UA rid r off h Hr Hk Ho Hc NG). destruct (HB rid r Hr) as [B0 B1].
  rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (HD rid r Hr Hk);
  destruct (Z.leb_spec0 a (r_base r + off)); destruct (Z.ltb_spec0 (r_base r + off) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity; exfalso; lia.
Qed.

Lemma mrel_same st st' :
  s_regions st' = s_regions st -> s_next_rid st' = s_next_rid st -> s_reserved st' = s_reserved st -> mrel st st'.
Proof.
  intros ER EN ES. split; [| rewrite EN; lia | exact ES].
  intros rid r H. exists r. rewrite ER. repeat split; auto. lia.
Qed.

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a668.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.
End FASTCORE.

Lemma malloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> malloc_fp st st2 lo sp1 a -> malloc_fp st st2 lo sp2 a.
Proof.
  intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma malloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> malloc_fp st sta lo sp a -> malloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply malloc_fp_mono; [exact HR| exact H]. Qed.

Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a668.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.
End ASCALL.


End CANSEC1.
End F_malloc_join.

Module F_malloc_small.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp. Import F_malloc_enf. Import AllocSlot_iface. Import MM12. Import MM12.Malloc_iface. Import F_malloc_join.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition coarse_sc (st : mstate) (sc : Z) : Z :=
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.

Lemma malloc_small_ctrl_eq {R} lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail :
  malloc_small_ctrl lay st n k bail =
  let sc := coarse_sc st (size_to_class n) in
  let g := active st sc in
  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>
    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.
Proof. reflexivity. Qed.

Lemma usages_length : forall st, length (usages st) = 48%nat.
Proof. intros. unfold usages. rewrite length_map, length_seq. reflexivity. Qed.
Lemma usages_nth : forall st sc, 0 <= sc < 48 -> nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
  intros st sc Hsc. unfold usages. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat sc <? 48)%nat with true by (symmetry; apply Nat.ltb_lt; lia). cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma lxor_sign_small x : 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros Hx. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 63) as [->|NE].
    - replace (Z.testbit x 63) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - rewrite Z.pow2_bits_false by lia. apply andb_false_r. }
  reflexivity.
Qed.

Lemma land_ones64 y : Z.land y 18446744073709551615 = y mod 2^64.
Proof. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma land_1_even x : (Z.land x 1 = 0) <-> Z.even x = true.
Proof.
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite Z.even_spec. split.
  - intros H. exists (x / 2). lia.
  - intros [k ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
Qed.

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : MFACTS st LB.
End COARSE.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lor1_check : bool :=
  forallb (fun sc => negb ((4 <=? sc) && (sc <? 32) && Z.even sc) || (size_class sc <=? size_class (Z.lor sc 1))) (zseq 0 48).
Lemma lor1_check_true : lor1_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_class_lor1 sc : 4 <= sc < 32 -> Z.even sc = true -> size_class sc <= size_class (Z.lor sc 1).
Proof.
  intros H E. pose proof (forallb_zseq _ 0 48 sc lor1_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  replace (4 <=? sc) with true in X by (symmetry; apply Z.leb_le; lia).
  replace (sc <? 32) with true in X by (symmetry; apply Z.ltb_lt; lia). rewrite E in X. cbn [andb negb orb] in X.
  apply Z.leb_le. exact X.
Qed.

Definition lor1_range_check : bool := forallb (fun sc => (0 <=? Z.lor sc 1) && (Z.lor sc 1 <? 48)) (zseq 0 48).
Lemma lor1_range_check_true : lor1_range_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lor1_range sc : 0 <= sc < 48 -> 0 <= Z.lor sc 1 < 48.
Proof.
  intros H. pose proof (forallb_zseq _ 0 48 sc lor1_range_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.

Lemma coarse_sc_cases st sc : 0 <= sc < 48 ->
  coarse_sc st sc = sc \/ (coarse_sc st sc = Z.lor sc 1 /\ 4 <= sc < 32 /\ Z.even sc = true).
Proof.
  intros H. unfold coarse_sc. destruct (active st sc); [left; reflexivity|].
  destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0)) eqn:E; [|left; reflexivity].
  apply andb_prop in E. destruct E as [E E5]. apply andb_prop in E. destruct E as [E E4].
  apply andb_prop in E. destruct E as [E E3]. apply andb_prop in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  cbv zeta. destruct (_ <=? 12); [right|left]; auto.
Qed.

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis MF : MFACTS st LB.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a668.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 64 - AS_STACK FUEL.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.
End SMALL.


End CANSEC1.
End F_malloc_small.
