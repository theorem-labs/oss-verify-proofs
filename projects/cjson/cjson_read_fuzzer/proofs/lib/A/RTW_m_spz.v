(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_sec_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bandf (P : Prop) : Prop := P.
Lemma bandf_intro : forall P : Prop, P -> bandf P. Proof. intros P H. exact H. Qed.
Lemma bandf_elim : forall P : Prop, bandf P -> P. Proof. intros P H. exact H. Qed.

Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma A_SECONDARY_val : A_SECONDARY = 0xa6c58. Proof. reflexivity. Qed.
Lemma A_GSTATS_val : A_GSTATS = 0xa6ec8. Proof. reflexivity. Qed.
Definition A_SEC_MUTEX : Z := A_SECONDARY + 616.
Lemma A_SEC_MUTEX_val : A_SEC_MUTEX = 0xa6ec0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Z_to_bv8_eq_mod : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256. exact H. Qed.
Lemma Z_to_bv8_of_unsigned : forall (b : byte) x, x mod 256 = bv_unsigned b -> Z_to_bv 8 x = b.
Proof. intros b x H. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b). apply Z_to_bv8_eq_mod. rewrite H. symmetry. apply Z.mod_small. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. cbn in *. lia. Qed.
Lemma le4_256k : forall (b1 b2 b3 : byte) (lo : Z), 0 <= lo < 256 ->
  let k := bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3 in
  le4 (wz (256 * k + lo)) = [zb lo; b1; b2; b3].
Proof.
  intros b1 b2 b3 lo Hlo k.
  pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R1, R2, R3. cbn in R1, R2, R3.
  unfold le4, wz, zb. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  f_equal; [apply Z_to_bv8_eq_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_of_unsigned; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_of_unsigned; Z.div_mod_to_equations; lia|].
  f_equal; apply Z_to_bv8_of_unsigned; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma mutex_cells_of : forall m A j,
  rw_cells asegs m A [W1 0; CB 7 j] ->
  exists k j4 b1 b2 b3, 0 <= k < 2^24 /\ le4 (wz (256 * k)) = [zb 0; b1; b2; b3] /\ le4 (wz (256 * k + 1)) = [zb 1; b1; b2; b3]
    /\ rw_cells asegs m A [C4 (wz (256 * k))] /\ rw_cells asegs m (A + 4) [CB 4 j4].
Proof.
  intros m A j H.
  apply (rw_cells_split_CB _ _ _ [W1 0] _ _ _ [3; 4]%nat) in H; [| cbn; destruct H as [[W _] _]; cbn in W; lia].
  cbn [mk_CB_cells app] in H.
  pose proof (proj1 (rw_cells_app asegs m A [W1 0; CB 3 (firstn 3 j)] [CB 4 (firstn 4 (skipn 3 j))]) H) as [H1 H2].
  cbn [cells_size Cells.csize Nat.add] in H2.
  destruct H1 as [[W B] WR]. cbn in W. destruct W as [_ [L3 _]].
  destruct (firstn 3 j) as [|b1 [|b2 [|b3 [|? ?]]]] eqn:E3; cbn in L3; try lia.
  set (k := bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3).
  pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R1, R2, R3. cbn in R1, R2, R3.
  exists k, (firstn 4 (skipn 3 j)), b1, b2, b3.
  pose proof (le4_256k b1 b2 b3 0 ltac:(lia)) as E0. pose proof (le4_256k b1 b2 b3 1 ltac:(lia)) as E1. cbv zeta in E0, E1. fold k in E0, E1.
  rewrite Z.add_0_r in E0.
  split; [lia|]. split; [exact E0|]. split; [exact E1|]. split; [| exact H2].
  split; [split; [cbn; tauto|]| exact WR]. cbn [cells_bytes cbytes app]. unfold wz in E0 |- *. rewrite E0. exact B.
Qed.

(* [comment removed for export] *)
Lemma mutex_cells_to : forall m A (w : word) v b1 b2 b3 j4,
  le4 w = [zb v; b1; b2; b3] ->
  rw_cells asegs m A [C4 w] -> rw_cells asegs m (A + 4) [CB 4 j4] ->
  rw_cells asegs m A [C1 (zb v); CB 3 [b1; b2; b3]; CB 4 j4].
Proof.
  intros m A w v b1 b2 b3 j4 E H1 H2.
  assert (H1' : rw_cells asegs m A [C1 (zb v); CB 3 [b1; b2; b3]]).
  { eapply rw_cells_recast; [exact H1| cbn; auto| cbn [cells_bytes cbytes app]; rewrite E; reflexivity]. }
  apply (proj2 (rw_cells_app asegs m A [C1 (zb v); CB 3 [b1; b2; b3]] [CB 4 j4])). split; [exact H1'| exact H2].
Qed.

Lemma mutex_cells_merge : forall m A b1 b2 b3 j4,
  rw_cells asegs m A [C1 (zb 0); CB 3 [b1; b2; b3]; CB 4 j4] -> rw_cells asegs m A [W1 0; CB 7 ([b1; b2; b3] ++ j4)].
Proof.
  intros m A b1 b2 b3 j4 H. pose proof (rw_cells_merge asegs m A [C1 (zb 0)] [CB 3 [b1; b2; b3]; CB 4 j4] [] ) as M.
  cbn [app cells_size cells_bytes Cells.csize cbytes Nat.add] in M.
  specialize (M H). rewrite app_nil_r in M. cbn [app]. exact M.
Qed.

(* [comment removed for export] *)
Lemma sx32_256k_facts : forall k, 0 <= k < 2^24 ->
  let v := bv_unsigned (sx32 (Z_to_bv 64 (256*k))) in
  0 <= v < 2^64 /\ v mod 256 = 0 /\ v mod 2^32 = 256 * k /\ (v = 256 * k \/ v = 2^64 - 2^32 + 256 * k).
Proof.
  intros k Hk v. subst v. unfold sx32. rewrite (unsigned_lit (256 * k)) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32). change (Z.of_N 32 - 1) with 31.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land_255 : forall v, Z.land v 255 = v mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lxor1_even : forall v, 0 <= v -> v mod 2 = 0 -> Z.lxor v 1 = v + 1.
Proof.
  intros v Hv He. symmetry. apply Z.add_nocarry_lxor. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. exact He.
Qed.

Lemma lock_word_val : forall v, 0 <= v -> v mod 256 = 0 ->
  Z.lxor v (Z.land (Z.lxor v 1) 255) = v + 1 /\ Z.land v 255 = 0.
Proof.
  intros v Hv Hm. rewrite !lxor1_even by (try lia; Z.div_mod_to_equations; lia).
  rewrite !land_255. split; [| exact Hm]. replace ((v + 1) mod 256) with 1 by (Z.div_mod_to_equations; lia).
  apply lxor1_even; [lia| Z.div_mod_to_equations; lia].
Qed.

Lemma le4_mod32 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> x mod 2^32 = y mod 2^32 -> le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 y).
Proof.
  intros x y Hx Hy E. unfold le4. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  assert (B : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b).
  { intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256. exact H. }
  f_equal; [apply B; Z.div_mod_to_equations; lia|].
  f_equal; [apply B; Z.div_mod_to_equations; lia|].
  f_equal; [apply B; Z.div_mod_to_equations; lia|].
  f_equal. apply B; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Facts.
  Variables (st : rtstate) (m : word -> option byte).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.

  Lemma sec_obj_cells : exists j1 j2 j3,
    rw_cells asegs m A_SECONDARY [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st); CB 552 j2]
    /\ rw_cells asegs m (A_SECONDARY + 616) [W1 0; CB 7 j3].
  Proof.
    pose proof (rr_alloc st m HR) as (_ & (j1 & j2 & j3 & H) & _).
    pose proof (proj1 (rw_cells_app asegs m A_SECONDARY
       [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st); CB 552 j2]
       [W1 0; CB 7 j3]) H) as [H1 H2].
    exists j1, j2, j3. split; [exact H1| exact H2].
  Qed.

  Lemma ptr_cells : forall i, 0 <= i < nsec st -> rw_cells asegs m (st_pa st + 8 * i) [W8 (fst (nthz (st_sec st) i (0,0)))].
  Proof. pose proof (rr_ptrarr st m HR) as (_ & H & _). exact H. Qed.

  Lemma secmap_cells : forall mb n, In (mb, n) (st_sec st) -> R_secmap st m mb n.
  Proof.
    intros mb n Hin.
    pose proof (ws_entry st (wf_sec_ok st WF) (mb, n) Hin) as (HB & HN & HA & HW). cbn [fst snd] in *.
    destruct HW as [HW|HW].
    - assert (E : b_map_beg (sec_user mb) = mb) by (unfold b_map_beg, sec_user; lia).
      unfold all_blocks in HW. rewrite !in_app_iff in HW.
      assert (RB : exists md, R_block st m md (sec_user mb) n).
      { destruct HW as [HW|[HW|HW]].
        - exists BLive. exact (rr_live st m HR _ _ HW).
        - exists BQuar. exact (proj1 (rr_quar st m HR) _ _ HW).
        - exists BPend. exact (proj2 (rr_quar st m HR) _ _ HW). }
      destruct RB as [md (_ & _ & HS & _)]. unfold R_sechdr in HS. rewrite E in HS. exact (HS HB).
    - exact (proj2 (proj2 (rr_ptrarr st m HR)) (mb, n) HW).
  Qed.

  (* [comment removed for export] *)
  Lemma sec_entry_range : forall mb n, In (mb, n) (st_sec st) ->
    ablk mb (mb + smapsize n) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 /\ 0 < smapsize n /\ bprim n = false /\ 0 <= n < 2^40.
  Proof.
    intros mb n Hin.
    pose proof (ws_entry st (wf_sec_ok st WF) (mb, n) Hin) as (HB & HN & HA & _). cbn [fst snd] in *.
    pose proof (wb_ranges st (wf_base_ok st WF) (mb, mb + smapsize n)) as R.
    cbn [fst snd] in R. unfold CEIL.
    assert (In (mb, mb + smapsize n) (rt_ranges st)).
    { unfold rt_ranges. do 2 right. rewrite !in_app_iff. right. left. apply in_map_iff. exists (mb, n). split; [reflexivity| exact Hin]. }
    specialize (R ltac:(assumption)). destruct R as (R1 & R2 & R3 & R4).
    destruct (sec_facts n HB) as (F1 & _ & _ & F4 & _).
    split; [apply oclr_ablk; [exact R1| unfold usz in F4; lia| exact R3]|]. repeat split; try lia. exact HB.
  Qed.

  Lemma sec_disj : forall mb n h nh, In (mb, n) (st_sec st) -> In (h, nh) (st_sec st) ->
    h = mb \/ h + smapsize nh <= mb \/ mb + smapsize n <= h.
  Proof.
    intros mb n h nh H1 H2.
    assert (I1 : In (mb, mb + smapsize n) (rt_ranges st)).
    { unfold rt_ranges. do 2 right. rewrite !in_app_iff. right. left. apply in_map_iff. exists (mb, n). split; [reflexivity| exact H1]. }
    assert (I2 : In (h, h + smapsize nh) (rt_ranges st)).
    { unfold rt_ranges. do 2 right. rewrite !in_app_iff. right. left. apply in_map_iff. exists (h, nh). split; [reflexivity| exact H2]. }
    destruct (pwdj_In _ _ _ (wb_pwdj st (wf_base_ok st WF)) I1 I2) as [E|D]; [left; congruence| right; cbn [fst snd] in D; lia].
  Qed.
End Facts.



End CeilWrap.
End RTW_sec_defs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_secz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans.
Import RTW_sec_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition spz_ok (st : rtstate) (mb n : Z) (iv : Z * Z) : Prop :=
     (mb + 32 <= fst iv /\ snd iv <= mb + smapsize n)
  \/ (SH mb <= fst iv /\ snd iv <= SH (mb + smapsize n))
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ (CEIL <= fst iv).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MAPG.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (mb n : Z).
Hypothesis HSEC : In (mb, n) (st_sec st).
Local Abbreviation P := (st_pbase st).
Local Abbreviation T := (st_t st).

Lemma map_in_ranges : In (mb, mb + smapsize n) (rt_ranges st).
Proof. unfold rt_ranges. do 2 right. rewrite !in_app_iff. right. left. apply in_map_iff. exists (mb, n). split; [reflexivity| exact HSEC]. Qed.

(* [comment removed for export] *)
Lemma map_range : ablk mb (mb + smapsize n) /\ mb < mb + smapsize n /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0.
Proof.
  pose proof (wb_ranges st (wf_base_ok st WF) _ map_in_ranges) as R. cbn [fst snd] in R. unfold CEIL.
  pose proof (sec_entry_range st WF mb n HSEC) as (E1 & _). (nelim R 4%nat; intros _ R2 R3 R4). auto.
Qed.

Lemma map_sh_range : 0x800b7e00 <= SH mb /\ SH mb <= SH (mb + smapsize n) /\ SH (mb + smapsize n) <= 0x10007fef8000.
Proof.
  (nelimp map_range 4%nat; intros R1 R2 R3 _).
  pose proof (rt_SH_mono AIMG_HI mb (ablk_img _ _ R1)) as A. change (SH AIMG_HI) with 0x800b7e00 in A.
  pose proof (rt_SH_mono mb (mb + smapsize n) ltac:(lia)) as B.
  pose proof (rt_SH_mono (mb + smapsize n) CEIL R3) as C. pose proof SH_CEIL_range as SC. lia.
Qed.

Lemma prim_vs_map : P + PRIM_RES_SIZE <= mb \/ mb + smapsize n <= P.
Proof.
  pose proof (prim_vs_tail st WF (mb, mb + smapsize n)) as D. cbn [fst snd] in D.
  specialize (D ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (mb, n); split; [reflexivity| exact HSEC])). lia.
Qed.

Lemma pa_vs_map : st_pa st + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= st_pa st.
Proof.
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
  pose proof (pwdj_app_disj _ _ (st_pa st, st_pa st + PTRARR_RES_SIZE) (mb, mb + smapsize n) PW ltac:(right; left; reflexivity)
    ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (mb, n); split; [reflexivity| exact HSEC])) as D.
  cbn [fst snd] in D. lia.
Qed.

Lemma loose_vs_sec : forall b k e, In (b, k) (st_loose0 st) -> In e (st_sec st) ->
  b + k <= fst e \/ fst e + smapsize (snd e) <= b.
Proof.
  intros b k e Hb He. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. apply pwdj_app_r in PW.
  pose proof (pwdj_app_disj _ _ (b, b + k) (fst e, fst e + smapsize (snd e)) PW
    ltac:(apply in_map_iff; exists (b, k); split; [reflexivity| exact Hb])
    ltac:(apply in_or_app; left; apply in_map_iff; exists e; split; [reflexivity| exact He])) as D.
  cbn [fst snd] in D. lia.
Qed.
Lemma loose_vs_map : forall b k, In (b, k) (st_loose0 st) -> b + k <= mb \/ mb + smapsize n <= b.
Proof. intros b k Hb. pose proof (loose_vs_sec b k (mb, n) Hb HSEC) as D. cbn [fst snd] in D. exact D. Qed.
Lemma t_vs_map : T + 4096 <= mb \/ mb + smapsize n <= T.
Proof. exact (loose_vs_map _ _ (wb_t_loose st (wf_base_ok st WF))). Qed.
Lemma t_vs_sec : forall e, In e (st_sec st) -> T + 4096 <= fst e \/ fst e + smapsize (snd e) <= T.
Proof. intros e He. exact (loose_vs_sec _ _ e (wb_t_loose st (wf_base_ok st WF)) He). Qed.

Lemma sec_vs_map : forall e, In e (st_sec st) -> fst e <> mb -> fst e + smapsize (snd e) <= mb \/ mb + smapsize n <= fst e.
Proof.
  intros e He NE.
  assert (I2 : In (fst e, fst e + smapsize (snd e)) (rt_ranges st)).
  { unfold rt_ranges. do 2 right. rewrite !in_app_iff. right. left. apply in_map_iff. exists e. split; [reflexivity| exact He]. }
  destruct (pwdj_In _ _ _ (wb_pwdj st (wf_base_ok st WF)) map_in_ranges I2) as [E|D]; [exfalso; apply NE; congruence| cbn [fst snd] in D; lia].
Qed.
Lemma sec_range : forall e, In e (st_sec st) -> ablk (fst e) (fst e + smapsize (snd e)) /\ fst e + smapsize (snd e) <= CEIL.
Proof.
  intros e He. split; [exact (proj1 (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact He)))|]. pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R. unfold CEIL.
  specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; split; [reflexivity| exact He])). lia.
Qed.

Lemma nb_vs_map : forall b, In b (d_nblocks (st_depot st)) -> b + NODEBLOCK_SIZE <= mb \/ mb + smapsize n <= b.
Proof.
  intros b Hb. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. apply pwdj_app_r in PW.
  rewrite app_assoc in PW.
  pose proof (pwdj_app_disj _ _ (mb, mb + smapsize n) (b, b + NODEBLOCK_SIZE) PW
    ltac:(apply in_or_app; right; apply in_map_iff; exists (mb, n); split; [reflexivity| exact HSEC])
    ltac:(apply in_or_app; left; apply in_map_iff; exists b; split; [reflexivity| exact Hb])) as D.
  cbn [fst snd] in D. lia.
Qed.
Lemma nb_vs_t : forall b, In b (d_nblocks (st_depot st)) -> b + NODEBLOCK_SIZE <= T \/ T + 4096 <= b.
Proof.
  intros b Hb. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. apply pwdj_app_r in PW.
  pose proof (pwdj_app_disj _ _ (T, T + 4096) (b, b + NODEBLOCK_SIZE) PW
    ltac:(apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))])
    ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists b; split; [reflexivity| exact Hb])) as D.
  cbn [fst snd] in D. lia.
Qed.
Lemma nb_range : forall b, In b (d_nblocks (st_depot st)) -> oclr b (b + NODEBLOCK_SIZE) /\ b + NODEBLOCK_SIZE <= CEIL.
Proof.
  intros b Hb. pose proof (wb_ranges st (wf_base_ok st WF) (b, b + NODEBLOCK_SIZE)) as R. cbn [fst snd] in R. unfold CEIL.
  specialize (R ltac:(rewrite rt_ranges_tail; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists b; auto)). (nelim R 4%nat; intros R1 _ R3 _). split; assumption.
Qed.
Lemma prim_vs_t : P + PRIM_RES_SIZE <= T \/ T + 4096 <= P.
Proof.
  pose proof (prim_vs_tail st WF (T, T + 4096)) as D. cbn [fst snd] in D.
  specialize (D ltac:(apply in_or_app; left; apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))])). lia.
Qed.
End MAPG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SPZ.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (mb n : Z).
Hypothesis HSP : In (mb, n) (st_spend st).
Variable W : list (Z * Z).
Hypothesis HW : Forall (spz_ok st mb n) W.
Local Abbreviation P := (st_pbase st).
Local Abbreviation T := (st_t st).

Lemma spz_sec : In (mb, n) (st_sec st). Proof. exact (proj1 (ws_spend st (wf_sec_ok st WF) _ HSP)). Qed.
Lemma spz_noblock : ~ In (sec_user mb, n) (all_blocks st). Proof. exact (proj2 (ws_spend st (wf_sec_ok st WF) _ HSP)). Qed.

(* [comment removed for export] *)
Lemma spz_disj : forall a sz,
  (a + sz <= mb + 32 \/ mb + smapsize n <= a) ->
  (a + sz <= SH mb \/ SH (mb + smapsize n) <= a) ->
  (a + sz <= T + T_STATS \/ T + T_UNWINDING <= a) ->
  a + sz <= CEIL ->
  disjoint_from W a sz.
Proof.
  intros a sz D1 D2 D3 D4. pose proof HW as HW'. clear HW. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW') as K. unfold spz_ok in K. cbn [fst snd] in K. cbn. split; [| apply IH; exact (Forall_inv_tail HW')].
  lia.
Qed.

Local Ltac geom :=
  (nelimp (map_range st WF mb n spz_sec) 4%nat; intros MR1 MR2 MR3 MR4);
  (nelimp (map_sh_range st WF mb n spz_sec) 3%nat; intros MS1 MS2 MS3);
  pose proof (t_range st WF) as (TR1 & TR2);
  unfold KHIGHMEM_BEG, AIMG_HI in *.

(* [comment removed for export] *)
Lemma S1 : forall a sz, AIMG_LO <= a -> a + sz <= A_SECONDARY -> disjoint_from W a sz.
Proof. intros a sz H0 H. geom. rewrite A_SECONDARY_val in H. apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING, AIMG_LO in *; blia. Qed.
Lemma S2 : forall a sz, A_QUAR <= a -> a + sz <= KHIGHSHADOW_BEG ->
  (a + sz <= AIMG_HI \/ (KLOWSHADOW_BEG <= a /\ a + sz <= SH AIMG_HI)) -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2 H3. change (SH AIMG_HI) with 0x800b7e00 in H3. geom. rewrite KHIGHSHADOW_BEG_val in H2. rewrite A_QUAR_val in H1.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING, AIMG_LO, KLOWSHADOW_BEG in *; blia.
Qed.
Lemma S5 : forall b a sz, In b (d_nblocks (st_depot st)) -> b <= a -> a + sz <= b + NODEBLOCK_SIZE -> disjoint_from W a sz.
Proof.
  intros b a sz Hb H1 H2. geom. pose proof (nb_vs_map st WF mb n spz_sec b Hb) as D1. pose proof (nb_vs_t st WF b Hb) as D2.
  pose proof (nb_range st WF b Hb) as (R1 & R2). unfold KHIGHMEM_BEG, AIMG_HI in R1.
  apply spz_disj; unfold T_STATS, T_UNWINDING in *; blia.
Qed.
Lemma SZprim : forall a sz, P <= a -> a + sz <= P + PRIM_RES_SIZE -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. geom. pose proof (prim_vs_map st WF mb n spz_sec) as D1. pose proof (prim_vs_t st WF) as D2.
  (nelimp (P_range st WF) 3%nat; intros Q1 Q2 _). unfold KHIGHMEM_BEG, AIMG_HI in Q1.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; lia.
Qed.
Lemma SZprim_sh : forall a b, P <= a -> a <= b -> b <= P + PRIM_RES_SIZE -> disjoint_from W (SH a) (SH b - SH a).
Proof.
  intros a b H1 H2 H3. geom. pose proof (prim_vs_map st WF mb n spz_sec) as D1.
  (nelimp (P_range st WF) 3%nat; intros Q1 Q2 _). unfold KHIGHMEM_BEG, AIMG_HI in Q1.
  pose proof (rt_SH_mono a b H2) as M0.
  pose proof (rt_SH_mono (P + PRIM_RES_SIZE) (@CEIL ACEIL) ltac:(unfold CEIL in *; lia)) as M1. rewrite SH_CEIL in M1.
  pose proof (rt_SH_mono b (P + PRIM_RES_SIZE) H3) as M2.
  assert (D : SH b <= SH mb \/ SH (mb + smapsize n) <= SH a).
  { destruct D1 as [D1|D1]; [left; apply rt_SH_mono; lia| right; apply rt_SH_mono; lia]. }
  pose proof alloc_ceiling_range as ACR.
  pose proof (rt_SH_bounds a ltac:(unfold CEIL in *; lia)) as BA. pose proof (rt_SH_bounds b ltac:(unfold CEIL in *; lia)) as BB.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
Qed.
(* [comment removed for export] *)
Lemma SZsec : forall e a sz, In e (st_sec st) -> fst e <> mb -> fst e <= a -> a + sz <= fst e + smapsize (snd e) -> disjoint_from W a sz.
Proof.
  intros e a sz He NE H1 H2. geom. pose proof (sec_vs_map st WF mb n spz_sec e He NE) as D1. pose proof (t_vs_sec st WF e He) as D2.
  pose proof (sec_range st WF e He) as (R1 & R2). unfold KHIGHMEM_BEG, AIMG_HI in R1.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
Qed.
Lemma SZsec_sh : forall e a b, In e (st_sec st) -> fst e <> mb -> fst e <= a -> a <= b -> b <= fst e + smapsize (snd e) ->
  disjoint_from W (SH a) (SH b - SH a).
Proof.
  intros e a b He NE H1 H2 H3. geom. pose proof (sec_vs_map st WF mb n spz_sec e He NE) as D1.
  pose proof (sec_range st WF e He) as (R1 & R2). unfold KHIGHMEM_BEG, AIMG_HI in R1.
  pose proof (rt_SH_mono a b H2) as M0.
  pose proof (rt_SH_mono (fst e + smapsize (snd e)) CEIL R2) as M1. rewrite SH_CEIL in M1.
  pose proof (rt_SH_mono b (fst e + smapsize (snd e)) H3) as M2.
  assert (D : SH b <= SH mb \/ SH (mb + smapsize n) <= SH a).
  { destruct D1 as [D1|D1]; [left; apply rt_SH_mono; lia| right; apply rt_SH_mono; lia]. }
  pose proof alloc_ceiling_range as ACR. (nelimp (ablk_lin _ _ R1) 4%nat; intros L1 L2 L3 L4).
  pose proof (rt_SH_bounds a ltac:(unfold CEIL in *; lia)) as BA. pose proof (rt_SH_bounds b ltac:(unfold CEIL in *; lia)) as BB.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
Qed.
(* [comment removed for export] *)
Lemma block_map_other : forall A n', In (A, n') (all_blocks st) -> bprim n' = false -> b_map_beg A <> mb.
Proof.
  intros A n' HB HP E. (nelimp (wk_block st (wf_blocks_ok st WF) _ HB) 4%nat; intros _ _ _ Gs). cbn [fst snd] in Gs. specialize (Gs HP).
  rewrite E in Gs.
  pose proof (nodup_map_inj fst (st_sec st) (mb, n') (mb, n) (ws_nodup st (wf_sec_ok st WF)) Gs spz_sec eq_refl) as EQ.
  injection EQ as En. subst n'. apply spz_noblock. replace (sec_user mb) with A; [exact HB|].
  unfold sec_user. rewrite <- E. unfold b_map_beg. lia.
Qed.
Lemma SZloose : forall b k a sz, In (b, k) (st_loose0 st) -> b <= a -> a + sz <= b + k ->
  (b + k <= T \/ T + 4096 <= b \/ a + sz <= T + T_STATS \/ T + T_UNWINDING <= a) -> disjoint_from W a sz.
Proof.
  intros b k a sz Hin H1 H2 H3. geom. pose proof (loose_vs_map st WF mb n spz_sec b k Hin) as D1.
  (nelimp (loose0_range st WF b k Hin) 4%nat; intros R1 R2 R3 R4). unfold KHIGHMEM_BEG, AIMG_HI in R1.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
Qed.

Local Ltac s12 := first [ apply S1; rewrite ?A_SECONDARY_val; unfold AIMG_LO; lia
                         | apply S2; rewrite ?A_QUAR_val, ?KHIGHSHADOW_BEG_val; change (SH AIMG_HI) with 0x800b7e00; unfold AIMG_HI, KLOWSHADOW_BEG; lia ].

Lemma SP_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); s12| unfold A_GLOBREC_LO, A_GLOBREC_HI; s12]. Qed.
Lemma SP_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; s12.
Qed.
Lemma SP_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_MAXUSERSZ. rewrite A_SECONDARY_val, A_QUAR_val. unfold A_ALLOC, A_GSTATS, A_ALLOC.
  geom. repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING, AIMG_LO in *; blia.
Qed.
Lemma SP_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. s12. Qed.
Lemma SP_lowshadow : WOK_lowshadow W.
Proof. intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. s12. Qed.
Lemma SP_depot : WOK_depot st W.
Proof.
  pose proof (wf_depot_ok st WF) as WD. unfold WOK_depot.
  unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i Hi. s12.
  - s12.
  - intros k Hk. s12.
  - intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (b := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    apply (S5 b); [exact Hb| Z.div_mod_to_equations; lia| unfold NODEBLOCK_SIZE; Z.div_mod_to_equations; lia].
  - s12.
  - intros b Hb. s12.
Qed.
Lemma SP_rinfo : WOK_rinfo st W.
Proof. intros c Hc. (nelimp (ris_range st WF) 4%nat; intros X1 X2 X3 X4). unfold KNUMCLASSES in Hc. apply SZprim; unfold rinfo; lia. Qed.
Lemma SP_regions : WOK_regions st W.
Proof.
  intros c Hc. pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NF. apply SZprim; lia.
  - replace ((r_mapped (rg st c) - r_allocated (rg st c)) / 8) with (SH (rbeg st c + r_mapped (rg st c)) - SH (rbeg st c + r_allocated (rg st c)))
      by (rewrite !rt_SH_aligned_add by exact X8; Z.div_mod_to_equations; lia).
    apply SZprim_sh; lia.
Qed.
Lemma SP_avail : WOK_avail st W.
Proof.
  intros c k Hc Hk.
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  destruct (Z.eq_dec c 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hk. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hk. cbn in Hk.
    unfold apend_cptrs in Hk. apply in_map_iff in Hk as ([c' k'] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c'. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c (wf_class_ok st WF c Hc)). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hk. tauto. }
  (nelim (carved_chunk st WF c k Hc ltac:(lia) CV) 3%nat; intros C1 C2 C3).
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP. pose proof (csize_mod32 c ltac:(unfold KNUMCLASSES in Hc; lia)) as SM.
  assert (AL : cptr_addr st c k mod 8 = 0).
  { apply (mod0_of_sub _ (rbeg st c) 8 ltac:(lia)); [| exact X8]. apply (mod0_trans _ 8 (csize c)); [lia|lia| apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact SM]| exact C3]. }
  replace (csize c / 8) with (SH (cptr_addr st c k + csize c) - SH (cptr_addr st c k)) by (rewrite rt_SH_aligned_add by exact AL; lia).
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *. apply SZprim_sh; lia.
Qed.
Lemma SPt : forall a sz, T <= a -> a + sz <= T + T_STATS -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. eapply SZloose; [exact (wb_t_loose st (wf_base_ok st WF))| lia| unfold T_STATS in *; lia| lia].
Qed.
Lemma SP_cache : WOK_cache st W.
Proof.
  intros c Hc. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc)) as CM. pose proof (cmaxcount_le16 c). unfold KNUMCLASSES in Hc.
  split.
  - apply SPt; unfold pcaddr, acache, T_ACACHE, T_STATS; lia.
  - intros i Hi. apply SPt; unfold pcaddr, acache, T_ACACHE, T_STATS; lia.
Qed.
Lemma SP_thread : WOK_thread st W.
Proof.
  unfold WOK_thread.
  split; [apply SPt; unfold T_STATS; lia|].
  split; [apply SPt; unfold qcache_t, T_QCACHE, T_STATS; lia|].
  split; [eapply SZloose; [exact (wb_t_loose st (wf_base_ok st WF))| unfold T_UNWINDING; lia| unfold T_UNWINDING; lia| lia]|].
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3). pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
  (nelim (loose0_range st WF _ _ CL1) 4%nat; intros Q1 Q2 Q3 Q4).
  assert (CTX : forall a sz, st_ctx st <= a -> a + sz <= st_ctx st + 160 -> disjoint_from W a sz).
  { intros a sz H1 H2. eapply SZloose; [exact CL1| lia| lia|]. unfold T_STATS, T_UNWINDING. lia. }
  split; [apply CTX; unfold CTX_TID; lia|].
  split; [apply CTX; unfold CTX_THREAD; lia|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|].
  (nelim (wb_dtls_loose st (wf_base_ok st WF)) 5%nat; intros db dk DL1 DL2 DL3). pose proof (wb_dtls_t st (wf_base_ok st WF)) as DT.
  eapply SZloose; [exact DL1| lia| lia| unfold T_STATS, T_UNWINDING; lia].
Qed.
Lemma SP_block : forall A n', In (A, n') (all_blocks st) -> WOK_block W A n'.
Proof.
  intros A n' HB.
  (nelimp (block_geom st WF A n' HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs). unfold usz in Y. unfold KHIGHMEM_BEG, AIMG_HI in K.
  pose proof (rz_size_range n') as (Z1 & Z2).
  assert (ASZ : b_hi A n' = b_lo A n' + asz n') by reflexivity.
  apply WOK_block_intro.
  - intros a sz Ha Hs. destruct (bprim n') eqn:EP.
    + (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). apply SZprim; lia.
    + (nelim (Gs eq_refl) 3%nat; intros S1' T1 _). eapply (SZsec (b_lo A n', n')); [exact S1'| | cbn [fst]; lia| cbn [fst snd]; lia].
      cbn [fst]. unfold b_lo. rewrite EP. exact (block_map_other A n' HB EP).
  - unfold sh_tot. replace (asz n' / 8) with (SH (b_hi A n') - SH (b_lo A n')).
    2:{ rewrite ASZ, rt_SH_aligned_add by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
        destruct (bprim n') eqn:EP; [(nelim (prim_facts n' EP) 5%nat; intros _ _ F3 F4 F5); rewrite F5 | (nelim (sec_facts n' EP) 6%nat; intros _ _ F3 _ F5 _); rewrite F5]; Z.div_mod_to_equations; lia. }
    destruct (bprim n') eqn:EP.
    + (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). apply SZprim_sh; lia.
    + (nelim (Gs eq_refl) 3%nat; intros S1' T1 _). eapply (SZsec_sh (b_lo A n', n')); [exact S1'| | cbn [fst]; lia| lia| cbn [fst snd]; lia].
      cbn [fst]. unfold b_lo. rewrite EP. exact (block_map_other A n' HB EP).
  - rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n') eqn:EP.
    + Z.div_mod_to_equations. lia.
    + (nelim (sec_facts n' EP) 3%nat; intros _ F2 _). rewrite F2. cbn. lia.
Qed.
Lemma SP_live : WOK_live st W.
Proof. intros A n' Hin. apply SP_block. unfold all_blocks; apply in_or_app; left; exact Hin. Qed.
Lemma SP_quar : WOK_quar st W.
Proof. intros A n' Hin. apply SP_block. unfold all_blocks; apply in_or_app; right; exact Hin. Qed.
Lemma SP_batches : WOK_batches st W.
Proof.
  intros b Hb.
  (nelim (batch_geom st WF b Hb) 5%nat; intros BB BF R1 R2 AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split].
  - apply SZprim; lia.
  - intros i Hi. apply SZprim; lia.
  - assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    replace 1024 with (SH (qb_addr b + 8192) - SH (qb_addr b)) by (rewrite rt_SH_aligned_add by exact AL8; change (8192 / 8) with 1024; lia).
    apply SZprim_sh; lia.
Qed.
Lemma SP_ptrarr : WOK_ptrarr st W.
Proof.
  geom. (nelimp (pa_range st WF) 5%nat; intros Q1 Q2 Q3 Q4 Q5). unfold KHIGHMEM_BEG, AIMG_HI in Q1. pose proof (pa_vs_map st WF mb n spz_sec) as D1.
  assert (PT : st_pa st + PTRARR_RES_SIZE <= T \/ T + 4096 <= st_pa st).
  { pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
    pose proof (pwdj_app_disj _ _ (st_pa st, st_pa st + PTRARR_RES_SIZE) (T, T + 4096) PW ltac:(right; left; reflexivity)
      ltac:(apply in_or_app; left; apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))])) as D.
    cbn [fst snd] in D. lia. }
  split.
  - intros i Hi. apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _]. pose proof (sec_range st WF e HE) as (R1 & R2). unfold KHIGHMEM_BEG, AIMG_HI in R1.
    pose proof (t_vs_sec st WF e HE) as D2.
    pose proof (ws_entry st (wf_sec_ok st WF) e HE) as (EP & _). (nelimp (sec_facts (snd e) EP) 5%nat; intros _ _ _ SZ _). unfold usz in SZ.
    destruct (Z.eq_dec (fst e) mb) as [E|NE].
    + apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
    + pose proof (sec_vs_map st WF mb n spz_sec e HE NE) as D3. apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
Qed.
Lemma SP_fs : WOK_fs st W.
Proof.
  pose proof (wb_fs_loose st (wf_base_ok st WF)) as FL. (nelimp (t_page st WF) 4%nat; intros _ _ _ TF). unfold framefree in TF.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz H1 H2. eapply SZloose; [exact FL| exact H1| exact H2| lia]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k Hin. (nelimp (frame_range st WF F k Hin) 4%nat; intros Hk X1 X2 _). pose proof (fsz_12 k Hk) as (FZ & _).
    assert (8 <= fsz k) by (rewrite FZ; destruct Hk as [-> | ->]; cbn; lia).
    apply OBJ; unfold FS_FRAMES_OFF in *; lia.
Qed.

(* [comment removed for export] *)
Theorem spz_rtrep : forall m m', munch W m m' -> wmono asegs m m' -> RTREP st m -> RTREP st m'.
Proof.
  intros m m' MU WM HR.
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T st W m m' MU) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  constructor.
  - tapp T_link st WF W m m' MU WM; [exact (rr_link st m HR)| apply SP_link].
  - tapp T_consts st WF W m m' MU WM; [exact (rr_consts st m HR)| apply SP_consts].
  - tapp T_alloc st WF W m m' MU WM; [exact (rr_alloc st m HR)| apply SP_alloc].
  - tapp T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| apply SP_rinfo].
  - tapp T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| apply SP_regions].
  - tapp T_avail st WF W m m' MU WM; [exact (rr_avail st m HR)| apply SP_avail].
  - tapp T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| apply SP_cache].
  - tapp T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| apply SP_thread].
  - tapp T_live st WF W m m' MU WM; [exact (rr_live st m HR)| apply SP_live].
  - tapp T_quar st WF W m m' MU WM; [exact (rr_quar st m HR)| apply SP_quar].
  - tapp T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| apply SP_batches].
  - tapp T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| apply SP_ptrarr].
  - tapp T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| apply SP_depot].
  - tapp T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| apply SP_fs].
  - tapp T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| apply SP_ia].
  - tapp T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| apply SP_lowshadow].
Qed.
End SPZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_liveS (st : rtstate) (mb n : Z) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 ((sec_user mb, n) :: LB) AP (remove_first ck_eqb (mb, n) SP) QP b4 b5
  end.

Lemma st_liveS_same : forall st mb n,
  st_sp0 (st_liveS st mb n) = st_sp0 st /\ st_lb (st_liveS st mb n) = (sec_user mb, n) :: st_lb st /\ st_lf (st_liveS st mb n) = st_lf st
  /\ st_trs (st_liveS st mb n) = st_trs st /\ st_apend (st_liveS st mb n) = st_apend st
  /\ st_spend (st_liveS st mb n) = remove_first ck_eqb (mb, n) (st_spend st) /\ st_sec (st_liveS st mb n) = st_sec st
  /\ st_qpend (st_liveS st mb n) = st_qpend st /\ st_qtmp (st_liveS st mb n) = st_qtmp st /\ st_qcur (st_liveS st mb n) = st_qcur st
  /\ st_qthread (st_liveS st mb n) = st_qthread st /\ st_qglobal (st_liveS st mb n) = st_qglobal st /\ st_depot (st_liveS st mb n) = st_depot st
  /\ st_fs (st_liveS st mb n) = st_fs st /\ st_t (st_liveS st mb n) = st_t st /\ st_spacebeg (st_liveS st mb n) = st_spacebeg st
  /\ st_pbase (st_liveS st mb n) = st_pbase st /\ st_pa (st_liveS st mb n) = st_pa st
  /\ st_ctx (st_liveS st mb n) = st_ctx st /\ st_tls (st_liveS st mb n) = st_tls st /\ st_cache_inited (st_liveS st mb n) = st_cache_inited st
  /\ st_regions (st_liveS st mb n) = st_regions st /\ st_nreserved (st_liveS st mb n) = st_nreserved st
  /\ st_trs0 (st_liveS st mb n) = st_trs0 st /\ st_hints (st_liveS st mb n) = st_hints st /\ st_loose0 (st_liveS st mb n) = st_loose0 st
  /\ st_ia_inited (st_liveS st mb n) = st_ia_inited st /\ st_cache (st_liveS st mb n) = st_cache st.
Proof. intros st mb n. destruct st. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.

Lemma RTWF_liveS' : forall st mb n, RTWF st -> bprim n = false -> In (mb, n) (st_spend st) -> RTWF (st_liveS st mb n).
Proof. intros st mb n WF HP HIN. destruct st. eapply RTWF_liveS; eauto. Qed.
Lemma rt_prov_liveS' : forall st mb n, bprim n = false -> rt_prov (st_liveS st mb n) = rt_prov st + fp n + rp n.   (* [comment removed for export] *)
Proof. intros st mb n HP. destruct st. eapply rt_prov_liveS; eauto. Qed.
Lemma RTMODEL_liveS' : forall st mb n mo, RTMODEL st mo -> RTMODEL (st_liveS st mb n) mo.
Proof. intros st mb n mo H. destruct st. exact H. Qed.
Lemma SWIN_liveS' : forall st mb n g, SWIN st g -> SWIN (st_liveS st mb n) g.
Proof. intros st mb n g H. destruct st. exact H. Qed.
Lemma GWIN_liveS' : forall st mb n m mo g, GWIN st m mo g -> GWIN (st_liveS st mb n) m mo g.
Proof. intros st mb n m mo g H. destruct st. exact H. Qed.
Lemma liveS_fresh' : forall st mb n, RTWF st -> bprim n = false -> In (mb, n) (st_spend st) ->
  forall A' n', In (A', n') (all_blocks st) -> A' <> sec_user mb.
Proof. intros st mb n WF HP HIN A' n' HB. destruct st. eapply liveS_fresh; eauto. Qed.
Lemma liveS_quiet_spend : forall st mb n, st_spend st = [(mb, n)] -> st_spend (st_liveS st mb n) = [].
Proof. intros st mb n E. destruct st. cbn in E |- *. rewrite E. cbn. rewrite (proj2 (ck_eqb_eq _ _) eq_refl). reflexivity. Qed.

Section LIVESM.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (mb n : Z).
Hypothesis HSP : In (mb, n) (st_spend st).
Let A := sec_user mb.
Let stL := st_liveS st mb n.

Lemma R_block_liveS : forall m md A' n', R_block st m md A' n' -> R_block stL m md A' n'.
Proof. intros m md A' n' H. unfold stL, st_liveS. destruct st. exact H. Qed.

Theorem RTREP_liveS' : forall W m m',
  Forall (spz_ok st mb n) W -> munch W m m' -> wmono asegs m m' -> RTREP st m ->
  R_block st m' BLive A n ->
  RTREP stL m'.
Proof.
  intros W m m' HW MU WM HR HB.
  pose proof (spz_rtrep st WF mb n HSP W HW m m' MU WM HR) as HR'.
  assert (RL : R_live stL m').
  { unfold stL. intros A' n' Hin. (nelim (st_liveS_same st mb n) 3%nat; intros _ E _). rewrite E in Hin.
    destruct Hin as [E'|Hin].
    - injection E' as E1 E2. subst A' n'. apply R_block_liveS. exact HB.
    - apply R_block_liveS. exact (rr_live st m' HR' A' n' Hin). }
  assert (RP : R_ptrarr stL m').
  { (nelim (rr_ptrarr st m' HR') 3%nat; intros V C S). unfold stL, st_liveS in *. destruct st. split; [exact V|]. split; [exact C|].
    intros e He. cbn in He. pose proof (S e (remove_first_In _ _ _ _ He)) as X. exact X. }
  destruct HR'. unfold stL, st_liveS in *. destruct st. constructor; assumption.
Qed.
End LIVESM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition spzc_ok (st : rtstate) (mb n SP : Z) (iv : Z * Z) : Prop :=
     (mb + 32 <= fst iv /\ snd iv <= mb + smapsize n)
  \/ (SH mb <= fst iv /\ snd iv <= SH (mb + smapsize n))
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ (CEIL <= fst iv /\ snd iv <= SP).

Lemma spzc_spz : forall st mb n SP W, Forall (spzc_ok st mb n SP) W -> Forall (spz_ok st mb n) W.
Proof.
  intros st mb n SP W H. eapply Forall_impl; [| exact H]. intros [lo hi] A1. unfold spzc_ok, spz_ok in *. cbn [fst snd] in *. tauto.
Qed.

Section CLIS.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (mb n : Z).
Hypothesis HSP : In (mb, n) (st_spend st).
Variable SP : Z.
Hypothesis HSPc : CEIL <= SP.

Lemma map_not_client : forall a, mb <= a < mb + smapsize n -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha HC. pose proof (spz_sec st WF mb n HSP) as HE.
  (nelimp (map_range st WF mb n HE) 4%nat; intros MR1 MR2 MR3 MR4). unfold KHIGHMEM_BEG, AIMG_HI in MR1.
  destruct HC as [H|[H|[(A & n' & Hb & Hr)|[(F & j & Hb & Hr)|H]]]].
  - unfold CEIL in *. lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI in *. blia.
  - assert (HB : In (A, n') (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (spend_blockfree st WF (mb, n) HSP A n' HB) as D. cbn [fst snd] in D.
    (nelimp (block_geom st WF A n' HB) 6%nat; intros _ _ _ X Y _). unfold usz in Y. lia.
  - (nelimp (frame_range st WF F j Hb) 4%nat; intros Hk X Y AL). (nelimp (fs_range st WF) 3%nat; intros F1 F2 _).
    pose proof (sec_framefree st WF mb n HE) as D. unfold framefree in D. change FS_FRAMES_OFF with 36864 in X. unfold KHIGHMEM_BEG, AIMG_HI in F1.
    assert (8 <= fsz j) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr]; [lia|].
    pose proof (rt_SH_bounds (F + fsz j) ltac:(unfold CEIL in *; blia)) as B. rewrite (rt_SH_aligned_add F (fsz j) AL) in B.
    pose proof (rt_SH_bounds F ltac:(unfold CEIL in *; blia)) as B0. blia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. blia.
Qed.

Lemma map_shadow_not_client : forall a, SH mb <= a < SH (mb + smapsize n) -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha HC. pose proof (spz_sec st WF mb n HSP) as HE.
  (nelimp (map_range st WF mb n HE) 4%nat; intros MR1 MR2 MR3 MR4). unfold KHIGHMEM_BEG, AIMG_HI in MR1.
  (nelimp (map_sh_range st WF mb n HE) 3%nat; intros MS1 MS2 MS3).
  destruct HC as [H|[H|[(A & n' & Hb & Hr)|[(F & j & Hb & Hr)|H]]]].
  - unfold CEIL in *. lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI in *. lia.
  - assert (HB : In (A, n') (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    (nelimp (block_geom st WF A n' HB) 6%nat; intros _ _ X0 X Y _). unfold usz in Y. unfold KHIGHMEM_BEG, AIMG_HI in *. blia.
  - (nelimp (frame_range st WF F j Hb) 4%nat; intros Hk X Y AL). (nelimp (fs_range st WF) 3%nat; intros F1 F2 _).
    pose proof (loose_vs_map st WF mb n HE _ _ (wb_fs_loose st (wf_base_ok st WF))) as D.
    change FS_FRAMES_OFF with 36864 in X. unfold KHIGHMEM_BEG, AIMG_HI in F1.
    assert (8 <= fsz j) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr]; [blia|].
    rewrite <- (rt_SH_aligned_add F (fsz j) AL) in Hr.
    destruct D as [D|D].
    + pose proof (rt_SH_mono (F + fsz j) mb ltac:(lia)). lia.
    + pose proof (rt_SH_mono (mb + smapsize n) F ltac:(lia)). lia.
  - unfold astack_shadow in H. pose proof (rt_SH_mono (mb + smapsize n) CEIL MR3) as MC. rewrite ?CEIL_eq in *. lia.
Qed.

Lemma cli_pres_spz : forall W m m',
  munch W m m' -> wmono asegs m m' -> Forall (spzc_ok st mb n SP) W -> cli_pres st SP m m'.
Proof.
  intros W m m' MU WM HW. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold spzc_ok in A1. cbn [fst snd] in A1. cbn. split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. destruct A1 as [A1|[A1|[A1|A1]]].
  - apply (map_not_client a); [lia| exact HC].
  - apply (map_shadow_not_client a); [lia| exact HC].
  - apply (tpage_not_client st WF SP HSPc a); [unfold T_STATS, T_UNWINDING, T_ACACHE in *; lia| exact HC].
  - apply (below_sp_not_client st WF SP a); [lia| exact HC].
Qed.
End CLIS.


End CeilWrap.
