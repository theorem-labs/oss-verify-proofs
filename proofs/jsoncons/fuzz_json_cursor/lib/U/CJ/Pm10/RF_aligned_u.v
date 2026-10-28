(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import F_malloc_free_u F_malloc_fast_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Pm10 Require Import F_syscalls_u RMallocRep_u RF_get_meta_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc Monad.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Lemma write_to_mem_same : forall bs m a,
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, (i < length bs)%nat -> m (wa (a + Z.of_nat i)) = nth_error bs i) ->
  write_to_mem m (wa a) bs = m.
Proof.
  intros bs m a Ha Hl H. extensionality x.
  rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  rewrite <- (H (Z.to_nat (bv_unsigned x - a))) by lia.
  replace (a + Z.of_nat (Z.to_nat (bv_unsigned x - a))) with (bv_unsigned x) by lia.
  unfold wa. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma bytes_at_overlay : forall m a bs,
  bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= 0x10000 \/ 0xf8000 <= a) ->
  forall i, (i < length bs)%nat -> m (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros m a bs (A0 & Ahi & BA) OUT i Hi. rewrite <- (BA i Hi). symmetry. apply ref_mrd_overlay.
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_overlay1 : forall m a b,
  rw_cells rsegs m a [C1 b] -> (a + 1 <= 0x10000 \/ 0xf8000 <= a) -> m (wa a) = Some b.
Proof.
  intros m a b [[_ BA] _] OUT. cbn [cells_bytes cbytes app] in BA.
  pose proof (bytes_at_overlay m a [b] BA OUT 0%nat ltac:(cbn; lia)) as H. rewrite Z.add_0_r in H. exact H.
Qed.

Lemma rw_cells_overlay4 : forall m a (w : word),
  rw_cells rsegs m a [C4 w] -> (a + 4 <= 0x10000 \/ 0xf8000 <= a) ->
  forall i, (i < 4)%nat -> m (wa (a + Z.of_nat i)) = nth_error (le4 w) i.
Proof.
  intros m a w [[_ BA] _] OUT. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
  intros i Hi. apply (bytes_at_overlay m a (le4 w) BA); rewrite ?length_le4; [exact OUT| exact Hi].
Qed.

Section AFTER.
Lemma evt_after_step : forall (P : machine_state -> Prop) ms ms1,
  evt rsegs P ms -> mstep rsegs ms ms1 -> (P ms -> P ms1) -> evt rsegs P ms1.
Proof.
  intros P ms ms1 (ms' & Hs & HP) ST HPP. inversion Hs; subst.
  - apply evt_done. apply HPP. exact HP.
  - pose proof (mstep_det rsegs _ _ _ ST H) as ->. exists ms'. split; assumption.
Qed.

Lemma impl_after_step : forall {R} (t : itree node R) Q ms ms1,
  impl rsegs (at_node rsegs) t Q ms -> mstep rsegs ms ms1 ->
  (forall r, Q r ms -> Q r ms1) -> (forall n, ~ at_node rsegs n ms) ->
  impl rsegs (at_node rsegs) t Q ms1.
Proof.
  intros R t Q ms ms1 H ST HQ HN. destruct t as [r|n k]; cbn [impl] in *.
  - eapply evt_after_step; [exact H| exact ST| apply HQ].
  - eapply evt_after_step; [exact H| exact ST|]. intros [Hat _]. exfalso. exact (HN n Hat).
Qed.

Lemma implM_after_step : forall {TS A : Type} (c : Monad.M TS A) (s : TS) Q ms ms1,
  implM rsegs c s Q ms -> mstep rsegs ms ms1 ->
  (forall a s', Q a s' ms -> Q a s' ms1) -> (forall n, ~ at_node rsegs n ms) ->
  implM rsegs c s Q ms1.
Proof.
  intros TS A c s Q ms ms1 H ST HQ HN. unfold implM in *. eapply impl_after_step; [exact H| exact ST| | exact HN].
  intros [|[a s']]; cbn [epost]; [trivial| apply HQ].
Qed.

Lemma impl_post_evt : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl rsegs (at_node rsegs) t Q ms -> (forall r ms', Q r ms' -> evt rsegs (Q' r) ms') -> impl rsegs (at_node rsegs) t Q' ms.
Proof.
  intros R t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn [impl] in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk| exact HQ].
Qed.

Lemma implM_post_evt : forall {TS A : Type} (c : Monad.M TS A) (s : TS) (Q Q' : A -> TS -> machine_state -> Prop) ms,
  implM rsegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt rsegs (Q' a s') ms') -> implM rsegs c s Q' ms.
Proof.
  intros TS A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms'; cbn [epost fst snd]; [intros _; apply evt_done; exact I| apply HQ].
Qed.
End AFTER.

Lemma at_node_svc_none : forall n R F pc fc m ro, ~ at_node rsegs n (MS R F pc fc None m ro).
Proof.
  intros n R F pc fc m ro H. destruct n; cbn [at_node ms_svc_pending MS] in H;
    repeat match type of H with _ /\ _ => destruct H as [H _] | _ \/ _ => destruct H as [H|H] end; discriminate H.
Qed.

Definition RAA_SYM : Z := 0xa9148.
Definition RMALLOC_IMPL : Z := 0xa9db4.
Definition RAA_RET : Z := 0xa91e8.

Definition raa_pre_post (sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (n : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (junk : list byte) m',
    ms' = MS (mkR (wz RAA_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz 16) (wz n) (wz n) (wz n) (wz 16) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 RMALLOC_IMPL) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra].

Lemma raa_pre_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (lo n : Z),
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv rsegs m ->
  rw_cells rsegs m (RCTX + 928) [C4 (wz 0); C4 (wz 0)] ->
  a0 = wz 16 -> a1 = wz n -> 0 <= n <= 2^32 ->
  evt rsegs (raa_pre_post sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra n F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RAA_SYM) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros ST CLO LO MI REPL -> -> Hn. unfold RAA_SYM. pose_ceil. unfold RCTX in REPL. replace (1010704 + 928) with 1011632 in REPL by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  step. step. step. step.

  step. step. step. if_false.

  step. step. if_false.

  step. step. if_cases K; zify_cond K.
  { exfalso. revert K. rewrite !wz_unsigned by lia. change (Z.lxor 16 18446744073709551615) with 18446744073709551599. lia. }

  step. step. step. if_true.

  step. step. if_false. step. step. step. step. step. step.
  replace (16 + n + -16) with n by lia. unfold raa_pre_post. finish. exact FR.
Qed.

Lemma raa_null_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (junk : list byte) (s1o s0o rao : word) (n : Z),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs (fun ms' => ms' = MS (mkR rao (wz (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rao) fc None m (seg_rom rsegs))
      (MS (mkR (wz RAA_RET) sp gp tp t0 t1 t2 (wz 16) (wz n) (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RAA_RET) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros FR. unfold RAA_RET at 2.
  step. if_true. step. step. step. step. step. apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.

Lemma lor_hdr : forall r idx, 0 <= idx < 32 -> 0 <= r -> Z.lor (r * 32) idx = idx + 32 * r.
Proof.
  intros r idx Hi Hr.
  assert (D : Z.land (r * 32) idx = 0).
  { apply Z.bits_inj'. intros i Hi0. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 5) as [L|L].
    - change 32 with (2^5). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite andb_false_iff. right.
      destruct (Z.eq_dec idx 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact D. pose proof (Z.add_nocarry_lxor _ _ D). lia.
Qed.

Lemma le1_wz : forall z, le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.
End CEIL_WRAP_2.

Local Ltac mem_after_store_opt ::= idtac.

Ltac restore_mem E :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      replace (write_to_mem m a bs) with m;
      [| symmetry; replace a with (wa E) by (unfold wa; f_equal; lia);
         apply write_to_mem_same; [lia| cbn [length]; rewrite ?length_le4; lia|] ]
  end.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.

Definition raa_fin_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR rao (wz (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rao) fc None m (seg_rom rsegs).

Lemma raa_fin_walk : forall (sp gp tp t0 t1 a1 a3 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 : word) F fc m
   (junk : list byte) (s1o s0o rao : word) (n P B EE QQ stride res b3 off16 idx : Z),
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
  bv_unsigned a0 = P -> 0 < P -> P mod 16 = 0 -> P <= EE + 4 ->
  rw_cells rsegs m (bv_unsigned a0 + -4) [C1 (b8 0); C1 (b8 b3); C2 (wz off16)] ->
  0 <= b3 < 256 -> 0 <= idx < 32 -> idx = Z.land b3 31 -> 0 <= stride ->
  EE = B + 16 + stride * (idx + 1) - 4 -> 0 <= B -> QQ = P + n -> res = EE - QQ ->
  0 <= n -> 0 <= res < 2^31 -> EE + 4 <= alloc_ceiling ->
  b3 = idx + 32 * Z.min res 5 ->
  (0 < res -> res <> 5 -> rw_cells rsegs m QQ [C1 (b8 0)]) ->
  (5 <= res -> rw_cells rsegs m (EE + -5) [C1 (b8 0); C4 (wz res)]) ->

  m (wa (P - 3)) = Some (b8 b3) ->
  (0 < res -> m (wa (EE - res)) = Some (b8 0)) ->
  (5 <= res -> m (wa (EE - 5)) = Some (b8 0)) ->
  (5 <= res -> forall i, (i < 4)%nat -> m (wa (EE - 4 + Z.of_nat i)) = nth_error (le4 (wz res)) i) ->
  evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
      (MS (mkR (wz RAA_RET) sp gp tp t0 t1 (Z_to_bv 64 (0 + - bv_unsigned a0)) (wz 16) (wz n)
               a0 a1 (wz n) a3 (wz B) a5 (Z_to_bv 64 stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa9310) fc None m (seg_rom rsegs)).
Proof.
  intros until idx. intros FR CSP SPH HP P0 AL PEE HDR B3 IDX HIDX STR0 HEE HB0 HQQ HRES Hn RES EEH HB3 TZ T5 O3 OZ O5 O4.
  pose_ceil.
  assert (STR : 0 <= stride * (idx + 1) <= EE) by nia.
  assert (ONE1 : forall (a : Z) (b : byte), m (wa a) = Some b -> forall i, (i < length [b])%nat -> m (wa (a + Z.of_nat i)) = nth_error [b] i).
  { intros a b Hb i Hi. destruct i; [rewrite Z.add_0_r; exact Hb| cbn in Hi; lia]. }

  st1. st1. st1. st1. st1. st1.
  replace (Z.land 15 (bv_unsigned (Z_to_bv 64 (0 + - bv_unsigned a0)))) with 0.
  2:{ rewrite HP. rewrite unsigned_lit_wrap by lia. change 15 with (2^4 - 1). rewrite zb_land_mask_l by lia. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^4) with 16. clear -AL P0. Z.div_mod_to_equations. lia. }
  replace (B + 16 + stride * (idx + 1) + -4) with EE by lia.
  replace (B + 16 + stride * (idx + 1)) with (EE + 4) by lia.
  st1. if_cases K13; zify_cond K13. 2:{ exfalso. rewrite ?wz_unsigned in K13 by lia. lia. }

  st1. st1. rewrite <- HP in HQQ. replace (n + bv_unsigned a0) with QQ by lia.
  replace (bv_swrap 32 (EE - QQ)) with res. 2:{ rewrite <- HRES. symmetry. rewrite swrap32_eq'. rewrite Z.mod_small; lia. }
  st1. if_cases K14; zify_cond K14.
  -
    rewrite ?wz_unsigned in K14 by lia.

    st1. st1. st1. st1.
    rewrite (Z.shiftl_mul_pow2 res 5) by lia. change (2^5) with 32. rewrite <- HIDX.
    replace (bv_unsigned (Z_to_bv 64 (res * 32))) with (res * 32) by (symmetry; apply unsigned_lit; lia).
    replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
    replace (Z.lor (res * 32) idx) with b3 by (rewrite HB3, K14, Z.mul_0_l, Z.lor_0_l; lia).
    st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }

    st1. st1. st1. st1. st1. st1.
    unfold raa_fin_post. finish.
  -
    rewrite ?wz_unsigned in K14 by lia.
    st1. replace (bv_swrap 32 (EE - QQ)) with res by (rewrite <- HRES; symmetry; rewrite swrap32_eq'; rewrite Z.mod_small; lia).
    st1. st1. st1.
    replace (bv_swrap 32 (0 - res)) with (- res) by (symmetry; rewrite swrap32_eq'; rewrite Z.mod_small; lia).
    destruct (Z.eq_dec res 5) as [R5|R5].
    +
      specialize (T5 ltac:(lia)). clear TZ.
      replace (EE + - res) with (EE + -5) by lia.
      st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
      st1. if_cases K15; zify_cond K15. { exfalso. rewrite signed_wz_small in K15 by lia. lia. }

      st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
      st1. restore_mem (EE - 4). 2:{ exact (O4 ltac:(lia)). }
      st1.

      st1. st1. st1. st1. rewrite <- HIDX.
      replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
      replace (Z.lor 160 idx) with b3 by (rewrite HB3, R5; change 160 with (5 * 32); rewrite lor_hdr by lia; lia).
      st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
      st1. st1. st1. st1. st1. st1.
      unfold raa_fin_post. finish.
    + replace (EE + - res) with QQ by lia.
      specialize (TZ ltac:(lia) R5).
      destruct (Z_lt_le_dec res 5) as [R4|R6].
      *
        clear T5.
        st1. rewrite le1_wz. restore_mem (EE - res). 2:{ exact (ONE1 _ _ (OZ ltac:(lia))). }
        st1. if_cases K15; zify_cond K15. 2:{ exfalso. rewrite signed_wz_small in K15 by lia. lia. }

        st1. st1. st1. st1. st1. rewrite <- HIDX.
        rewrite (Z.shiftl_mul_pow2 res 5) by lia. change (2^5) with 32.
        replace (bv_unsigned (Z_to_bv 64 (res * 32))) with (res * 32) by (symmetry; apply unsigned_lit; lia).
        replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
        replace (Z.lor (res * 32) idx) with b3 by (rewrite HB3; rewrite lor_hdr by lia; lia).
        st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
        st1. st1. st1. st1. st1. st1.
        unfold raa_fin_post. finish.
      *
        specialize (T5 R6).
        st1. rewrite le1_wz. restore_mem (EE - res). 2:{ exact (ONE1 _ _ (OZ ltac:(lia))). }
        st1. if_cases K15; zify_cond K15. { exfalso. rewrite signed_wz_small in K15 by lia. lia. }
        st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
        st1. restore_mem (EE - 4). 2:{ exact (O4 ltac:(lia)). }
        st1.
        st1. st1. st1. st1. rewrite <- HIDX.
        replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
        replace (Z.lor 160 idx) with b3 by (rewrite HB3; replace (res `min` 5) with 5 by lia; change 160 with (5 * 32); rewrite lor_hdr by lia; lia).
        st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
        st1. st1. st1. st1. st1. st1.
        unfold raa_fin_post. finish.
Qed.

Lemma raa_tail_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
   (junk : list byte) (s1o s0o rao : word)
   (n P G B AR EE QQ stride res : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
  bv_unsigned a0 = P -> 0 < P -> P mod 16 = 0 -> 16 * off16 + 16 <= P ->
  B = P - 16 * off16 - 16 -> AR = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  rw_cells rsegs m (bv_unsigned a0 + -4) [C1 (b8 0); C1 (b8 b3); C2 (wz off16)] ->
  ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes rsegs m (wa AR) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63 /\ last_idx = 0 /\ maplen <> 0) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
  EE = B + 16 + stride * (idx + 1) - 4 -> QQ = P + n -> res = EE - QQ ->
  0 <= n -> 0 <= res < 2^31 -> EE + 4 <= alloc_ceiling -> P <= EE + 4 ->
  b3 = idx + 32 * Z.min res 5 ->
  (0 < res -> res <> 5 -> rw_cells rsegs m QQ [C1 (b8 0)]) ->
  (5 <= res -> rw_cells rsegs m (EE + -5) [C1 (b8 0); C4 (wz res)]) ->
  m (wa (P - 3)) = Some (b8 b3) ->
  (0 < res -> m (wa (EE - res)) = Some (b8 0)) ->
  (5 <= res -> m (wa (EE - 5)) = Some (b8 0)) ->
  (5 <= res -> forall i, (i < 4)%nat -> m (wa (EE - 4 + Z.of_nat i)) = nth_error (le4 (wz res)) i) ->
  evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
      (MS (mkR (wz RAA_RET) sp gp tp t0 t1 t2 (wz 16) (wz n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RAA_RET) fc None m (seg_rom rsegs)).
Proof.
  intros until next. intros idx mword FR CSP SPH HP P0 AL PLO HB HA GLO GHI HDR RG MM RA RC RS B3 O16 AV FRD SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml HST HEE HQQ HRES Hn RES EEH PEE HB3 TZ T5 O3 OZ O5 O4. unfold RAA_RET at 2.
  pose proof CSP as CSP'. pose proof EEH as EEH'. pose_ceil.
  assert (PHI : P + 16 <= 2^64) by nia.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  pose proof (size_class_range sc) as SZR.
  assert (STR : 0 <= stride).
  { rewrite HST. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:E.
    - apply andb_prop in E as [_ E]. destruct (maplen =? 0) eqn:M0; [discriminate|]. apply Z.eqb_neq in M0. lia.
    - destruct (Z_lt_le_dec sc 48); [specialize (SZR ltac:(lia)); lia|].
      destruct (Hsc63 ltac:(lia)) as (-> & E1 & E2). rewrite E1 in E. cbn in E. destruct (maplen =? 0) eqn:M0; [|discriminate]. apply Z.eqb_eq in M0. lia. }

  st1. if_cases K0; zify_cond K0. { exfalso. lia. }

  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }

  st1. st1. st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1. clear RG'.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. fold idx. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }

  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

  st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (MW3 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  assert (MW4 : mword - mword mod 4096 = 4096 * maplen).
  { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. lia. }

  assert (FIN : forall (t0' t1' a1' a3' a5' t3' t4' t5' t6' : word) (m' : word -> option byte),
    m' = m ->
    evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
      (MS (mkR (wz RAA_RET) sp gp tp t0' t1' (Z_to_bv 64 (0 + - bv_unsigned a0)) (wz 16) (wz n)
               a0 a1' (wz n) a3' (wz B) a5' (Z_to_bv 64 stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0xa9310) fc None m' (seg_rom rsegs))).
  { intros t0' t1' a1' a3' a5' t3' t4' t5' t6' m' ->.
    eapply (raa_fin_walk sp gp tp t0' t1' a1' a3' a5' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' a0 F fc m junk s1o s0o rao
              n P B EE QQ stride res b3 off16 idx); try eassumption; try lia; try reflexivity. }
  st1. st1. st1. st1. rewrite MW2. st1. st1. st1. st1. if_cases K8; zify_cond K8.
  -
    destruct (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)) as (Hsc63' & HLI0 & HML0).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }

    st1. rewrite MW3. st1. st1. if_cases K10; zify_cond K10. { exfalso. rewrite ?wz_unsigned in K10 by lia. lia. }

    st1. st1. st1. if_cases K11; zify_cond K11.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K11 by lia. change (2^8) with 256 in K11. change 18446744073709551615 with (Z.ones 64) in K11.
        rewrite Z.land_ones, ?wz_unsigned in K11 by lia. rewrite Z.mod_small in K11 by lia. specialize (Hml HML0). lia. }

    st1. if_cases K12; zify_cond K12. 2:{ exfalso. rewrite ?wz_unsigned in K12 by lia. lia. }

    st1. st1. rewrite land_pgmask by lia. rewrite MW4. st1. st1.
    assert (HSTR : stride = 4096 * maplen - 16). { rewrite HST, HLI0. cbn [Z.eqb andb]. destruct (Z.eqb_spec maplen 0); [lia| cbn; lia]. }
    replace (4096 * maplen + -16) with stride by lia. apply FIN. reflexivity.
  -
    assert (SC48 : sc < 48) by (rewrite ?wz_unsigned in K8 by lia; lia).
    specialize (RS SC48). specialize (Hsc SC48). specialize (SZR ltac:(lia)).

    st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
    assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (123688 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (123688 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    st1. try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }

    st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1.

    st1. rewrite MW3. st1. st1. if_cases K12; zify_cond K12.
    +
      rewrite ?wz_unsigned in K12 by lia.
      assert (HSTR : stride = 16 * size_class sc). { rewrite HST, K12. cbn [Z.eqb negb andb]. rewrite andb_false_r. reflexivity. }

      st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. replace (size_class sc * 16) with stride by lia.
      apply FIN. reflexivity.
    +
      rewrite ?wz_unsigned in K12 by lia.
      st1. st1. st1. if_cases K13; zify_cond K13.
      2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K13 by lia. change (2^8) with 256 in K13. change 18446744073709551615 with (Z.ones 64) in K13.
          rewrite Z.land_ones, ?wz_unsigned in K13 by lia. rewrite Z.mod_small in K13 by lia. specialize (Hml K12). lia. }

      st1. if_cases K14; zify_cond K14.
      *
        rewrite ?wz_unsigned in K14 by lia.
        st1. st1. rewrite land_pgmask by lia. rewrite MW4. st1. st1.
        assert (HSTR : stride = 4096 * maplen - 16). { rewrite HST, K14. cbn [Z.eqb andb]. destruct (Z.eqb_spec maplen 0); [lia| cbn; lia]. }
        replace (4096 * maplen + -16) with stride by lia. apply FIN. reflexivity.
      * rewrite ?wz_unsigned in K14 by lia.
        assert (HSTR : stride = 16 * size_class sc). { rewrite HST. destruct (Z.eqb_spec last_idx 0); [lia|]. reflexivity. }
        st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
        rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. replace (size_class sc * 16) with stride by lia.
        apply FIN. reflexivity.
Qed.
End CEIL_WRAP_3.

