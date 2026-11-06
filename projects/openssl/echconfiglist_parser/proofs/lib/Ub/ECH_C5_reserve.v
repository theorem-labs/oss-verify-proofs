(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_malloc ECH_C1_realloc ECH_C5_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma div5_magic : forall x, 0 <= x < 2^31 -> (x * 1717986919) / 2^33 = x / 5.
Proof.
  intros x Hx. set (q := x / 5). set (r := x mod 5).
  assert (E : x = 5 * q + r) by (subst q r; apply Z.div_mod; lia).
  assert (R : 0 <= r < 5) by (subst r; apply Z.mod_pos_bound; lia).
  assert (Q : 0 <= q <= x) by (subst q; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  replace (x * 1717986919) with (q * 2^33 + (3 * q + r * 1717986919)) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (3 * q + r * 1717986919)) by lia. lia.
Qed.
Lemma lxor_ones31 : forall x, 0 <= x < 2^31 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof.
  intros x Hx. pose proof (Z.add_lxor_2land x 2147483647) as E.
  change 2147483647 with (Z.ones 31) in E |- *. rewrite Z.land_ones, Z.mod_small in E by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma srl_check : forall cap, 0 <= cap < 2^20 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 ((cap + -268435456) mod 18446744073709551616)) 29) = 7.
Proof.
  intros cap H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296.
  rewrite Z.shiftr_div_pow2 by lia.
  replace ((cap + -268435456) mod 18446744073709551616) with (cap + -268435456 + 18446744073709551616).
  2:{ rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
  replace ((cap + -268435456 + 18446744073709551616) mod 4294967296) with (cap + 4026531840).
  2:{ symmetry. rewrite <- (Z.mod_add _ (-4294967295)) by lia. rewrite Z.mod_small by lia. lia. }
  pose proof (Z.div_le_lower_bound (cap + 4026531840) (2^29) 7 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (cap + 4026531840) (2^29) 8 ltac:(lia) ltac:(lia)).
  replace ((cap + 4026531840) / 2 ^ 29) with 7 by lia. reflexivity.
Qed.
Lemma sk_grow_ge : forall cap, 4 <= cap -> cap + 1 <= sk_grow cap <= 2 * cap.
Proof. intros cap H. unfold sk_grow. split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]. Qed.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition SK_FILE : Z := 0x2a3a6.
  Definition SR_RA1 : Z := 0xe8714.    (* [comment removed for export] *)
  Definition SR_RA2 : Z := 0xe8778.    (* [comment removed for export] *)
  Definition SR_A3 : Z := 0x2a227.     (* [comment removed for export] *)

  Lemma sk_hdr_size : forall K pad, cells_size (sk_hdr_cells K pad) = 56%nat.
  Proof. reflexivity. Qed.
  Local Ltac prep HDR := unfold sk_hdr_cells, wz in HDR; pose proof (rw_cells_bound _ _ _ _ HDR) as HB; cbn [cells_size csize Nat.add] in HB.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_segB :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo ->
      0 <= sk_num K -> sk_num K + 1 <= sk_cap K -> 4 <= sk_cap K <= 2^20 -> sk_data K <> 0 -> 0 <= sk_data K < 2^64 ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists t0' a1' a3' a4' a5' m1,
          ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' (Z_to_bv 64 0) a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp)
          /\ rw_cells usegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_sk_reserve) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros AL HDR POS BL NN ROOM CAP DNZ DR ST LO MI. unfold P_sk_reserve. prep HDR. unfold SK_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    do 8 step. step. ubal_by AL. step. if_lit.
    st1. rewrite sx32_wz by lia. unfold wz.
    zstep. zstep. zstep. zstep. rewrite ?swrap32_small by lia.
    step. ub_dead.                                   (* [comment removed for export] *)
    zstep. rewrite ?swrap32_small by lia.            (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [| kill K0]. clear K0.   (* [comment removed for export] *)
    zstep. zstep. rewrite ?swrap32_small by lia.     (* [comment removed for export] *)
    step. ub_dead.                                   (* [comment removed for export] *)
    zstep. rewrite ?swrap32_small by lia.            (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    assert (FIN : forall na (a0x a3x a4x : word), na = Z.max (sk_num K + 1) 4 ->
      evt usegs (fun ms' => exists t0' a1' a3' a4' a5' m1,
          ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' (Z_to_bv 64 0) a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp)
          /\ rw_cells usegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) a0x (Z_to_bv 64 1) (Z_to_bv 64 0)
                 a3x a4x a5 a6 a7 (Z_to_bv 64 na) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe86e0) fc None m0 (seg_rom usegs))).
    { intros na a0x a3x a4x NA. st1. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
      st1. rewrite sx32_wz by lia. unfold wz. step. if_lit.
      step. if_cases K2; zify_cond K2; [| kill K2]. clear K2.
      do 8 step. release_frame FR ST (bv_unsigned sp). finish. }
    cbv delta [mkR] in FIN.
    step. if_cases K1; zify_cond K1.
    - apply FIN. revert K1. rewrite ?signed_lit by lia. lia.
    - step. apply FIN. revert K1. rewrite ?signed_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_segA :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo ->
      sk_num K = 0 -> sk_cap K = 0 -> sk_data K = 0 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists t0' a4' m1 j,
          ms' = MS (mkR (Z_to_bv 64 SR_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 194) a4' a5 a6 a7
                       (Z_to_bv 64 4) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_calloc) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells usegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra)
          /\ rw_cells usegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_sk_reserve) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros AL HDR POS BL N0 C0 D0 ST CEIL LO MI. unfold P_sk_reserve, P_CRYPTO_calloc, SR_RA1, SK_FILE. prep HDR. unfold SK_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    rewrite N0, D0 in HDR.
    carve_frame 48%nat ST.
    do 8 step. step. ubal_by AL. step. if_lit.
    st1. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    zstep. zstep. zstep. zstep.
    step. try if_lit. try ub_dead.                          (* [comment removed for export] *)
    zstep. step. try if_lit. try (if_cases K0; zify_cond K0; [| kill K0]; clear K0).
    zstep. zstep. step. try if_lit. try ub_dead.            (* [comment removed for export] *)
    zstep. step. step. try if_lit. try (if_cases K1; zify_cond K1; [kill K1|]; clear K1).
    step.
    st1. step. try if_lit. try if_true.                      (* [comment removed for export] *)
    do 6 step.
    finish. all: try exact FR. all: unfold sk_hdr_cells, wz; rewrite ?N0, ?D0; exact HDR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_segC :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo ->
      sk_num K = sk_cap K -> 4 <= sk_cap K <= SK_CAP_MAX -> 0 < sk_data K < 2^64 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 SR_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 (sk_data K)) (Z_to_bv 64 (sk_grow (sk_cap K))) (Z_to_bv 64 8) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 212)
                       a5 a6 a7
                       (Z_to_bv 64 (sk_cap K + 1)) (Z_to_bv 64 (sk_grow (sk_cap K))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_realloc_array) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells usegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra)
          /\ rw_cells usegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_sk_reserve) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros AL HDR POS BL FULL CAP DR ST CEIL LO MI. unfold P_sk_reserve, P_CRYPTO_realloc_array, SR_RA2, SK_FILE, SK_CAP_MAX in *. prep HDR. unfold SK_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    rewrite FULL in HDR.
    carve_frame 48%nat ST.
    do 8 step. step. ubal_by AL. step. if_lit.
    st1. rewrite sx32_wz by lia. unfold wz.
    zstep. zstep. zstep. zstep. rewrite ?swrap32_small by lia.
    step. ub_dead.
    zstep. rewrite ?swrap32_small by lia.
    step. if_cases K0; zify_cond K0; [| kill K0]. clear K0.
    zstep. zstep. rewrite ?swrap32_small by lia.
    step. ub_dead.
    zstep. rewrite ?swrap32_small by lia.
    step. step. if_cases K1; zify_cond K1; [| kill K1]. clear K1.     (* [comment removed for export] *)
    st1. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.      (* [comment removed for export] *)
    st1. rewrite sx32_wz by lia. unfold wz. step. if_lit.             (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.            (* [comment removed for export] *)
    do 5 step.
    (* [comment removed for export] *)
    zstep. zstep. rewrite srl_check by lia.
    step. try if_lit.                                                 (* [comment removed for export] *)
    assert (X8 : 0 <= sk_cap K * 8 < 2^24) by lia.
    pose proof (div5_magic (sk_cap K * 8) ltac:(lia)) as DM.
    assert (PM : 0 <= sk_cap K * 8 * 1717986919 < 2^55) by lia.
    zstep. rewrite (Z.shiftl_mul_pow2 (sk_cap K) 3) by lia. change (2^3) with 8. rewrite (swrap32_small (sk_cap K * 8)) by lia.
    zstep.
    zstep. rewrite (Z.shiftr_div_pow2 _ 63) by lia. rewrite (Z.div_small _ (2^63)) by lia.
    zstep. rewrite signed_lit by lia. rewrite (Z.shiftr_div_pow2 _ 33), DM by lia.
    pose proof (sk_grow_ge (sk_cap K) ltac:(lia)) as GG. unfold sk_grow in GG |- *.
    zstep. rewrite ?Z.add_0_r.
    step. if_cases K3; zify_cond K3; [kill K3|]. clear K3.
    do 6 step.
    finish. all: try exact FR. all: unfold sk_hdr_cells, wz; rewrite ?FULL; exact HDR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sr_segA2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a D : Z) (K : skrep) (pad j : list byte),
      0 < D < 2^64 -> 0 < a -> (a + 56 <= D \/ D + 32 <= a) -> a + 56 <= bv_unsigned sp + -48 ->
      rw_cells usegs m a (sk_hdr_cells K pad) ->
      rw_cells usegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(a, a + 56)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 a (sk_hdr_cells (mkSK (sk_elems K) D 4 (sk_sorted K) (sk_comp K) (sk_cmp_thunk K) (sk_free_thunk K) (sk_copy_thunk K) (sk_id K) (sk_did K)) pad))
        (MS (mkR (Z_to_bv 64 SR_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 4) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 SR_RA1)) fc None m (seg_rom usegs)).
  Proof.
    intros until j. intros HD POS DJ HS HDR FR MI. unfold SR_RA1.
    replace (ret_pc (Z_to_bv 64 0xe8714)) with (Z_to_bv 64 0xe8714) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. prep HDR. unfold cm_frame in FR.
    pose proof (munch_refl [(a, a + 56)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    st1. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    st1. do 9 step. finish.
  Qed.

  Lemma sr_segC2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a D cap' : Z) (K : skrep) (pad j : list byte),
      0 < D < 2^64 -> 0 < a -> 0 <= cap' < 2^31 -> (a + 56 <= D \/ D + 8 * cap' <= a) -> 8 <= 8 * cap' -> a + 56 <= bv_unsigned sp + -48 ->
      rw_cells usegs m a (sk_hdr_cells K pad) ->
      rw_cells usegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(a, a + 56)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 a (sk_hdr_cells (mkSK (sk_elems K) D cap' (sk_sorted K) (sk_comp K) (sk_cmp_thunk K) (sk_free_thunk K) (sk_copy_thunk K) (sk_id K) (sk_did K)) pad))
        (MS (mkR (Z_to_bv 64 SR_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                 s2x (Z_to_bv 64 cap') s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 SR_RA2)) fc None m (seg_rom usegs)).
  Proof.
    intros until j. intros HD POS HC DJ C8P HS HDR FR MI. unfold SR_RA2.
    replace (ret_pc (Z_to_bv 64 0xe8778)) with (Z_to_bv 64 0xe8778) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. prep HDR. unfold cm_frame in FR.
    pose proof (munch_refl [(a, a + 56)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    st1. st1. do 8 step. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.
  Hypothesis HRE : realloc_sr_stmt H.

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport usegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  Lemma u64arr_nil : forall m A, 0 <= A <= 2^64 -> u64arr usegs m A [].
  Proof.
    intros m A HA. split.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  Qed.
  Lemma u64arr_of_CB : forall m A ws, rw_cells usegs m A [CB (8 * length ws)%nat (u64s ws)] -> u64arr usegs m A ws.
  Proof.
    intros m A ws [[WF B] W]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. cbn [cells_size csize Nat.add] in W.
    split; [exact B|]. replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * length ws + 0)) by lia. exact W.
  Qed.
  Lemma MEMFLAG_xnil : forall LB SP m m1 v, xpres LB SP [] m m1 -> MEMFLAG m v -> MEMFLAG m1 v.
  Proof.
    intros LB SP m m1 v XP (fb & MF & E1 & E2). exists fb. split; [| split; [exact E1| exact E2]].
    eapply xpres_rw_cells'; [exact XP| exact MF| | constructor]. right; left. unfold A_mem_inited, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_cons_fresh : forall LB SP X m m' p D n,
    xpres LB SP X m m' -> (forall a, D <= a < D + n -> rin_ivs X a) -> xpres ((p, D, n) :: LB) SP X m m'.
  Proof.
    intros LB SP X m m' p D n XP HX. eapply xpres_reLB; [exact XP|].
    intros a Ha C NX. split; [| exact NX].
    destruct C as [C|[C|(b & [<-|Hb] & R)]]; [left; exact C| right; left; exact C| | right; right; exists b; split; [exact Hb| exact R]].
    exfalso. apply NX. apply HX. cbn [blk_addr blk_size fst snd] in R. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma SKobj_rehdr_gen : forall LB m m' a K pad W,
    SKobj LB m a K -> length pad = 4%nat -> rw_cells usegs m' a (sk_hdr_cells K pad) ->
    munch W m m' -> wmono usegs m m' -> (sk_cap K = 0 \/ disjoint_from W (sk_data K) (8 * sk_cap K)) ->
    SKobj LB m' a K.
  Proof.
    intros LB m m' a K pad W SO PL HDR MU WM DJ.
    destruct SO as (_ & POS & IN & NC & CAP & SRT & EL & DAT). unfold SKobj, sk_num in *.
    split; [exists pad; split; [exact PL| exact HDR]|]. split; [exact POS|]. split; [exact IN|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [left; exact D0| right].
    destruct DJ as [DJ|DJ]; [lia|]. unfold zlength in *.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split.
    - eapply u64arr_transport; [exact AR| exact MU| exact WM|]. rewrite length_map. eapply disjoint_from_mono; [exact DJ| lia].
    - exists junk. eapply rw_cells_transport; [exact JK| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact DJ| lia| lia| lia].
  Qed.


  Lemma skreserve_spec : skreserve_stmt H.
  Proof.
    unfold skreserve_stmt. intros until errv.
    intros A0 A1 A2 SO CAPX HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP (MF & IM & GM). subst a0 a1 a2.
    unfold SKRESERVE_STACK, FR_sk_reserve, CARRAY_STACK, CREALLOC_ARRAY_STACK, CZALLOC_STACK, CREALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_array,
      FR_CRYPTO_zalloc, FR_CRYPTO_realloc, FR_CRYPTO_malloc, RMALLOC_STACK, RREALLOC_STACK in LO. unfold RMALLOC_STACK in LO.
    unfold SKPUSH_COST, SK_CAP_MAX in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof SO as SO'. destruct SO' as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    pose proof (HB _ HIN) as ABL. cbn [blk_addr blk_size fst snd] in ABL. unfold SK_SIZE in ABL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP HIN) as (_ & AL16 & _ & _ & AIMG). cbn [blk_addr blk_size fst snd] in AIMG, AL16. unfold SK_SIZE in AIMG.
    assert (AL8 : a mod 8 = 0) by (clear - AL16; lia).   (* [comment removed for export] *)
    pose proof (sk_grow_ge (sk_cap K)) as GG.
    destruct DAT as [[C0 D0]|(D4 & DP & DDJ & DIN & AR & junk & JK)].
    - (* [comment removed for export] *)
      assert (N0 : sk_num K = 0) by lia.
      eapply (sr_evt_krel H HH); [exact KREL| eapply sr_segA with (lo := lo); [exact AL8| exact HDR| exact POS| unfold SK_SIZE; lia| exact N0| exact C0| exact D0| exact ST| exact CEIL| lia| exact MI]|].
      intros ms1 (t0' & a4' & m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
      assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
      { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
      pose proof (ccalloc_spec H HH) as CC. unfold ccalloc_stmt, czalloc_stmt_gen in CC.
      eapply (sr_seq H HH).
      { eapply CC with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 4) (size := 8); rewrite ?unsigned_lit by lia; try reflexivity.
        all: try (cbn; lia).
        all: try first [exact KREL| exact ST1| exact CEIL| exact MI1| exact TP].
        all: lazymatch goal with
             | |- _ /\ _ => split; [reflexivity| lia]
             | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]
             | |- lb_big _ + _ <= _ => rewrite big1_small by (unfold BIGB; lia); pose proof (big1_range (8 * sk_grow (sk_cap K))); lia
             | |- lb_bytes _ + _ <= _ => unfold sk_grow in BUD; rewrite C0 in BUD; cbn in BUD; lia
             | |- _ <= bv_unsigned _ + _ - _ => unfold CARRAY_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia
             | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; constructor; [cbn; lia| constructor]
             | |- rw_cells _ _ _ _ => subst tp; rewrite errno_RATP in *; errno_across ERR MU1 WM1
             | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
             | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
             | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
             end. }
      intros [ms2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & D & p' & s' &
                      -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & MF2 & IM2 & GM2).
      rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia. change (4 * 8) with 32 in BR, HEAP2, BLK.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in HDR1; rewrite ?sk_hdr_size in *;
        [| eapply rclient_range_block; [exact HIN| cbn; lia| cbn; unfold SK_SIZE; lia]| unfold memflag_foot, A_mem_inited; constructor; [clear - AIMG; cbn; lia| constructor]].
      pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp + -48) a 56 HEAP2
                    ltac:(eapply rclient_range_block; [exact HIN| cbn; lia| cbn; unfold SK_SIZE; lia]) ltac:(lia) ltac:(lia)) as SEP.
      eapply (sr_evt_krel H HH); [exact KREL2| eapply sr_segA2; [lia| exact POS| exact SEP| lia| exact HDR1| exact FR1| exact MI2]|].
      intros ms3 (m3 & -> & MU3 & WM3 & MI3 & HDR3).
      apply (sr_done H HH). unfold skreserve_post. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, s', ((p', D, 32) :: LB).
      exists (sk_after_reserve K D 4 p'), D, 4, p'.
      split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|].
      split. { apply (rw_cells_transport usegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
               apply (stk_transport_disjoint usegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
               unfold cm_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
      split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; lia]. }
      split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
      split; [reflexivity|].
      split. { right; left. cbn. split; [exact C0| split; reflexivity]. }
      split. { unfold sk_num. cbn. unfold sk_num in N0. lia. }
      split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor].
               apply rclient_write_ok_cons. right; right. exists (sk_id K, a, SK_SIZE). cbn. unfold SK_SIZE. split; [exact HIN| lia]. }
      split.
      { unfold SKobj, sk_num. cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk sk_id sk_did sk_after_reserve].
        unfold sk_num in N0, NC.
        split; [exists pad; split; [exact PL| exact HDR3]|]. split; [exact POS|]. split; [right; exact HIN|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact EL|].
        right. split; [lia|]. split; [lia|]. split; [unfold SK_SIZE; lia|]. split; [left; reflexivity|]. split.
        - assert (E0 : sk_elems K = []) by (destruct (sk_elems K); [reflexivity| unfold zlength in N0; cbn [length] in N0; lia]).
          rewrite E0. cbn [map]. apply u64arr_nil. lia.
        - exists (zeros (Z.to_nat 32)). rewrite N0. replace (D + 8 * 0) with D by lia. change (Z.to_nat (8 * (4 - 0))) with (Z.to_nat 32).
          eapply rw_cells_transport; [exact BLK| exact MU3| exact WM3| cbn; lia]. }
      split.
      { unfold SK_foot. cbn [sk_cap sk_data sk_after_reserve Z.eqb]. unfold SK_SIZE.
        eapply xpres_trans.
        - apply xpres_cons_fresh; [| intros q Hq; apply rin_ivs_app; right; cbn; lia].
          eapply xpres_X_mono; [eapply xpres_trans; [exact XP1| eapply (xpres_weaken LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto]]|].
          intros q Hq; apply rin_ivs_app; left; exact Hq.
        - eapply xpres_of_munch_gen; [exact MU3| exact WM3|]. intros q Hq [HC HX]. rewrite rin_ivs_app in HX. cbn in HX |- *. clear - Hq HX. lia. }
      exists 1. split; [| destruct MF as (fb0 & _ & _ & V01); lia]. split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
      split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
      eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2].
    - pose proof (rw_cells_bound _ _ _ _ JK) as JB. cbn [cells_size csize Nat.add] in JB.
      pose proof (HB _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL.
      pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB. unfold sk_num, zlength in *.
      destruct (Z_lt_le_dec (Z.of_nat (length (sk_elems K))) (sk_cap K)) as [ROOM|FULL].
      + (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL| eapply sr_segB with (lo := lo);
          [exact AL8| exact HDR| exact POS| unfold SK_SIZE; lia| unfold sk_num, zlength; lia| unfold sk_num, zlength; lia| lia| lia| lia| exact ST| lia| exact MI]|].
        intros ms1 (t0' & a1' & a3' & a4' & a5' & m1 & -> & MU1 & WM1 & MI1 & ST1 & HDR1).
        apply (sr_done H HH). unfold skreserve_post. cbn [cfg_ms cfg_model].
        exists t0', t1, t2, a1', (Z_to_bv 64 0), a3', a4', a5', a6, a7, t3, t4, t5, t6, m1, errv, s, LB.
        exists (sk_after_reserve K (sk_data K) (sk_cap K) (sk_did K)), (sk_data K), (sk_cap K), (sk_did K).
        split; [reflexivity|]. split; [exact KREL|]. split; [apply (mpres_refl H HH)|]. split; [exact MI1|]. split; [exact ST1|].
        split. { subst tp. rewrite errno_RATP in ERR |- *. eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| unfold RERRNO; cbn; lia]. }
        split. { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
        split; [reflexivity|].
        split. { left. cbn. unfold sk_num, zlength. repeat split; lia. }
        split. { unfold sk_num, zlength. cbn. lia. }
        split. { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
        split.
        { destruct K as [el da ca so co ct ft cpt id did]. cbn in *.
          eapply (SKobj_rehdr_gen LB m m1); [exact SO| exact PL| exact HDR1| exact MU1| exact WM1| right; cbn; lia]. }
        split.
        { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
        exists v. split; [| lia]. split; [eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]|].
        split; [eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]|].
        eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM].
      + (* [comment removed for export] *)
        assert (FULLE : Z.of_nat (length (sk_elems K)) = sk_cap K) by lia.
        specialize (GG ltac:(lia)). destruct GG as [GG1 GG2].
        assert (GG3 : 5 * sk_grow (sk_cap K) <= sk_cap K * 8) by (unfold sk_grow; apply Z.mul_div_le; lia).
        eapply (sr_evt_krel H HH); [exact KREL| eapply sr_segC with (lo := lo);
          [exact AL8| exact HDR| exact POS| unfold SK_SIZE; lia| unfold sk_num, zlength; lia| unfold SK_CAP_MAX; lia| lia| exact ST| exact CEIL| lia| exact MI]|].
        intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
        apply (u64arr_transport usegs _ m m1 _ _ AR) in MU1 as AR1; [| exact WM1| rewrite length_map; cbn; lia].
        apply (rw_cells_transport usegs _ m m1 _ _ JK) in MU1 as JK1; [| exact WM1| cbn; lia].
        (* [comment removed for export] *)
        assert (JN : junk = []).
        { destruct JK as [[WF _] _]. cbn in WF. destruct junk; [reflexivity| cbn in WF; lia]. }
        subst junk.
        assert (OBS : bytes_at usegs m1 (sk_data K) (u64s (map wz (sk_elems K)))) by exact (proj1 AR1).
        pose proof (crealloc_array_spec H HH HRE) as CR. unfold crealloc_array_stmt, crealloc_stmt_gen in CR.
        eapply (sr_seq H HH).
        { eapply CR with (lo := lo) (B := B) (LB := LB) (s := s) (p := sk_did K) (A := sk_data K) (old := 8 * sk_cap K)
                           (num := sk_cap K * 8 / 5) (size := 8) (obs := u64s (map wz (sk_elems K)));
            rewrite ?unsigned_lit by lia; try reflexivity.
          all: try first [exact KREL| exact ST1| exact CEIL| exact MI1| exact TP| exact DIN| exact OBS].
          all: lazymatch goal with
               | |- 1 <= _ < RMMAP_THRESHOLD => unfold RMMAP_THRESHOLD; unfold sk_grow in *; lia
               | |- _ = _ /\ _ => split; [reflexivity| lia]
               | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; clear -LO CEIL SPR; lia| apply Forall_nil]
               | |- zlength _ = _ => unfold zlength; rewrite u64s_length, length_map; lia
               | |- lb_bytes _ + _ <= _ => unfold sk_grow in *; lia
               | |- Z.of_nat (length _) + 1 <= _ => exact BUDC
               | |- lb_big _ + _ <= _ => replace (sk_cap K * 8 / 5 * 8) with (8 * sk_grow (sk_cap K)) by (unfold sk_grow; lia); exact BUDB
               | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; clear -LO CEIL SPR SPB HCEILB; lia| apply Forall_nil]
               | |- rw_cells _ _ _ _ => subst tp; rewrite errno_RATP in *; errno_across ERR MU1 WM1
               | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
               | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
               | |- _ => unfold CREALLOC_ARRAY_STACK, CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, RREALLOC_STACK, RMALLOC_STACK; clear - LO CEIL SPR SPB HCEILB; lia
               end. }
        intros [ms2 mo2] PO. unfold crealloc_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A' & junk' & p' & s' &
                        -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & IM2 & GM2).
        rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia.
        set (g := sk_cap K * 8 / 5) in *.
        replace (g * 8) with (8 * g) in BR, HEAP2, BLK by lia.
        pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
        (* [comment removed for export] *)
        assert (HINR : In (sk_id K, a, SK_SIZE) (hs_lb_remove H (sk_did K) LB)).
        { apply (proj2 (proj2 (proj2 (lb_remove_exact H HH _ _ _ _ (HH_RHEAP_blocks_nodup H HH _ _ _ HP) DIN)) (sk_id K, a, SK_SIZE))).
          split; [exact HIN|]. cbn. intros E.
          pose proof (nodup_id_inj LB _ _ (HH_RHEAP_blocks_nodup H HH _ _ _ HP) HIN DIN E) as EE. injection EE as E1 E2. unfold SK_SIZE in *. lia. }
        assert (SUBR : forall b, In b (hs_lb_remove H (sk_did K) LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
        eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| constructor].
        eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in HDR1; rewrite ?sk_hdr_size in *;
          [| eapply rclient_range_block; [exact HINR| cbn; lia| cbn; unfold SK_SIZE; lia]| constructor].
        pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp + -48) a 56 HEAP2
                      ltac:(eapply rclient_range_block; [exact HINR| cbn; lia| cbn; unfold SK_SIZE; lia]) ltac:(lia) ltac:(lia)) as SEP.
        eapply (sr_evt_krel H HH); [exact KREL2| eapply sr_segC2; [lia| exact POS| lia| exact SEP| lia| lia| exact HDR1| exact FR1| exact MI2]|].
        intros ms3 (m3 & -> & MU3 & WM3 & MI3 & HDR3).
        apply (sr_done H HH). unfold skreserve_post. cbn [cfg_ms cfg_model].
        exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, s', ((p', A', 8 * g) :: hs_lb_remove H (sk_did K) LB).
        exists (sk_after_reserve K A' g p'), A', g, p'.
        split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|].
        split. { apply (rw_cells_transport usegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
                 apply (stk_transport_disjoint usegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
                 unfold cm_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
        split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; lia]. }
        split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
        split; [reflexivity|].
        split. { right; right. cbn. split; [lia|]. split; [unfold sk_num, zlength; lia|]. split; [reflexivity|].
                 eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply (lb_remove_perm H HH); [exact HP| exact DIN]. }
        split. { unfold sk_num, zlength. cbn. lia. }
        split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor].
                 apply rclient_write_ok_cons. right; right. exists (sk_id K, a, SK_SIZE). cbn. unfold SK_SIZE in *. split; [exact HINR| lia]. }
        split.
        { (* [comment removed for export] *)
          rewrite Z.min_l in BLK by lia. rewrite firstn_all2 in BLK by (rewrite u64s_length, length_map; lia).
          change (rw_cells usegs m2 A' ([CB (Z.to_nat (8 * sk_cap K)) (u64s (map wz (sk_elems K)))] ++ [CB (Z.to_nat (8 * g - 8 * sk_cap K)) junk'])) in BLK.
          apply (proj1 (rw_cells_app _ _ _ _ _)) in BLK. destruct BLK as [BK BJ]. cbn [cells_size csize Nat.add] in BJ.
          unfold SKobj, sk_num. cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk sk_id sk_did sk_after_reserve].
          split; [exists pad; split; [exact PL| exact HDR3]|]. split; [exact POS|]. split; [right; exact HINR|].
          unfold zlength. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact EL|].
          right. split; [lia|]. split; [lia|]. split; [unfold SK_SIZE; lia|]. split; [left; reflexivity|]. split.
          - eapply u64arr_transport; [| exact MU3| exact WM3| rewrite length_map; cbn; lia].
            apply u64arr_of_CB. replace (8 * length (map wz (sk_elems K)))%nat with (Z.to_nat (8 * sk_cap K)) by (rewrite length_map; lia). exact BK.
          - exists junk'. replace (A' + 8 * Z.of_nat (length (sk_elems K))) with (A' + Z.of_nat (Z.to_nat (8 * sk_cap K) + 0)) by lia.
            replace (Z.to_nat (8 * (g - Z.of_nat (length (sk_elems K))))) with (Z.to_nat (8 * g - 8 * sk_cap K)) by lia.
            eapply rw_cells_transport; [exact BJ| exact MU3| exact WM3| cbn; lia]. }
        split.
        { unfold SK_foot. cbn [sk_cap sk_data sk_after_reserve]. replace (g =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold SK_SIZE.
          apply xpres_cons_fresh; [| intros q Hq; apply rin_ivs_app; right; cbn; lia].
          eapply xpres_trans; [| eapply xpres_trans].
          - eapply xpres_of_munch; [exact MU1| exact WM1| |]. { constructor; [left; cbn; lia| constructor]. } intros b Hb. apply HB. apply SUBR. exact Hb.
          - eapply xpres_weaken; [exact XP2| lia| auto| intros q Hq; destruct Hq].
          - eapply xpres_of_munch_gen; [exact MU3| exact WM3|]. intros q Hq [HC HX]. rewrite rin_ivs_app in HX. cbn in HX |- *. clear - Hq HX. lia. }
        exists v. split; [| lia]. split.
        { eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia|].
          eapply MEMFLAG_xnil; [exact XP2|]. eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]. }
        split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
        eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2].
  Qed.
End W.
