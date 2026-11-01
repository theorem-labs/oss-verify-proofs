(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_G_kit2 Fz_ckit Fz_M_malloc Fz_env Fz_M_zalloc Th_mutex Fz_M_locknew Fz_G_CRYPTO_calloc Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_lhst.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import PLayout Th_mutex Th_mutex_init Th_cond.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tslia ::= wp_tslia.
(* [comment removed for export] *)
Local Ltac wp_out Ho SPL unf := cbn [app outside]; unf;
  repeat (split; [ first [ wp_na
                         | (clear - Ho SPL; first [ tauto | lia ])
                         | match goal with H : wp_box (aclient _ _ _ _) |- _ => unfold wp_box in H; lia end
                         | (repeat match goal with H : wp_box _ |- _ => unfold wp_box in H end; lia) ] |]); exact I.
(* [comment removed for export] *)
Local Ltac wg_T := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifT | |- _ => idtac end.
Local Ltac wg_F := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifF | |- _ => idtac end.
Local Ltac zstore := zstep; fix_lit_store.
Local Ltac wg_raw H := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => rewrite H; cbv iota end.
Local Ltac wg_at p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => unify p q | |- _ => fail "wgen: unexpected pc" end.

Definition e_ossl_decoder_cache_new : Z := 0x3155a0.
Definition SITE_ossl_decoder_cache_new_1 : Z := 0x3155e0.     (* [comment removed for export] *)
Definition SITE_ossl_decoder_cache_new_2 : Z := 0x3155f0.     (* [comment removed for export] *)
Definition SITE_ossl_decoder_cache_new_3 : Z := 0x315620.     (* [comment removed for export] *)
Definition SITE_ossl_decoder_cache_new_4 : Z := 0x315648.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (pad : list byte) (m1 : mem),
    ms = entry_st (Z_to_bv 64 SITE_ossl_decoder_cache_new_1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1
           (Z_to_bv 64 16) (Z_to_bv 64 0xa30e0) (Z_to_bv 64 775) a3 a4 a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc e_CRYPTO_malloc m1
    /\ stk asegs m1 lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m1 (bv_unsigned sp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m1 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]
    /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1.

Lemma ossl_decoder_cache_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3155a0) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    OnStk LoRoom LoHigh SpCap Untouched ShadowRO MemOk.
  unfold ossl_decoder_cache_new_s0_post, entry_st, e_CRYPTO_malloc, SITE_ossl_decoder_cache_new_1.
  pose proof (wmono_refl asegs m) as Wm.
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. change (bv_modulus 64) with (2 ^ 64) in SpRange.
  remember (bv_unsigned sp) as usp eqn:UspDef.
  pose proof (munch_refl [(usp + -48, usp)] m) as Mu.
  assert (ShFp : sh_fp [(usp + -48, usp)]) by sh_fp_lia.
  assert (UtFp : ut_fp [(usp + -48, usp)]) by ut_fp_lia.
  replace sp with (Z_to_bv 64 usp) by (subst usp; apply Z_to_bv_bv_unsigned).
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat OnStk.
  zstep. do 5 zstep. do 9 zstep.
  apply evt_done. exists (firstn 8 junk), m0. split; [reflexivity|].
  split; [exact OnStk|]. split; [exact FR|]. split; [exact ShadowRO|]. split; [exact Mu|]. split; [exact Wm|exact MemOk].
Qed.

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word)
    (v1 : Z) (jbr1_1 j1 : list byte) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = entry_st (Z_to_bv 64 SITE_ossl_decoder_cache_new_2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1)
        (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1
        F1 fc1 e_lock_new m
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_decoder_cache_new_s1_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (jbr1_1 j1 : list byte) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m v1 [CB 16 jbr1_1] ->
  acc asegs m v1 16 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 16 <= 2 ^ 47 ->
  v1 + 16 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 jbr1_1 j1 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x3155e0) fc1 None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 jbr1_1 j1 F1 fc1 m lo
    OnStk LoRoom LoHigh SpCap FrameCells ShadowRO V1Word Untouched V1Cells V1Acc V1Al V1High V1Cap V1Below MemOk.
  unfold ossl_decoder_cache_new_s1_post, entry_st, e_lock_new, SITE_ossl_decoder_cache_new_2.
  zstep. wg_F. zstep. zstep.
  apply evt_done. split; [reflexivity | exact ShadowRO].
Qed.

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word)
    (v1 v2 : Z) (j2 j1 : list byte) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (tail : list byte) (m1 : mem),
    ms = entry_st (Z_to_bv 64 SITE_ossl_decoder_cache_new_3) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1)
           (Z_to_bv 64 0x3156e0) (Z_to_bv 64 0x315864) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880))
           s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2 F2 fc2 e_OPENSSL_LH_new m1
    /\ rw_cells asegs m1 v1 [C8 (Z_to_bv 64 v2); CB 8 tail]
    /\ ro_cells asegs m1 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]
    /\ munch [(v1, v1 + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1.

Lemma ossl_decoder_cache_new_s2_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (j2 j1 : list byte) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 16 j2] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 16 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 16 <= 2 ^ 47 ->
  v1 + 16 <= lo ->
  (negb (bv_eqb (Z_to_bv 64 (Z.land v1 7)) (Z_to_bv 64 0))) = false ->
  (bv_eqb (Z_to_bv 64 v2) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 j2 j1 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x3155f0) fc2 None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 j2 j1 F2 fc2 m lo
    OnStk LoRoom LoHigh SpCap V1Cells FrameCells ShadowRO V1Word V2Word Untouched V1Acc V1Al V1High V1Cap V1Below AlignOk LockNonNull MemOk.
  unfold ossl_decoder_cache_new_s2_post, entry_st, e_OPENSSL_LH_new, SITE_ossl_decoder_cache_new_3.
  pose proof (munch_refl [(v1, v1 + 8)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  assert (UtFp : ut_fp [(v1, v1 + 8)]) by ut_fp_lia.
  assert (ShFp : sh_fp [(v1, v1 + 8)]) by sh_fp_lia.
  zstep. zstep. zstep. zstep. wg_F.
  zstep. zstep. wg_raw LockNonNull.
  do 5 zstep.
  apply evt_done. exists (skipn 8 j2), m0. split; [reflexivity|].
  split; [exact V1Cells|]. split; [exact ShadowRO|]. split; [exact Mu|]. split; [exact Wm|exact MemOk].
Qed.

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word)
    (v1 v2 v3 : Z) (j3 j1 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = entry_st (Z_to_bv 64 SITE_ossl_decoder_cache_new_4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1)
        (Z_to_bv 64 v3) (Z_to_bv 64 0x31707c) (Z_to_bv 64 0x31709c) (Z_to_bv 64 0x3170bc) (Z_to_bv 64 0x3170dc) b5_3 b6_3 b7_3
        (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3
        F3 fc3 e_OPENSSL_LH_set_thunks m
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_decoder_cache_new_s3_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (j3 j1 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); CB 8 j3] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 j3 j1 F3 fc3 lo m)
    (MS (mkR ra3 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
        F3 (Z_to_bv 64 0x315620) fc3 None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 j3 j1 F3 fc3 m lo
    OnStk LoRoom LoHigh SpCap V1Cells FrameCells ShadowRO V1Word V2Word V3Word Untouched MemOk.
  unfold ossl_decoder_cache_new_s3_post, entry_st, e_OPENSSL_LH_set_thunks, SITE_ossl_decoder_cache_new_4.
  do 9 zstep.
  apply evt_done. split; [reflexivity | exact ShadowRO].
Qed.

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s4_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word)
    (v1 v2 v4 : Z) (j3 j1 : list byte) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m1 : mem,
    ms = MS (mkR ra sp gp tp u0_4 u1_4 u2_4 s0 s1 (Z_to_bv 64 v1) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) b3_4 b4_4 b5_4 b6_4 b7_4
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (ret_pc ra) fc4 None m1 (seg_rom asegs)
    /\ rw_cells asegs m1 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4)]
    /\ ro_cells asegs m1 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]
    /\ stk asegs m1 lo (bv_unsigned sp)
    /\ munch [(v1 + 8, v1 + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1.

Lemma ossl_decoder_cache_new_s4_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v4 : Z) (j3 j1 : list byte) (F4 : bvmap 5 word) (fc4 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); CB 8 j3] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 16 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 16 <= 2 ^ 47 ->
  v1 + 16 <= lo ->
  (negb (bv_eqb (Z_to_bv 64 v4) (Z_to_bv 64 0))) = true ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s4_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v4 j3 j1 F4 fc4 lo m)
    (MS (mkR ra4 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v4) b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
        F4 (Z_to_bv 64 0x315648) fc4 None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v4 j3 j1 F4 fc4 m lo
    OnStk LoRoom LoHigh SpCap V1Cells FrameCells ShadowRO V1Word V2Word V4Word Untouched V1Acc V1Al V1High V1Cap V1Below TableNonNull MemOk.
  unfold ossl_decoder_cache_new_s4_post.
  assert (UtFp : ut_fp [(v1 + 8, v1 + 16)]) by ut_fp_lia.
  assert (ShFp : sh_fp [(v1 + 8, v1 + 16)]) by sh_fp_lia.
  pose proof (munch_refl [(v1 + 8, v1 + 16)] m) as Mu.
  pose proof (wmono_refl asegs m) as Wm.
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. change (bv_modulus 64) with (2 ^ 64) in SpRange.
  remember (bv_unsigned sp) as usp eqn:UspDef.
  replace sp with (Z_to_bv 64 usp) by (subst usp; apply Z_to_bv_bv_unsigned).
  do 4 zstep. zstep. wg_F.
  zstep. zstep. wg_raw TableNonNull.
  do 8 zstep.
  th_release FrameCells usp.
  apply evt_done. exists m0. split; [reflexivity|].
  split; [exact V1Cells|]. split; [exact ShadowRO|]. split; [exact OnStk|]. split; [exact Mu|]. split; [exact Wm|exact MemOk].
Qed.

Section ossl_decoder_cache_new_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CRYPTO_malloc : crypto_malloc_env_stmt RT.
Hypothesis C_lock_new : crypto_lock_new_env_stmt RT.
Hypothesis C_OPENSSL_LH_new : OPENSSL_LH_new_stmt RT.
Hypothesis C_OPENSSL_LH_set_thunks : OPENSSL_LH_set_thunks_keep_stmt RT.

Definition ossl_decoder_cache_new_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
    fdfs_only PMc ->
    mat_stable PMc ->
    tp = Z_to_bv 64 12205808 ->
    ART RT Σ m ->
    mem_inv asegs m ->
    call_ok RT Σ m sp lo ->
    lo + RT_STACK + 560 <= bv_unsigned sp ->
    cg_ctx (rt_cg RT Σ) e_ossl_decoder_cache_new (bv_unsigned ra :: outer) ->
    uw_chain m sp s0 outer ->
    cg_has (rt_cg RT Σ)
      [(SITE_ossl_decoder_cache_new_1, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_2, e_ossl_decoder_cache_new);
       (SITE_ossl_decoder_cache_new_3, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_4, e_ossl_decoder_cache_new);
       (SITE_ln_zalloc, e_lock_new); (SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new);
       (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
      [(SITE_ossl_decoder_cache_new_1, e_CRYPTO_malloc); (SITE_ossl_decoder_cache_new_2, e_lock_new);
       (SITE_ossl_decoder_cache_new_3, e_OPENSSL_LH_new); (SITE_ossl_decoder_cache_new_4, e_OPENSSL_LH_set_thunks);
       (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc);
       (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
    Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX ->
    mcost 16 + 1 + (mcost 104 + mcost 128) <= rt_credit RT Σ ->
    cl_env m lb canary ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_decoder_cache_new m)))
      (fun c => exists (Σ' : rts RT) (p lk q1 q2 : Z),
         ASTA RT Σ' PMc
           (fun ms => exists m' : mem,
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
              /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
              /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
              /\ cl_env m' (Z_to_bv 8 1) canary
              /\ rw_cells asegs m' p [C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 q1)] /\ acc asegs m' p 16
              /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ acc asegs m' lk 40
              /\ rw_cells asegs m' q1
                   [C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 0x315864); C8 (Z_to_bv 64 0x3156e0); C8 (Z_to_bv 64 0x31707c);
                    C8 (Z_to_bv 64 0x31709c); C8 (Z_to_bv 64 0x3170bc); C8 (Z_to_bv 64 0x3170dc); C4 (Z_to_bv 64 8);
                    C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256);
                    C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)] /\ acc asegs m' q1 104
              /\ rw_cells asegs m' q2 [CB 128 (repeat (Z_to_bv 8 0) 128)] /\ acc asegs m' q2 128) c
         /\ rt_live RT Σ' = (q2, 128) :: (q1, 104) :: (lk, 40) :: (p, 16) :: rt_live RT Σ
         /\ rt_frames RT Σ' = rt_frames RT Σ
         /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ' = rt_credit RT Σ - (mcost 16 + 1 + (mcost 104 + mcost 128))
         /\ 0 < p /\ p mod 16 = 0 /\ p + 16 < USTACK_TOP
         /\ 0 < lk /\ lk mod 16 = 0 /\ lk + 40 < USTACK_TOP
         /\ 0 < q1 /\ q1 mod 16 = 0 /\ q1 + 104 < USTACK_TOP
         /\ 0 < q2 /\ q2 mod 16 = 0 /\ q2 + 128 < USTACK_TOP
         /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_decoder_cache_new_cps : ossl_decoder_cache_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FdOnly MatSt TpIs Art0 Mi0 CallOk StkRoom Ctx0 Unw0 Graph FramesRoom LiveRoom CreditRoom Env0 T c Start Kont.
  destruct CallOk as (Stk0 & LoWin & LoRt & SpTop & SpAl).
  pose proof (af_sp0_win RT AF Σ m Art0) as Sp0Win. pose proof (af_sp0_range RT AF Σ m Art0) as Sp0Rng.
  assert (Costs : mcost 16 = 0 /\ mcost 104 = 0 /\ mcost 128 = 0) by (split; [|split]; reflexivity).
  destruct Costs as (Cost16 & Cost104 & Cost128).
  pose proof (proj1 Graph) as SiteIn. pose proof (proj2 Graph) as CallIn.
  set (usp := bv_unsigned sp) in *.
  assert (LoHigh : 0x10007fff8000 <= lo) by (unfold STACK_WIN, SEGTOP_A in *; lia).
  assert (UspCap : usp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (FrameW : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; unfold RT_STACK in *; lia).
  assert (FrameAl : (usp + -48) mod 16 = 0).
  { replace (usp + -48) with (usp + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact SpAl. }
  assert (CallAt : forall (Σx : rts RT) (mx : mem), stk asegs mx lo (usp + -48) -> rt_sp0 RT Σx = rt_sp0 RT Σ ->
                     call_ok RT Σx mx (Z_to_bv 64 (usp + -48)) lo).
  { intros Σx mx StkX Sp0X. unfold call_ok. rewrite FrameW, Sp0X.
    split; [exact StkX|]. split; [exact LoWin|]. split; [lia|]. split; [unfold USTACK_TOP in *; lia | exact FrameAl]. }
  assert (LoFrame : lo + 65536 + 560 <= usp) by (unfold RT_STACK in *; lia).
  assert (NotGac : forall y, usp + -48 <= y -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] y).
  { intros y Above. cbn [outside]. split; [unfold G_ALLOW_CUST; lia | exact I]. }
  assert (NotGacHeap : forall y, 0x10007fff8000 <= y -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] y).
  { intros y Heap. cbn [outside]. split; [unfold G_ALLOW_CUST; lia | exact I]. }
  destruct (af_client_consts RT AF Σ m Art0) as (_ & Shad0 & _ & _ & Ut0).
  pose proof (ossl_decoder_cache_new_s0_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                Stk0 ltac:(lia) LoHigh UspCap Ut0 Shad0 Mi0) as Walk0.
  cl_lift Walk0 Start c1 At1.
  destruct (ASTA_unpack RT Σ _ _ c1 At1) as (ms1 & (pad & m1 & -> & Stk1 & Frame1 & _ShadowCell1 & Mu1 & Wm1 & Mi1) & At1e). clear At1.
  fold usp in Stk1, Frame1, Mu1, At1e.
  assert (Art1 : ART RT Σ m1).
  { apply (cl_seg_ART RT AF Σ m m1 usp 48 [] Art0); [lia | unfold USTACK_TOP in *; lia | exact Mu1 | intros y InW; exfalso; apply InW; exact I | exact Wm1]. }
  assert (Env1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary Env0 Mu1); cl_fp_lia).
  assert (Up1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1).
  { intros w Rw. cbv beta in Rw. apply Mu1. cbn [outside]. split; [lia | exact I]. }
  assert (Saved1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [CB 8 pad; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m1 (usp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] Frame1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_decoder_cache_new e_CRYPTO_malloc SITE_ossl_decoder_cache_new_1 m m1 ra s0 sp (Z_to_bv 64 (usp + -48)) outer
              Ctx0 (SiteIn (SITE_ossl_decoder_cache_new_1, e_ossl_decoder_cache_new) ltac:(wp_in_lit))
              (CallIn (SITE_ossl_decoder_cache_new_1, e_CRYPTO_malloc) ltac:(wp_in_lit)) Unw0 Up1 Saved1
              ltac:(rewrite FrameW; lia) SpTop) as (CtxM & UnwM).
  apply (C_CRYPTO_malloc Σ PMc (Z_to_bv 64 SITE_ossl_decoder_cache_new_1) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 sp s1
           (Z_to_bv 64 16) (Z_to_bv 64 0xa30e0) (Z_to_bv 64 775) a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 16 lo (bv_unsigned ra :: outer) lb canary FdOnly MatSt eq_refl TpIs ltac:(lia) Art1 Mi1 (CallAt Σ m1 Stk1 eq_refl)).
  { rewrite FrameW. lia. }
  { rewrite (unsigned_lit SITE_ossl_decoder_cache_new_1) by (unfold SITE_ossl_decoder_cache_new_1; lia). exact CtxM. }
  { exact UnwM. }
  { apply (cg_has_weaken _ _ _ _ _ Graph); vm_compute; reflexivity. }
  { lia. }
  { lia. }
  { exact Env1. }
  { exact At1e. }
  intros c2 (Σ1 & v1 & At2 & Live1 & Frames1 & Sp01 & Credit1 & V1Pos & V1Al16 & V1Top & Cg1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 At2) as (ms2 & (m2 & Ret2 & After2 & Pres2 & Env2 & V1Wr & V1Acc2) & At2e). clear At2.
  destruct Ret2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite FrameW in After2, Pres2. destruct After2 as (Art2 & Mi2 & Wm2 & Stk2).
  rewrite (ret_pc_even SITE_ossl_decoder_cache_new_1) in At2e by (unfold SITE_ossl_decoder_cache_new_1; lia).
  assert (V1In1 : In (v1, 16) (rt_live RT Σ1)) by (rewrite Live1; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 v1 16 Art2 V1In1) as V1Rng. rewrite Sp01 in V1Rng.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 v1 16 Art2 V1In1 ltac:(lia)) as V1High.
  assert (V1Below : v1 + 16 <= lo) by lia.
  assert (V1Cap : v1 + 16 <= 2 ^ 47) by (unfold USTACK_TOP in V1Top; lia).
  assert (V1Word : 0 <= v1 < 2 ^ 64) by lia.
  pose proof (wg_mod16_8 v1 V1Al16) as V1Al.
  destruct (wr_at_rw_CB m2 v1 16 V1Wr ltac:(lia)) as (vjunk & V1Cells2).
  change (Z.to_nat 16) with 16%nat in V1Cells2.
  destruct (af_client_consts RT AF Σ1 m2 Art2) as (_ & Shad2 & _ & _ & Ut2).
  assert (Frame2 : rw_cells asegs m2 (usp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ Frame1). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply Pres2; [apply acl_stack; unfold USTACK_TOP in *; lia | apply NotGac; lia]. }
  assert (Up2 : agree_on (fun x => usp <= x < USTACK_TOP) m m2).
  { intros w Rw. cbv beta in Rw. rewrite (Pres2 w ltac:(apply acl_stack; lia) ltac:(apply NotGac; lia)). exact (Up1 w Rw). }
  assert (Saved2 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [CB 8 pad; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m2 (usp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] Frame2). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_decoder_cache_new e_lock_new SITE_ossl_decoder_cache_new_2 m m2 ra s0 sp (Z_to_bv 64 (usp + -48)) outer
              Ctx0 (SiteIn (SITE_ossl_decoder_cache_new_2, e_ossl_decoder_cache_new) ltac:(wp_in_lit))
              (CallIn (SITE_ossl_decoder_cache_new_2, e_lock_new) ltac:(wp_in_lit)) Unw0 Up2 Saved2
              ltac:(rewrite FrameW; lia) SpTop) as (CtxL & UnwL).
  pose proof (ossl_decoder_cache_new_s1_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_decoder_cache_new_1)
                u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 v1 vjunk pad F1 fc1 m2 lo
                Stk2 ltac:(lia) LoHigh UspCap Frame2 Shad2 V1Word Ut2 V1Cells2 V1Acc2 V1Al V1High V1Cap V1Below Mi2) as Walk1.
  cl_lift Walk1 At2e c3 At3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 At3) as (ms3 & (-> & _ShadowCell3) & At3e). clear At3.
  apply (C_lock_new Σ1 PMc (Z_to_bv 64 SITE_ossl_decoder_cache_new_2) (Z_to_bv 64 (usp + -48)) gp tp u0 u1 u2 sp (Z_to_bv 64 v1)
           (Z_to_bv 64 v1) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m2 lo
           (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FdOnly MatSt TpIs Art2 Mi2 (CallAt Σ1 m2 Stk2 Sp01)).
  { rewrite FrameW. lia. }
  { rewrite Cg1, (unsigned_lit SITE_ossl_decoder_cache_new_2) by (unfold SITE_ossl_decoder_cache_new_2; lia). exact CtxL. }
  { exact UnwL. }
  { rewrite Cg1. apply (cg_has_weaken _ _ _ _ _ Graph); vm_compute; reflexivity. }
  { rewrite Frames1. exact FramesRoom. }
  { rewrite Live1. cbn [length]. lia. }
  { rewrite Credit1. lia. }
  { exact Env2. }
  { exact At3e. }
  intros c4 (Σ2 & lk & At4 & Live2 & Frames2 & Sp02 & Credit2 & LkPos & LkAl16 & LkTop & Cg2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 At4) as (ms4 & (m3 & Ret4 & After4 & Pres4 & Env3 & LkCells3 & LkAcc3) & At4e). clear At4.
  destruct Ret4 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite FrameW in After4, Pres4. destruct After4 as (Art3 & Mi3 & Wm3 & Stk3).
  rewrite (ret_pc_even SITE_ossl_decoder_cache_new_2) in At4e by (unfold SITE_ossl_decoder_cache_new_2; lia).
  assert (LkIn2 : In (lk, 40) (rt_live RT Σ2)) by (rewrite Live2; left; reflexivity).
  assert (V1In2 : In (v1, 16) (rt_live RT Σ2)) by (rewrite Live2, Live1; right; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m3 lk 40 Art3 LkIn2 ltac:(lia)) as LkHigh.
  assert (LkWord : 0 <= lk < 2 ^ 64) by (unfold USTACK_TOP in LkTop; lia).
  pose proof (wg_live_apart RT AF Σ2 m3 [] lk 40 ((v1, 16) :: rt_live RT Σ) v1 16 Art3
                ltac:(rewrite Live2, Live1; reflexivity) ltac:(cbn [app In]; left; reflexivity)) as LkV1.
  assert (Frame3 : rw_cells asegs m3 (usp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ Frame2). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply Pres4; [apply acl_stack; unfold USTACK_TOP in *; lia | apply NotGac; lia]. }
  assert (V1Cells3 : rw_cells asegs m3 v1 [CB 16 vjunk]).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ V1Cells2). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply Pres4; [apply (acl_live _ _ _ v1 16); [exact V1In1 | lia] | apply NotGacHeap; lia]. }
  pose proof (proj2 (af_acc_live RT AF Σ2 m3 v1 16 Art3 V1In2)) as V1Acc3.
  destruct (af_client_consts RT AF Σ2 m3 Art3) as (_ & Shad3 & _ & _ & Ut3).
  assert (AlignOk : negb (bv_eqb (Z_to_bv 64 (Z.land v1 7)) (Z_to_bv 64 0)) = false).
  { rewrite wg_land7 by lia. rewrite V1Al. vm_compute. reflexivity. }
  assert (LockNZ : bv_eqb (Z_to_bv 64 lk) (Z_to_bv 64 0) = false) by solve_cond_u.
  pose proof (ossl_decoder_cache_new_s2_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_decoder_cache_new_2)
                w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 v1 lk vjunk pad F2 fc2 m3 lo
                Stk3 ltac:(lia) LoHigh UspCap V1Cells3 Frame3 Shad3 V1Word LkWord Ut3 V1Acc3 V1Al V1High V1Cap V1Below
                AlignOk LockNZ Mi3) as Walk2.
  cl_lift Walk2 At4e c5 At5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 At5) as (ms5 & (vtail & m4 & -> & V1Cells4 & _ShadowCell5 & Mu4 & Wm4 & Mi4) & At5e). clear At5.
  fold usp in At5e.
  assert (Art4 : ART RT Σ2 m4).
  { apply (af_frame RT AF Σ2 m3 m4 (usp + -48) Art3 ltac:(rewrite Sp02, Sp01; lia)); [|exact Wm4].
    intros w NotCl. apply Mu4. cbn [outside]. split; [|exact I]. intros InV1. apply NotCl. apply (acl_live _ _ _ v1 16); [exact V1In2 | lia]. }
  assert (Env4 : cl_env m4 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m3 m4 _ canary Env3 Mu4); cl_fp_lia).
  assert (Stk4 : stk asegs m4 lo (usp + -48)).
  { apply (stk_munch _ m3 m4 lo (usp + -48) Stk3 Mu4 Wm4). intros y Ry. cbn [outside]. split; [lia | exact I]. }
  assert (Frame4 : rw_cells asegs m4 (usp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ Frame3). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply Mu4. cbn [outside]. split; [lia | exact I]. }
  assert (LkCells4 : rw_cells asegs m4 lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ LkCells3). intros w Rw. cbv beta in Rw. cbn [cells_size mutex_cells csize Nat.add] in Rw.
    apply Mu4. cbn [outside]. split; [lia | exact I]. }
  assert (Up4 : agree_on (fun x => usp <= x < USTACK_TOP) m m4).
  { intros w Rw. cbv beta in Rw.
    rewrite (Mu4 w ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (Pres4 w ltac:(apply acl_stack; lia) ltac:(apply NotGac; lia)).
    exact (Up2 w Rw). }
  assert (Saved4 : rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [CB 8 pad; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m4 (usp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] Frame4). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_decoder_cache_new e_OPENSSL_LH_new SITE_ossl_decoder_cache_new_3 m m4 ra s0 sp (Z_to_bv 64 (usp + -48)) outer
              Ctx0 (SiteIn (SITE_ossl_decoder_cache_new_3, e_ossl_decoder_cache_new) ltac:(wp_in_lit))
              (CallIn (SITE_ossl_decoder_cache_new_3, e_OPENSSL_LH_new) ltac:(wp_in_lit)) Unw0 Up4 Saved4
              ltac:(rewrite FrameW; lia) SpTop) as (CtxH & UnwH).
  apply (C_OPENSSL_LH_new Σ2 PMc (Z_to_bv 64 SITE_ossl_decoder_cache_new_3) (Z_to_bv 64 (usp + -48)) gp tp w0 w1 w2 sp (Z_to_bv 64 v1)
           (Z_to_bv 64 0x3156e0) (Z_to_bv 64 0x315864) d2 d3 d4 d5 d6 d7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880))
           s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m4 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           FdOnly MatSt TpIs Art4 Mi4 (CallAt Σ2 m4 Stk4 ltac:(rewrite Sp02, Sp01; reflexivity))).
  { rewrite FrameW. lia. }
  { rewrite Cg2, Cg1, (unsigned_lit SITE_ossl_decoder_cache_new_3) by (unfold SITE_ossl_decoder_cache_new_3; lia). exact CtxH. }
  { exact UnwH. }
  { rewrite Cg2, Cg1. apply (cg_has_weaken _ _ _ _ _ Graph); vm_compute; reflexivity. }
  { rewrite Live2, Live1. cbn [length]. lia. }
  { rewrite Credit2, Credit1. lia. }
  { exact Env4. }
  { vm_compute. reflexivity. }
  { vm_compute. reflexivity. }
  { exact At5e. }
  intros c6 (Σ3 & q1 & q2 & At6 & Live3 & Frames3 & Sp03 & Credit3 & Q1Pos & Q1Al16 & Q1Top & Q2Pos & Q2Al16 & Q2Top & Cg3).
  destruct (ASTA_unpack RT Σ3 _ _ c6 At6)
    as (ms6 & (m5 & Ret6 & After6 & Pres6 & Env5 & Q1Wr & Q1Acc & Q2Wr & Q2Acc & Q1Cells5 & Q2Cells5) & At6e). clear At6.
  destruct Ret6 as (e0 & e1 & e2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & e3 & e4 & e5 & e6 & F3 & fc3 & ->).
  rewrite FrameW in After6, Pres6. destruct After6 as (Art5 & Mi5 & Wm5 & Stk5).
  rewrite (ret_pc_even SITE_ossl_decoder_cache_new_3) in At6e by (unfold SITE_ossl_decoder_cache_new_3; lia).
  assert (LiveAll : rt_live RT Σ3 = (q2, 128) :: (q1, 104) :: (lk, 40) :: (v1, 16) :: rt_live RT Σ) by (rewrite Live3, Live2, Live1; reflexivity).
  assert (FramesAll : rt_frames RT Σ3 = rt_frames RT Σ) by (rewrite Frames3, Frames2, Frames1; reflexivity).
  assert (Sp0All : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (rewrite Sp03, Sp02, Sp01; reflexivity).
  assert (V1In3 : In (v1, 16) (rt_live RT Σ3)) by (rewrite LiveAll; right; right; right; left; reflexivity).
  assert (LkIn3 : In (lk, 40) (rt_live RT Σ3)) by (rewrite LiveAll; right; right; left; reflexivity).
  assert (Q1In3 : In (q1, 104) (rt_live RT Σ3)) by (rewrite LiveAll; right; left; reflexivity).
  assert (Q2In3 : In (q2, 128) (rt_live RT Σ3)) by (rewrite LiveAll; left; reflexivity).
  pose proof (wg_live_apart RT AF Σ3 m5 [(q2, 128); (q1, 104); (lk, 40)] v1 16 (rt_live RT Σ) q1 104 Art5 LiveAll
                ltac:(cbn [app In]; right; left; reflexivity)) as V1Q1.
  pose proof (wg_live_apart RT AF Σ3 m5 [(q2, 128); (q1, 104); (lk, 40)] v1 16 (rt_live RT Σ) q2 128 Art5 LiveAll
                ltac:(cbn [app In]; left; reflexivity)) as V1Q2.
  pose proof (wg_live_apart RT AF Σ3 m5 [(q2, 128)] q1 104 ((lk, 40) :: (v1, 16) :: rt_live RT Σ) lk 40 Art5 LiveAll
                ltac:(cbn [app In]; right; left; reflexivity)) as Q1Lk.
  pose proof (wg_live_apart RT AF Σ3 m5 [(q2, 128)] q1 104 ((lk, 40) :: (v1, 16) :: rt_live RT Σ) q2 128 Art5 LiveAll
                ltac:(cbn [app In]; left; reflexivity)) as Q1Q2.
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m5 q1 104 Art5 Q1In3 ltac:(lia)) as Q1High.
  pose proof (af_live_range RT AF Σ3 m5 q1 104 Art5 Q1In3) as Q1Rng. rewrite Sp0All in Q1Rng.
  assert (Q1Word : 0 <= q1 < 2 ^ 64) by (unfold USTACK_TOP in Q1Top; lia).
  assert (Frame5 : rw_cells asegs m5 (usp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m4 m5 _ _ Frame4). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply Pres6; [apply acl_stack; unfold USTACK_TOP in *; lia | apply NotGac; lia]. }
  assert (V1Cells5 : rw_cells asegs m5 v1 [C8 (Z_to_bv 64 lk); CB 8 vtail]).
  { apply (rw_cells_agree_nw asegs m4 m5 _ _ V1Cells4). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply Pres6; [apply (acl_live _ _ _ v1 16); [exact V1In2 | lia] | apply NotGacHeap; lia]. }
  assert (LkCells5 : rw_cells asegs m5 lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (rw_cells_agree_nw asegs m4 m5 _ _ LkCells4). intros w Rw. cbv beta in Rw. cbn [cells_size mutex_cells csize Nat.add] in Rw.
    apply Pres6; [apply (acl_live _ _ _ lk 40); [exact LkIn2 | lia] | apply NotGacHeap; lia]. }
  destruct (af_client_consts RT AF Σ3 m5 Art5) as (_ & Shad5 & _ & _ & Ut5).
  pose proof (ossl_decoder_cache_new_s3_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_decoder_cache_new_3)
                e0 e1 e2 g1 g2 g3 g4 g5 g6 g7 e3 e4 e5 e6 v1 lk q1 vtail pad F3 fc3 m5 lo
                Stk5 ltac:(lia) LoHigh UspCap V1Cells5 Frame5 Shad5 V1Word LkWord Q1Word Ut5 Mi5) as Walk3.
  cl_lift Walk3 At6e c7 At7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 At7) as (ms7 & (-> & _ShadowCell7) & At7e). clear At7.
  apply (C_OPENSSL_LH_set_thunks Σ3 PMc (Z_to_bv 64 SITE_ossl_decoder_cache_new_4) (Z_to_bv 64 (usp + -48)) gp tp e0 e1 e2 sp (Z_to_bv 64 v1)
           (Z_to_bv 64 q1) (Z_to_bv 64 0x31707c) (Z_to_bv 64 0x31709c) (Z_to_bv 64 0x3170bc) (Z_to_bv 64 0x3170dc) g5 g6 g7
           (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 e3 e4 e5 e6 F3 fc3 m5 lo q1
           (Z_to_bv 64 q2) (Z_to_bv 64 0x315864) (Z_to_bv 64 0x3156e0) (Z_to_bv 64 8) (Z_to_bv 64 16) (Z_to_bv 64 8) (Z_to_bv 64 512) (Z_to_bv 64 256)
           FdOnly MatSt eq_refl TpIs Art5 Mi5 (CallAt Σ3 m5 Stk5 Sp0All)).
  { rewrite FrameW. lia. }
  { exact Q1In3. }
  { exact Q1Al16. }
  { exact Q1Cells5. }
  { exact At7e. }
  intros c8 At8.
  destruct (ASTA_unpack RT Σ3 _ _ c8 At8) as (ms8 & (m6 & Ret8 & After8 & Pres8 & Q1Cells6) & At8e). clear At8.
  destruct Ret8 as (h0 & h1 & h2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & h3 & h4 & h5 & h6 & F4 & fc4 & ->).
  rewrite FrameW in After8, Pres8. destruct After8 as (Art6 & Mi6 & Wm6 & Stk6).
  rewrite (ret_pc_even SITE_ossl_decoder_cache_new_4) in At8e by (unfold SITE_ossl_decoder_cache_new_4; lia).
  assert (Frame6 : rw_cells asegs m6 (usp + -48) [CB 8 pad; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m5 m6 _ _ Frame5). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply Pres8; [apply acl_stack; unfold USTACK_TOP in *; lia | cbn [outside]; split; [lia | exact I]]. }
  assert (V1Cells6 : rw_cells asegs m6 v1 [C8 (Z_to_bv 64 lk); CB 8 vtail]).
  { apply (rw_cells_agree_nw asegs m5 m6 _ _ V1Cells5). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply Pres8; [apply (acl_live _ _ _ v1 16); [exact V1In3 | lia] | cbn [outside]; split; [lia | exact I]]. }
  pose proof (proj2 (af_acc_live RT AF Σ3 m6 v1 16 Art6 V1In3)) as V1Acc6.
  destruct (af_client_consts RT AF Σ3 m6 Art6) as (_ & Shad6 & _ & _ & Ut6).
  assert (TableNZ : negb (bv_eqb (Z_to_bv 64 q1) (Z_to_bv 64 0)) = true) by solve_cond_u.
  pose proof (ossl_decoder_cache_new_s4_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_decoder_cache_new_4)
                h0 h1 h2 k1 k2 k3 k4 k5 k6 k7 h3 h4 h5 h6 v1 lk q1 vtail pad F4 fc4 m6 lo
                Stk6 ltac:(lia) LoHigh UspCap V1Cells6 Frame6 Shad6 V1Word LkWord Q1Word Ut6 V1Acc6 V1Al V1High V1Cap V1Below TableNZ Mi6) as Walk4.
  cl_lift Walk4 At8e c9 At9.
  apply Kont. exists Σ3, v1, lk, q1, q2.
  split.
  { apply (ASTA_conseq RT Σ3 PMc _ _ c9 At9). intros ms (m7 & RetF & V1F & _ShadowCellF & StkF & MuF & WmF & MiF).
    exists m7. split; [subst ms; do 16 eexists; reflexivity|].
    assert (ArtF : ART RT Σ3 m7).
    { apply (af_frame RT AF Σ3 m6 m7 usp Art6 ltac:(rewrite Sp0All; lia)); [|exact WmF].
      intros w NotCl. apply MuF. cbn [outside]. split; [|exact I]. intros InV1. apply NotCl. apply (acl_live _ _ _ v1 16); [exact V1In3 | lia]. }
    split.
    { split; [exact ArtF|]. split; [exact MiF|]. split; [|exact StkF].
      exact (wmono_trans _ _ _ _ Wm1 (wmono_trans _ _ _ _ Wm2 (wmono_trans _ _ _ _ Wm3 (wmono_trans _ _ _ _ Wm4
               (wmono_trans _ _ _ _ Wm5 (wmono_trans _ _ _ _ Wm6 WmF)))))). }
    split.
    { intros w Acl Out.
      pose proof (cl_split RT AF Σ m usp 48 (bv_unsigned w) Art0 ltac:(lia) ltac:(lia) Acl) as Side.
      pose proof (wg_newchunk_apart RT AF Σ Σ3 m5 [(q2, 128); (q1, 104); (lk, 40); (v1, 16)] v1 16 usp (bv_unsigned w) Art5 LiveAll
                    ltac:(right; right; right; left; reflexivity) FramesAll Sp0All ltac:(lia) ltac:(lia) Acl) as OffV1.
      pose proof (wg_newchunk_apart RT AF Σ Σ3 m5 [(q2, 128); (q1, 104); (lk, 40); (v1, 16)] q1 104 usp (bv_unsigned w) Art5 LiveAll
                    ltac:(right; left; reflexivity) FramesAll Sp0All ltac:(lia) ltac:(lia) Acl) as OffQ1.
      assert (Lower : forall Σx : rts RT, (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σx)) -> rt_frames RT Σx = rt_frames RT Σ ->
                      aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -48) (bv_unsigned w)).
      { intros Σx Grow FrX. apply (aclient_mono _ _ _ _ _ _ _ Acl Grow); [rewrite FrX; auto | lia]. }
      rewrite (MuF w ltac:(cbn [outside]; split; [lia | exact I])).
      rewrite (Pres8 w (Lower Σ3 ltac:(intros e InE; rewrite LiveAll; right; right; right; right; exact InE) FramesAll)
                 ltac:(cbn [outside]; split; [lia | exact I])).
      rewrite (Pres6 w (Lower Σ2 ltac:(intros e InE; rewrite Live2, Live1; right; right; exact InE) ltac:(rewrite Frames2, Frames1; reflexivity)) Out).
      rewrite (Mu4 w ltac:(cbn [outside]; split; [lia | exact I])).
      rewrite (Pres4 w (Lower Σ1 ltac:(intros e InE; rewrite Live1; right; exact InE) Frames1) Out).
      rewrite (Pres2 w (Lower Σ ltac:(auto) eq_refl) Out).
      apply Mu1. cbn [outside]. split; [lia | exact I]. }
    split.
    { assert (Env6 : cl_env m6 (Z_to_bv 8 1) canary).
      { apply (cl_env_agree m5 m6 _ _ Env5). intros w ClW. pose proof (cl_cell_static _ ClW) as StW. pose proof (client_static_range _ StW) as RgW.
        apply Pres8; [apply acl_static; exact StW | cbn [outside]; split; [unfold SEGTOP_A in RgW; lia | exact I]]. }
      apply (cl_env_seg _ m6 m7 _ canary Env6 MuF). cl_fp_lia. }
    split; [exact V1F|].
    split; [exact (proj2 (af_acc_live RT AF Σ3 m7 v1 16 ArtF V1In3))|].
    split.
    { assert (LkCells6 : rw_cells asegs m6 lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
      { apply (rw_cells_agree_nw asegs m5 m6 _ _ LkCells5). intros w Rw. cbv beta in Rw. cbn [cells_size mutex_cells csize Nat.add] in Rw.
        apply Pres8; [apply (acl_live _ _ _ lk 40); [exact LkIn3 | lia] | cbn [outside]; split; [lia | exact I]]. }
      apply (rw_cells_agree_nw asegs m6 m7 _ _ LkCells6). intros w Rw. cbv beta in Rw. cbn [cells_size mutex_cells csize Nat.add] in Rw.
      apply MuF. cbn [outside]. split; [lia | exact I]. }
    split; [exact (proj2 (af_acc_live RT AF Σ3 m7 lk 40 ArtF LkIn3))|].
    split.
    { apply (rw_cells_agree_nw asegs m6 m7 _ _ Q1Cells6). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
      apply MuF. cbn [outside]. split; [lia | exact I]. }
    split; [exact (proj2 (af_acc_live RT AF Σ3 m7 q1 104 ArtF Q1In3))|].
    assert (Q2Cells6 : rw_cells asegs m6 q2 [CB 128 (repeat (Z_to_bv 8 0) 128)]).
    { apply (rw_cells_agree_nw asegs m5 m6 _ _ Q2Cells5). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
      apply Pres8; [apply (acl_live _ _ _ q2 128); [exact Q2In3 | lia] | cbn [outside]; split; [lia | exact I]]. }
    split; [|exact (proj2 (af_acc_live RT AF Σ3 m7 q2 128 ArtF Q2In3))].
    apply (rw_cells_agree_nw asegs m6 m7 _ _ Q2Cells6). intros w Rw. cbv beta in Rw. cbn [cells_size csize Nat.add] in Rw.
    apply MuF. cbn [outside]. split; [lia | exact I]. }
  split; [exact LiveAll|]. split; [exact FramesAll|]. split; [exact Sp0All|].
  split; [rewrite Credit3, Credit2, Credit1; lia|].
  repeat (split; [assumption|]). rewrite Cg3, Cg2, Cg1. reflexivity.
Qed.
End ossl_decoder_cache_new_cps.
