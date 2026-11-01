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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Th_mutex Fz_M_locknew.
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

Definition e_ossl_method_store_new : Z := 0x204724.
Definition SITE_ossl_method_store_new_1 : Z := 0x204770.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_2 : Z := 0x2047a8.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_3 : Z := 0x2047bc.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_4 : Z := 0x2047d8.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_5 : Z := 0x2047f8.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_6 : Z := 0x204840.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ossl_method_store_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1
                 (Z_to_bv 64 24) (Z_to_bv 64 308352) (Z_to_bv 64 328) a3 a4 a5 a6 a7
                 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x204724) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ImgClean ShadowCell MemOk.
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. unfold bv_modulus in SpRange. cbn [Z.of_N] in SpRange.
  remember (bv_unsigned sp) as SPV eqn:SpVal. rewrite <- (Z_to_bv_bv_unsigned sp), <- SpVal.
  pose proof (munch_refl [(SPV + -64, SPV)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  assert (ImgOut : ut_fp [(SPV + -64, SPV)]) by ut_fp_lia. assert (ShOut : sh_fp [(SPV + -64, SPV)]) by sh_fp_lia.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat StkLo.
  (* prologue: open the frame, save ra and s0..s6, set the frame pointer *)
  do 10 zstep.
  (* read the address 6736696 from the GOT cell 5916088, then the shadow base 0x7fff8000 from 6736696 (the cell the ro_cells hypothesis gives) into s4; keep ctx in s2, call CRYPTO_zalloc(24, file, 328) *)
  do 9 zstep.
  subst SPV. rewrite ?Z_to_bv_bv_unsigned.
  apply evt_done. exists m1. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact FR|]. split; [exact StkLo|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s1_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word)
    (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 4) (Z_to_bv 64 96) (Z_to_bv 64 308352) (Z_to_bv 64 295) b4_1 b5_1 b6_1 b7_1
                 a0 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 4) s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (Z_to_bv 64 e_CRYPTO_calloc) fc1 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s1_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m v1 [CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  acc asegs m v1 24 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 24 <= 2 ^ 47 ->
  v1 + 24 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s1_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x204770) fc1 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap FrameCells ShadowCell R1 ImgClean StoreCells StoreAcc StoreAl StoreHi StoreCap StoreBelow MemOk.
  pose proof (munch_refl [(v1, v1 + 8)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v1 [] 24 _ [] [8; 16]%nat) in StoreCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in StoreCells.
  (* the zalloc result is not NULL; its first word is addressable *)
  zstep. ifF.
  do 4 zstep. zstep. ifF.
  (* store ctx in the first word, then call CRYPTO_calloc(4, 96, file, 295) with the shard count 4 in s5 *)
  do 8 zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact StoreCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s2_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word)
    (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_3) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2
                 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
            F2 (Z_to_bv 64 e_ossl_sa_new) fc2 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s2_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m v2 [CB 384 (repeat (Z_to_bv 8 0) 384)] ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s2_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 a0 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 4) s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x2047a8) fc2 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap StoreCells FrameCells ShadowCell R1 R2 ImgClean ShardCells ShardAcc ShardAl ShardHi ShardCap ShardBelow MemOk.
  (* the calloc result v2 is not NULL: keep it in s2 and s3, put v2 + 88 (the address of the first shard's lock word, bytes 88..95) in s6, call ossl_sa_new *)
  zstep. ifF.
  do 4 zstep.
  apply evt_done. split; [reflexivity| exact ShadowCell].
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s3_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word)
    (v1 v2 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v3) (Z_to_bv 64 0) b2_3 b3_3 b4_3 b5_3 b6_3 b7_3
                 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
            F3 (Z_to_bv 64 e_lock_new) fc3 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 376 (repeat (Z_to_bv 8 0) 376)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s3_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [CB 384 (repeat (Z_to_bv 8 0) 384)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v3) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s3_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 F3 fc3 lo m)
    (MS (mkR ra3 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
        F3 (Z_to_bv 64 0x2047bc) fc3 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2, v2 + 8)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [] 384 _ [] [8; 376]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 3 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s4_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word)
    (v1 v2 v3 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_5) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v4) (Z_to_bv 64 (v2 + 80)) (Z_to_bv 64 0) b3_4 b4_4 b5_4 b6_4 b7_4
                 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (Z_to_bv 64 e_lock_new) fc4 None m' (seg_rom asegs)
    /\ munch [(v2 + 80, v2 + 88)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); CB 296 (repeat (Z_to_bv 8 0) 296)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s4_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v3 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 376 (repeat (Z_to_bv 8 0) 376)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v4) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s4_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v3 v4 F4 fc4 lo m)
    (MS (mkR ra4 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v4) b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
        F4 (Z_to_bv 64 0x2047d8) fc4 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 80, v2 + 88)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3)] 376 _ [] [72; 8; 296]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s5_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word)
    (v1 v2 v3 v4 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_3) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v5) (Z_to_bv 64 (v2 + 88)) (Z_to_bv 64 0) b3_5 b4_5 b5_5 b6_5 b7_5
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
            F5 (Z_to_bv 64 e_ossl_sa_new) fc5 None m' (seg_rom asegs)
    /\ munch [(v2 + 88, v2 + 96)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); CB 288 (repeat (Z_to_bv 8 0) 288)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s5_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v2 v3 v4 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); CB 296 (repeat (Z_to_bv 8 0) 296)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v5) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s5_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v2 v3 v4 v5 F5 fc5 lo m)
    (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
        F5 (Z_to_bv 64 0x2047f8) fc5 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 88, v2 + 96)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4)] 296 _ [] [8; 288]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  do 3 zstep. zstep. ifT.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s6_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word)
    (v1 v2 v3 v4 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v6) (Z_to_bv 64 0) b2_6 b3_6 b4_6 b5_6 b6_6 b7_6
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
            F6 (Z_to_bv 64 e_lock_new) fc6 None m' (seg_rom asegs)
    /\ munch [(v2 + 96, v2 + 104)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 280 (repeat (Z_to_bv 8 0) 280)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s6_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v2 v3 v4 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); CB 288 (repeat (Z_to_bv 8 0) 288)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v6) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s6_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v2 v3 v4 v5 v6 F6 fc6 lo m)
    (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
        F6 (Z_to_bv 64 0x2047bc) fc6 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 96, v2 + 104)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5)] 288 _ [] [8; 280]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 3 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s7_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word)
    (v1 v2 v3 v4 v5 v6 v7 : Z) (F7 : bvmap 5 word) (fc7 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_5) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v7) (Z_to_bv 64 (v2 + 176)) (Z_to_bv 64 0) b3_7 b4_7 b5_7 b6_7 b7_7
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
            F7 (Z_to_bv 64 e_lock_new) fc7 None m' (seg_rom asegs)
    /\ munch [(v2 + 176, v2 + 184)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); CB 200 (repeat (Z_to_bv 8 0) 200)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s7_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v2 v3 v4 v5 v6 v7 : Z) (F7 : bvmap 5 word) (fc7 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 280 (repeat (Z_to_bv 8 0) 280)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v7) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s7_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 v1 v2 v3 v4 v5 v6 v7 F7 fc7 lo m)
    (MS (mkR ra7 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
        F7 (Z_to_bv 64 0x2047d8) fc7 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 176, v2 + 184)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6)] 280 _ [] [72; 8; 200]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s8_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word)
    (v1 v2 v3 v4 v5 v6 v7 v8 : Z) (F8 : bvmap 5 word) (fc8 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_3) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v8) (Z_to_bv 64 (v2 + 184)) (Z_to_bv 64 0) b3_8 b4_8 b5_8 b6_8 b7_8
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
            F8 (Z_to_bv 64 e_ossl_sa_new) fc8 None m' (seg_rom asegs)
    /\ munch [(v2 + 184, v2 + 192)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); CB 192 (repeat (Z_to_bv 8 0) 192)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s8_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v2 v3 v4 v5 v6 v7 v8 : Z) (F8 : bvmap 5 word) (fc8 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); CB 200 (repeat (Z_to_bv 8 0) 200)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v8) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s8_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 v1 v2 v3 v4 v5 v6 v7 v8 F8 fc8 lo m)
    (MS (mkR ra8 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v8) b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
        F8 (Z_to_bv 64 0x2047f8) fc8 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 R8 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 184, v2 + 192)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7)] 200 _ [] [8; 192]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  do 3 zstep. zstep. ifT.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s9_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 : Z) (F9 : bvmap 5 word) (fc9 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v9) (Z_to_bv 64 0) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
            F9 (Z_to_bv 64 e_lock_new) fc9 None m' (seg_rom asegs)
    /\ munch [(v2 + 192, v2 + 200)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 184 (repeat (Z_to_bv 8 0) 184)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s9_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 : Z) (F9 : bvmap 5 word) (fc9 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); CB 192 (repeat (Z_to_bv 8 0) 192)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v9) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s9_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 v1 v2 v3 v4 v5 v6 v7 v8 v9 F9 fc9 lo m)
    (MS (mkR ra9 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v9) b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
        F9 (Z_to_bv 64 0x2047bc) fc9 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 R8 R9 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 192, v2 + 200)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8)] 192 _ [] [8; 184]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 3 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s10_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Z) (F10 : bvmap 5 word) (fc10 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_5) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v10) (Z_to_bv 64 (v2 + 272)) (Z_to_bv 64 0) b3_10 b4_10 b5_10 b6_10 b7_10
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
            F10 (Z_to_bv 64 e_lock_new) fc10 None m' (seg_rom asegs)
    /\ munch [(v2 + 272, v2 + 280)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); CB 104 (repeat (Z_to_bv 8 0) 104)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s10_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Z) (F10 : bvmap 5 word) (fc10 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 184 (repeat (Z_to_bv 8 0) 184)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v10) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s10_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 F10 fc10 lo m)
    (MS (mkR ra10 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10) b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
        F10 (Z_to_bv 64 0x2047d8) fc10 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 272, v2 + 280)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9)] 184 _ [] [72; 8; 104]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s11_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Z) (F11 : bvmap 5 word) (fc11 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_3) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v11) (Z_to_bv 64 (v2 + 280)) (Z_to_bv 64 0) b3_11 b4_11 b5_11 b6_11 b7_11
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
            F11 (Z_to_bv 64 e_ossl_sa_new) fc11 None m' (seg_rom asegs)
    /\ munch [(v2 + 280, v2 + 288)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); CB 96 (repeat (Z_to_bv 8 0) 96)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s11_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Z) (F11 : bvmap 5 word) (fc11 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); CB 104 (repeat (Z_to_bv 8 0) 104)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v11) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s11_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 F11 fc11 lo m)
    (MS (mkR ra11 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
        F11 (Z_to_bv 64 0x2047f8) fc11 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 280, v2 + 288)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10)] 104 _ [] [8; 96]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  do 3 zstep. zstep. ifT.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s12_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 : word)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Z) (F12 : bvmap 5 word) (fc12 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v12) (Z_to_bv 64 0) b2_12 b3_12 b4_12 b5_12 b6_12 b7_12
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_12 u4_12 u5_12 u6_12)
            F12 (Z_to_bv 64 e_lock_new) fc12 None m' (seg_rom asegs)
    /\ munch [(v2 + 288, v2 + 296)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 88 (repeat (Z_to_bv 8 0) 88)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s12_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Z) (F12 : bvmap 5 word) (fc12 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); CB 96 (repeat (Z_to_bv 8 0) 96)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v12) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s12_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 F12 fc12 lo m)
    (MS (mkR ra12 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1) (Z_to_bv 64 v12) b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_12 u4_12 u5_12 u6_12)
        F12 (Z_to_bv 64 0x2047bc) fc12 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 288, v2 + 296)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11)] 96 _ [] [8; 88]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 3 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s13_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 : word)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Z) (F13 : bvmap 5 word) (fc13 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_5) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 v13) (Z_to_bv 64 (v2 + 368)) (Z_to_bv 64 0) b3_13 b4_13 b5_13 b6_13 b7_13
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_13 u4_13 u5_13 u6_13)
            F13 (Z_to_bv 64 e_lock_new) fc13 None m' (seg_rom asegs)
    /\ munch [(v2 + 368, v2 + 376)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s13_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Z) (F13 : bvmap 5 word) (fc13 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 88 (repeat (Z_to_bv 8 0) 88)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v13) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s13_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 F13 fc13 lo m)
    (MS (mkR ra13 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1) (Z_to_bv 64 v13) b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_13 u4_13 u5_13 u6_13)
        F13 (Z_to_bv 64 0x2047d8) fc13 None m (seg_rom asegs)).
Proof.
  intros until lo. intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 ImgClean ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 368, v2 + 376)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12)] 88 _ [] [72; 8; 8]%nat) in ShardCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in ShardCells.
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s14_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 : word)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Z) (F14 : bvmap 5 word) (fc14 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_method_store_new_6) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_14 u1_14 u2_14 sp (Z_to_bv 64 v1)
                 (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) (Z_to_bv 64 0) b3_14 b4_14 b5_14 b6_14 b7_14
                 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 384)) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 (v2 + 472)) s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14)
            F14 (Z_to_bv 64 e_lock_new) fc14 None m' (seg_rom asegs)
    /\ munch [(v2 + 376, v2 + 384); (v1 + 8, v1 + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' v1 [C8 a0; C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s14_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Z) (F14 : bvmap 5 word) (fc14 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 24 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 24 <= 2 ^ 47 ->
  v1 + 24 <= lo ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v14) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s14_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 F14 fc14 lo m)
    (MS (mkR ra14 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_14 u1_14 u2_14 sp (Z_to_bv 64 v1) (Z_to_bv 64 v14) b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14)
        F14 (Z_to_bv 64 0x2047f8) fc14 None m (seg_rom asegs)).
Proof.
  intros until lo.
  intros StkLo LoBelow LoHigh SpCap ShardCells StoreCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14
    ImgClean StoreAcc StoreAl StoreHi StoreCap StoreBelow ShardAcc ShardAl ShardHi ShardCap ShardBelow Apart NonNull MemOk.
  pose proof (munch_refl [(v2 + 376, v2 + 384); (v1 + 8, v1 + 16)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  apply (rw_cells_split_CB asegs m v1 [C8 a0] 16 _ [] [8; 8]%nat) in StoreCells; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn repeat] in StoreCells.
  (* last lock of the fourth shard *)
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  (* the shard store left the shadow of the store object alone *)
  apply (acc_munch_sh [(v2 + 376, v2 + 384); (v1 + 8, v1 + 16)] m m0 v1 24) in StoreAcc; [| exact Mu | sh_fp_lia | lia | lia].
  (* the shard counter reaches 0: leave the loop *)
  do 3 zstep. zstep. ifF.
  (* store the shard array in the second word of the store, then call CRYPTO_THREAD_lock_new for the big lock *)
  do 4 zstep. zstep. ifF.
  zstep. zstep.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact ShardCells|]. split; [exact StoreCells|]. exact ShadowCell.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s15_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 : word)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Z) (F15 : bvmap 5 word) (fc15 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR ra sp gp tp u0_15 u1_15 u2_15 s0 s1 (Z_to_bv 64 v1) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 0) b3_15 b4_15 b5_15 b6_15 b7_15
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_15 u4_15 u5_15 u6_15)
            F15 (ret_pc ra) fc15 None m' (seg_rom asegs)
    /\ munch [(v1 + 16, v1 + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' v1 [C8 a0; C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v15)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_method_store_new_s15_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Z) (F15 : bvmap 5 word) (fc15 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 a0; C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 24 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 24 <= 2 ^ 47 ->
  v1 + 24 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v15) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s15_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 F15 fc15 lo m)
    (MS (mkR ra15 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_15 u1_15 u2_15 sp (Z_to_bv 64 v1) (Z_to_bv 64 v15) b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 384)) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 (v2 + 472)) s7 s8 s9 s10 s11 u3_15 u4_15 u5_15 u6_15)
        F15 (Z_to_bv 64 0x204840) fc15 None m (seg_rom asegs)).
Proof.
  intros until lo.
  intros StkLo LoBelow LoHigh SpCap StoreCells ShardCells FrameCells ShadowCell R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15
    ImgClean StoreAcc StoreAl StoreHi StoreCap StoreBelow Apart NonNull MemOk.
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. unfold bv_modulus in SpRange. cbn [Z.of_N] in SpRange.
  remember (bv_unsigned sp) as SPV eqn:SpVal. rewrite <- (Z_to_bv_bv_unsigned sp), <- SpVal.
  pose proof (munch_refl [(v1 + 16, v1 + 24)] m) as Mu. pose proof (wmono_refl asegs m) as Wm.
  (* the big lock goes to the third word of the store *)
  do 4 zstep. zstep. ifF.
  zstep. zstep. wg_raw NonNull.
  (* return the store: restore ra and s0..s6, close the frame *)
  do 11 zstep.
  th_release FrameCells SPV.
  zstep.
  subst SPV. rewrite ?Z_to_bv_bv_unsigned.
  apply evt_done. exists m0. split; [reflexivity|].
  split; [exact Mu|]. split; [exact Wm|]. split; [exact MemOk|]. split; [exact StkLo|]. split; [exact StoreCells|]. exact ShadowCell.
Qed.

Section ossl_method_store_new_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CRYPTO_zalloc : crypto_zalloc_env_stmt RT.
Hypothesis C_CRYPTO_calloc : CRYPTO_calloc_stmt RT.
Hypothesis C_ossl_sa_new : ossl_sa_new_stmt RT.
Hypothesis C_lock_new : crypto_lock_new_env_stmt RT.

Definition ossl_method_store_new_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
    fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 12205808 ->
    ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 576 <= bv_unsigned sp ->
    cg_ctx (rt_cg RT Σ) e_ossl_method_store_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
    cg_has (rt_cg RT Σ)
      [(SITE_ossl_method_store_new_1, e_ossl_method_store_new); (SITE_ossl_method_store_new_2, e_ossl_method_store_new);
       (SITE_ossl_method_store_new_3, e_ossl_method_store_new); (SITE_ossl_method_store_new_4, e_ossl_method_store_new);
       (SITE_ossl_method_store_new_5, e_ossl_method_store_new); (SITE_ossl_method_store_new_6, e_ossl_method_store_new);
       (SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
      [(SITE_ossl_method_store_new_1, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_2, e_CRYPTO_calloc);
       (SITE_ossl_method_store_new_2, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_3, e_ossl_sa_new);
       (SITE_ossl_method_store_new_3, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_4, e_lock_new);
       (SITE_ossl_method_store_new_5, e_lock_new); (SITE_ossl_method_store_new_6, e_lock_new);
       (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
    (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
    Z.of_nat (length (rt_live RT Σ)) + 14 < LIVE_MAX ->
    9 <= rt_credit RT Σ ->
    cl_env m lb canary ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_method_store_new m)))
      (fun c => exists (Σ' : rts RT) (p sh sa1 la1 lb1 sa2 la2 lb2 sa3 la3 lb3 sa4 la4 lb4 big : Z),
         ASTA RT Σ' PMc
           (fun ms => exists m' : mem,
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
              /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
              /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
              /\ cl_env m' (Z_to_bv 8 1) canary
              /\ rw_cells asegs m' p [C8 a0; C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 big)] /\ acc asegs m' p 24
              /\ rw_cells asegs m' sh
                   [C8 (Z_to_bv 64 sa1); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la1); C8 (Z_to_bv 64 lb1);
                    C8 (Z_to_bv 64 sa2); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la2); C8 (Z_to_bv 64 lb2);
                    C8 (Z_to_bv 64 sa3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la3); C8 (Z_to_bv 64 lb3);
                    C8 (Z_to_bv 64 sa4); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la4); C8 (Z_to_bv 64 lb4)]
              /\ acc asegs m' sh 384
              /\ Forall (fun q => rw_cells asegs m' q [CB 32 (repeat (Z_to_bv 8 0) 32)] /\ acc asegs m' q 32) [sa1; sa2; sa3; sa4]
              /\ Forall (fun q => rw_cells asegs m' q (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ acc asegs m' q 40)
                   [la1; lb1; la2; lb2; la3; lb3; la4; lb4; big]) c
         /\ rt_live RT Σ' = [(big, 40); (lb4, 40); (la4, 40); (sa4, 32); (lb3, 40); (la3, 40); (sa3, 32); (lb2, 40); (la2, 40); (sa2, 32);
                             (lb1, 40); (la1, 40); (sa1, 32); (sh, 384); (p, 24)] ++ rt_live RT Σ
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 9
         /\ Forall (fun blk => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP)
              [(big, 40); (lb4, 40); (la4, 40); (sa4, 32); (lb3, 40); (la3, 40); (sa3, 32); (lb2, 40); (la2, 40); (sa2, 32);
               (lb1, 40); (la1, 40); (sa1, 32); (sh, 384); (p, 24)]
         /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_method_store_new_cps : ossl_method_store_new_stmt.
Proof using AF AFP C_CRYPTO_zalloc C_CRYPTO_calloc C_ossl_sa_new C_lock_new.
  unfold ossl_method_store_new_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    Fdfs Mst TpVal Art0 Mi0 CallOk Room CgCtx Uw CgHas FramesOk LiveOk CreditOk Env0.
  destruct CallOk as (Stk0 & Sp0Lo & LoRt & SpTop & SpAl).
  pose proof (af_sp0_win RT AF Σ m Art0) as Sp0Win.
  pose proof (af_client_consts RT AF Σ m Art0) as (_ & Shadow0 & _ & _ & Img0).
  pose proof (bv_unsigned_in_range 64 sp) as SpRange. unfold bv_modulus in SpRange. cbn [Z.of_N] in SpRange.
  set (SP := bv_unsigned sp) in *.
  assert (LoHigh : 0x10007fff8000 <= lo) by (unfold STACK_WIN in Sp0Lo; lia).
  assert (SpCap : SP <= 2 ^ 47) by (unfold USTACK_TOP in SpTop; lia).
  assert (FrameRoom : lo <= SP - 64) by (unfold RT_STACK in Room; lia).
  assert (PmStable : forall S : rts RT, mat_stable (fun mo => ARTM RT S mo /\ PMc mo)) by (intros S; exact (PMc_mat_stable RT AF S PMc Mst)).
  (* where the callee frames go, and the unwind record of this frame *)
  assert (SpBelow : bv_unsigned (Z_to_bv 64 (SP + -64)) = SP + -64) by (apply unsigned_lit; lia).
  assert (CallOkAt : forall (S : rts RT) (mk : mem), stk asegs mk lo (SP + -64) -> rt_sp0 RT S = rt_sp0 RT Σ ->
            call_ok RT S mk (Z_to_bv 64 (SP + -64)) lo).
  { intros S mk StkK Sp0K. unfold call_ok. rewrite SpBelow, Sp0K.
    split; [exact StkK|]. unfold RT_STACK, USTACK_TOP in *. split; [lia|]. split; [lia|]. split; [lia|].
    replace (SP + -64) with ((SP / 16 - 4) * 16) by (pose proof (Z.div_mod SP 16 ltac:(lia)); lia). apply Z.mod_mul. lia. }
  assert (Chain : forall (S : rts RT) (mk : mem) site callee, rt_cg RT S = rt_cg RT Σ ->
            agree_on (fun x => SP <= x < USTACK_TOP) m mk ->
            rw_cells asegs mk (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            0 <= site < 2 ^ 64 -> In (site, e_ossl_method_store_new) (cg_site (rt_cg RT Σ)) -> In (site, callee) (cg_call (rt_cg RT Σ)) ->
            cg_ctx (rt_cg RT S) callee (bv_unsigned (Z_to_bv 64 site) :: bv_unsigned ra :: outer)
            /\ uw_chain mk (Z_to_bv 64 (SP + -64)) sp (bv_unsigned ra :: outer)).
  { intros S mk site callee CgK AgreeK FrameK SiteRange SiteIn CallIn. rewrite CgK, unsigned_lit by exact SiteRange.
    apply (cl_chain_call (rt_cg RT Σ) e_ossl_method_store_new callee site m mk ra s0 sp (Z_to_bv 64 (SP + -64)) outer CgCtx SiteIn CallIn Uw AgreeK).
    - apply (rw_cells_skip mk (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) in FrameK.
      cbn [cells_size csize Nat.add Z.of_nat] in FrameK. fold SP. replace (SP - 16) with (SP + -64 + 48) by lia. exact FrameK.
    - rewrite SpBelow. lia.
    - unfold USTACK_TOP in *. lia. }
  (* a walk writes its frame and blocks this call allocated; the runtime state stays valid *)
  assert (ArtWalk : forall (S : rts RT) (mk mk' : mem) (W : list (Z * Z)), ART RT S mk -> rt_sp0 RT S = rt_sp0 RT Σ ->
            munch W mk mk' -> wmono asegs mk mk' ->
            (forall x, ~ outside W x -> in_live (rt_live RT S) x \/ SP + -64 <= x < SP) -> ART RT S mk').
  { intros S mk mk' W ArtK Sp0K MuK WmK Inside.
    apply (af_frame RT AF S mk mk' (SP + -64) ArtK); [rewrite Sp0K; unfold STACK_WIN in *; lia| |exact WmK].
    intros a NotCl. apply MuK. destruct (outside_dec W (bv_unsigned a)) as [Out|Out]; [exact Out|]. exfalso. apply NotCl.
    destruct (Inside _ Out) as [Live|Frame]; [right; right; left; exact Live| left; unfold USTACK_TOP in *; lia]. }
  assert (EnvWalk : forall (mk mk' : mem) (W : list (Z * Z)) lbx, cl_env mk lbx canary -> munch W mk mk' ->
            (forall x, ~ outside W x -> 0x10007fff8000 <= x) -> cl_env mk' lbx canary).
  { intros mk mk' W lbx EnvK MuK High. apply (cl_env_seg W mk mk' lbx canary EnvK MuK).
    intros x Cell. destruct (outside_dec W x) as [Out|Out]; [exact Out|]. exfalso. specialize (High x Out).
    unfold cl_cell, in_ranges, CL_CELLS in Cell. destruct Cell as (l & h & InC & Rg).
    unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in InC.
    cbn [In] in InC. repeat (destruct InC as [InC|InC]; [injection InC as <- <-; lia|]). exact InC. }
  assert (AgreeWalk : forall (mk mk' : mem) (W : list (Z * Z)), agree_on (fun x => SP <= x < USTACK_TOP) m mk -> munch W mk mk' ->
            (forall x, ~ outside W x -> x < SP) -> agree_on (fun x => SP <= x < USTACK_TOP) m mk').
  { intros mk mk' W AgreeK MuK Low. apply (agree_trans _ m mk mk' AgreeK). intros a Ra. apply MuK.
    destruct (outside_dec W (bv_unsigned a)) as [Out|Out]; [exact Out|]. specialize (Low _ Out). lia. }
  assert (PresWalk : forall (S : rts RT) (mS mk mk' : mem) (NEW W : list (Z * Z)),
            ART RT S mS -> rt_live RT S = NEW ++ rt_live RT Σ -> rt_frames RT S = rt_frames RT Σ -> rt_sp0 RT S = rt_sp0 RT Σ ->
            Forall (fun e => 0 <= snd e) NEW ->
            rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m mk -> munch W mk mk' ->
            (forall x, ~ outside W x -> SP + -64 <= x < SP \/ in_live NEW x) ->
            rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m mk').
  { intros S mS mk mk' NEW W ArtS LiveS FramesS Sp0S Sizes PresK MuK Inside.
    apply (pres_fp_trans _ _ _ _ m mk mk' PresK). apply (pres_fp_of_munch _ _ _ _ W mk mk' MuK).
    intros x Cl _. destruct (outside_dec W x) as [Out|Out]; [exact Out|]. exfalso.
    destruct (Inside x Out) as [Fr|(p & n & InN & Rg)].
    - destruct (cl_split RT AF Σ m SP 64 x Art0 ltac:(unfold STACK_WIN in *; lia) ltac:(lia) Cl); lia.
    - apply (wg_newchunk_apart RT AF Σ S mS NEW p n SP x ArtS LiveS InN FramesS Sp0S ltac:(unfold STACK_WIN in *; lia)
               (proj1 (Forall_forall _ _) Sizes _ InN) Cl). exact Rg. }
  (* a call keeps what lies above its stack pointer and the live blocks, except the latch byte *)
  assert (PresCall : forall (S : rts RT) (NEW : list (Z * Z)) (mk mk' : mem),
            rt_live RT S = NEW ++ rt_live RT Σ -> rt_frames RT S = rt_frames RT Σ ->
            rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m mk ->
            rt_pres_fp (rt_live RT S) (rt_frames RT S) (SP + -64) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] mk mk' ->
            rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m mk').
  { intros S NEW mk mk' LiveS FramesS PresK PresC. apply (pres_fp_trans _ _ _ _ m mk mk' PresK).
    apply (pres_fp_sub _ _ _ _ _ _ _ _ mk mk' PresC). intros x Cl Out. split; [|exact Out].
    apply (aclient_mono _ _ _ _ _ _ _ Cl); [intros e Ein; rewrite LiveS; apply in_or_app; right; exact Ein| intros e Ein; rewrite FramesS; exact Ein| lia]. }
  assert (AgreeCall : forall (live : list (Z * Z)) fr (mk mk' : mem), agree_on (fun x => SP <= x < USTACK_TOP) m mk ->
            rt_pres_fp live fr (SP + -64) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] mk mk' -> agree_on (fun x => SP <= x < USTACK_TOP) m mk').
  { intros live fr mk mk' AgreeK PresC. apply (agree_trans _ m mk mk' AgreeK). apply (agree_of_pres_fp _ _ _ _ mk mk' _ PresC).
    intros x Rg. split; [apply acl_stack; lia| cbn [outside]; unfold G_ALLOW_CUST; split; [lia| exact I]]. }
  assert (FrameCall : forall (live : list (Z * Z)) fr (mk mk' : mem),
            rw_cells asegs mk (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            rt_pres_fp live fr (SP + -64) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] mk mk' -> wmono asegs mk mk' ->
            rw_cells asegs mk' (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { intros live fr mk mk' FrameK PresC WmC. apply (rw_cells_agree asegs mk mk' _ _ FrameK); [|exact WmC].
    apply (agree_of_pres_fp _ _ _ _ mk mk' _ PresC). intros x Rg. cbn [cells_size csize Nat.add Z.of_nat] in Rg.
    split; [apply acl_stack; unfold USTACK_TOP in *; lia| cbn [outside]; unfold G_ALLOW_CUST; split; [lia| exact I]]. }
  assert (LiveCall : forall (live : list (Z * Z)) fr (mk mk' : mem) X cs n,
            rt_pres_fp live fr (SP + -64) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] mk mk' -> wmono asegs mk mk' ->
            In (X, n) live -> Z.of_nat (cells_size cs) <= n -> 0x10007fff8000 <= X ->
            rw_cells asegs mk X cs -> rw_cells asegs mk' X cs).
  { intros live fr mk mk' X cs n PresC WmC InL Hi High CellsK.
    apply (wg_keep_live live fr (SP + -64) _ mk mk' X n X cs CellsK PresC WmC InL ltac:(lia) ltac:(lia)).
    intros x Rg. cbn [outside]. unfold G_ALLOW_CUST. split; [lia| exact I]. }
  (* what the runtime says about a block it just handed out *)
  assert (Fresh : forall (S : rts RT) (mS : mem) p n rest, ART RT S mS -> rt_live RT S = (p, n) :: rest -> rt_sp0 RT S = rt_sp0 RT Σ ->
            1 <= n <= 64512 ->
            acc asegs mS p n /\ 0x10007fff8000 <= p /\ p + n <= 2 ^ 47 /\ p + n <= lo /\ (forall q k, In (q, k) rest -> p + n <= q \/ q + k <= p)).
  { intros S mS p n rest ArtS LiveS Sp0S Size.
    assert (InS : In (p, n) (rt_live RT S)) by (rewrite LiveS; left; reflexivity).
    split; [exact (proj2 (af_acc_live RT AF S mS p n ArtS InS))|].
    split; [exact (afp_live_hi RT GOBJ AFP S mS p n ArtS InS ltac:(lia))|].
    split; [exact (proj2 (afp_live_mem RT GOBJ AFP S mS p n ArtS InS ltac:(lia)))|].
    split; [pose proof (af_live_range RT AF S mS p n ArtS InS) as (_ & Top & _); rewrite Sp0S in Top; unfold STACK_WIN in *; lia|].
    intros q k InR. exact (af_live_disj RT AF S mS p n q k [] rest ArtS LiveS InR). }
  (* call graph entries of this function and of its callees *)
  destruct CgHas as (SitesIn & CallsIn).
  assert (Site1 : In (SITE_ossl_method_store_new_1, e_ossl_method_store_new) (cg_site (rt_cg RT Σ))) by (apply SitesIn; repeat (first [left; reflexivity| right])).
  assert (Site2 : In (SITE_ossl_method_store_new_2, e_ossl_method_store_new) (cg_site (rt_cg RT Σ))) by (apply SitesIn; repeat (first [left; reflexivity| right])).
  assert (Site3 : In (SITE_ossl_method_store_new_3, e_ossl_method_store_new) (cg_site (rt_cg RT Σ))) by (apply SitesIn; repeat (first [left; reflexivity| right])).
  assert (Site4 : In (SITE_ossl_method_store_new_4, e_ossl_method_store_new) (cg_site (rt_cg RT Σ))) by (apply SitesIn; repeat (first [left; reflexivity| right])).
  assert (Site5 : In (SITE_ossl_method_store_new_5, e_ossl_method_store_new) (cg_site (rt_cg RT Σ))) by (apply SitesIn; repeat (first [left; reflexivity| right])).
  assert (Site6 : In (SITE_ossl_method_store_new_6, e_ossl_method_store_new) (cg_site (rt_cg RT Σ))) by (apply SitesIn; repeat (first [left; reflexivity| right])).
  assert (ToZalloc1 : In (SITE_ossl_method_store_new_1, e_CRYPTO_zalloc) (cg_call (rt_cg RT Σ))) by (apply CallsIn; repeat (first [left; reflexivity| right])).
  assert (ToCalloc2 : In (SITE_ossl_method_store_new_2, e_CRYPTO_calloc) (cg_call (rt_cg RT Σ))) by (apply CallsIn; repeat (first [left; reflexivity| right])).
  assert (ToZalloc2 : In (SITE_ossl_method_store_new_2, e_CRYPTO_zalloc) (cg_call (rt_cg RT Σ))) by (apply CallsIn; repeat (first [left; reflexivity| right])).
  assert (ToSa3 : In (SITE_ossl_method_store_new_3, e_ossl_sa_new) (cg_call (rt_cg RT Σ))) by (apply CallsIn; repeat (first [left; reflexivity| right])).
  assert (ToZalloc3 : In (SITE_ossl_method_store_new_3, e_CRYPTO_zalloc) (cg_call (rt_cg RT Σ))) by (apply CallsIn; repeat (first [left; reflexivity| right])).
  assert (ToLock4 : In (SITE_ossl_method_store_new_4, e_lock_new) (cg_call (rt_cg RT Σ))) by (apply CallsIn; repeat (first [left; reflexivity| right])).
  assert (ToLock5 : In (SITE_ossl_method_store_new_5, e_lock_new) (cg_call (rt_cg RT Σ))) by (apply CallsIn; repeat (first [left; reflexivity| right])).
  assert (ToLock6 : In (SITE_ossl_method_store_new_6, e_lock_new) (cg_call (rt_cg RT Σ))) by (apply CallsIn; repeat (first [left; reflexivity| right])).
  assert (AllocCg : forall S : rts RT, rt_cg RT S = rt_cg RT Σ ->
            cg_has (rt_cg RT S) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)]).
  { intros S CgK. rewrite CgK. split; intros e Ein; [apply SitesIn| apply CallsIn]; cbn [In] in Ein;
      repeat (destruct Ein as [<-|Ein]; [repeat (first [left; reflexivity| right])|]); contradiction. }
  assert (LockCg : forall S : rts RT, rt_cg RT S = rt_cg RT Σ ->
            cg_has (rt_cg RT S) [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
              [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)]).
  { intros S CgK. rewrite CgK. split; intros e Ein; [apply SitesIn| apply CallsIn]; cbn [In] in Ein;
      repeat (destruct Ein as [<-|Ein]; [repeat (first [left; reflexivity| right])|]); contradiction. }
  (* prologue: frame, then CRYPTO_zalloc(24) for the store *)
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms <-. unfold entry_st, e_ossl_method_store_new.
    apply (ossl_method_store_new_s0_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      fold SP; try assumption; lia. }
  apply cps_AST_ex. intros W0. apply cps_AST_pure. intros (MuW0 & WmW0 & MiW0 & FrameW0 & StkW0 & ShadowW0).
  change (bv_unsigned sp) with SP in MuW0, FrameW0, StkW0 |- *.
  assert (InFrame0 : forall x, ~ outside [(SP + -64, SP)] x -> SP + -64 <= x < SP) by (intros x Out; cbn [outside] in Out; lia).
  pose proof (ArtWalk Σ m W0 _ Art0 eq_refl MuW0 WmW0 ltac:(intros x Out; right; exact (InFrame0 x Out))) as ArtW0.
  pose proof (AgreeWalk m W0 _ (fun a _ => eq_refl) MuW0 ltac:(intros x Out; pose proof (InFrame0 x Out); lia)) as AgrW0.
  pose proof (EnvWalk m W0 _ lb Env0 MuW0 ltac:(intros x Out; pose proof (InFrame0 x Out); lia)) as EnvW0.
  pose proof (PresWalk Σ m m W0 [] _ Art0 eq_refl eq_refl eq_refl (Forall_nil _) (pres_fp_refl _ _ _ _ m) MuW0
                ltac:(intros x Out; left; exact (InFrame0 x Out))) as PresW0.
  assert (LiveN0 : rt_live RT Σ = [] ++ rt_live RT Σ) by reflexivity.
  assert (FramesN0 : rt_frames RT Σ = rt_frames RT Σ) by reflexivity.
  assert (Sp0N0 : rt_sp0 RT Σ = rt_sp0 RT Σ) by reflexivity.
  assert (CgN0 : rt_cg RT Σ = rt_cg RT Σ) by reflexivity.
  assert (CreditN0 : rt_credit RT Σ = rt_credit RT Σ - 0) by lia.
  pose proof WmW0 as WmAllW0.

  (* call 1: CRYPTO_zalloc at SITE_ossl_method_store_new_1 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_CRYPTO_zalloc| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - reflexivity.
    - exact TpVal.
    - lia.
    - exact ArtW0.
    - exact MiW0.
    - exact (CallOkAt Σ W0 StkW0 Sp0N0).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain Σ W0 SITE_ossl_method_store_new_1 e_CRYPTO_zalloc CgN0 AgrW0 FrameW0 ltac:(unfold SITE_ossl_method_store_new_1; lia) Site1 ToZalloc1)).
    - exact (proj2 (Chain Σ W0 SITE_ossl_method_store_new_1 e_CRYPTO_zalloc CgN0 AgrW0 FrameW0 ltac:(unfold SITE_ossl_method_store_new_1; lia) Site1 ToZalloc1)).
    - exact (AllocCg Σ CgN0).
    - rewrite LiveN0, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN0. repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end. lia.
    - exact EnvW0. }
  apply cps_ex. intros S1. apply cps_ex. intros v1. apply cps_pure.
  intros (Live1 & Frames1 & Sp01 & Credit1 & Pos1 & Al1 & Top1 & Cg1).
  unfold ASTA. apply cps_AST_ex. intros M1. apply cps_AST_pure.
  intros ((Art1 & Mi1 & Wm1 & Stk1) & Pres1 & Env1 & Wr1 & Acc1 & Zero1).
  rewrite SpBelow in Pres1, Stk1.
  unfold ret_st. apply cps_AST_ex; intros j1_0. apply cps_AST_ex; intros j1_1. apply cps_AST_ex; intros j1_2. apply cps_AST_ex; intros j1_3. apply cps_AST_ex; intros j1_4. apply cps_AST_ex; intros j1_5. apply cps_AST_ex; intros j1_6. apply cps_AST_ex; intros j1_7. apply cps_AST_ex; intros j1_8. apply cps_AST_ex; intros j1_9. apply cps_AST_ex; intros j1_10. apply cps_AST_ex; intros j1_11. apply cps_AST_ex; intros j1_12. apply cps_AST_ex; intros j1_13. apply cps_AST_ex; intros j1_14. apply cps_AST_ex; intros j1_15.
  assert (LiveN1 : rt_live RT S1 = [(v1, 24)] ++ rt_live RT Σ) by (rewrite Live1, LiveN0; reflexivity).
  assert (FramesN1 : rt_frames RT S1 = rt_frames RT Σ) by (rewrite Frames1; exact FramesN0).
  assert (Sp0N1 : rt_sp0 RT S1 = rt_sp0 RT Σ) by (rewrite Sp01; exact Sp0N0).
  assert (CgN1 : rt_cg RT S1 = rt_cg RT Σ) by (rewrite Cg1; exact CgN0).
  assert (CreditN1 : rt_credit RT S1 = rt_credit RT Σ - 0) by (rewrite Credit1, CreditN0; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S1 M1 v1 24 _ Art1 Live1 Sp0N1 ltac:(lia)) as (FAcc1 & Hi1 & Cap1 & Below1 & Apart1).
  assert (R1 : 0 <= v1 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W0 M1 FrameW0 Pres1 Wm1) as FrameM1.
  pose proof (AgreeCall _ _ W0 M1 AgrW0 Pres1) as AgrM1.
  pose proof (PresCall Σ [] W0 M1 LiveN0 FramesN0 PresW0 Pres1) as PresM1.
  pose proof (wmono_trans asegs m W0 M1 WmAllW0 Wm1) as WmAllM1.
  pose proof (af_client_consts RT AF S1 M1 Art1) as (_ & Shadow1 & _ & _ & Img1).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_1; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s1_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk1.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact FrameM1.
    - exact Shadow1.
    - exact R1.
    - exact Img1.
    - exact (wp_zero_rw_CB asegs M1 v1 24 Zero1 Wr1 ltac:(lia)).
    - exact (proj2 (af_acc_live RT AF S1 M1 v1 24 Art1 (ltac:(rewrite LiveN1; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v1 Al1).
    - exact Hi1.
    - exact Cap1.
    - exact Below1.
    - exact Mi1. }
  apply cps_AST_ex. intros W1. apply cps_AST_pure.
  intros (MuW1 & WmW1 & MiW1 & StoreW1 & ShadowW1).
  assert (InW1 : forall x, ~ outside [(v1, v1 + 8)] x -> in_live [(v1, 24)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v1, 24; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S1 M1 W1 _ Art1 Sp0N1 MuW1 WmW1 ltac:(intros x Out; left; destruct (InW1 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN1; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW1.
  pose proof (AgreeWalk M1 W1 _ AgrM1 MuW1 ltac:(intros x Out; pose proof (InW1 x Out); lia)) as AgrW1.
  pose proof (EnvWalk M1 W1 _ _ Env1 MuW1 ltac:(intros x Out; pose proof (InW1 x Out); lia)) as EnvW1.
  pose proof (PresWalk S1 M1 M1 W1 [(v1, 24)] _ Art1 LiveN1 FramesN1 Sp0N1 ltac:(repeat constructor; cbn; lia) PresM1 MuW1
                ltac:(intros x Out; right; destruct (InW1 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW1.
  pose proof (wg_keep_seg _ M1 W1 _ _ FrameM1 MuW1 WmW1 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v1, v1 + 8)] x) as [O|O]; [exact O| pose proof (InW1 x O); lia])) as FrameW1.
  pose proof (stk_munch _ M1 W1 lo (SP + -64) Stk1 MuW1 WmW1 ltac:(intros x Rg; destruct (outside_dec [(v1, v1 + 8)] x) as [O|O]; [exact O| pose proof (InW1 x O); lia])) as StkW1.
  pose proof (wmono_trans asegs m M1 W1 WmAllM1 WmW1) as WmAllW1.
  clear dependent M1. clear dependent W0.

  (* call 2: CRYPTO_calloc at SITE_ossl_method_store_new_2 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_CRYPTO_calloc| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - rewrite !unsigned_lit by lia. lia.
    - vm_compute. reflexivity.
    - exact ArtW1.
    - exact MiW1.
    - exact (CallOkAt S1 W1 StkW1 Sp0N1).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S1 W1 SITE_ossl_method_store_new_2 e_CRYPTO_calloc CgN1 AgrW1 FrameW1 ltac:(unfold SITE_ossl_method_store_new_2; lia) Site2 ToCalloc2)).
    - exact (proj2 (Chain S1 W1 SITE_ossl_method_store_new_2 e_CRYPTO_calloc CgN1 AgrW1 FrameW1 ltac:(unfold SITE_ossl_method_store_new_2; lia) Site2 ToCalloc2)).
    - rewrite CgN1, unsigned_lit by (unfold SITE_ossl_method_store_new_2; lia). exact ToZalloc2.
    - exact (AllocCg S1 CgN1).
    - rewrite LiveN1, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN1. repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end. lia.
    - exact EnvW1. }
  apply cps_ex. intros S2. apply cps_ex. intros v2. apply cps_pure.
  intros (Live2 & Frames2 & Sp02 & Credit2 & Pos2 & Al2 & Top2 & Cg2).
  unfold ASTA. apply cps_AST_ex. intros M2. apply cps_AST_pure.
  intros ((Art2 & Mi2 & Wm2 & Stk2) & Pres2 & Env2 & Wr2 & Acc2 & Zero2).
  change (bv_unsigned (Z_to_bv 64 4) * bv_unsigned (Z_to_bv 64 96)) with 384 in Live2, Credit2, Top2, Wr2, Acc2, Zero2.
  rewrite SpBelow in Pres2, Stk2.
  unfold ret_st. apply cps_AST_ex; intros j2_0. apply cps_AST_ex; intros j2_1. apply cps_AST_ex; intros j2_2. apply cps_AST_ex; intros j2_3. apply cps_AST_ex; intros j2_4. apply cps_AST_ex; intros j2_5. apply cps_AST_ex; intros j2_6. apply cps_AST_ex; intros j2_7. apply cps_AST_ex; intros j2_8. apply cps_AST_ex; intros j2_9. apply cps_AST_ex; intros j2_10. apply cps_AST_ex; intros j2_11. apply cps_AST_ex; intros j2_12. apply cps_AST_ex; intros j2_13. apply cps_AST_ex; intros j2_14. apply cps_AST_ex; intros j2_15.
  assert (LiveN2 : rt_live RT S2 = [(v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live2, LiveN1; reflexivity).
  assert (FramesN2 : rt_frames RT S2 = rt_frames RT Σ) by (rewrite Frames2; exact FramesN1).
  assert (Sp0N2 : rt_sp0 RT S2 = rt_sp0 RT Σ) by (rewrite Sp02; exact Sp0N1).
  assert (CgN2 : rt_cg RT S2 = rt_cg RT Σ) by (rewrite Cg2; exact CgN1).
  assert (CreditN2 : rt_credit RT S2 = rt_credit RT Σ - 0) by (rewrite Credit2, CreditN1; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S2 M2 v2 384 _ Art2 Live2 Sp0N2 ltac:(lia)) as (FAcc2 & Hi2 & Cap2 & Below2 & Apart2).
  assert (R2 : 0 <= v2 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W1 M2 FrameW1 Pres2 Wm2) as FrameM2.
  pose proof (AgreeCall _ _ W1 M2 AgrW1 Pres2) as AgrM2.
  pose proof (PresCall S1 [(v1, 24)] W1 M2 LiveN1 FramesN1 PresW1 Pres2) as PresM2.
  pose proof (wmono_trans asegs m W1 M2 WmAllW1 Wm2) as WmAllM2.
  pose proof (af_client_consts RT AF S2 M2 Art2) as (_ & Shadow2 & _ & _ & Img2).
  pose proof (LiveCall _ _ W1 M2 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres2 Wm2 (ltac:(rewrite LiveN1; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW1) as StoreM2.
  pose proof (wp_zero_rw_CB asegs M2 v2 384 Zero2 Wr2 ltac:(lia)) as ShardM2.
  assert (ApT2 : wp_apbox (v2 + 384 <= v1 \/ v1 + 24 <= v2)) by exact (Apart2 v1 24 ltac:(rewrite LiveN1; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_2; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s2_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk2.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact StoreM2.
    - exact FrameM2.
    - exact Shadow2.
    - exact R1.
    - exact R2.
    - exact Img2.
    - exact ShardM2.
    - exact (proj2 (af_acc_live RT AF S2 M2 v2 384 Art2 (ltac:(rewrite LiveN2; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact Mi2. }
  unfold ossl_method_store_new_s2_post. apply cps_AST_pure. intros ShadowW2.
  pose proof Art2 as ArtW2.
  pose proof Mi2 as MiW2.
  pose proof Env2 as EnvW2.
  pose proof Stk2 as StkW2.
  pose proof AgrM2 as AgrW2. pose proof PresM2 as PresW2. pose proof FrameM2 as FrameW2. pose proof WmAllM2 as WmAllW2.
  pose proof StoreM2 as StoreW2. pose proof ShardM2 as ShardW2.

  (* call 3: ossl_sa_new at SITE_ossl_method_store_new_3 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_ossl_sa_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW2.
    - exact MiW2.
    - exact (CallOkAt S2 M2 StkW2 Sp0N2).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S2 M2 SITE_ossl_method_store_new_3 e_ossl_sa_new CgN2 AgrW2 FrameW2 ltac:(unfold SITE_ossl_method_store_new_3; lia) Site3 ToSa3)).
    - exact (proj2 (Chain S2 M2 SITE_ossl_method_store_new_3 e_ossl_sa_new CgN2 AgrW2 FrameW2 ltac:(unfold SITE_ossl_method_store_new_3; lia) Site3 ToSa3)).
    - rewrite CgN2, unsigned_lit by (unfold SITE_ossl_method_store_new_3; lia). exact ToZalloc3.
    - exact (AllocCg S2 CgN2).
    - rewrite LiveN2, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN2. repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end. lia.
    - exact EnvW2. }
  apply cps_ex. intros S3. apply cps_ex. intros v3. apply cps_pure.
  intros (Live3 & Frames3 & Sp03 & Credit3 & Pos3 & Al3 & Top3 & Cg3).
  unfold ASTA. apply cps_AST_ex. intros M3. apply cps_AST_pure.
  intros ((Art3 & Mi3 & Wm3 & Stk3) & Pres3 & Env3 & Wr3 & Acc3 & Zero3).
  rewrite SpBelow in Pres3, Stk3.
  unfold ret_st. apply cps_AST_ex; intros j3_0. apply cps_AST_ex; intros j3_1. apply cps_AST_ex; intros j3_2. apply cps_AST_ex; intros j3_3. apply cps_AST_ex; intros j3_4. apply cps_AST_ex; intros j3_5. apply cps_AST_ex; intros j3_6. apply cps_AST_ex; intros j3_7. apply cps_AST_ex; intros j3_8. apply cps_AST_ex; intros j3_9. apply cps_AST_ex; intros j3_10. apply cps_AST_ex; intros j3_11. apply cps_AST_ex; intros j3_12. apply cps_AST_ex; intros j3_13. apply cps_AST_ex; intros j3_14. apply cps_AST_ex; intros j3_15.
  assert (LiveN3 : rt_live RT S3 = [(v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live3, LiveN2; reflexivity).
  assert (FramesN3 : rt_frames RT S3 = rt_frames RT Σ) by (rewrite Frames3; exact FramesN2).
  assert (Sp0N3 : rt_sp0 RT S3 = rt_sp0 RT Σ) by (rewrite Sp03; exact Sp0N2).
  assert (CgN3 : rt_cg RT S3 = rt_cg RT Σ) by (rewrite Cg3; exact CgN2).
  assert (CreditN3 : rt_credit RT S3 = rt_credit RT Σ - 0) by (rewrite Credit3, CreditN2; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S3 M3 v3 32 _ Art3 Live3 Sp0N3 ltac:(lia)) as (FAcc3 & Hi3 & Cap3 & Below3 & Apart3).
  assert (R3 : 0 <= v3 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ M2 M3 FrameW2 Pres3 Wm3) as FrameM3.
  pose proof (AgreeCall _ _ M2 M3 AgrW2 Pres3) as AgrM3.
  pose proof (PresCall S2 [(v2, 384); (v1, 24)] M2 M3 LiveN2 FramesN2 PresW2 Pres3) as PresM3.
  pose proof (wmono_trans asegs m M2 M3 WmAllW2 Wm3) as WmAllM3.
  pose proof (af_client_consts RT AF S3 M3 Art3) as (_ & Shadow3 & _ & _ & Img3).
  pose proof (LiveCall _ _ M2 M3 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres3 Wm3 (ltac:(rewrite LiveN2; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW2) as StoreM3.
  pose proof (LiveCall _ _ M2 M3 v2 [CB 384 (repeat (Z_to_bv 8 0) 384)] 384 Pres3 Wm3 (ltac:(rewrite LiveN2; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW2) as ShardM3.
  pose proof (wp_zero_rw_CB asegs M3 v3 32 Zero3 Wr3 ltac:(lia)) as Blk3M3.
  assert (ApS3 : wp_apbox (v3 + 32 <= v2 \/ v2 + 384 <= v3)) by exact (Apart3 v2 384 ltac:(rewrite LiveN2; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT3 : wp_apbox (v3 + 32 <= v1 \/ v1 + 24 <= v3)) by exact (Apart3 v1 24 ltac:(rewrite LiveN2; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_3; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s3_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk3.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM3.
    - exact StoreM3.
    - exact FrameM3.
    - exact Shadow3.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact Img3.
    - exact (proj2 (af_acc_live RT AF S3 M3 v2 384 Art3 (ltac:(rewrite LiveN3; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi3. }
  apply cps_AST_ex. intros W3. apply cps_AST_pure.
  intros (MuW3 & WmW3 & MiW3 & ShardW3 & ShadowW3).
  assert (InW3 : forall x, ~ outside [(v2, v2 + 8)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S3 M3 W3 _ Art3 Sp0N3 MuW3 WmW3 ltac:(intros x Out; left; destruct (InW3 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN3; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW3.
  pose proof (AgreeWalk M3 W3 _ AgrM3 MuW3 ltac:(intros x Out; pose proof (InW3 x Out); lia)) as AgrW3.
  pose proof (EnvWalk M3 W3 _ _ Env3 MuW3 ltac:(intros x Out; pose proof (InW3 x Out); lia)) as EnvW3.
  pose proof (PresWalk S3 M3 M3 W3 [(v3, 32); (v2, 384); (v1, 24)] _ Art3 LiveN3 FramesN3 Sp0N3 ltac:(repeat constructor; cbn; lia) PresM3 MuW3
                ltac:(intros x Out; right; destruct (InW3 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW3.
  pose proof (wg_keep_seg _ M3 W3 _ _ FrameM3 MuW3 WmW3 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2, v2 + 8)] x) as [O|O]; [exact O| pose proof (InW3 x O); lia])) as FrameW3.
  pose proof (stk_munch _ M3 W3 lo (SP + -64) Stk3 MuW3 WmW3 ltac:(intros x Rg; destruct (outside_dec [(v2, v2 + 8)] x) as [O|O]; [exact O| pose proof (InW3 x O); lia])) as StkW3.
  pose proof (wmono_trans asegs m M3 W3 WmAllM3 WmW3) as WmAllW3.
  pose proof (wg_keep_seg _ M3 W3 _ _ StoreM3 MuW3 WmW3 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW3.
  pose proof (wg_keep_seg _ M3 W3 _ _ Blk3M3 MuW3 WmW3 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W3.
  clear dependent M3. clear dependent M2. clear dependent S2.

  (* call 4: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_4 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW3.
    - exact MiW3.
    - exact (CallOkAt S3 W3 StkW3 Sp0N3).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S3 W3 SITE_ossl_method_store_new_4 e_lock_new CgN3 AgrW3 FrameW3 ltac:(unfold SITE_ossl_method_store_new_4; lia) Site4 ToLock4)).
    - exact (proj2 (Chain S3 W3 SITE_ossl_method_store_new_4 e_lock_new CgN3 AgrW3 FrameW3 ltac:(unfold SITE_ossl_method_store_new_4; lia) Site4 ToLock4)).
    - exact (LockCg S3 CgN3).
    - rewrite FramesN3. exact FramesOk.
    - rewrite LiveN3, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN3. lia.
    - exact EnvW3. }
  apply cps_ex. intros S4. apply cps_ex. intros v4. apply cps_pure.
  intros (Live4 & Frames4 & Sp04 & Credit4 & Pos4 & Al4 & Top4 & Cg4).
  unfold ASTA. apply cps_AST_ex. intros M4. apply cps_AST_pure.
  intros ((Art4 & Mi4 & Wm4 & Stk4) & Pres4 & Env4 & Mutex4 & Acc4).
  rewrite SpBelow in Pres4, Stk4.
  unfold ret_st. apply cps_AST_ex; intros j4_0. apply cps_AST_ex; intros j4_1. apply cps_AST_ex; intros j4_2. apply cps_AST_ex; intros j4_3. apply cps_AST_ex; intros j4_4. apply cps_AST_ex; intros j4_5. apply cps_AST_ex; intros j4_6. apply cps_AST_ex; intros j4_7. apply cps_AST_ex; intros j4_8. apply cps_AST_ex; intros j4_9. apply cps_AST_ex; intros j4_10. apply cps_AST_ex; intros j4_11. apply cps_AST_ex; intros j4_12. apply cps_AST_ex; intros j4_13. apply cps_AST_ex; intros j4_14. apply cps_AST_ex; intros j4_15.
  assert (LiveN4 : rt_live RT S4 = [(v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live4, LiveN3; reflexivity).
  assert (FramesN4 : rt_frames RT S4 = rt_frames RT Σ) by (rewrite Frames4; exact FramesN3).
  assert (Sp0N4 : rt_sp0 RT S4 = rt_sp0 RT Σ) by (rewrite Sp04; exact Sp0N3).
  assert (CgN4 : rt_cg RT S4 = rt_cg RT Σ) by (rewrite Cg4; exact CgN3).
  assert (CreditN4 : rt_credit RT S4 = rt_credit RT Σ - 1) by (rewrite Credit4, CreditN3; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S4 M4 v4 40 _ Art4 Live4 Sp0N4 ltac:(lia)) as (FAcc4 & Hi4 & Cap4 & Below4 & Apart4).
  assert (R4 : 0 <= v4 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W3 M4 FrameW3 Pres4 Wm4) as FrameM4.
  pose proof (AgreeCall _ _ W3 M4 AgrW3 Pres4) as AgrM4.
  pose proof (PresCall S3 [(v3, 32); (v2, 384); (v1, 24)] W3 M4 LiveN3 FramesN3 PresW3 Pres4) as PresM4.
  pose proof (wmono_trans asegs m W3 M4 WmAllW3 Wm4) as WmAllM4.
  pose proof (af_client_consts RT AF S4 M4 Art4) as (_ & Shadow4 & _ & _ & Img4).
  pose proof (LiveCall _ _ W3 M4 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres4 Wm4 (ltac:(rewrite LiveN3; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW3) as StoreM4.
  pose proof (LiveCall _ _ W3 M4 v2 [C8 (Z_to_bv 64 v3); CB 376 (repeat (Z_to_bv 8 0) 376)] 384 Pres4 Wm4 (ltac:(rewrite LiveN3; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW3) as ShardM4.
  pose proof (LiveCall _ _ W3 M4 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres4 Wm4 (ltac:(rewrite LiveN3; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W3) as Blk3M4.
  pose proof Mutex4 as Blk4M4.
  assert (ApS4 : wp_apbox (v4 + 40 <= v2 \/ v2 + 384 <= v4)) by exact (Apart4 v2 384 ltac:(rewrite LiveN3; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT4 : wp_apbox (v4 + 40 <= v1 \/ v1 + 24 <= v4)) by exact (Apart4 v1 24 ltac:(rewrite LiveN3; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_4; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s4_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk4.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM4.
    - exact StoreM4.
    - exact FrameM4.
    - exact Shadow4.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact Img4.
    - exact (proj2 (af_acc_live RT AF S4 M4 v2 384 Art4 (ltac:(rewrite LiveN4; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi4. }
  apply cps_AST_ex. intros W4. apply cps_AST_pure.
  intros (MuW4 & WmW4 & MiW4 & ShardW4 & ShadowW4).
  assert (InW4 : forall x, ~ outside [(v2 + 80, v2 + 88)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S4 M4 W4 _ Art4 Sp0N4 MuW4 WmW4 ltac:(intros x Out; left; destruct (InW4 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN4; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW4.
  pose proof (AgreeWalk M4 W4 _ AgrM4 MuW4 ltac:(intros x Out; pose proof (InW4 x Out); lia)) as AgrW4.
  pose proof (EnvWalk M4 W4 _ _ Env4 MuW4 ltac:(intros x Out; pose proof (InW4 x Out); lia)) as EnvW4.
  pose proof (PresWalk S4 M4 M4 W4 [(v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art4 LiveN4 FramesN4 Sp0N4 ltac:(repeat constructor; cbn; lia) PresM4 MuW4
                ltac:(intros x Out; right; destruct (InW4 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW4.
  pose proof (wg_keep_seg _ M4 W4 _ _ FrameM4 MuW4 WmW4 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 80, v2 + 88)] x) as [O|O]; [exact O| pose proof (InW4 x O); lia])) as FrameW4.
  pose proof (stk_munch _ M4 W4 lo (SP + -64) Stk4 MuW4 WmW4 ltac:(intros x Rg; destruct (outside_dec [(v2 + 80, v2 + 88)] x) as [O|O]; [exact O| pose proof (InW4 x O); lia])) as StkW4.
  pose proof (wmono_trans asegs m M4 W4 WmAllM4 WmW4) as WmAllW4.
  pose proof (wg_keep_seg _ M4 W4 _ _ StoreM4 MuW4 WmW4 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW4.
  pose proof (wg_keep_seg _ M4 W4 _ _ Blk3M4 MuW4 WmW4 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W4.
  pose proof (wg_keep_seg _ M4 W4 _ _ Blk4M4 MuW4 WmW4 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W4.
  clear dependent M4. clear dependent W3. clear dependent S3.

  (* call 5: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_5 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW4.
    - exact MiW4.
    - exact (CallOkAt S4 W4 StkW4 Sp0N4).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S4 W4 SITE_ossl_method_store_new_5 e_lock_new CgN4 AgrW4 FrameW4 ltac:(unfold SITE_ossl_method_store_new_5; lia) Site5 ToLock5)).
    - exact (proj2 (Chain S4 W4 SITE_ossl_method_store_new_5 e_lock_new CgN4 AgrW4 FrameW4 ltac:(unfold SITE_ossl_method_store_new_5; lia) Site5 ToLock5)).
    - exact (LockCg S4 CgN4).
    - rewrite FramesN4. exact FramesOk.
    - rewrite LiveN4, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN4. lia.
    - exact EnvW4. }
  apply cps_ex. intros S5. apply cps_ex. intros v5. apply cps_pure.
  intros (Live5 & Frames5 & Sp05 & Credit5 & Pos5 & Al5 & Top5 & Cg5).
  unfold ASTA. apply cps_AST_ex. intros M5. apply cps_AST_pure.
  intros ((Art5 & Mi5 & Wm5 & Stk5) & Pres5 & Env5 & Mutex5 & Acc5).
  rewrite SpBelow in Pres5, Stk5.
  unfold ret_st. apply cps_AST_ex; intros j5_0. apply cps_AST_ex; intros j5_1. apply cps_AST_ex; intros j5_2. apply cps_AST_ex; intros j5_3. apply cps_AST_ex; intros j5_4. apply cps_AST_ex; intros j5_5. apply cps_AST_ex; intros j5_6. apply cps_AST_ex; intros j5_7. apply cps_AST_ex; intros j5_8. apply cps_AST_ex; intros j5_9. apply cps_AST_ex; intros j5_10. apply cps_AST_ex; intros j5_11. apply cps_AST_ex; intros j5_12. apply cps_AST_ex; intros j5_13. apply cps_AST_ex; intros j5_14. apply cps_AST_ex; intros j5_15.
  assert (LiveN5 : rt_live RT S5 = [(v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live5, LiveN4; reflexivity).
  assert (FramesN5 : rt_frames RT S5 = rt_frames RT Σ) by (rewrite Frames5; exact FramesN4).
  assert (Sp0N5 : rt_sp0 RT S5 = rt_sp0 RT Σ) by (rewrite Sp05; exact Sp0N4).
  assert (CgN5 : rt_cg RT S5 = rt_cg RT Σ) by (rewrite Cg5; exact CgN4).
  assert (CreditN5 : rt_credit RT S5 = rt_credit RT Σ - 2) by (rewrite Credit5, CreditN4; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S5 M5 v5 40 _ Art5 Live5 Sp0N5 ltac:(lia)) as (FAcc5 & Hi5 & Cap5 & Below5 & Apart5).
  assert (R5 : 0 <= v5 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W4 M5 FrameW4 Pres5 Wm5) as FrameM5.
  pose proof (AgreeCall _ _ W4 M5 AgrW4 Pres5) as AgrM5.
  pose proof (PresCall S4 [(v4, 40); (v3, 32); (v2, 384); (v1, 24)] W4 M5 LiveN4 FramesN4 PresW4 Pres5) as PresM5.
  pose proof (wmono_trans asegs m W4 M5 WmAllW4 Wm5) as WmAllM5.
  pose proof (af_client_consts RT AF S5 M5 Art5) as (_ & Shadow5 & _ & _ & Img5).
  pose proof (LiveCall _ _ W4 M5 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres5 Wm5 (ltac:(rewrite LiveN4; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW4) as StoreM5.
  pose proof (LiveCall _ _ W4 M5 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); CB 296 (repeat (Z_to_bv 8 0) 296)] 384 Pres5 Wm5 (ltac:(rewrite LiveN4; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW4) as ShardM5.
  pose proof (LiveCall _ _ W4 M5 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres5 Wm5 (ltac:(rewrite LiveN4; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W4) as Blk3M5.
  pose proof (LiveCall _ _ W4 M5 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres5 Wm5 (ltac:(rewrite LiveN4; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W4) as Blk4M5.
  pose proof Mutex5 as Blk5M5.
  assert (ApS5 : wp_apbox (v5 + 40 <= v2 \/ v2 + 384 <= v5)) by exact (Apart5 v2 384 ltac:(rewrite LiveN4; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT5 : wp_apbox (v5 + 40 <= v1 \/ v1 + 24 <= v5)) by exact (Apart5 v1 24 ltac:(rewrite LiveN4; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_5; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s5_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk5.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM5.
    - exact StoreM5.
    - exact FrameM5.
    - exact Shadow5.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact Img5.
    - exact (proj2 (af_acc_live RT AF S5 M5 v2 384 Art5 (ltac:(rewrite LiveN5; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi5. }
  apply cps_AST_ex. intros W5. apply cps_AST_pure.
  intros (MuW5 & WmW5 & MiW5 & ShardW5 & ShadowW5).
  assert (InW5 : forall x, ~ outside [(v2 + 88, v2 + 96)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S5 M5 W5 _ Art5 Sp0N5 MuW5 WmW5 ltac:(intros x Out; left; destruct (InW5 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN5; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW5.
  pose proof (AgreeWalk M5 W5 _ AgrM5 MuW5 ltac:(intros x Out; pose proof (InW5 x Out); lia)) as AgrW5.
  pose proof (EnvWalk M5 W5 _ _ Env5 MuW5 ltac:(intros x Out; pose proof (InW5 x Out); lia)) as EnvW5.
  pose proof (PresWalk S5 M5 M5 W5 [(v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art5 LiveN5 FramesN5 Sp0N5 ltac:(repeat constructor; cbn; lia) PresM5 MuW5
                ltac:(intros x Out; right; destruct (InW5 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW5.
  pose proof (wg_keep_seg _ M5 W5 _ _ FrameM5 MuW5 WmW5 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 88, v2 + 96)] x) as [O|O]; [exact O| pose proof (InW5 x O); lia])) as FrameW5.
  pose proof (stk_munch _ M5 W5 lo (SP + -64) Stk5 MuW5 WmW5 ltac:(intros x Rg; destruct (outside_dec [(v2 + 88, v2 + 96)] x) as [O|O]; [exact O| pose proof (InW5 x O); lia])) as StkW5.
  pose proof (wmono_trans asegs m M5 W5 WmAllM5 WmW5) as WmAllW5.
  pose proof (wg_keep_seg _ M5 W5 _ _ StoreM5 MuW5 WmW5 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW5.
  pose proof (wg_keep_seg _ M5 W5 _ _ Blk3M5 MuW5 WmW5 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W5.
  pose proof (wg_keep_seg _ M5 W5 _ _ Blk4M5 MuW5 WmW5 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W5.
  pose proof (wg_keep_seg _ M5 W5 _ _ Blk5M5 MuW5 WmW5 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W5.
  clear dependent M5. clear dependent W4. clear dependent S4.

  (* call 6: ossl_sa_new at SITE_ossl_method_store_new_3 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_ossl_sa_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW5.
    - exact MiW5.
    - exact (CallOkAt S5 W5 StkW5 Sp0N5).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S5 W5 SITE_ossl_method_store_new_3 e_ossl_sa_new CgN5 AgrW5 FrameW5 ltac:(unfold SITE_ossl_method_store_new_3; lia) Site3 ToSa3)).
    - exact (proj2 (Chain S5 W5 SITE_ossl_method_store_new_3 e_ossl_sa_new CgN5 AgrW5 FrameW5 ltac:(unfold SITE_ossl_method_store_new_3; lia) Site3 ToSa3)).
    - rewrite CgN5, unsigned_lit by (unfold SITE_ossl_method_store_new_3; lia). exact ToZalloc3.
    - exact (AllocCg S5 CgN5).
    - rewrite LiveN5, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN5. repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end. lia.
    - exact EnvW5. }
  apply cps_ex. intros S6. apply cps_ex. intros v6. apply cps_pure.
  intros (Live6 & Frames6 & Sp06 & Credit6 & Pos6 & Al6 & Top6 & Cg6).
  unfold ASTA. apply cps_AST_ex. intros M6. apply cps_AST_pure.
  intros ((Art6 & Mi6 & Wm6 & Stk6) & Pres6 & Env6 & Wr6 & Acc6 & Zero6).
  rewrite SpBelow in Pres6, Stk6.
  unfold ret_st. apply cps_AST_ex; intros j6_0. apply cps_AST_ex; intros j6_1. apply cps_AST_ex; intros j6_2. apply cps_AST_ex; intros j6_3. apply cps_AST_ex; intros j6_4. apply cps_AST_ex; intros j6_5. apply cps_AST_ex; intros j6_6. apply cps_AST_ex; intros j6_7. apply cps_AST_ex; intros j6_8. apply cps_AST_ex; intros j6_9. apply cps_AST_ex; intros j6_10. apply cps_AST_ex; intros j6_11. apply cps_AST_ex; intros j6_12. apply cps_AST_ex; intros j6_13. apply cps_AST_ex; intros j6_14. apply cps_AST_ex; intros j6_15.
  assert (LiveN6 : rt_live RT S6 = [(v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live6, LiveN5; reflexivity).
  assert (FramesN6 : rt_frames RT S6 = rt_frames RT Σ) by (rewrite Frames6; exact FramesN5).
  assert (Sp0N6 : rt_sp0 RT S6 = rt_sp0 RT Σ) by (rewrite Sp06; exact Sp0N5).
  assert (CgN6 : rt_cg RT S6 = rt_cg RT Σ) by (rewrite Cg6; exact CgN5).
  assert (CreditN6 : rt_credit RT S6 = rt_credit RT Σ - 2) by (rewrite Credit6, CreditN5; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S6 M6 v6 32 _ Art6 Live6 Sp0N6 ltac:(lia)) as (FAcc6 & Hi6 & Cap6 & Below6 & Apart6).
  assert (R6 : 0 <= v6 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W5 M6 FrameW5 Pres6 Wm6) as FrameM6.
  pose proof (AgreeCall _ _ W5 M6 AgrW5 Pres6) as AgrM6.
  pose proof (PresCall S5 [(v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W5 M6 LiveN5 FramesN5 PresW5 Pres6) as PresM6.
  pose proof (wmono_trans asegs m W5 M6 WmAllW5 Wm6) as WmAllM6.
  pose proof (af_client_consts RT AF S6 M6 Art6) as (_ & Shadow6 & _ & _ & Img6).
  pose proof (LiveCall _ _ W5 M6 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres6 Wm6 (ltac:(rewrite LiveN5; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW5) as StoreM6.
  pose proof (LiveCall _ _ W5 M6 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); CB 288 (repeat (Z_to_bv 8 0) 288)] 384 Pres6 Wm6 (ltac:(rewrite LiveN5; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW5) as ShardM6.
  pose proof (LiveCall _ _ W5 M6 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres6 Wm6 (ltac:(rewrite LiveN5; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W5) as Blk3M6.
  pose proof (LiveCall _ _ W5 M6 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres6 Wm6 (ltac:(rewrite LiveN5; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W5) as Blk4M6.
  pose proof (LiveCall _ _ W5 M6 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres6 Wm6 (ltac:(rewrite LiveN5; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W5) as Blk5M6.
  pose proof (wp_zero_rw_CB asegs M6 v6 32 Zero6 Wr6 ltac:(lia)) as Blk6M6.
  assert (ApS6 : wp_apbox (v6 + 32 <= v2 \/ v2 + 384 <= v6)) by exact (Apart6 v2 384 ltac:(rewrite LiveN5; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT6 : wp_apbox (v6 + 32 <= v1 \/ v1 + 24 <= v6)) by exact (Apart6 v1 24 ltac:(rewrite LiveN5; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_3; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s6_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk6.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM6.
    - exact StoreM6.
    - exact FrameM6.
    - exact Shadow6.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact Img6.
    - exact (proj2 (af_acc_live RT AF S6 M6 v2 384 Art6 (ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi6. }
  apply cps_AST_ex. intros W6. apply cps_AST_pure.
  intros (MuW6 & WmW6 & MiW6 & ShardW6 & ShadowW6).
  assert (InW6 : forall x, ~ outside [(v2 + 96, v2 + 104)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S6 M6 W6 _ Art6 Sp0N6 MuW6 WmW6 ltac:(intros x Out; left; destruct (InW6 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN6; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW6.
  pose proof (AgreeWalk M6 W6 _ AgrM6 MuW6 ltac:(intros x Out; pose proof (InW6 x Out); lia)) as AgrW6.
  pose proof (EnvWalk M6 W6 _ _ Env6 MuW6 ltac:(intros x Out; pose proof (InW6 x Out); lia)) as EnvW6.
  pose proof (PresWalk S6 M6 M6 W6 [(v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art6 LiveN6 FramesN6 Sp0N6 ltac:(repeat constructor; cbn; lia) PresM6 MuW6
                ltac:(intros x Out; right; destruct (InW6 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW6.
  pose proof (wg_keep_seg _ M6 W6 _ _ FrameM6 MuW6 WmW6 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 96, v2 + 104)] x) as [O|O]; [exact O| pose proof (InW6 x O); lia])) as FrameW6.
  pose proof (stk_munch _ M6 W6 lo (SP + -64) Stk6 MuW6 WmW6 ltac:(intros x Rg; destruct (outside_dec [(v2 + 96, v2 + 104)] x) as [O|O]; [exact O| pose proof (InW6 x O); lia])) as StkW6.
  pose proof (wmono_trans asegs m M6 W6 WmAllM6 WmW6) as WmAllW6.
  pose proof (wg_keep_seg _ M6 W6 _ _ StoreM6 MuW6 WmW6 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW6.
  pose proof (wg_keep_seg _ M6 W6 _ _ Blk3M6 MuW6 WmW6 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W6.
  pose proof (wg_keep_seg _ M6 W6 _ _ Blk4M6 MuW6 WmW6 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W6.
  pose proof (wg_keep_seg _ M6 W6 _ _ Blk5M6 MuW6 WmW6 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W6.
  pose proof (wg_keep_seg _ M6 W6 _ _ Blk6M6 MuW6 WmW6 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W6.
  clear dependent M6. clear dependent W5. clear dependent S5.

  (* call 7: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_4 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW6.
    - exact MiW6.
    - exact (CallOkAt S6 W6 StkW6 Sp0N6).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S6 W6 SITE_ossl_method_store_new_4 e_lock_new CgN6 AgrW6 FrameW6 ltac:(unfold SITE_ossl_method_store_new_4; lia) Site4 ToLock4)).
    - exact (proj2 (Chain S6 W6 SITE_ossl_method_store_new_4 e_lock_new CgN6 AgrW6 FrameW6 ltac:(unfold SITE_ossl_method_store_new_4; lia) Site4 ToLock4)).
    - exact (LockCg S6 CgN6).
    - rewrite FramesN6. exact FramesOk.
    - rewrite LiveN6, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN6. lia.
    - exact EnvW6. }
  apply cps_ex. intros S7. apply cps_ex. intros v7. apply cps_pure.
  intros (Live7 & Frames7 & Sp07 & Credit7 & Pos7 & Al7 & Top7 & Cg7).
  unfold ASTA. apply cps_AST_ex. intros M7. apply cps_AST_pure.
  intros ((Art7 & Mi7 & Wm7 & Stk7) & Pres7 & Env7 & Mutex7 & Acc7).
  rewrite SpBelow in Pres7, Stk7.
  unfold ret_st. apply cps_AST_ex; intros j7_0. apply cps_AST_ex; intros j7_1. apply cps_AST_ex; intros j7_2. apply cps_AST_ex; intros j7_3. apply cps_AST_ex; intros j7_4. apply cps_AST_ex; intros j7_5. apply cps_AST_ex; intros j7_6. apply cps_AST_ex; intros j7_7. apply cps_AST_ex; intros j7_8. apply cps_AST_ex; intros j7_9. apply cps_AST_ex; intros j7_10. apply cps_AST_ex; intros j7_11. apply cps_AST_ex; intros j7_12. apply cps_AST_ex; intros j7_13. apply cps_AST_ex; intros j7_14. apply cps_AST_ex; intros j7_15.
  assert (LiveN7 : rt_live RT S7 = [(v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live7, LiveN6; reflexivity).
  assert (FramesN7 : rt_frames RT S7 = rt_frames RT Σ) by (rewrite Frames7; exact FramesN6).
  assert (Sp0N7 : rt_sp0 RT S7 = rt_sp0 RT Σ) by (rewrite Sp07; exact Sp0N6).
  assert (CgN7 : rt_cg RT S7 = rt_cg RT Σ) by (rewrite Cg7; exact CgN6).
  assert (CreditN7 : rt_credit RT S7 = rt_credit RT Σ - 3) by (rewrite Credit7, CreditN6; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S7 M7 v7 40 _ Art7 Live7 Sp0N7 ltac:(lia)) as (FAcc7 & Hi7 & Cap7 & Below7 & Apart7).
  assert (R7 : 0 <= v7 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W6 M7 FrameW6 Pres7 Wm7) as FrameM7.
  pose proof (AgreeCall _ _ W6 M7 AgrW6 Pres7) as AgrM7.
  pose proof (PresCall S6 [(v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W6 M7 LiveN6 FramesN6 PresW6 Pres7) as PresM7.
  pose proof (wmono_trans asegs m W6 M7 WmAllW6 Wm7) as WmAllM7.
  pose proof (af_client_consts RT AF S7 M7 Art7) as (_ & Shadow7 & _ & _ & Img7).
  pose proof (LiveCall _ _ W6 M7 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres7 Wm7 (ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW6) as StoreM7.
  pose proof (LiveCall _ _ W6 M7 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 280 (repeat (Z_to_bv 8 0) 280)] 384 Pres7 Wm7 (ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW6) as ShardM7.
  pose proof (LiveCall _ _ W6 M7 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres7 Wm7 (ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W6) as Blk3M7.
  pose proof (LiveCall _ _ W6 M7 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres7 Wm7 (ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W6) as Blk4M7.
  pose proof (LiveCall _ _ W6 M7 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres7 Wm7 (ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W6) as Blk5M7.
  pose proof (LiveCall _ _ W6 M7 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres7 Wm7 (ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W6) as Blk6M7.
  pose proof Mutex7 as Blk7M7.
  assert (ApS7 : wp_apbox (v7 + 40 <= v2 \/ v2 + 384 <= v7)) by exact (Apart7 v2 384 ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT7 : wp_apbox (v7 + 40 <= v1 \/ v1 + 24 <= v7)) by exact (Apart7 v1 24 ltac:(rewrite LiveN6; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_4; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s7_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk7.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM7.
    - exact StoreM7.
    - exact FrameM7.
    - exact Shadow7.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact Img7.
    - exact (proj2 (af_acc_live RT AF S7 M7 v2 384 Art7 (ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi7. }
  apply cps_AST_ex. intros W7. apply cps_AST_pure.
  intros (MuW7 & WmW7 & MiW7 & ShardW7 & ShadowW7).
  assert (InW7 : forall x, ~ outside [(v2 + 176, v2 + 184)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S7 M7 W7 _ Art7 Sp0N7 MuW7 WmW7 ltac:(intros x Out; left; destruct (InW7 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN7; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW7.
  pose proof (AgreeWalk M7 W7 _ AgrM7 MuW7 ltac:(intros x Out; pose proof (InW7 x Out); lia)) as AgrW7.
  pose proof (EnvWalk M7 W7 _ _ Env7 MuW7 ltac:(intros x Out; pose proof (InW7 x Out); lia)) as EnvW7.
  pose proof (PresWalk S7 M7 M7 W7 [(v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art7 LiveN7 FramesN7 Sp0N7 ltac:(repeat constructor; cbn; lia) PresM7 MuW7
                ltac:(intros x Out; right; destruct (InW7 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW7.
  pose proof (wg_keep_seg _ M7 W7 _ _ FrameM7 MuW7 WmW7 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 176, v2 + 184)] x) as [O|O]; [exact O| pose proof (InW7 x O); lia])) as FrameW7.
  pose proof (stk_munch _ M7 W7 lo (SP + -64) Stk7 MuW7 WmW7 ltac:(intros x Rg; destruct (outside_dec [(v2 + 176, v2 + 184)] x) as [O|O]; [exact O| pose proof (InW7 x O); lia])) as StkW7.
  pose proof (wmono_trans asegs m M7 W7 WmAllM7 WmW7) as WmAllW7.
  pose proof (wg_keep_seg _ M7 W7 _ _ StoreM7 MuW7 WmW7 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW7.
  pose proof (wg_keep_seg _ M7 W7 _ _ Blk3M7 MuW7 WmW7 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W7.
  pose proof (wg_keep_seg _ M7 W7 _ _ Blk4M7 MuW7 WmW7 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W7.
  pose proof (wg_keep_seg _ M7 W7 _ _ Blk5M7 MuW7 WmW7 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W7.
  pose proof (wg_keep_seg _ M7 W7 _ _ Blk6M7 MuW7 WmW7 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W7.
  pose proof (wg_keep_seg _ M7 W7 _ _ Blk7M7 MuW7 WmW7 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS7; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk7W7.
  clear dependent M7. clear dependent W6. clear dependent S6.

  (* call 8: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_5 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW7.
    - exact MiW7.
    - exact (CallOkAt S7 W7 StkW7 Sp0N7).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S7 W7 SITE_ossl_method_store_new_5 e_lock_new CgN7 AgrW7 FrameW7 ltac:(unfold SITE_ossl_method_store_new_5; lia) Site5 ToLock5)).
    - exact (proj2 (Chain S7 W7 SITE_ossl_method_store_new_5 e_lock_new CgN7 AgrW7 FrameW7 ltac:(unfold SITE_ossl_method_store_new_5; lia) Site5 ToLock5)).
    - exact (LockCg S7 CgN7).
    - rewrite FramesN7. exact FramesOk.
    - rewrite LiveN7, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN7. lia.
    - exact EnvW7. }
  apply cps_ex. intros S8. apply cps_ex. intros v8. apply cps_pure.
  intros (Live8 & Frames8 & Sp08 & Credit8 & Pos8 & Al8 & Top8 & Cg8).
  unfold ASTA. apply cps_AST_ex. intros M8. apply cps_AST_pure.
  intros ((Art8 & Mi8 & Wm8 & Stk8) & Pres8 & Env8 & Mutex8 & Acc8).
  rewrite SpBelow in Pres8, Stk8.
  unfold ret_st. apply cps_AST_ex; intros j8_0. apply cps_AST_ex; intros j8_1. apply cps_AST_ex; intros j8_2. apply cps_AST_ex; intros j8_3. apply cps_AST_ex; intros j8_4. apply cps_AST_ex; intros j8_5. apply cps_AST_ex; intros j8_6. apply cps_AST_ex; intros j8_7. apply cps_AST_ex; intros j8_8. apply cps_AST_ex; intros j8_9. apply cps_AST_ex; intros j8_10. apply cps_AST_ex; intros j8_11. apply cps_AST_ex; intros j8_12. apply cps_AST_ex; intros j8_13. apply cps_AST_ex; intros j8_14. apply cps_AST_ex; intros j8_15.
  assert (LiveN8 : rt_live RT S8 = [(v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live8, LiveN7; reflexivity).
  assert (FramesN8 : rt_frames RT S8 = rt_frames RT Σ) by (rewrite Frames8; exact FramesN7).
  assert (Sp0N8 : rt_sp0 RT S8 = rt_sp0 RT Σ) by (rewrite Sp08; exact Sp0N7).
  assert (CgN8 : rt_cg RT S8 = rt_cg RT Σ) by (rewrite Cg8; exact CgN7).
  assert (CreditN8 : rt_credit RT S8 = rt_credit RT Σ - 4) by (rewrite Credit8, CreditN7; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S8 M8 v8 40 _ Art8 Live8 Sp0N8 ltac:(lia)) as (FAcc8 & Hi8 & Cap8 & Below8 & Apart8).
  assert (R8 : 0 <= v8 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W7 M8 FrameW7 Pres8 Wm8) as FrameM8.
  pose proof (AgreeCall _ _ W7 M8 AgrW7 Pres8) as AgrM8.
  pose proof (PresCall S7 [(v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W7 M8 LiveN7 FramesN7 PresW7 Pres8) as PresM8.
  pose proof (wmono_trans asegs m W7 M8 WmAllW7 Wm8) as WmAllM8.
  pose proof (af_client_consts RT AF S8 M8 Art8) as (_ & Shadow8 & _ & _ & Img8).
  pose proof (LiveCall _ _ W7 M8 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres8 Wm8 (ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW7) as StoreM8.
  pose proof (LiveCall _ _ W7 M8 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); CB 200 (repeat (Z_to_bv 8 0) 200)] 384 Pres8 Wm8 (ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW7) as ShardM8.
  pose proof (LiveCall _ _ W7 M8 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres8 Wm8 (ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W7) as Blk3M8.
  pose proof (LiveCall _ _ W7 M8 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres8 Wm8 (ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W7) as Blk4M8.
  pose proof (LiveCall _ _ W7 M8 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres8 Wm8 (ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W7) as Blk5M8.
  pose proof (LiveCall _ _ W7 M8 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres8 Wm8 (ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W7) as Blk6M8.
  pose proof (LiveCall _ _ W7 M8 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres8 Wm8 (ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk7W7) as Blk7M8.
  pose proof Mutex8 as Blk8M8.
  assert (ApS8 : wp_apbox (v8 + 40 <= v2 \/ v2 + 384 <= v8)) by exact (Apart8 v2 384 ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT8 : wp_apbox (v8 + 40 <= v1 \/ v1 + 24 <= v8)) by exact (Apart8 v1 24 ltac:(rewrite LiveN7; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_5; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s8_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk8.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM8.
    - exact StoreM8.
    - exact FrameM8.
    - exact Shadow8.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact R8.
    - exact Img8.
    - exact (proj2 (af_acc_live RT AF S8 M8 v2 384 Art8 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi8. }
  apply cps_AST_ex. intros W8. apply cps_AST_pure.
  intros (MuW8 & WmW8 & MiW8 & ShardW8 & ShadowW8).
  assert (InW8 : forall x, ~ outside [(v2 + 184, v2 + 192)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S8 M8 W8 _ Art8 Sp0N8 MuW8 WmW8 ltac:(intros x Out; left; destruct (InW8 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN8; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW8.
  pose proof (AgreeWalk M8 W8 _ AgrM8 MuW8 ltac:(intros x Out; pose proof (InW8 x Out); lia)) as AgrW8.
  pose proof (EnvWalk M8 W8 _ _ Env8 MuW8 ltac:(intros x Out; pose proof (InW8 x Out); lia)) as EnvW8.
  pose proof (PresWalk S8 M8 M8 W8 [(v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art8 LiveN8 FramesN8 Sp0N8 ltac:(repeat constructor; cbn; lia) PresM8 MuW8
                ltac:(intros x Out; right; destruct (InW8 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW8.
  pose proof (wg_keep_seg _ M8 W8 _ _ FrameM8 MuW8 WmW8 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 184, v2 + 192)] x) as [O|O]; [exact O| pose proof (InW8 x O); lia])) as FrameW8.
  pose proof (stk_munch _ M8 W8 lo (SP + -64) Stk8 MuW8 WmW8 ltac:(intros x Rg; destruct (outside_dec [(v2 + 184, v2 + 192)] x) as [O|O]; [exact O| pose proof (InW8 x O); lia])) as StkW8.
  pose proof (wmono_trans asegs m M8 W8 WmAllM8 WmW8) as WmAllW8.
  pose proof (wg_keep_seg _ M8 W8 _ _ StoreM8 MuW8 WmW8 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW8.
  pose proof (wg_keep_seg _ M8 W8 _ _ Blk3M8 MuW8 WmW8 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W8.
  pose proof (wg_keep_seg _ M8 W8 _ _ Blk4M8 MuW8 WmW8 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W8.
  pose proof (wg_keep_seg _ M8 W8 _ _ Blk5M8 MuW8 WmW8 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W8.
  pose proof (wg_keep_seg _ M8 W8 _ _ Blk6M8 MuW8 WmW8 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W8.
  pose proof (wg_keep_seg _ M8 W8 _ _ Blk7M8 MuW8 WmW8 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS7; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk7W8.
  pose proof (wg_keep_seg _ M8 W8 _ _ Blk8M8 MuW8 WmW8 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS8; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk8W8.
  clear dependent M8. clear dependent W7. clear dependent S7.

  (* call 9: ossl_sa_new at SITE_ossl_method_store_new_3 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_ossl_sa_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW8.
    - exact MiW8.
    - exact (CallOkAt S8 W8 StkW8 Sp0N8).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S8 W8 SITE_ossl_method_store_new_3 e_ossl_sa_new CgN8 AgrW8 FrameW8 ltac:(unfold SITE_ossl_method_store_new_3; lia) Site3 ToSa3)).
    - exact (proj2 (Chain S8 W8 SITE_ossl_method_store_new_3 e_ossl_sa_new CgN8 AgrW8 FrameW8 ltac:(unfold SITE_ossl_method_store_new_3; lia) Site3 ToSa3)).
    - rewrite CgN8, unsigned_lit by (unfold SITE_ossl_method_store_new_3; lia). exact ToZalloc3.
    - exact (AllocCg S8 CgN8).
    - rewrite LiveN8, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN8. repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end. lia.
    - exact EnvW8. }
  apply cps_ex. intros S9. apply cps_ex. intros v9. apply cps_pure.
  intros (Live9 & Frames9 & Sp09 & Credit9 & Pos9 & Al9 & Top9 & Cg9).
  unfold ASTA. apply cps_AST_ex. intros M9. apply cps_AST_pure.
  intros ((Art9 & Mi9 & Wm9 & Stk9) & Pres9 & Env9 & Wr9 & Acc9 & Zero9).
  rewrite SpBelow in Pres9, Stk9.
  unfold ret_st. apply cps_AST_ex; intros j9_0. apply cps_AST_ex; intros j9_1. apply cps_AST_ex; intros j9_2. apply cps_AST_ex; intros j9_3. apply cps_AST_ex; intros j9_4. apply cps_AST_ex; intros j9_5. apply cps_AST_ex; intros j9_6. apply cps_AST_ex; intros j9_7. apply cps_AST_ex; intros j9_8. apply cps_AST_ex; intros j9_9. apply cps_AST_ex; intros j9_10. apply cps_AST_ex; intros j9_11. apply cps_AST_ex; intros j9_12. apply cps_AST_ex; intros j9_13. apply cps_AST_ex; intros j9_14. apply cps_AST_ex; intros j9_15.
  assert (LiveN9 : rt_live RT S9 = [(v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live9, LiveN8; reflexivity).
  assert (FramesN9 : rt_frames RT S9 = rt_frames RT Σ) by (rewrite Frames9; exact FramesN8).
  assert (Sp0N9 : rt_sp0 RT S9 = rt_sp0 RT Σ) by (rewrite Sp09; exact Sp0N8).
  assert (CgN9 : rt_cg RT S9 = rt_cg RT Σ) by (rewrite Cg9; exact CgN8).
  assert (CreditN9 : rt_credit RT S9 = rt_credit RT Σ - 4) by (rewrite Credit9, CreditN8; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S9 M9 v9 32 _ Art9 Live9 Sp0N9 ltac:(lia)) as (FAcc9 & Hi9 & Cap9 & Below9 & Apart9).
  assert (R9 : 0 <= v9 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W8 M9 FrameW8 Pres9 Wm9) as FrameM9.
  pose proof (AgreeCall _ _ W8 M9 AgrW8 Pres9) as AgrM9.
  pose proof (PresCall S8 [(v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W8 M9 LiveN8 FramesN8 PresW8 Pres9) as PresM9.
  pose proof (wmono_trans asegs m W8 M9 WmAllW8 Wm9) as WmAllM9.
  pose proof (af_client_consts RT AF S9 M9 Art9) as (_ & Shadow9 & _ & _ & Img9).
  pose proof (LiveCall _ _ W8 M9 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres9 Wm9 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW8) as StoreM9.
  pose proof (LiveCall _ _ W8 M9 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); CB 192 (repeat (Z_to_bv 8 0) 192)] 384 Pres9 Wm9 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW8) as ShardM9.
  pose proof (LiveCall _ _ W8 M9 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres9 Wm9 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W8) as Blk3M9.
  pose proof (LiveCall _ _ W8 M9 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres9 Wm9 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W8) as Blk4M9.
  pose proof (LiveCall _ _ W8 M9 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres9 Wm9 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W8) as Blk5M9.
  pose proof (LiveCall _ _ W8 M9 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres9 Wm9 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W8) as Blk6M9.
  pose proof (LiveCall _ _ W8 M9 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres9 Wm9 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk7W8) as Blk7M9.
  pose proof (LiveCall _ _ W8 M9 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres9 Wm9 (ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk8W8) as Blk8M9.
  pose proof (wp_zero_rw_CB asegs M9 v9 32 Zero9 Wr9 ltac:(lia)) as Blk9M9.
  assert (ApS9 : wp_apbox (v9 + 32 <= v2 \/ v2 + 384 <= v9)) by exact (Apart9 v2 384 ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT9 : wp_apbox (v9 + 32 <= v1 \/ v1 + 24 <= v9)) by exact (Apart9 v1 24 ltac:(rewrite LiveN8; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_3; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s9_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk9.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM9.
    - exact StoreM9.
    - exact FrameM9.
    - exact Shadow9.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact R8.
    - exact R9.
    - exact Img9.
    - exact (proj2 (af_acc_live RT AF S9 M9 v2 384 Art9 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi9. }
  apply cps_AST_ex. intros W9. apply cps_AST_pure.
  intros (MuW9 & WmW9 & MiW9 & ShardW9 & ShadowW9).
  assert (InW9 : forall x, ~ outside [(v2 + 192, v2 + 200)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S9 M9 W9 _ Art9 Sp0N9 MuW9 WmW9 ltac:(intros x Out; left; destruct (InW9 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN9; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW9.
  pose proof (AgreeWalk M9 W9 _ AgrM9 MuW9 ltac:(intros x Out; pose proof (InW9 x Out); lia)) as AgrW9.
  pose proof (EnvWalk M9 W9 _ _ Env9 MuW9 ltac:(intros x Out; pose proof (InW9 x Out); lia)) as EnvW9.
  pose proof (PresWalk S9 M9 M9 W9 [(v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art9 LiveN9 FramesN9 Sp0N9 ltac:(repeat constructor; cbn; lia) PresM9 MuW9
                ltac:(intros x Out; right; destruct (InW9 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW9.
  pose proof (wg_keep_seg _ M9 W9 _ _ FrameM9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 192, v2 + 200)] x) as [O|O]; [exact O| pose proof (InW9 x O); lia])) as FrameW9.
  pose proof (stk_munch _ M9 W9 lo (SP + -64) Stk9 MuW9 WmW9 ltac:(intros x Rg; destruct (outside_dec [(v2 + 192, v2 + 200)] x) as [O|O]; [exact O| pose proof (InW9 x O); lia])) as StkW9.
  pose proof (wmono_trans asegs m M9 W9 WmAllM9 WmW9) as WmAllW9.
  pose proof (wg_keep_seg _ M9 W9 _ _ StoreM9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW9.
  pose proof (wg_keep_seg _ M9 W9 _ _ Blk3M9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W9.
  pose proof (wg_keep_seg _ M9 W9 _ _ Blk4M9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W9.
  pose proof (wg_keep_seg _ M9 W9 _ _ Blk5M9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W9.
  pose proof (wg_keep_seg _ M9 W9 _ _ Blk6M9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W9.
  pose proof (wg_keep_seg _ M9 W9 _ _ Blk7M9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS7; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk7W9.
  pose proof (wg_keep_seg _ M9 W9 _ _ Blk8M9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS8; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk8W9.
  pose proof (wg_keep_seg _ M9 W9 _ _ Blk9M9 MuW9 WmW9 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS9; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk9W9.
  clear dependent M9. clear dependent W8. clear dependent S8.

  (* call 10: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_4 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW9.
    - exact MiW9.
    - exact (CallOkAt S9 W9 StkW9 Sp0N9).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S9 W9 SITE_ossl_method_store_new_4 e_lock_new CgN9 AgrW9 FrameW9 ltac:(unfold SITE_ossl_method_store_new_4; lia) Site4 ToLock4)).
    - exact (proj2 (Chain S9 W9 SITE_ossl_method_store_new_4 e_lock_new CgN9 AgrW9 FrameW9 ltac:(unfold SITE_ossl_method_store_new_4; lia) Site4 ToLock4)).
    - exact (LockCg S9 CgN9).
    - rewrite FramesN9. exact FramesOk.
    - rewrite LiveN9, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN9. lia.
    - exact EnvW9. }
  apply cps_ex. intros S10. apply cps_ex. intros v10. apply cps_pure.
  intros (Live10 & Frames10 & Sp010 & Credit10 & Pos10 & Al10 & Top10 & Cg10).
  unfold ASTA. apply cps_AST_ex. intros M10. apply cps_AST_pure.
  intros ((Art10 & Mi10 & Wm10 & Stk10) & Pres10 & Env10 & Mutex10 & Acc10).
  rewrite SpBelow in Pres10, Stk10.
  unfold ret_st. apply cps_AST_ex; intros j10_0. apply cps_AST_ex; intros j10_1. apply cps_AST_ex; intros j10_2. apply cps_AST_ex; intros j10_3. apply cps_AST_ex; intros j10_4. apply cps_AST_ex; intros j10_5. apply cps_AST_ex; intros j10_6. apply cps_AST_ex; intros j10_7. apply cps_AST_ex; intros j10_8. apply cps_AST_ex; intros j10_9. apply cps_AST_ex; intros j10_10. apply cps_AST_ex; intros j10_11. apply cps_AST_ex; intros j10_12. apply cps_AST_ex; intros j10_13. apply cps_AST_ex; intros j10_14. apply cps_AST_ex; intros j10_15.
  assert (LiveN10 : rt_live RT S10 = [(v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live10, LiveN9; reflexivity).
  assert (FramesN10 : rt_frames RT S10 = rt_frames RT Σ) by (rewrite Frames10; exact FramesN9).
  assert (Sp0N10 : rt_sp0 RT S10 = rt_sp0 RT Σ) by (rewrite Sp010; exact Sp0N9).
  assert (CgN10 : rt_cg RT S10 = rt_cg RT Σ) by (rewrite Cg10; exact CgN9).
  assert (CreditN10 : rt_credit RT S10 = rt_credit RT Σ - 5) by (rewrite Credit10, CreditN9; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S10 M10 v10 40 _ Art10 Live10 Sp0N10 ltac:(lia)) as (FAcc10 & Hi10 & Cap10 & Below10 & Apart10).
  assert (R10 : 0 <= v10 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W9 M10 FrameW9 Pres10 Wm10) as FrameM10.
  pose proof (AgreeCall _ _ W9 M10 AgrW9 Pres10) as AgrM10.
  pose proof (PresCall S9 [(v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W9 M10 LiveN9 FramesN9 PresW9 Pres10) as PresM10.
  pose proof (wmono_trans asegs m W9 M10 WmAllW9 Wm10) as WmAllM10.
  pose proof (af_client_consts RT AF S10 M10 Art10) as (_ & Shadow10 & _ & _ & Img10).
  pose proof (LiveCall _ _ W9 M10 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW9) as StoreM10.
  pose proof (LiveCall _ _ W9 M10 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 184 (repeat (Z_to_bv 8 0) 184)] 384 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW9) as ShardM10.
  pose proof (LiveCall _ _ W9 M10 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W9) as Blk3M10.
  pose proof (LiveCall _ _ W9 M10 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W9) as Blk4M10.
  pose proof (LiveCall _ _ W9 M10 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W9) as Blk5M10.
  pose proof (LiveCall _ _ W9 M10 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W9) as Blk6M10.
  pose proof (LiveCall _ _ W9 M10 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk7W9) as Blk7M10.
  pose proof (LiveCall _ _ W9 M10 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk8W9) as Blk8M10.
  pose proof (LiveCall _ _ W9 M10 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres10 Wm10 (ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk9W9) as Blk9M10.
  pose proof Mutex10 as Blk10M10.
  assert (ApS10 : wp_apbox (v10 + 40 <= v2 \/ v2 + 384 <= v10)) by exact (Apart10 v2 384 ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT10 : wp_apbox (v10 + 40 <= v1 \/ v1 + 24 <= v10)) by exact (Apart10 v1 24 ltac:(rewrite LiveN9; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_4; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s10_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk10.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM10.
    - exact StoreM10.
    - exact FrameM10.
    - exact Shadow10.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact R8.
    - exact R9.
    - exact R10.
    - exact Img10.
    - exact (proj2 (af_acc_live RT AF S10 M10 v2 384 Art10 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi10. }
  apply cps_AST_ex. intros W10. apply cps_AST_pure.
  intros (MuW10 & WmW10 & MiW10 & ShardW10 & ShadowW10).
  assert (InW10 : forall x, ~ outside [(v2 + 272, v2 + 280)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S10 M10 W10 _ Art10 Sp0N10 MuW10 WmW10 ltac:(intros x Out; left; destruct (InW10 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN10; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW10.
  pose proof (AgreeWalk M10 W10 _ AgrM10 MuW10 ltac:(intros x Out; pose proof (InW10 x Out); lia)) as AgrW10.
  pose proof (EnvWalk M10 W10 _ _ Env10 MuW10 ltac:(intros x Out; pose proof (InW10 x Out); lia)) as EnvW10.
  pose proof (PresWalk S10 M10 M10 W10 [(v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art10 LiveN10 FramesN10 Sp0N10 ltac:(repeat constructor; cbn; lia) PresM10 MuW10
                ltac:(intros x Out; right; destruct (InW10 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW10.
  pose proof (wg_keep_seg _ M10 W10 _ _ FrameM10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 272, v2 + 280)] x) as [O|O]; [exact O| pose proof (InW10 x O); lia])) as FrameW10.
  pose proof (stk_munch _ M10 W10 lo (SP + -64) Stk10 MuW10 WmW10 ltac:(intros x Rg; destruct (outside_dec [(v2 + 272, v2 + 280)] x) as [O|O]; [exact O| pose proof (InW10 x O); lia])) as StkW10.
  pose proof (wmono_trans asegs m M10 W10 WmAllM10 WmW10) as WmAllW10.
  pose proof (wg_keep_seg _ M10 W10 _ _ StoreM10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW10.
  pose proof (wg_keep_seg _ M10 W10 _ _ Blk3M10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W10.
  pose proof (wg_keep_seg _ M10 W10 _ _ Blk4M10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W10.
  pose proof (wg_keep_seg _ M10 W10 _ _ Blk5M10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W10.
  pose proof (wg_keep_seg _ M10 W10 _ _ Blk6M10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W10.
  pose proof (wg_keep_seg _ M10 W10 _ _ Blk7M10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS7; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk7W10.
  pose proof (wg_keep_seg _ M10 W10 _ _ Blk8M10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS8; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk8W10.
  pose proof (wg_keep_seg _ M10 W10 _ _ Blk9M10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS9; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk9W10.
  pose proof (wg_keep_seg _ M10 W10 _ _ Blk10M10 MuW10 WmW10 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS10; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk10W10.
  clear dependent M10. clear dependent W9. clear dependent S9.

  (* call 11: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_5 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW10.
    - exact MiW10.
    - exact (CallOkAt S10 W10 StkW10 Sp0N10).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S10 W10 SITE_ossl_method_store_new_5 e_lock_new CgN10 AgrW10 FrameW10 ltac:(unfold SITE_ossl_method_store_new_5; lia) Site5 ToLock5)).
    - exact (proj2 (Chain S10 W10 SITE_ossl_method_store_new_5 e_lock_new CgN10 AgrW10 FrameW10 ltac:(unfold SITE_ossl_method_store_new_5; lia) Site5 ToLock5)).
    - exact (LockCg S10 CgN10).
    - rewrite FramesN10. exact FramesOk.
    - rewrite LiveN10, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN10. lia.
    - exact EnvW10. }
  apply cps_ex. intros S11. apply cps_ex. intros v11. apply cps_pure.
  intros (Live11 & Frames11 & Sp011 & Credit11 & Pos11 & Al11 & Top11 & Cg11).
  unfold ASTA. apply cps_AST_ex. intros M11. apply cps_AST_pure.
  intros ((Art11 & Mi11 & Wm11 & Stk11) & Pres11 & Env11 & Mutex11 & Acc11).
  rewrite SpBelow in Pres11, Stk11.
  unfold ret_st. apply cps_AST_ex; intros j11_0. apply cps_AST_ex; intros j11_1. apply cps_AST_ex; intros j11_2. apply cps_AST_ex; intros j11_3. apply cps_AST_ex; intros j11_4. apply cps_AST_ex; intros j11_5. apply cps_AST_ex; intros j11_6. apply cps_AST_ex; intros j11_7. apply cps_AST_ex; intros j11_8. apply cps_AST_ex; intros j11_9. apply cps_AST_ex; intros j11_10. apply cps_AST_ex; intros j11_11. apply cps_AST_ex; intros j11_12. apply cps_AST_ex; intros j11_13. apply cps_AST_ex; intros j11_14. apply cps_AST_ex; intros j11_15.
  assert (LiveN11 : rt_live RT S11 = [(v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live11, LiveN10; reflexivity).
  assert (FramesN11 : rt_frames RT S11 = rt_frames RT Σ) by (rewrite Frames11; exact FramesN10).
  assert (Sp0N11 : rt_sp0 RT S11 = rt_sp0 RT Σ) by (rewrite Sp011; exact Sp0N10).
  assert (CgN11 : rt_cg RT S11 = rt_cg RT Σ) by (rewrite Cg11; exact CgN10).
  assert (CreditN11 : rt_credit RT S11 = rt_credit RT Σ - 6) by (rewrite Credit11, CreditN10; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S11 M11 v11 40 _ Art11 Live11 Sp0N11 ltac:(lia)) as (FAcc11 & Hi11 & Cap11 & Below11 & Apart11).
  assert (R11 : 0 <= v11 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W10 M11 FrameW10 Pres11 Wm11) as FrameM11.
  pose proof (AgreeCall _ _ W10 M11 AgrW10 Pres11) as AgrM11.
  pose proof (PresCall S10 [(v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W10 M11 LiveN10 FramesN10 PresW10 Pres11) as PresM11.
  pose proof (wmono_trans asegs m W10 M11 WmAllW10 Wm11) as WmAllM11.
  pose proof (af_client_consts RT AF S11 M11 Art11) as (_ & Shadow11 & _ & _ & Img11).
  pose proof (LiveCall _ _ W10 M11 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW10) as StoreM11.
  pose proof (LiveCall _ _ W10 M11 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); CB 104 (repeat (Z_to_bv 8 0) 104)] 384 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW10) as ShardM11.
  pose proof (LiveCall _ _ W10 M11 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W10) as Blk3M11.
  pose proof (LiveCall _ _ W10 M11 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W10) as Blk4M11.
  pose proof (LiveCall _ _ W10 M11 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W10) as Blk5M11.
  pose proof (LiveCall _ _ W10 M11 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W10) as Blk6M11.
  pose proof (LiveCall _ _ W10 M11 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk7W10) as Blk7M11.
  pose proof (LiveCall _ _ W10 M11 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk8W10) as Blk8M11.
  pose proof (LiveCall _ _ W10 M11 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk9W10) as Blk9M11.
  pose proof (LiveCall _ _ W10 M11 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres11 Wm11 (ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk10W10) as Blk10M11.
  pose proof Mutex11 as Blk11M11.
  assert (ApS11 : wp_apbox (v11 + 40 <= v2 \/ v2 + 384 <= v11)) by exact (Apart11 v2 384 ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT11 : wp_apbox (v11 + 40 <= v1 \/ v1 + 24 <= v11)) by exact (Apart11 v1 24 ltac:(rewrite LiveN10; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_5; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s11_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk11.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM11.
    - exact StoreM11.
    - exact FrameM11.
    - exact Shadow11.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact R8.
    - exact R9.
    - exact R10.
    - exact R11.
    - exact Img11.
    - exact (proj2 (af_acc_live RT AF S11 M11 v2 384 Art11 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi11. }
  apply cps_AST_ex. intros W11. apply cps_AST_pure.
  intros (MuW11 & WmW11 & MiW11 & ShardW11 & ShadowW11).
  assert (InW11 : forall x, ~ outside [(v2 + 280, v2 + 288)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S11 M11 W11 _ Art11 Sp0N11 MuW11 WmW11 ltac:(intros x Out; left; destruct (InW11 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN11; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW11.
  pose proof (AgreeWalk M11 W11 _ AgrM11 MuW11 ltac:(intros x Out; pose proof (InW11 x Out); lia)) as AgrW11.
  pose proof (EnvWalk M11 W11 _ _ Env11 MuW11 ltac:(intros x Out; pose proof (InW11 x Out); lia)) as EnvW11.
  pose proof (PresWalk S11 M11 M11 W11 [(v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art11 LiveN11 FramesN11 Sp0N11 ltac:(repeat constructor; cbn; lia) PresM11 MuW11
                ltac:(intros x Out; right; destruct (InW11 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW11.
  pose proof (wg_keep_seg _ M11 W11 _ _ FrameM11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 280, v2 + 288)] x) as [O|O]; [exact O| pose proof (InW11 x O); lia])) as FrameW11.
  pose proof (stk_munch _ M11 W11 lo (SP + -64) Stk11 MuW11 WmW11 ltac:(intros x Rg; destruct (outside_dec [(v2 + 280, v2 + 288)] x) as [O|O]; [exact O| pose proof (InW11 x O); lia])) as StkW11.
  pose proof (wmono_trans asegs m M11 W11 WmAllM11 WmW11) as WmAllW11.
  pose proof (wg_keep_seg _ M11 W11 _ _ StoreM11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk3M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk4M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk5M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk6M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk7M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS7; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk7W11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk8M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS8; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk8W11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk9M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS9; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk9W11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk10M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS10; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk10W11.
  pose proof (wg_keep_seg _ M11 W11 _ _ Blk11M11 MuW11 WmW11 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS11; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk11W11.
  clear dependent M11. clear dependent W10. clear dependent S10.

  (* call 12: ossl_sa_new at SITE_ossl_method_store_new_3 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_ossl_sa_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW11.
    - exact MiW11.
    - exact (CallOkAt S11 W11 StkW11 Sp0N11).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S11 W11 SITE_ossl_method_store_new_3 e_ossl_sa_new CgN11 AgrW11 FrameW11 ltac:(unfold SITE_ossl_method_store_new_3; lia) Site3 ToSa3)).
    - exact (proj2 (Chain S11 W11 SITE_ossl_method_store_new_3 e_ossl_sa_new CgN11 AgrW11 FrameW11 ltac:(unfold SITE_ossl_method_store_new_3; lia) Site3 ToSa3)).
    - rewrite CgN11, unsigned_lit by (unfold SITE_ossl_method_store_new_3; lia). exact ToZalloc3.
    - exact (AllocCg S11 CgN11).
    - rewrite LiveN11, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN11. repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end. lia.
    - exact EnvW11. }
  apply cps_ex. intros S12. apply cps_ex. intros v12. apply cps_pure.
  intros (Live12 & Frames12 & Sp012 & Credit12 & Pos12 & Al12 & Top12 & Cg12).
  unfold ASTA. apply cps_AST_ex. intros M12. apply cps_AST_pure.
  intros ((Art12 & Mi12 & Wm12 & Stk12) & Pres12 & Env12 & Wr12 & Acc12 & Zero12).
  rewrite SpBelow in Pres12, Stk12.
  unfold ret_st. apply cps_AST_ex; intros j12_0. apply cps_AST_ex; intros j12_1. apply cps_AST_ex; intros j12_2. apply cps_AST_ex; intros j12_3. apply cps_AST_ex; intros j12_4. apply cps_AST_ex; intros j12_5. apply cps_AST_ex; intros j12_6. apply cps_AST_ex; intros j12_7. apply cps_AST_ex; intros j12_8. apply cps_AST_ex; intros j12_9. apply cps_AST_ex; intros j12_10. apply cps_AST_ex; intros j12_11. apply cps_AST_ex; intros j12_12. apply cps_AST_ex; intros j12_13. apply cps_AST_ex; intros j12_14. apply cps_AST_ex; intros j12_15.
  assert (LiveN12 : rt_live RT S12 = [(v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live12, LiveN11; reflexivity).
  assert (FramesN12 : rt_frames RT S12 = rt_frames RT Σ) by (rewrite Frames12; exact FramesN11).
  assert (Sp0N12 : rt_sp0 RT S12 = rt_sp0 RT Σ) by (rewrite Sp012; exact Sp0N11).
  assert (CgN12 : rt_cg RT S12 = rt_cg RT Σ) by (rewrite Cg12; exact CgN11).
  assert (CreditN12 : rt_credit RT S12 = rt_credit RT Σ - 6) by (rewrite Credit12, CreditN11; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S12 M12 v12 32 _ Art12 Live12 Sp0N12 ltac:(lia)) as (FAcc12 & Hi12 & Cap12 & Below12 & Apart12).
  assert (R12 : 0 <= v12 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W11 M12 FrameW11 Pres12 Wm12) as FrameM12.
  pose proof (AgreeCall _ _ W11 M12 AgrW11 Pres12) as AgrM12.
  pose proof (PresCall S11 [(v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W11 M12 LiveN11 FramesN11 PresW11 Pres12) as PresM12.
  pose proof (wmono_trans asegs m W11 M12 WmAllW11 Wm12) as WmAllM12.
  pose proof (af_client_consts RT AF S12 M12 Art12) as (_ & Shadow12 & _ & _ & Img12).
  pose proof (LiveCall _ _ W11 M12 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW11) as StoreM12.
  pose proof (LiveCall _ _ W11 M12 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); CB 96 (repeat (Z_to_bv 8 0) 96)] 384 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW11) as ShardM12.
  pose proof (LiveCall _ _ W11 M12 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W11) as Blk3M12.
  pose proof (LiveCall _ _ W11 M12 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W11) as Blk4M12.
  pose proof (LiveCall _ _ W11 M12 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W11) as Blk5M12.
  pose proof (LiveCall _ _ W11 M12 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W11) as Blk6M12.
  pose proof (LiveCall _ _ W11 M12 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk7W11) as Blk7M12.
  pose proof (LiveCall _ _ W11 M12 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk8W11) as Blk8M12.
  pose proof (LiveCall _ _ W11 M12 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk9W11) as Blk9M12.
  pose proof (LiveCall _ _ W11 M12 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk10W11) as Blk10M12.
  pose proof (LiveCall _ _ W11 M12 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres12 Wm12 (ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk11W11) as Blk11M12.
  pose proof (wp_zero_rw_CB asegs M12 v12 32 Zero12 Wr12 ltac:(lia)) as Blk12M12.
  assert (ApS12 : wp_apbox (v12 + 32 <= v2 \/ v2 + 384 <= v12)) by exact (Apart12 v2 384 ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT12 : wp_apbox (v12 + 32 <= v1 \/ v1 + 24 <= v12)) by exact (Apart12 v1 24 ltac:(rewrite LiveN11; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_3; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s12_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk12.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM12.
    - exact StoreM12.
    - exact FrameM12.
    - exact Shadow12.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact R8.
    - exact R9.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact Img12.
    - exact (proj2 (af_acc_live RT AF S12 M12 v2 384 Art12 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi12. }
  apply cps_AST_ex. intros W12. apply cps_AST_pure.
  intros (MuW12 & WmW12 & MiW12 & ShardW12 & ShadowW12).
  assert (InW12 : forall x, ~ outside [(v2 + 288, v2 + 296)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S12 M12 W12 _ Art12 Sp0N12 MuW12 WmW12 ltac:(intros x Out; left; destruct (InW12 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN12; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW12.
  pose proof (AgreeWalk M12 W12 _ AgrM12 MuW12 ltac:(intros x Out; pose proof (InW12 x Out); lia)) as AgrW12.
  pose proof (EnvWalk M12 W12 _ _ Env12 MuW12 ltac:(intros x Out; pose proof (InW12 x Out); lia)) as EnvW12.
  pose proof (PresWalk S12 M12 M12 W12 [(v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art12 LiveN12 FramesN12 Sp0N12 ltac:(repeat constructor; cbn; lia) PresM12 MuW12
                ltac:(intros x Out; right; destruct (InW12 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW12.
  pose proof (wg_keep_seg _ M12 W12 _ _ FrameM12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 288, v2 + 296)] x) as [O|O]; [exact O| pose proof (InW12 x O); lia])) as FrameW12.
  pose proof (stk_munch _ M12 W12 lo (SP + -64) Stk12 MuW12 WmW12 ltac:(intros x Rg; destruct (outside_dec [(v2 + 288, v2 + 296)] x) as [O|O]; [exact O| pose proof (InW12 x O); lia])) as StkW12.
  pose proof (wmono_trans asegs m M12 W12 WmAllM12 WmW12) as WmAllW12.
  pose proof (wg_keep_seg _ M12 W12 _ _ StoreM12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk3M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk4M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk5M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk6M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk7M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS7; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk7W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk8M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS8; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk8W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk9M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS9; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk9W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk10M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS10; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk10W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk11M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS11; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk11W12.
  pose proof (wg_keep_seg _ M12 W12 _ _ Blk12M12 MuW12 WmW12 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS12; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk12W12.
  clear dependent M12. clear dependent W11. clear dependent S11.

  (* call 13: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_4 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW12.
    - exact MiW12.
    - exact (CallOkAt S12 W12 StkW12 Sp0N12).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S12 W12 SITE_ossl_method_store_new_4 e_lock_new CgN12 AgrW12 FrameW12 ltac:(unfold SITE_ossl_method_store_new_4; lia) Site4 ToLock4)).
    - exact (proj2 (Chain S12 W12 SITE_ossl_method_store_new_4 e_lock_new CgN12 AgrW12 FrameW12 ltac:(unfold SITE_ossl_method_store_new_4; lia) Site4 ToLock4)).
    - exact (LockCg S12 CgN12).
    - rewrite FramesN12. exact FramesOk.
    - rewrite LiveN12, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN12. lia.
    - exact EnvW12. }
  apply cps_ex. intros S13. apply cps_ex. intros v13. apply cps_pure.
  intros (Live13 & Frames13 & Sp013 & Credit13 & Pos13 & Al13 & Top13 & Cg13).
  unfold ASTA. apply cps_AST_ex. intros M13. apply cps_AST_pure.
  intros ((Art13 & Mi13 & Wm13 & Stk13) & Pres13 & Env13 & Mutex13 & Acc13).
  rewrite SpBelow in Pres13, Stk13.
  unfold ret_st. apply cps_AST_ex; intros j13_0. apply cps_AST_ex; intros j13_1. apply cps_AST_ex; intros j13_2. apply cps_AST_ex; intros j13_3. apply cps_AST_ex; intros j13_4. apply cps_AST_ex; intros j13_5. apply cps_AST_ex; intros j13_6. apply cps_AST_ex; intros j13_7. apply cps_AST_ex; intros j13_8. apply cps_AST_ex; intros j13_9. apply cps_AST_ex; intros j13_10. apply cps_AST_ex; intros j13_11. apply cps_AST_ex; intros j13_12. apply cps_AST_ex; intros j13_13. apply cps_AST_ex; intros j13_14. apply cps_AST_ex; intros j13_15.
  assert (LiveN13 : rt_live RT S13 = [(v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live13, LiveN12; reflexivity).
  assert (FramesN13 : rt_frames RT S13 = rt_frames RT Σ) by (rewrite Frames13; exact FramesN12).
  assert (Sp0N13 : rt_sp0 RT S13 = rt_sp0 RT Σ) by (rewrite Sp013; exact Sp0N12).
  assert (CgN13 : rt_cg RT S13 = rt_cg RT Σ) by (rewrite Cg13; exact CgN12).
  assert (CreditN13 : rt_credit RT S13 = rt_credit RT Σ - 7) by (rewrite Credit13, CreditN12; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S13 M13 v13 40 _ Art13 Live13 Sp0N13 ltac:(lia)) as (FAcc13 & Hi13 & Cap13 & Below13 & Apart13).
  assert (R13 : 0 <= v13 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W12 M13 FrameW12 Pres13 Wm13) as FrameM13.
  pose proof (AgreeCall _ _ W12 M13 AgrW12 Pres13) as AgrM13.
  pose proof (PresCall S12 [(v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W12 M13 LiveN12 FramesN12 PresW12 Pres13) as PresM13.
  pose proof (wmono_trans asegs m W12 M13 WmAllW12 Wm13) as WmAllM13.
  pose proof (af_client_consts RT AF S13 M13 Art13) as (_ & Shadow13 & _ & _ & Img13).
  pose proof (LiveCall _ _ W12 M13 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW12) as StoreM13.
  pose proof (LiveCall _ _ W12 M13 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 88 (repeat (Z_to_bv 8 0) 88)] 384 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW12) as ShardM13.
  pose proof (LiveCall _ _ W12 M13 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W12) as Blk3M13.
  pose proof (LiveCall _ _ W12 M13 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W12) as Blk4M13.
  pose proof (LiveCall _ _ W12 M13 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W12) as Blk5M13.
  pose proof (LiveCall _ _ W12 M13 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W12) as Blk6M13.
  pose proof (LiveCall _ _ W12 M13 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk7W12) as Blk7M13.
  pose proof (LiveCall _ _ W12 M13 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk8W12) as Blk8M13.
  pose proof (LiveCall _ _ W12 M13 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk9W12) as Blk9M13.
  pose proof (LiveCall _ _ W12 M13 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk10W12) as Blk10M13.
  pose proof (LiveCall _ _ W12 M13 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk11W12) as Blk11M13.
  pose proof (LiveCall _ _ W12 M13 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres13 Wm13 (ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk12W12) as Blk12M13.
  pose proof Mutex13 as Blk13M13.
  assert (ApS13 : wp_apbox (v13 + 40 <= v2 \/ v2 + 384 <= v13)) by exact (Apart13 v2 384 ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT13 : wp_apbox (v13 + 40 <= v1 \/ v1 + 24 <= v13)) by exact (Apart13 v1 24 ltac:(rewrite LiveN12; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_4; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s13_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk13.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM13.
    - exact StoreM13.
    - exact FrameM13.
    - exact Shadow13.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact R8.
    - exact R9.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact R13.
    - exact Img13.
    - exact (proj2 (af_acc_live RT AF S13 M13 v2 384 Art13 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi13. }
  apply cps_AST_ex. intros W13. apply cps_AST_pure.
  intros (MuW13 & WmW13 & MiW13 & ShardW13 & ShadowW13).
  assert (InW13 : forall x, ~ outside [(v2 + 368, v2 + 376)] x -> in_live [(v2, 384)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v2, 384; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S13 M13 W13 _ Art13 Sp0N13 MuW13 WmW13 ltac:(intros x Out; left; destruct (InW13 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN13; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW13.
  pose proof (AgreeWalk M13 W13 _ AgrM13 MuW13 ltac:(intros x Out; pose proof (InW13 x Out); lia)) as AgrW13.
  pose proof (EnvWalk M13 W13 _ _ Env13 MuW13 ltac:(intros x Out; pose proof (InW13 x Out); lia)) as EnvW13.
  pose proof (PresWalk S13 M13 M13 W13 [(v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art13 LiveN13 FramesN13 Sp0N13 ltac:(repeat constructor; cbn; lia) PresM13 MuW13
                ltac:(intros x Out; right; destruct (InW13 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW13.
  pose proof (wg_keep_seg _ M13 W13 _ _ FrameM13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 368, v2 + 376)] x) as [O|O]; [exact O| pose proof (InW13 x O); lia])) as FrameW13.
  pose proof (stk_munch _ M13 W13 lo (SP + -64) Stk13 MuW13 WmW13 ltac:(intros x Rg; destruct (outside_dec [(v2 + 368, v2 + 376)] x) as [O|O]; [exact O| pose proof (InW13 x O); lia])) as StkW13.
  pose proof (wmono_trans asegs m M13 W13 WmAllM13 WmW13) as WmAllW13.
  pose proof (wg_keep_seg _ M13 W13 _ _ StoreM13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as StoreW13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk3M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk4M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk5M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk6M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk7M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS7; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk7W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk8M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS8; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk8W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk9M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS9; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk9W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk10M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS10; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk10W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk11M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS11; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk11W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk12M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS12; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk12W13.
  pose proof (wg_keep_seg _ M13 W13 _ _ Blk13M13 MuW13 WmW13 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS13; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk13W13.
  clear dependent M13. clear dependent W12. clear dependent S12.

  (* call 14: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_5 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW13.
    - exact MiW13.
    - exact (CallOkAt S13 W13 StkW13 Sp0N13).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S13 W13 SITE_ossl_method_store_new_5 e_lock_new CgN13 AgrW13 FrameW13 ltac:(unfold SITE_ossl_method_store_new_5; lia) Site5 ToLock5)).
    - exact (proj2 (Chain S13 W13 SITE_ossl_method_store_new_5 e_lock_new CgN13 AgrW13 FrameW13 ltac:(unfold SITE_ossl_method_store_new_5; lia) Site5 ToLock5)).
    - exact (LockCg S13 CgN13).
    - rewrite FramesN13. exact FramesOk.
    - rewrite LiveN13, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN13. lia.
    - exact EnvW13. }
  apply cps_ex. intros S14. apply cps_ex. intros v14. apply cps_pure.
  intros (Live14 & Frames14 & Sp014 & Credit14 & Pos14 & Al14 & Top14 & Cg14).
  unfold ASTA. apply cps_AST_ex. intros M14. apply cps_AST_pure.
  intros ((Art14 & Mi14 & Wm14 & Stk14) & Pres14 & Env14 & Mutex14 & Acc14).
  rewrite SpBelow in Pres14, Stk14.
  unfold ret_st. apply cps_AST_ex; intros j14_0. apply cps_AST_ex; intros j14_1. apply cps_AST_ex; intros j14_2. apply cps_AST_ex; intros j14_3. apply cps_AST_ex; intros j14_4. apply cps_AST_ex; intros j14_5. apply cps_AST_ex; intros j14_6. apply cps_AST_ex; intros j14_7. apply cps_AST_ex; intros j14_8. apply cps_AST_ex; intros j14_9. apply cps_AST_ex; intros j14_10. apply cps_AST_ex; intros j14_11. apply cps_AST_ex; intros j14_12. apply cps_AST_ex; intros j14_13. apply cps_AST_ex; intros j14_14. apply cps_AST_ex; intros j14_15.
  assert (LiveN14 : rt_live RT S14 = [(v14, 40); (v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live14, LiveN13; reflexivity).
  assert (FramesN14 : rt_frames RT S14 = rt_frames RT Σ) by (rewrite Frames14; exact FramesN13).
  assert (Sp0N14 : rt_sp0 RT S14 = rt_sp0 RT Σ) by (rewrite Sp014; exact Sp0N13).
  assert (CgN14 : rt_cg RT S14 = rt_cg RT Σ) by (rewrite Cg14; exact CgN13).
  assert (CreditN14 : rt_credit RT S14 = rt_credit RT Σ - 8) by (rewrite Credit14, CreditN13; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S14 M14 v14 40 _ Art14 Live14 Sp0N14 ltac:(lia)) as (FAcc14 & Hi14 & Cap14 & Below14 & Apart14).
  assert (R14 : 0 <= v14 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W13 M14 FrameW13 Pres14 Wm14) as FrameM14.
  pose proof (AgreeCall _ _ W13 M14 AgrW13 Pres14) as AgrM14.
  pose proof (PresCall S13 [(v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W13 M14 LiveN13 FramesN13 PresW13 Pres14) as PresM14.
  pose proof (wmono_trans asegs m W13 M14 WmAllW13 Wm14) as WmAllM14.
  pose proof (af_client_consts RT AF S14 M14 Art14) as (_ & Shadow14 & _ & _ & Img14).
  pose proof (LiveCall _ _ W13 M14 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] 24 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW13) as StoreM14.
  pose proof (LiveCall _ _ W13 M14 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); CB 8 (repeat (Z_to_bv 8 0) 8)] 384 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW13) as ShardM14.
  pose proof (LiveCall _ _ W13 M14 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W13) as Blk3M14.
  pose proof (LiveCall _ _ W13 M14 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W13) as Blk4M14.
  pose proof (LiveCall _ _ W13 M14 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W13) as Blk5M14.
  pose proof (LiveCall _ _ W13 M14 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W13) as Blk6M14.
  pose proof (LiveCall _ _ W13 M14 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk7W13) as Blk7M14.
  pose proof (LiveCall _ _ W13 M14 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk8W13) as Blk8M14.
  pose proof (LiveCall _ _ W13 M14 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk9W13) as Blk9M14.
  pose proof (LiveCall _ _ W13 M14 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk10W13) as Blk10M14.
  pose proof (LiveCall _ _ W13 M14 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk11W13) as Blk11M14.
  pose proof (LiveCall _ _ W13 M14 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk12W13) as Blk12M14.
  pose proof (LiveCall _ _ W13 M14 v13 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres14 Wm14 (ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk13W13) as Blk13M14.
  pose proof Mutex14 as Blk14M14.
  assert (ApS14 : wp_apbox (v14 + 40 <= v2 \/ v2 + 384 <= v14)) by exact (Apart14 v2 384 ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT14 : wp_apbox (v14 + 40 <= v1 \/ v1 + 24 <= v14)) by exact (Apart14 v1 24 ltac:(rewrite LiveN13; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_5; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s14_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk14.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact ShardM14.
    - exact StoreM14.
    - exact FrameM14.
    - exact Shadow14.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact R8.
    - exact R9.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact R13.
    - exact R14.
    - exact Img14.
    - exact (proj2 (af_acc_live RT AF S14 M14 v1 24 Art14 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v1 Al1).
    - exact Hi1.
    - exact Cap1.
    - exact Below1.
    - exact (proj2 (af_acc_live RT AF S14 M14 v2 384 Art14 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v2 Al2).
    - exact Hi2.
    - exact Cap2.
    - exact Below2.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi14. }
  apply cps_AST_ex. intros W14. apply cps_AST_pure.
  intros (MuW14 & WmW14 & MiW14 & ShardW14 & StoreW14 & ShadowW14).
  assert (InW14 : forall x, ~ outside [(v2 + 376, v2 + 384); (v1 + 8, v1 + 16)] x -> in_live [(v2, 384); (v1, 24)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. assert (Cases : v2 + 376 <= x < v2 + 384 \/ v1 + 8 <= x < v1 + 16) by lia.
    split; [destruct Cases; [exists v2, 384; split; [left; reflexivity| lia]| exists v1, 24; split; [right; left; reflexivity| lia]]| lia]. }
  pose proof (ArtWalk S14 M14 W14 _ Art14 Sp0N14 MuW14 WmW14 ltac:(intros x Out; left; destruct (InW14 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN14; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW14.
  pose proof (AgreeWalk M14 W14 _ AgrM14 MuW14 ltac:(intros x Out; pose proof (InW14 x Out); lia)) as AgrW14.
  pose proof (EnvWalk M14 W14 _ _ Env14 MuW14 ltac:(intros x Out; pose proof (InW14 x Out); lia)) as EnvW14.
  pose proof (PresWalk S14 M14 M14 W14 [(v14, 40); (v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art14 LiveN14 FramesN14 Sp0N14 ltac:(repeat constructor; cbn; lia) PresM14 MuW14
                ltac:(intros x Out; right; destruct (InW14 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg])) as PresW14.
  pose proof (wg_keep_seg _ M14 W14 _ _ FrameM14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; destruct (outside_dec [(v2 + 376, v2 + 384); (v1 + 8, v1 + 16)] x) as [O|O]; [exact O| pose proof (InW14 x O); lia])) as FrameW14.
  pose proof (stk_munch _ M14 W14 lo (SP + -64) Stk14 MuW14 WmW14 ltac:(intros x Rg; destruct (outside_dec [(v2 + 376, v2 + 384); (v1 + 8, v1 + 16)] x) as [O|O]; [exact O| pose proof (InW14 x O); lia])) as StkW14.
  pose proof (wmono_trans asegs m M14 W14 WmAllM14 WmW14) as WmAllW14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk3M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS3 ApT3; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk3W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk4M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS4 ApT4; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk4W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk5M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS5 ApT5; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk5W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk6M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS6 ApT6; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk6W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk7M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS7 ApT7; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk7W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk8M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS8 ApT8; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk8W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk9M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS9 ApT9; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk9W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk10M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS10 ApT10; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk10W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk11M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS11 ApT11; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk11W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk12M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS12 ApT12; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk12W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk13M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS13 ApT13; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk13W14.
  pose proof (wg_keep_seg _ M14 W14 _ _ Blk14M14 MuW14 WmW14 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApS14 ApT14; unfold wp_apbox in *; cbn [outside]; repeat split; lia)) as Blk14W14.
  clear dependent M14. clear dependent W13. clear dependent S13.

  (* call 15: CRYPTO_THREAD_lock_new at SITE_ossl_method_store_new_6 *)
  eapply cps_seq.
  { eapply cps_AST_conseq; [eapply C_lock_new| intros ms Ems; exact (eq_sym Ems)| intros mo Hmo; exact Hmo].
    - exact Fdfs.
    - exact Mst.
    - exact TpVal.
    - exact ArtW14.
    - exact MiW14.
    - exact (CallOkAt S14 W14 StkW14 Sp0N14).
    - rewrite SpBelow. unfold RT_STACK in *. lia.
    - exact (proj1 (Chain S14 W14 SITE_ossl_method_store_new_6 e_lock_new CgN14 AgrW14 FrameW14 ltac:(unfold SITE_ossl_method_store_new_6; lia) Site6 ToLock6)).
    - exact (proj2 (Chain S14 W14 SITE_ossl_method_store_new_6 e_lock_new CgN14 AgrW14 FrameW14 ltac:(unfold SITE_ossl_method_store_new_6; lia) Site6 ToLock6)).
    - exact (LockCg S14 CgN14).
    - rewrite FramesN14. exact FramesOk.
    - rewrite LiveN14, length_app. cbn [length]. unfold LIVE_MAX in *. lia.
    - rewrite CreditN14. lia.
    - exact EnvW14. }
  apply cps_ex. intros S15. apply cps_ex. intros v15. apply cps_pure.
  intros (Live15 & Frames15 & Sp015 & Credit15 & Pos15 & Al15 & Top15 & Cg15).
  unfold ASTA. apply cps_AST_ex. intros M15. apply cps_AST_pure.
  intros ((Art15 & Mi15 & Wm15 & Stk15) & Pres15 & Env15 & Mutex15 & Acc15).
  rewrite SpBelow in Pres15, Stk15.
  unfold ret_st. apply cps_AST_ex; intros j15_0. apply cps_AST_ex; intros j15_1. apply cps_AST_ex; intros j15_2. apply cps_AST_ex; intros j15_3. apply cps_AST_ex; intros j15_4. apply cps_AST_ex; intros j15_5. apply cps_AST_ex; intros j15_6. apply cps_AST_ex; intros j15_7. apply cps_AST_ex; intros j15_8. apply cps_AST_ex; intros j15_9. apply cps_AST_ex; intros j15_10. apply cps_AST_ex; intros j15_11. apply cps_AST_ex; intros j15_12. apply cps_AST_ex; intros j15_13. apply cps_AST_ex; intros j15_14. apply cps_AST_ex; intros j15_15.
  assert (LiveN15 : rt_live RT S15 = [(v15, 40); (v14, 40); (v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] ++ rt_live RT Σ) by (rewrite Live15, LiveN14; reflexivity).
  assert (FramesN15 : rt_frames RT S15 = rt_frames RT Σ) by (rewrite Frames15; exact FramesN14).
  assert (Sp0N15 : rt_sp0 RT S15 = rt_sp0 RT Σ) by (rewrite Sp015; exact Sp0N14).
  assert (CgN15 : rt_cg RT S15 = rt_cg RT Σ) by (rewrite Cg15; exact CgN14).
  assert (CreditN15 : rt_credit RT S15 = rt_credit RT Σ - 9) by (rewrite Credit15, CreditN14; repeat match goal with |- context [mcost ?x] => replace (mcost x) with 0 by (vm_compute; reflexivity) end; lia).
  pose proof (Fresh S15 M15 v15 40 _ Art15 Live15 Sp0N15 ltac:(lia)) as (FAcc15 & Hi15 & Cap15 & Below15 & Apart15).
  assert (R15 : 0 <= v15 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  pose proof (FrameCall _ _ W14 M15 FrameW14 Pres15 Wm15) as FrameM15.
  pose proof (AgreeCall _ _ W14 M15 AgrW14 Pres15) as AgrM15.
  pose proof (PresCall S14 [(v14, 40); (v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] W14 M15 LiveN14 FramesN14 PresW14 Pres15) as PresM15.
  pose proof (wmono_trans asegs m W14 M15 WmAllW14 Wm15) as WmAllM15.
  pose proof (af_client_consts RT AF S15 M15 Art15) as (_ & Shadow15 & _ & _ & Img15).
  pose proof (LiveCall _ _ W14 M15 v1 [C8 a0; C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8)] 24 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) StoreW14) as StoreM15.
  pose proof (LiveCall _ _ W14 M15 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); C8 (Z_to_bv 64 v14)] 384 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) ShardW14) as ShardM15.
  pose proof (LiveCall _ _ W14 M15 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk3W14) as Blk3M15.
  pose proof (LiveCall _ _ W14 M15 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk4W14) as Blk4M15.
  pose proof (LiveCall _ _ W14 M15 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk5W14) as Blk5M15.
  pose proof (LiveCall _ _ W14 M15 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk6W14) as Blk6M15.
  pose proof (LiveCall _ _ W14 M15 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk7W14) as Blk7M15.
  pose proof (LiveCall _ _ W14 M15 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk8W14) as Blk8M15.
  pose proof (LiveCall _ _ W14 M15 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk9W14) as Blk9M15.
  pose proof (LiveCall _ _ W14 M15 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk10W14) as Blk10M15.
  pose proof (LiveCall _ _ W14 M15 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk11W14) as Blk11M15.
  pose proof (LiveCall _ _ W14 M15 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)] 32 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk12W14) as Blk12M15.
  pose proof (LiveCall _ _ W14 M15 v13 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk13W14) as Blk13M15.
  pose proof (LiveCall _ _ W14 M15 v14 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) 40 Pres15 Wm15 (ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))) ltac:(vm_compute; discriminate) ltac:(lia) Blk14W14) as Blk14M15.
  pose proof Mutex15 as Blk15M15.
  assert (ApS15 : wp_apbox (v15 + 40 <= v2 \/ v2 + 384 <= v15)) by exact (Apart15 v2 384 ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))).
  assert (ApT15 : wp_apbox (v15 + 40 <= v1 \/ v1 + 24 <= v15)) by exact (Apart15 v1 24 ltac:(rewrite LiveN14; cbn [In app]; repeat (first [left; reflexivity| right]))).
  eapply cps_seq.
  { apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PmStable|].
    intros ms ->. rewrite ret_pc_even by (unfold SITE_ossl_method_store_new_6; first [lia | reflexivity]).
    eapply (ossl_method_store_new_s15_walk ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); fold SP.
    - exact Stk15.
    - lia.
    - exact LoHigh.
    - exact SpCap.
    - exact StoreM15.
    - exact ShardM15.
    - exact FrameM15.
    - exact Shadow15.
    - exact R1.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R5.
    - exact R6.
    - exact R7.
    - exact R8.
    - exact R9.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact R13.
    - exact R14.
    - exact R15.
    - exact Img15.
    - exact (proj2 (af_acc_live RT AF S15 M15 v1 24 Art15 (ltac:(rewrite LiveN15; cbn [In app]; repeat (first [left; reflexivity| right]))))).
    - exact (wg_mod16_8 v1 Al1).
    - exact Hi1.
    - exact Cap1.
    - exact Below1.
    - exact ApT2.
    - unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia.
    - exact Mi15. }

  (* the store goes back to the caller *)
  intros T c Pre Kont. apply Kont.
  exists S15, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15.
  split.
  2: { rewrite LiveN15. split; [reflexivity|]. split; [exact FramesN15|]. split; [exact Sp0N15|]. split; [rewrite CreditN15; lia|].
       split; [|exact CgN15].
       constructor; [exact (conj Pos15 (conj Al15 Top15))|]. constructor; [exact (conj Pos14 (conj Al14 Top14))|]. constructor; [exact (conj Pos13 (conj Al13 Top13))|]. constructor; [exact (conj Pos12 (conj Al12 Top12))|]. constructor; [exact (conj Pos11 (conj Al11 Top11))|]. constructor; [exact (conj Pos10 (conj Al10 Top10))|]. constructor; [exact (conj Pos9 (conj Al9 Top9))|]. constructor; [exact (conj Pos8 (conj Al8 Top8))|]. constructor; [exact (conj Pos7 (conj Al7 Top7))|]. constructor; [exact (conj Pos6 (conj Al6 Top6))|]. constructor; [exact (conj Pos5 (conj Al5 Top5))|]. constructor; [exact (conj Pos4 (conj Al4 Top4))|]. constructor; [exact (conj Pos3 (conj Al3 Top3))|]. constructor; [exact (conj Pos2 (conj Al2 Top2))|]. constructor; [exact (conj Pos1 (conj Al1 Top1))|]. constructor. }
  eapply AST_conseq; [exact Pre| |intros mo Hmo; exact Hmo].
  intros ms (W15 & Ret & MuW15 & WmW15 & MiW15 & StkW15 & StoreW15 & ShadowW15).
  change (bv_unsigned sp) with SP in StkW15.
  assert (InW15 : forall x, ~ outside [(v1 + 16, v1 + 24)] x -> in_live [(v1, 24)] x /\ 0x10007fff8000 <= x /\ x < lo).
  { intros x Out. cbn [outside] in Out. split; [exists v1, 24; split; [left; reflexivity| lia]| lia]. }
  pose proof (ArtWalk S15 M15 W15 _ Art15 Sp0N15 MuW15 WmW15 ltac:(intros x Out; left; destruct (InW15 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [rewrite LiveN15; apply in_or_app; left; cbn [In] in InL |- *; tauto| exact Rg])) as ArtW15.
  exists W15. split; [rewrite Ret; do 16 eexists; reflexivity|].
  split; [split; [exact ArtW15|]; split; [exact MiW15|]; split; [exact (wmono_trans asegs m M15 W15 WmAllM15 WmW15)| exact StkW15]|].
  split; [exact (PresWalk S15 M15 M15 W15 [(v15, 40); (v14, 40); (v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] _ Art15 LiveN15 FramesN15 Sp0N15 ltac:(repeat constructor; cbn; lia) PresM15 MuW15
            ltac:(intros x Out; right; destruct (InW15 x Out) as ((p & q & InL & Rg) & _ & _); exists p, q; split; [cbn [In] in InL |- *; tauto| exact Rg]))|].
  split; [exact (EnvWalk M15 W15 _ _ Env15 MuW15 ltac:(intros x Out; pose proof (InW15 x Out); lia))|].
  assert (AccAt : forall q k, In (q, k) [(v15, 40); (v14, 40); (v13, 40); (v12, 32); (v11, 40); (v10, 40); (v9, 32); (v8, 40); (v7, 40); (v6, 32); (v5, 40); (v4, 40); (v3, 32); (v2, 384); (v1, 24)] -> acc asegs W15 q k).
  { intros q k InN. apply (proj2 (af_acc_live RT AF S15 W15 q k ArtW15 ltac:(rewrite LiveN15; apply in_or_app; left; exact InN))). }
  split; [exact StoreW15|]. split; [apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])|].
  split; [exact (wg_keep_seg _ M15 W15 _ _ ShardM15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize Nat.add Z.of_nat] in Rg; clear - Rg ApT2; unfold wp_apbox in *; cbn [outside]; repeat split; lia))|].
  split; [apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])|].
  split.
  { constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk3M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT3; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk6M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT6; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk9M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT9; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk12M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT12; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor. }
  { constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk4M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT4; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk5M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT5; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk7M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT7; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk8M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT8; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk10M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT10; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk11M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT11; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk13M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT13; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk14M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT14; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor; [split; [exact (wg_keep_seg _ M15 W15 _ _ Blk15M15 MuW15 WmW15 ltac:(intros x Rg; cbn [cells_size csize mutex_cells Nat.add Z.of_nat] in Rg; clear - Rg ApT15; unfold wp_apbox in *; cbn [outside]; repeat split; lia))| apply AccAt; cbn [In]; repeat (first [left; reflexivity| right])]|]. constructor. }
Qed.
End ossl_method_store_new_cps.
