(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition tpA : Z := 0xba3ef0.
Definition pth_tsd : Z := 0xba3e98.          (* [comment removed for export] *)
Definition g_pthread_tsd_main : Z := 0xbc5298.  (* [comment removed for export] *)
Definition g_tsd_key_inited : Z := 0x66c3a0.
Definition g_tsd_key : Z := 0x66c3a4.

(* [comment removed for export] *)
Lemma pthread_getspecific_spec : forall ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (tsdp k v : Z),
  rw_cells asegs m pth_tsd [C8 (Z_to_bv 64 tsdp)] ->
  rw_cells asegs m (tsdp + 8 * k) [C8 (Z_to_bv 64 v)] ->
  (0 <= k < 2^32)%Z -> (0 <= tsdp)%Z -> (tsdp + 8 * k + 8 <= 2^64)%Z -> (0 <= v < 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x529438) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros TS TK HK HT HTK HV MI. unfold tpA, pth_tsd in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 5 zstep.
  replace (Z_to_bv 64 (tsdp + (k ≪ 32 mod 18446744073709551616) ≫ 29)) with (Z_to_bv 64 (tsdp + 8 * k)).
  2:{ f_equal. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
      rewrite Z.shiftr_div_pow2 by lia. replace (k * 2 ^ 32)%Z with ((8 * k) * 2 ^ 29)%Z by lia.
      rewrite Z.div_mul by lia. reflexivity. }
  assert (HQ : (0 <= tsdp + 8 * k)%Z) by lia. clear HK. set (q := (tsdp + 8 * k)%Z) in *. clearbody q.
  do 2 zstep.
  finish.
Qed.

(* [comment removed for export] *)
Definition tsd_cells (TCX : Z) (m : mem) : Prop :=
  rw_cells asegs m g_tsd_key_inited [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m g_tsd_key [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m pth_tsd [C8 (Z_to_bv 64 g_pthread_tsd_main)]
  /\ rw_cells asegs m g_pthread_tsd_main [C8 (Z_to_bv 64 TCX)].

(* [comment removed for export] *)
Lemma asan_tsd_get_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (TCX : Z),
  tsd_cells TCX m -> (0 <= TCX < 2^64)%Z ->
  mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc TCX m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c56bc) fc None m (seg_rom asegs)).
Proof.
  intros until TCX. intros (KI & K & TS & T0) HT MI.
  unfold g_tsd_key_inited, g_tsd_key in *.
  do 4 zstep. if_false.
  do 2 zstep.
  rewrite (sx32_small_A 0) by lia.
  eapply (pthread_getspecific_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m g_pthread_tsd_main 0 TCX);
    try eassumption; unfold g_pthread_tsd_main; try lia.
Qed.

(* [comment removed for export] *)
Definition thread_cells (TCX T : Z) (m : mem) : Prop :=
  tsd_cells TCX m /\ rw_cells asegs m (TCX + 0x98) [C8 (Z_to_bv 64 T)].

Definition frame_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v : Z) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma get_current_thread_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (TCX T lo : Z),
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 2^64)%Z -> (0 <= T < 2^64)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z ->
  (TCX + 0xa0 <= lo \/ bv_unsigned sp <= TCX + 0x98)%Z ->
  (0xbc5778 <= lo)%Z ->
  mem_inv asegs m ->
  evt asegs (frame_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T
               [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1cd0c4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros [TS TT] HT0 HT1 HT ST LO SEP ILO MI.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  destruct TS as (KI & K & TS & T0).
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  carve_frame 16%nat ST.
  do 3 zstep.
  call asan_tsd_get_spec.
  1:{ unfold tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]. }
  1:{ lia. }
  1:{ assumption. }
  zstep.
  assert (C1 : bv_eqb (Z_to_bv 64 TCX) (Z_to_bv 64 0) = false).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  rewrite C1; cbv iota.
  do 4 zstep.
  release_frame FR ST (bv_unsigned sp). finish.
Qed.
