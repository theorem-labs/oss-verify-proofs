(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Th_tsd Th_key Th_once Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation MK_ONCE := (0xb9f500)%Z (only parsing).
Notation MK_KEY := (0xb9f520)%Z (only parsing).

Lemma t_scale8 : forall i, 0 <= i < 2 ^ 60 -> Z.shiftl i 3 = 8 * i.
Proof. intros i Hi. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

(* [comment removed for export] *)
Definition T_set_local_ex_steady_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k id MK SA NODES sb : Z) (pad top ne oldv : word),
  a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
  ro_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] ->
  ro_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
  ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> sb = 0 \/ sb = 4 ->
  ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp <= lo ->
  ro_cells asegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 <= T -> T + 8 * k + 8 <= lo ->
  0x10007fff8000 <= MK -> MK mod 8 = 0 -> MK + 72 <= lo -> acc asegs m MK 72 ->
  ro_cells asegs m (MK + 8 * id) [C8 (Z_to_bv 64 SA)] ->
  0x10007fff8000 <= SA -> SA mod 8 = 0 -> SA + 32 <= lo -> acc asegs m SA 32 ->
  rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) ->
  0x10007fff8000 <= NODES -> NODES mod 8 = 0 -> NODES + 128 <= lo -> acc asegs m NODES 128 ->
  rw_cells asegs m NODES [C8 oldv] -> (SA + 32 <= NODES \/ NODES + 128 <= SA) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs
    (fun ms' => exists (t1' a1' a2' a3' top' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (NODES, NODES + 8)] m m'
       /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
       /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 (bv_unsigned ne + sa_delta a2 oldv)) (Z_to_bv 64 NODES))
       /\ rw_cells asegs m' NODES [C8 a2])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f6804) fc None m (seg_rom asegs)).

Theorem T_set_local_ex_steady_proof : T_set_local_ex_steady_stmt.
Proof.
  unfold T_set_local_ex_steady_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo T k id MK SA NODES sb pad top ne oldv
    idA0 idRng ctxA1 onceC keyC keyRng keySh shOK tsdC tpRng slotT tLo tHi mkLo mkAl mkHi mkAcc mkSlot saLo saAl saHi saAcc saHdr
    ndLo ndAl ndHi ndAcc ndCell saNd imgU shadowBase stkM loLo loSp spHi invM.
  subst a0 a1.
  pose proof (bv_unsigned_in_range 64 sp) as spRng. unfold bv_modulus in spRng. cbn [Z.of_N] in spRng.
  remember (bv_unsigned sp) as S0 eqn:S0def.
  rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- S0def.
  assert (idU : bv_unsigned (Z_to_bv 64 id) = id) by (apply unsigned_lit; lia).
  assert (mkU : bv_unsigned (Z_to_bv 64 MK) = MK) by (apply unsigned_lit; lia).
  assert (saU : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
  unfold g_shadow_memory_dynamic_address, SHB in shadowBase. unfold sa_hdr in saHdr.
  pose proof (munch_refl [(S0 - 112, S0); (SA + 8, SA + 24); (NODES, NODES + 8)] m) as fpTrack.
  pose proof (wmono_refl asegs m) as wmTrack.
  assert (fpUT : ut_fp [(S0 - 112, S0); (SA + 8, SA + 24); (NODES, NODES + 8)]) by ut_fp_lia.
  assert (fpSH : sh_fp [(S0 - 112, S0); (SA + 8, SA + 24); (NODES, NODES + 8)]) by sh_fp_lia.
  carve_frame 64%nat stkM. rename FR into frame64.
  do 16 zstep. th_if_lit.
  do 6 zstep.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo);
    try first [lia | eassumption].
  do 2 zstep. if_false. zstep. th_if_lit.
  do 3 zstep.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k sb (Z_to_bv 64 MK));
    try first [lia | eassumption | eapply ut_munch; [exact imgU | exact fpTrack | exact fpUT]].
  do 2 zstep. if_false.
  do 4 zstep.
  rewrite (t_scale8 id) by lia. rewrite SFModel.land_W64, Z.mod_small by lia.
  remember (MK + 8 * id) as slotA eqn:slotDef.
  do 2 zstep. th_if_lit.
  do 2 zstep. if_true.
  do 2 zstep. th_if_lit.
  do 12 zstep.
  th_release frame64 S0.
  tcall (T_sa_set_leaf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo SA 0 NODES pad top ne oldv);
    try first [lia | reflexivity | eassumption | eapply ut_munch; [exact imgU | exact fpTrack | exact fpUT]].
  all: try (eapply acc_munch_sh; [eassumption | exact fpTrack | exact fpSH | lia | lia]).
  { rewrite Z.mul_0_r, Z.add_0_r. exact ndCell. }
  lazymatch goal with Hn : rw_cells _ _ (NODES + 8 * 0) _ |- _ => rewrite Z.mul_0_r, Z.add_0_r in Hn end.
  apply evt_done. do 6 eexists.
  refine (conj eq_refl _).
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
