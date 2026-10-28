(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Th_tsd Th_key Th_once Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_ukit.
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
    tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    ro_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] ->
    ro_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 T)] -> 0 <= T -> T + 8 * k + 8 <= lo ->
    ro_cells asegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0x10007fff8000 <= MK -> MK mod 8 = 0 -> MK + 72 <= lo -> acc asegs m MK 72 ->
    ro_cells asegs m (MK + 8 * id) [C8 (Z_to_bv 64 SA)] -> 0x10007fff8000 <= SA -> SA mod 8 = 0 -> SA + 32 <= lo -> acc asegs m SA 32 ->
    rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) ->
    0x10007fff8000 <= NODES -> NODES mod 8 = 0 -> NODES + 128 <= lo -> acc asegs m NODES 128 ->
    rw_cells asegs m NODES [C8 oldv] -> (SA + 32 <= NODES \/ NODES + 128 <= SA) ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t1' a1' a2' a3' : word) (top' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (NODES, NODES + 8)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 (bv_unsigned ne + sa_delta a2 oldv)) (Z_to_bv 64 NODES))
                 /\ rw_cells asegs m' NODES [C8 a2])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f6804) fc None m (seg_rom asegs)).

Theorem T_set_local_ex_steady_proof : T_set_local_ex_steady_stmt.
Proof.
  unfold T_set_local_ex_steady_stmt, sa_hdr, g_shadow_memory_dynamic_address, SHB. intros until oldv.
  intros -> -> HID -> OC KC HK KSB HSB UT SHC TSD T0 TLO MKC MKHI MKAL MKLO ACCM SLOT SAHI SAAL SALO ACCS HC NHI NAL NLO ACCN VC DISJ ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (NODES, NODES + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Pk := T + 8 * k) in *. set (Pi := MK + 8 * id) in *.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 9 zstep. zstep. do 3 zstep. do 2 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo);
    [exact OC | exact ST | lia | lia | lia | exact MI |].
  cbv delta [mkR].
  do 2 zstep. if_cases K8; zify_cond K8. { exfalso. lia. }
  zstep. th_if_lit.
  do 2 zstep. zstep.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k sb (Z_to_bv 64 MK));
    [exact KC | exact HK | reflexivity | lia | lia | exact KSB | exact HSB | exact (ut_munch _ m _ UT MU HWU) | exact SHC | exact TSD | lia | lia | exact MKC | lia | lia
    | eassumption | lia | lia | lia | assumption |].                                        (* [comment removed for export] *)
  cbv delta [mkR].
  zstep. zstep. if_cases KM; zify_cond KM. { exfalso. lia. }
  do 2 zstep.
  rewrite (t_scale8 id) by lia. fold Pi. assert (HPi : MK <= Pi /\ Pi + 8 <= MK + 72) by (unfold Pi; lia).
  assert (PIAL : Pi mod 8 = 0) by (unfold Pi; clear - MKAL HID; lia).
  do 2 zstep. zstep. zstep. th_if_lit.
  zstep. zstep. if_cases KS; zify_cond KS. 2:{ exfalso. lia. }                              (* [comment removed for export] *)
  zstep. zstep. th_if_lit. zstep. do 2 zstep. do 7 zstep. th_release FR (bv_unsigned sp). zstep. zstep.
  eapply evt_mono.
  { eapply (T_sa_set_leaf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo SA 0 NODES pad top ne oldv);
      first [reflexivity | eassumption | lia | exact (acc_munch_sh _ m _ _ _ ACCS MU HWS ltac:(lia) ltac:(lia)) | exact (acc_munch_sh _ m _ _ _ ACCN MU HWS ltac:(lia) ltac:(lia))
            | exact (ut_munch _ m _ UT MU HWU) | rewrite Z.mul_0_r, Z.add_0_r; eassumption ]. }
  intros ms' (a1' & a2' & a3' & top' & m' & -> & MU' & WM' & MI' & HT' & ST' & HC' & VC'). cbv delta [mkR].
  replace (NODES + 8 * 0) with NODES in VC' by lia.
  do 6 eexists. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']]; intros xx Hxx; cbn [outside] in *; lia|].
  split; [exact (wmono_trans _ _ _ _ WM WM')|]. split; [exact MI'|]. split; [exact HT'|]. split; [exact ST'|]. exact (conj HC' VC').
Qed.
