(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_T_once Fz_T_local Fz_T_sa Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_get_local_ex : Z := 0x1f66e4.
Definition G_TL_MASTER_ONCE : Z := 0xb9f500.    (* [comment removed for export] *)
Definition G_TL_MASTER_KEY : Z := 0xb9f520.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition T_get_local_ex_steady_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k MK SA LV NODES : Z) (sb : Z) (pad top ne v : word),
    a0 = Z_to_bv 64 3 -> a1 = Z_to_bv 64 1 ->
    ro_cells asegs m G_TL_MASTER_ONCE [C4 (Z_to_bv 64 2)] ->
    ro_cells asegs m G_TL_MASTER_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells asegs m (G_TL_MASTER_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
    ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> bv_unsigned tp <= lo ->
    ro_cells asegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 <= T -> T + 8 * k + 8 <= lo ->
    ro_cells asegs m (MK + 24) [C8 (Z_to_bv 64 SA)] -> acc asegs m MK 72 -> 0 < MK -> MK mod 8 = 0 -> MK + 72 <= lo ->
    ro_cells asegs m SA (sa_hdr (Z_to_bv 64 LV) pad top ne (Z_to_bv 64 NODES)) -> acc asegs m SA 32 -> 0 < SA -> SA mod 8 = 0 -> SA + 32 <= lo ->
    bv_unsigned ne <> 0 -> 0 <= LV < 2 ->
    ro_cells asegs m NODES [C8 v] -> acc asegs m NODES 128 -> 0 < NODES -> NODES mod 8 = 0 -> NODES + 128 <= lo ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t1' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_local_ex) fc None m (seg_rom asegs)).

Theorem T_get_local_ex_steady_proof : T_get_local_ex_steady_stmt.
Proof.
  unfold T_get_local_ex_steady_stmt, sa_hdr, g_shadow_memory_dynamic_address, SHB, e_get_local_ex, G_TL_MASTER_ONCE, G_TL_MASTER_KEY. intros until v.
  intros -> -> ONCE KEY HK KSB HSB TSD TP TPLO MKC T0 TLO SLOT ACCM MK0 MKAL MKLO SAC ACCS SA0 SAAL SALO HNE HLV VC ACCN N0 NAL NLO UT SHC ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-48) EU1.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  do 7 zstep. do 3 zstep.
  do 2 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo);
    [exact ONCE | exact ST | lia | lia | lia | exact MI |].
  cbv delta [mkR].
  do 2 zstep. if_cases K8; zify_cond K8. { exfalso. lia. }
  zstep. th_if_lit.
  do 2 zstep. zstep.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k sb (Z_to_bv 64 MK));
    [exact KEY | exact HK | reflexivity | lia | lia | exact KSB | exact HSB | exact (ut_munch _ m _ UT MU HWU) | exact SHC | exact TSD | lia | lia | exact MKC | lia | lia
    | eassumption | lia | lia | lia | assumption |].                                      (* [comment removed for export] *)
  cbv delta [mkR].
  zstep. if_cases KM; zify_cond KM. { exfalso. lia. }
  do 2 zstep.
  do 3 zstep. zstep. th_if_lit. zstep.
  zstep. if_cases KS; zify_cond KS. { exfalso. lia. }                                    (* [comment removed for export] *)
  zstep. do 5 zstep. th_release FR (bv_unsigned sp). zstep. zstep.
  eapply evt_mono.
  { eapply (T_sa_get_leaf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo SA 0 LV NODES pad top ne v);
      [reflexivity | lia | exact SAAL | lia | eassumption | exact (acc_munch_sh _ m _ _ _ ACCS MU HWS ltac:(lia) ltac:(lia)) | reflexivity | lia
      | pose proof (bv_unsigned_in_range 64 top); lia | exact HNE | exact HLV | lia | exact NAL | lia
      | rewrite Z.mul_0_r, Z.add_0_r; eassumption | exact (acc_munch_sh _ m _ _ _ ACCN MU HWS ltac:(lia) ltac:(lia))
      | exact (ut_munch _ m _ UT MU HWU) | exact SHC | eassumption | lia | lia | lia | assumption]. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & MU' & WM' & MI' & ST'). cbv delta [mkR].
  do 9 eexists. split; [reflexivity|].
  split; [| split; [exact (wmono_trans _ _ _ _ WM WM') | split; [exact MI' | exact ST']]].
  eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']]. intros xx Hxx. cbn [outside] in *. lia.
Qed.
