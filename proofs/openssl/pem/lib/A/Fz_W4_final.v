(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Arr SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_W4_kit Fz_W4_defs Fz_ukit Fz_W4_block.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition W4_decode_final_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C T OL lo num : Z) (K : nat) (ln old : word) (ed bs0 : list byte),
    a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 T -> a2 = Z_to_bv 64 OL ->
    rw_cells asegs m C (ectx_cells (Z_to_bv 64 num) ed ln z64) -> length ed = 80%nat -> 0 <= num <= 64 ->
    0 < C -> C mod 8 = 0 -> C + 92 <= lo -> acc asegs m C 92 -> (C + 92 <= 0x10000 \/ 0xbc6000 <= C) -> (C + 92 <= 0x7fff8000 \/ 0x10007fff8000 <= C) ->
    rw_cells asegs m T [CB K bs0] -> 0 < T -> 3 * (num / 4) <= Z.of_nat K -> T + Z.of_nat K <= lo -> acc asegs m T (Z.of_nat K) ->
    (T + Z.of_nat K <= 0x10000 \/ 0xbc6000 <= T) -> (T + Z.of_nat K <= 0x7fff8000 \/ 0x10007fff8000 <= T) ->
    rw_cells asegs m OL [C4 old] -> 0 < OL -> OL mod 4 = 0 -> acc asegs m OL 4 -> (OL + 4 <= lo \/ bv_unsigned sp <= OL) -> OL + 4 <= 2 ^ 47 ->
    (OL + 4 <= 0x10000 \/ 0xbc6000 <= OL) -> (OL + 4 <= 0x7fff8000 \/ 0x10007fff8000 <= OL) ->
    (C + 92 <= T \/ T + Z.of_nat K <= C) -> (C + 92 <= OL \/ OL + 4 <= C) -> (T + Z.of_nat K <= OL \/ OL + 4 <= T) ->
    acc asegs m 672160 128 ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (rv dl num' : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (bs' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (C, C + 4); (T, T + 3 * (num / 4)); (OL, OL + 4)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ ((rv = 1 /\ num' = 0 /\ 0 <= dl <= 3 * (num / 4)) \/ (rv = -1 /\ num' = num /\ dl = 0))
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' C (ectx_cells (Z_to_bv 64 num') ed ln z64)
                 /\ rw_cells asegs m' T [CB K bs']
                 /\ rw_cells asegs m' OL [C4 (Z_to_bv 64 dl)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_EVP_DecodeFinal) fc None m (seg_rom asegs)).

Theorem W4_decode_final_proof : W4_decode_final_stmt.
Proof.
  unfold W4_decode_final_stmt, ectx_cells, g_shadow_memory_dynamic_address, SHB, e_EVP_DecodeFinal. intros until bs0.
  intros -> -> -> CTX LED HN HC CAL CLO ACC_C CIM CSH DST HT0 HK TLO ACC_T TIM TSH OLC HO0 OAL ACC_O OLO OTOP OIM OSH S1 S2 S3 ACC_B UT SHC ST LO0 LO HTOP MI.
  pose proof (rw_cells_bound _ _ _ _ CTX) as CB. cbn [cells_size csize Nat.add] in CB.
  pose proof (rw_cells_bound _ _ _ _ DST) as TB. cbn [cells_size csize Nat.add] in TB.
  pose proof (rw_cells_bound _ _ _ _ OLC) as OB. cbn [cells_size csize Nat.add] in OB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HD : 0 <= num / 4) by (apply Z.div_pos; lia).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (C, C + 4); (T, T + 3 * (num / 4)); (OL, OL + 4)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(bv_unsigned sp - 128, bv_unsigned sp); (C, C + 4); (T, T + 3 * (num / 4)); (OL, OL + 4)]%Z) by (clear - CB TB OB RSP HD HN LO0 LO HTOP CLO TLO OLO CIM TIM OIM HK; ut_fp_lia).
  assert (HWS : sh_fp [(bv_unsigned sp - 128, bv_unsigned sp); (C, C + 4); (T, T + 3 * (num / 4)); (OL, OL + 4)]%Z) by (clear - CB TB OB RSP HD HN LO0 LO HTOP CLO TLO OLO CSH TSH OSH HK; sh_fp_lia).
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 9 ths.
  (* [comment removed for export] *)
  zstep.
  do 3 zstep.
  chk_byte ACC_O OL 4. do 4 zstep. zstep. chk_join 0x32007c 10 12. ths.
  (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small num) by lia.
  do 2 zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    do 9 zstep.
    th_release FR (bv_unsigned sp). zstep.
    apply evt_done. exists 1, 0, 0. do 14 eexists. exists bs0. eexists.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [left; lia|]. split; [exact ST|].
    replace num with 0 in CTX by lia. split; [exact CTX|]. split; [exact DST | exact OLC].
  - do 5 zstep.
    pose proof (proj1 CTX : ro_cells asegs _ C (ectx_cells (Z_to_bv 64 num) ed ln z64)) as CRO.
    tcall (dblock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C T K num (-1) (Z_to_bv 64 num) ln ed bs0 lo).
    1-5: reflexivity. 1: exact CRO. 1: exact LED. 1-3: first [assumption | lia].
    1: exact (acc_munch_sh _ m _ _ _ ACC_C MU HWS ltac:(lia) ltac:(lia)).
    1: exact DST. 1: exact HT0. 1: lia.
    1: exact (acc_munch_sh _ m _ _ _ ACC_T MU HWS ltac:(lia) ltac:(lia)).
    1-6: first [assumption | lia].
    1: exact (acc_munch_sh _ m _ _ _ ACC_B MU HWS ltac:(lia) ltac:(lia)).
    1: exact (ut_munch _ m _ UT MU HWU).
    1: unfold g_shadow_memory_dynamic_address, SHB; exact SHC.
    1: exact ST. 1-3: lia. 1: exact MI.
    clear PC1. cbv beta delta [mkR].
    destruct PC as [-> | PC].
    + (* [comment removed for export] *)
      zstep. th_if_lit.
      do 9 zstep. th_release FR (bv_unsigned sp). zstep.
      apply evt_done. exists (-1), 0, num. do 14 eexists. eexists. eexists.
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [right; lia|].
      split; [eassumption|]. split; [exact CTX|]. split; [exact POST | exact OLC].
    + zstep. if_cases KD; zify_cond KD; signed_lits_in KD. { exfalso. lia. }
      (* [comment removed for export] *)
      zstep. zstep. th_if_lit. ths.
      (* [comment removed for export] *)
      chk_byte ACC_O OL 4. zstep. zstep. chk_join 0x3200c8 11 12. zstep.
      do 10 zstep. th_release FR (bv_unsigned sp). zstep.
      apply evt_done. exists 1, x, 0. do 14 eexists. eexists. eexists.
      split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [left; lia|].
      split; [eassumption|]. split; [exact CTX|]. split; [exact POST | exact OLC].
Qed.
