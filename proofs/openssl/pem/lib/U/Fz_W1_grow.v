(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memset. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_W1_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition W1_grow_fit_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BM D len max len' : Z) (flw : word) (junk : list byte),
    a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 len' -> 0 < BM -> BM mod 8 = 0 -> 0 < D -> 0 <= len -> len < len' -> len' <= max -> max < 2 ^ 31 -> D + max < 2 ^ 63 ->
    rw_cells usegs m BM (bufmem_cells len D max flw) -> length junk = Z.to_nat max -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 48 -> BM + 32 <= lo -> D + max <= lo ->
    (D + max <= BM \/ BM + 32 <= D) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 len') a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + max); (BM, BM + 8)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' BM (bufmem_cells len' D max flw)
                 /\ length junk' = Z.to_nat max /\ rw_cells usegs m' D [CB (Z.to_nat max) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x116dcc) fc None m (seg_rom usegs)).

Theorem W1_grow_fit_proof : W1_grow_fit_stmt.
Proof.
  unfold W1_grow_fit_stmt, bufmem_cells. intros until junk.
  intros -> -> HBM ALBM HD HLEN HLT HFIT HMAX HD63 BMC LJ DBLK ST LO0 LO SBM SD APDM MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + max); (BM, BM + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  destruct (rw_cells_CB_split_at usegs m D (Z.to_nat max) junk (Z.to_nat len) ltac:(lia) DBLK) as [DA DBC].
  destruct (rw_cells_CB_split_at usegs m (D + Z.of_nat (Z.to_nat len)) (Z.to_nat max - Z.to_nat len) (skipn (Z.to_nat len) junk) (Z.to_nat (len' - len)) ltac:(lia) DBC) as [DB DC].
  rewrite Z2Nat.id in DB, DC by lia. rewrite Z2Nat.id in DC by lia. clear DBC DBLK.
  ths. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 6 ths.
  ths. ubs_if. ths. ths. ths. ubs_if.
  ths. ths. ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  ths. ths. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths. ths. rewrite ?(unsigned_lit D), ?(unsigned_lit len) by lia.
  ths. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit in KO by lia. lia. }
  ths. ths. ths. ths.
  rewrite ?v_sltu_b2z, ?v_sltiu_b2z. rewrite ?(unsigned_lit 0), ?(unsigned_lit D), ?(unsigned_lit (len + D)) by lia. try change (bv_wrap 64 1) with 1.
  replace (0 <? D) with true by (symmetry; apply Z.ltb_lt; lia). replace (len + D <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. th_if_lit.
  ths. ths. ths.
  rewrite ?(unsigned_lit len) by lia. replace (len' + - len) with (len' - len) by lia.
  replace (len + D) with (D + len) by lia.
  ths.
  tcall (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (D + len) 0 (len' - len) _).
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  ths. ths. do 5 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths.
  lazymatch goal with Hz : rw_cells _ ?mm (D + len) [CB _ ?zz] |- _ =>
    pose proof (rw_cells_CB_join usegs mm D _ _ _ _ ltac:(eassumption) ltac:(rewrite Z2Nat.id by lia; exact Hz)) as J1 end.
  lazymatch goal with Hc : rw_cells _ ?mm (D + len + (len' - len)) _ |- _ =>
    pose proof (rw_cells_CB_join usegs mm D _ _ _ _ J1 ltac:(rewrite Nat2Z.inj_add, !Z2Nat.id by lia; rewrite Z.add_assoc; exact Hc)) as J2 end.
  replace (Z.to_nat len + Z.to_nat (len' - len) + (Z.to_nat max - Z.to_nat len - Z.to_nat (len' - len)))%nat with (Z.to_nat max) in J2 by lia.
  apply evt_done. do 14 eexists. eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [| exact J2].
  rewrite !length_app, repeat_length, firstn_length, !skipn_length. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bufmem_bcells (len data max sec : Z) : list cell :=
  [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 max); C1 (Z_to_bv 8 sec); CB 7 (repeat (Z_to_bv 8 0) 7)].

Definition W1_grow_tail_stmt : Prop :=
  forall (x1 gp tp t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SP BM D' len dold mold n len' sec : Z) (junk : list byte) (j8 : list byte) (rao s0o s1o s2o s3o : word),
    0 < BM -> 0 < D' -> 0 <= len -> len < len' -> len' <= n -> n < 2 ^ 31 -> D' + n < 2 ^ 63 ->
    rw_cells usegs m BM (bufmem_bcells len dold mold sec) -> length junk = Z.to_nat n -> rw_cells usegs m D' [CB (Z.to_nat n) junk] ->
    rw_cells usegs m (SP + -48) [CB 8 j8; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
    stk usegs m lo (SP + -48) -> 0 <= lo -> lo <= SP - 48 -> SP < 2 ^ 64 -> BM + 32 <= lo -> D' + n <= lo ->
    (D' + n <= BM \/ BM + 32 <= D') ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk' : list byte) (m' : mem),
                 ms' = MS (mkR rao (Z_to_bv 64 SP) gp tp t0' t1' t2' s0o s1o (Z_to_bv 64 len') a1' a2' a3' a4' a5' a6' a7' s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc rao) fc None m' (seg_rom usegs)
                 /\ munch [(SP - 48, SP); (D', D' + n); (BM, BM + 24)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo SP
                 /\ rw_cells usegs m' BM (bufmem_bcells len' D' n sec)
                 /\ length junk' = Z.to_nat n /\ rw_cells usegs m' D' [CB (Z.to_nat n) junk'])
        (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 x8 (Z_to_bv 64 len') (Z_to_bv 64 D') a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 n)
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x116ed8) fc None m (seg_rom usegs)).

Theorem W1_grow_tail_proof : W1_grow_tail_stmt.
Proof.
  unfold W1_grow_tail_stmt, bufmem_bcells. intros until s3o.
  intros HBM HD HLEN HLT HFIT HN HD63 BMC LJ DBLK FR ST LO0 LO HSP SBM SD APDM MI.
  pose proof (munch_refl [(SP - 48, SP); (D', D' + n); (BM, BM + 24)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  destruct (rw_cells_CB_split_at usegs m D' (Z.to_nat n) junk (Z.to_nat len) ltac:(lia) DBLK) as [DA DBC].
  destruct (rw_cells_CB_split_at usegs m (D' + Z.of_nat (Z.to_nat len)) (Z.to_nat n - Z.to_nat len) (skipn (Z.to_nat len) junk) (Z.to_nat (len' - len)) ltac:(lia) DBC) as [DB DC].
  rewrite Z2Nat.id in DB, DC by lia. rewrite Z2Nat.id in DC by lia. clear DBC DBLK.
  cbv beta delta [mkR].
  ths. ths. ths. ths.
  ths. if_cases KO; zify_cond KO. { exfalso. rewrite ?unsigned_lit, ?zb_lxor_ones in KO by lia. lia. }
  ths. ths.
  rewrite (unsigned_lit len) by lia. replace (len' + - len) with (len' - len) by lia.
  ths. ths.
  tcall (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (D' + len) 0 (len' - len) _).
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  ths. ths. do 5 ths.
  th_release FR SP.
  ths. ths.
  lazymatch goal with Hz : rw_cells _ ?mm (D' + len) [CB _ ?zz] |- _ =>
    pose proof (rw_cells_CB_join usegs mm D' _ _ _ _ ltac:(eassumption) ltac:(rewrite Z2Nat.id by lia; exact Hz)) as J1 end.
  lazymatch goal with Hc : rw_cells _ ?mm (D' + len + (len' - len)) _ |- _ =>
    pose proof (rw_cells_CB_join usegs mm D' _ _ _ _ J1 ltac:(rewrite Nat2Z.inj_add, !Z2Nat.id by lia; rewrite Z.add_assoc; exact Hc)) as J2 end.
  replace (Z.to_nat len + Z.to_nat (len' - len) + (Z.to_nat n - Z.to_nat len - Z.to_nat (len' - len)))%nat with (Z.to_nat n) in J2 by lia.
  apply evt_done. do 14 eexists. eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [| exact J2].
  rewrite !length_app, repeat_length, firstn_length, !skipn_length. lia.
Qed.
