(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SysStep Bytes Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key Th_errno. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_local Fz_T_once Fz_T_sa Fz_T_master Fz_I3_base
  Fz_M_malloc Fz_M_free F_strlen Str_stpcpy Fz_W5_glx Fz_W5_gsi Fz_W5_defs Fz_W5_vset Fz_W5_new Fz_W5_debug.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation nulls := (repeat (Z_to_bv 64 0) 16) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dbg_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E QN lo : Z) (fl mk buf fs ls : list word) (nstr : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (QN, QN + (Z.of_nat (length nstr) + 1)); (E, E + 904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ es_rep m' E 1 0 fl mk buf fs ls (upd nulls 1%nat (Z_to_bv 64 QN))
    /\ rw_cells usegs m' QN [CB (S (length nstr)) (nstr ++ [Z_to_bv 8 0])].

Lemma dbg_s3_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (line : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E SF SN QN : Z)
    (fl mk buf fs ls : list word) (nstr nslack junk j8 : list byte),
  es_rep m E 1 0 fl mk buf fs ls nulls -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x353000 <= E) ->
  ro_bytes usegs SN (nstr ++ Z_to_bv 8 0 :: nslack) -> ~ In (Z_to_bv 8 0) nstr -> (- (SN + Z.of_nat (length nstr) + 1)) mod 8 <= Z.of_nat (length nslack) ->
  0x10000 <= SN -> SN + (Z.of_nat (length nstr) + 1) + Z.of_nat (length nslack) <= 0x2c0000 -> (1 <= length nstr)%nat -> Z.of_nat (length nstr) + 1 <= 64 ->
  rw_cells usegs m QN [CB (S (length nstr)) junk] -> rblock_range QN (Z.of_nat (length nstr) + 1) ->
  (QN + (Z.of_nat (length nstr) + 1) <= E \/ E + 904 <= QN) ->
  stk usegs m lo (bv_unsigned sp + -80) -> GLOBALS_TOP <= lo -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DBG_STACK ->
  E + 904 <= lo ->
  rw_cells usegs m (bv_unsigned sp + -80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv usegs m ->
  evt usegs (dbg_s3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E QN lo fl mk buf fs ls nstr m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_m2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 SN) (Z_to_bv 64 QN) a1 a2 a3 a4 a5 a6 a7
             line (Z_to_bv 64 (E + 776)) (Z_to_bv 64 SF) (Z_to_bv 64 8) (Z_to_bv 64 4) (Z_to_bv 64 (E + 584)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_m2) fc None m (seg_rom usegs)).
Proof.
  intros until j8.
  intros ES E0 EAL EIMG ROBN NONULN PADN SLOWN SHIGHN NNE NLEN BLK RNG QE ST GLO ACL LO SE FR MI.
  unfold DBG_STACK, CM_STACK, RMALLOC_STACK, SITE_dbg_m2, GLOBALS_TOP in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64. pose proof (repeat_length (Z_to_bv 64 0) 16) as LN16.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof RNG as (Q0 & _ & _ & QCL & QIMG).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (QN, QN + (Z.of_nat (length nstr) + 1)); (E, E + 904)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  ths. ubs_if.
  wstore64 A9 (E + 768) (repeat (Z_to_bv 64 0) 16) 1 (E + 776).
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths.
  (* [comment removed for export] *)
  do 9 ths. th_release FR (bv_unsigned sp). ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with H : mem_inv usegs mX |- _ =>
      assert (STRb : bytes_at usegs mX SN (nstr ++ Z_to_bv 8 0 :: nslack))
        by (apply ro_bytes_at; [exact H| lia| rewrite length_app; cbn [length]; lia| exact ROBN]) end end.
  tcall (strcpy_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nstr nslack junk lo).
  all: try first [eassumption | lia].
  clear STRb. cbv beta delta [mkR].
  apply evt_done. unfold dbg_s3_post. do 16 eexists.
  split; [cbv delta [mkR]; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [| assumption].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.
End WithCeiling0.
