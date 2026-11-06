(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SysStep Bytes.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.MallocP Require Import RMallocRep RMalloc_iface.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Layout Fz_iface Drv_kit Th_kit Th_key Th_errno Fz_T_kit Fz_T_local Fz_T_once Fz_T_sa Fz_T_master Fz_I3_base
  Fz_M_free Fz_W5_glx Fz_W5_gsi Fz_W5_gsi0 Fz_W5_defs Fz_W5_vset Fz_W5_new Fz_W5_debug Fz_W5_clear.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition CLR_STACK : Z := 64 + CF_STACK.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast2 : forall m A cs cs',
  rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells psegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clr_s0_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra s0 s1 s2 s3 s4 s5 s6 : word)
    (E lo : Z) (top bot : Z) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (rax s2x s6x t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7
                    s2x (Z_to_bv 64 (E + 512 + 0 * 4)) (Z_to_bv 64 (E + 768 + 0 * 8)) (Z_to_bv 64 (E + 896)) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 CLR_HEAD) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 208, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells psegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ es_rep m' E top bot fl mk buf fs ls fn.

Lemma clr_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k MK SA NODES E top bot : Z) (od pad tw ne : word) (fl mk buf fs ls fn : list word),
  164 <= bv_unsigned tp ->
  rw_cells psegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells psegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells psegs m (IC_S + 96) [C8 od] ->
  ro_cells psegs m 0x2e8704 [C4 (Z_to_bv 64 2)] ->
  ro_cells psegs m 0x2e8708 [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
  ro_cells psegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 0 <= T ->
  ro_cells psegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 ->
  ro_cells psegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 ->
  ro_cells psegs m SA (sa_hdr (Z_to_bv 64 1) pad tw ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 ->
  ro_cells psegs m NODES [C8 (Z_to_bv 64 E)] -> bv_unsigned ne <> 0 ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x30d000 <= E) -> bv_unsigned tp = RATP ->
  stk psegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - CLR_STACK ->
  E + 904 <= lo ->
  (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
  (MK + 8 * 3 + 8 <= lo \/ bv_unsigned sp <= MK + 8 * 3) ->
  (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
  (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
  mem_inv psegs m ->
  evt psegs (clr_s0_post sp gp tp s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 E lo top bot fl mk buf fs ls fn m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_ERRCLR) fc None m (seg_rom psegs)).
Proof.
  intros until fn.
  intros TP STOP ONCE OD OC KC HK TS T0 MKC HMK SAC HSA HC HNO VC NE0 ES E0 EAL EIMG TPV ST GLO LO SE S1 S2 S3 S4 MI.
  unfold CLR_STACK, CF_STACK, RFREE_STACK, GSI_STACK, FZ_ERRCLR, sa_hdr, IC_S, GLOBALS_TOP, RATP in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (ro_cells_bound _ _ _ _ MKC) as MKB. cbn [cells_size csize Nat.add] in MKB.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  set (Pk := T + 8 * k) in *. set (P3 := MK + 8 * 3) in *.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  (* [comment removed for export] *)
  do 10 ths. ths. ths.
  pose proof T_get_state_steady0_proof as GSI. unfold T_get_state_steady0_stmt, GSI_STACK, sa_hdr, IC_S, GLOBALS_TOP in GSI.
  tcall (GSI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k MK SA NODES E od pad tw ne).
  all: try first [eassumption | reflexivity | lia].
  clear GSI. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths. ths. ths. ths. ths. ths. ths.
  apply evt_done. unfold clr_s0_post, CLR_HEAD. do 19 eexists.
  split. { cbv delta [mkR]. rewrite ?(Z_to_bv_bv_unsigned sp). replace (E + 512 + 0 * 4) with (E + 512) by lia. replace (E + 768 + 0 * 8) with (E + 768) by lia. reflexivity. }
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clr_sC_last_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E lo : Z) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(E, E + 904); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ es_rep m' E 0 0 fl mk buf fs ls (upd fn 15%nat (Z_to_bv 64 0)).

Lemma clr_sC_last_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax s2x s6x : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E top bot : Z) (fl mk buf fs ls fn : list word),
  es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x30d000 <= E) ->
  stk psegs m lo (bv_unsigned sp + -64) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 64 -> E + 904 <= lo ->
  rw_cells psegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv psegs m ->
  evt psegs (clr_sC_last_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E lo fl mk buf fs ls fn m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 (E + 512 + 15 * 4)) (Z_to_bv 64 (E + 768 + 15 * 8)) (Z_to_bv 64 (E + 896)) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_clr_f2) fc None m (seg_rom psegs)).
Proof.
  intros until fn. intros ES E0 EAL EIMG ST GLO LO SE FR MI. unfold SITE_clr_f2, GLOBALS_TOP in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(E, E + 904); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  replace (E + 512 + 15 * 4) with (E + 572) by lia. replace (E + 768 + 15 * 8) with (E + 888) by lia.
  (* [comment removed for export] *)
  wstore64 A9 (E + 768) fn 15 (E + 888).
  ths. ths.
  ths. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
  (* [comment removed for export] *)
  apply (rw_cells_recast2 _ _ _ [CB 8 (le4 (Z_to_bv 64 top) ++ le4 (Z_to_bv 64 bot))]) in TB; [| cbn; repeat split; try exact I; reflexivity| reflexivity| reflexivity].
  ths.
  (* [comment removed for export] *)
  do 8 ths. th_release FR (bv_unsigned sp). ths. ths.
  apply evt_done. unfold clr_sC_last_post. do 16 eexists.
  split; [cbv delta [mkR]; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  lazymatch goal with H : rw_cells psegs ?mf (E + 896) ?cs |- _ =>
    apply (rw_cells_recast2 _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in H; [| cbn; repeat split; try exact I; reflexivity| reflexivity| reflexivity] end.
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.
End WithCeiling0.
