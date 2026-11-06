(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SysStep.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.MallocP Require Import RMallocRep RMalloc_iface.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Layout Fz_iface Drv_kit Th_kit Th_key Th_errno Fz_T_kit Fz_T_local Fz_T_once Fz_T_sa Fz_T_master Fz_I3_base Fz_M_free
  Fz_W5_glx Fz_W5_gsi Fz_W5_defs Fz_W5_vset.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation nulls := (repeat (Z_to_bv 64 0) 16) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition FZ_ERRNEW : Z := 0xe2308.
Definition ERRNEW_STACK : Z := 32 + GSI_STACK.

(* [comment removed for export] *)
Lemma upd_same : forall {X} (l : list X) i x, nth_error l i = Some x -> upd l i x = l.
Proof. induction l as [|y l IH]; intros [|i] x H; cbn in *; [discriminate | discriminate | congruence | rewrite (IH i x H); reflexivity]. Qed.

(* [comment removed for export] *)
Ltac zstore AH BASE len OFF n ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok_n psegs mX BASE (repeat (Z_to_bv 8 0) len) OFF n (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(rewrite repeat_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AZ" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      pose proof (u8arr_write_bytes psegs mX BASE (repeat (Z_to_bv 8 0) len) OFF bs AH ltac:(lia) ltac:(rewrite !repeat_length; cbn; lia)) as A2;
      change bs with (repeat (Z_to_bv 8 0) n) in A2 at 2; rewrite upd_bytes_zeros in A2 by lia
    end;
    replace (BASE + OFF) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.

(* [comment removed for export] *)
Ltac wstore32 AH BASE ws i ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok psegs mX BASE ws i (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AW" in
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) => pose proof (u32arr_write psegs mX BASE ws i v AH ltac:(lia)) as A2
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mY ?a ?bs) _) =>
        change (write_to_mem mY a bs) with (write_to_mem mY a (le4 (Z_to_bv 64 0))); pose proof (u32arr_write psegs mX BASE ws i (Z_to_bv 64 0) AH ltac:(lia)) as A2
    end;
    replace (BASE + 4 * i) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.
Ltac wstore64 AH BASE ws i ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok psegs mX BASE ws i (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AW" in
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le8 ?v)) _) => pose proof (u64arr_write psegs mX BASE ws i v AH ltac:(lia)) as A2
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mY ?a ?bs) _) =>
        change (write_to_mem mY a bs) with (write_to_mem mY a (le8 (Z_to_bv 64 0))); pose proof (u64arr_write psegs mX BASE ws i (Z_to_bv 64 0) AH ltac:(lia)) as A2
    end;
    replace (BASE + 8 * i) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.

Definition T_err_new_rest_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k MK SA NODES E : Z) (errv od pad tw ne : word)
         (fl mk buf ls : list word),
    164 <= bv_unsigned tp ->
    (* [comment removed for export] *)
    rw_cells psegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells psegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells psegs m (IC_S + 96) [C8 od] ->
    ro_cells psegs m 0x2e8704 [C4 (Z_to_bv 64 2)] ->
    ro_cells psegs m 0x2e8708 [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    ro_cells psegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 0 <= T ->
    ro_cells psegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 ->
    ro_cells psegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 ->
    ro_cells psegs m SA (sa_hdr (Z_to_bv 64 1) pad tw ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 ->
    ro_cells psegs m NODES [C8 (Z_to_bv 64 E)] -> bv_unsigned ne <> 0 ->
    rw_cells psegs m (bv_unsigned tp + -164) [C4 errv] ->
    (* [comment removed for export] *)
    lx_statics m ->
    (* [comment removed for export] *)
    es_rep m E 0 0 fl mk buf nulls ls nulls -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x30d000 <= E) -> bv_unsigned tp = RATP ->
    stk psegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ERRNEW_STACK ->
    0x2e8708 + 4 <= lo -> IC_S + 104 <= lo -> E + 904 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -164) ->
    (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
    (MK + 8 * 3 + 8 <= lo \/ bv_unsigned sp <= MK + 8 * 3) ->
    (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
    (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (fl' mk' buf' ls' : list word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned sp - ERRNEW_STACK, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160); (E, E + 904)] m m'
                 /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ rw_cells psegs m' (bv_unsigned tp + -164) [C4 (sx32 errv)]
                 /\ stk psegs m' lo (bv_unsigned sp)
                 /\ es_rep m' E 1 0 fl' mk' buf' nulls ls' nulls)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_ERRNEW) fc None m (seg_rom psegs)).

Theorem T_err_new_rest_proof : T_err_new_rest_stmt.
Proof.
  unfold T_err_new_rest_stmt, ERRNEW_STACK, GSI_STACK, FZ_ERRNEW, sa_hdr. intros until ls.
  intros TP STOP ONCE OD OC KC HK TS T0 MKC HMK SAC HSA HC HNO VC NE0 ERR LXS ES E0 EAL EIMG TPV ST GLO LO S6 S7 SE S0 S1 S2 S3 S4 MI.
  unfold IC_S, GLOBALS_TOP, RATP in *. change (32 + (48 + 96))%Z with 176%Z in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64. pose proof (repeat_length (Z_to_bv 64 0) 16) as LN16.
  pose proof (ro_cells_bound _ _ _ _ MKC) as MKB. cbn [cells_size csize Nat.add] in MKB.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160); (E, E + 904)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  set (Pk := T + 8 * k) in *. set (P3 := MK + 8 * 3) in *.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  (* [comment removed for export] *)
  do 5 ths. ths. ths. ths.
  pose proof T_get_state_steady_proof as GSI. unfold T_get_state_steady_stmt, GSI_STACK, sa_hdr, IC_S, GLOBALS_TOP in GSI.
  tcall (GSI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k MK SA NODES E errv od pad tw ne).
  all: try first [eassumption | reflexivity | lia].
  clear GSI. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  ths. try rewrite (t_sx32_small 0) by lia. ths. try rewrite (t_sx32_small 0) by lia.
  do 6 ths. ths.
  ths. th_if_lit.
  (* [comment removed for export] *)
  ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u8arr_read psegs mX (E + 512) (repeat (Z_to_bv 8 0) 64) 4 (Z_to_bv 8 0) (Z_to_bv 64 (E + 516)) A6
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  ths. ths. ths. ths. th_if_lit. ths.
  zstore A4 (E + 256) 128%nat 8 8%nat (E + 264).
  zstore A5 (E + 384) 128%nat 8 8%nat (E + 392).
  ths.
  zstore A6 (E + 512) 64%nat 4 4%nat (E + 516).
  (* [comment removed for export] *)
  ths.
  wstore32 A8 (E + 704) ls 1 (E + 708).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read psegs mX (E + 576) (repeat (Z_to_bv 64 0) 16) 1 (Z_to_bv 64 0) (Z_to_bv 64 (E + 584)) A7
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD.
  wstore32 A2 (E + 64) mk 1 (E + 68).
  wstore32 A1 E fl 1 (E + 4).
  wstore64 A3 (E + 128) buf 1 (E + 136).
  (* [comment removed for export] *)
  ths. ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (LXS1 : lx_statics mX)
      by (eapply lx_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact LXS];
          intros a Ha; cbv beta; cbn [outside]; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; repeat split; try exact I; lia) end.
  tcall (crypto_free_null _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | reflexivity | unfold GLOBALS_TOP; lia].
  clear LXS1. cbv beta delta [mkR].
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read psegs mX (E + 768) (repeat (Z_to_bv 64 0) 16) 1 (Z_to_bv 64 0) (Z_to_bv 64 (E + 776)) A9
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD.
  wstore64 A7 (E + 576) (repeat (Z_to_bv 64 0) 16) 1 (E + 584). rewrite (upd_same (repeat (Z_to_bv 64 0) 16) 1%nat (Z_to_bv 64 0) eq_refl) in A7.
  ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (LXS1 : lx_statics mX)
      by (eapply lx_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact LXS];
          intros a Ha; cbv beta; cbn [outside]; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; repeat split; try exact I; lia) end.
  tcall (crypto_free_null _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | reflexivity | unfold GLOBALS_TOP; lia].
  clear LXS1. cbv beta delta [mkR].
  wstore64 A9 (E + 768) (repeat (Z_to_bv 64 0) 16) 1 (E + 776). rewrite (upd_same (repeat (Z_to_bv 64 0) 16) 1%nat (Z_to_bv 64 0) eq_refl) in A9.
  (* [comment removed for export] *)
  ths. ths. ths. ths. th_release FR (bv_unsigned sp). ths. ths.
  apply evt_done. do 20 eexists. split; [cbv delta [mkR]; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.
End WithCeiling0.
