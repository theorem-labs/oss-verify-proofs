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
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Layout Fz_iface Drv_kit Th_kit Th_key Th_errno Fz_T_kit Fz_I3_base Fz_M_free Fz_W5_defs Fz_W5_vset Fz_W5_new Fz_W5_debug.
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

Definition FZ_ERRCLR : Z := 0xe2c10.
Definition CLR_HEAD : Z := 0xe2c60.        (* [comment removed for export] *)
Definition SITE_clr_f1 : Z := 0xe2cac.     (* [comment removed for export] *)
Definition SITE_clr_f2 : Z := 0xe2cc0.     (* [comment removed for export] *)

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
(* [comment removed for export] *)
Definition clr_sA_post (sp gp tp s0 s1 s2 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E i top bot : Z) (w : word) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 SITE_clr_f1) sp gp tp t0 t1 t2 s0 s1 w s2 (Z_to_bv 64 112) a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 (E + 512 + i * 4)) (Z_to_bv 64 (E + 768 + i * 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m' (seg_rom psegs)
    /\ munch [(E, E + 904)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ es_rep m' E top bot (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) fs (upd ls (Z.to_nat i) s6) fn.

Lemma clr_sA_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E i top bot : Z) (w : word) (fl mk buf fs ls fn : list word),
  0 <= i < 16 -> nth_error fs (Z.to_nat i) = Some w ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x30d000 <= E) ->
  stk psegs m lo (bv_unsigned sp) -> E + 904 <= lo -> lo <= bv_unsigned sp -> mem_inv psegs m ->
  evt psegs (clr_sA_post sp gp tp s0 s1 s2 s5 s6 s7 s8 s9 s10 s11 F fc E i top bot w fl mk buf fs ls fn m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (E + 512 + i * 4)) (Z_to_bv 64 (E + 768 + i * 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CLR_HEAD) fc None m (seg_rom psegs)).
Proof.
  intros until fn. intros HI FSI ES E0 EAL EIMG ST SE SLO MI. unfold CLR_HEAD in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(E, E + 904)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u8arr_read psegs mX (E + 512) (repeat (Z_to_bv 8 0) 64) (i * 4) (Z_to_bv 8 0) (Z_to_bv 64 (E + 512 + i * 4)) A6
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  ths. ths. th_if_lit.
  zstore A4 (E + 256) 128%nat (i * 8) 8%nat (E + 768 + i * 8 + -512).
  zstore A5 (E + 384) 128%nat (i * 8) 8%nat (E + 768 + i * 8 + -384).
  ths.
  zstore A6 (E + 512) 64%nat (i * 4) 4%nat (E + 512 + i * 4).
  wstore32 A2 (E + 64) mk i (E + 512 + i * 4 + -448).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read psegs mX (E + 576) fs i w (Z_to_bv 64 (E + 768 + i * 8 + -192)) A7 FSI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD.
  wstore32 A1 E fl i (E + 512 + i * 4 + -512).
  wstore64 A3 (E + 128) buf i (E + 768 + i * 8 + -640).
  wstore32 A8 (E + 704) ls i (E + 512 + i * 4 + 192).
  ths. ths. ths.
  apply evt_done. unfold clr_sA_post, SITE_clr_f1. do 13 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clr_sB_post (sp gp tp s0 s1 s2 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E i top bot : Z) (w : word) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 SITE_clr_f2) sp gp tp t0 t1 t2 s0 s1 w s2 (Z_to_bv 64 114) a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 (E + 512 + i * 4)) (Z_to_bv 64 (E + 768 + i * 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m' (seg_rom psegs)
    /\ munch [(E, E + 904)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ es_rep m' E top bot fl mk buf (upd fs (Z.to_nat i) (Z_to_bv 64 0)) ls fn.

Lemma clr_sB_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E i top bot : Z) (w : word) (fl mk buf fs ls fn : list word),
  0 <= i < 16 -> nth_error fn (Z.to_nat i) = Some w ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x30d000 <= E) ->
  stk psegs m lo (bv_unsigned sp) -> E + 904 <= lo -> lo <= bv_unsigned sp -> mem_inv psegs m ->
  evt psegs (clr_sB_post sp gp tp s0 s1 s2 s5 s6 s7 s8 s9 s10 s11 F fc E i top bot w fl mk buf fs ls fn m)
    (MS (mkR (Z_to_bv 64 SITE_clr_f1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (E + 512 + i * 4)) (Z_to_bv 64 (E + 768 + i * 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_clr_f1) fc None m (seg_rom psegs)).
Proof.
  intros until fn. intros HI FNI ES E0 EAL EIMG ST SE SLO MI. unfold SITE_clr_f1 in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(E, E + 904)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read psegs mX (E + 768) fn i w (Z_to_bv 64 (E + 768 + i * 8)) A9 FNI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD.
  wstore64 A7 (E + 576) fs i (E + 768 + i * 8 + -192).
  ths. ths. ths.
  apply evt_done. unfold clr_sB_post, SITE_clr_f2. do 13 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clr_sC_post (sp gp tp s0 s1 s2 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E i top bot : Z) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 SITE_clr_f2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 (E + 512 + (i + 1) * 4)) (Z_to_bv 64 (E + 768 + (i + 1) * 8)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 CLR_HEAD) fc None m' (seg_rom psegs)
    /\ munch [(E, E + 904)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ es_rep m' E top bot fl mk buf fs ls (upd fn (Z.to_nat i) (Z_to_bv 64 0)).

Lemma clr_sC_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E i top bot : Z) (fl mk buf fs ls fn : list word),
  0 <= i < 15 ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x30d000 <= E) ->
  stk psegs m lo (bv_unsigned sp) -> E + 904 <= lo -> lo <= bv_unsigned sp -> mem_inv psegs m ->
  evt psegs (clr_sC_post sp gp tp s0 s1 s2 (Z_to_bv 64 (E + 896)) s6 s7 s8 s9 s10 s11 F fc E i top bot fl mk buf fs ls fn m)
    (MS (mkR (Z_to_bv 64 SITE_clr_f2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (E + 512 + i * 4)) (Z_to_bv 64 (E + 768 + i * 8))
             (Z_to_bv 64 (E + 896)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_clr_f2) fc None m (seg_rom psegs)).
Proof.
  intros until fn. intros HI ES E0 EAL EIMG ST SE SLO MI. unfold SITE_clr_f2 in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(E, E + 904)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  wstore64 A9 (E + 768) fn i (E + 768 + i * 8).
  ths. ths.
  ths. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
  apply evt_done. unfold clr_sC_post, CLR_HEAD. do 16 eexists.
  split. { cbv delta [mkR]. replace (E + 768 + i * 8 + 8) with (E + 768 + (i + 1) * 8) by lia. replace (E + 512 + i * 4 + 4) with (E + 512 + (i + 1) * 4) by lia. reflexivity. }
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.
End WithCeiling0.
