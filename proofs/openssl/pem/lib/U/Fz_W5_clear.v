(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SysStep Bytes Ubs SFModel ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key Th_errno. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_I3_base Fz_M_free Fz_W5_defs Fz_W5_vset Fz_W5_new Fz_W5_debug.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_I3_eciter.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition FZ_ERRCLR : Z := 0xe80c8.
Definition CLR_HEAD : Z := 0xe80fc.        (* [comment removed for export] *)
Definition SITE_clr_f1 : Z := 0xe7cbc.     (* [comment removed for export] *)
Definition SITE_clr_f2 : Z := 0xe7ce4.     (* [comment removed for export] *)

Ltac zstore AH BASE len OFF n ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok_n usegs mX BASE (repeat (Z_to_bv 8 0) len) OFF n (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(rewrite repeat_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AZ" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      pose proof (u8arr_write_bytes usegs mX BASE (repeat (Z_to_bv 8 0) len) OFF bs AH ltac:(lia) ltac:(rewrite !repeat_length; cbn; lia)) as A2;
      change bs with (repeat (Z_to_bv 8 0) n) in A2 at 2; rewrite upd_bytes_zeros in A2 by lia
    end;
    replace (BASE + OFF) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.

Ltac clr_shz := match goal with |- context [Z.shiftl ?a ?n] => let p := eval vm_compute in (2 ^ n) in
  rewrite (Z.shiftl_mul_pow2 a n) by lia; change (2 ^ n) with p end.
Ltac clr_zc H := zify_cond H; signed_lits_in H; rewrite ?unsigned_lit in H by lia; rewrite ?ubs_land7, ?zb_lxor_ones in H by lia.
Ltac clr_if := let H := fresh "KA" in
  first [ if_cases H; clr_zc H; [exfalso; lia | clear H] | if_cases H; clr_zc H; [clear H | exfalso; lia] ].
Ltac clr_closed c := match c with | context [?v] => is_var v; fail 1 | _ => idtac end.
Ltac clr_lit := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  clr_closed c; let v := eval vm_compute in c in
  lazymatch v with true => change c with true; cbv iota | false => change c with false; cbv iota end end.
Ltac clr_step := first [clr_shz | ubs_if | clr_lit | clr_if | zstep].
Ltac clr_at o := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) =>
  let d := eval vm_compute in (n =? o) in lazymatch d with true => idtac | false => fail end end.

Ltac clr_mtry E i w fl mk buf fs ls A1 A2 A3 A4 A5 A6 A7 A8 FSI :=
  first [ zstore A4 (E + 256) 128%nat (i * 8) 8%nat (E + 256 + i * 8)
        | zstore A5 (E + 384) 128%nat (i * 8) 8%nat (E + 384 + i * 8)
        | zstore A6 (E + 512) 64%nat (i * 4) 4%nat (E + i * 4 + 512)
        | zstore A6 (E + 512) 64%nat (i * 4) 4%nat (E + 512 + i * 4)
        | wstore32 A2 (E + 64) mk i (E + 64 + i * 4)
        | wstore32 A2 (E + 64) mk i (E + i * 4 + 64)
        | wstore32 A1 E fl i (E + i * 4)
        | wstore64 A3 (E + 128) buf i (E + 128 + i * 8)
        | wstore64 A3 (E + 128) buf i (E + i * 8 + 128)
        | wstore32 A8 (E + 704) ls i (E + 704 + i * 4)
        | wstore32 A8 (E + 704) ls i (E + i * 4 + 704)
        | let RD := fresh "RD" in
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
            first [ pose proof (u64arr_read usegs mX (E + 576) fs i w (Z_to_bv 64 (E + 576 + i * 8)) A7 FSI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD
                  | pose proof (u64arr_read usegs mX (E + 576) fs i w (Z_to_bv 64 (E + i * 8 + 576)) A7 FSI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD ] end;
          ths; clear RD ].
Ltac clr_mtry_B E i w fs fn A7 A9 FNI :=
  first [ wstore64 A7 (E + 576) fs i (E + 576 + i * 8)
        | wstore64 A7 (E + 576) fs i (E + 576 + i * 8 + 0)
        | let RD := fresh "RD" in
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
            first [ pose proof (u64arr_read usegs mX (E + 768) fn i w (Z_to_bv 64 (E + 768 + i * 8)) A9 FNI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD
                  | pose proof (u64arr_read usegs mX (E + 768) fn i w (Z_to_bv 64 (E + i * 8 + 768)) A9 FNI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD ] end;
          ths; clear RD ].
Ltac clr_mtry_C E i fn A9 :=
  first [ wstore64 A9 (E + 768) fn i (E + 768 + i * 8) | wstore64 A9 (E + 768) fn i (E + 768 + i * 8 + 0) ].


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CLR_HRET : Z := 0xe810c.

Definition clr_hframe (s0 s4 s5 s6 : word) (E i : Z) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 E); C8 s0; C8 (Z_to_bv 64 CLR_HRET)].

Definition clr_sA_post (sp gp tp s0 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E i lo top bot : Z) (w : word) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 SITE_clr_f1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) w a1 (Z_to_bv 64 112) a3 a4 a5 a6 a7
                    (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 (E + i * 4)) (Z_to_bv 64 (E + i * 4 + 512)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (E, E + 904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (clr_hframe s0 s4 s5 s6 E i)
    /\ es_rep m' E top bot (upd fl (Z.to_nat i) (Z_to_bv 64 0)) (upd mk (Z.to_nat i) (Z_to_bv 64 0)) (upd buf (Z.to_nat i) (Z_to_bv 64 0)) fs
              (upd ls (Z.to_nat i) (Z_to_bv 64 (-1))) fn.

Lemma clr_sA_walk : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E i top bot : Z) (w : word) (fl mk buf fs ls fn : list word),
  0 <= i < 16 -> nth_error fs (Z.to_nat i) = Some w ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x353000 <= E) ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> E + 904 <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv usegs m ->
  evt usegs (clr_sA_post sp gp tp s0 s4 s5 s6 s7 s8 s9 s10 s11 F fc E i lo top bot w fl mk buf fs ls fn m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 i) (Z_to_bv 64 16) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CLR_HEAD) fc None m (seg_rom usegs)).
Proof using All.
  intros until fn. intros HI FSI ES E0 EAL EIMG ST GLO SE SLO MI. unfold CLR_HEAD, GLOBALS_TOP in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (E, E + 904)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 4 step.
  step; th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST; do 8 ths; step.
  repeat clr_step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u8arr_read usegs mX (E + 512) (repeat (Z_to_bv 8 0) 64) (i * 4) (Z_to_bv 8 0) (Z_to_bv 64 (E + i * 4 + 512)) A6
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  repeat (tryif clr_at FZ_CRYPTO_FREE then fail else first [clr_step | clr_mtry E i w fl mk buf fs ls A1 A2 A3 A4 A5 A6 A7 A8 FSI]).
  apply evt_done. unfold clr_sA_post, SITE_clr_f1. do 14 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [unfold clr_hframe, CLR_HRET; eassumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clr_sB_post (sp gp tp s0 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E i lo top bot : Z) (w : word) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 SITE_clr_f2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 (E + 768 + i * 8)) w a1 (Z_to_bv 64 114) a3 a4 a5 a6 a7
                    (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 (E + i * 4)) (Z_to_bv 64 (E + i * 4 + 512)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m' (seg_rom usegs)
    /\ munch [(E, E + 904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (clr_hframe s0 s4 s5 s6 E i)
    /\ es_rep m' E top bot fl mk buf (upd fs (Z.to_nat i) (Z_to_bv 64 0)) ls fn.

Lemma clr_sB_walk : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E i top bot : Z) (w : word) (fl mk buf fs ls fn : list word),
  0 <= i < 16 -> nth_error fn (Z.to_nat i) = Some w ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x353000 <= E) ->
  stk usegs m lo (bv_unsigned sp + -64) -> GLOBALS_TOP <= lo -> E + 904 <= lo -> lo <= bv_unsigned sp - 64 ->
  rw_cells usegs m (bv_unsigned sp + -64) (clr_hframe s0 s4 s5 s6 E i) -> mem_inv usegs m ->
  evt usegs (clr_sB_post sp gp tp s0 s4 s5 s6 s7 s8 s9 s10 s11 F fc E i lo top bot w fl mk buf fs ls fn m)
    (MS (mkR (Z_to_bv 64 SITE_clr_f1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 (E + i * 4)) (Z_to_bv 64 (E + i * 4 + 512)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_clr_f1) fc None m (seg_rom usegs)).
Proof using All.
  intros until fn. intros HI FNI ES E0 EAL EIMG ST GLO SE SLO FR MI. unfold SITE_clr_f1, GLOBALS_TOP in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(E, E + 904)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold clr_hframe in FR.
  repeat (tryif clr_at FZ_CRYPTO_FREE then fail else first [clr_step | clr_mtry_B E i w fs fn A7 A9 FNI]).
  apply evt_done. unfold clr_sB_post, SITE_clr_f2. do 14 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [unfold clr_hframe; eassumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clr_sC_post (sp gp tp s0 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E i lo top bot : Z) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 CLR_HRET) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 (i + 1)) (Z_to_bv 64 16) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (if i =? 15 then FZ_ECL_DONE else CLR_HEAD)) fc None m' (seg_rom usegs)
    /\ munch [(E, E + 904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ es_rep m' E top bot fl mk buf fs ls (upd fn (Z.to_nat i) (Z_to_bv 64 0)).

Lemma clr_sC_walk : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E i top bot : Z) (fl mk buf fs ls fn : list word),
  0 <= i < 16 ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x353000 <= E) ->
  stk usegs m lo (bv_unsigned sp + -64) -> GLOBALS_TOP <= lo -> E + 904 <= lo -> lo <= bv_unsigned sp - 64 ->
  rw_cells usegs m (bv_unsigned sp + -64) (clr_hframe s0 s4 s5 s6 E i) -> mem_inv usegs m ->
  evt usegs (clr_sC_post sp gp tp s0 s4 s5 s6 s7 s8 s9 s10 s11 F fc E i lo top bot fl mk buf fs ls fn m)
    (MS (mkR (Z_to_bv 64 SITE_clr_f2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 (E + 768 + i * 8)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (i * 8)) (Z_to_bv 64 (E + 576 + i * 8)) (Z_to_bv 64 (E + i * 4)) (Z_to_bv 64 (E + i * 4 + 512)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_clr_f2) fc None m (seg_rom usegs)).
Proof using All.
  intros until fn. intros HI ES E0 EAL EIMG ST GLO SE SLO FR MI. unfold SITE_clr_f2, GLOBALS_TOP in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(E, E + 904)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold clr_hframe in FR.
  repeat (tryif clr_at CLR_HRET then fail else first [clr_step | clr_mtry_C E i fn A9]).
  unfold CLR_HRET in *. th_ret_lit. th_release FR (bv_unsigned sp). zstep.
  zstep. if_cases K15; zify_cond K15.
  - apply evt_done. unfold clr_sC_post, CLR_HEAD. rewrite (proj2 (Z.eqb_neq i 15)) by lia. do 16 eexists.
    split; [cbv delta [mkR]; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
  - apply evt_done. unfold clr_sC_post, FZ_ECL_DONE. rewrite (proj2 (Z.eqb_eq i 15)) by lia. do 16 eexists.
    split; [cbv delta [mkR]; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.
End WithCeiling0.
