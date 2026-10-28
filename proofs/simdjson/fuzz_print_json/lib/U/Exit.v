(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim Monad Stdio Driver.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation usegs := Image.usegs.

Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells usegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells usegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells usegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x10f1d0 0 2 mode 0xffffffff tail).

Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0xdce88); (RSTDOUT_BUF, 0x10f5d8)]%Z m m'
      /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = []
      /\ stderr_file m'
      /\ rw_cells usegs m' 0xdb8b0 [C8 (Z_to_bv 64 0x10ec58)] /\ rw_cells usegs m' 0x10ec58 [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk usegs m lo (bv_unsigned sp) ->
      rw_cells usegs m 0x10ec78 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      rw_cells usegs m 0x10f1c0 [C8 z64] ->
      rw_cells usegs m 0x10f1b0 [C8 z64] ->
      rw_cells usegs m 0xdce88 [C8 (Z_to_bv 64 RSTDOUT)] ->
      rw_cells usegs m 0xdcd98 [C8 (Z_to_bv 64 RSTDERR)] ->
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells usegs m 0xdb8b0 [C8 (Z_to_bv 64 0x10ec58)] -> rw_cells usegs m 0x10ec58 [C8 guard] ->
      mem_inv usegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (0x110000 <= lo)%Z ->
      implM usegs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xc4df0) fc None m (seg_rom usegs)).
End StdioExitStatement.

Definition RAEX_CALL : Z := 0xbf794.
Definition RAEF_GUARD : Z := 0x3ccd0.

Definition aex_cells (m : word -> option byte) (k : Z) : Prop :=
  rw_cells usegs m 0x10ea30 [C1 (Z_to_bv 8 0)]
  /\ rw_cells usegs m 0x10ea34 [C4 z64; C4 (Z_to_bv 64 k)]
  /\ rw_cells usegs m 0x10ea40 [C8 (Z_to_bv 64 (if (k =? 0)%Z then 0 else 0x10ea48)); C8 z64;
                               C8 (Z_to_bv 64 (if (k =? 0)%Z then 0 else RAEX_CALL))]
  /\ rw_cells usegs m 0x10eb50 [C8 (Z_to_bv 64 (if (k =? 0)%Z then 0 else RAEF_GUARD))]
  /\ rw_cells usegs m 0xecf00 [C1 (Z_to_bv 8 k)]
  /\ rw_cells usegs m 0xecf04 [C1 (Z_to_bv 8 0)].

Definition aex_inv (m : word -> option byte) : Prop := exists k, (0 <= k <= 1)%Z /\ aex_cells m k.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x10ea30, 0x10ea48)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp).

Ltac lock_ret := steps_to 0xd0b0c%Z; lstep; change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word); lstep; if_true; lstep.

Ltac unlock_ret := lstep; replace (sx32 z64) with z64 by (vm_compute; reflexivity); lstep; if_false; lstep.

Lemma funcs_on_exit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m 0x10ec78 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  (0 <= k <= 1)%Z ->

  rw_cells usegs m 0x10ea30 [C1 (Z_to_bv 8 0)] ->
  rw_cells usegs m 0x10ea34 [C4 z64; C4 (Z_to_bv 64 k)] ->
  rw_cells usegs m 0x10ea40 [C8 (Z_to_bv 64 (if (k =? 0)%Z then 0 else 0x10ea48)); C8 z64; C8 (Z_to_bv 64 (if (k =? 0)%Z then 0 else RAEX_CALL))] ->
  rw_cells usegs m 0x10eb50 [C8 (Z_to_bv 64 (if (k =? 0)%Z then 0 else RAEF_GUARD))] ->
  rw_cells usegs m 0xecf04 [C1 (Z_to_bv 8 0)] ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x110000 <= lo)%Z ->
  evt usegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xbf53c) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LCH Hk X1 X2 X3 X4 X6 MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold RAEX_CALL, RAEF_GUARD in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x10ea30, 0x10ea48)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  assert (K : k = 0%Z \/ k = 1%Z) by lia. destruct K as [-> | ->]; cbn [Z.eqb Pos.eqb] in X2, X3, X4.
  -
    carve_frame 48%nat ST.
    steps_to 0xd0b08%Z. lock_ret.
    lstep. lstep. if_true.
    steps_to 0xbf600%Z.
    release_frame FR ST (bv_unsigned sp).
    astep. unlock_ret.
    apply evt_done. unfold funcs_on_exit_post. sys_finish.
  -
    carve_frame 48%nat ST.
    steps_to 0xd0b08%Z. lock_ret.
    lstep. lstep. if_false.
    lstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
    astep. lstep. try change (bv_swrap 32 (1 + -1)) with 0%Z.
    lstep. lstep. if_false.
    steps_to 0xbf5ac%Z.
    lstep. astep. unlock_ret.
    lstep. astep.
    astep.
    steps_to 0x3ccd8%Z. lstep. if_false.
    lstep.
    lstep. astep. lock_ret.
    lstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    lstep. try change (bv_swrap 32 (0 + -1)) with (-1)%Z.
    lstep. lstep. if_false.
    lstep. astep.
    lstep. lstep. lstep. lstep.
    lstep. if_true.
    steps_to 0xbf600%Z.
    release_frame FR ST (bv_unsigned sp).
    astep. unlock_ret.
    apply evt_done. unfold funcs_on_exit_post. sys_finish.
Time Qed.

Definition exit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0xbf854) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xc4df0) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x10ea30, 0x10ea48); (0x10ec50, 0x10ec54); (0xdcef8, 0xdcef9)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells usegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells usegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m' 0x10ec50 [C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m' 0xdcef8 [C1 (Z_to_bv 8 1)].

Lemma exit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
    (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
  rw_cells usegs m 0x10ec50 [C4 z64] ->
  rw_cells usegs m 0xdb8b8 [C8 (Z_to_bv 64 0xd5ef0); C8 (Z_to_bv 64 0xd5ee8)] ->
  rw_cells usegs m 0xd5ee8 [C8 (Z_to_bv 64 0x3c818)] ->
  rw_cells usegs m 0xdcef8 [C1 (Z_to_bv 8 0)] ->
  rw_cells usegs m 0xdb758 [C8 (Z_to_bv 64 0xbf604); C8 z64] ->
  rw_cells usegs m 0xdc8e0 [C8 (Z_to_bv 64 0xdc8e0)] ->
  rw_cells usegs m 0x10ec78 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  aex_inv m ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (0x110000 <= lo)%Z ->
  evt usegs (exit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xbf7e8) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH (k & Hk & (X1 & X2 & X3 & X4 & X5 & X6)) MI -> -> Ht LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold RAEX_CALL, RAEF_GUARD in X3, X4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x10ea30, 0x10ea48); (0x10ec50, 0x10ec54); (0xdcef8, 0xdcef9)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 16%nat ST.
  do 6 lstep.
  replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  lstep. lstep.

  amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
  lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
  lstep. astep.

  call_sp (funcs_on_exit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo k cdt thr sec tm1);
    [ unfold RAEX_CALL, RAEF_GUARD; first [hyp_by_addr | exact Hk | lia] .. | ].
  rename POST into ST.
  steps_to 0xbf79c%Z.

  carve_frame 32%nat ST. steps_to 0x3c818%Z.

  carve_frame 16%nat ST. steps_to 0x3c8a4%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
  steps_to 0xbf7e4%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
  astep.
  unfold exit_prefix_post. sys_finish.
Time Qed.

Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word),
    stk usegs m lo (bv_unsigned sp) ->
    rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells usegs m 0x10ec50 [C4 z64] ->
    rw_cells usegs m 0xdb8b8 [C8 (Z_to_bv 64 0xd5ef0); C8 (Z_to_bv 64 0xd5ee8)] ->
    rw_cells usegs m 0xd5ee8 [C8 (Z_to_bv 64 0x3c818)] ->
    rw_cells usegs m 0xdcef8 [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs m 0xdb758 [C8 (Z_to_bv 64 0xbf604); C8 z64] ->
    rw_cells usegs m 0xdc8e0 [C8 (Z_to_bv 64 0xdc8e0)] ->
    rw_cells usegs m 0x10ec78 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    aex_inv m ->
    rw_cells usegs m 0x10f1c0 [C8 z64] -> rw_cells usegs m 0x10f1b0 [C8 z64] ->
    rw_cells usegs m 0xdce88 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells usegs m 0xdcd98 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells usegs m 0xdb8b0 [C8 (Z_to_bv 64 0x10ec58)] -> rw_cells usegs m 0x10ec58 [C8 guard] ->
    mem_inv usegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x110000 <= lo)%Z ->
    implM usegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xbf7e8) fc None m (seg_rom usegs)).
  Proof.
    intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH AEX OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.

    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind usegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0xbf854) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0xbf854) fc None m' (seg_rom usegs))).
    -
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      call exit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact AEX | exact MI
                              | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0xbf854)) with (Z_to_bv 64 0xbf854) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    -
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Time Qed.
End ExitProof.

Definition at_exit {St : Type} (get_so : St -> stdout_st) (code : Z) (s : St) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t : Z) (td0 td1 td2 td3 guard : word)
         (cdt thr sec : byte) (tm1 : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xbf7e8) fc None m (seg_rom usegs)
    /\ stk usegs m lo (bv_unsigned sp)
    /\ rw_cells usegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells usegs m 0x10ec50 [C4 z64]
    /\ rw_cells usegs m 0xdb8b8 [C8 (Z_to_bv 64 0xd5ef0); C8 (Z_to_bv 64 0xd5ee8)]
    /\ rw_cells usegs m 0xd5ee8 [C8 (Z_to_bv 64 0x3c818)]
    /\ rw_cells usegs m 0xdcef8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs m 0xdb758 [C8 (Z_to_bv 64 0xbf604); C8 z64]
    /\ rw_cells usegs m 0xdc8e0 [C8 (Z_to_bv 64 0xdc8e0)]
    /\ rw_cells usegs m 0x10ec78 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ aex_inv m
    /\ rw_cells usegs m 0x10f1c0 [C8 z64] /\ rw_cells usegs m 0x10f1b0 [C8 z64]
    /\ rw_cells usegs m 0xdce88 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells usegs m 0xdcd98 [C8 (Z_to_bv 64 RSTDERR)]
    /\ stdout_file m (get_so s) /\ stderr_file m
    /\ rw_cells usegs m 0xdb8b0 [C8 (Z_to_bv 64 0x10ec58)] /\ rw_cells usegs m 0x10ec58 [C8 guard]
    /\ mem_inv usegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ (0 < t < 4194304)%Z /\ (lo <= bv_unsigned sp - 176)%Z /\ (0x110000 <= lo)%Z.

Lemma exit_from_at_exit {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) :
  stdio_exit_spec_stmt get_so set_so ->
  forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop) code ms,
    at_exit get_so code s ms -> implM usegs (Driver.exit_model (io_S get_so set_so) code) s Q ms.
Proof.
  intros STDIO_EXIT s Q code ms H.
  destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t &
                 td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & -> & H).
  destruct H as (ST & TD & EXL & GF & FA & FIN & GCX & DSO & LCH & AEX & OFL & SIN & SOU & SEU & SOF & SEF & GG & GU & MI & Htp & Ha0 & Ht & LO & LOLO).
  eapply (exit_spec get_so set_so STDIO_EXIT s Q);
    [exact ST | exact TD | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact AEX | exact OFL | exact SIN | exact SOU | exact SEU
    | exact SOF | exact SEF | exact GG | exact GU | exact MI | exact Htp | exact Ha0 | exact Ht | exact LO | exact LOLO].
Qed.

Lemma impl_msys_of_enode : forall segs {St A} (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
  impl segs (at_node segs) (enode n pl) (epost Q) ms ->
  impl segs (at_node segs) (Monad.msys n pl s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
  intros segs St A n pl Q s ms H. unfold Monad.msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.
