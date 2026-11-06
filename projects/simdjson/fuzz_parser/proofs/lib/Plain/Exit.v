(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import StrFun STRW_tac Startup_kit Amo_tac.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg F_syscalls Startup_A StdioFiles.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Notation rsegs := PImg.psegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p_Exit_spec : forall (code : Z) (Q : Empty_set -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 code ->
  impl rsegs (at_node rsegs) (enode (NExit code) dec_exit) (epost Q)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x62b2c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI ->.
  pose proof (wmono_refl rsegs m) as WM.
  apply impl_enode. do 2 lstep. step_ecall.
  split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Qed.

(* [comment removed for export] *)
Lemma p_Exit_specM : forall {St : Type} (s : St) (code : Z) (Q : Empty_set -> St -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 code ->
  implM rsegs (msys (NExit code) dec_exit) s Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x62b2c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI ->.
  pose proof (wmono_refl rsegs m) as WM.
  apply implM_sys. do 2 lstep. step_ecall.
  split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x62dc8) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x65b24) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0xa7dc8, 0xa7de0); (0xa7fe8, 0xa7ff0); (0x77148, 0x77149)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells rsegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells rsegs m' 0xa7fe8 [C4 (Z_to_bv 64 t)]
    /\ rw_cells rsegs m' 0x77148 [C1 (Z_to_bv 8 1)].

Definition pexit_tbl (m : word -> option byte) : Prop :=
  (rw_cells rsegs m 0xa7dc8 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
   /\ rw_cells rsegs m 0xa7dd8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
   /\ rw_cells rsegs m 0xa7ee8 [C8 (Z_to_bv 64 0)])
  \/ (rw_cells rsegs m 0xa7dc8 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1)]
      /\ rw_cells rsegs m 0xa7dd8 [C8 (Z_to_bv 64 0xa7de0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x62d08)]
      /\ rw_cells rsegs m 0xa7ee8 [C8 (Z_to_bv 64 0x26ca0)]
      /\ rw_cells rsegs m 0x87154 [C1 (Z_to_bv 8 0)]).

Lemma pexit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 dso : word) (cdt thr sec : byte) (tm1 : word),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
  rw_cells rsegs m 0xa7fe8 [C4 z64] ->                                              (* [comment removed for export] *)
  rw_cells rsegs m 0x75e90 [C8 (Z_to_bv 64 0x72a58); C8 (Z_to_bv 64 0x72a50)] ->    (* [comment removed for export] *)
  rw_cells rsegs m 0x72a50 [C8 (Z_to_bv 64 0x267e8)] ->                            (* [comment removed for export] *)
  rw_cells rsegs m 0x77148 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
  rw_cells rsegs m 0x75d70 [C8 (Z_to_bv 64 0x62c40); C8 z64] ->                     (* [comment removed for export] *)
  rw_cells rsegs m 0x76ea0 [C8 dso] ->
  rw_cells rsegs m 0xa8010 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  pexit_tbl m ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (0xa9000 <= lo)%Z ->
  evt rsegs (pexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x62d5c) fc None m (seg_rom rsegs)).
Proof.
  intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH TBL MI -> -> Ht LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0xa7dc8, 0xa7de0); (0xa7fe8, 0xa7ff0); (0x77148, 0x77149)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct TBL as [(T0 & T1 & T2) | (T0 & T1 & T2 & INCB)].
  all: carve_frame 16%nat ST.
  all: do 6 lstep.
  all: replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  all: lstep. all: lstep.
  (* [comment removed for export] *)
  all: amo_step. all: replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  all: lstep. all: if_false. all: amo_step. all: lstep. all: if_false.
  all: lstep. all: change (bv_swrap 32 (0 + 0)) with 0%Z.
  all: lstep. all: if_cases K; zify_cond K; [exfalso; lia|]. all: clear K. all: lstep. all: if_true.
  all: steps_to 0x62b78%Z.
  all: carve_frame 48%nat ST.
  2: steps_to 0x62bb0%Z.
  2: replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  all: steps_to 0x62c3c%Z.
  all: release_frame FR0 ST (bv_unsigned sp + -16)%Z.
  all: steps_to 0x62d10%Z.
  (* [comment removed for export] *)
  all: carve_frame 32%nat ST. all: steps_to 0x267e8%Z.
  all: carve_frame 16%nat ST. all: steps_to 0x26874%Z. all: release_frame FR1 ST (bv_unsigned sp + -48)%Z. all: astep.
  all: steps_to 0x62d58%Z. all: release_frame FR0 ST (bv_unsigned sp + -16)%Z. all: astep. all: astep.
  all: astep.
  all: unfold pexit_prefix_post; sys_finish.
Qed.

Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  (* [comment removed for export] *)
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard dso : word)
      (cdt thr sec : byte) (tm1 : word),
    stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
    rw_cells rsegs m 0xa7fe8 [C4 z64] ->                                              (* [comment removed for export] *)
    rw_cells rsegs m 0x75e90 [C8 (Z_to_bv 64 0x72a58); C8 (Z_to_bv 64 0x72a50)] ->    (* [comment removed for export] *)
    rw_cells rsegs m 0x72a50 [C8 (Z_to_bv 64 0x267e8)] ->                            (* [comment removed for export] *)
    rw_cells rsegs m 0x77148 [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
    rw_cells rsegs m 0x75d70 [C8 (Z_to_bv 64 0x62c40); C8 z64] ->                     (* [comment removed for export] *)
    rw_cells rsegs m 0x76ea0 [C8 dso] ->
    pexit_tbl m ->
    rw_cells rsegs m 0xa8010 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells rsegs m 0xa8440 [C8 z64] -> rw_cells rsegs m 0xa8430 [C8 z64] ->
    rw_cells rsegs m 0x770e0 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells rsegs m 0x76ff0 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 guard] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0xa9000 <= lo)%Z ->
    (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
    implM rsegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x62d5c) fc None m (seg_rom rsegs)).
  Proof.
    intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO TBL LCH OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO SP47.
    unfold got_ssp, ssp_guard in GG, GU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind rsegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x62dc8) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x62dc8) fc None m' (seg_rom rsegs))).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      call pexit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact TBL
                              | exact MI | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM, got_ssp, ssp_guard, GLOBALS_TOP in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x62dc8)) with (Z_to_bv 64 0x62dc8) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    - (* [comment removed for export] *)
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Qed.
End ExitProof.
