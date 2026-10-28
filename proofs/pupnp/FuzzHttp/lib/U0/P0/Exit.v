(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Startup_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memset.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Startup_A Startup_B Stdio_base Stdio_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_atexit.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Definition rfuncs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x5b860, 0x5b861); (0x5b868, 0x5b86c); (0x5b870, 0x5b878)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp).
Lemma rfuncs_on_exit_spec : forall (reg : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
stk rsegs m lo (bv_unsigned sp) ->
atx_state reg m ->
rw_cells rsegs m 0x5baa8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
mem_inv rsegs m ->
(lo <= bv_unsigned sp - 48)%Z -> (0x5d000 <= lo)%Z ->
evt rsegs (rfuncs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x17bb0) fc None m (seg_rom rsegs)).
Proof.
intros until tm1. intros ST ((X1 & X2 & X3 & X4 & X5 & X6 & X7) & CB) LCH MI LO LOLO.
unfold RATX, RATX_CALLFN, REXIT_GUARD, RAEF_INCB in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x5b860, 0x5b861); (0x5b868, 0x5b86c); (0x5b870, 0x5b878)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 48%nat ST.
steps_to 0x251dc%Z.
lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
lstep.
destruct reg; cbn [negb andb orb] in *.
-
lstep. if_false.
lstep. try replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
lstep. lstep. try change (bv_swrap 32 (1 + -1))%Z with 0%Z. lstep. lstep. if_false.
steps_to 0x25464%Z.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
steps_to 0x13f44%Z.
lstep. lstep. lstep. if_false. lstep.
steps_to 0x251dc%Z.
lstep. lstep. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. lstep.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity).
lstep. try change (bv_swrap 32 (0 + -1))%Z with (-1)%Z. lstep. lstep. if_false.
steps_to 0x17bfc%Z. lstep. if_true.
steps_to 0x17c70%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
unfold rfuncs_on_exit_post, RATX. sys_finish.
-
lstep. if_true.
steps_to 0x17c70%Z.
release_frame FR ST (bv_unsigned sp). astep. astep.
lstep. try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (vm_compute; reflexivity). lstep. if_false. lstep.
unfold rfuncs_on_exit_post, RATX. sys_finish.
Qed.
Definition rlibc_exit_fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x2b6c8, 0x2b6c8 + 1)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' 0x2b6c8 [C1 (Z_to_bv 8 1)].
Lemma rlibc_exit_fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m 0x2a158 [C8 (Z_to_bv 64 0x2a0b0); C8 (Z_to_bv 64 0x2a0a8)] ->
rw_cells rsegs m 0x2a0a8 [C8 (Z_to_bv 64 0x13a8c)] ->
rw_cells rsegs m 0x2b6c8 [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m 0x2a0f0 [C8 (Z_to_bv 64 0x17c78); C8 z64] ->
rw_cells rsegs m 0x2b180 [C8 (Z_to_bv 64 0x2b180)] ->
mem_inv rsegs m ->
(lo <= bv_unsigned sp - 48)%Z -> (0x5d000 <= lo)%Z ->
evt rsegs (rlibc_exit_fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x17d48) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros ST GF FA FIN GCX DSO MI LO LOLO.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x2b6c8, 0x2b6c8 + 1)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 32%nat ST. steps_to 0x13a8c%Z.
carve_frame 16%nat ST. steps_to 0x13b14%Z. release_frame FR0 ST (bv_unsigned sp + -32)%Z. astep. astep.
steps_to 0x17d8c%Z. release_frame FR ST (bv_unsigned sp). astep. astep. astep.
unfold rlibc_exit_fini_post. sys_finish.
Qed.
Definition rexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x17e00) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1ab58) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x5ba80, 0x5ba80 + 4); (0x2b6c8, 0x2b6c8 + 1);
(0x5b860, 0x5b861); (0x5b868, 0x5b86c); (0x5b870, 0x5b878)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -16)
/\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
/\ rw_cells rsegs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m' 0x5ba80 [C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m' 0x2b6c8 [C1 (Z_to_bv 8 1)].
Lemma rexit_prefix_spec : forall (reg : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
(cdt thr sec : byte) (tm1 : word),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
rw_cells rsegs m 0x5ba80 [C4 z64] ->
rw_cells rsegs m 0x2a158 [C8 (Z_to_bv 64 0x2a0b0); C8 (Z_to_bv 64 0x2a0a8)] ->
rw_cells rsegs m 0x2a0a8 [C8 (Z_to_bv 64 0x13a8c)] ->
rw_cells rsegs m 0x2b6c8 [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m 0x2a0f0 [C8 (Z_to_bv 64 0x17c78); C8 z64] ->
rw_cells rsegs m 0x2b180 [C8 (Z_to_bv 64 0x2b180)] ->
rw_cells rsegs m 0x5baa8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
atx_state reg m ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
(0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> (0x5d000 <= lo)%Z ->
evt rsegs (rexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x17d94) fc None m (seg_rom rsegs)).
Proof.
intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH AX MI -> -> Ht LO LOLO.
destruct AX as [(X1 & X2 & X3 & X4 & X5 & X6 & X7) CB]. unfold RAEF_INCB in CB.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x5ba80, 0x5ba80 + 4); (0x2b6c8, 0x2b6c8 + 1);
(0x5b860, 0x5b861); (0x5b868, 0x5b86c); (0x5b870, 0x5b878)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 16%nat ST.
do 6 lstep.
replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
lstep. lstep.
amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
lstep. if_false. amo_step. lstep. if_false.
lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
steps_to 0x17bb0%Z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AX : atx_state reg mx) by (exact (conj (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 X7)))))) CB)) end.
clear X1 X2 X3 X4 X5 X6 X7 CB.
call_sp (rfuncs_on_exit_spec reg);
[ exact ST | exact AX | exact LCH | exact MI | lia | lia | ].
astep.
call_sp rlibc_exit_fini_spec;
[ hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | hyp_by_addr | lia | lia | ].
astep.
unfold rexit_prefix_post, RATX. sys_finish.
Qed.
Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  #[using="stdio_exit_spec"] Lemma exit_spec : forall (reg : bool) (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word),
    stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells rsegs m 0x5ba80 [C4 z64] ->
    rw_cells rsegs m 0x2a158 [C8 (Z_to_bv 64 0x2a0b0); C8 (Z_to_bv 64 0x2a0a8)] ->
    rw_cells rsegs m 0x2a0a8 [C8 (Z_to_bv 64 0x13a8c)] ->
    rw_cells rsegs m 0x2b6c8 [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m 0x2a0f0 [C8 (Z_to_bv 64 0x17c78); C8 z64] ->
    rw_cells rsegs m 0x2b180 [C8 (Z_to_bv 64 0x2b180)] ->
    rw_cells rsegs m 0x5baa8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    atx_state reg m ->
    rw_cells rsegs m 0x5bed8 [C8 z64] -> rw_cells rsegs m 0x5bec8 [C8 z64] ->
    rw_cells rsegs m 0x2b658 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells rsegs m 0x2b568 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells rsegs m 0x2a150 [C8 (Z_to_bv 64 0x5ba88)] -> rw_cells rsegs m 0x5ba88 [C8 guard] ->
    mem_inv rsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> (0x5d000 <= lo)%Z ->
    (bv_unsigned sp <= 2^47)%Z ->
    implM rsegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x17d94) fc None m (seg_rom rsegs)).
  Proof.
    intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH AX OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO SP47.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.

    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind rsegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x17e00) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x17e00) fc None m' (seg_rom rsegs))).
    -
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      call (rexit_prefix_spec reg); [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO
                              | exact LCH | exact AX | exact MI | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0x17e00)) with (Z_to_bv 64 0x17e00) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
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
