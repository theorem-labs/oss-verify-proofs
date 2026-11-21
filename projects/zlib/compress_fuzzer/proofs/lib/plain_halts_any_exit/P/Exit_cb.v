(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image MonadX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Export Layout F_atexit Exit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Str_tac Startup_glue Stdio_iface F_stdio_write F_stdout_write F_stdio_exit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_compress_fuzzer_repro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation psegs := Image.psegs.

Definition AEF_EXIT_STATUS : Z := 77.

Definition RGOT_STDOUTP : Z := 0x29538.
Definition RSTDOUTP : Z := 0x294e0.
Definition R_FFLUSH : Z := 0x225e8.
Definition R__EXIT : Z := 0x282d4.

Definition EXITCB_DEPTH : Z := 256.

Definition adp_cells_cb (m : mem) : Prop :=
     rw_cells psegs m RINIT_FLAG [C1 (Z_to_bv 8 1)]
  /\ rw_cells psegs m RIN_CB [C1 (Z_to_bv 8 1)]
  /\ rw_cells psegs m RATX_FIN [C1 (Z_to_bv 8 0)]
  /\ rw_cells psegs m RATX_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1)]
  /\ rw_cells psegs m RATX_HEAD [C8 (Z_to_bv 64 RATX_BUILTIN); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 R_CALL)]
  /\ rw_cells psegs m RATX_A0 [C8 (Z_to_bv 64 R_AEF_GUARD)].

Section ExitCb.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.

  Definition cb_exit_prog : M St Empty_set :=
    stdout_exit_flush get_so set_so ;;; msys (NExit AEF_EXIT_STATUS) dec_exit.

  Lemma exit_cb_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word),
    stk psegs m lo (bv_unsigned sp) ->
    rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->
    rw_cells psegs m 0x5ab68 [C4 z64] ->
    adp_cells_cb m ->
    rw_cells psegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells psegs m RGOT_STDOUTP [C8 (Z_to_bv 64 RSTDOUTP)] ->
    rw_cells psegs m RSTDOUTP [C8 (Z_to_bv 64 RSTDOUT)] ->
    stdout_file m (get_so s) ->
    rw_cells psegs m 0x29570 [C8 (Z_to_bv 64 0x5ab70)] -> rw_cells psegs m 0x5ab70 [C8 guard] ->
    mem_inv psegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - EXITCB_DEPTH)%Z -> (0x5c000 <= lo)%Z ->
    implM psegs cb_exit_prog s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x206ac) fc None m (seg_rom psegs)).
  Proof.
    intros until tm1. intros ST TDa EXL ATX LCH GSO PSO SOF GG GU MI -> -> Ht LO LOLO.
    destruct ATX as (AL & ACB & AFIN & ALCK & AHD & AA0).
    unfold RINIT_FLAG, RIN_CB, RATX_FIN, RATX_LOCK, RATX_HEAD, RATX_A0, RATX_BUILTIN, R_CALL, R_AEF_GUARD, RLIBC_HEAD,
           RGOT_STDOUTP, RSTDOUTP, EXITCB_DEPTH in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    unfold file_cells in FC.
    remember (get_so s) as so eqn:ESO.
    unfold cb_exit_prog.
    eapply (implM_bind psegs _ _ s
              (fun _ s' ms' => exists ra' gp' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp' (Z_to_bv 64 RTP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x15e4c) fc None m' (seg_rom psegs)
                 /\ stk psegs m' lo (bv_unsigned sp + -80) /\ mem_inv psegs m')).
    -
      unfold stdout_exit_flush. apply (implM_rdso get_so). rewrite <- ESO.
      eapply (implM_evt psegs). 2:{ intros ms' H; exact H. } cbv beta.
      pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp); (0x5ab68, 0x5ab6c); (0x5a948, 0x5a960); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU.
      pose proof (wmono_refl psegs m) as WM.

      carve_frame 16%nat ST.
      do 6 lstep.
      replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
        by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
      lstep. lstep.
      amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
      lstep. if_false. amo_step. lstep. if_false.
      lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
      lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
      lstep. lstep.

      carve_frame 48%nat ST.
      xsteps_to 0x2822c%Z. xstep. xstep. xstep.
      xsteps_to 0x15e24%Z.

      xstep. xstep.
      carve_frame 16%nat ST.
      xsteps_to 0x225e8%Z.

      carve_frame 32%nat ST.
      xsteps_to 0x2263c%Z.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - RSP LO LOLO; lia).
      assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
      assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
      { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.eq_dec i 6) as [->|NE].
        - pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
          change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
        - change 64 with (2^6). rewrite Z.pow2_bits_eqb by lia.
          destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }

      step. step.
      destruct (0 <? zlength (so_buf so)) eqn:CF.
      +
        pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
        assert (ACT : so_active so = true).
        { destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
        rewrite ACT in FC |- *.
        step. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
        do 4 step. step.
        rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
        replace (Z_to_bv 64 (if so_first so then 143108 else 142700) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
          by (rewrite <- ESO; reflexivity).
        apply evt_done.
        eapply implM_post_evt'.
        { eapply (stdout_writefn_proof get_so set_so get_set set_set) with (lo := lo) (S := 0) (s := []) (flags := flags) (mode := mode) (tail := tail) (canary := guard);
            [ rewrite <- ESO; exact ACT
            | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite <- ESO; exact FC
            | exact FL64
            | rewrite <- ESO; eapply CB_prefix_bytes_at; [exact BUF| rewrite LTB; exact BUFP]
            | rewrite <- ESO; exact BUFL
            | apply bytes_at_nil; clear; lia
            | reflexivity | reflexivity | reflexivity
            | rewrite ESP; exact ST | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | exact LOLO
            | split; [exact GG | exact GU] | exact MI
            | unfold zlength; cbn; clear; lia | clear; lia | unfold zlength; cbn; clear; lia
            | left; reflexivity
            | left; reflexivity ]. }
        cbv beta. intros [] st2 ms2 PO2.
        destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
        rewrite ESP in MU2, ST2. unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2. try rewrite <- ESO.
        rewrite (ret_pc_even 140892) by (cbn; lia).
        transport_after_call psegs m1 m2 MU2 WM2.
        unfold stdout_cells, file_cells in FC2. cbn [so_buf so_after zlength length Z.of_nat] in FC2. rewrite Z.add_0_r in FC2.

        xsteps_to 0x226f0%Z.
        xstep. xstep. xstep. xstep. xstep. xstep. xstep.
        release_frame FR2 ST2 (bv_unsigned sp + -80).
        apply evt_done. do 30 eexists. split; [ | split; [exact ST2 | exact MI2] ].
        reflexivity.
      +
        pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
        assert (E0 : so_buf so = []).
        { destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
        rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
        step. if_refl.

        xsteps_to 0x226f0%Z.
        xstep. xstep. xstep. xstep. xstep. xstep. xstep.
        release_frame FR2 ST (bv_unsigned sp + -80).
        apply evt_done. first [apply implM_ret | idtac]. apply evt_done.
        do 30 eexists. split; [ | split; [exact ST | exact MI] ].
        reflexivity.
    -
      cbv beta. intros [] s' ms' PO.
      destruct PO as (ra' & gp' & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 &
                      x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & -> & ST' & MI').
      pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp)]%Z m') as MU'.
      pose proof (wmono_refl psegs m') as WM'.
      apply implM_sys.
      lstep. lstep.
      carve_frame 16%nat ST'.
      lstep. lstep. lstep. lstep. lstep.
      step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H ].
  Time Qed.
End ExitCb.

Definition at_exit_cb {St : Type} (get_so : St -> stdout_st) (s : St) (ms : machine_state) : Prop :=
  exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo code t : Z) (td0 td1 td2 td3 guard : word)
         (cdt thr sec : byte) (tm1 : word),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x206ac) fc None m (seg_rom psegs)
    /\ stk psegs m lo (bv_unsigned sp)
    /\ rw_cells psegs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m 0x5ab68 [C4 z64]
    /\ adp_cells_cb m
    /\ rw_cells psegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells psegs m RGOT_STDOUTP [C8 (Z_to_bv 64 RSTDOUTP)]
    /\ rw_cells psegs m RSTDOUTP [C8 (Z_to_bv 64 RSTDOUT)]
    /\ stdout_file m (get_so s)
    /\ rw_cells psegs m 0x29570 [C8 (Z_to_bv 64 0x5ab70)] /\ rw_cells psegs m 0x5ab70 [C8 guard]
    /\ mem_inv psegs m
    /\ tp = Z_to_bv 64 RTP /\ a0 = Z_to_bv 64 code
    /\ (0 < t < 4194304)%Z /\ (lo <= bv_unsigned sp - EXITCB_DEPTH)%Z /\ (0x5c000 <= lo)%Z.

Lemma exit_cb_from_at {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) :
  (forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
  forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop) ms,
    at_exit_cb get_so s ms -> implM psegs (cb_exit_prog get_so set_so) s Q ms.
Proof.
  intros GS SS s Q ms H.
  destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & code & t &
                 td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & -> & H).
  destruct H as (ST & TD & EXL & ATX & LCH & GSO & PSO & SOF & GG & GU & MI & Htp & Ha0 & Ht & LO & LOLO).
  eapply (exit_cb_spec get_so set_so GS SS s Q);
    [exact ST | exact TD | exact EXL | exact ATX | exact LCH | exact GSO | exact PSO | exact SOF | exact GG | exact GU | exact MI
    | exact Htp | exact Ha0 | exact Ht | exact LO | exact LOLO].
Qed.

Lemma exit_cb_bind_from_at {St A : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) (k : Empty_set -> M St A) :
  (forall s so, get_so (set_so so s) = so) -> (forall s so so', set_so so' (set_so so s) = set_so so' s) ->
  forall (s : St) (Q : A -> St -> machine_state -> Prop) ms,
    at_exit_cb get_so s ms -> implM psegs (mbind (cb_exit_prog get_so set_so) k) s Q ms.
Proof.
  intros GS SS s Q ms H.
  eapply implM_bind; [eapply (exit_cb_from_at get_so set_so GS SS s (fun _ _ _ => False)); exact H | intros [] ].
Qed.
