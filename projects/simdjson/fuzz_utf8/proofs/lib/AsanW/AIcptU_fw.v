(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge Cells InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA StepF StrwF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells ShadowTac F_syscalls StdioFiles Stdio_kit MonadF I_fwrite AExitU_wr AIos_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AIcptU_hmap AIcptU_fflush AIcptU_defs AIcptU_mem0 AIcptU_fw0.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition fwrite_i_post0_post (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v s2v s3v s4v s5v : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch []%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma fwrite_i_post0 : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp - 2128) -> stk asegs m (bv_unsigned sp - 2128) (bv_unsigned sp - 56) ->
  rw_cells asegs m (bv_unsigned sp - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  lo <= bv_unsigned sp - 2128 -> KHIGH <= lo ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fwrite_i_post0_post sp gp tp s6 s7 s8 s9 s10 s11 F fc rav s0v s1v s2v s3v s4v s5v lo m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 2128)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d74c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST STM FR LO KLO RI RSTK.
  pose proof (munch_refl []%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) in * by lia.
  replace (bv_unsigned sp - 56) with (bv_unsigned sp + -56) in * by lia.
  run_to 0%Z.
  pose proof (stk_merge asegs _ _ _ _ ST STM ltac:(lia)) as ST1. clear ST STM.
  release_frame FR ST1 (bv_unsigned sp).
  apply evtF_done. unfold fwrite_i_post0_post.
  do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
Lemma flags72_zx8 : forall flags : word, Z.land (bv_unsigned flags) 72 = 0 -> Z.land (bv_unsigned (zx32 flags)) 8 = 0.
Proof.
  intros flags H.
  assert (H8 : Z.land (bv_unsigned flags) 8 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 3) as [->|NE].
    - pose proof (f_equal (fun z => Z.testbit z 3) H) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
      change (Z.testbit 72 3) with true in T. change (Z.testbit 8 3) with true. exact T.
    - change 8 with (2^3). rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 3 i); [lia|]. apply Bool.andb_false_r. }
  unfold zx32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite Z.mod_small.
  - rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8. exact H8.
  - pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)). lia.
Qed.

Section Chains.
  Variables (T SLO SHI : Z).

  Theorem fwrite0_err_proof : fwrite0_err_stmt (icptU T) (icptU_rng T).
  Proof.
    unfold fwrite0_err_stmt. intros until guard. intros ST SEF [GS GU] IC MI -> -> -> -> LO GLO ALO SP16 RSTK RI [RBE RBO].
    pose proof IC as ((R1 & R2 & R3 & R4 & R5 & R6) & (M1 & M2 & B1 & B2 & TLO & THI & TAL)).
    unfold GLOBALS_TOP in GLO. unfold HMAP, BOFF_ERR, BOFF_OUT in *.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold FWRITE0_STUB. unfold hm_bucket0 in B1, B2. unfold got_ssp, ssp_guard in GS, GU. unfold file_cells in EFC.
    atop_facts.
    zstep.                                  (* [comment removed for export] *)
    eapply evtF_cut; [eapply (fwrite_i_pre RNG) with (lo := lo); first [eassumption | unfold KHIGH; lia]|].
    lazymatch goal with MIh : mem_inv asegs ?mm |- forall _, _ => post_call asegs mm end.
    replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) in * by lia.
    replace (bv_unsigned sp - 56) with (bv_unsigned sp + -56) in * by lia.
    (* [comment removed for export] *)
    call_sp (fwrite0_musl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo RSTDERR).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- _ \/ _ => right; reflexivity
         | |- rw_cells _ _ _ (file_cells _ _ _ _ _ _ _ _ _ _ _) => unfold file_cells; eassumption
         | |- stk _ _ _ _ => eassumption
         | |- _ => iprem0
         end.
    (* [comment removed for export] *)
    eapply evtF_cut; [eapply (fwrite_i_post0 RNG) with (lo := lo)|].
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- stk _ _ _ _ => (replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) by lia; replace (bv_unsigned sp - 56) with (bv_unsigned sp + -56) by lia; eassumption)
         | |- rw_cells _ _ _ _ => (replace (bv_unsigned sp - 56) with (bv_unsigned sp + -56) by lia; eassumption)
         | |- _ => unfold KHIGH in *; iprem0
         end.
    lazymatch goal with MIh : mem_inv asegs ?mm |- forall _, _ => post_call asegs mm end.
    apply evtF_done. unfold icpt_post.
    do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split. { unfold ssp_cells, got_ssp, ssp_guard. split; assumption. }
    split. { unfold icptU, icpt_rt, icpt_tab, HMAP, BOFF_ERR, BOFF_OUT, hm_bucket0.
             repeat match goal with |- _ /\ _ => split end; assumption. }
    lazymatch goal with CS : _ \/ _ |- stderr_file _ =>
      destruct CS as [(_ & -> & -> & -> & -> & ->)|[(_ & -> & -> & -> & ->)|(_ & _ & -> & -> & ->)]] end.
    all: unfold stderr_file; do 5 eexists; eassumption.
  Qed.

  Theorem fwrite0_out_proof : fwrite0_out_stmt (icptU T) (icptU_rng T).
  Proof.
    unfold fwrite0_out_stmt. intros until so_x. intros ST SOF [GS GU] IC MI -> -> -> -> LO GLO ALO SP16 RSTK RI [RBE RBO].
    pose proof IC as ((R1 & R2 & R3 & R4 & R5 & R6) & (M1 & M2 & B1 & B2 & TLO & THI & TAL)).
    unfold GLOBALS_TOP in GLO. unfold HMAP, BOFF_ERR, BOFF_OUT in *.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold FWRITE0_STUB. unfold hm_bucket0 in B1, B2. unfold got_ssp, ssp_guard in GS, GU. unfold file_cells in FC.
    atop_facts.
    zstep.                                  (* [comment removed for export] *)
    eapply evtF_cut; [eapply (fwrite_i_pre RNG) with (lo := lo); first [eassumption | unfold KHIGH; lia]|].
    lazymatch goal with MIh : mem_inv asegs ?mm |- forall _, _ => post_call asegs mm end.
    replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) in * by lia.
    replace (bv_unsigned sp - 56) with (bv_unsigned sp + -56) in * by lia.
    (* [comment removed for export] *)
    call_sp (fwrite0_musl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo RSTDOUT).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- _ \/ _ => left; reflexivity
         | |- rw_cells _ _ _ (file_cells _ _ _ _ _ _ _ _ _ _ _) => unfold file_cells; eassumption
         | |- stk _ _ _ _ => eassumption
         | |- _ => iprem0
         end.
    (* [comment removed for export] *)
    eapply evtF_cut; [eapply (fwrite_i_post0 RNG) with (lo := lo)|].
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- stk _ _ _ _ => (replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) by lia; replace (bv_unsigned sp - 56) with (bv_unsigned sp + -56) by lia; eassumption)
         | |- rw_cells _ _ _ _ => (replace (bv_unsigned sp - 56) with (bv_unsigned sp + -56) by lia; eassumption)
         | |- _ => unfold KHIGH in *; iprem0
         end.
    lazymatch goal with MIh : mem_inv asegs ?mm |- forall _, _ => post_call asegs mm end.
    apply evtF_done. unfold icpt_post.
    do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split. { unfold ssp_cells, got_ssp, ssp_guard. split; assumption. }
    split. { unfold icptU, icpt_rt, icpt_tab, HMAP, BOFF_ERR, BOFF_OUT, hm_bucket0.
             repeat match goal with |- _ /\ _ => split end; assumption. }
    lazymatch goal with CS : _ \/ _ |- stdout_file _ _ =>
      destruct CS as [(NZ & -> & -> & -> & -> & ->)|[(ZW & -> & -> & -> & ->)|(_ & NOWR & _)]] end.
    - (* [comment removed for export] *)
      destruct (so_active so_x) eqn:EA; [| exfalso; apply NZ; reflexivity].
      exists flags, mode, tail, bufbytes. cbn [so_act so_active so_buf so_lbf_nl so_first].
      split; [eassumption|]. split; [exact FL72|]. split; [eassumption|]. split; [exact BUFP|]. split; [exact BUFL|]. intros X; discriminate X.
    - (* [comment removed for export] *)
      destruct (so_active so_x) eqn:EA; [exfalso; cbv in ZW; discriminate ZW|].
      pose proof (INACT eq_refl) as EB.
      exists flags. eexists. exists tail, bufbytes. cbn [so_act so_active so_buf so_lbf_nl so_first]. rewrite EB in *.
      change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      split; [eassumption|]. split; [exact FL72|]. split; [eassumption|]. split; [exact BUFP|]. split; [exact BUFL|]. intros X; discriminate X.
    - exfalso. apply NOWR. apply flags72_zx8. exact FL72.
  Qed.
End Chains.
End CANSEC1.
