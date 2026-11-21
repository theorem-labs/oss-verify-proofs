(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.   (* port727: vdso_run_init (stdin0's run) *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require PropExec StdModel ShapeAlg ShapeLaws ModelAmb DrawDefs Spec U0ReadBase U0ReadStage
  U0Startup U0LPilotOOM U0LOpenFailBranch U0TargetPre.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PlainU0 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Mr Require Import MrRoom MrRulesU0.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MrP0 Require Import U0HeapPre U0HBase U0HConv U0TrTail U0RdLib U0RdInv U0RdRules U0RdGrow U0RdChunk U0RdLoop U0RdEnd
  U0LRdFrontA U0LRdFrontB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OSp := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec.
Module OTP := OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.U0TargetPre.

Section TOP.
Context {rc : runConstT}.
(* port727 (): over the launch input (argv = [a0s; path] by Hav), as RdFrontA: the
   ruled VLAUNCH + LOK and the launch's channel reader replace entry_stack_fits. The read loop's AmbIn and file system
   are the launch's, as RdFrontB's FRONTF. *)
Variables (sp0 : word) (a0s path : list byte) (inp : ProcInput) (rdraw : EntryDraw) (tid : word).
Local Notation envv := (in_envp inp) (only parsing).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fdata : list byte).
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
Local Notation stdin0 := (ModelAmb.amb_of inp (vdso_run_init (ed_vdso rdraw))) (only parsing).
Local Notation fs0 := (in_fs inp) (only parsing).
Hypothesis Hav : in_argv inp = [a0s; path].
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
Hypothesis Hcr : in_channel_reader inp = true.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
Hypothesis ME : U0Startup.main_entry sp0 inp mbase rdraw tid regs0 mem0.
Hypothesis Hbrk : valid_brk psegs brk.
Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
Hypothesis Hpne : path <> [].
Hypothesis Hpnd : path <> OSp.dot_path.
Hypothesis Hplen : (length path <= 4095)%nat.
Hypothesis HCAN : CAN = DrawDefs.canary_w rdraw.
Hypothesis HSEC : SECRET = bv_unsigned (DrawDefs.secret_w rdraw).
Hypothesis HATOP : ATOP = bv_unsigned sp0 - 8388608.

Variables (AI AIm : nat -> list bptr -> PState -> Model -> Prop).
Hypothesis RMF : rule_malloc_first AI 10.
Hypothesis RM : rule_malloc_grow AI AIm.
Hypothesis RF : rule_free_grow AI AIm.
Hypothesis AIm_perm : forall j X X' s mo, Permutation.Permutation X X' -> AIm j X s mo -> AIm j X' s mo.
Hypothesis AI_vm : forall j X s mo mo', AI j X s mo -> m_vmmaps mo' = m_vmmaps mo -> m_vm_materialized mo' = m_vm_materialized mo -> AI j X s mo'.
Hypothesis AI_end : forall j pb s mo, AI j [pb] s mo -> drv_state s /\ room (2 ^ 27) mo.
Hypothesis TPH : target_phase_h_stmt.

Let SP : Z := bv_unsigned sp0.
Let L : Z := Z.of_nat (length fdata).
Abbreviation GRD := (G_rd path stdin0 fs0 tid).
Abbreviation GPOST := (G_post stdin0 fs0 tid).
Abbreviation TOOM := (OSp.t_die OSp.msg_oom fs0).
Abbreviation TREF := (OSp.t_die OSp.msg_refused fs0).

Definition oom1_cont : Prop :=
  forall (M' : word -> option byte) (s' : PState) (mo' : Model)
         (y1 y5 y6 y7 x8 x9 y11 y12 y13 y14 y15 y16 y17 x18 x19 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31 : word),
    rd_base SP tid M' -> RHEAP s' [] M' -> OWN [] (GRD 0) s' mo' ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (SP - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 x8 x9
                                   (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 x18 x19 (Z_to_bv 64 3) (Z_to_bv 64 65536)
                                   x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                              bvmap_empty (Z_to_bv 64 0x14018) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') TOOM.
(* route (A): hdr_cont takes its own run, as RdLeafHdr's leaves (a generic RunCtx) state it; RdTop's
   uses below take RC_a1_1, and its parameters stay those of the leaves' calls (no mbase). *)
Definition hdr_cont {RCa1 : RunCtx} (P : Prop) (T : ShapeAlg.TSet) : Prop :=
  forall (j : nat) (pb : bptr) (buf cap : Z) (M : word -> option byte) (s : PState) (mo : Model)
         (x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    rd_inv SP tid fdata GPOST pb buf cap L M s mo -> AI j [pb] s mo -> 65536 <= cap <= 2 ^ 26 -> L < cap -> P ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (SP - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                                   y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 L) (Z_to_bv 64 3) (Z_to_bv 64 cap)
                                   (Z_to_bv 64 0x1fc79) (Z_to_bv 64 0) x24 x25 x26 x27 y28 y29 y30 y31)
                              bvmap_empty (Z_to_bv 64 0x13e6c) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.

Hypothesis LEAF_oom1 : oom1_cont.
Hypothesis LEAF_oom : oom_cont SP path stdin0 fs0 tid fdata TOOM.
Hypothesis LEAF_ref : ref_cont SP path stdin0 fs0 tid fdata TREF.
Hypothesis LEAF_short : hdr_cont (L < 6) (OSp.t_die OSp.msg_short fs0).
Hypothesis LEAF_over : hdr_cont (6 <= L < 6 + OTP.hdr_cfglen fdata) (OSp.t_die OSp.msg_overrun fs0).

Lemma SPr : 0x7fff80000000 <= SP <= 0x800000000000.
Proof. destruct Hvsp as (A & B & _). unfold sp_window_lo, sp_window_hi in *. unfold SP. lia. Qed.
Lemma SP16 : SP mod 16 = 0.
Proof. destruct Hvsp as (_ & _ & C). exact C. Qed.

Lemma t_body_has_nil : forall data fs, OSp.t_body data fs [].
Proof.
  intros data fs. unfold OSp.t_body.
  destruct (OSp.MAX_INPUT <=? _); [apply ShapeLaws.t_emit_has_nil|].
  destruct (_ <? 6)%nat; [apply ShapeLaws.t_emit_has_nil|].
  cbv zeta. destruct (_ <? _)%nat; [apply ShapeLaws.t_emit_has_nil|].
  destruct (_ - _ - _)%nat; [apply ShapeLaws.t_emit_has_nil | apply ShapeLaws.t_alt2_has_nil_l; apply ShapeLaws.t_exit_has_nil].
Qed.

Lemma end_top : end_cont SP stdin0 fs0 tid fdata AI (OSp.t_body fdata fs0).
Proof.
  intros j pb buf cap M s mo x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI HAI HCAP HL.
  fold L in RI, HL |- *.
  pose proof (Z.mod_pos_bound (OTP.hdr_cfg fdata) 32768 ltac:(lia)) as CR. fold (OTP.hdr_cfglen fdata) in CR.
  assert (TB0 : (OSp.MAX_INPUT <=? Z.of_nat (length fdata)) = false) by (apply Z.leb_gt; unfold OSp.MAX_INPUT; fold L; lia).
  destruct (Z_lt_le_dec L 6) as [S6|S6].
  -
    replace (OSp.t_body fdata fs0) with (OSp.t_die OSp.msg_short fs0).
    2:{ unfold OSp.t_body. rewrite TB0. replace (length fdata <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; unfold L in S6; lia). reflexivity. }
    eapply LEAF_short; eassumption.
  - destruct (Z_lt_le_dec L (6 + OTP.hdr_cfglen fdata)) as [OV|OK].
    +
      replace (OSp.t_body fdata fs0) with (OSp.t_die OSp.msg_overrun fs0).
      2:{ unfold OSp.t_body. rewrite TB0. replace (length fdata <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; unfold L in S6; lia).
          cbv zeta.
          replace (length fdata <? 6 + Z.to_nat ((bv_unsigned (nth 0 fdata (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 fdata (Z_to_bv 8 0))) mod 32768))%nat
            with true; [reflexivity|].
          symmetry. apply Nat.ltb_lt. unfold OTP.hdr_cfglen, OTP.hdr_cfg, OTP.hdr_b0, OTP.hdr_b1, L in *. lia. }
      eapply LEAF_over; try eassumption. lia.
    +
      rewrite (OTP.t_body_target fdata fs0) by (unfold OSp.MAX_INPUT, OTP.hdr_cfglen, L in *; lia).
      destruct (AI_end j pb s mo HAI) as [HDRV HROOM].
      eapply (rd_end_rz SP SPr SP16 HATOP stdin0 fs0 tid fdata Htid); [exact RI | lia | fold L; lia | exact HDRV | exact HROOM |].
      intros R' TP.
      replace fs0 with (m_fs mo).
      2:{ pose proof (ri_own _ _ _ _ _ _ _ _ _ _ _ RI) as [_ [_ HG]]. unfold G_post in HG. rewrite HG. reflexivity. }
      exact (TPH SP buf cap fdata R' M mo TP).
Qed.

Theorem read_phase_h :
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) regs0 (Z_to_bv 64 0x13d70) mem0 (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
                        (U0LPilotOOM.model0 sp0 inp rdraw tid brk mbase))
           (ShapeAlg.t_alt2 (OSp.t_die (OSp.msg_cannot_open path) fs0) (OSp.t_opened fdata fs0)).
Proof.
  pose proof SPr as SPR.
  assert (Hva' : valid_argv (in_argv inp)) by (rewrite Hav; exact Hva).
  eapply ShapeAlg.rz_conseq.
  2:{ apply ShapeLaws.t_alt2_congr_r. unfold OSp.t_opened.
      eapply ShapeAlg.t_eq_trans; [apply (SH_norm SP SPr fdata TOOM TREF (OSp.t_body fdata fs0) 10%nat 65536); [reflexivity | lia]|].
      apply ShapeLaws.t_alt2_congr_r. fold L.
      destruct (L <? 2 ^ 26) eqn:EL; [apply ShapeAlg.t_eq_refl|].
      apply Z.ltb_ge in EL. unfold OSp.t_body.
      replace (OSp.MAX_INPUT <=? Z.of_nat (length fdata)) with true by (symmetry; apply Z.leb_le; unfold OSp.MAX_INPUT; fold L; lia).
      apply ShapeAlg.t_eq_refl. }
  (* port727 (): RdFrontA's front_to_malloc and the carried open-fail branch are stated over the launch
; their launch premises are this section's. *)
  eapply (front_to_malloc sp0 a0s path inp rdraw tid regs0 mem0 brk mbase); try eassumption.
  - eapply U0LOpenFailBranch.open_err_branch_cannot_open; eassumption.
  - intros R M G1 G2 G3 G4 G8 G10 G18 G20 G21 FM MF.
    eapply (first_malloc_rz sp0 inp mbase rdraw tid regs0 mem0 Hva' Hve Hvsp ME HCAN HSEC HATOP brk Hvl Hlau path fdata
              Hfile Htid Hbrk Hcr AI 10%nat RMF TOOM (SH fdata TOOM TREF (OSp.t_body fdata fs0) 10 65536) R M);
      try eassumption.
    + apply ShapeLaws.t_emit_has_nil.
    + apply SH_nil; [apply ShapeLaws.t_emit_has_nil | apply ShapeLaws.t_emit_has_nil | ].
      apply t_body_has_nil.
    + intros pb buf M' s' mo' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x18 x24 x25 x26 x27 y28 y29 y30 y31 RI HAI.
      eapply (read_loop_rz SP SPr HATOP path stdin0 fs0 tid fdata Hfile Htid AI AIm RM RF AIm_perm AI_vm TOOM TREF (OSp.t_body fdata fs0));
        [apply ShapeLaws.t_emit_has_nil | apply ShapeLaws.t_emit_has_nil | apply t_body_has_nil | exact LEAF_oom | exact LEAF_ref | exact end_top
        | exact RI | lia | reflexivity | lia | exact HAI].
Qed.
End TOP.
