(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_13084_14000 RCode_15000_16000 RCode_17000_18000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import MuslTac StdioDefs Exit_run1 Exit_run2 Exit_run3 StdioWrite_run1 StdioWrite_run2 StdioWrite.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := rl_zaddr H.

(* [comment removed for export] *)
Lemma E_1579c : is_ecall W_1579c = true. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP3.
  Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL} {RD : RelocData RL} {RW : RelocRW RL RD}.
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.
End VP3.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VT1.
  Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL} {RD : RelocData RL} {RW : RelocRW RL RD}.
Theorem exit_tail_clean :
  forall regs mem model (sp code : word) (wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = rl dF_15800 0x1586c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem (0x1f530 + dA_1f440) wp1 rp1 ->
  file_clean mem (0x1f440 + dA_1f440) wp2 rp2 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (rl dF_1771c 0x1771c) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  rl_dwin_bounds.
  intros regs mem model sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK G F1 F2 Hh Hlazy.
  destruct (w3a regs mem (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2) as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  eapply rz_exit_at; [exact F_1579c | exact E_1579c | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.
End VT1.

Section VT2.
  Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL} {RD : RelocData RL} {RW : RelocRW RL RD}.
Theorem exit_tail_flush :
  forall regs mem model (sp code : word) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = rl dF_15800 0x1586c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem (0x1f440 + dA_1f440) wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (rl dF_1771c 0x1771c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  rl_dwin_bounds.
  intros regs mem model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending Hsp Hs0 Hra SPlo SPhi SOK G F2 SP Hh Hlazy Hfd.
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  rl_zaddr P1l; rl_zaddr P1wp; rl_zaddr P1wb; rl_zaddr P1wr; rl_zaddr P1buf; rl_zaddr P1bsz; rl_zaddr P1fd; rl_zaddr P1rp; rl_zaddr P1re.
  (* [comment removed for export] *)
  destruct G as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w3b1 regs mem (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ repeat split; [rl_zaddr Gnl|rl_zaddr Gofl|rl_zaddr Gin|rl_zaddr Gout|rl_zaddr Gerr]; rdn_solve. }
  1:{ repeat split; rl_zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (rl dF_1771c 0x177cc) with (rl dF_1771c 0x177cc) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a mem sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) (0x1f530 + dA_1f440) wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (rl dF_1771c 0x177cc) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a; sok_stack SOK
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a; rl_zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a; repeat rdn_peel1; exact BYTES
    | reflexivity
    | rl_ret_ok
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct F2 as (F2l & F2wp & F2wb & F2rp & F2re).
    rl_zaddr F2l; rl_zaddr F2wp; rl_zaddr F2wb; rl_zaddr F2rp; rl_zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a; rl_zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a; rl_zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_1579c | exact E_1579c | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.
End VT2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
