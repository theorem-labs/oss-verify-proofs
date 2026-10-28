(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Spec LibWritev.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0StdioDefs_u Bs0Exit_run1_u Bs0Exit_run2_u Bs0Exit_run3_u Bs0StdioWrite_run1_u Bs0StdioWrite_run2_u Bs0StdioWrite_u
 Bs0_code_r1ff24_20000_u Bs0_code_r4b000_4c000_u Bs0_code_r4d000_4e000_u Bs0_code_r4e000_4f000_u  .
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.RdnPeelKit.
(* [comment removed for export] *)
Local Ltac rdn_side_fast := rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia_fast.
Local Ltac rdn_solve_fast :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (first [ RdnPeelKit.rdn_peel_many ltac:(idtac; rdn_side_fast) | rdn_peel1 ]; rdn_solve_fast)
  | |- _ => rdn_hyp
  end.
Local Ltac rdn_solve ::= rdn_solve_fast.

Ltac zaddr_rec H := zaddr H.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0xb83f0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0x9adf0 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC. destruct ec_ax as [ax AX].
  (* [comment removed for export] *)
  destruct (w1 ax regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1, ax_writes; destruct ax; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2, mem_w1, ax_writes; destruct ax; store_ok_peel; exact ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1, ax_writes; destruct ax; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve. }
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_994cc | exact E_994cc | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0x9adf0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct EC. destruct ec_ax as [ax AX]. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  destruct (w1 ax regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1, ax_writes; destruct ax; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w3b1 regs2 (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2, mem_w1, ax_writes; destruct ax; store_ok_peel; exact ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1, ax_writes; destruct ax; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve. }
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0xa04a8) with (0xa04a8 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write scfg regs3 mem3 model (bv_unsigned sp - 32) 0xb83f0 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0xa04a8 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; sok_stack ec_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1, ax_writes; destruct ax; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_994cc | exact E_994cc | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

#[using="Type"] Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0x9adf0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply srz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  srealizes RSEGS scfg (mkCfg (mkst regs (Z_to_bv 64 0x9adf0) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x9adf0) with (0x9adf0 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
