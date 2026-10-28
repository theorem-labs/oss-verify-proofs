(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes Spec LibWritev
  Frame. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10StdioDefs_u Pm10ExitAx_u Pm10Exit_run1_u Pm10Exit_run2_u Pm10Exit_run3_u Pm10StdioWrite_run1_u Pm10StdioWrite_run2_u Pm10StdioWrite_u
 Pm10_code_a5000_a6000_u     .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

Ltac outside_all :=
  intros; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; unfold RS_all; cbn [outside]; unfold in_rng, LIBENV_LO, LIBENV_LEN, HSCR, AX in *;
  unorm; repeat split; try exact I; lia.
Ltac rdn_solve_x FMF :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; rdn_solve_x FMF)
  | |- _ => erewrite (frame_mod_rdn RSEGS _ _ _ _ _ FMF); [unfold mem_w1; rdn_solve | outside_all | nowrap_tac]
  end.
Ltac rdn_cross FMF := unfold mem_w3a, mem_w2; rdn_solve_x FMF.
Ltac sok_cross FMF SOK :=
  unfold mem_w3a, mem_w2; store_ok_peel; eapply frame_mod_store_ok; [exact FMF|]; unfold mem_w1; store_ok_peel; exact SOK.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

Section AX.
Variable HInv : (word -> option byte) -> Prop.
Hypothesis HInv_stable : forall (m m' : word -> option byte) (spw : word),
  (4294967296 <= bv_unsigned spw - 144)%Z ->
  HInv m -> frame_mod m m' [(Z_to_bv 64 (bv_unsigned spw - 144), 144%Z); (Z_to_bv 64 AX, 0x224%Z)] -> HInv m'.
Variable hs : list (Z * Z).
Hypothesis HLEN : (Z.of_nat (length hs) <= 32)%Z.
Hypothesis HOK : Forall (fun h => handler_ok HInv (fst h) (snd h)) hs.

Lemma w1F : forall regs mem (sp tp code : word) (tid : Z) (wp2 rp2 : word),
  exit_common regs mem sp tp code tid wp2 rp2 -> atexit_state mem hs -> HInv mem ->
  exists regsB memF,
    msteps RSEGS (mkst regs (0xa7160 : word) mem (seg_rom RSEGS)) (mkst regsB (0xa7114 : word) memF (seg_rom RSEGS))
    /\ getr regsB 2 = Z_to_bv 64 (bv_unsigned sp - 16) /\ getr regsB 8 = code /\ getr regsB 1 = Z_to_bv 64 0xa71c8
    /\ frame_mod (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) memF (RS_all sp).
Proof.
  intros regs mem sp tp code tid wp2 rp2 EC AS HI. destruct EC.
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  set (mem1 := mem_w1 mem sp (getr regs 1) (getr regs 8) tid) in *.
  eassert (FR1 : frame_mod mem mem1 _).
  { subst mem1. unfold mem_w1. repeat (apply fm_wb; [| zsimp; lia]). apply (frame_mod_refl _ []). }
  destruct ec_glob as (Gnl & _).
  destruct (wF HInv HInv_stable sp (getr regs1 8) (getr regs1 9) (getr regs1 18) (getr regs1 19) hs (seg_rom RSEGS)
               ec_splo ec_sphi HLEN HOK regs1 mem1 R1sp R1ra eq_refl eq_refl eq_refl eq_refl)
    as (regsF & memF & RUNF & F2 & F8 & F9 & F18 & F19 & F4 & F3 & FMF & HIF).
  { subst mem1. unfold mem_w1. store_ok_peel. exact ec_sok. }
  { subst mem1. unfold mem_w1. zaddr Gnl. rdn_solve. }
  { eapply atexit_state_frame; [exact HLEN | exact AS | exact FR1 |].
    intros x Hx. cbn [outside app]. unfold in_rng. zsimp. unorm. repeat split; try exact I; lia. }
  { eapply (HInv_stable mem mem1 sp); [exact ec_splo | exact HI|]. eapply frame_mod_weaken; [| exact FR1].
    intros x Hx. cbn [outside app] in *. unfold in_rng, AX in *. revert Hx. zsimp. unorm. intros Hx. repeat split; try exact I; lia. }
  destruct (w1b regsF memF (seg_rom RSEGS)) as (regsB & RUNB & B1 & BO).
  exists regsB, memF.
  split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; eassumption|].
  split; [rewrite BO by discriminate; exact F2|].
  split; [rewrite BO by discriminate; rewrite F8; exact R1s0|].
  split; [exact B1 | exact FMF].
Qed.

Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0xc4c58 wp1 rp1 ->
  atexit_state mem hs -> HInv mem ->
  m_halted model = None -> m_vm_lazy model = [] ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0xa7160 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 AS HI Hh Hlazy.
  destruct (w1F regs mem sp tp code tid wp2 rp2 EC AS HI) as (regs1 & memF & RUN1 & R1sp & R1s0 & R1ra & FMF).
  destruct EC.

  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.

  destruct (w2 regs1 memF (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (first [ eapply frame_mod_store_ok; [exact FMF|]; unfold mem_w1; store_ok_peel; exact ec_sok
                  | erewrite (frame_mod_rdn RSEGS _ _ _ _ _ FMF); [unfold mem_w1; rdn_solve | outside_all | nowrap_tac] ]).
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.

  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 memF sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ sok_cross FMF ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; rdn_cross FMF. }
  1:{ repeat split; zaddr_goal; rdn_cross FMF. }
  1:{ repeat split; zaddr_goal; rdn_cross FMF. }
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.

  eapply rz_exit_at; [exact F_a5080 | exact E_a5080 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  atexit_state mem hs -> HInv mem ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0xa7160 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP AS HI Hh Hlazy Hfd.
  destruct (w1F regs mem sp tp code tid wp2 rp2 EC AS HI) as (regs1 & memF & RUN1 & R1sp & R1s0 & R1ra & FMF).
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.

  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.

  destruct (w2 regs1 memF (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (first [ eapply frame_mod_store_ok; [exact FMF|]; unfold mem_w1; store_ok_peel; exact ec_sok
                  | erewrite (frame_mod_rdn RSEGS _ _ _ _ _ FMF); [unfold mem_w1; rdn_solve | outside_all | nowrap_tac] ]).
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.

  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w3b1 regs2 (mem_w2 memF sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ sok_cross FMF ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; rdn_cross FMF. }
  1:{ repeat split; zaddr_goal; rdn_cross FMF. }
  eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.

  replace (Z_to_bv 64 0xac954) with (0xac954 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 memF sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write scfg regs3 mem3 model (bv_unsigned sp - 32) 0xc4c58 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0xac954 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    |
      subst mem3; unfold mem_w3a, mem_w2; store_ok_peel;
      eapply (store_ok_sub _ _ _ _ 144%nat); [ | eapply frame_mod_store_ok; [exact FMF|]; unfold mem_w1; store_ok_peel; exact ec_sok | | ]; zsimp; lia
    | lia | lia
    |   split; subst mem3; zaddr_goal; rdn_cross FMF
    |   split; subst mem3; rdn_cross FMF
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2; repeat rdn_peel1;
      erewrite (frame_mod_rdn RSEGS _ _ _ _ _ FMF);
        [ unfold mem_w1; repeat rdn_peel1; exact BYTES
        | intros; unfold RS_all; cbn [outside]; unfold in_rng, LIBENV_LO, LIBENV_LEN, HSCR, AX in *; unorm; repeat split; try exact I; lia
        | unorm; lia ]
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; zaddr_goal; rdn_cross FMF | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; zaddr_goal; rdn_cross FMF | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply srz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_a5080 | exact E_a5080 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit_ax : forall regs mem model code pending,
  exit_pre regs mem model code pending -> atexit_state mem hs -> HInv mem ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0xa7160 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES) AS HI.
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply srz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

Corollary ref_exit_ax_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending -> atexit_state mem hs -> HInv mem ->
  srealizes RSEGS scfg (mkCfg (mkst regs (Z_to_bv 64 0xa7160) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0xa7160) with (0xa7160 : word) by (apply bv_eq; reflexivity).
  apply ref_exit_ax; assumption.
Qed.
End AX.

Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending -> atexit_state mem [] ->
  srealizes RSEGS scfg (mkCfg (mkst regs (0xa7160 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending EP AS.
  apply (ref_exit_ax (fun _ => True) (fun _ _ _ _ _ _ => I) [] ltac:(cbn; lia) (Forall_nil _) regs mem model code pending EP AS I).
Qed.

Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending -> atexit_state mem [] ->
  srealizes RSEGS scfg (mkCfg (mkst regs (Z_to_bv 64 0xa7160) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0xa7160) with (0xa7160 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
