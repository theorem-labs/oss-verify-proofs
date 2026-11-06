(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LibWritev.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefStdioDefs RefExit_run1 RefExit_run2 RefExit_run3 RefStdioWrite_run1 RefStdioWrite_run2 RefStdioWrite RefExit RefExitAx_run Ref_code_13894_14104 Ref_code_1b104_1c2fc Ref_code_1d2fc_1e5f0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stdio_globals1 (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x56a3b) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x56e60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x26540) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26458)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x26630) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26548)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x26450) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26368)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x567fc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x26338) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26338)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x264e4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x26480) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x26490) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x26460) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x26468) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).      (* [comment removed for export] *)

(* [comment removed for export] *)
Record exit_common1 (regs : bvmap 5 word) (mem : word -> option byte)
       (sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
  ec1_sp   : getr regs 2 = sp;
  ec1_tp   : getr regs 4 = tp;
  ec1_a0   : getr regs 10 = code;
  ec1_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  ec1_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  ec1_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  ec1_tplo : (168 <= bv_unsigned tp)%Z;
  ec1_tphi : (bv_unsigned tp <= 4294967296)%Z;
  ec1_tid  : (0 < tid < 2147483648)%Z;
  ec1_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  ec1_lock : rdn RSEGS mem (Z_to_bv 64 0x56a18) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec1_fe   : rdn RSEGS mem (Z_to_bv 64 0x25328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x25290));
  ec1_fs   : rdn RSEGS mem (Z_to_bv 64 0x25330) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x25288));
  ec1_fa   : rdn RSEGS mem (Z_to_bv 64 0x25288) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13950));
  ec1_comp : rdn RSEGS mem (Z_to_bv 64 0x26688) 1%nat = Some [Z_to_bv 8 0];
  ec1_g1   : rdn RSEGS mem (Z_to_bv 64 0x252d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1b9dc));
  ec1_g2   : rdn RSEGS mem (Z_to_bv 64 0x252d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  ec1_glob : stdio_globals1 mem;
  ec1_ax   : atexit_one mem;
  ec1_err  : file_clean mem 0x26368 wp2 rp2
}.

(* [comment removed for export] *)
Definition exit_pre1 (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop :=
  exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
    exit_common1 regs mem sp tp code tid wp2 rp2
    /\ m_halted model = None /\ m_vm_lazy model = []
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x26548 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit1_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common1 regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x26548 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x1baf8 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  (* [comment removed for export] *)
  pose proof ec1_glob0 as (Gnl & Gofl & Gin & Gout & Gerr & Glk & Gdso & Gil & Giw & Gib & Gir & Gie).
  destruct (w1x regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1x; first [store_ok_peel; exact ec1_sok0 | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec1_err0 as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2, mem_w1x; store_ok_peel; exact ec1_sok0. }
  1:{ repeat split; unfold mem_w2, mem_w1x; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1x; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1x; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_1b900 | exact E_1b900 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit1_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common1 regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x1baf8 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  pose proof ec1_glob0 as (Gnl & Gofl & Gin & Gout & Gerr & Glk & Gdso & Gil & Giw & Gib & Gir & Gie).
  destruct (w1x regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1x; first [store_ok_peel; exact ec1_sok0 | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct (w3b1 regs2 (mem_w2 (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2, mem_w1x; store_ok_peel; exact ec1_sok0. }
  1:{ repeat split; unfold mem_w2, mem_w1x; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1x; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x1de34) with (0x1de34 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x26548 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x1de34 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2, mem_w1x; sok_stack ec1_sok0
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1x; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1x; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2, mem_w1x; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec1_err0 as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1x; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1x; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_1b900 | exact E_1b900 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit1 : forall regs mem model code pending,
  exit_pre1 regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x1baf8 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit1_clean; eassumption.
  - eapply ref_exit1_flush; eassumption.
Qed.

(* [comment removed for export] *)
Corollary ref_exit1_Z : forall regs mem model code pending,
  exit_pre1 regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x1baf8) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x1baf8) with (0x1baf8 : word) by (apply bv_eq; reflexivity).
  apply ref_exit1; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
