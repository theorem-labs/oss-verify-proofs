From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling RunWord RegsEquiv InitStack EntrySecret.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim ShapeP0 CeilP.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Segs RDriver_kit H_parser_inst.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Segs RDriver_kit AllocInst H_fuzz_stmt H_parser_inst.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Top Require AssembleP0.
From OssFuzzTheorems.pupnp.FuzzHttp.images Require Plain.
From OssFuzzTheorems.pupnp.FuzzHttp.images Require Ubsan.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import TSimS.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Top Require Import ShapeU.
Import ListNotations.
Open Scope Z_scope.

Local Notation rsU := OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0.Segs.rsegs (only parsing).

Definition imgU : Image := mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs.

Definition P0U_REAL (rsvU : Z) : Prop :=
  forall (sp0 : word) (VSP : valid_sp sp0) (rnd : EntryDraw) (brk0 mbase : word) (lim : Z) (inp : ProcInput),
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_brk rsU brk0 ->
    realizes rsU
      (mkCfg (init_ms rsU Ubsan.M.init_pc Ubsan.M.phdrs sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd)
             (init_model (segments_reserved rsU) brk0 mbase sp0 lim inp))
      (@T_P0g (ceilP sp0 VSP) rsvU rsU (in_argv inp) (init_model (segments_reserved rsU) brk0 mbase sp0 lim inp)).

Theorem fuzzhttp_ubsan_error_free_real : forall rsvU, P0U_REAL rsvU -> strong_universal_error_free_T_scfg ACFG imgP0 imgU.
Proof.
  intros rsvU HU [spA brkA mbA dA] [spB brkB mbB dB] inp VA VB VI.
  pose proof (valid_input_va_size _ VI) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in VA. cbn [imgP0] in VA.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in VB. cbn [imgU] in VB.
  destruct VA as (VSPA & VBRKA & VMBA & ESFA). destruct VB as (VSPB & VBRKB & VMBB & ESFB).
  pose proof VI as (VARGV & VENVP & _).
  pose proof (@OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top.AssembleP0.p0_realizes (guardP dA) (ceilP spA VSPA) spA (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) dA
                brkA mbA source_alloc_limit inp VSPA eq_refl VARGV VENVP ESFA eq_refl eq_refl VBRKA
                (@OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0.H_parser_inst.fuzz_one_P0_closed (guardP dA) (ceilP spA VSPA))) as RA.
  pose proof (HU spB VSPB dB brkB mbB target_alloc_limit inp VARGV VENVP ESFB VBRKB) as RB.
  pose proof (T_P0g_eq (ceilP spA VSPA) (ceilP spB VSPB) OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0.RDriver_kit.RSV rsvU spA brkA mbA spB brkB mbB inp VI
                VSPA VBRKA VMBA (ceilP_eq spA VSPA) VSPB VBRKB VMBB (ceilP_eq spB VSPB)
                (realizes_has_nil _ _ _ RA) (realizes_has_nil _ _ _ RB)) as TE.
  destruct (realizes_run_fields _ _ _ _ _ _ _ _ _ _ RA) as [EA TA].
  destruct (realizes_run_fields _ _ _ _ _ _ _ _ _ _ RB) as [EB TB].
  unfold strong_equiv_error_free_scfg, error_free. cbn [run_scfg imgP0 imgU bh_errors bh_traces].
  split; [exact EA|]. split; [exact EB|].
  intros tr. etransitivity; [exact (TA tr)|]. etransitivity; [exact (TE tr)|]. symmetry. exact (TB tr).
Qed.

Definition FZU : Prop :=
  forall (HGW : HasGuard) (HCEIL : HasCeiling),
    OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0.H_fuzz_stmt.fuzz_one_stmt OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0.AllocInst.AI_P0.

Lemma p0U_real : FZU -> P0U_REAL OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0.RDriver_kit.RSV.
Proof.
  intros FZ sp0 VSP rnd brk0 mbase lim inp VARGV VENVP ESF VBRK.
  exact (@OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Top.AssembleP0.p0_realizes (guardP rnd) (ceilP sp0 VSP) sp0 (in_argv inp) (in_envp inp)
           (in_uid inp) (in_hwcap inp) rnd brk0 mbase lim inp VSP eq_refl VARGV VENVP ESF eq_refl eq_refl VBRK (FZ (guardP rnd) (ceilP sp0 VSP))).
Qed.

Theorem fuzzhttp_ubsan_error_free_of : FZU -> strong_universal_error_free_T_scfg ACFG imgP0 imgU.
Proof. intros FZ. exact (fuzzhttp_ubsan_error_free_real _ (p0U_real FZ)). Qed.

Theorem fuzzhttp_ubsan_error_free : strong_universal_error_free_T_scfg ACFG imgP0 imgU.
Proof. exact (fuzzhttp_ubsan_error_free_of (fun HGW HCEIL => @OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0.H_parser_inst.fuzz_one_P0_closed HGW HCEIL)). Qed.
