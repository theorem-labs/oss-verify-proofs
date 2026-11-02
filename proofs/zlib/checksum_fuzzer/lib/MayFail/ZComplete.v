(** Composition for the unchanged full catalog statement.
    The remaining runtime contracts below are premises to be proved, not axioms
    and not an accepted proof of plain_halts. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OssFuzzTheorems.Core Require Import Shapes.
From OssFuzzTheorems.zlib.checksum_fuzzer Require Statements Images.
From OssFuzzTheorems.zlib.checksum_fuzzer.images Require Plain.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI5b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI5c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZImage.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import TraceHalting.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
Definition zlib_runtime_contracts : Prop :=
  forall rc : RunCeil, exists API : @AllocAPI rc src0_msyms,
    AllocExtra src0_msyms (aa_MR API) /\
    lib_contract_x_all (rc:=rc) (LS:=checksum_shape)
      src0_msyms API LIBPC RA_LIB EMPTY LIB_STACK.
Lemma checksum_room_calls : forall n k b,
  @room_calls checksum_shape n k b.
Proof. intros n k. induction k; intros b; cbn [room_calls lib_room lib_delta checksum_shape]; auto. Qed.
Lemma valid_sp_window_for_ceil : forall sp,
  valid_sp sp -> sp_window_lo <= bv_unsigned sp <= sp_window_hi.
Proof. intros sp [Hlo [Hhi Hal]]. auto. Qed.
Theorem plain_halts_may_fail_from_runtime_contracts :
  zlib_runtime_contracts -> Statements.plain_halts_may_fail.
Proof.
  intros HC. unfold Statements.plain_halts_may_fail, halts_may_fail.
  intros [sp brk0 mbase rnd] inp Hentry Hinput.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp)).
  destruct (HC rc) as [API [AX LX]].
  change (must_exit_in_at_cfg may_fail_cfg zsegs Exits.any
    (init_config zsegs Plain.M.init_pc Plain.M.phdrs
      sp brk0 mbase rnd Budgets.Standard.lim_source inp)).
  eapply must_exit_in_at_cfg_mono_set with (S1:=zallowed).
  - intros code Hcode. unfold zallowed in Hcode. destruct Hcode as [<-|[<-|[]]];
      apply HaltsAllowed.in_byte_codes; lia.
  - eapply realizes_must_exit_allowed with (T:=SPECX (LS:=checksum_shape) inp).
    + apply (src0_realizes_specX (rc:=rc) (LS:=checksum_shape) API AX LX
      driver_obligationsX_proved (fun data => checksum_room_calls (payload_len data) (calls data) DRB) sp brk0 mbase rnd
      Budgets.Standard.lim_source inp Hsp Hbrk Hmb Hfits Hinput).
      * apply SRC_LIM_MIN_le_source.
      * unfold rc. apply ceil_of_top_run.
    + unfold permitted_halt. cbn [init_config cfg_model init_model]. exact I.
    + apply checksum_SPECX_exits_allowed.
Qed.
