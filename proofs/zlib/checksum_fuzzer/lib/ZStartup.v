(** Concrete symbolic execution into libc startup for the fixed plain image. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YK0i YP0m YP09 YP0l YP0k YP02 YP03 YP08.
From OssFuzzTheorems.zlib.checksum_fuzzer.images Require Plain.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import ZImage SymbolicExit.
Import ListNotations.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Definition zstart_result := Eval vm_compute in
  (sym_run_toN zsegs ztbl 32 0x1551c (zss0 false)).
Definition zstart_state := fst zstart_result.
Lemma zstart_reaches_libc :
  sym_run_toN zsegs ztbl 32 0x1551c (zss0 false)
    = (zstart_state, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma zstart_pc : ss_pc zstart_state = 0x1551c.
Proof. vm_compute. reflexivity. Qed.

Theorem zstart_machine_certificate : forall sp argv envp uid hw rnd xw xd,
  valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  xd UID_DATOM = uid_bytes uid -> xd HWCAP_DATOM = hwcap_bytes hw ->
  xd RAND_DATOM = rand_bytes rnd ->
  exists final,
    msteps zsegs (init_machine_state zsegs Plain.M.init_pc Plain.M.phdrs
      sp rnd argv envp uid hw) final /\
    st_ok zsegs (E0 sp argv envp xw xd) zstart_state final /\
    frame_of (E0 sp argv envp xw xd) (ss_mem (zss0 false))
      (ms_mem (init_machine_state zsegs Plain.M.init_pc Plain.M.phdrs
        sp rnd argv envp uid hw)) (ms_mem final).
Proof.
  intros sp argv envp uid hw rnd xw xd Hsp Hva Hve Hfits Huid Hhw Hrnd.
  pose proof (z_init_st_ok sp argv envp uid hw rnd xw xd false
    Hsp Hva Hve Hfits Huid Hhw Hrnd I) as HS.
  exact (msteps_run_to_gen zsegs ztbl ztbl_ok 32 0x1551c
    (E0 sp argv envp xw xd) (zss0 false) zstart_state RS_running
    (init_machine_state zsegs Plain.M.init_pc Plain.M.phdrs sp rnd argv envp uid hw)
    HS zstart_reaches_libc).
Qed.

Definition zstart_probe := Eval vm_compute in
  (sym_runN zsegs ztbl 256 (zss0 false)).
Eval vm_compute in (ss_pc (fst zstart_probe), snd zstart_probe).

Set Printing Fully Qualified.
Print Assumptions zstart_reaches_libc.
Print Assumptions zstart_machine_certificate.
