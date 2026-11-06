From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.plugin_hostd.fuzz_reply Require Statements Images.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK15 YO06 YO09 YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AgreeShape ZTraceSpec SlotTopG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Uniform Agree.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require AgreeP3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Statement SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require StatementKept SlotAllCf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Agree AgreeRcP3U SlotTopG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Statement SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require StatementKept SlotAllCf.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_reply's ubsan_agrees, by agree_frame (as lib/AgreeFramePK.v ubsan_agrees_of_slots_p) over the runs of each
   build at its budget:
   - plain, 16 GiB: T_reply and plain_runs_reply, copied from origin/cold/h-aag-10-reply a0d853acc6a
     lib/AsanAgreesReply.v:26-45 (without its ASan imports): AgreeP3.plain_crealizes_of_cgp3 at the plain cut-free
     slot top Prog.CF.SlotAllCf.fuzz_reply_slot_cgp3_src0;
   - ubsan, 512 GiB: U.AgreeRcP3U.ubsan_crealizes_of_cgp3_rc at the ubsan cut-free slot top
     U.Prog.CF.SlotAllCf.fuzz_reply_slot_cgp3_src0, its limit law from U.AgreeRcP3U.limlaw_of_rclim
     (LIM_AG = 2 ^ 39 = lim_target). *)

Definition T_reply : ProcInput -> TSet := fun inp => SPECX (LS:=ag_shape checksum_shape) inp.

Lemma plain_runs_reply : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (T_reply inp) /\
  cf_run Images.plain Budgets.Standard.lim_source en inp.
Proof.
  intros en inp Hv Hi.
  exact (AgreeP3.plain_crealizes_of_cgp3 (ag_shape checksum_shape) lib.Prog.SlotCaps3.CS_reply
    lib.Prog.Statement.G_reply lib.Prog.CF.StatementKept.GI_t lib.Prog.SlotCaps3.CS_reply_ok
    (fun a H => H)
    (lib.Prog.CF.StatementKept.GI_t_local src0_msyms ms_segs_rsegs)
    (lib.Prog.CF.StatementKept.GI_t_img src0_msyms ms_segs_rsegs)
    (lib.Prog.CF.SlotAllCf.fuzz_reply_slot_cgp3_src0 (ag_shape checksum_shape)
       (fun pl fs K => eq_refl) (fun n b => eq_refl))
    en inp Budgets.Standard.lim_source Hv Hi
    ltac:(apply Z.leb_le; vm_compute; reflexivity)).
Qed.

Lemma ubsan_runs_reply : forall en inp, valid_entry Images.ubsan en inp -> valid_input inp ->
  rz_run Images.ubsan Budgets.Standard.lim_target en inp (T_reply inp) /\
  cf_run Images.ubsan Budgets.Standard.lim_target en inp.
Proof.
  intros en inp Hv Hi.
  exact (U.AgreeRcP3U.ubsan_crealizes_of_cgp3_rc (ag_shape checksum_shape) U.Prog.SlotCaps3.CS_reply
    U.Prog.Statement.G_reply U.Prog.CF.StatementKept.GI_t U.Prog.SlotCaps3.CS_reply_ok
    (fun a H => H)
    (U.Prog.CF.StatementKept.GI_t_local U.Reusable.YH02.src0_msyms U.SlotTopG.ms_segs_rsegs)
    (U.Prog.CF.StatementKept.GI_t_img U.Reusable.YH02.src0_msyms U.SlotTopG.ms_segs_rsegs)
    (fun rc Hr => U.Prog.CF.SlotAllCf.fuzz_reply_slot_cgp3_src0 (ag_shape checksum_shape)
       (fun pl fs K => eq_refl) (fun n b => eq_refl) rc (U.AgreeRcP3U.limlaw_of_rclim rc Hr))
    en inp Budgets.Standard.lim_target Hv Hi
    ltac:(apply Z.leb_le; vm_compute; reflexivity) ltac:(apply Z.leb_le; vm_compute; reflexivity)).
Qed.

Theorem ubsan_agrees_of_runs : forall T : ProcInput -> TSet,
  (forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
     rz_run Images.plain Budgets.Standard.lim_source en inp (T inp) /\
     cf_run Images.plain Budgets.Standard.lim_source en inp) ->
  (forall en inp, valid_entry Images.ubsan en inp -> valid_input inp ->
     rz_run Images.ubsan Budgets.Standard.lim_target en inp (T inp) /\
     cf_run Images.ubsan Budgets.Standard.lim_target en inp) ->
  Statements.ubsan_agrees.
Proof.
  intros T HP HS. unfold Statements.ubsan_agrees, agrees_in. intros en_p en_s inp Hp Hs Hi _.
  destruct (HP en_p inp Hp Hi) as [Rp Cp]. destruct (HS en_s inp Hs Hi) as [Rs Cs].
  exact (agree_frame Images.plain Budgets.Standard.lim_source en_p Images.ubsan Budgets.Standard.lim_target en_s inp
    (T inp) (T inp) Rp Rs (t_eq_refl _) (budget_of_cf_run _ _ _ _ Cp) (budget_of_cf_run _ _ _ _ Cs)).
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof. exact (ubsan_agrees_of_runs T_reply plain_runs_reply ubsan_runs_reply). Qed.
