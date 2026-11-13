(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by gabelogan195, 2026-11: made in part from this harness's proofs/lib/MsgpackEncAsanTop.v at commit f92feaf8b7, lines 94-100: the valid_entry_sv48 rewrite, the destruct of the valid input and the call of top_of_guarded with frm_safe_Ma0, used in the proofs of the plain and ASan halting theorems; the rest of the file is new. *)
(** The halting theorems of the plain and ASan builds, in the form [Statements.v] states them.

    The agreement theorem of the ASan pair is built from two realizations of one
    trace set, [BigintSpec.spec]: the plain build realizes it at 16 GiB
    ([MsgpackEncFinalS.msgpack_enc_src]) and the ASan build at 512 GiB
    ([MsgpackEncAsanBase.na0_tgt_closed]).  Every exit the set admits has status
    0 or 2 ([HaltsKit.exit_codes_in_spec]) and it admits no death by a signal
    ([KillFree.kill_free_spec]), so walking either realization proves that
    build halts with an allowed status.

    The plain build's realization is at the statement's own budget, so its
    theorem is [HaltsKit.srealizes_init_must_exit] applied to the statement's
    own premise.  The ASan build's is at 512 GiB and [Statements.asan_halts]
    asks for 16 GiB: [HaltsOff.srealizes_init_must_exit_off] walks it with no
    premise on the budget, and the transfer of [Halts.Lim.LimTransfer] carries
    the result down to 16 GiB on every input that 16 GiB never refuses, which is
    the statement's premise. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec BMode FrmInit MsgpackEncFinalS MsgpackEncAsanBase.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts Require HaltsOff.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim Require LimTransfer.

Section Tops.
#[local] Existing Instance OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec.fx0.

Lemma lim16_le_lim512 : (ShippedBudgets.lim_source <= target_alloc_limit)%Z.
Proof. vm_compute. discriminate. Qed.

Theorem halts_jsoncons_fuzz_msgpack_encoder_plain :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source
    OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.codes02
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.loaded_segments
             OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.init_pc
             OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.phdrs).
Proof.
  intros [sp brk0 mbase rnd] inp Hen Hinp Hbud.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as (Hsp & Hbrk & Hmb & Hfit).
  destruct Hinp as (Hargv & Henvp & Hfs & _ & Hcreds & _).
  exact (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.srealizes_init_must_exit
           _ _ _ _ sp brk0 mbase rnd _ inp
           OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.codes02 _
           (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.FrmInit.top_of_guarded
              _ _ _ _ _ _ _ _ _ _ _
              OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.FrmInit.frm_safe_Ms0
              (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncFinalS.msgpack_enc_src
                 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncFinalS.open_S_closed
                 sp brk0 mbase rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds))
           (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.exit_codes_in_spec _ _)
           (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.KillFree.kill_free_spec _ _)
           Hbud).
Qed.

(** The ASan build must exit at 512 GiB, the budget its realization is proved at. *)
Lemma asan_must_exit_512 : forall en inp,
  valid_entry (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.loaded_segments
                       OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.init_pc
                       OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.phdrs) en inp ->
  valid_input inp ->
  must_exit_in_scfg forced_only_cfg
    OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.codes02
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.loaded_segments
             OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.init_pc
             OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.phdrs)
    target_alloc_limit en inp.
Proof.
  intros [sp brk0 mbase rnd] inp Hen Hinp.
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as (Hsp & Hbrk & Hmb & Hfit).
  destruct Hinp as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
  exact (@OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.HaltsOff.srealizes_init_must_exit_off
           OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BMode.bm_off_inst eq_refl
           _ _ _ _ sp brk0 mbase rnd _ inp
           OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.codes02 _
           (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.FrmInit.top_of_guarded
              _ _ _ _ _ _ _ _ _ _ _
              OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.FrmInit.frm_safe_Ma0
              (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncAsanBase.na0_tgt_closed
                 sp brk0 mbase rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds Hhw Hsv48))
           (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.exit_codes_in_spec _ _)
           (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.KillFree.kill_free_spec _ _)).
Qed.

Theorem halts_jsoncons_fuzz_msgpack_encoder_asan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source
    OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.codes02
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.loaded_segments
             OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.init_pc
             OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.phdrs).
Proof.
  intros en inp Hen Hinp Hbud.
  exact (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim.LimTransfer.lim_transfer_scfg
           forced_only_cfg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.HaltsKit.codes02
           (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.loaded_segments
                    OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.init_pc
                    OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.phdrs)
           en inp ShippedBudgets.lim_source target_alloc_limit lim16_le_lim512
           (asan_must_exit_512 en inp Hen Hinp) Hbud).
Qed.
End Tops.
