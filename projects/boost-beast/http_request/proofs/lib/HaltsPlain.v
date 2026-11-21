(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
Require OSSVerify.boost_beast.http_request.images.Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Scfg ShapeAlg Spec SpecProps HaltsBridge.
From OSSVerify.Proofs.boost_beast.http_request.lib Require RefTop.
(* LPS 08b1429: each walk is over the binary's own segments; [RomStable.run_init] /
   [RomStableS.srun_init] lift it to the run's segment list, the vDSO premise closed by
   [reflexivity] on the concrete image. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common.Cfg Require RomStable RomStableS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition SRC : Image :=
  mkImage OSSVerify.boost_beast.http_request.images.Plain.M.loaded_segments
          OSSVerify.boost_beast.http_request.images.Plain.M.init_pc
          OSSVerify.boost_beast.http_request.images.Plain.M.phdrs.

Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

Lemma spec_exits_codes02 : spec_exits = codes02.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem plain_must_exit_scfg : RefTop.XFUZZ ->
  forall en inp, valid_entry SRC en inp -> valid_input inp ->
    must_exit_in_scfg the_scfg codes02 SRC source_alloc_limit en inp.
Proof.
  intros XF [sp brk mbase rnd] inp Hen Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  (* the launch facts [RefTop.ref_realizes_spec] takes: [valid_input]'s launch clause and
     [valid_entry]'s last conjunct (Run.valid_input_launch, Run.valid_entry_sv48). *)
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb [Hfit Hlau]]]].
  destruct Hvalid as (Hargv & Henvp & Hfs & _).
  unfold SRC. rewrite <- spec_exits_codes02.
  eapply (realizes_must_exit_in _ spec_exits).
  - apply RomStable.run_init; [reflexivity |].
    exact (RefTop.ref_realizes_spec XF sp brk mbase rnd inp Hsp Hbrk Hfit Hargv Henvp Hfs Hmb Hrd Hvl Hlau).
  - apply spec_shape_good.
Qed.

(* [comment removed for export] *)
Theorem halts_plain : RefTop.XFUZZ ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02 SRC.
Proof.
  intros XF en inp Hen Hvalid _.
  unfold ShippedBudgets.lim_source.
  apply (must_exit_in_scfg_down forced_only_cfg the_scfg); [apply forced_only_cfg_least|].
  exact (plain_must_exit_scfg XF en inp Hen Hvalid).
Qed.
