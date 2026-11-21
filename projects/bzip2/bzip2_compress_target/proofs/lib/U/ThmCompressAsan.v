(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch facts from Run.valid_input and the walk lifted to the run segment list (RomStable.run_init)). *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW StartupRnd ShapeAlg Spec04.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocCover. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocDcv. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import S0H_Iface S0H_Cover S0H_Dcv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0HarnStmt U.S0B2BCStmt U.S0B2BDStmt U.S0HarnBody U.ThmCompressUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_glueB2B S0_cmp_bs S0_cmp_msO. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require U.S0B2BC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common.Cfg Require RomStable.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition U0img : Image :=
  mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc
          Ubsan.M.phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma harn_S0 : forall (ACEIL__ : ACeil) (RUNW__ : RunW), harn_spec S0_alloc S0_cover S0I.
Proof.
  intros AC RW. apply (harn_s0 S0_alloc S0_cover S0_dcv S0_freev).
  - intros BZP. exact (@U.S0B2BC.b2bC_s0 BZP AC RW
      (@OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_bs.S0_blockSort BZP AC
         (fun X Q XOK XSEP => @OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msO.S0_bigs BZP AC X Q XOK XSEP))
      S0_alloc S0_cover).
  - exact (S0F_glueB2B.S0F_b2bD S0_alloc S0_cover S0_dcv S0_freev).
Qed.

Lemma s0_side04 : forall en inp, valid_entry U0img en inp -> valid_input inp ->
  error_free (run_scfg (alloc_only_cfg false) U0img target_alloc_limit en inp)
  /\ trace_equiv (bh_traces (run_scfg (alloc_only_cfg false) U0img target_alloc_limit en inp)) (spec04 (in_argv inp) (in_fs inp)).
Proof.
  intros [rsp rbrk rmb rrnd] inp Hens Hvalid.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrdr.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens.
  destruct Hens as (Hrsp & Hrbrk & Hrmb & _ & Hlau). destruct Hvalid as [Hargv [Henvp [Hfs Hrest]]].
  assert (R : realizes s0segs
                (init_config s0segs Ubsan.M.init_pc Ubsan.M.phdrs
                             rsp rbrk rmb rrnd target_alloc_limit inp)
                (spec04 (in_argv inp) (in_fs inp))).
  { apply (@s0_realizes04 (aceil_of_sp (bv_unsigned rsp)) (mkRunW (canary_w rrnd) (secret_word rrnd))
             (harn_S0 _ _) rsp rbrk rmb rrnd inp Hrsp Hrbrk Hvl Hlau Hargv Henvp Hfs Hrdr).
    - rewrite (aceil_of_sp_valid rsp Hrsp). reflexivity.
    - reflexivity.
    - reflexivity. }
  (* LPS 08b1429: the run reads the binary against [run_segments], from the run's own start;
     [RomStable.run_init] lifts the walk ([vdso_image s0segs = None] by computation) *)
  pose proof (RomStable.run_init s0segs inp rsp rmb Ubsan.M.init_pc Ubsan.M.phdrs rbrk rrnd target_alloc_limit _ eq_refl R) as R'.
  split.
  - unfold U0img. cbn [run_scfg bh_errors bh_traces]. exact (realizes_no_error _ _ _ R').
  - intro tr. unfold U0img. cbn [run_scfg bh_errors bh_traces]. exact (realizes_obs_iff _ _ _ R' tr).
Qed.

