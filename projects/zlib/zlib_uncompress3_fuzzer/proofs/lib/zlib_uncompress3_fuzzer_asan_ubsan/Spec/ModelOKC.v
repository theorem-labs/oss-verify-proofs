(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import ITree Nodes Decode Image InitMem CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import Prelim Monad MSafe MSafeP CMonad STree Malloc Stdio PState Prog ProgC KInv KLink KEv StepB Gap ModelInv ModelInvC ImgFacts LB_Main.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import TopLevel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PlainU0 Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Theorem prog_model_ok_D : forall D segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  leaves_unreachable_m nstep (progD D segs rs inp en) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (progD D segs rs inp en) (mo0 segs lim en inp).
Proof.
  intros D segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp Hlow.
  pose proof (never_forced_D D segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp Hlow) as HNF.
  (* the launch facts Spec/ModelInv GI_init takes. *)
  assert (Hrd : in_channel_reader inp = true)
    by (destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
  destruct en as [sp brk0 mbase dr]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hinp) in Hen.
  destruct Hen as ((HspL & HspH & _) & Hbrk & (Hmb & _) & _). destruct Hinp as (Hargv & _ & _ & _).
  revert HNF. unfold progD, progD_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp]. intros HNF.
  apply (mspecP_program (GI []) (prog_withD D rs (argv_Z (in_argv inp)))).
  - apply prog_withD_GIP. apply argv_Z_short. exact Hargv.
  - eapply GI_init; [exact Hbrk| exact Hpos| split; [exact HspL| exact HspH]| reflexivity| exact Hceil| exact Hlow| exact Hmb| exact Hrd].
  - exact HNF.
Qed.

Theorem prog_model_ok_plain_DL : forall lim D rs en inp, 2^31 <= lim ->
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (progD D psegs rs inp en) (mo0 psegs lim en inp)
  /\ tsafe nstep nsafe (progD D psegs rs inp en) (mo0 psegs lim en inp).
Proof. intros lim D rs en inp Hlim He Hi. apply (prog_model_ok_D D psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| exact Hlim| exact He| exact Hi| apply low_plain]. Qed.

Theorem never_forced_p_DL : forall lim D rs en inp, 2^31 <= lim ->
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tnf (progD D psegs rs inp en) (mo0 psegs lim en inp).
Proof. intros lim D rs en inp Hlim He Hi. apply (never_forced_D D psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| exact Hlim| exact He| exact Hi| apply low_plain]. Qed.

Theorem prog_model_ok_plain_D : forall D rs en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (progD D psegs rs inp en) (mo0 psegs source_alloc_limit en inp)
  /\ tsafe nstep nsafe (progD D psegs rs inp en) (mo0 psegs source_alloc_limit en inp).
Proof. intros D rs en inp He Hi. apply (prog_model_ok_D D psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| apply lim_p| exact He| exact Hi| apply low_plain]. Qed.

Theorem prog_model_ok_ubsan_D : forall D rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (progD D usegs rs inp en) (mo0 usegs target_alloc_limit en inp)
  /\ tsafe nstep nsafe (progD D usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof. intros D rs en inp He Hi. apply (prog_model_ok_D D usegs rs u_init_pc u_phdrs); [apply top_pos_ubsan| apply ceil_ubsan| apply floor_ubsan| apply resv_ubsan| apply lim_u| exact He| exact Hi| apply low_ubsan]. Qed.

Theorem never_forced_p_D : forall D rs en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tnf (progD D psegs rs inp en) (mo0 psegs source_alloc_limit en inp).
Proof. intros D rs en inp He Hi. apply (never_forced_D D psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| apply lim_p| exact He| exact Hi| apply low_plain]. Qed.

Theorem never_forced_u_D : forall D rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  tnf (progD D usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof. intros D rs en inp He Hi. apply (never_forced_D D usegs rs u_init_pc u_phdrs); [apply top_pos_ubsan| apply ceil_ubsan| apply floor_ubsan| apply resv_ubsan| apply lim_u| exact He| exact Hi| apply low_ubsan]. Qed.
