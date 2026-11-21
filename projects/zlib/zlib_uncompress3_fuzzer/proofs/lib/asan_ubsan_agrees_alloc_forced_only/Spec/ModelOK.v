(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc Stdio PState Prog KInv KLink KEv StepB Gap ModelInv ImgFacts LB_Main.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import TopLevel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PlainU0 Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Theorem prog_model_ok : forall segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  leaves_unreachable_m nstep (Prog.prog segs rs inp en) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (Prog.prog segs rs inp en) (mo0 segs lim en inp).
Proof.
  intros segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp Hlow.
  pose proof (never_forced segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp Hlow) as HNF.
  (* the launch facts Spec/ModelInv GI_init takes. *)
  assert (Hrd : in_channel_reader inp = true)
    by (destruct Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hr & _); exact Hr).
  destruct en as [sp brk0 mbase dr]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hinp) in Hen.
  destruct Hen as ((HspL & HspH & _) & Hbrk & (Hmb & _) & _). destruct Hinp as (Hargv & _ & _ & _).
  revert HNF. unfold prog, prog_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp]. intros HNF.
  apply (mspecP_program (GI []) (prog_with rs (argv_Z (in_argv inp)))).
  - apply prog_with_GIP. apply argv_Z_short. exact Hargv.
  - eapply GI_init; [exact Hbrk| exact Hpos| split; [exact HspL| exact HspH]| reflexivity| exact Hceil| exact Hlow| exact Hmb| exact Hrd].
  - exact HNF.
Qed.

Theorem prog_model_ok_plain_L : forall lim rs en inp, 2^31 <= lim ->
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (Prog.prog psegs rs inp en) (mo0 psegs lim en inp)
  /\ tsafe nstep nsafe (Prog.prog psegs rs inp en) (mo0 psegs lim en inp).
Proof. intros lim rs en inp Hlim He Hi. apply (prog_model_ok psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| exact Hlim| exact He| exact Hi| apply low_plain]. Qed.

Theorem prog_model_ok_plain : forall rs en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (Prog.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp)
  /\ tsafe nstep nsafe (Prog.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp).
Proof. intros rs en inp He Hi. apply (prog_model_ok psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| apply lim_p| exact He| exact Hi| apply low_plain]. Qed.

Theorem prog_model_ok_ubsan : forall rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (Prog.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp)
  /\ tsafe nstep nsafe (Prog.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof. intros rs en inp He Hi. apply (prog_model_ok usegs rs u_init_pc u_phdrs); [apply top_pos_ubsan| apply ceil_ubsan| apply floor_ubsan| apply resv_ubsan| apply lim_u| exact He| exact Hi| apply low_ubsan]. Qed.
