(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc Stdio PState ProgP KInv KLink KEv StepB Gap ModelInv ImgFacts LB_Main.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Theorem prog_model_ok : forall segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^31 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (ProgP.prog segs rs inp en) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (ProgP.prog segs rs inp en) (mo0 segs lim en inp).
Proof.
  intros segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp.
  pose proof (never_forced segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp) as HNF.
  destruct en as [sp brk0 mbase dr]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hinp) in Hen.
  destruct Hen as ((HspL & HspH & _) & Hbrk & _ & _). destruct Hinp as (Hargv & _ & _ & _).
  revert HNF. unfold prog, prog_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp]. intros HNF.
  apply (mspecP_program (GIo []) (prog_with rs (argv_Z (in_argv inp)))).
  - apply prog_with_GIP. apply argv_Z_short. exact Hargv.
  - eapply GIo_init; [exact Hbrk| exact Hpos| split; [exact HspL| exact HspH]| reflexivity| exact Hceil].
  - exact HNF.
Qed.

Theorem prog_model_ok_plain : forall rs en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (ProgP.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp)
  /\ tsafe nstep nsafe (ProgP.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp).
Proof. intros rs en inp He Hi. apply (prog_model_ok psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| apply lim_p| exact He| exact Hi]. Qed.

(* [comment removed for export] *)
Theorem prog_model_ok_plain_lim : forall lim, 2^31 <= lim -> forall rs en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (ProgP.prog psegs rs inp en) (mo0 psegs lim en inp)
  /\ tsafe nstep nsafe (ProgP.prog psegs rs inp en) (mo0 psegs lim en inp).
Proof. intros lim Hlim rs en inp He Hi. apply (prog_model_ok psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| exact Hlim| exact He| exact Hi]. Qed.

Theorem prog_model_ok_ubsan : forall rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (ProgP.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp)
  /\ tsafe nstep nsafe (ProgP.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof. intros rs en inp He Hi. apply (prog_model_ok usegs rs u_init_pc u_phdrs); [apply top_pos_ubsan| apply ceil_ubsan| apply floor_ubsan| apply resv_ubsan| apply lim_u| exact He| exact Hi]. Qed.
