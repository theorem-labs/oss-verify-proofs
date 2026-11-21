(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (prog_model_ok's reserved-ledger premise now leaves room for the vDSO pair: live bytes plus 20 pages within 2^30, and a new bound reserved_top + brk_aslr_max + 4 pages + 4096 + 20 pages <= mmap_base_min; the proof passes the channel-reader fact and the mmap-base fact to GI_init; GI_init's state is moved to the run's initial model (init_model with the vDSO draw installed) by GI_with_vdso). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc Stdio PState Prog KInv KLink KEv StepB Gap ModelInv ImgFacts LB_Main.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Theorem prog_model_ok : forall segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  (live_bytes (segments_reserved segs) + 20 * page_size <= 2^30
   /\ reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ + 4096 + 20 * page_size <= mmap_base_min) -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (Prog.prog segs rs inp en) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (Prog.prog segs rs inp en) (mo0 segs lim en inp).
Proof.
  intros segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp.
  pose proof (never_forced segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp) as HNF.
  destruct en as [sp brk0 mbase dr]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hinp) in Hen.
  pose proof (valid_input_either_reader _ Hinp) as Hrdr.
  destruct Hen as ((HspL & HspH & _) & Hbrk & Hmb & _). destruct Hinp as (Hargv & _ & _ & _).
  revert HNF. unfold prog, prog_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp]. intros HNF.
  apply (mspecP_program (GI []) (prog_with rs (argv_Z (in_argv inp)))).
  - apply prog_with_GIP. apply argv_Z_short. exact Hargv.
  - apply GI_with_vdso. eapply GI_init; [exact Hbrk| exact Hpos| split; [exact HspL| exact HspH]| reflexivity| exact Hceil| exact Hrdr| exact Hmb| exact Hresv].
  - exact HNF.
Qed.
Theorem prog_model_ok_plain : forall rs en inp,
valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
leaves_unreachable_m nstep (Prog.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp)
/\ tsafe nstep nsafe (Prog.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp).
Proof. intros rs en inp He Hi. apply (prog_model_ok psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| apply lim_p| exact He| exact Hi]. Qed.
Theorem prog_model_ok_plain_L : forall L rs en inp, 2^31 <= L ->
valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
leaves_unreachable_m nstep (Prog.prog psegs rs inp en) (mo0 psegs L en inp)
/\ tsafe nstep nsafe (Prog.prog psegs rs inp en) (mo0 psegs L en inp).
Proof. intros L rs en inp HL He Hi. apply (prog_model_ok psegs rs p_init_pc p_phdrs); [apply top_pos_plain| apply ceil_plain| apply floor_plain| apply resv_plain| exact HL| exact He| exact Hi]. Qed.
Theorem prog_model_ok_ubsan : forall rs en inp,
valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
leaves_unreachable_m nstep (Prog.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp)
/\ tsafe nstep nsafe (Prog.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof. intros rs en inp He Hi. apply (prog_model_ok usegs rs u_init_pc u_phdrs); [apply top_pos_ubsan| apply ceil_ubsan| apply floor_ubsan| apply resv_ubsan| apply lim_u| exact He| exact Hi]. Qed.
