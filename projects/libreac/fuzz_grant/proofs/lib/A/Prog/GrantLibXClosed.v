(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfi.v's tfib_lib_x_closed and tfib_lib_x_all for libreac/fuzz_grant: module paths, GrantB, GrantClose.v's instances, the allocator rules from a Theorem Labs lane's closed interceptor walks, and the entry function's phase lemmas in place of cgif's three function contracts. *)
(* The ASan build's program contract for fuzz_grant, closed: `grant_lib_x_all` at the asyms
   GrantB, the meter that counts nothing and the driver's read-only range, from the phase
   machine of the entry function's walk (GrantEntryChain.v), every phase instantiated at
   the image `PI_grant` with GrantClose.v's instances of the runtime's contracts. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0s YK14 YK15 YK18 YP09 YCbn YI04 YI09 YI00 YN3v YG0v YK04 YA0i YA0n YCbm YCbq YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbp YE00 YE01 YL01 YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB1v AE2k ACfn ACej AF0l AD2l AF0m AD1u AF0w AF0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require ACeg.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import GrantShape.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantAddr GrantImg
GrantEntryDefs GrantEntryChain GrantLibX GrantClose.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
HeadampTxEffective HeadampTxSet HeadampDefault HeadampTxArmScene HeadampTxSetResweep GrantBuildSweep
CtrlParseCut CtrlParse KindOfLink1 CtrlHeadampRecordVerify CtrlChecksumVerify CtrlIdentityPollBlock CheckGroupa CheckGroupaWalk
GrantAllocFits GrantAllocate HeadampTxNext HeadampTxNextClose.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require GrantEntryUnset GrantEntrySet GrantEntryInit GrantEntryHdr GrantEntryRaw GrantEntrySchedSetup GrantEntryHead GrantEntrySweep GrantEntryAdmit GrantEntrySchedTurn GrantEntryLeave GrantEntryEndFree.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntrySweepDefs GrantEntrySweepS4.
Import ListNotations.

Section a. Context {rc : YM05.RunCeil}.

(* The phases, each at every floating-point state, at the image's
   instance, GrantB and the meter that counts nothing: each is its theorem applied to GrantClose.v's
   instances, except reac_grant_build_sweep's, Hypothesis BSW below, which lib/A/GrantTop.v:125 gives. *)

(* The unset-cell check (a Theorem Labs lane, lib/A/Prog/GrantEntryUnset.v:688), closed. *)
Lemma grant_ph_unset : forall fx : YK11.FPState,
  ph_unset (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx. exact (GrantEntryUnset.ge_unset GrantB ameter_triv grant_LAWS grant_PALib _).
Qed.

(* reac_grant_build_sweep (a Theorem Labs lane, lib/A/Prog/GrantBuildSweep.v); its walk is lib/A/Prog/GrantBuildSweepWalk.v:276, given at lib/A/GrantTop.v:125 grant_BSW. *)
Hypothesis BSW : forall fx : YK11.FPState,
  treac_grant_build_sweep_spec (fx := fx) (PI := PI_grant) GrantB.

(* reac_ctrl_parse (a Theorem Labs lane, lib/A/Prog/CtrlParse.v), which check_groupa calls: closed,
   with GrantClose.v's facts for the six 0xff bytes the bcmp wrapper compares against. *)
Lemma grant_TPARSE : forall fx : YK11.FPState,
  tctrl_parse_spec (fx := fx) (PI := PI_grant) GrantB.
Proof.
  intros fx.
  exact (pb_ctrl_parse GrantB grant_LAWS grant_PALib grant_PALibF grant_ML
           grant_AMEMSET grant_AMEMCPY grant_ABCMP grant_ASM1 grant_SMP grant_ASF grant_FFL
           (pb_kind_of_link1 GrantB grant_LAWS) GRANT_GLOBS grant_globs_marked grant_glob_BCAST
           grant_img_shadow_vis grant_rng_BCAST grant_bcast_val).
Qed.

(* The memory-checking runtime's malloc and free: a Theorem Labs lane's closed walks of the two
   interceptors (lib/A/AF0w.v:45, lib/A/AF0q.v:13), as lib/A/AGrantT.v:43-44 uses them. *)
Lemma grant_AMALLOC : forall fx : YK11.FPState, amalloc_realizes (fx := fx) tfibsegs GrantB.
Proof. intros fx. exact (tfib_amalloc_realizes GrantB GrantB_syms (fun t => eq_refl)). Qed.
Lemma grant_AFREE : forall fx : YK11.FPState, afree_realizes (fx := fx) tfibsegs GrantB.
Proof. intros fx. exact (afree_realizes_closed GrantB GrantB_syms (fun t => eq_refl)). Qed.

(* The allocator rules at GrantB and the meter that counts nothing (lib/Reusable/YCbp.v). *)
Lemma grant_AMALLOC4 : forall fx : YK11.FPState,
  amalloc04_rule (fx := fx) tfibsegs GrantB ameter_triv.
Proof.
  intros fx.
  exact (amalloc04_rule_triv tfibsegs GrantB ACeg.tfib_segs_low grant_api_env grant_LAWS grant_ML
           (grant_AMALLOC fx)).
Qed.
Lemma grant_AFREE4 : forall fx : YK11.FPState,
  afree04_rule (fx := fx) tfibsegs GrantB ameter_triv.
Proof.
  intros fx.
  exact (afree04_rule_triv tfibsegs GrantB ACeg.tfib_segs_low grant_api_env grant_LAWS grant_ML
           (grant_AFREE fx)).
Qed.
Lemma grant_AFREEN4 : forall fx : YK11.FPState,
  afree_null04_rule (fx := fx) tfibsegs GrantB ameter_triv.
Proof.
  intros fx.
  exact (afree_null04_rule_triv tfibsegs GrantB ACeg.tfib_segs_low grant_api_env grant_LAWS grant_ML
           (grant_AFREE fx)).
Qed.

(* The table's set-up (a Theorem Labs lane, lib/A/Prog/GrantEntryInit.v:1049), closed. *)
Lemma grant_ph_init : forall fx : YK11.FPState,
  ph_init (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  exact (GrantEntryInit.ge_init GrantB ameter_triv grant_PALib grant_LAWS ameter_triv_laws
           grant_AMEMSET (grant_AMALLOC4 fx) _).
Qed.

(* The entry segment (a Theorem Labs lane, lib/A/Prog/GrantEntryHead.v), closed: the prologue, the
   frame on the side stack and its shadow; the jump to GP_leave is never taken there, so
   the second premise of ph_head is not used. *)
Lemma grant_ph_head : forall fx : YK11.FPState,
  ph_head (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx HHDR _.
  exact (GrantEntryHead.ge_head GrantB ameter_triv grant_PALib grant_PALibF grant_LAWS grant_ML
           ameter_triv_laws ameter_triv_fs_laws grant_ASM4 grant_SMP grant_FFL _ HHDR).
Qed.

(* The header read (a Theorem Labs lane, lib/A/Prog/GrantEntryHdr.v:798), closed. *)
Lemma grant_ph_hdr : forall fx : YK11.FPState,
  ph_hdr (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  exact (GrantEntryHdr.ge_hdr_read GrantB ameter_triv grant_LAWS grant_PALib grant_PALibF _).
Qed.

(* The hand-built allocation (a Theorem Labs lane, lib/A/Prog/GrantEntryRaw.v:51). *)
Lemma grant_ph_raw : forall fx : YK11.FPState,
  ph_raw (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  exact (GrantEntryRaw.ge_raw GrantB ameter_triv grant_LAWS grant_PALib ameter_triv_laws
           ameter_triv_fs_laws (grant_AMALLOC4 fx) (grant_AFREE4 fx) (BSW fx) _).
Qed.

(* The scheduler's setup (a Theorem Labs lane, lib/A/Prog/GrantEntrySchedSetup.v:71), closed,
   with a Theorem Labs lane's and a Theorem Labs lane's closed walks of its two callees. *)
Lemma grant_ph_setup : forall fx : YK11.FPState,
  ph_setup (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  exact (GrantEntrySchedSetup.ge_sched_setup GrantB ameter_triv grant_LAWS grant_PALib grant_PALibF
           (pb_headamp_tx_arm_scene GrantB grant_LAWS grant_PALib grant_AMEMSET)
           (pb_headamp_tx_set_resweep GrantB grant_LAWS grant_PALib)
           grant_AMEMSET _).
Qed.

(* The admission tests (two Theorem Labs lanes, lib/A/Prog/GrantEntryAdmit.v:715), closed,
   with a Theorem Labs lane's and a Theorem Labs lane's closed walks of reac_grant_alloc_fits and reac_grant_allocate. *)
Lemma grant_ph_admit : forall fx : YK11.FPState,
  ph_admit (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  exact (GrantEntryAdmit.ge_admit GrantB ameter_triv grant_LAWS
           (pb_reac_grant_alloc_fits GrantB grant_LAWS)
           ltac:(first [exact (pb_grant_allocate GrantB grant_LAWS grant_PALib)
                       | exact (pb_grant_allocate GrantB grant_LAWS)]) _).
Qed.

(* The scheduler's frame loop (a Theorem Labs lane, lib/A/Prog/GrantEntrySchedTurn.v), closed,
   with a Theorem Labs lane's, a Theorem Labs lane's and a Theorem Labs lane's closed walks of its three callees. *)
Lemma grant_ph_turn : forall fx : YK11.FPState,
  ph_turn (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  exact (GrantEntrySchedTurn.ge_sched_turn GrantB ameter_triv grant_LAWS
           ltac:(first [exact (pb_reac_headamp_tx_next GrantB grant_LAWS grant_PALib)
                       | exact (pb_reac_headamp_tx_next GrantB grant_LAWS)])
           (pb_headamp_tx_effective GrantB grant_LAWS grant_PALib)
           (pb_reac_headamp_default GrantB grant_LAWS) _).
Qed.

(* The frame given back and the return (a Theorem Labs lane, lib/A/Prog/GrantEntryLeave.v), closed:
   __asan_set_shadow_f5 is a Theorem Labs lane's contract at GrantClose.v's instance. *)
Lemma grant_ph_leave : forall fx : YK11.FPState,
  ph_leave (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  first [ exact (GrantEntryLeave.ge_leave GrantB ameter_triv grant_LAWS grant_ML ameter_triv_laws
                   ameter_triv_fs_laws grant_ASF grant_FFL grant_SSF5)
        | exact (GrantEntryLeave.ge_leave GrantB ameter_triv grant_PALib grant_PALibF grant_LAWS grant_ML
                   ameter_triv_laws ameter_triv_fs_laws grant_ASF grant_FFL grant_SSF5) ].
Qed.

(* The free of the table and the re-marking of the frame (a Theorem Labs lane, lib/A/Prog/GrantEntryEndFree.v),
   closed. *)
Lemma grant_ph_end : forall fx : YK11.FPState,
  ph_end (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  exact (GrantEntryEndFree.ge_end_free GrantB ameter_triv grant_LAWS grant_PALib grant_PALibF
           ameter_triv_laws (grant_AFREE4 fx) _ (grant_ph_leave fx)).
Qed.

(* The sweep (a Theorem Labs lane, lib/A/Prog/GrantEntrySweep.v:74), with check_groupa's and
   reac_ctrl_identity_poll_block's closed walks and GrantClose.v's tables. *)
Lemma grant_ph_sweep : forall fx : YK11.FPState,
  ph_sweep (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  pose proof (pb_check_groupa (RO := grant_RO) GrantB grant_PALib grant_LAWS grant_PALibF grant_ML
                grant_AMEMCPY grant_ASM2 grant_SMP grant_ASF grant_FFL grant_tbl_T0
                grant_img_shadow_vis grant_zs_T0 grant_rng_T0 (grant_TPARSE fx)
                (pb_headamp_tx_effective GrantB grant_LAWS grant_PALib)
                (pb_ctrl_headamp_record_verify GrantB grant_LAWS grant_PALib)
                ltac:(first [exact (pb_ctrl_checksum_verify GrantB grant_LAWS grant_PALib) | exact (pb_ctrl_checksum_verify GrantB grant_LAWS)])) as TCG.
  pose proof (pb_ctrl_identity_poll_block GrantB GRANT_GLOBS grant_LAWS grant_AMEMCPY
                grant_globs_marked grant_img_shadow_vis) as TIPB.
  assert (RT : GSW_RT (PI := PI_grant) GrantB ameter_triv).
  { unfold GSW_RT.
    exact (conj grant_LAWS (conj grant_PALib (conj ameter_triv_laws (conj ameter_triv_fs_laws
            (conj (grant_AMALLOC4 fx) (conj (grant_AFREE4 fx) (conj (grant_AFREEN4 fx)
            (conj grant_ABCMP (conj grant_img_shadow_vis (conj grant_ML grant_PALibF)))))))))). }
  exact (GrantEntrySweep.ge_sweep (RO := grant_RO) GrantB ameter_triv GRANT_GLOBS
           grant_tbl_HEAD_ACK grant_tbl_HEAD_MARK grant_rng_HEAD_ACK grant_rng_HEAD_MARK
           grant_globs_marked grant_glob_HEAD_ACK grant_glob_HEAD_MARK
           (BSW fx) (pb_reac_headamp_default GrantB grant_LAWS) TCG TIPB
           grant_glob_GROUPB (proj1 grant_rng_GROUPB) (proj2 grant_rng_GROUPB) grant_tbl_GROUPB
           grant_glob_POLL (proj1 grant_rng_POLL) (proj2 grant_rng_POLL) grant_tbl_POLL
           RT).
Qed.

(* The set loop (a Theorem Labs lane, lib/A/Prog/GrantEntrySet.v:75), closed, with its three callees'
   closed walks. *)
Lemma grant_ph_set : forall fx : YK11.FPState,
  ph_set (fx := fx) (PI := PI_grant) GrantB ameter_triv.
Proof.
  intros fx.
  exact (GrantEntrySet.ge_set GrantB ameter_triv grant_LAWS
           (pb_headamp_tx_set GrantB grant_LAWS grant_PALib)
           (pb_headamp_tx_effective GrantB grant_LAWS grant_PALib)
           (pb_reac_headamp_default GrantB grant_LAWS) _).
Qed.

Lemma grant_start : forall fx : YK11.FPState,
  ge_start (fx := fx) (PI := PI_grant) GrantB ameter_triv
    (ge_post (fx := fx) (PI := PI_grant) GrantB ameter_triv).
Proof.
  intros fx.
  exact (ge_chain GrantB ameter_triv (grant_ph_head fx) (grant_ph_hdr fx) (grant_ph_init fx) (grant_ph_set fx)
           (grant_ph_unset fx) (grant_ph_admit fx) (grant_ph_sweep fx) (grant_ph_raw fx) (grant_ph_setup fx)
           (grant_ph_turn fx) (grant_ph_end fx) (grant_ph_leave fx)).
Qed.

Theorem grant_lib_x_all : tfib_lib_contract_x_all GrantB ameter_triv GX_XL0 GX_XL0 GX_RLO GX_RHI.
Proof.
  intros fx.
  (* The sink of the image keeps its laws: a Theorem Labs lane's lib/A/AD1u.v:43 `tfib_AIL`. *)
  exact (grant_lib_x_closed (tfib_AIL GrantB GrantB_syms) (grant_start fx)).
Qed.

End a.

(* Every axiom printed here is on origin/ossv/recipes:toolchain/allowed-axioms.txt. *)
Print Assumptions grant_lib_x_all.
