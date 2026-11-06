(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumD.v, with its module paths and module names changed; 1378 of its 1493 lines of code are new or changed and 601 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/VrdNumEnd.v, with its module paths and module names changed; 40 of its 73 lines of code are new or changed and 1460 lines of the source are left out. *)
(* fuzz_preset, slice S5b, lanes VnumG / A2NumP (worker a Theorem Labs lane): parse_value's NUMBER ARM in image A, assembled.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   vrd_num_a_P is VrdNum.vrd_num_a_stmt_P: the arm with the GENERIC MEMORY INVARIANT P and its three laws
   (YC80x.srr_inv_laws, YSRrMemnorm.srr_inv_call / srr_inv_mn), P of the memory at the dispatch to P of the memory at
   the join. REASON (a Theorem Labs lane's 12:19Z ruling): an SRr post is opaque once Qed, so an end-state memory invariant
   must be in the segment's STATEMENT; the generic SRr_memnorm was measured NOT provable (a Theorem Labs lane), so it cannot be
   added afterwards. Its proof is VnumD's assembly VrdNumScan.vrd_num_a_from_tail_P at P with its two premises
   discharged and nothing more: the statics' image fact (PST_IMG) and the tail VrdNumTail.vrd_num_tail_P at P, whose
   one end-segment hypothesis is A'End's VrdNumEnd.vrd_num_end (a working branch, code commit c656828872da,
   lib/A/VrdNumEnd.v blob bee19f17edc7), on the kit's post-implication reader text.
   THE OLD THEOREM vrd_num_a (vrd_num_a_stmt, no P) IS GONE: its tail needed a Section hypothesis that claimed memnorm
   at every allocator state (unprovable; deleted), and it is not the instance at P := fun _ => True, because
   srr_inv_mn at that P is the same claim. Nothing outside the number arm's four files cited it. The unit's top
   instantiates P := fun m => memnorm segs mem0 -> memnorm segs m (YSRrMemnorm.srr_inv_laws_imp over
   srr_inv_laws_memnorm_k, srr_inv_call_imp, and srr_inv_mn_imp from tparse_value_specX's memnorm premise at mem0).
   The Section hypotheses are vrd_num_tail_P's stand-ins, verbatim; each names its owner where VrdNumTail.v states
   it. fuzz_malloc is no stand-in (its published text is a premise of vrd_num_a_stmt_P); HI_head is the slice's
   one-name instance fact (reflexivity at CfParams_preset). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YN3v YG0s YP07 YP0a YG0p YP0d YP0c YC80 YImgTop YC1fP YC80x YC1fPx YC80xf
YGcallx YCbqGcall YGcallSx YGcallMx FCiface YStrtodRowX YFclsStep YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog VrdPro VrdNum VrdNumTail VrdNumScan VrdNumEnd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import strtod_c strtod_row S1Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis PST_IMG : forall a, Exists (in_zr a) prh_pst -> in_img segs a.
Hypothesis H_checked_memcpy_xm : aintrin_realizes_xm segs B ARx OCpy (pa_sigma AS___asan_memcpy).
Hypothesis B_tp : as_tp B = STRTOD_TP.
Hypothesis B_errno : as_errno B = STRTOD_ERRNO.
Hypothesis B_errno_own : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis H_HL : HL = cf_head.
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview segs (w_H W) mem (shadow_addr a) <> None.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs pa_relro_lo pa_relro_hi a.
Hypothesis HW : prh_head_wide.
Hypothesis H_pv_frame : 176 <= pi_frame F_parse_value.
Hypothesis PST_ERRNO : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4).
(* the strtod GOT guard word is one of B's const cells (S8aNumberW.w_hgotc at the instance); it replaces the earlier
   "the guard is no owned static of B", which is false at image A (Tfib_owned_static holds the guard, AF0m.v:1784) *)
Hypothesis B_got_const : forall ly, In (z8 (ANum STRTOD_GOT_GUARD) STRTOD_GUARD) (as_const B ly).
(* the instance fact HI_head, one name across the slice: discharged by `reflexivity` at CfParams_preset *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.

Theorem vrd_num_a_P : vrd_num_a_stmt_P B ARx SK.
Proof.
intros P PLAW PCALL PMN.
exact (vrd_num_a_from_tail_P B ARx SK LAWS P PLAW PST_IMG
  (vrd_num_tail_P B ARx SK LAWS PST_IMG H_checked_memcpy_xm B_tp B_errno B_errno_own
     H_HL H_zsal H_imgvis H_pst_ro HW H_pv_frame PST_ERRNO B_got_const HI_head
     (vrd_num_end B ARx SK LAWS HW PST_IMG) P PLAW PCALL PMN)).
Qed.

End a.

(* the axiom audit of the number arm's top lemma and of the lane's new helper texts (the kit's cut re-fit, lane RValue),
   in the build log of record *)
Print Assumptions vrd_num_a_P.
Print Assumptions VrdNumTail.vrd_num_tail_P.
Print Assumptions VrdRefJoinP.vrd_ref_join_P.
Print Assumptions VrdNum.vrd_ref_join.
Print Assumptions VrdNum.vrd_pv_post_sh_frame.
Print Assumptions VrdNum.vrd_ncapR_frame.
Print Assumptions VrdNum.vrd_frees_leaf.
Print Assumptions VrdNum.vrd_frees_eof.
Print Assumptions VrdNum.vrd_frees_cont.
Print Assumptions VrdNum.vrd_zero_fo.
Print Assumptions VrdNum.vrd_str_fo.
Print Assumptions VrdNum.vrd_live_at0.
Print Assumptions VrdPro.vrd_cur_entry_call.
Print Assumptions VrdPro.vrd_disp_chain.
