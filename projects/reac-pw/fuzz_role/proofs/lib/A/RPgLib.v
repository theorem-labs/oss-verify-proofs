(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan image (fuzz_knock.asan, sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118) from proofs/cgif/cgif_file_fuzzer/lib/A at
   c8557374ad2e: ACfn.v lines 22-72 (the contract tfib_lib_contract_x / _all), ACfj.v lines 180-255 (its proof
   tfib_lib_x_body / tfib_lib_x, with lx_leaf_fail's post), ACfh.v lines 29-50 and 153-164 (ajournal_fp_nil,
   srz_enter, ajournal_closed_io, ajournal_nil_io) and ACfi.v lines 56-140 (XL0, the links,
   tfib_lib_x_closed / tfib_lib_x_all), with their module paths changed. rule 24: no function proved (a port of the
   released cgif_file_fuzzer program part).

   The knock changes:
   - names: tfib_lib_pre_x / tfib_lib_post_x / tfib_lib_contract_x / tfib_lib_contract_x_all / tfib_lib_x_body /
     tfib_lib_x / tfib_lib_x_all / link_ASM2 -> knock_lib_pre_x / knock_lib_post_x / knock_lib_contract_x /
     knock_lib_contract_x_all / knock_lib_x_body / knock_lib_x / knock_lib_x_all / link_ASM1.
   - constants: A_LLVMF / RA_LLVMF / A_EMPTY / EV_LIB / LIVE_LIB / LLVMF_STK are lib/A/ACfm.v's (knock's values, not
     restated here); the read-only pair is knock's .data.rel.ro start .. .got end, RO_LO 0x96070 .. RO_HI 0x972c8
     (section headers; the second disjunct of lib/A/ACeh.v in_ro_tfa), where cgif's is 0x9da38 .. 0x9eca8.
   - the sink: tfib_K and tfib_sink_head are knock's (lib/A/AE2k.v, ofl_head 0x5f1bc8), passed by name at every SK
     use; tfib_sink_head is a plain Definition and the SINK-HEAD GUARD below removes the plain build's src0_sink_head
     instance (Reusable/YI5b.v), so no sink head is ever inferred. cgif's tfib_ROB (ACfi.v:39-52) has no counterpart: knock_lib_A_seg and rt_H do not use ro_tfa_below_ofl.
   - the library tree: cgif's ACfj proves its contract at its global shape ff_lib_shape (lib/YI0a.v), whose LIBK is
     cgif's GIF tree aff_tree; knock's harness writes no file, so the proof takes LEAF, LIBK pl fs K = K (LL 0 fs []),
     which knock's shapes give by eq_refl (ZTraceSpec.checksum_shape, AgreeKnock.ag_sil_shape, FrameSlotK.kept_shape),
     and the post is cgif's lx_leaf_fail case (ACfj.v:180-207) for every input.
   - the walk: cgif's tfib_lib_A_seg + lx_RA2 (ACfj.v:226-255) -> knock's APgMain0.knock_lib_A_seg (S0) + APgMain2.rt_H
     (S1 .. S7 from ss_H) at FP = [] and POST = rt_post B MT [] (APgRt), which carries no cgif PX; cgif's HXL / HXL2
     (RT_NEED1 and the palette malloc) become HXL : 0 <= XL n, knock_lib_A_seg's 0 <= T.
   - the links: cgif's link_ASM2 (class 2, A/AF0s.v stack_malloc2_contract) -> link_ASM1 (class 1, knock's
     A/AF0s.v stack_malloc1_contract at 0x3c064). knock's harness calls no allocator, so cgif's AMALLOC / AFREE have
     no counterpart. rt_H (S1 .. S7) takes the three callee contracts TKINIT / TKHEARD / TKSTEP; the closed form
     discharges them with h-rec-s3's walks pb_knock_initX / pb_knock_heardX / pb_knock_stepX (A/APgInit.v, APgHeard.v,
     APgStep.v) at PI_knock_asan, through h-rec-s3's bridge lib/A/APgImgLink.v (cgif's A/ACed.v shape: tfibX_lib :
     TfibLib TfibB, tfibX_LAWS, tfibX_PALib0, tfibX_AMEMSET, tfibX_init0 / heard0 / step0). AIL (cgif's ACfi.v Section e
     hypothesis) is discharged by the core's lib/A/AD1u.v tfib_AIL at TfibB (TfibB_syms, lib/A/AD2l.v), so
     the closed form's one hypothesis left is LEAF. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632
   (lines 73-75 and 111-124, the names XL0, RO_LO, RO_HI, the contract and its _all form; lines 368-371, the adapter)
   for reac-pw/fuzz_role image A: the contract is lib/A/RPgCSpec.v's rl_lib_contract_x at image A's segments, sink
   and harness constants, in fuzz_grant's exists-fx' form (role's harness changes float registers), so the adapter
   goes to ACfn.tfib_lib_contract_xf_all; the proof of the contract is not here: role_lib_x_all_stmt states it, with
   the allocator's two operations as premises (role's harness allocates and frees two blocks), for the closing to
   take as a Section variable until the walk proves it. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb): the whole-run contract of
   LLVMFuzzerTestOneInput (0x7ff88, 11308 bytes) as the closing (lib/A/AD2o.v) consumes it, and its statement.
   Statement text and the adapter only: rule 24, proves no function (kind: statement text).
   It Requires lib/A/AB1v (tfibsegs), AD2l (TfibB), AE2k (tfib_K, tfib_sink_head) and ACfn of the relocated frame
   (step A3); ACfn must be fuzz_grant's fx-slot text (tfib_lib_contract_xf_all), so this file builds only on a tree
   that holds that frame.

   RO_LO / RO_HI: image A's .data.rel.ro start .. .got end (section headers of the pinned file: .data.rel.ro
   0x9a120 .. 0x9a7d0, .got 0x9a7d0 .. 0x9b528; the same in the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6), the second disjunct of lib/A/ACeg.v in_ro_tfa,
   as knock's 0x96070 .. 0x972c8 is knock's.

   The order of role_lib_x_all_stmt's premises is the closing's: the lib shape's one-leaf law (LEAF), then the free
   operation, then the malloc operation, each for every float state (fuzz_ctrl's walk top takes its free and malloc
   hypotheses in this order, lib/A/ACtl.v at origin/ossv/recipes 75ff9552daa). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require AB1v AD2l AE2k ACfn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Definition XL0 : Z -> Z := fun _ => 0.
Definition RO_LO : Z := 0x9a120.
Definition RO_HI : Z := 0x9b528.

(* ============================== the contract (RPgCSpec.rl_lib_contract_x at image A) ============================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Definition role_lib_contract_x : Prop :=
@rl_lib_contract_x fx rc AE2k.tfib_sink_head AB1v.tfibsegs LS B MT AE2k.tfib_K XM_LIB XN_LIB RLO RHI
ACfn.A_LLVMF ACfn.RA_LLVMF ACfn.A_EMPTY ACfn.EV_LIB ACfn.LIVE_LIB ACfn.LLVMF_STK.
End a.
Definition role_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @role_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.

(* ============================== the statement the walk proves ============================== *)
(* At image A's symbols TfibB, the meter that counts nothing and XL0 (as every released libreac closing), the
   read-only range RO_LO .. RO_HI. *)
Definition role_lib_x_all_stmt : Prop :=
forall (rc : YM05.RunCeil) (LS : lib_shape),
(forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) ->
(forall fx : YK11.FPState, @afree_realizes fx rc AB1v.tfibsegs AD2l.TfibB) ->
(forall fx : YK11.FPState, @amalloc_realizes fx rc AB1v.tfibsegs AD2l.TfibB) ->
@role_lib_contract_x_all rc LS AD2l.TfibB ameter_triv XL0 XL0 RO_LO RO_HI.

(* ============================== the adapter to the core's contract ============================== *)
(* The core's fx-slot contract (lib/A/ACfn.v tfib_lib_contract_xf_all, fuzz_grant's text) is the same text at the
   same segments, sink and constants: RPgBase.arodata_okP segs RLO RHI B is ACfn's arodata_okS segs B RLO RHI. *)
Lemma role_lib_contract_x_all_tfib {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) :
role_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI -> ACfn.tfib_lib_contract_xf_all B MT XM_LIB XN_LIB RLO RHI.
Proof. intros HX fx. exact (HX fx). Qed.
