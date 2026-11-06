(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan image (fuzz_knock.asan, sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118) from proofs/cgif/cgif_file_fuzzer/lib/A at
   c8557374ad2e: ACfn.v lines 22-72 (the contract tfib_lib_contract_x / _all), ACfj.v lines 180-255 (its proof
   tfib_lib_x_body / tfib_lib_x, with lx_leaf_fail's post), ACfh.v lines 29-50 and 153-164 (ajournal_fp_nil,
   srz_enter, ajournal_closed_io, ajournal_nil_io) and ACfi.v lines 56-140 (XL0, the links,
   tfib_lib_x_closed / tfib_lib_x_all), with their module paths changed. rule 24: no function proved (a port of the
   released cgif_file_fuzzer program part). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632
   (lines 73-75 and 111-124, the names XL0, RO_LO, RO_HI, the contract and its _all form; lines 368-371, the adapter)
   for reac-pw/fuzz_role image A: the contract is lib/A/RPgCSpec.v's rl_lib_contract_x at image A's segments, sink
   and harness constants, in fuzz_grant's exists-fx' form (role's harness changes float registers), so the adapter
   goes to ACfn.tfib_lib_contract_xf_all; the proof of the contract is not here: role_lib_x_all_stmt states it, with
   the allocator's two operations as premises (role's harness allocates and frees two blocks), for the closing to
   take as a Section variable until the walk proves it. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgLib.v at 0de5d668c87e for reac-pw/fuzz_rate
   image A: module paths changed; role_ -> rate_ and rl_lib_contract_x -> lib/A/RtPgCSpec.v's rt_lib_contract_x; RO_LO
   and RO_HI measured on fuzz_rate.asan; the statement takes the allocator's two operations as premises in the same
   order (rate's harness allocates and frees three blocks: pp, pod and buf). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgLib.v at af0538adbf24 for image B
   (fuzz_rate.asan-ubsan): the relocated frame is image B's core (lib/AU/YB1v.v tfibsegs, YD2l.v TfibB, YE2k.v tfib_K /
   tfib_sink_head, YCfn.v's constants and tfib_lib_contract_xf_all), RO_LO / RO_HI are measured on fuzz_rate.asan-ubsan,
   and every name ends in _B. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14): the whole-run contract of
   LLVMFuzzerTestOneInput (0x8076c, 11756 bytes) as image B's closing (lib/AU/YD2o.v) consumes it, and its statement.
   Statement text and the adapter only: rule 24, proves no function (kind: statement text).
   It Requires lib/AU/YB1v (tfibsegs), YD2l (TfibB), YE2k (tfib_K, tfib_sink_head) and YCfn of image B's core; YCfn is
   fuzz_grant's fx-slot text (tfib_lib_contract_xf_all).

   RO_LO_B / RO_HI_B: image B's .data.rel.ro start .. .got end (section headers of the pinned file: .data.rel.ro
   0x9b9e0 .. 0x9c110, .got 0x9c110 .. 0x9ce68; the same in the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1), the second disjunct of the frame's in_ro_tfa.

   The order of rate_lib_x_all_stmt_B's premises is the closing's (and image A's): the lib shape's one-leaf law
   (LEAF), then the free operation, then the malloc operation, each for every float state. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require YB1v YD2l YE2k YCfn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Definition XL0_B : Z -> Z := fun _ => 0.
Definition RO_LO_B : Z := 0x9b9e0.
Definition RO_HI_B : Z := 0x9ce68.

(* ============================== the contract (RtPgCSpec.rt_lib_contract_x at image B) ============================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Definition rate_lib_contract_x_B : Prop :=
@rt_lib_contract_x fx rc YE2k.tfib_sink_head YB1v.tfibsegs LS B MT YE2k.tfib_K XM_LIB XN_LIB RLO RHI
YCfn.A_LLVMF YCfn.RA_LLVMF YCfn.A_EMPTY YCfn.EV_LIB YCfn.LIVE_LIB YCfn.LLVMF_STK.
End a.
Definition rate_lib_contract_x_all_B {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @rate_lib_contract_x_B fx rc LS B MT XM_LIB XN_LIB RLO RHI.

(* ============================== the statement the walk proves ============================== *)
(* At image B's symbols TfibB, the meter that counts nothing and XL0_B (as image A's statement), the read-only range
   RO_LO_B .. RO_HI_B. *)
Definition rate_lib_x_all_stmt_B : Prop :=
forall (rc : YM05.RunCeil) (LS : lib_shape),
(forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) ->
(forall fx : YK11.FPState, @afree_realizes fx rc YB1v.tfibsegs YD2l.TfibB) ->
(forall fx : YK11.FPState, @amalloc_realizes fx rc YB1v.tfibsegs YD2l.TfibB) ->
@rate_lib_contract_x_all_B rc LS YD2l.TfibB ameter_triv XL0_B XL0_B RO_LO_B RO_HI_B.

(* ============================== the adapter to the core's contract ============================== *)
(* The core's fx-slot contract (lib/AU/YCfn.v tfib_lib_contract_xf_all, fuzz_grant's text) is the same text at the
   same segments, sink and constants: RtPgBase.arodata_okP segs RLO RHI B is YCfn's arodata_okS segs B RLO RHI. *)
Lemma rate_lib_contract_x_all_tfib_B {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) :
rate_lib_contract_x_all_B B MT XM_LIB XN_LIB RLO RHI -> YCfn.tfib_lib_contract_xf_all B MT XM_LIB XN_LIB RLO RHI.
Proof. intros HX fx. exact (HX fx). Qed.

Print Assumptions rate_lib_contract_x_all_tfib_B.
