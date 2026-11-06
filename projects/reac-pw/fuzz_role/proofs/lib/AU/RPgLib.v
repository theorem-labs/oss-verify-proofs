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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgLib.v at d428443238a, for reac-pw/fuzz_role's
   image B (fuzz_role.asan-ubsan, pinned sha256 b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0;
   section headers of the unstripped twin dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): the
   image-A modules AB1v / AD2l / AE2k / ACfn are image B's lib/AU/YB1v / YD2l / YE2k / YCfn; RO_LO / RO_HI are image B's
   .data.rel.ro start 0x9a3c0 and .got end 0x9b7c8 (0x9aa70 + 0xd58); the shared text lib/A/RPgCSpec.v is the same. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): the whole-run contract of LLVMFuzzerTestOneInput (0x80020,
   10848 bytes) as image B's closing consumes it, and its statement.
   Statement text and the adapter only: rule 24, proves no function (kind: statement text).
   It Requires lib/AU/YB1v (tfibsegs), YD2l (TfibB), YE2k (tfib_K, tfib_sink_head) and YCfn of image B's core; YCfn is
   fuzz_grant's fx-slot text (tfib_lib_contract_xf_all).

   RO_LO / RO_HI: image B's .data.rel.ro start .. .got end (section headers: .data.rel.ro 0x9a3c0 .. 0x9aa70, .got
   0x9aa70 .. 0x9b7c8), the second disjunct of lib/AU/YCeg.v in_ro_tfa.

   The order of role_lib_x_all_stmt's premises is the closing's: the lib shape's one-leaf law (LEAF), then the free
   operation, then the malloc operation, each for every float state. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require YB1v YD2l YE2k YCfn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Definition XL0 : Z -> Z := fun _ => 0.
Definition RO_LO : Z := 0x9a3c0.
Definition RO_HI : Z := 0x9b7c8.

(* ============================== the contract (RPgCSpec.rl_lib_contract_x at image B) ============================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Definition role_lib_contract_x : Prop :=
@rl_lib_contract_x fx rc YE2k.tfib_sink_head YB1v.tfibsegs LS B MT YE2k.tfib_K XM_LIB XN_LIB RLO RHI
YCfn.A_LLVMF YCfn.RA_LLVMF YCfn.A_EMPTY YCfn.EV_LIB YCfn.LIVE_LIB YCfn.LLVMF_STK.
End a.
Definition role_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @role_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.

(* ============================== the statement the walk proves ============================== *)
(* At image B's symbols TfibB, the meter that counts nothing and XL0, the read-only range RO_LO .. RO_HI. *)
Definition role_lib_x_all_stmt : Prop :=
forall (rc : YM05.RunCeil) (LS : lib_shape),
(forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) ->
(forall fx : YK11.FPState, @afree_realizes fx rc YB1v.tfibsegs YD2l.TfibB) ->
(forall fx : YK11.FPState, @amalloc_realizes fx rc YB1v.tfibsegs YD2l.TfibB) ->
@role_lib_contract_x_all rc LS YD2l.TfibB ameter_triv XL0 XL0 RO_LO RO_HI.

(* ============================== the adapter to the core's contract ============================== *)
(* The core's fx-slot contract (lib/AU/YCfn.v tfib_lib_contract_xf_all, fuzz_grant's text) is the same text at the
   same segments, sink and constants: RPgBase.arodata_okP segs RLO RHI B is YCfn's arodata_okS segs B RLO RHI. *)
Lemma role_lib_contract_x_all_tfib {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) :
role_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI -> YCfn.tfib_lib_contract_xf_all B MT XM_LIB XN_LIB RLO RHI.
Proof. intros HX fx. exact (HX fx). Qed.
