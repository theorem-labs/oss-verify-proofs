(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632
   (lines 73-75 and 111-124, the names XL0, RO_LO, RO_HI, the contract and its _all form; lines 368-371, the
   adapter) for reac-pw/fuzz_role image A. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgLib.v at
   0de5d668c87 for reac-pw/fuzz_headamp image A: module paths changed, the role_ prefix renamed to headamp_, and
   RO_LO / RO_HI measured on headamp's own pin. The text is lib/A/HPgCSpec.v's hd_lib_contract_x at image A's
   segments, sink and harness constants, in fuzz_grant's exists-fx' form (headamp's harness changes float
   registers, as role's does); the proof of the contract is not here: headamp_lib_x_all_stmt states it, with the
   allocator's two operations as premises (headamp's harness allocates and frees FOUR blocks, LIFO; the
   allocator's laws are per call, so the four blocks add no premise beyond role's two), for the closing to take as
   a Section variable until the walk proves it. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47): the whole-run contract of
   LLVMFuzzerTestOneInput (0x80bc0, 12924 bytes) as the closing (lib/A/AD2o.v) consumes it, and its statement.
   Statement text and the adapter only: proves no function (kind: statement text).
   It Requires lib/A/AB1v (tfibsegs), AD2l (TfibB), AE2k (tfib_K, tfib_sink_head) and ACfn of the relocated frame
   (from fuzz_role); ACfn must be fuzz_grant's fx-slot text (tfib_lib_contract_xf_all), so this file builds only on a
   tree that holds that frame.

   RO_LO / RO_HI: image A's .data.rel.ro start .. .got end (section headers of the pinned file: .data.rel.ro
   0x9bc80 .. 0x9c310, .got 0x9c310 .. 0x9d068; the same in the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a), the second disjunct of lib/A/ACeg.v
   in_ro_tfa, as knock's 0x96070 .. 0x972c8 is knock's and role's 0x9a120 .. 0x9b528 is role's. The window holds
   the three .data.rel.ro pointer tables the harness reads (ent_build.vocab 0x9c060, ent_headamp_key.odd_ch
   0x9c0e0, ent_headamp_key.param 0x9c180), the shadow-offset GOT word 0x9c370, the option-byte GOT word 0x9c3c8
   and the stack-guard GOT word 0x9cff8 that musl's strtol reads.

   The order of headamp_lib_x_all_stmt's premises is the closing's: the lib shape's one-leaf law (LEAF), then the
   free operation, then the malloc operation, each for every float state (fuzz_ctrl's walk top takes its free and
   malloc hypotheses in this order, lib/A/ACtl.v at origin/ossv/recipes 75ff9552daa). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require AB1v AD2l AE2k ACfn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Definition XL0 : Z -> Z := fun _ => 0.
Definition RO_LO : Z := 0x9bc80.
Definition RO_HI : Z := 0x9d068.

(* ============================== the contract (HPgCSpec.hd_lib_contract_x at image A) ============================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Definition headamp_lib_contract_x : Prop :=
@hd_lib_contract_x fx rc AE2k.tfib_sink_head AB1v.tfibsegs LS B MT AE2k.tfib_K XM_LIB XN_LIB RLO RHI
ACfn.A_LLVMF ACfn.RA_LLVMF ACfn.A_EMPTY ACfn.EV_LIB ACfn.LIVE_LIB ACfn.LLVMF_STK.
End a.
Definition headamp_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @headamp_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.

(* ============================== the statement the walk proves ============================== *)
(* At image A's symbols TfibB, the meter that counts nothing and XL0 (as every released libreac closing), the
   read-only range RO_LO .. RO_HI. *)
Definition headamp_lib_x_all_stmt : Prop :=
forall (rc : YM05.RunCeil) (LS : lib_shape),
(forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) ->
(forall fx : YK11.FPState, @afree_realizes fx rc AB1v.tfibsegs AD2l.TfibB) ->
(forall fx : YK11.FPState, @amalloc_realizes fx rc AB1v.tfibsegs AD2l.TfibB) ->
@headamp_lib_contract_x_all rc LS AD2l.TfibB ameter_triv XL0 XL0 RO_LO RO_HI.

(* ============================== the adapter to the core's contract ============================== *)
(* The core's fx-slot contract (lib/A/ACfn.v tfib_lib_contract_xf_all, fuzz_grant's text) is the same text at the
   same segments, sink and constants: HPgBase.arodata_okP segs RLO RHI B is ACfn's arodata_okS segs B RLO RHI. *)
Lemma headamp_lib_contract_x_all_tfib {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) :
headamp_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI -> ACfn.tfib_lib_contract_xf_all B MT XM_LIB XN_LIB RLO RHI.
Proof. intros HX fx. exact (HX fx). Qed.
