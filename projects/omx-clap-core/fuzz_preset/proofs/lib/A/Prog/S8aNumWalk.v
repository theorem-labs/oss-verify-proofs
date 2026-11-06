(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A, ex_value piece 5 (ev_number): the composition of the sub-pieces of
   S8aNumCut.v into WalkS8a's ev_number_spec (S8aIface.v:305). The continuation chain is
   T -> F -> E -> D (with T) -> C -> B -> A (with T), each sub-piece taking the next cuts' realizes as premises.
   No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP FCiface YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

Lemma ev_number_of_pieces :
  ev_A_stmt B ARx SK -> ev_B_stmt B ARx SK -> ev_C_stmt B ARx SK -> ev_D_stmt B ARx SK ->
  ev_E_stmt B ARx SK -> ev_F_stmt B ARx SK -> ev_T_stmt B ARx SK ->
  (forall a0, as_errno B <= a0 < as_errno B + 4 -> in_img segs a0) ->
  forall I : YStrtodRowX.strtod_img,
  (forall fx1, YStrtodRowX.astrtod_realizes_x (fx := fx1) segs B ARx I (pa_sigma AS_strtod) STK_RT_STRTOD
     strtod_c.strtod_model ev_txt_ok) ->
  ev_strtod_site B ARx I ->
  (forall fx1, aintrin_realizes_xm (fx := fx1) segs B ARx OCpy (pa_sigma AS___asan_memcpy)) ->
  (forall fx1, astrcmp_realizes_xrom (fx := fx1) segs B ARx pa_relro_lo pa_relro_hi (pa_sigma AS___wrap_strcmp)) ->
  (forall fx1, abcmp_realizes_xm (fx := fx1) segs B ARx (pa_sigma AS___wrap_bcmp)) ->
  ev_img_ok ->
  ev_number_spec B ARx SK.
Proof.
intros PA_ PB PC PD PE PF PT HERR I STR SITE CPY CMP BCMP HIMG a.
assert (KTa : KT B ARx SK a) by exact (PT HIMG a).
assert (KDa : KD B ARx SK a) by exact (PF HIMG a KTa).
assert (KCa : KC B ARx SK a) by exact (PE HIMG CMP BCMP a KDa).
assert (KRa : KR B ARx SK a) by exact (PD HIMG a KTa KCa).
assert (KSa : KS B ARx SK a) by exact (PC HIMG HERR I STR SITE CPY a KRa).
assert (KLa : KL B ARx SK a) by exact (PB a KSa).
exact (PA_ HIMG a KTa KLa).
Qed.
End c.
