(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X080.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0ms X0mx X0n0 X0k2 X0m4 X0m6 X0li X0lh X0ll.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X03o X03n X03m X0fy X0fg X0ed.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0um X0ul X16j X161 X14y.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0ms OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0mx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0n0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0k2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0m4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0m6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0li OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0lh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS.X0ll.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X03o.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0um OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ul OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14y.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Instance hl_fx : X0ms.FPState := X0ms.fx0.

Definition hs_lib_ok (ch : acs) : bool := true.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
(SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Theorem hs_lib_gen : forall A' : list (Z * Z),
(forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
hs_lib_ok ch = true -> LIB_A (mH FULL model A').
Proof using A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC.
intros A' _ _. exact (LIB_A_intro _).
Qed.

Theorem hs_lib : hs_lib_ok ch = true -> LIB_A (mH FULL model (rtA_allow (sigma0 A E ch model))).
Proof using A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC.
intros HT. exact (hs_lib_gen (rtA_allow (sigma0 A E ch model)) (ri_allow A E ch model) HT).
Qed.

End Lib.
End B_TWIN.

Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Instance hl_fx : X0ms.FPState := X0ms.fx0.

Definition hs_lib_ok (ch : acs) : bool := true.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
(SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Theorem hs_lib_gen : forall A' : list (Z * Z),
(forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
hs_lib_ok ch = true -> LIB_A (mH FULL model A').
Proof using A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC.
intros A' _ _. exact (LIB_A_intro _).
Qed.

Theorem hs_lib : hs_lib_ok ch = true -> LIB_A (mH FULL model (rtA_allow (sigma0 A E ch model))).
Proof using A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC.
intros HT. exact (hs_lib_gen (rtA_allow (sigma0 A E ch model)) (ri_allow A E ch model) HT).
Qed.

End Lib.
