(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 18 of its 40 lines of code are new or changed and 218 lines of the source are left out. *)
(* diginet_scribble_text (diginet_codec.c:267-285) at its address in image B (fuzz_codec.asan-ubsan, 0x86500)
   against its image-B contract cdcU_scribble_text_specX (lib/AU/Prog/CPgChkU.v): the six segment lemmas
   (diginet_scribble_text_B_s0.v, _ha.v, _hb.v, _p.v, _l.v, _x.v) composed by the boundary layer
   (diginet_scribble_text_B_inv.v, sc_spec_of_segs: the two loops closed by induction).
   The function makes no call at image B, so the theorem takes no callee or runtime contract. Section hypotheses:
   the meter's laws and the runtime's laws (ameter_laws, TfibLib, AR_laws). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCeh.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import
diginet_scribble_text_B_inv diginet_scribble_text_B_s0 diginet_scribble_text_B_ha diginet_scribble_text_B_hb
diginet_scribble_text_B_p diginet_scribble_text_B_l diginet_scribble_text_B_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Theorem diginet_scribble_text_B_holds : cdcU_scribble_text_specX tfibsegs B MT 0x86500.
Proof.
change 0x86500 with B_ST.
apply (sc_spec_of_segs B MT).
- eapply ss0_holds; eassumption.
- eapply sha_holds; eassumption.
- eapply shb_holds; eassumption.
- eapply sp_holds; eassumption.
- eapply sl_holds; eassumption.
- eapply sx_holds; eassumption.
Qed.
End d.
End b.
