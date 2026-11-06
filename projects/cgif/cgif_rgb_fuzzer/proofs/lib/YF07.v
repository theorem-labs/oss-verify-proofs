(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YK11 YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YB07 YB12.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil} {imgk : img}.
Lemma tfx_rom_all :
ltac:(let T := type of YB07.tra_rom_all in
let F := eval pattern (0x5ff000)%Z in T in
lazymatch F with ?f _ =>
let T1 := eval cbv beta in (f (0x5ff000 + @D_1000 imgk)%Z) in
let T2 := img_gen_type_ty_k imgk T1 in exact T2 end).
Proof.
destruct imgk.
- pose proof YB07.tra_rom_all as H_.
(exact H_).
- pose proof YB12.trb_rom_all as H_.
(exact H_).
Qed.
Lemma tfx_rw_rom :
ltac:(let T := type of YB07.tra_rw_rom in
let F := eval pattern (0xa1000)%Z, (0x5ff000)%Z in T in
lazymatch F with ?f _ _ =>
let T1 := eval cbv beta in (f (0xa1000 + @D_1000 imgk)%Z (0x5ff000 + @D_1000 imgk)%Z) in
let T2 := img_gen_type_ty_k imgk T1 in exact T2 end).
Proof.
destruct imgk.
- pose proof YB07.tra_rw_rom as H_.
(exact H_).
- pose proof YB12.trb_rw_rom as H_.
(exact H_).
Qed.
Lemma tfx_rw_window :
ltac:(let T := type of YB07.tra_rw_window in
let F := eval pattern (0xa1000)%Z, (0x5ff000)%Z in T in
lazymatch F with ?f _ _ =>
let T1 := eval cbv beta in (f (0xa1000 + @D_1000 imgk)%Z (0x5ff000 + @D_1000 imgk)%Z) in
let T2 := img_gen_type_ty_k imgk T1 in exact T2 end).
Proof.
destruct imgk.
- pose proof YB07.tra_rw_window as H_.
(exact H_).
- pose proof YB12.trb_rw_window as H_.
(exact H_).
Qed.
Lemma tfx_segs_eq : ltac:(img_gen_type YB07.tra_segs_eq).
Proof. destruct imgk; [(exact YB07.tra_segs_eq) | (exact YB12.trb_segs_eq)]. Qed.
End a.
