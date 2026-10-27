(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO09.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Record lleaf := LL { ll_ret : Z; ll_fs : Fs; ll_out : list byte }.
Class lib_shape := {
LIBK : list byte -> Fs -> (lleaf -> TSet) -> TSet;
LIBK_ext : forall pl fs K K', (forall l, t_eq (K l) (K' l)) -> t_eq (LIBK pl fs K) (LIBK pl fs K');
lib_delta : Z -> rbound -> rbound;
lib_room : rbound -> Z -> Prop
}.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Fixpoint lib_iter (pl : list byte) (j : nat) (K : Fs -> TSet) (fs : Fs) : TSet :=
match j with
| O => K fs
| S j' => LIBK pl fs (fun l => lib_iter pl j' K (ll_fs l))
end.
Definition run_tail (m : nat) (fs : Fs) : TSet :=
match m with O => ex 0 fs | S _ => wr ch_stdout (concat (repeat line0 m)) (ex 0 fs) end.
Definition run_shape (pl : list byte) (k : nat) (fs : Fs) : TSet :=
match k with
| O => ex 0 fs
| S k' => LIBK pl fs (fun l => wr ch_stdout line0 (lib_iter pl k' (run_tail k') (ll_fs l)))
end.
Fixpoint rb_calls (n : Z) (k : nat) (b : rbound) : rbound :=
match k with O => b | S k' => rb_calls n k' (lib_delta n b) end.
Fixpoint room_calls (n : Z) (k : nat) (b : rbound) : Prop :=
match k with O => True | S k' => lib_room b n /\ room_calls n k' (lib_delta n b) end.
End a.
