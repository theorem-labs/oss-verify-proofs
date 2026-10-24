(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0o YK0s YK15 YM06 YM02 YP0m YP0e YP09 YP0l YP0k YP06 YP03 YP08 YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01 YL0d YL0g YL05 YI06 YI16 YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SH : sink_head} {SK : sink_syms}.
Definition env_ivl : ivl :=
[(sk_ofl_head, sk_ofl_head + 8); (sk_threaded, sk_threaded + 1); (sk_ofl_lock, sk_ofl_lock + 4);
(sk_path_addr, sk_path_addr + 13); (sk_mode_addr, sk_mode_addr + 3); (sk_trailer_addr, sk_trailer_addr + 2);
(sk_rwa_addr, sk_rwa_addr + 8); (sk_highs_addr, sk_highs_addr + 8); (sk_ones_addr, sk_ones_addr + 8)].
Lemma env_addr_ivl : forall a, env_addr a -> in_ivl env_ivl a = true.
Proof.
intros a Ha. unfold env_addr in Ha. unfold in_ivl, env_ivl. apply existsb_exists.
destruct Ha as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]];
[ exists (sk_ofl_head, sk_ofl_head + 8) | exists (sk_threaded, sk_threaded + 1) | exists (sk_ofl_lock, sk_ofl_lock + 4)
| exists (sk_path_addr, sk_path_addr + 13) | exists (sk_mode_addr, sk_mode_addr + 3) | exists (sk_trailer_addr, sk_trailer_addr + 2)
| exists (sk_rwa_addr, sk_rwa_addr + 8) | exists (sk_highs_addr, sk_highs_addr + 8) | exists (sk_ones_addr, sk_ones_addr + 8) ];
(split; [cbn; tauto | cbn [fst snd]; rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia; reflexivity]).
Qed.
Definition env_check (rs : smem) : bool :=
forallb (fun p => sub_ivl (cimg_ivl rs) (fst p) (snd p)) env_ivl.
Lemma env_of_regions : forall segs E mem rs,
Forall (region_ok segs E mem) rs -> env_check rs = true ->
forall a, env_addr a -> mbyte segs mem a = seg_rom segs (Z_to_bv 64 a).
Proof.
intros segs E mem rs HF Hck a Ha.
apply (cimg_ivl_sound segs E mem rs a HF).
pose proof (env_addr_ivl a Ha) as Hin. unfold in_ivl in Hin. apply existsb_exists in Hin as (p & Hp & Hpa).
apply andb_prop in Hpa as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
unfold env_check in Hck. pose proof (forallb_In _ _ p Hck Hp) as Hsub. cbn beta in Hsub.
exact (sub_ivl_sound _ _ _ a Hsub ltac:(lia)).
Qed.
Lemma env_of_st_ok : forall segs E ss ms,
st_ok segs E ss ms -> env_check (ss_mem ss) = true ->
forall a, env_addr a -> mbyte segs (ms_mem ms) a = seg_rom segs (Z_to_bv 64 a).
Proof.
intros segs E ss ms HS Hck. destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
exact (env_of_regions segs E (ms_mem ms) (ss_mem ss) (proj1 (proj2 HM)) Hck).
Qed.
End b.
