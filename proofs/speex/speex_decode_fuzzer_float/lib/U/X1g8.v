(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1g7 X1g0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma unpack_pair : forall b n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. destruct (speex_bits_unpack_unsigned b n); reflexivity. Qed.

#[using="Type"] Lemma user_handler_proof : @user_handler_stmt ptr.
Proof.
unfold user_handler_stmt. intros until m. intros REP OK STK LO GLO APA APD -> -> -> MI FRM.
unfold USERH_DEPTH, NB_GLOBALS_TOP, apart in *.
assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. rewrite bits_cells_size in GB by exact Lrj.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold bits_cells in OBJ. clear REP.
pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold A_speex_default_user_handler.
carve_frame 16%nat STK.
do 5 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
assert (REP : bits_rep rsegs m1 A D b).
{ split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]. }
clear OBJ DAT.

zstep. call (speex_bits_unpack_unsigned_spec A D b 4); [exact REP | exact OK | lia | exact MI |].
clear REP. try rename MI0 into MI. rewrite (unpack_pair b 4) in *. cbn [fst snd] in *.
match goal with H : bits_rep _ _ _ _ (ub b 4) |- _ => rename H into REP1 end.
match goal with H : ?v = Z_to_bv 64 (uv b 4) |- _ => subst v end.
pose proof (speex_bits_unpack_unsigned_ok b 4 _ _ OK ltac:(lia) (unpack_pair b 4)) as sfP_; first [ sf_destruct 6%nat sfP_ as OK1 Hv _ _ Hbs1 _ | sf_fb; destruct sfP_ as (OK1 & Hv & _ & _ & Hbs1 & _) ].

zstep. zstep. zstep. rewrite wrap32_small, (Z.shiftr_div_pow2 _ 29), (Z.div_small _ (2^29)), swrap32_small by lia.
zstep. let K := fresh "K" in if_cases K; zify_cond K; [exfalso; lia | clear K].
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite swrap32_small by lia.
zstep. zstep.
replace (uv b 4 * 8 + 5) with (5 + 8 * uv b 4) by lia.
zstep. call (speex_bits_advance_spec A D (ub b 4) (5 + 8 * uv b 4)); [exact REP1 | exact OK1 | exact MI | lia |].
clear REP1. try rename MI0 into MI.
match goal with H : bits_rep _ _ _ _ (speex_bits_advance (ub b 4) _) |- _ => rename H into REP2 end.
pose proof (speex_bits_advance_ok (ub b 4) (5 + 8 * uv b 4) OK1) as AOK.

zstep. zstep. zstep. zstep.
release_frame FR STK (bv_unsigned sp).
zstep.
apply evt_done. unfold user_handler_post.
eexists (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). sf_eexists 3%nat.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact STK|].
unfold user_handler_bits. split; [exact REP2|].
apply AOK. unfold bits_ok, bits_pos in OK1 |- *. lia.
Qed.
End F.
