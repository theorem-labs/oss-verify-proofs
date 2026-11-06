(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import Stdio_kit F_syscalls StdioFiles MonadF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_printf_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Theorem towrite_proof : towrite_stmt.
Proof.
unfold towrite_stmt. intros until tail. intros FC NOWR B0 BHI BS0 MI RFP.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size file_cells csize Nat.add] in FB.
set (Fp := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>1159692297.69 16465536838.6716471341896.5919882575238.6826325528710.6828335790980.662891659680.68 36447186566.6852076332703.6856781706523.6958817367049.699303594756.66 00000400800<00@00D00H00L00P00Q00U00Y00]S2FBS2FBS2FBS2FBS2FBS2FBS2FBS2FBFS2FBS2FBS2FB".
do 5 zs. rewrite FL8. zs. zs. if_lit.
do 10 zs.
apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | let t := type of H in idtac "FC:" t; fail] end.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma arg_ok_vf : forall Fp B BS RNG m m' lo sp sp' ap w a,
arg_ok Fp B BS RNG m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> wmono asegs m m' ->
appW [(lo, sp); (Fp, Fp + 232)] -> arg_ok Fp B BS RNG m' lo sp' ap w a.
Proof.
intros Fp B BS RNG m m' lo sp sp' ap w a H Hsp MU WM AW. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4 & D5 & RG & r & RC & IR & RR). exists slack.
split; [|repeat (split; [first [assumption | lia]|])].
- eapply bytes_at_transport; [exact BY | exact MU |].
cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
- exists r. split; [| split; [exact IR | exact RR]]. eapply rclean_transport; [exact RC | exact MU | exact WM | exact AW].
Qed.
#[using="Type"] Lemma args_ok_vf : forall Fp B BS RNG m m' lo sp sp' ap ws args,
args_ok Fp B BS RNG m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> wmono asegs m m' ->
appW [(lo, sp); (Fp, Fp + 232)] -> args_ok Fp B BS RNG m' lo sp' ap ws args.
Proof.
intros Fp B BS RNG m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU WM AW; [destruct ws; exact I|].
cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.
#[using="Type"] Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
End CANSEC1.
Section CANSEC2. Context {rc : runConstT}.
Definition VF_FRAME : Z := 368.
End CANSEC2.
