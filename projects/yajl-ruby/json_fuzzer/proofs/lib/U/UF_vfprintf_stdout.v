(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_memset UF_memcpy UF_fwritex UF_pad.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_stdio_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_pop_arg U_Exit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UF_printf_iface UF_printf_core UF_vfprintf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_pieces.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.  (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Export UF_vfprintf_stdout1 UF_vfprintf_stdout2 UF_vfprintf_stdout3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono usegs m m' -> 356352 <= lo -> stdout_file m' so.
Proof.
  intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
  exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
  - eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.

Lemma out_pieces_outsk {St} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) :
  forall ps, out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. induction ps as [|p ps IH]; [reflexivity|]. cbn [out_pieces outsk]. rewrite IH. reflexivity. Qed.

Theorem emit_printf_proof : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
  emit_printf_stmt get_so set_so.
Proof.
  intros St get_so set_so. unfold emit_printf_stmt. intros until rc. intros GS SS FWX SF RC ERC ST LO GLO QHI SSP MI FRM.
  unfold EMIT_DEPTH, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  unfold zlength in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
  (* [comment removed for export] *)
  unfold stdout_vprintf.
  rewrite (out_pieces_outsk get_so set_so (pieces_emit_d rc)).
  ienter.
  carve_frame 80%nat ST.
  do 15 zs.
  (* [comment removed for export] *)
  do 7 zs.
  apply (proj1 (rw_cells_app usegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
  replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
  pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
  change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
  ileave.
  pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
  eapply implM_post_evt.
  { eapply VF with (A := A_FMT_emit) (VA := bv_unsigned sp + -56) (fmt := FMT_emit) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i rc])
                   (r := cnt_emit_d rc) (lo := lo) (canary := canary);
      clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
    all: try reflexivity. all: try lia.
    all: first [ eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | lia]
               | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_emit; lia | vm_compute; discriminate]
               | unfold FMT_emit; forall_range
               | exact VAA
               | cbn [args_ok arg_ok]; split; [split; [exact RC | exact ERC] | exact I]
               | apply printf_pieces_emit; exact RC
               | exact ST | split; [exact SSP1 | exact SSP2] | exact MI | exact FRM
               | unfold A_FMT_emit, FMT_emit; cbn [length]; lia ]. }
  cbv beta. intros [] st' ms' P. clear MU1.
  unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
  destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  zs. zs. zs.
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
    assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
    [ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
    | clear FR VAC ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed.
End RC__1.
