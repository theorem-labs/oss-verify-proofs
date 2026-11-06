(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition assert_VSB_state_entry : Z := 0x89c88.
Definition ASSERT_STATE_STACK : Z := 16.
Definition VSB_extendsize_entry : Z := 0x8b148.
Definition EXTSZ_STACK : Z := 16.
Definition vep_warn_entry : Z := 0x90664.

Section S.
Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition assert_VSB_state_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem) (S : Z) (vr : vsb_rec) (fin : bool) (lo : Z),
      a0 = Z_to_bv 64 S ->
      rw_cells rsegs v S (vsb_cells vr) -> vsb_inv vr fin ->
      a1 = Z_to_bv 64 (if fin then 0x20000 else 0) ->      (* [comment removed for export] *)
      shadowed LPA v S 40 -> cenv v ->
      S mod 8 = 0 -> kHighMemBeg <= S -> S + 40 <= alloc_ceiling ->
      stk rsegs v lo (bv_unsigned sp) -> lo + ASSERT_STATE_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vsb_leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None ASSERT_STATE_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 assert_VSB_state_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition VSB_extendsize_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem) (sz : Z) (lo : Z),
      a0 = Z_to_bv 64 sz -> 0 <= sz <= 2^40 ->
      stk rsegs v lo (bv_unsigned sp) -> lo + EXTSZ_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Some (vsb_extendsize sz)) EXTSZ_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSB_extendsize_entry) fc None v (seg_rom rsegs)).
  (* [comment removed for export] *)
  Definition vep_warn_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 VEP ->
      rw_cells rsegs v VEP (vep_cells vv tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      vv Fvc = h_vc H -> glob_ok LPA VIA H v -> hobj_ok LPA VIA H v -> hshadow LPA H v -> henv_geom LPA H -> cenv v ->
      shadowed LPA v VEP 312 -> kHighMemBeg <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling ->
      (h_ff H + HFSIZE <= VEP \/ VEP + 312 <= h_ff H) ->
      stk rsegs v lo (bv_unsigned sp) -> lo + VEPERR_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vep_error_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vep_warn_entry) fc None v (seg_rom rsegs)).
End S.
