(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Ref Require Import F_syscalls RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import StoreOk L5TopStretch.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module TE3W.
(* [comment removed for export] *)
Definition RESIZE : Z := 0x210bc.          (* [comment removed for export] *)
Definition RESIZE_RET1 : Z := 0x210e0.     (* [comment removed for export] *)
Definition BRESERVE : Z := 0x211e0.        (* [comment removed for export] *)
Definition ARESERVE : Z := 0x213d0.        (* [comment removed for export] *)
Definition ASSERT_THROW : Z := 0x21470.    (* [comment removed for export] *)
Definition MAXW : Z := 2 ^ 61 - 1.         (* [comment removed for export] *)

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.

Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | MG : mem_grows ?mq m |- _ => apply (TS.mem_grows_write' mq m (wa a) bs) in MG
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Lemma e3x : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
                   (lo fb len cap : Z),
  stk rsegs m lo (bv_unsigned sp) -> 0x7fff7f800000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
  MAXW <= bv_unsigned a1 ->
  bv_unsigned a0 + 32 <= 2 ^ 47 -> (bv_unsigned a0 + 32 <= bv_unsigned sp - 128 \/ bv_unsigned sp <= bv_unsigned a0) ->
  ro_cells rsegs m (bv_unsigned a0 + 0) [C1 (b8 fb)] -> 0 <= fb < 256 -> Z.testbit fb 0 = true ->
  ro_cells rsegs m (bv_unsigned a0 + 8) [C8 (wz len)] -> ro_cells rsegs m (bv_unsigned a0 + 16) [C8 (wz cap)] ->
  0 <= len < 2 ^ 64 -> 0 <= cap < MAXW ->
  evt rsegs (fun ms' => exists (j0 j1 : list byte) m',
      ms' = MS (mkR (wz RESIZE_RET1) (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 a0 a1 (wz 16) a1 (wz MAXW) a3 a4 a5 a6 a7
                   (wz len) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASSERT_THROW) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -128)
           [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 (wz len); C8 a1; C8 a0; C8 (wz RESIZE_RET1);
            CB 32 j1; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_grows m m'
      /\ stk rsegs m' lo (bv_unsigned sp + -128))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 RESIZE) fc None m (seg_rom rsegs)).
Proof.
  intros until cap. intros ST CLO LO SHI Hn Oh OAP FB Hfb DYN OL OC Hlen Hcap.
  unfold RESIZE, RESIZE_RET1, ASSERT_THROW, MAXW in *.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra0, Ra1. cbn in Ra0, Ra1.
  pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (mem_grows_refl m) as MG.
  carve_frame 128%nat ST.
  (* [comment removed for export] *)
  do 9 st1.
  (* [comment removed for export] *)
  set (RA1 := Z_to_bv 64 135392).
  (* [comment removed for export] *)
  do 14 st1.
  (* [comment removed for export] *)
  rewrite (TS.land1_bit0 fb ltac:(lia)), DYN.
  st1; if_cases K; zify_cond K; [| exfalso; lia].
  (* [comment removed for export] *)
  st1; if_cases K2; zify_cond K2; [exfalso; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia; lia|].
  (* [comment removed for export] *)
  st1; if_cases K3; zify_cond K3; [| exfalso; rewrite ?unsigned_lit in K3 by lia; lia].
  do 12 st1.
  (* [comment removed for export] *)
  do 8 st1.
  st1; if_cases K4; zify_cond K4; [| exfalso; lia].
  st1. subst RA1.
  finish. exact FR.
Qed.
End TE3W.
