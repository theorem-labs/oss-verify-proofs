(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition BFA_RA : Z := 0x100674.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bfa_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (B : biorep),
      a0 = Z_to_bv 64 a -> rblock_range a BIO_SIZE ->
      0 <= bio_method B < 2^64 -> 0 <= bio_init B < 2^32 -> 0 <= bio_shutdown B < 2^32 -> 0 <= bio_flags B < 2^32 -> 0 <= bio_retry B < 2^32 -> 0 <= bio_numf B < 2^32 ->
      0 <= bio_ptr B < 2^64 -> 0 <= bio_next B < 2^64 -> 0 <= bio_prev B < 2^64 -> 0 <= bio_refs B < 2^32 -> 0 <= bio_nread B < 2^64 -> 0 <= bio_nwrite B < 2^64 ->
      rw_cells rsegs m a (bio_cells B) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 BFA_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bio_next B))
                       (Z_to_bv 64 a) (Z_to_bv 64 (bv_unsigned sp + -28)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_int) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 4 j; C4 (wz 0); C8 s1; C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free_all) fc None m (seg_rom rsegs)).
  Proof.
    intros until B. intros A0 RA M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 BC ST CEIL LO MI. subst a0. hcb.
    pose proof RA as (AP & AAL & _ & AH & AI).
    unfold P_BIO_free_all, P_BIO_free_int, BFA_RA, BIO_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, wz in BC.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    carve_frame 32%nat ST. do 6 st1.
    st1. st1. st1. step. step.
    finish; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma bfa_seg2 :
    forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (s1o s0o rao : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb lo : Z) (j : list byte) (B : biorep),
      0 < mb < 2^64 -> rblock_range mb BIO_SIZE ->
      0 <= bio_method B < 2^64 -> 0 <= bio_init B < 2^32 -> 0 <= bio_shutdown B < 2^32 -> 0 <= bio_flags B < 2^32 -> 0 <= bio_retry B < 2^32 -> 0 <= bio_numf B < 2^32 ->
      0 <= bio_ptr B < 2^64 -> 0 <= bio_next B < 2^64 -> 0 <= bio_prev B < 2^64 -> 0 <= bio_refs B < 2^32 -> 0 <= bio_nread B < 2^64 -> 0 <= bio_nwrite B < 2^64 ->
      rw_cells rsegs m mb (bio_cells B) ->
      rw_cells rsegs m (bv_unsigned sp + -32) [CB 4 j] -> rw_cells rsegs m (bv_unsigned sp + -28) [C4 (wz 0)] ->
      rw_cells rsegs m (bv_unsigned sp + -24) [C8 s1o; C8 s0o; C8 rao] ->
      stk rsegs m lo (bv_unsigned sp + -32) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 BFA_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bio_next B))
                       (Z_to_bv 64 mb) (Z_to_bv 64 (bv_unsigned sp + -28)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_int) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -28, bv_unsigned sp + -24)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -28) [C4 (wz 0)])
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 mb) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 BFA_RA)) fc None m (seg_rom rsegs)).
  Proof.
    intros until B. intros MBR RM M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 BC FRJ SLOT FR3 ST CEIL LO MI. hcb.
    pose proof RM as (MP & MAL & _ & MH & MI_).
    unfold P_BIO_free_int, BFA_RA, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x100674)) with (Z_to_bv 64 0x100674) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, wz in BC. unfold wz in SLOT.
    pose proof (munch_refl [(bv_unsigned sp + -28, bv_unsigned sp + -24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. if_cases K1; zify_cond K1; [|kill K1]; clear K1.
    st1. st1. st1. step. step.
    finish; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma bfa_seg3 :
    forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (s1o s0o rao : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (j : list byte),
      rw_cells rsegs m (bv_unsigned sp + -32) [CB 4 j] -> rw_cells rsegs m (bv_unsigned sp + -28) [C4 (wz 0)] ->
      rw_cells rsegs m (bv_unsigned sp + -24) [C8 s1o; C8 s0o; C8 rao] ->
      stk rsegs m lo (bv_unsigned sp + -32) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m -> bv_unsigned rao mod 2 = 0 ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR rao sp gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc rao) fc None m (seg_rom rsegs)
          /\ stk rsegs m lo (bv_unsigned sp))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 BFA_RA)) fc None m (seg_rom rsegs)).
  Proof.
    intros until j. intros FRJ SLOT FR3 ST CEIL LO MI RAE. hcb. unfold BFA_RA in *.
    replace (ret_pc (Z_to_bv 64 0x100674)) with (Z_to_bv 64 0x100674) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold wz in SLOT.
    (* [comment removed for export] *)
    st1. step. if_false. step. if_false.
    st1. st1. st1. step.
    release_frame FRJ ST (bv_unsigned sp + -28). release_frame SLOT ST (bv_unsigned sp + -24). release_frame FR3 ST (bv_unsigned sp).
    step.
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.
