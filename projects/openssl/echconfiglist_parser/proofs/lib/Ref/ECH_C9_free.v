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
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C7_read ECH_C7_new ECH_C7_free ECH_C7_freeint ECH_C9_new.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition B64FR_RA1 : Z := 0x26e4a8.   (* [comment removed for export] *)
  Definition B64FR_RA2 : Z := 0x26e4b8.   (* [comment removed for export] *)
  Definition B64FR_RA3 : Z := 0x26e4cc.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo rbp : Z) (R : b64frep) (jv : word) (hdr junk : list byte) (elen : Z),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 rbp -> rw_cells rsegs m rbp [C4 jv] -> bv_unsigned sp <= rbp -> rbp + 4 <= 2^64 ->
      rblock_range a BIO_SIZE -> rblock_range (bf_ctx R) B64CTX_SIZE -> (a + BIO_SIZE <= bf_ctx R \/ bf_ctx R + B64CTX_SIZE <= a) ->
      0 <= bf_flags R < 2^31 -> 0 <= bf_retry R < 2^32 -> 0 <= bf_nread R < 2^63 -> 0 <= bf_next R < 2^64 -> 0 <= bf_prev R < 2^64 -> 0 <= bf_enc R < 2^64 ->
      rw_cells rsegs m a (bio_cells (b64f_bio R)) ->
      length hdr = 32%nat -> length junk = 2528%nat -> 0 <= elen < 2^64 ->
      rw_cells rsegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen) ->
      METH_b64 m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 B64FR_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 (Z_to_bv 64 0) t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 a)
                       (Z_to_bv 64 0) (Z_to_bv 64 B64_FILE) (Z_to_bv 64 103) a3 a4 a5 (Z_to_bv 64 0) a7 (Z_to_bv 64 (bf_ctx R)) (Z_to_bv 64 B64_FILE)
                       (Z_to_bv 64 (bf_ctx R + 2047)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -96, bv_unsigned sp); (rbp, rbp + 4); (a + 88, a + 92)] m m1
          /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -80)
          /\ rw_cells rsegs m1 a (bio_cells (mkBIO A_b64_method 1 1 (bf_flags R) (bf_retry R) 0 (bf_ctx R) (bf_next R) (bf_prev R) 0 (bf_nread R) 0))
          /\ rw_cells rsegs m1 (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen)
          /\ METH_b64 m1
          /\ rw_cells rsegs m1 rbp [C4 (wz 0)]
          /\ rw_cells rsegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
          /\ rw_cells rsegs m1 (bv_unsigned sp + -80) [C8 s4; C8 s3; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 BFI_RA1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free_int) fc None m (seg_rom rsegs)).
  Proof.
    intros until elen. intros A0 A1 SLOT RLO RHI RA RC DJ FLR RTR NRR NXR PVR ENR BC LH LJ ELR CTX METH ST CEIL LO MI. subst a0 a1. hcb.
    pose proof RA as (AP & AAL & _ & AH & AI). pose proof RC as (CP & _ & _ & CH & CI).
    unfold P_BIO_free_int, P_CRYPTO_free, B64FR_RA1, BFI_RA1, B64_FILE, O_BIO_REFS, BIO_SIZE, B64CTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC. unfold b64ctx_used_cells, wz in CTX.
    pose proof METH as METH0. unfold METH_b64, O_METH_BREAD, A_b64_method, P_b64_free, wz in METH. norm_addr METH.
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (rbp, rbp + 4); (a + 88, a + 92)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 6 st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step. astep.
    match goal with |- context [write_to_mem _ _ (Z_to_le_bytes 4 ?v)] => let z := eval vm_compute in v in change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 z)) end.
    mem_after_store.
    change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    (* [comment removed for export] *)
    step.
    st1. step. if_false. step. st1. step. step. if_false.
    (* [comment removed for export] *)
    st1. st1. step. if_true. step. if_true. st1. step. if_false. st1. step. if_false. step. step.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    carve_frame 48%nat ST. do 8 st1. step. step. step.
    carve_frame 16%nat ST. do 4 st1. st1. do 3 st1. release_frame FR1 ST (bv_unsigned sp + -80). step.
    (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    step. step. st1. step. step. step. step. step. step.
    finish; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_seg2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (R : b64frep) (hdr junk : list byte) (elen : Z),
      rblock_range (bf_ctx R) B64CTX_SIZE -> 0 <= bf_enc R < 2^64 ->
      length hdr = 32%nat -> length junk = 2528%nat -> 0 <= elen < 2^64 ->
      rw_cells rsegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen) ->
      stk rsegs m lo (bv_unsigned sp + -80) -> hceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 B64FR_RA2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 a)
                       (Z_to_bv 64 (bf_enc R)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (bf_ctx R)) (Z_to_bv 64 B64_FILE) (Z_to_bv 64 (bf_ctx R + 2047)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_ENCODE_CTX_free) fc None m1 (seg_rom rsegs)
          /\ munch [(bf_ctx R + 2568, bf_ctx R + 2584)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -80)
          /\ rw_cells rsegs m1 (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk 0))
        (MS (mkR (Z_to_bv 64 B64FR_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 a)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (bf_ctx R)) (Z_to_bv 64 B64_FILE) (Z_to_bv 64 (bf_ctx R + 2047)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 B64FR_RA1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until elen. intros RC ENR LH LJ ELR CTX ST CEIL LO MI. hcb.
    pose proof RC as (CP & _ & _ & CH & CI).
    unfold B64FR_RA1, B64FR_RA2, B64_FILE, P_EVP_ENCODE_CTX_free, B64CTX_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x26e4a8)) with (Z_to_bv 64 0x26e4a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold b64ctx_used_cells, wz in CTX.
    pose proof (munch_refl [(bf_ctx R + 2568, bf_ctx R + 2584)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    st1. st1. st1. step.
    finish; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (c : Z),
      mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 B64FR_RA3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 B64_FILE) (Z_to_bv 64 107) a3 a4 a5 a6 a7
                       (Z_to_bv 64 c) (Z_to_bv 64 B64_FILE) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 B64FR_RA2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 c) (Z_to_bv 64 B64_FILE) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 B64FR_RA2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until c. intros MI. unfold B64FR_RA2, B64FR_RA3, B64_FILE, P_CRYPTO_free in *.
    replace (ret_pc (Z_to_bv 64 0x26e4b8)) with (Z_to_bv 64 0x26e4b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_seg4 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3x s4x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (fl rt ctx nx pv nr : Z),
      rblock_range a BIO_SIZE -> 0 <= fl < 2^31 -> 0 <= rt < 2^32 -> 0 <= ctx < 2^64 -> 0 <= nx < 2^64 -> 0 <= pv < 2^64 -> 0 <= nr < 2^63 ->
      rw_cells rsegs m a (bio_cells (mkBIO A_b64_method 1 1 fl rt 0 ctx nx pv 0 nr 0)) ->
      rw_cells rsegs m (bv_unsigned sp + -80) [C8 s4; C8 s3; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 BFI_RA1)] ->
      stk rsegs m lo (bv_unsigned sp + -80) -> hceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 BFI_RA2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 a) (Z_to_bv 64 (a + O_BIO_EXDATA)) a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free_ex_data) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -96, bv_unsigned sp + -80); (a + 40, a + 44); (a + 64, a + 72)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells rsegs m1 a (bio_cells (mkBIO A_b64_method 0 1 fl rt 0 0 nx pv 0 nr 0)))
        (MS (mkR (Z_to_bv 64 B64FR_RA3) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 a)
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 B64FR_RA3)) fc None m (seg_rom rsegs)).
  Proof.
    intros until nr. intros RA FLR RTR CXR NXR PVR NRR BC FR0 ST CEIL LO MI. hcb.
    pose proof RA as (AP & AAL & _ & AH & AI).
    unfold B64FR_RA3, BFI_RA1, BFI_RA2, P_CRYPTO_free_ex_data, CRYPTO_EX_INDEX_BIO, O_BIO_EXDATA, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x26e4cc)) with (Z_to_bv 64 0x26e4cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC.
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp + -80); (a + 40, a + 44); (a + 64, a + 72)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    step. step. step. step.
    carve_frame 16%nat ST. do 4 st1. st1. do 3 st1. release_frame FR ST (bv_unsigned sp + -80). step.
    (* [comment removed for export] *)
    step. step. step. step.
    carve_frame 16%nat ST. do 4 st1. st1. do 3 st1. release_frame FR ST (bv_unsigned sp + -80). step.
    (* [comment removed for export] *)
    step. do 6 st1. step. release_frame FR0 ST (bv_unsigned sp + -32). step.
    (* [comment removed for export] *)
    step. step. step. step.
    finish; try eassumption.
  Qed.
End S.
