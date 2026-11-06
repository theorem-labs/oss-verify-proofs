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
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C6_acc ECH_C7_stmt ECH_C7_read ECH_C7_rd ECH_C7_new ECH_C7_free.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma fi_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo rbp : Z) (R : membio) (jv : word),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 rbp -> rw_cells rsegs m rbp [C4 jv] -> bv_unsigned sp <= rbp -> rbp + 4 <= 2^64 -> rblock_range a BIO_SIZE -> rblock_range (mb_bb R) BIOBUFMEM_SIZE -> rblock_range (mb_bm R) BUFMEM_SIZE ->
      MEMBIO_apart a R ->
      0 <= mb_pos R <= mb_len R -> 0 <= mb_len R < 2^31 -> 0 < mb_buf R -> mb_buf R + mb_len R <= hceil ->
      0 <= mb_flags R < 2^31 -> Z.land (mb_flags R) BIO_FLAGS_MEM_RDONLY = BIO_FLAGS_MEM_RDONLY -> 0 <= mb_nread R < 2^63 -> 0 <= mb_next R < 2^64 -> 0 <= mb_prev R < 2^64 ->
      mb_numf R = 0 ->
      rw_cells rsegs m a (bio_cells (membio_bio R)) ->
      rw_cells rsegs m (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))] ->
      rw_cells rsegs m (mb_bm R) (buf_cells (mkBUF (mb_len R - mb_pos R) (mb_buf R + mb_pos R) (mb_len R - mb_pos R) 0)) ->
      METH_mem m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 MBF_RA) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 (Z_to_bv 64 0) t2 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 1)
                       (Z_to_bv 64 (mb_bm R)) (Z_to_bv 64 (mb_bb R)) (Z_to_bv 64 2) a3 a4 a5 (Z_to_bv 64 0) a7 (Z_to_bv 64 1) s3
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BUF_MEM_free) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -96, bv_unsigned sp); (rbp, rbp + 4); (a + 88, a + 92); (mb_bm R + 8, mb_bm R + 16)] m m1
          /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -96)
          /\ rw_cells rsegs m1 a (bio_cells (bio_unref (membio_bio R)))
          /\ rw_cells rsegs m1 (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))]
          /\ rw_cells rsegs m1 (mb_bm R) (buf_cells (mkBUF (mb_len R - mb_pos R) 0 (mb_len R - mb_pos R) 0))
          /\ METH_mem m1
          /\ rw_cells rsegs m1 rbp [C4 (wz 0)]
          /\ rw_cells rsegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
          /\ rw_cells rsegs m1 (bv_unsigned sp + -64) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 BFI_RA1)]
          /\ (exists j, rw_cells rsegs m1 (bv_unsigned sp + -96) [CB 8 j; C8 (Z_to_bv 64 (mb_bb R)); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 MF_RA1)]))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free_int) fc None m (seg_rom rsegs)).
  Proof.
    intros until jv. intros A0 A1 SLOT RLO RHI RA RBB RBM APART POSR LENR BUFP BUFH FLR RDO NRD NXT PRV NUMF BA BB BM METH ST CEIL LO MI. subst a0 a1. hcb.
    pose proof RA as (AP & AAL & _ & AH & AI). pose proof RBB as (BBP & _ & _ & BBH & BBI). pose proof RBM as (BMP & _ & _ & BMH & BMI).
    destruct APART as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6).
    unfold P_BIO_free_int, P_BUF_MEM_free, MBF_RA, BFI_RA1, MF_RA1, O_BIO_REFS, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, membio_bio, wz in BA. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    unfold A_mem_buf_method in BA. rewrite NUMF in BA. unfold wz in BB. unfold buf_cells, wz in BM. cbn [bm_len bm_data bm_max bm_flags] in BM.
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, P_mem_free, wz in METH. norm_addr METH.
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (rbp, rbp + 4); (a + 88, a + 92); (mb_bm R + 8, mb_bm R + 16)] m) as MU.
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
    carve_frame 32%nat ST. do 6 st1. st1. step.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 5 st1. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    st1. step. step. if_false. st1. step. if_false. st1. step. if_cases K3; zify_cond K3; [kill K3|]. clear K3.
    pose proof (bio_flags_byte1_raw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BA ltac:(lia)) as RD1'. step. clear RD1'.
    st1. step. rewrite wz_unsigned by (pose proof (Z.mod_pos_bound (mb_flags R / 256) 256 ltac:(lia)); lia).
    rewrite (rdonly_byte1 (mb_flags R)) by lia.
    step. if_false. st1. step.
    finish; try eassumption.
    - unfold bio_cells, bio_unref, membio_bio, wz. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      unfold A_mem_buf_method. rewrite NUMF. exact BA.
    - eexists. eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fi_seg2 :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (bb bm rp lo : Z) (j : list byte),
      rblock_range bb BIOBUFMEM_SIZE ->
      rw_cells rsegs m bb [C8 (wz bm); C8 (wz rp)] ->
      rw_cells rsegs m (bv_unsigned sp + -96) [CB 8 j; C8 (Z_to_bv 64 bb); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 MF_RA1)] ->
      stk rsegs m lo (bv_unsigned sp + -96) -> hceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 MF_RA2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 bb)
                       (Z_to_bv 64 rp) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 153) a3 a4 a5 a6 a7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs)
          /\ stk rsegs m lo (bv_unsigned sp + -64))
        (MS (mkR (Z_to_bv 64 MBF_RA) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MBF_RA)) fc None m (seg_rom rsegs)).
  Proof.
    intros until j. intros RBB BB FR ST CEIL LO MI. hcb. pose proof RBB as (BBP & _ & _ & BBH & BBI).
    unfold MBF_RA, MF_RA1, MF_RA2, MEM_FILE, P_CRYPTO_free, BIOBUFMEM_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x1d5dbc)) with (Z_to_bv 64 0x1d5dbc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold wz in BB.
    step. step. st1. st1. st1. step. step. release_frame FR ST (bv_unsigned sp + -64).
    step. if_false. st1. step. step. step. step. step.
    apply evt_done. split; [reflexivity| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma fi_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z),
      rw_cells rsegs m (bv_unsigned sp + -64) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 BFI_RA1)] ->
      0 < a -> a + BIO_SIZE <= hceil ->
      stk rsegs m lo (bv_unsigned sp + -64) -> hceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 BFI_RA2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 a) (Z_to_bv 64 (a + O_BIO_EXDATA)) a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free_ex_data) fc None m (seg_rom rsegs)
          /\ stk rsegs m lo (bv_unsigned sp + -32))
        (MS (mkR (Z_to_bv 64 MF_RA3) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MF_RA3)) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros FR AP AH ST CEIL LO MI. hcb.
    unfold MF_RA3, BFI_RA1, BFI_RA2, P_CRYPTO_free_ex_data, CRYPTO_EX_INDEX_BIO, O_BIO_EXDATA, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x1d5ce4)) with (Z_to_bv 64 0x1d5ce4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    step. st1. st1. st1. st1. step. step. release_frame FR ST (bv_unsigned sp + -32).
    step. step. step. step.
    apply evt_done. split; [reflexivity| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma fi_seg6 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells rsegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk rsegs m lo (bv_unsigned sp + -32) -> hceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom rsegs)
          /\ stk rsegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 BFI_RA3) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 BFI_RA3)) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros F1 ST CEIL LO MI RAE. hcb. unfold BFI_RA3 in *.
    replace (ret_pc (Z_to_bv 64 0xff700)) with (Z_to_bv 64 0xff700) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    step. step. st1. st1. st1. st1. step. release_frame F1 ST (bv_unsigned sp). step.
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.
