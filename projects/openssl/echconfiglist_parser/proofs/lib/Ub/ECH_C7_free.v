(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C6_acc ECH_C7_stmt ECH_C7_read ECH_C7_rd ECH_C7_new ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma bio_flags_byte1 : forall m a B, rw_cells usegs m a (bio_cells B) -> 0 <= bio_flags B < 2^64 ->
  ov_read_bytes usegs m (wa (a + 49)) 1 = Some [b8 ((bio_flags B / 256) mod 256)].
Proof.
  intros m a B [[_ HB] _] POS.
  rewrite (bytes_at_ov_read usegs m a (cells_bytes (bio_cells B)) 49 1 HB) by (cbn; lia).
  cbn. f_equal. f_equal. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (Z.mod_small (bio_flags B) (2^64)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma bio_flags_byte1_raw : forall m a (v0 v1 v2 v3 v4 i sh rt nf z0 ptr nx pv rf z1 nr nw e1 e2 : word) f,
  rw_cells usegs m a [C8 v0; C8 v1; C8 v2; C8 v3; C8 v4; C4 i; C4 sh; C4 (Z_to_bv 64 f); C4 rt; C4 nf; C4 z0; C8 ptr; C8 nx; C8 pv; C4 rf; C4 z1; C8 nr; C8 nw; C8 e1; C8 e2] ->
  0 <= f < 2^64 ->
  ov_read_bytes usegs m (wa (a + 49)) 1 = Some [b8 ((f / 256) mod 256)].
Proof.
  intros until f. intros [[_ HB] _] POS.
  rewrite (bytes_at_ov_read usegs m a _ 49 1 HB) by (cbn; lia).
  cbn. f_equal. f_equal. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (Z.mod_small f (2^64)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rdonly_byte1 : forall f, 0 <= f -> Z.land f 512 = 512 -> Z.land ((f / 256) mod 256) 2 = 2.
Proof.
  intros f Hf H. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  destruct (Z.eq_dec k 1) as [->|NE].
  - change (Z.testbit 2 1) with true. rewrite Bool.andb_true_r.
    change 256 with (2^8). rewrite <- Z.land_ones, Z.land_spec, <- Z.shiftr_div_pow2, Z.shiftr_spec by lia.
    rewrite Z.ones_spec_low by lia. rewrite Bool.andb_true_r. change (1 + 8) with 9.
    apply (f_equal (fun z => Z.testbit z 9)) in H. rewrite Z.land_spec in H. change (Z.testbit 512 9) with true in H.
    rewrite Bool.andb_true_r in H. exact H.
  - replace (Z.testbit 2 k) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec k 0) as [->|]; [reflexivity|]. apply Z.bits_above_log2; [lia|]. cbn. lia.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition BF_RET : Z := 0x10aaa8.     (* [comment removed for export] *)
  Definition BFI_RA1 : Z := 0x10ab70.    (* [comment removed for export] *)
  Definition BFI_RA2 : Z := 0x10ab80.    (* [comment removed for export] *)
  Definition BFI_RA3 : Z := 0x10ab94.    (* [comment removed for export] *)
  Definition MF_RA1 : Z := 0x2087f8.     (* [comment removed for export] *)
  Definition MF_RA2 : Z := 0x208820.     (* [comment removed for export] *)
  Definition MF_RA3 : Z := 0x208834.     (* [comment removed for export] *)
  Definition MBF_RA : Z := MF_RA1.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition bio_unref (B : biorep) : biorep :=
    mkBIO (bio_method B) (bio_init B) (bio_shutdown B) (bio_flags B) (bio_retry B) (bio_numf B) (bio_ptr B) (bio_next B) (bio_prev B) 0 (bio_nread B) (bio_nwrite B).

  (* [comment removed for export] *)
  Lemma fr_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (R : membio),
      a0 = Z_to_bv 64 a -> bv_unsigned sp mod 16 = 0 (* [comment removed for export] *) -> rblock_range a BIO_SIZE -> rblock_range (mb_bb R) BIOBUFMEM_SIZE -> rblock_range (mb_bm R) BUFMEM_SIZE ->
      MEMBIO_apart a R ->
      0 <= mb_pos R <= mb_len R -> 0 <= mb_len R < 2^31 -> 0 < mb_buf R -> mb_buf R + mb_len R <= hceil ->
      0 <= mb_flags R < 2^31 -> Z.land (mb_flags R) BIO_FLAGS_MEM_RDONLY = BIO_FLAGS_MEM_RDONLY -> 0 <= mb_nread R < 2^63 -> 0 <= mb_next R < 2^64 -> 0 <= mb_prev R < 2^64 ->
      mb_numf R = 0 ->
      rw_cells usegs m a (bio_cells (membio_bio R)) ->
      rw_cells usegs m (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))] ->
      rw_cells usegs m (mb_bm R) (buf_cells (mkBUF (mb_len R - mb_pos R) (mb_buf R + mb_pos R) (mb_len R - mb_pos R) 0)) ->
      METH_mem m ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j3,
          ms' = MS (mkR (Z_to_bv 64 MBF_RA) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (mb_bb R))
                       (Z_to_bv 64 (mb_bm R)) (Z_to_bv 64 0) (Z_to_bv 64 2) a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)      (* [comment removed for export] *)
                   F (Z_to_bv 64 P_BUF_MEM_free) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -112, bv_unsigned sp); (a + 88, a + 92); (mb_bm R + 8, mb_bm R + 16)] m m1
          /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp + -96)
          /\ rw_cells usegs m1 a (bio_cells (bio_unref (membio_bio R)))
          /\ rw_cells usegs m1 (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))]
          /\ rw_cells usegs m1 (mb_bm R) (buf_cells (mkBUF (mb_len R - mb_pos R) 0 (mb_len R - mb_pos R) 0))
          /\ METH_mem m1
          /\ rw_cells usegs m1 (bv_unsigned sp + -32) [CB 12 j3; C4 (wz 0); C8 s0; C8 ra]
          /\ rw_cells usegs m1 (bv_unsigned sp + -64) [C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 BF_RET)]
          /\ rw_cells usegs m1 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 BFI_RA1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free) fc None m (seg_rom usegs)).
  Proof.
    intros until R. intros A0 SPAL RA RBB RBM APART POSR LENR BUFP BUFH FLR RDO NRD NXT PRV NUMF BA BB BM METH ST CEIL LO MI. subst a0. hcb.
    pose proof RA as (AP & AAL & _ & AH & AI). pose proof RBB as (BBP & BBAL & _ & BBH & BBI). pose proof RBM as (BMP & BMAL & _ & BMH & BMI).
    destruct APART as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6).
    unfold P_BIO_free, P_BUF_MEM_free, MBF_RA, BF_RET, BFI_RA1, MF_RA1, O_BIO_REFS, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, membio_bio, wz in BA. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    unfold A_mem_buf_method in BA. rewrite NUMF in BA. unfold wz in BB. unfold buf_cells, wz in BM. cbn [bm_len bm_data bm_max bm_flags] in BM.
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, P_mem_free, wz in METH. norm_addr METH.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (a + 88, a + 92); (mb_bm R + 8, mb_bm R + 16)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 6 st1.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 6 st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. ubal_by AAL. step. if_lit.
    step. step. astep.
    match goal with |- context [write_to_mem _ _ (Z_to_le_bytes 4 ?v)] => let z := eval vm_compute in v in change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 z)) end.
    mem_after_store.
    change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    (* [comment removed for export] *)
    step.
    step. if_lit.
    step. ubal_by SPAL. step. if_lit.
    st1. step. if_false. step. st1. step. step. if_false.
    (* [comment removed for export] *)
    st1. step. if_false. st1. step. if_true. st1. step. if_false. step. ubal. step. if_lit. st1. step. if_false. step. step.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 6 st1.
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    step. ubal_by AAL. step. if_lit. st1. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 4 st1. step. ubal_by AAL. step. if_lit.
    st1. step. if_false. st1. step. if_false. st1. step. if_cases K3; zify_cond K3; [kill K3|]. clear K3.
    step. ubal_by BBAL. step. if_lit.
    pose proof (bio_flags_byte1_raw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BA ltac:(lia)) as RD1'. step. clear RD1'.
    st1. step. rewrite wz_unsigned by (pose proof (Z.mod_pos_bound (mb_flags R / 256) 256 ltac:(lia)); lia).
    rewrite (rdonly_byte1 (mb_flags R)) by lia.
    step. if_false. step. if_cases K3; zify_cond K3; [kill K3|]. clear K3. step. ubal_by BMAL. step. if_lit.
    st1. st1. st1. step. release_frame FR2 ST (bv_unsigned sp + -96). step.
    finish; try eassumption.
    - unfold bio_cells, bio_unref, membio_bio, wz. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      unfold A_mem_buf_method. rewrite NUMF. exact BA.
  Qed.
  (* [comment removed for export] *)
  Lemma fr_seg2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (bb bm rp lo : Z),
      rblock_range bb BIOBUFMEM_SIZE ->
      rw_cells usegs m bb [C8 (wz bm); C8 (wz rp)] ->
      stk usegs m lo (bv_unsigned sp + -96) -> hceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 MF_RA2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 bb)
                       (Z_to_bv 64 rp) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 153) a3 a4 a5 a6 a7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs)
          /\ stk usegs m lo (bv_unsigned sp + -96))
        (MS (mkR (Z_to_bv 64 MBF_RA) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 bb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MBF_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros RBB BB ST CEIL LO MI. hcb. pose proof RBB as (BBP & BBAL & _ & BBH & BBI).
    unfold MBF_RA, MF_RA1, MF_RA2, MEM_FILE, P_CRYPTO_free, BIOBUFMEM_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x2087f8)) with (Z_to_bv 64 0x2087f8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold wz in BB.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. ubal_by BBAL. step. if_lit.   (* [comment removed for export] *)
    st1. step. step. step. step. step. step.                                                   (* [comment removed for export] *)
    apply evt_done. split; [reflexivity| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma fr_seg3 :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (bb : Z),
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 MF_RA3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 bb) (Z_to_bv 64 bb) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 154) a3 a4 a5 a6 a7
                       (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 MF_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 bb) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MEM_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MF_RA2)) fc None m (seg_rom usegs)).
  Proof.
    intros until bb. intros MI. unfold MF_RA2, MF_RA3, MEM_FILE, P_CRYPTO_free in *.
    replace (ret_pc (Z_to_bv 64 0x208820)) with (Z_to_bv 64 0x208820) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. apply evt_done. reflexivity.        (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma fr_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z),
      rw_cells usegs m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (bv_unsigned sp + -32)); C8 (Z_to_bv 64 BFI_RA1)] ->
      0 < a -> a + BIO_SIZE <= hceil ->
      stk usegs m lo (bv_unsigned sp + -96) -> hceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 BFI_RA2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 a)
                       (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 a) (Z_to_bv 64 (a + O_BIO_EXDATA)) a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free_ex_data) fc None m (seg_rom usegs)
          /\ stk usegs m lo (bv_unsigned sp + -64))
        (MS (mkR (Z_to_bv 64 MF_RA3) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MF_RA3)) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros FR AP AH ST CEIL LO MI. hcb.
    unfold MF_RA3, BFI_RA1, BFI_RA2, P_CRYPTO_free_ex_data, CRYPTO_EX_INDEX_BIO, O_BIO_EXDATA, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x208834)) with (Z_to_bv 64 0x208834) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    step. st1. st1. st1. st1. step. step. release_frame FR ST (bv_unsigned sp + -64).
    step. step. step. step.
    apply evt_done. split; [reflexivity| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma fr_seg5 :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 BFI_RA3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) (Z_to_bv 64 a) (Z_to_bv 64 BIO_FILE) (Z_to_bv 64 145) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 BFI_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 BFI_RA2)) fc None m (seg_rom usegs)).
  Proof.
    intros until a. intros MI. unfold BFI_RA2, BFI_RA3, BIO_FILE, P_CRYPTO_free in *.
    replace (ret_pc (Z_to_bv 64 0x10ab80)) with (Z_to_bv 64 0x10ab80) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_seg6 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (j3 : list byte),
      rw_cells usegs m (bv_unsigned sp + -64) [C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 BF_RET)] ->
      rw_cells usegs m (bv_unsigned sp + -32) [CB 12 j3; C4 (wz 0); C8 s0; C8 ra] ->
      stk usegs m lo (bv_unsigned sp + -64) -> hceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom usegs)
          /\ stk usegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 BFI_RA3) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 BFI_RA3)) fc None m (seg_rom usegs)).
  Proof.
    intros until j3. intros F1 F0 ST CEIL LO MI RAE. hcb. unfold BFI_RA3, BF_RET in *.
    replace (ret_pc (Z_to_bv 64 0x10ab94)) with (Z_to_bv 64 0x10ab94) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold wz in F0.
    step. step. st1. st1. st1. st1. step. step. release_frame F1 ST (bv_unsigned sp + -32).
    st1. st1. step. step. release_frame F0 ST (bv_unsigned sp).
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S.
