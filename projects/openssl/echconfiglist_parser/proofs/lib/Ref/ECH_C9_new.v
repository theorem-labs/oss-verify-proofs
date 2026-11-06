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
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C7_read ECH_C7_new.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition B64N_RA1 : Z := 0x26e3c4.   (* [comment removed for export] *)
  Definition B64N_RA2 : Z := 0x26e3e8.   (* [comment removed for export] *)
  Definition B64_FILE : Z := 0x2a3a3.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bn_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      a0 = Z_to_bv 64 A_b64_method ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 NEX_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp)) s1
                       (Z_to_bv 64 128) (Z_to_bv 64 BIO_FILE) (Z_to_bv 64 83) a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_b64_method)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_new) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros A0 ST CEIL LO MI. subst a0. hcb.
    unfold P_BIO_new, P_CRYPTO_zalloc, NEX_RA1, BIO_FILE, A_b64_method.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 10 st1.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 14 st1.
    finish. all: try eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition bio_hdr1_b64 : biorep := mkBIO A_b64_method 0 1 0 0 0 0 0 0 1 0 0.

  (* [comment removed for export] *)
  Lemma bn_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
      0 < A -> A + BIO_SIZE <= hceil ->
      rw_cells rsegs m A (bio_cells bio_zero) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 NEX_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 A) (Z_to_bv 64 (A + O_BIO_EXDATA))
                       a3 a4 a5 a6 a7 (Z_to_bv 64 (A + O_BIO_EXDATA)) (Z_to_bv 64 A_b64_method) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_new_ex_data) fc None m1 (seg_rom rsegs)
          /\ munch [(A, A + BIO_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 A (bio_cells bio_hdr1_b64))
        (MS (mkR (Z_to_bv 64 NEX_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_b64_method)
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 NEX_RA1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until A. intros AP AH BLK MI. hcb. unfold NEX_RA1, NEX_RA2, P_CRYPTO_new_ex_data, CRYPTO_EX_INDEX_BIO, O_BIO_EXDATA, A_b64_method, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0xff4f0)) with (Z_to_bv 64 0xff4f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold bio_cells, bio_zero, wz in BLK. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BLK.
    pose proof (munch_refl [(A, A + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. st1. st1. st1. step. st1. step. step. step. step. step. step.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A lo : Z),
      0 < A -> A + BIO_SIZE <= hceil -> METH_b64 m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 B64N_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 A)
                       (Z_to_bv 64 B64CTX_SIZE) (Z_to_bv 64 B64_FILE) (Z_to_bv 64 73) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 A_b64_method)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 j; C8 (Z_to_bv 64 A_b64_method); C8 s2; C8 (Z_to_bv 64 A); C8 s0; C8 (Z_to_bv 64 NEX_RA3)]
          /\ METH_b64 m1)
        (MS (mkR (Z_to_bv 64 NEX_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 A_b64_method)
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 NEX_RA2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros AP AH METH ST CEIL LO MI. hcb.
    unfold NEX_RA2, NEX_RA3, B64N_RA1, P_CRYPTO_zalloc, B64_FILE, A_b64_method, BIO_SIZE, B64CTX_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0xff528)) with (Z_to_bv 64 0xff528) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof METH as METH0. unfold METH_b64, O_METH_BREAD, A_b64_method, P_b64_new, wz in METH. norm_addr METH.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    st1. step. if_false. step. step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 15 st1.
    finish. all: try eassumption.
    all: eapply rw_cells_transport; [exact METH0| exact MU| exact WM| unfold A_b64_method; cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Definition b64ctx_zero_cells : list cell :=
    [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); CB 2528 (zeros 2528); C8 (wz 0); C8 (wz 0)].
  Definition b64ctx_cs_cells : list cell :=
    [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0); C8 (wz 0); CB 2528 (zeros 2528); C8 (wz 0); C8 (wz 0)].
  Lemma b64ctx_zero_recut : forall m C, rw_cells rsegs m C [CB (Z.to_nat B64CTX_SIZE) (zeros (Z.to_nat B64CTX_SIZE))] -> rw_cells rsegs m C b64ctx_zero_cells.
  Proof. intros m C HB. eapply rw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma bn_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 s2 s3 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (C : Z),
      0 < C -> C + B64CTX_SIZE <= hceil ->
      rw_cells rsegs m C b64ctx_zero_cells -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 B64N_RA2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (C + 2047)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 C)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_ENCODE_CTX_new) fc None m1 (seg_rom rsegs)
          /\ munch [(C, C + B64CTX_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 C b64ctx_cs_cells)
        (MS (mkR (Z_to_bv 64 B64N_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) a1 a2 a3 a4 a5 a6 a7 s2 s3
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 B64N_RA1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until C. intros CP CH BLK MI. hcb. unfold B64N_RA1, B64N_RA2, P_EVP_ENCODE_CTX_new, B64CTX_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x26e3c4)) with (Z_to_bv 64 0x26e3c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold b64ctx_zero_cells, wz in BLK.
    pose proof (munch_refl [(C, C + 2584)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step. st1. st1. st1. st1. step.
    finish.
  Qed.

  (* [comment removed for export] *)
  Definition bn_R (C E : Z) (i1 i2 i3 : bptr) : b64frep := mkBF 0 0 0 0 0 C E i1 i2 i3.

  (* [comment removed for export] *)
  Lemma bn_seg5 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s2x : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A C E lo : Z) (j1 j2 : list byte) (i1 i2 i3 : bptr),
      rblock_range A BIO_SIZE -> rblock_range C B64CTX_SIZE -> 0 < E -> E + ENCCTX_SIZE <= hceil ->
      (A + BIO_SIZE <= C \/ C + B64CTX_SIZE <= A) ->
      rw_cells rsegs m A (bio_cells bio_hdr1_b64) ->
      rw_cells rsegs m C b64ctx_cs_cells ->
      METH_b64 m ->
      rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs m (bv_unsigned sp + -96) [CB 8 j2; C8 (Z_to_bv 64 A_b64_method); C8 s2x; C8 (Z_to_bv 64 A); C8 sp; C8 (Z_to_bv 64 NEX_RA3)] ->
      stk rsegs m lo (bv_unsigned sp + -96) -> hceil <= lo -> lo <= bv_unsigned sp - 112 -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1,
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -112, bv_unsigned sp); (A, A + BIO_SIZE); (C, C + B64CTX_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ rw_cells rsegs m1 A (bio_cells (b64f_bio (bn_R C E i1 i2 i3)))
          /\ rw_cells rsegs m1 C (b64ctx_fresh_cells E (zeros 2528))
          /\ METH_b64 m1)
        (MS (mkR (Z_to_bv 64 B64N_RA2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 A)
                 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 C) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 B64N_RA2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until i3. intros RA RC EP EH DJ BA BC METH F1 F2 ST CEIL LO MI RAE. hcb.
    pose proof RA as (AP & _ & _ & AH & AI). pose proof RC as (CP & _ & _ & CH & CI).
    unfold B64N_RA2, NEX_RA3, P_BIO_set_data, P_BIO_set_init, A_b64_method, BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x26e3e8)) with (Z_to_bv 64 0x26e3e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, bio_hdr1_b64, wz in BA. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    unfold A_b64_method in BA. unfold b64ctx_cs_cells, wz in BC.
    pose proof METH as METH0. unfold METH_b64, O_METH_BREAD, A_b64_method, P_b64_new, wz in METH. norm_addr METH.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp); (A, A + 128); (C, C + 2584)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. step. step. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 4 st1. st1. do 3 st1. release_frame FR ST (bv_unsigned sp + -96). step.
    (* [comment removed for export] *)
    step. step. step. step.
    carve_frame 16%nat ST. do 4 st1. st1. do 3 st1. release_frame FR ST (bv_unsigned sp + -96). step.
    (* [comment removed for export] *)
    step. step. st1. st1. st1. st1. st1. step. release_frame F2 ST (bv_unsigned sp + -48). step.
    (* [comment removed for export] *)
    step. if_false. st1. step. if_true. step. st1. st1. st1. st1. st1. step. release_frame F1 ST (bv_unsigned sp).
    step.
    finish. all: try eassumption.
  Qed.
End S.
