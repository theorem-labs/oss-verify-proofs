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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C6_acc ECH_C7_stmt ECH_C7_read ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition BIO_FILE : Z := 0x1db74.      (* [comment removed for export] *)
  Definition MEM_FILE : Z := 0x122aa.      (* [comment removed for export] *)
  Definition NMB_RET : Z := 0x207f68.      (* [comment removed for export] *)
  Definition NEX_RA1 : Z := 0x10a974.      (* [comment removed for export] *)
  Definition NEX_RA2 : Z := 0x10a9b4.      (* [comment removed for export] *)
  Definition NEX_RA3 : Z := 0x10a9d4.      (* [comment removed for export] *)
  Definition MI_RA1 : Z := 0x2089bc.       (* [comment removed for export] *)
  Definition MI_RA2 : Z := 0x2089cc.       (* [comment removed for export] *)
  Definition MI_RA3 : Z := 0x2089f4.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma nm_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (buf len lo : Z),
      a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 len -> 0 < buf -> buf + len <= hceil -> 0 <= len < 2^31 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 NEX_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 buf)
                       (Z_to_bv 64 128) (Z_to_bv 64 BIO_FILE) (Z_to_bv 64 83) a3 a4 a5 a6 a7 (Z_to_bv 64 A_mem_buf_method) (Z_to_bv 64 0)   (* [comment removed for export] *)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -80)
          /\ rw_cells usegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
          /\ rw_cells usegs m1 (bv_unsigned sp + -80) [CB 8 j; C8 s3; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 buf); C8 sp; C8 (Z_to_bv 64 NMB_RET)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_new_mem_buf) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros A0 A1 BP BH LR ST CEIL LO MI. subst a0 a1. hcb.
    unfold P_BIO_new_mem_buf, P_CRYPTO_zalloc, NEX_RA1, BIO_FILE, NMB_RET, A_mem_buf_method.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 6 st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step. if_cases K1; zify_cond K1; [| kill K1]. clear K1.
    step. step. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 10 st1.
    release_frame FR0 ST (bv_unsigned sp + -32).
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 14 st1.
    finish. eassumption.
  Qed.
  (* [comment removed for export] *)
  Definition bio_zero : biorep := mkBIO 0 0 0 0 0 0 0 0 0 0 0 0.
  Definition bio_hdr1 : biorep := mkBIO A_mem_buf_method 0 1 0 0 0 0 0 0 1 0 0.
  (* [comment removed for export] *)
  Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof.
    induction l1 as [|x l1 IH]; destruct l2 as [|y l2]; cbn; intros E; try discriminate; [reflexivity|].
    injection E as E1 E2. f_equal; [apply bv_eq; exact E1| apply IH; exact E2].
  Qed.
  Lemma bio_zero_recut : forall m A, rw_cells usegs m A [CB (Z.to_nat BIO_SIZE) (zeros (Z.to_nat BIO_SIZE))] -> rw_cells usegs m A (bio_cells bio_zero).
  Proof. intros m A HB. eapply rw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.
  (* [comment removed for export] *)
  Lemma bio_cells_split_ex : forall m A B, rw_cells usegs m A (bio_cells B) ->
    rw_cells usegs m A (firstn 18 (bio_cells B)) /\ rw_cells usegs m (A + O_BIO_EXDATA) [C8 (wz 0); C8 (wz 0)].
  Proof.
    intros m A B HB. unfold bio_cells in *.
    change (rw_cells usegs m A (firstn 18 [C8 (wz 0); C8 (wz (bio_method B)); C8 (wz 0); C8 (wz 0); C8 (wz 0);
       C4 (wz (bio_init B)); C4 (wz (bio_shutdown B)); C4 (wz (bio_flags B)); C4 (wz (bio_retry B));
       C4 (wz (bio_numf B)); C4 (wz 0); C8 (wz (bio_ptr B)); C8 (wz (bio_next B)); C8 (wz (bio_prev B));
       C4 (wz (bio_refs B)); C4 (wz 0); C8 (wz (bio_nread B)); C8 (wz (bio_nwrite B)); C8 (wz 0); C8 (wz 0)] ++ [C8 (wz 0); C8 (wz 0)])) in HB.
    apply rw_cells_app in HB. cbn [cells_size csize firstn Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HB. unfold O_BIO_EXDATA. exact HB.
  Qed.
  Lemma bio_cells_join_ex : forall m A B, rw_cells usegs m A (firstn 18 (bio_cells B)) -> rw_cells usegs m (A + O_BIO_EXDATA) [C8 (wz 0); C8 (wz 0)] ->
    rw_cells usegs m A (bio_cells B).
  Proof.
    intros m A B H1 H2. unfold bio_cells in *.
    change (rw_cells usegs m A (firstn 18 [C8 (wz 0); C8 (wz (bio_method B)); C8 (wz 0); C8 (wz 0); C8 (wz 0);
       C4 (wz (bio_init B)); C4 (wz (bio_shutdown B)); C4 (wz (bio_flags B)); C4 (wz (bio_retry B));
       C4 (wz (bio_numf B)); C4 (wz 0); C8 (wz (bio_ptr B)); C8 (wz (bio_next B)); C8 (wz (bio_prev B));
       C4 (wz (bio_refs B)); C4 (wz 0); C8 (wz (bio_nread B)); C8 (wz (bio_nwrite B)); C8 (wz 0); C8 (wz 0)] ++ [C8 (wz 0); C8 (wz 0)])).
    apply rw_cells_app. cbn [cells_size csize firstn Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold O_BIO_EXDATA in H2. split; [exact H1| exact H2].
  Qed.

  (* [comment removed for export] *)
  Lemma nm_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
      0 < A -> A + BIO_SIZE <= hceil -> A mod 16 = 0 (* [comment removed for export] *) ->
      rw_cells usegs m A (bio_cells bio_zero) -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 NEX_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 A) (Z_to_bv 64 (A + O_BIO_EXDATA))
                       a3 a4 a5 a6 a7 (Z_to_bv 64 A_mem_buf_method) (Z_to_bv 64 (A + O_BIO_EXDATA)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)   (* [comment removed for export] *)
                   F (Z_to_bv 64 P_CRYPTO_new_ex_data) fc None m1 (seg_rom usegs)
          /\ munch [(A, A + BIO_SIZE)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 A (bio_cells bio_hdr1))
        (MS (mkR (Z_to_bv 64 NEX_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 A_mem_buf_method) (Z_to_bv 64 0)
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 NEX_RA1)) fc None m (seg_rom usegs)).
  Proof.
    intros until A. intros AP AH AAL BLK MI. hcb. unfold NEX_RA1, NEX_RA2, P_CRYPTO_new_ex_data, CRYPTO_EX_INDEX_BIO, O_BIO_EXDATA, A_mem_buf_method, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x10a974)) with (Z_to_bv 64 0x10a974) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold bio_cells, bio_zero, wz in BLK. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BLK.
    pose proof (munch_refl [(A, A + 128)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. ubal_by AAL. step. if_lit.       (* [comment removed for export] *)
    step. st1. st1. st1. step. st1. step. step. step. step. step. step.
    finish.
  Qed.
  (* [comment removed for export] *)
  Lemma nm_seg3 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A lo : Z),
      0 < A -> A + BIO_SIZE <= hceil -> METH_mem m ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 MI_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 A)
                       (Z_to_bv 64 16) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 111) a3 a4 a5 a6 a7 (Z_to_bv 64 A) (Z_to_bv 64 0)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells usegs m1 (bv_unsigned sp + -48)
               [CB 8 j; C8 (Z_to_bv 64 (A + O_BIO_EXDATA)); C8 (Z_to_bv 64 A_mem_buf_method); C8 (Z_to_bv 64 A); C8 s0; C8 (Z_to_bv 64 NEX_RA3)]   (* [comment removed for export] *)
          /\ METH_mem m1)
        (MS (mkR (Z_to_bv 64 NEX_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 A_mem_buf_method) (Z_to_bv 64 (A + O_BIO_EXDATA)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 NEX_RA2)) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros AP AH METH ST CEIL LO MI. hcb.
    unfold NEX_RA2, NEX_RA3, MI_RA1, P_CRYPTO_zalloc, MEM_FILE, O_BIO_EXDATA, A_mem_buf_method, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x10a9b4)) with (Z_to_bv 64 0x10a9b4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, P_mem_new, wz in METH. norm_addr METH.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. if_lit. step. ubal. step. if_lit.
    st1. step. if_false. step. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 9 st1. release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 15 st1.
    finish. eassumption.
  Qed.
  (* [comment removed for export] *)
  Lemma nm_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Abb : Z),
      0 < Abb -> Abb + BIOBUFMEM_SIZE <= hceil -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 MI_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Abb) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BUF_MEM_new) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 MI_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Abb) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0)
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MI_RA1)) fc None m (seg_rom usegs)).
  Proof.
    intros until Abb. intros AP AH MI. hcb. unfold MI_RA1, MI_RA2, P_BUF_MEM_new, BIOBUFMEM_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x2089bc)) with (Z_to_bv 64 0x2089bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma nm_seg5 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (Abb Abm : Z),
      0 < Abb -> Abb + BIOBUFMEM_SIZE <= hceil -> 0 < Abm -> Abm + BUFMEM_SIZE <= hceil -> Abb mod 16 = 0 (* [comment removed for export] *) ->
      rw_cells usegs m Abb [C8 (wz 0); C8 (wz 0)] -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 MI_RA3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Abb) (Z_to_bv 64 32) (Z_to_bv 64 MEM_FILE) (Z_to_bv 64 119) a3 a4 a5 a6 a7 s2 s3
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom usegs)
          /\ munch [(Abb, Abb + BIOBUFMEM_SIZE)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 Abb [C8 (Z_to_bv 64 Abm); C8 (wz 0)])
        (MS (mkR (Z_to_bv 64 MI_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Abb) (Z_to_bv 64 Abm) a1 a2 a3 a4 a5 a6 a7 s2 s3
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MI_RA2)) fc None m (seg_rom usegs)).
  Proof.
    intros until Abm. intros AP AH MP MH BBAL BB MI. hcb. unfold MI_RA2, MI_RA3, P_CRYPTO_zalloc, MEM_FILE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x2089cc)) with (Z_to_bv 64 0x2089cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold wz in BB.
    pose proof (munch_refl [(Abb, Abb + 16)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. ubal_by BBAL. step. if_lit.                    (* [comment removed for export] *)
    st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step. step. step. step.                  (* [comment removed for export] *)
    finish.
  Qed.
  (* [comment removed for export] *)
  Lemma le4_wz_mod : forall x, le4 (wz x) = le4 (wz (x mod 2^32)).
  Proof.
    intros x. unfold le4, wz. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite <- (Z_to_le_bytes_mod 4 (x mod 2^64) 32) by (cbn; lia).
    rewrite <- (Z_to_le_bytes_mod 4 ((x mod 2^32) mod 2^64) 32) by (cbn; lia).
    f_equal. pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as B.
    rewrite (Z.mod_small (x mod 2^32) (2^64)) by lia. rewrite Z.mod_mod by lia.
    change (2^64) with (2^32 * 2^32). rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm (2^32)), Z.mod_add, Z.mod_mod by lia. reflexivity.
  Qed.
  Lemma rw_cells_C4_mod : forall segs m A pre x post,
    rw_cells segs m A (pre ++ C4 (wz x) :: post) -> rw_cells segs m A (pre ++ C4 (wz (x mod 2^32)) :: post).
  Proof.
    intros segs m A pre x post [[Hwf Hb] Hw]. split; [split|].
    - apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [W1 [_ W3]]. split; [exact W1|]. split; [exact I| exact W3].
    - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite <- le4_wz_mod. exact Hb.
    - rewrite cells_size_app in *. cbn [cells_size csize Nat.add] in *. exact Hw.
  Qed.
  Lemma rw_cells_C8_C4C4 : forall segs m A pre z post, 0 <= z < 2^64 ->
    rw_cells segs m A (pre ++ C8 (wz z) :: post) -> rw_cells segs m A (pre ++ C4 (wz z) :: C4 (wz (Z.shiftr z 32)) :: post).
  Proof.
    intros segs m A pre z post Hz [[Hwf Hb] Hw].
    assert (E : le8 (wz z) = le4 (wz z) ++ le4 (wz (Z.shiftr z 32))).
    { unfold le8, le4, word_to_le_bytes, wz.
      assert (S32 : 0 <= Z.shiftr z 32 < 2^32).
      { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^32) with (2^64). lia. }
      rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. reflexivity. }
    split; [split|].
    - apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [W1 [_ W3]]. split; [exact W1|]. split; [exact I|]. split; [exact I| exact W3].
    - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite E in Hb. rewrite <- app_assoc in Hb. exact Hb.
    - rewrite cells_size_app in *. cbn [cells_size csize Nat.add] in *. exact Hw.
  Qed.

  (* [comment removed for export] *)
  Definition bio_hdr1_cells40 : list cell :=
    [C8 (wz 0); C8 (wz A_mem_buf_method); C8 (wz 0); C8 (wz 0); C8 (wz 0);
     C8 (wz 4294967296); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
     C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Lemma bio_hdr1_recut : forall m A, rw_cells usegs m A (bio_cells bio_hdr1) -> rw_cells usegs m A bio_hdr1_cells40.
  Proof. intros m A HB. eapply rw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| apply bytes_eq_of_unsigned; vm_compute; reflexivity]. Qed.
  Lemma buf_zero_recut : forall m A, rw_cells usegs m A [CB (Z.to_nat BUFMEM_SIZE) (zeros (Z.to_nat BUFMEM_SIZE))] -> rw_cells usegs m A (buf_cells (mkBUF 0 0 0 0)).
  Proof. intros m A HB. eapply rw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.

  (* [comment removed for export] *)
  Definition nm_R (buf len Abb Abm Arp : Z) (i1 i2 i3 i4 : bptr) : membio :=
    mkMB buf len 0 (BIO_FLAGS_MEM_RDONLY + BIO_FLAGS_MEM_LEGACY_EOF) 0 0 0 0 Abb Abm Arp i1 i2 i3 i4.

  (* [comment removed for export] *)
  Lemma nm_seg6 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s0m a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0x : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A Abb Abm Arp buf len lo : Z) (j2 j3 : list byte) (i1 i2 i3 i4 : bptr),
      rblock_range A BIO_SIZE -> rblock_range Abb BIOBUFMEM_SIZE -> rblock_range Abm BUFMEM_SIZE -> rblock_range Arp BUFMEM_SIZE ->
      0 < buf -> buf + len <= hceil -> 0 <= len < 2^31 ->
      MEMBIO_apart A (nm_R buf len Abb Abm Arp i1 i2 i3 i4) ->
      rw_cells usegs m A (bio_cells bio_hdr1) -> rw_cells usegs m Abb [C8 (Z_to_bv 64 Abm); C8 (wz 0)] ->
      rw_cells usegs m Abm (buf_cells (mkBUF 0 0 0 0)) -> rw_cells usegs m Arp [CB (Z.to_nat BUFMEM_SIZE) (zeros (Z.to_nat BUFMEM_SIZE))] ->
      rw_cells usegs m (bv_unsigned sp + -128)
               [CB 8 j3; C8 (Z_to_bv 64 (A + O_BIO_EXDATA)); C8 (Z_to_bv 64 A_mem_buf_method); C8 (Z_to_bv 64 A); C8 s0x; C8 (Z_to_bv 64 NEX_RA3)] ->   (* [comment removed for export] *)
      rw_cells usegs m (bv_unsigned sp + -80) [CB 8 j2; C8 s3; C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 buf); C8 sp; C8 (Z_to_bv 64 NMB_RET)] ->
      rw_cells usegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      METH_mem m ->
      stk usegs m lo (bv_unsigned sp + -128) -> hceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (fun ms' => exists a1' a2' a3' m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + BIO_SIZE); (Abb, Abb + BIOBUFMEM_SIZE); (Abm, Abm + BUFMEM_SIZE); (Arp, Arp + BUFMEM_SIZE)] m m1
          /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp)
          /\ rw_cells usegs m1 A (bio_cells (membio_bio (nm_R buf len Abb Abm Arp i1 i2 i3 i4)))
          /\ rw_cells usegs m1 Abb [C8 (wz Abm); C8 (wz Arp)]
          /\ rw_cells usegs m1 Abm (buf_cells (mkBUF len buf len 0))
          /\ rw_cells usegs m1 Arp (buf_cells (mkBUF len buf len 0))
          /\ METH_mem m1)
        (MS (mkR (Z_to_bv 64 MI_RA3) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0m (Z_to_bv 64 Abb) (Z_to_bv 64 Arp) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 A) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MI_RA3)) fc None m (seg_rom usegs)).
  Proof.
    intros until i4. intros RA RBB RBM RRP BP BH LR APART BA BB BM RP F3 F2 F0 METH ST CEIL LO MI RAE. hcb.
    pose proof RA as (AP & AAL & _ & AH & AI). pose proof RBB as (BBP & BBAL & _ & BBH & BBI). pose proof RBM as (BMP & BMAL & _ & BMH & BMI). pose proof RRP as (RPP & _ & _ & RPH & RPI).
    clear RA RBB RBM RRP.
    unfold MI_RA3, NEX_RA3, NMB_RET, O_BIO_EXDATA, A_mem_buf_method, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x2089f4)) with (Z_to_bv 64 0x2089f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct APART as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6). cbn [mb_bb mb_bm mb_rp nm_R] in AP1, AP2, AP3, AP4, AP5, AP6.
    unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AP1, AP2, AP3, AP4, AP5, AP6.
    apply bio_hdr1_recut in BA. unfold bio_hdr1_cells40, A_mem_buf_method, wz in BA.
    unfold wz in BB. unfold buf_cells, wz in BM. cbn [bm_len bm_data bm_max bm_flags] in BM.
    apply buf_zero_recut in RP. unfold buf_cells, wz in RP. cbn [bm_len bm_data bm_max bm_flags] in RP.
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, P_mem_new, wz in METH. norm_addr METH.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + 128); (Abb, Abb + 16); (Abm, Abm + 32); (Arp, Arp + 32)] m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    st1. st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    st1. st1. st1. st1. st1. st1. st1. st1.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. ubal_by AAL. step. if_lit.     (* [comment removed for export] *)
    st1. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). step. step. step.
    step. change (Z.lor (bv_unsigned (Z_to_bv 64 0)) 4096) with 4096. step. step.
    st1. st1. st1. st1. step.
    do 5 st1. step. step.
    (* [comment removed for export] *)
    step. if_false. st1. step. if_true. step. do 5 st1. step. step.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    step. ubal_by AAL. step. if_lit.
    st1. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step. ubal_by BBAL. step. if_lit.
    st1. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step. ubal_by BMAL. step. if_lit.
    st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. step. do 4 st1. step. step.
    release_frame F3 ST (bv_unsigned sp + -80). release_frame F2 ST (bv_unsigned sp + -32). release_frame F0 ST (bv_unsigned sp).
    (* [comment removed for export] *)
    lazymatch type of BA with rw_cells _ ?mm _ [?c0; ?c1; ?c2; ?c3; ?c4; C8 (Z_to_bv 64 4294967297); ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14; ?c15; ?c16; ?c17; ?c18] =>
      change (rw_cells usegs mm A ([c0; c1; c2; c3; c4] ++ C8 (wz 4294967297) :: [c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18])) in BA;
      apply rw_cells_C8_C4C4 in BA; [| lia];
      apply rw_cells_C4_mod in BA;
      change (4294967297 mod 2 ^ 32) with 1 in BA; change (Z.shiftr 4294967297 32) with 1 in BA;
      cbn [app] in BA
    end.
    finish.
  Qed.
End S.
