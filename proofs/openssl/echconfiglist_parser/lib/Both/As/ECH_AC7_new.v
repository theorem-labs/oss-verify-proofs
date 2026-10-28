(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  (* [comment removed for export] *)
  Local Ltac reacc ACC0 MU NSW :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ACC0 with accessible _ ?x ?n =>
        let T := fresh "ACC" in
        assert (T : accessible mx x n) by (eapply accessible_across2; [exact ACC0| exact MU| exact NSW])
      end end.

  Definition ANEX_RA1 : Z := 0x236c64.    (* [comment removed for export] *)
  Definition ANEX_RA2 : Z := 0x236cf0.    (* [comment removed for export] *)
  Definition ANEX_RA3 : Z := 0x236d24.    (* [comment removed for export] *)
  Definition AMI_RA1 : Z := 0x418608.     (* [comment removed for export] *)
  Definition AMI_RA2 : Z := 0x41861c.     (* [comment removed for export] *)
  Definition AMI_RA3 : Z := 0x418654.     (* [comment removed for export] *)
  Definition AMI_RA4 : Z := 0x418688.     (* [comment removed for export] *)
  Definition ANMB_RET : Z := 0x4170e4.    (* [comment removed for export] *)
  Definition ANMB_RA2 : Z := 0x4171a0.    (* [comment removed for export] *)
  Definition ABIO_FILE : Z := 0x71560.     (* [comment removed for export] *)
  Definition AMEM_FILE : Z := 0xbfff0.     (* [comment removed for export] *)

  Definition bio_zero : biorep := mkBIO 0 0 0 0 0 0 0 0 0 0 0 0.
  Definition bio_hdr1 (mt : Z) : biorep := mkBIO mt 0 1 0 0 0 0 0 0 1 0 0.
  (* [comment removed for export] *)
  Definition bio_hdr2 (bb : Z) : biorep := mkBIO A_mem_buf_method 1 1 4096 0 (-1) bb 0 0 1 0 0.
  Definition bio_hdr3 (bb : Z) : biorep := mkBIO A_mem_buf_method 1 1 4608 0 0 bb 0 0 1 0 0.
  Definition buf_zero : bufrep := mkBUF 0 0 0 0.
  Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof.
    induction l1 as [|b1 l1 IH]; intros [|b2 l2] E; cbn in E; try discriminate; [reflexivity|].
    injection E as E1 E2. f_equal; [apply bv_eq; exact E1| apply IH; exact E2].
  Qed.
  Lemma bio_zero_recut : forall m A, rw_cells asegs m A [CB (Z.to_nat BIO_SIZE) (zeros (Z.to_nat BIO_SIZE))] -> rw_cells asegs m A (bio_cells bio_zero).
  Proof. intros m A HB. eapply arw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.
  Lemma bb_zero_recut : forall m A, rw_cells asegs m A [CB (Z.to_nat BIOBUFMEM_SIZE) (zeros (Z.to_nat BIOBUFMEM_SIZE))] -> rw_cells asegs m A [C8 (wz 0); C8 (wz 0)].
  Proof. intros m A HB. eapply arw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.
  Lemma buf_zero_recut : forall m A, rw_cells asegs m A [CB (Z.to_nat BUFMEM_SIZE) (zeros (Z.to_nat BUFMEM_SIZE))] -> rw_cells asegs m A (buf_cells buf_zero).
  Proof. intros m A HB. eapply arw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.
  (* [comment removed for export] *)
  Lemma bio_cells_split_ex : forall m A B, rw_cells asegs m A (bio_cells B) ->
    rw_cells asegs m A (firstn 18 (bio_cells B)) /\ rw_cells asegs m (A + O_BIO_EXDATA) [C8 (wz 0); C8 (wz 0)].
  Proof.
    intros m A B HB. unfold bio_cells in *.
    match type of HB with rw_cells _ _ _ ?cs =>
      let l := eval cbv in (firstn 18 cs) in change cs with (l ++ [C8 (wz 0); C8 (wz 0)]) in HB end.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in HB. destruct HB as [H1 H2]. cbn [firstn]. split; [exact H1|].
    cbn [cells_size csize Nat.add] in H2. unfold O_BIO_EXDATA. exact H2.
  Qed.
  Lemma bio_cells_join_ex : forall m A B, rw_cells asegs m A (firstn 18 (bio_cells B)) -> rw_cells asegs m (A + O_BIO_EXDATA) [C8 (wz 0); C8 (wz 0)] ->
    rw_cells asegs m A (bio_cells B).
  Proof.
    intros m A B H1 H2. unfold bio_cells in *.
    match goal with |- rw_cells _ _ _ ?cs =>
      let l := eval cbv in (firstn 18 cs) in change cs with (l ++ [C8 (wz 0); C8 (wz 0)]) end.
    apply (proj2 (rw_cells_app asegs _ _ _ _)). cbn [firstn] in H1. split; [exact H1|]. cbn [cells_size csize Nat.add]. unfold O_BIO_EXDATA in H2. exact H2.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (buf len lo : Z),
      a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 len -> 0 < buf -> buf + len <= aceil -> 0 <= len < 2^31 -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 ANEX_RA1) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) s1
                       (Z_to_bv 64 128) (Z_to_bv 64 ABIO_FILE) (Z_to_bv 64 83) a3 a4 a5 a6 a7 (Z_to_bv 64 A_mem_buf_method) (Z_to_bv 64 0)
                       (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -112, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -112)
          /\ rw_cells asegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
          /\ rw_cells asegs m1 (bv_unsigned sp + -112) [CB 8 j; C8 s5; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1; C8 sp; C8 (Z_to_bv 64 ANMB_RET)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_new_mem_buf) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros A0 A1 BP BH LR AC ST CEIL LO MI. subst a0 a1. acb.
    unfold P_BIO_new_mem_buf, P_CRYPTO_zalloc, ANEX_RA1, ABIO_FILE, ANMB_RET, A_mem_buf_method.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    carve_frame 48%nat ST.
    do 8 step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step. step. step. step. if_cases K1; zify_cond K1; [| kill K1]. clear K1.
    step. step. step. step.
    carve_frame 16%nat ST. step. st1. st1. step. step. step. st1. st1. step. step. release_frame FR0 ST (bv_unsigned sp + -48).
    carve_frame 64%nat ST. step. do 8 st1. do 10 step.
    finish; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A mt : Z),     (* [comment removed for export] *)
      0 < A -> A mod 16 = 0 -> A + BIO_SIZE <= aceil -> aapp A BIO_SIZE ->
      rw_cells asegs m A (bio_cells bio_zero) -> accessible m A BIO_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ANEX_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 A) (Z_to_bv 64 (A + O_BIO_EXDATA))
                       a3 a4 a5 a6 a7 (Z_to_bv 64 mt) (Z_to_bv 64 (A + O_BIO_EXDATA)) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_new_ex_data) fc None m1 (seg_rom asegs)
          /\ munch [(A, A + BIO_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 A (bio_cells (bio_hdr1 mt)))
        (MS (mkR (Z_to_bv 64 ANEX_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 mt) (Z_to_bv 64 0)
                 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ANEX_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until mt. intros AP AAL AH AAP BLK ACC MI. pose proof (aword_range (Z_to_bv 64 mt)) as MTR. acb. unfold ANEX_RA1, ANEX_RA2, P_CRYPTO_new_ex_data, CRYPTO_EX_INDEX_BIO, O_BIO_EXDATA, A_mem_buf_method, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x236c64)) with (Z_to_bv 64 0x236c64) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold bio_cells, bio_zero, wz in BLK. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BLK.
    pose proof (munch_refl [(A, A + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. unfold ALOWSH_LO, AHI_LO in NSA.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(A, A + 128)]) by nsw_tac.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. idtac. step. ubal_any. step. if_lit. step. zstep. ck8_check ACC A. st1.
    zstep. zstep. zstep. reacc ACC MU NSW. ck8_check ACC0 (A + 8). clear ACC0. st1.
    zstep. zstep. zstep. reacc ACC MU NSW. ck8_check ACC0 (A + 44). clear ACC0. step. zstep. st1.
    zstep. zstep. reacc ACC MU NSW. ck8_check ACC0 (A + 88). clear ACC0. step. st1. step.
    zstep. step. step. step. step.
    finish. all: unfold bio_cells, bio_hdr1, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg3 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A lo : Z),
      ACONST m -> METH_mem m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AMI_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 16) (Z_to_bv 64 AMEM_FILE) (Z_to_bv 64 111)
                       a3 a4 a5 a6 a7 (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148195517) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells asegs m1 (bv_unsigned sp + -48) [C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_mem_buf_method + 72)); C8 (Z_to_bv 64 A); C8 s0; C8 (Z_to_bv 64 ANEX_RA3)])
        (MS (mkR (Z_to_bv 64 ANEX_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 A_mem_buf_method) (Z_to_bv 64 (A + 112))
                 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ANEX_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AC NM ST CEIL LO MI. acb. unfold ANEX_RA2, ANEX_RA3, AMI_RA1, AMEM_FILE, P_CRYPTO_zalloc, A_mem_buf_method in *.
    replace (ret_pc (Z_to_bv 64 0x236cf0)) with (Z_to_bv 64 0x236cf0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof NM as MT. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT. norm_addr MT.
    assert (IN : In (0x5ae5a0, 112, 112) aglobals) by in_nth.
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt.
    assert (ACCmt : accessible m 0x5ae5a0 112) by (eapply addressable_accessible; [exact ADmt| lia| lia| unfold AAPP_HI; lia]).
    step. if_lit. step. ub_dead. step. step. if_lit. zstep. zstep. zstep. ck8_check_lit ACCmt (0x5ae5a0 + 72). st1. step. if_false. step. unfold P_mem_new. step.
    carve_frame 16%nat ST. step. st1. st1. step. step. st1. st1. step. step. release_frame FR ST (bv_unsigned sp).
    carve_frame 48%nat ST. step. do 6 st1. do 12 step.
    change (5957024 + 72) with 5957096. finish. all: exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (BB : Z), 0 < BB < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AMI_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 BB) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0)
                                        (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 P_BUF_MEM_new) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AMI_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BB) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0)
                 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMI_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until BB. intros BBP MI. unfold AMI_RA1, AMI_RA2 in *.
    replace (ret_pc (Z_to_bv 64 0x418608)) with (Z_to_bv 64 0x418608) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. step. step. unfold P_BUF_MEM_new. step.
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg5 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (BB BM : Z),
      0 < BM < 2^64 -> BB mod 16 = 0 -> aapp BB BIOBUFMEM_SIZE -> rw_cells asegs m BB [C8 (wz 0); C8 (wz 0)] -> accessible m BB BIOBUFMEM_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AMI_RA3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 BB) (Z_to_bv 64 32) (Z_to_bv 64 AMEM_FILE) (Z_to_bv 64 119)
                       a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.shiftr BB 3 + 2147450880)) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(BB, BB + BIOBUFMEM_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 BB [C8 (wz BM); C8 (wz 0)])
        (MS (mkR (Z_to_bv 64 AMI_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 BB) (Z_to_bv 64 BM) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0)
                 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMI_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until BM. intros BMP BBAL AAP BBC ACC MI. acb. unfold AMI_RA2, AMI_RA3, AMEM_FILE, P_CRYPTO_zalloc, BIOBUFMEM_SIZE in *. unfold wz in BBC |- *.
    replace (ret_pc (Z_to_bv 64 0x41861c)) with (Z_to_bv 64 0x41861c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [(BB, BB + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHI & BBP & _). unfold AAPP_HI in AHI.
    step. ubal_by BBAL. step. if_lit. zstep. zstep. ck8_check ACC BB. st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step. step. step. step.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg6 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (BB BM RP : Z),
      0 < RP < 2^64 -> 0 <= BM < 2^64 -> aapp BB BIOBUFMEM_SIZE -> rw_cells asegs m BB [C8 (wz BM); C8 (wz 0)] -> accessible m BB BIOBUFMEM_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AMI_RA4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 BB) (Z_to_bv 64 RP) (Z_to_bv 64 BM) (Z_to_bv 64 32)
                       a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.shiftr BB 3 + 2147450880)) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
          /\ munch [(BB, BB + BIOBUFMEM_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 BB [C8 (wz BM); C8 (wz RP)])
        (MS (mkR (Z_to_bv 64 AMI_RA3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 BB) (Z_to_bv 64 RP) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (Z.shiftr BB 3 + 2147450880))
                 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMI_RA3)) fc None m (seg_rom asegs)).
  Proof.
    intros until RP. intros RPP BMR AAP BBC ACC MI. acb. unfold AMI_RA3, AMI_RA4, AASAN_MEMCPY, BIOBUFMEM_SIZE in *. unfold wz in BBC |- *.
    replace (ret_pc (Z_to_bv 64 0x418654)) with (Z_to_bv 64 0x418654) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [(BB, BB + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHI & BBP & _). unfold AAPP_HI in AHI.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. unfold ALOWSH_LO, AHI_LO in NSA.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(BB, BB + 16)]) by nsw_tac.
    zstep. zstep. zstep. ck8_check ACC (BB + 8). st1.
    reacc ACC MU NSW. ck8_check ACC0 BB. clear ACC0. st1. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg7 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (s0x s0o s1o s5o : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A BB RP buf len lo : Z) (j : list byte),
      aapp A BIO_SIZE -> A mod 16 = 0 -> rw_cells asegs m A (firstn 18 (bio_cells (bio_hdr1 A_mem_buf_method))) -> accessible m A BIO_SIZE -> 0 <= BB < 2^64 ->
      ACONST m -> METH_mem m ->
      rw_cells asegs m (bv_unsigned sp + -48) [C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 (A + 112)); C8 (Z_to_bv 64 (A_mem_buf_method + 72)); C8 (Z_to_bv 64 A); C8 s0x; C8 (Z_to_bv 64 ANEX_RA3)] ->
      rw_cells asegs m (bv_unsigned sp) [CB 8 j; C8 s5o; C8 (Z_to_bv 64 2147450880); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 len); C8 s1o; C8 s0o; C8 (Z_to_bv 64 ANMB_RET)] ->
      stk asegs m lo (bv_unsigned sp + -48) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> bv_unsigned sp + 64 <= 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ANMB_RET) (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 buf) (Z_to_bv 64 2147450880) s5o s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ANMB_RET) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp + 64); (A, A + 112)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + 64)
          /\ rw_cells asegs m1 A (firstn 18 (bio_cells (bio_hdr2 BB))))
        (MS (mkR (Z_to_bv 64 AMI_RA4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 BB) (Z_to_bv 64 RP) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 A) (Z_to_bv 64 (Z.shiftr BB 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2148195517) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMI_RA4)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros AAP AAL BA ACC BBR AC NM FRM FRX ST CEIL LO SPH MI. acb. unfold AMI_RA4, ANEX_RA3, ANMB_RET, A_mem_buf_method, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x418688)) with (Z_to_bv 64 0x418688) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp + 64); (A, A + 112)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (AH & ACE & AHI & AP & _). unfold AAPP_HI in AHI. unfold AIMG_TOP in AH.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. unfold ALOWSH_LO, AHI_LO in NSA.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp + 64); (A, A + 112)]) by nsw_tac.
    unfold bio_cells, bio_hdr1, wz, A_mem_buf_method in BA.
    cbn [firstn bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    pose proof NM as MT. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT. norm_addr MT.
    assert (IN : In (0x5ae5a0, 112, 112) aglobals) by in_nth.
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt.
    assert (ACCmt : accessible m 0x5ae5a0 112) by (eapply addressable_accessible; [exact ADmt| lia| lia| unfold AAPP_HI; lia]).
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. ubal_by AAL. step. if_lit.
    zstep. zstep. zstep. ck8_check ACC (A + 44). step. zstep. st1.
    zstep. zstep. reacc ACC MU NSW. ck8_check ACC0 (A + 40). clear ACC0. st1.
    zstep. zstep. zstep. reacc ACC MU NSW. ck8_check ACC0 (A + 56). clear ACC0. step. zstep. st1.
    zstep. zstep. reacc ACC MU NSW. ck8_check ACC0 (A + 48). clear ACC0. st1. rewrite sx32_lit by lia. step. zstep. zstep. st1.
    zstep. zstep. reacc ACC MU NSW. ck8_check ACC0 (A + 64). clear ACC0. st1.
    step. step. do 6 st1. step. step. release_frame FRM ST (bv_unsigned sp).
    step. if_lit.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCmt1 : accessible mx 0x5ae5a0 112) by (eapply accessible_across2; [exact ACCmt| exact MU| exact NSW]) end.
    ck8_check_lit ACCmt1 (0x5ae5a0 + 72). st1. unfold P_mem_new. step. if_true.
    step. do 7 st1. step. step. release_frame FRX ST (bv_unsigned sp + 64).
    replace (ret_pc (Z_to_bv 64 4288740)) with (Z_to_bv 64 4288740) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    finish. all: unfold bio_cells, bio_hdr2, wz, A_mem_buf_method;
    cbn [firstn bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg8 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A BB BM RP buf len : Z),
      aapp A BIO_SIZE -> aapp BB BIOBUFMEM_SIZE -> aapp BM BUFMEM_SIZE -> A mod 16 = 0 -> BB mod 16 = 0 -> BM mod 16 = 0 -> 0 <= RP < 2^64 -> 0 <= buf < 2^64 -> 0 <= len < 2^64 ->
      rw_cells asegs m A (firstn 18 (bio_cells (bio_hdr2 BB))) ->
      rw_cells asegs m BB [C8 (wz BM); C8 (wz RP)] -> rw_cells asegs m BM (buf_cells buf_zero) ->
      accessible m A BIO_SIZE -> accessible m BB BIOBUFMEM_SIZE -> accessible m BM BUFMEM_SIZE ->
      (A + BIO_SIZE <= BM \/ BM + BUFMEM_SIZE <= A) -> (BB + BIOBUFMEM_SIZE <= BM \/ BM + BUFMEM_SIZE <= BB) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ANMB_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 RP) (Z_to_bv 64 BM) (Z_to_bv 64 32)
                       (Z_to_bv 64 0) a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 buf) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AASAN_MEMCPY) fc None m1 (seg_rom asegs)
          /\ munch [(BM, BM + BUFMEM_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 BM (buf_cells (mkBUF len buf len 0)))
        (MS (mkR (Z_to_bv 64 ANMB_RET) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 len) (Z_to_bv 64 buf) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ANMB_RET) fc None m (seg_rom asegs)).
  Proof.
    intros until len. intros AAP BBAP BMAP AAL BBAL BMAL RPR BUFR LENR BA BBC BMC ACCa ACCbb ACCbm AP2 AP4 MI. acb.
    unfold ANMB_RET, ANMB_RA2, AASAN_MEMCPY, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *. unfold wz in BBC.
    unfold buf_cells, buf_zero, wz in BMC. cbn [bm_len bm_data bm_max bm_flags] in BMC.
    unfold bio_cells, bio_hdr2, wz, A_mem_buf_method in BA. cbn [firstn bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    pose proof (munch_refl [(BM, BM + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & _ & AHIa & AP & _). pose proof (aapp_bounds _ _ BBAP ltac:(lia)) as (_ & _ & AHIbb & BBP & _).
    pose proof (aapp_bounds _ _ BMAP ltac:(lia)) as (_ & _ & AHIbm & BMP & _). unfold AAPP_HI in AHIa, AHIbb, AHIbm.
    pose proof (aapp_not_shadowland _ _ BMAP) as NSbm. unfold ALOWSH_LO, AHI_LO in NSbm.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(BM, BM + 32)]) by nsw_tac.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step.
    idtac. step. ubal_any. step. if_lit. step. zstep. zstep. ck8_check ACCa (A + 64). st1.
    step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. ck8_check ACCbb BB. st1.
    step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_check ACCbm (BM + 8). st1.
    zstep. zstep. reacc ACCbm MU NSW. ck8_check ACC (BM). clear ACC. st1.
    zstep. zstep. zstep. reacc ACCbm MU NSW. ck8_check ACC (BM + 16). clear ACC. st1.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => assert (ACCbb1 : accessible mx BB 16) by (eapply accessible_across2; [exact ACCbb| exact MU| exact NSW]) end.
    ck8_check ACCbb1 (BB + 8). st1. step. step. step.
    finish. all: unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma anm_seg9 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (s4o s3o s2o s1o s0o rao : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A BB RP buf len lo : Z),
      aapp A BIO_SIZE -> rw_cells asegs m A (firstn 18 (bio_cells (bio_hdr2 BB))) -> accessible m A BIO_SIZE ->
      rw_cells asegs m (bv_unsigned sp + -48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
      stk asegs m lo (bv_unsigned sp + -48) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists a1' m1,
          ms' = MS (mkR rao sp gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 A) a1' a2 a3 a4 a5 a6 a7 s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc rao) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp); (A, A + 112)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 A (firstn 18 (bio_cells (bio_hdr3 BB))))
        (MS (mkR (Z_to_bv 64 ANMB_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 RP) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 len) (Z_to_bv 64 buf) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ANMB_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AAP BA ACCa FR ST CEIL LO MI. acb. unfold ANMB_RA2, BIO_SIZE in *.
    replace (ret_pc (Z_to_bv 64 0x4171a0)) with (Z_to_bv 64 0x4171a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold bio_cells, bio_hdr2, wz, A_mem_buf_method in BA. cbn [firstn bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + 112)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (_ & ACE & AHIa & AP & _). unfold AAPP_HI in AHIa.
    pose proof (aapp_not_shadowland _ _ AAP) as NSa. unfold ALOWSH_LO, AHI_LO in NSa.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (A, A + 112)]) by nsw_tac.
    zstep. zstep. zstep. ck8_check ACCa (A + 48). st1. rewrite sx32_lit by lia. zstep. zstep. st1.
    zstep. zstep. reacc ACCa MU NSW. ck8_check ACC (A + 56). clear ACC. st1.
    step. step. do 6 st1. step. step. release_frame FR ST (bv_unsigned sp).
    finish. all: unfold bio_cells, bio_hdr3, wz, A_mem_buf_method;
    cbn [firstn bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; assumption.
  Qed.
End S.
