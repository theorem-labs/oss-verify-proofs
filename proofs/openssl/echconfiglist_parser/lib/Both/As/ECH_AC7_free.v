(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsAtomics AsStack0 AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj InNth.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma bio_flags_byte1_raw : forall m a (v0 v1 v2 v3 v4 i sh rt nf z0 ptr nx pv rf z1 nr nw e1 e2 : word) f,
  rw_cells asegs m a [C8 v0; C8 v1; C8 v2; C8 v3; C8 v4; C4 i; C4 sh; C4 (Z_to_bv 64 f); C4 rt; C4 nf; C4 z0; C8 ptr; C8 nx; C8 pv; C4 rf; C4 z1; C8 nr; C8 nw; C8 e1; C8 e2] ->
  0 <= f < 2^64 ->
  ov_read_bytes asegs m (wa (a + 49)) 1 = Some [b8 ((f / 256) mod 256)].
Proof.
  intros until f. intros [[_ HB] _] POS. replace (a + 49) with (a + Z.of_nat 49) by lia.
  rewrite (bytes_at_ov_read asegs m a _ 49 1 HB) by (cbn; lia).
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

Lemma bytes_eq_of_unsigned7 : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] E; cbn in E; try discriminate; [reflexivity|].
  injection E as E1 E2. f_equal; [apply bv_eq; exact E1| apply IH; exact E2].
Qed.

(* [comment removed for export] *)
Lemma le4_wz_of_bytes : forall bs, length bs = 4%nat -> le4 (wz (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le4, wz. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
  change (2 ^ (8 * Z.of_nat 4)) with (2^32) in B. rewrite unsigned_lit by lia. rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.
Lemma rw_cells_CB4_C4 : forall segs m A pre bs post,
  rw_cells segs m A (pre ++ CB 4 bs :: post) -> rw_cells segs m A (pre ++ C4 (wz (bytes_le_to_Z bs)) :: post).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  pose proof Hwf as W0. apply cells_wf_app in W0. destruct W0 as [_ [L _]]. cbn in L.
  split; [split|].
  - apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [W1 [_ W3]]. split; [exact W1|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le4_wz_of_bytes by exact L. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac reacc ACC0 MU NSW :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ACC0 with accessible _ ?x ?n =>
        let T := fresh "ACC" in
        assert (T : accessible mx x n) by (eapply accessible_across2; [exact ACC0| exact MU| exact NSW])
      end end.

  Definition AFI_RA1 : Z := R_BIO_free_int_destroy.          (* [comment removed for export] *)
  Definition AFI_RA2 : Z := R_BIO_free_int_CRYPTO_free_ex_data. (* [comment removed for export] *)
  Definition AFI_RA3 : Z := R_BIO_free_int_CRYPTO_free.      (* [comment removed for export] *)
  Definition AMF_RA1 : Z := R_mem_free_mem_buf_free.          (* [comment removed for export] *)
  Definition AMF_RA2 : Z := R_mem_free_CRYPTO_free.           (* [comment removed for export] *)
  Definition AMF_RA3 : Z := R_mem_free_CRYPTO_free_2.         (* [comment removed for export] *)
  Definition AMBF_RA : Z := R_mem_buf_free_BUF_MEM_free.      (* [comment removed for export] *)
  Definition ABF_RET : Z := R_BIO_free_BIO_free_int.          (* [comment removed for export] *)
  Definition ABIO_FILE_ : Z := 0x71560.    (* [comment removed for export] *)
  Definition AMEM_FILE_ : Z := 0xbfff0.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition bio_unref (B : biorep) : biorep :=
    mkBIO (bio_method B) (bio_init B) (bio_shutdown B) (bio_flags B) (bio_retry B) (bio_numf B) (bio_ptr B) (bio_next B) (bio_prev B) 0 (bio_nread B) (bio_nwrite B).

  (* [comment removed for export] *)
  Lemma afi_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a rbp lo : Z) (R : membio) (jv : word),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 rbp ->
      aapp a BIO_SIZE -> aapp (mb_bb R) BIOBUFMEM_SIZE -> aapp (mb_bm R) BUFMEM_SIZE -> a mod 16 = 0 -> mb_bb R mod 16 = 0 -> mb_bm R mod 16 = 0 ->
      MEMBIO_apart a R ->
      0 <= mb_pos R <= mb_len R -> 0 <= mb_len R < 2^31 -> 0 < mb_buf R -> mb_buf R + mb_len R <= aceil ->
      0 <= mb_flags R < 2^31 -> Z.land (mb_flags R) BIO_FLAGS_MEM_RDONLY = BIO_FLAGS_MEM_RDONLY -> 0 <= mb_nread R < 2^63 -> 0 <= mb_next R < 2^64 -> 0 <= mb_prev R < 2^64 ->
      mb_numf R = 0 -> 0 <= mb_rp R < 2^64 ->
      rw_cells asegs m a (bio_cells (membio_bio R)) ->
      rw_cells asegs m (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))] ->
      rw_cells asegs m (mb_bm R) (buf_cells (mkBUF (mb_len R - mb_pos R) (mb_buf R + mb_pos R) (mb_len R - mb_pos R) 0)) ->
      rw_cells asegs m rbp [C4 jv] -> bv_unsigned sp <= rbp -> rbp + 8 <= AAPP_HI -> rbp mod 4 = 0 ->
      accessible m a BIO_SIZE -> accessible m (mb_bb R) BIOBUFMEM_SIZE -> accessible m (mb_bm R) BUFMEM_SIZE -> accessible m rbp 8 ->
      ACONST m -> METH_mem m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 96 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j1 (t1x : word),
          ms' = MS (mkR (Z_to_bv 64 AMF_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1x t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 (mb_bb R))
                       (Z_to_bv 64 (mb_bm R)) (Z_to_bv 64 (mb_bm R + 8)) (Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) a5 a6 a7
                       (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BUF_MEM_free) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -96, bv_unsigned sp); (a + 88, a + 92); (rbp, rbp + 4); (mb_bm R + 8, mb_bm R + 16)] m m1
          /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -80)
          /\ rw_cells asegs m1 a (bio_cells (bio_unref (membio_bio R)))
          /\ rw_cells asegs m1 (mb_bb R) [C8 (wz (mb_bm R)); C8 (wz (mb_rp R))]
          /\ rw_cells asegs m1 (mb_bm R) (buf_cells (mkBUF (mb_len R - mb_pos R) 0 (mb_len R - mb_pos R) 0))
          /\ rw_cells asegs m1 rbp [C4 (wz 0)]
          /\ rw_cells asegs m1 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
          /\ rw_cells asegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free_int) fc None m (seg_rom asegs)).
  Proof.
    intros until jv. intros A0 A1 AAP BBAP BMAP AAL BBAL BMAL APART POSR LENR BUFP BUFH FLR RDO NRD NXT PRV NUMF RPR BA BB BM RBC SPRB RBH RBAL ACCA ACCB ACCM ACCR AC METH ST CEIL LO MI.
    subst a0 a1. acb.
    pose proof (aapp_bounds _ _ AAP ltac:(unfold BIO_SIZE; lia)) as (AH & ACE & AHI & AP & _). pose proof (aapp_bounds _ _ BBAP ltac:(unfold BIOBUFMEM_SIZE; lia)) as (BBH & BBCE & BBHI & BBP & _).
    pose proof (aapp_bounds _ _ BMAP ltac:(unfold BUFMEM_SIZE; lia)) as (BMH & BMCE & BMHI & BMP & _).
    unfold AIMG_TOP in AH, BBH, BMH. unfold AAPP_HI in AHI, BBHI, BMHI, RBH.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. pose proof (aapp_not_shadowland _ _ BBAP) as NSB. pose proof (aapp_not_shadowland _ _ BMAP) as NSM.
    unfold ALOWSH_LO, AHI_LO in NSA, NSB, NSM.
    destruct APART as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6).
    unfold P_BIO_free_int, P_BUF_MEM_free, P_mem_free, AMBF_RA, AFI_RA1, AMF_RA1, R_mem_buf_free_BUF_MEM_free, R_BIO_free_int_destroy, R_mem_free_mem_buf_free,
      O_BIO_REFS, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY in *.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, membio_bio, wz in BA. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    unfold A_mem_buf_method in BA. rewrite NUMF in BA. unfold wz in BB. unfold buf_cells, wz in BM. cbn [bm_len bm_data bm_max bm_flags] in BM.
    pose proof METH as MT. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in MT. norm_addr MT.
    assert (IN : In (0x5ae5a0, 112, 112) aglobals) by in_nth.
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt.
    assert (ACCmt : accessible m 0x5ae5a0 112) by (eapply addressable_accessible; [exact ADmt| lia| lia| unfold AAPP_HI; lia]).
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (a + 88, a + 92); (rbp, rbp + 4); (mb_bm R + 8, mb_bm R + 16)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bv_unsigned sp + -96, bv_unsigned sp); (a + 88, a + 92); (rbp, rbp + 4); (mb_bm R + 8, mb_bm R + 16)]) by nsw_tac.
    hide NSA. hide NSB. hide NSM.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. ubal_any. step. if_lit. step. st1. st1.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 88). clear ACC.
    (* [comment removed for export] *)
    assert (AL88 : (a + 88) mod 4 = 0) by (clear - AAL; Z.div_mod_to_equations; lia). assert (R88 : 0 <= a + 88 < 2^64) by lia.
    step. astep. rewrite (unsigned_lit 1) in BA by lia. change (1 + 4294967295) with 4294967296 in BA.
    (* [comment removed for export] *)
    step. try change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    try change (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 1) + -1))) with (Z_to_bv 64 0).
    step. if_lit. step. ubal_by RBAL. step. if_lit. zstep. zstep. reacc ACCR MU NSW. ck8_check ACC rbp. clear ACC.
    st1. step. if_lit. step. reacc ACCR MU NSW. ck8_check ACC rbp. clear ACC. st1. step. step. if_lit.
    (* [comment removed for export] *)
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 16). clear ACC. st1. step. if_lit.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 24). clear ACC. st1. step. if_lit.
    (* [comment removed for export] *)
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 8). clear ACC. st1. step. if_lit.
    step. ubal_any. step. if_lit. zstep. zstep. zstep. reacc ACCmt MU NSW. ck8_check_lit ACC (5957024 + 80). clear ACC. st1. unfold P_mem_free. step. if_lit. step. step.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. step. do 4 st1. step. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    step. ubal_any. step. if_lit. step. st1. st1. zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 64). clear ACC. st1. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    step. do 2 st1. do 2 step. ubal_any. step. if_lit. step. st1. st1.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 44). clear ACC. st1. idtac. step. if_lit.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 40). clear ACC. st1. step. if_lit.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 64). clear ACC. st1. step. if_cases K3; zify_cond K3; [kill K3|]. clear K3.
    (* [comment removed for export] *)
    step. ubal_by BBAL. step. if_lit. zstep. zstep. reacc ACCB MU NSW. ck8_check ACC (mb_bb R). clear ACC.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_load ACC (a + 48). clear ACC. st1. step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (RD1 : ov_read_bytes asegs mx (wa (a + 49)) 1 = Some [b8 ((mb_flags R / 256) mod 256)]) by (eapply bio_flags_byte1_raw; [exact BA| lia]) end.
    step. clear RD1. zstep. cbn beta.
    assert (E2 : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (b8 ((mb_flags R / 256) mod 256))))) 2 = 2).
    { unfold b8. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2^64).
      pose proof (Z.mod_pos_bound (mb_flags R / 256) 256 ltac:(lia)) as MB.
      rewrite (Z.mod_small _ (2^64)) by (pose proof (Z.mod_pos_bound ((mb_flags R / 256) mod 256) 256 ltac:(lia)); lia).
      rewrite Z.mod_mod by lia. apply rdonly_byte1; lia. }
    rewrite E2. clear E2. step. if_lit.
    (* [comment removed for export] *)
    step. ub_dead. step. ubal_by BMAL. step. if_lit. zstep. zstep. zstep. reacc ACCM MU NSW. ck8_check ACC (mb_bm R + 8). clear ACC. st1.
    st1. st1. step. release_frame FR1 ST (bv_unsigned sp + -80). step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (BA' : rw_cells asegs mx a (bio_cells (bio_unref (membio_bio R))))
        by (eapply arw_cells_recut; [exact BA| cbn; repeat split| unfold bio_cells, bio_unref, membio_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite];
              unfold A_mem_buf_method; rewrite NUMF; cbn [cells_bytes cbytes app];
              repeat (apply (f_equal2 (@app byte)); [first [reflexivity| apply bytes_eq_of_unsigned7; vm_compute; reflexivity]|]); reflexivity]) end.
    clear BA. finish; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma afi_seg2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (bb bm rp lo : Z),
      aapp bb BIOBUFMEM_SIZE -> 0 <= rp < 2^64 ->
      rw_cells asegs m bb [C8 (wz bm); C8 (wz rp)] -> accessible m bb BIOBUFMEM_SIZE ->
      bb mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp + -80) -> aceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AMF_RA2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 bb)
                       (Z_to_bv 64 rp) (Z_to_bv 64 AMEM_FILE_) (Z_to_bv 64 153) a3 a4 a5 a6 a7 (Z_to_bv 64 AMEM_FILE_) (Z_to_bv 64 2147450880)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AMF_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 bb)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMF_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros BBAP RPR BB ACCB BBAL ST CEIL LO MI. acb.
    unfold AMF_RA1, AMF_RA2, AMEM_FILE_, R_mem_free_mem_buf_free, R_mem_free_CRYPTO_free, P_CRYPTO_free, BIOBUFMEM_SIZE in *.
    replace (ret_pc (Z_to_bv 64 4292980)) with (Z_to_bv 64 4292980) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (aapp_bounds _ _ BBAP ltac:(lia)) as (BBH & BBCE & BBHI & BBP & _). unfold AIMG_TOP in BBH. unfold AAPP_HI in BBHI.
    unfold wz in BB.
    step. ub_dead. step. ubal_by BBAL. step. if_lit.
    zstep. zstep. zstep. ck8_check ACCB (bb + 8). st1. step. step. step. step. step. step.
    apply evt_done; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afi_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AMF_RA3) sp gp tp t0 t1 t2 s0 s1 s1 s2 (Z_to_bv 64 154) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AMF_RA2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMF_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros. unfold AMF_RA2, AMF_RA3, R_mem_free_CRYPTO_free, R_mem_free_CRYPTO_free_2, P_CRYPTO_free.
    replace (ret_pc (Z_to_bv 64 0x4181b0)) with (Z_to_bv 64 0x4181b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. apply evt_done; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afi_seg4 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z),
      0 <= a -> a + 128 <= 2^64 ->
      rw_cells asegs m (bv_unsigned sp + -80) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)] ->
      stk asegs m lo (bv_unsigned sp + -80) -> aceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFI_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 a) (Z_to_bv 64 (a + O_BIO_EXDATA)) a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free_ex_data) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AMF_RA3) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMF_RA3)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AP AH FR ST CEIL LO MI. acb.
    unfold AMF_RA3, AFI_RA1, AFI_RA2, R_mem_free_CRYPTO_free_2, R_BIO_free_int_destroy, R_BIO_free_int_CRYPTO_free_ex_data, P_CRYPTO_free_ex_data, CRYPTO_EX_INDEX_BIO, O_BIO_EXDATA in *.
    replace (ret_pc (Z_to_bv 64 0x4181c4)) with (Z_to_bv 64 0x4181c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    step. do 4 st1. step. step. release_frame FR ST (bv_unsigned sp + -48).
    replace (ret_pc (Z_to_bv 64 2322360)) with (Z_to_bv 64 2322360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. step. step. step. apply evt_done; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afi_seg5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AFI_RA3) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 ABIO_FILE_) (Z_to_bv 64 145) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AFI_RA2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFI_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros. unfold AFI_RA2, AFI_RA3, ABIO_FILE_, R_BIO_free_int_CRYPTO_free_ex_data, R_BIO_free_int_CRYPTO_free, P_CRYPTO_free.
    replace (ret_pc (Z_to_bv 64 0x236fc8)) with (Z_to_bv 64 0x236fc8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. apply evt_done; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma afi_seg6 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0x s1x s3x : word) (s3o s2o s1o s0o rao : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (j : list byte),
      rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
      stk asegs m lo (bv_unsigned sp + -48) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR rao sp gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc rao) fc None m (seg_rom asegs)
          /\ stk asegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 AFI_RA3) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AFI_RA3)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros FR ST CEIL LO MI. acb. unfold AFI_RA3, R_BIO_free_int_CRYPTO_free.
    replace (ret_pc (Z_to_bv 64 0x236fdc)) with (Z_to_bv 64 0x236fdc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    step. step. do 5 st1. step. step. release_frame FR ST (bv_unsigned sp).
    apply evt_done. split; [reflexivity| assumption].
  Qed.

  (* [comment removed for export] *)
  Lemma afr_segA :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j0 (jv : word),
          ms' = MS (mkR (Z_to_bv 64 ABF_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 a0 (Z_to_bv 64 (bv_unsigned sp + -20)) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free_int) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) [CB 12 j0] /\ rw_cells asegs m1 (bv_unsigned sp + -20) [C4 jv]
          /\ rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. acb. unfold P_BIO_free, P_BIO_free_int, ABF_RET, R_BIO_free_BIO_free_int.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST. step. step. step. step. zstep. step.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?mx _ [CB 16 ?jj; C8 _; C8 _] =>
      change ([CB 16 jj; C8 s0; C8 ra]) with ([CB 16 jj] ++ [C8 s0; C8 ra]) in FR end.
    destruct (proj1 (rw_cells_app asegs _ _ _ _) FR) as [FRj FRhi]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRhi.
    lazymatch type of FRj with rw_cells _ ?mx _ [CB 16 ?jj] =>
      assert (FRj' : rw_cells asegs mx (bv_unsigned sp + -32) ([CB 12 (firstn 12 jj)] ++ CB 4 (skipn 12 jj) :: []))
        by (eapply arw_cells_recut; [exact FRj| cbn; pose proof (proj1 (proj1 FRj)) as W; cbn in W; rewrite length_firstn, length_skipn; repeat split; lia
                                     | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; apply firstn_skipn]) end.
    apply rw_cells_CB4_C4 in FRj'. destruct (proj1 (rw_cells_app asegs _ _ [CB 12 _] [C4 _]) FRj') as [FR12 FR4].
    lazymatch type of FR4 with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -20) in FR4 by (cbn; lia) end.
    lazymatch type of FRhi with rw_cells _ _ ?adr _ => replace adr with (bv_unsigned sp + -16) in FRhi by (cbn; lia) end.
    finish; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma afr_segZ :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0o rao : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells asegs m (bv_unsigned sp + -16) [C8 s0o; C8 rao] ->
      stk asegs m lo (bv_unsigned sp + -32) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR rao sp gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc rao) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ABF_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ABF_RET)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI. acb. unfold ABF_RET, R_BIO_free_BIO_free_int.
    replace (ret_pc (Z_to_bv 64 0x236e68)) with (Z_to_bv 64 0x236e68) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    st1. st1. step. step. apply evt_done; reflexivity.
  Qed.
End S.
