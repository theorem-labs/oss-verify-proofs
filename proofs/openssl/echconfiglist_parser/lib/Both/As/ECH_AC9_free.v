(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_AC7_free ECH_AC9_new.
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
  Local Ltac if_lit :=
    match goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        tryif (match c with context [?x] => is_var x end) then fail 1 "if_lit: open condition" else
        let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
    end.
  Local Ltac reacc ACC0 MU NSW :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ACC0 with accessible _ ?x ?n =>
        let T := fresh "ACC" in
        assert (T : accessible mx x n) by (eapply accessible_across2; [exact ACC0| exact MU| exact NSW])
      end end.
  Local Ltac ubal_any :=
    lazymatch goal with
    | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
        lazymatch R with
        | context [Z.land ?x 7] =>
            first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                  | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                  | idtac ]
        | context [Z.land ?x 3] =>
            first [ match goal with H : _ mod 16 = 0 |- _ => ubal_by H end
                  | match goal with H : _ mod 8 = 0 |- _ => ubal_by H end
                  | match goal with H : _ mod 4 = 0 |- _ => ubal_by H end
                  | idtac ]
        | _ => idtac
        end
    | _ => idtac
    end.

  Definition ABF_RA1 : Z := R_b64_free_BIO_get_data.            (* [comment removed for export] *)
  Definition ABF_RA2 : Z := R_b64_free_CRYPTO_free.             (* [comment removed for export] *)
  Definition ABF_RA3 : Z := R_b64_free_EVP_ENCODE_CTX_free - 8.   (* [comment removed for export] *)
  Definition ABF_RA4 : Z := R_b64_free_EVP_ENCODE_CTX_free.      (* [comment removed for export] *)
  Definition ABF_RA5 : Z := R_b64_free_CRYPTO_free_2.           (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma abf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a rbp lo elen : Z) (R : b64frep) (hdr junk : list byte) (jv : word),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 rbp ->
      aapp a BIO_SIZE -> aapp (bf_ctx R) B64CTX_SIZE -> a mod 16 = 0 -> bf_ctx R mod 16 = 0 ->
      (a + BIO_SIZE <= bf_ctx R \/ bf_ctx R + B64CTX_SIZE <= a) ->
      0 <= bf_flags R < 2^31 -> 0 <= bf_retry R < 2^32 -> 0 <= bf_nread R < 2^63 -> 0 <= bf_next R < 2^64 -> 0 <= bf_prev R < 2^64 ->
      0 < bf_ctx R -> 0 <= bf_enc R < 2^64 -> 0 <= elen < 2^64 -> length hdr = 32%nat -> length junk = 2528%nat ->
      rw_cells asegs m a (bio_cells (b64f_bio R)) ->
      rw_cells asegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen) ->
      rw_cells asegs m rbp [C4 jv] -> bv_unsigned sp <= rbp -> rbp + 8 <= AAPP_HI -> rbp mod 4 = 0 ->
      accessible m a BIO_SIZE -> accessible m (bf_ctx R) B64CTX_SIZE -> accessible m rbp 8 ->
      ACONST m -> METH_b64 m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j1 j2,
          ms' = MS (mkR (Z_to_bv 64 ABF_RA2) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 a)
                       (Z_to_bv 64 0) (Z_to_bv 64 AB64_FILE) (Z_to_bv 64 103) (Z_to_bv 64 0) a4 a5 a6 a7
                       (Z_to_bv 64 (bf_ctx R)) (Z_to_bv 64 (bf_ctx R + O_B64_ENCBUF)) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (bf_ctx R + O_B64_ENCBUF) 3 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -128, bv_unsigned sp); (a + 88, a + 92); (rbp, rbp + 4)] m m1
          /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -112)
          /\ rw_cells asegs m1 a (bio_cells (bio_unref (b64f_bio R)))
          /\ rw_cells asegs m1 rbp [C4 (wz 0)]
          /\ rw_cells asegs m1 (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
          /\ rw_cells asegs m1 (bv_unsigned sp + -112) [CB 8 j2; C8 s5; C8 s4; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_free_int) fc None m (seg_rom asegs)).
  Proof.
    intros until jv. intros A0 A1 AAP CAP AAL CAL DJ FLR RTR NRD NXT PRV CP ENR ELR LH LJ BA BC RBC SPRB RBH RBAL ACCA ACCC ACCR AC METH ST CEIL LO MI.
    subst a0 a1. acb.
    pose proof (aapp_bounds _ _ AAP ltac:(unfold BIO_SIZE; lia)) as (AH & ACE & AHI & AP & _). pose proof (aapp_bounds _ _ CAP ltac:(unfold B64CTX_SIZE; lia)) as (CH0 & CCE & CHI & _ & _).
    unfold AIMG_TOP in AH, CH0. unfold AAPP_HI in AHI, CHI, RBH.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. pose proof (aapp_not_shadowland _ _ CAP) as NSC. unfold ALOWSH_LO, AHI_LO in NSA, NSC.
    unfold P_BIO_free_int, P_CRYPTO_free, ABF_RA2, AFI_RA1, R_b64_free_CRYPTO_free, R_BIO_free_int_destroy, AB64_FILE, O_B64_ENCBUF, SHB,
      O_BIO_REFS, BIO_SIZE, B64CTX_SIZE in *.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold bio_cells, b64f_bio, wz in BA. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    unfold A_b64_method in BA. unfold b64ctx_used_cells, wz in BC.
    pose proof METH as MT. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in MT. norm_addr MT.
    assert (IN : In (0x5e75e0, 112, 112) aglobals) by in_nth.
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt.
    assert (ACCmt : accessible m 0x5e75e0 112) by (eapply addressable_accessible; [exact ADmt| lia| lia| unfold AAPP_HI; lia]).
    pose proof (ACONST_shbase _ AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (a + 88, a + 92); (rbp, rbp + 4)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bv_unsigned sp + -128, bv_unsigned sp); (a + 88, a + 92); (rbp, rbp + 4)]) by nsw_tac.
    hide NSA. hide NSC.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. ubal_any. step. if_lit. step. st1. st1.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 88). clear ACC.
    (* [comment removed for export] *)
    assert (AL88 : (a + 88) mod 4 = 0) by (clear - AAL; Z.div_mod_to_equations; lia). assert (R88 : 0 <= a + 88 < 2^64) by lia.
    step. astep. rewrite (unsigned_lit 1) in BA by lia. lazymatch type of BA with context [(1 + ?k)%Z] => let v := eval vm_compute in (1 + k) in change (1 + k) with v in BA end.
    (* [comment removed for export] *)
    do 2 st1. if_lit. do 2 st1. ubal_any. if_lit. do 2 st1. reacc ACCR MU NSW. ck8_check ACC rbp. clear ACC.
    do 2 st1. if_lit. st1. reacc ACCR MU NSW. ck8_check ACC rbp. clear ACC.
    do 3 st1. if_lit.
    (* [comment removed for export] *)
    step. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 16). clear ACC. st1. step. if_lit.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 24). clear ACC. st1. step. if_lit.
    (* [comment removed for export] *)
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 8). clear ACC. st1. step. if_lit.
    step. ubal_any. step. if_lit. zstep. zstep. zstep. reacc ACCmt MU NSW. ck8_check_lit ACC (6190560 + 80). clear ACC. st1. unfold P_b64_free. step. if_lit. step. step.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. step. do 7 st1. step. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    step. step. st1. idtac. do 2 step. step. unfold P_BIO_get_data. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. step. st1. st1. step. step. ub_dead. step. ubal_any. step. if_lit. step. st1. st1.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 64). clear ACC. st1. st1. st1. step. release_frame FR1 ST (bv_unsigned sp + -112). step.
    replace (ret_pc (Z_to_bv 64 R_b64_free_BIO_get_data)) with (Z_to_bv 64 R_b64_free_BIO_get_data) by (symmetry; apply ret_pc_even; [unfold R_b64_free_BIO_get_data; lia| reflexivity]).
    unfold R_b64_free_BIO_get_data.
    (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    do 3 st1. ubal_any. if_lit. do 4 st1. replace (bf_ctx R + 2047 + 521) with (bf_ctx R + 2568) by lia.
    reacc ACCC MU NSW. ck8_check ACC (bf_ctx R + 2568). clear ACC. st1.
    step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (BA' : rw_cells asegs mx a (bio_cells (bio_unref (b64f_bio R))))
        by (eapply arw_cells_recut; [exact BA| cbn; repeat split| unfold bio_cells, bio_unref, b64f_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite];
              unfold A_b64_method; cbn [cells_bytes cbytes app];
              repeat (apply (f_equal2 (@app byte)); [first [reflexivity| apply bytes_eq_of_unsigned7; vm_compute; reflexivity]|]); reflexivity]) end.
    clear BA. finish; try eassumption. all: try reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma abf_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (C E elen : Z) (hdr junk : list byte),
      0 < C -> C mod 16 = 0 -> aapp C B64CTX_SIZE -> 0 <= E < 2^64 -> 0 <= elen < 2^64 ->
      rw_cells asegs m C (b64ctx_used_cells E hdr junk elen) -> accessible m C B64CTX_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ABF_RA2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 C) (Z_to_bv 64 (C + O_B64_ENCBUF)) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (C + O_B64_ENCBUF) 3 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ABF_RA3) fc None m1 (seg_rom asegs)
          /\ munch [(C + O_B64_ENCBUF, C + B64CTX_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 C (b64ctx_used_cells E hdr junk 0))
        (MS (mkR (Z_to_bv 64 ABF_RA2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 C) (Z_to_bv 64 (C + O_B64_ENCBUF)) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (C + O_B64_ENCBUF) 3 + SHB)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ABF_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until junk. intros CP CAL CAP ER ELR BC ACCC MI. acb.
    replace (ret_pc (Z_to_bv 64 ABF_RA2)) with (Z_to_bv 64 ABF_RA2) by (symmetry; apply ret_pc_even; [unfold ABF_RA2, R_b64_free_CRYPTO_free; lia| reflexivity]).
    unfold ABF_RA2, ABF_RA3, R_b64_free_CRYPTO_free, R_b64_free_EVP_ENCODE_CTX_free, O_B64_ENCBUF, B64CTX_SIZE, SHB in *.
    pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (CH0 & CCE & CHI & _ & _). unfold AAPP_HI in CHI. unfold AIMG_TOP in CH0.
    pose proof (aapp_not_shadowland _ _ CAP) as NSC. unfold ALOWSH_LO, AHI_LO in NSC.
    unfold b64ctx_used_cells, wz in BC.
    pose proof (munch_refl [(C + 2568, C + 2584)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(C + 2568, C + 2584)]) by nsw_tac.
    ck8_check ACCC (C + 2568). do 4 st1. reacc ACCC MU NSW. ck8_check ACC (C + 2576). clear ACC. do 4 st1.
    reacc ACCC MU NSW. ck8_check ACC (C + 32). clear ACC. st1.
    finish. all: unfold b64ctx_used_cells, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma abf_seg3 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ABF_RA4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_ENCODE_CTX_free) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ABF_RA3) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold ABF_RA3, ABF_RA4, R_b64_free_EVP_ENCODE_CTX_free, P_EVP_ENCODE_CTX_free.
    step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma abf_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (C : Z),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ABF_RA5) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 AB64_FILE) (Z_to_bv 64 107) a3 a4 a5 a6 a7
                       (Z_to_bv 64 C) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ABF_RA4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 C) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ABF_RA4)) fc None m (seg_rom asegs)).
  Proof.
    intros until C. intros MI. unfold ABF_RA4, ABF_RA5, R_b64_free_EVP_ENCODE_CTX_free, R_b64_free_CRYPTO_free_2, P_CRYPTO_free, AB64_FILE in *.
    replace (ret_pc (Z_to_bv 64 0x5576d0)) with (Z_to_bv 64 0x5576d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma abf_seg5 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s3o s2o : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (B : biorep) (j2 : list byte) (s5o s4o : word),
      aapp a BIO_SIZE -> rw_cells asegs m a (bio_cells B) -> accessible m a BIO_SIZE -> ACONST m ->
      rw_cells asegs m (bv_unsigned sp + -112) [CB 8 j2; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 (Z_to_bv 64 a); C8 sp; C8 (Z_to_bv 64 AFI_RA1)] ->
      stk asegs m lo (bv_unsigned sp + -112) -> aceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m -> a mod 16 = 0 ->
      evt asegs (fun ms' => exists m1 (a3x : word),
          ms' = MS (mkR (Z_to_bv 64 AFI_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 a) (Z_to_bv 64 (a + O_BIO_EXDATA)) a3x a4 a5 a6 a7 s2o s3o s4o s5o s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free_ex_data) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -128, bv_unsigned sp + -112); (a + O_BIO_INIT, a + O_BIO_INIT + 4); (a + O_BIO_PTR, a + O_BIO_PTR + 8)] m m1
          /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells asegs m1 a (bio_cells (bio_with_init (bio_with_ptr B 0) 0)))
        (MS (mkR (Z_to_bv 64 ABF_RA5) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 a)
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ABF_RA5)) fc None m (seg_rom asegs)).
  Proof.
    intros until s4o. intros AAP BA ACCA AC F2 ST CEIL LO MI. acb.
    unfold ABF_RA5, AFI_RA1, AFI_RA2, R_b64_free_CRYPTO_free_2, R_BIO_free_int_destroy, R_BIO_free_int_CRYPTO_free_ex_data, P_CRYPTO_free_ex_data,
      CRYPTO_EX_INDEX_BIO, O_BIO_EXDATA, O_BIO_INIT, O_BIO_PTR, BIO_SIZE, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x5576e8)) with (Z_to_bv 64 0x5576e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (AH & ACE & AHI & AP & _). unfold AAPP_HI in AHI. unfold AIMG_TOP in AH.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. unfold ALOWSH_LO, AHI_LO in NSA.
    destruct B as [bmth binit bshut bfl brt bnf bptr bnx bpv brf bnr bnwr].
    intros AAL.
    unfold bio_cells, wz in BA. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    pose proof (ACONST_shbase _ AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp + -112); (a + 40, a + 40 + 4); (a + 64, a + 64 + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bv_unsigned sp + -128, bv_unsigned sp + -112); (a + 40, a + 40 + 4); (a + 64, a + 64 + 8)]) by nsw_tac.
    (* [comment removed for export] *)
    step. step. step. unfold P_BIO_set_data. step.
    carve_frame 16%nat ST. step. st1. st1. step. step. ub_dead. step. ubal_any. step. if_lit. step. st1. st1.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 64). clear ACC. st1. st1. st1. step. release_frame FR ST (bv_unsigned sp + -112). step.
    replace (ret_pc (Z_to_bv 64 R_b64_free_BIO_set_data)) with (Z_to_bv 64 R_b64_free_BIO_set_data) by (symmetry; apply ret_pc_even; [unfold R_b64_free_BIO_set_data; lia| reflexivity]).
    unfold R_b64_free_BIO_set_data.
    (* [comment removed for export] *)
    step. step. step. unfold P_BIO_set_init. step.
    carve_frame 16%nat ST. step. st1. st1. step. step. ub_dead. step. ubal_any. step. if_lit. step. st1. st1.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (a + 40). clear ACC. st1. st1. st1. step. release_frame FR ST (bv_unsigned sp + -112). step.
    replace (ret_pc (Z_to_bv 64 R_b64_free_BIO_set_init)) with (Z_to_bv 64 R_b64_free_BIO_set_init) by (symmetry; apply ret_pc_even; [unfold R_b64_free_BIO_set_init; lia| reflexivity]).
    unfold R_b64_free_BIO_set_init.
    (* [comment removed for export] *)
    step. do 7 st1. step. release_frame F2 ST (bv_unsigned sp + -48). step.
    replace (ret_pc (Z_to_bv 64 2322360)) with (Z_to_bv 64 2322360) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    zstep. step. step. step.
    replace (a + 40 + 4) with (a + 44) in MU by lia. replace (a + 64 + 8) with (a + 72) in MU by lia.
    finish. all: try reflexivity. all: try exact MU.
    all: unfold bio_cells, bio_with_init, bio_with_ptr, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; try assumption.
  Qed.
End S.
