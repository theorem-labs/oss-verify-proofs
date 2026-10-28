(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_AC7_new.
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
  Local Ltac if_lit :=
    match goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        tryif (match c with context [?x] => is_var x end) then fail 1 "if_lit: open condition" else
        let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
    end.

  Definition ABN_RA1 : Z := R_b64_new_CRYPTO_zalloc.          (* [comment removed for export] *)
  Definition ABN_RA2 : Z := R_b64_new_EVP_ENCODE_CTX_new - 8.           (* [comment removed for export] *)
  Definition ABN_RA3 : Z := R_b64_new_EVP_ENCODE_CTX_new.     (* [comment removed for export] *)
  Definition ABN_RA4 : Z := R_b64_new_BIO_set_data.           (* [comment removed for export] *)
  Definition ABN_RA5 : Z := R_b64_new_BIO_set_init.           (* [comment removed for export] *)
  Definition AB64_FILE : Z := 0x1126a0.                        (* [comment removed for export] *)
  Definition SHB : Z := 0x7fff8000.

  (* [comment removed for export] *)
  Definition b64ctx_zero_cells : list cell :=
    [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); CB 2528 (zeros 2528); C8 (wz 0); C8 (wz 0)].
  Definition b64ctx_cs_cells : list cell :=
    [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0); C8 (wz 0); CB 2528 (zeros 2528); C8 (wz 0); C8 (wz 0)].
  Lemma b64ctx_zero_recut : forall m C, rw_cells asegs m C [CB (Z.to_nat B64CTX_SIZE) (zeros (Z.to_nat B64CTX_SIZE))] -> rw_cells asegs m C b64ctx_zero_cells.
  Proof. intros m C HB. eapply arw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.
  (* [comment removed for export] *)
  Lemma b64ctx_cs_split : forall m C, rw_cells asegs m C b64ctx_cs_cells ->
    rw_cells asegs m C (firstn 10 b64ctx_cs_cells) /\ rw_cells asegs m (C + O_B64_ENCBUF) [CB (Z.to_nat 16) (zeros 16)].
  Proof.
    intros m C HB. unfold b64ctx_cs_cells in *.
    match type of HB with rw_cells _ _ _ ?cs =>
      let l := eval cbv in (firstn 10 cs) in change cs with (l ++ [C8 (wz 0); C8 (wz 0)]) in HB end.
    apply (proj1 (rw_cells_app asegs _ _ _ _)) in HB. destruct HB as [H1 H2]. cbn [firstn]. split; [exact H1|].
    cbn [cells_size csize Nat.add] in H2. unfold O_B64_ENCBUF.
    eapply arw_cells_recut; [exact H2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.
  Lemma b64ctx_fresh_join : forall m C E, rw_cells asegs m C (firstn 8 b64ctx_cs_cells ++ [C8 (wz E); CB 2528 (zeros 2528)]) ->
    rw_cells asegs m (C + O_B64_ENCBUF) [CB (Z.to_nat 16) (zeros 16)] -> rw_cells asegs m C (b64ctx_fresh_cells E (zeros 2528)).
  Proof.
    intros m C E H1 H2. unfold b64ctx_fresh_cells.
    match goal with |- rw_cells _ _ _ ?cs =>
      let l := eval cbv in (firstn 10 cs) in change cs with (l ++ [C8 (wz 0); C8 (wz 0)]) end.
    apply (proj2 (rw_cells_app asegs _ _ _ _)). cbn [firstn app] in H1 |- *. split; [exact H1|].
    cbn [cells_size csize Nat.add]. unfold O_B64_ENCBUF in H2.
    eapply arw_cells_recut; [exact H2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma abn_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      a0 = Z_to_bv 64 A_b64_method -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 ANEX_RA1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1
                       (Z_to_bv 64 128) (Z_to_bv 64 ABIO_FILE) (Z_to_bv 64 83) a3 a4 a5 a6 a7 (Z_to_bv 64 A_b64_method) (Z_to_bv 64 0)
                       (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -64)
          /\ rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_new) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros A0 AC ST CEIL LO MI. subst a0. acb.
    unfold P_BIO_new, P_CRYPTO_zalloc, ANEX_RA1, ABIO_FILE, A_b64_method, SHB.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase _ AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. step. st1. st1. step. step. step. st1. st1. step. step. release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    carve_frame 64%nat ST. step. do 8 st1. do 10 step.
    finish; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma abn_seg3 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A lo : Z),
      ACONST m -> METH_b64 m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 ABN_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 2584) (Z_to_bv 64 AB64_FILE) (Z_to_bv 64 73)
                       a3 a4 a5 a6 a7 (Z_to_bv 64 (A_b64_method + 72)) (Z_to_bv 64 SHB) (Z_to_bv 64 SHB) (Z_to_bv 64 (sh (A_b64_method + 72))) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells asegs m1 (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 (Z_to_bv 64 (A_b64_method + 72)); C8 (Z_to_bv 64 A); C8 s0; C8 (Z_to_bv 64 ANEX_RA3)])
        (MS (mkR (Z_to_bv 64 ANEX_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 A_b64_method) s3
                 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ANEX_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AC NM ST CEIL LO MI. acb. unfold ANEX_RA2, ANEX_RA3, ABN_RA1, R_b64_new_CRYPTO_zalloc, AB64_FILE, P_CRYPTO_zalloc, A_b64_method, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x236cf0)) with (Z_to_bv 64 0x236cf0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase _ AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof NM as MT. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in MT. norm_addr MT.
    assert (IN : In (0x5e75e0, 112, 112) aglobals) by in_nth.
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt.
    assert (ACCmt : accessible m 0x5e75e0 112) by (eapply addressable_accessible; [exact ADmt| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    step. if_lit. step. ub_dead. step. ubal_any. step. if_lit. zstep. zstep. zstep. ck8_check_lit ACCmt (0x5e75e0 + 72). st1. step. if_false. step. unfold P_b64_new. step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. step. do 5 st1. do 12 step.
    change (6190560 + 72) with 6190632. unfold sh. rewrite ASHADOW_BASE_val. change (2147450880 + 6190632 / 8) with 2148224709.
    finish. all: try exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma abn_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (C : Z),
      0 < C -> C mod 16 = 0 -> C + B64CTX_SIZE <= aceil -> aapp C B64CTX_SIZE ->
      rw_cells asegs m C b64ctx_zero_cells -> accessible m C B64CTX_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ABN_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (C + 2576)) (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 C) (Z_to_bv 64 SHB)
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ABN_RA2) fc None m1 (seg_rom asegs)
          /\ munch [(C, C + B64CTX_SIZE)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 C b64ctx_cs_cells)
        (MS (mkR (Z_to_bv 64 ABN_RA1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SHB)
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ABN_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until C. intros CP CAL CH CAP BLK ACC MI. acb. unfold ABN_RA1, ABN_RA2, R_b64_new_CRYPTO_zalloc, R_b64_new_EVP_ENCODE_CTX_new, B64CTX_SIZE, O_B64_ENCBUF, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x5574c0)) with (Z_to_bv 64 0x5574c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold b64ctx_zero_cells, wz in BLK.
    pose proof (munch_refl [(C, C + 2584)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (_ & _ & CHI & _). unfold AAPP_HI in CHI.
    pose proof (aapp_not_shadowland _ _ CAP) as NSA. unfold ALOWSH_LO, AHI_LO in NSA.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(C, C + 2584)]) by nsw_tac.
    (* [comment removed for export] *)
    st1. ub_dead. do 3 st1. ubal_any. if_lit. do 3 st1. ck8_check ACC (C + 24). do 5 st1.
    (* [comment removed for export] *)
    reacc ACC MU NSW. ck8_check ACC0 (C + 20). clear ACC0. do 5 st1.
    (* [comment removed for export] *)
    reacc ACC MU NSW. ck8_check ACC0 (C + 2568). clear ACC0. do 4 st1. reacc ACC MU NSW. ck8_check ACC0 (C + 2576). clear ACC0. st1.
    finish. all: unfold b64ctx_cs_cells, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma abn_seg5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ABN_RA3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_EVP_ENCODE_CTX_new) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ABN_RA1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ABN_RA2) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI. unfold ABN_RA1, ABN_RA2, ABN_RA3, R_b64_new_CRYPTO_zalloc, R_b64_new_EVP_ENCODE_CTX_new, P_EVP_ENCODE_CTX_new.
    step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition abn_R (C E : Z) (i1 i2 i3 : bptr) : b64frep := mkBF 0 0 0 0 0 C E i1 i2 i3.

  (* [comment removed for export] *)
  Lemma abn_seg6 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s3x : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A C E lo : Z) (j1 j2 : list byte) (i1 i2 i3 : bptr),
      aapp A BIO_SIZE -> aapp C B64CTX_SIZE -> 0 < A -> A mod 16 = 0 -> 0 < C -> 0 < E -> E + ENCCTX_SIZE <= aceil ->
      (A + BIO_SIZE <= C \/ C + B64CTX_SIZE <= A) ->
      rw_cells asegs m A (firstn 18 (bio_cells (bio_hdr1 A_b64_method))) -> accessible m A BIO_SIZE ->
      rw_cells asegs m C (firstn 10 b64ctx_cs_cells) -> accessible m C B64CTX_SIZE ->
      ACONST m -> METH_b64 m ->
      rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m (bv_unsigned sp + -112) [CB 8 j2; C8 s3x; C8 (Z_to_bv 64 (A_b64_method + 72)); C8 (Z_to_bv 64 A); C8 sp; C8 (Z_to_bv 64 ANEX_RA3)] ->
      stk asegs m lo (bv_unsigned sp + -112) -> aceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1,
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + O_BIO_EXDATA); (C, C + O_B64_ENCBUF)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 A (firstn 18 (bio_cells (b64f_bio (abn_R C E i1 i2 i3))))
          /\ rw_cells asegs m1 C (firstn 8 b64ctx_cs_cells ++ [C8 (wz E); CB 2528 (zeros 2528)]))
        (MS (mkR (Z_to_bv 64 ABN_RA3) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 A)
                 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 C) (Z_to_bv 64 SHB) (Z_to_bv 64 SHB) (Z_to_bv 64 (sh (A_b64_method + 72))) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ABN_RA3)) fc None m (seg_rom asegs)).
  Proof.
    intros until i3. intros AAP CAP AP AAL CP EP EH DJ BA ACCA BC ACCC AC METH F1 F2 ST CEIL LO MI RAE. acb.
    unfold ABN_RA3, R_b64_new_EVP_ENCODE_CTX_new, ANEX_RA3, A_b64_method, BIO_SIZE, B64CTX_SIZE, ENCCTX_SIZE, O_BIO_EXDATA, O_B64_ENCBUF, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x557540)) with (Z_to_bv 64 0x557540) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (aapp_bounds _ _ AAP ltac:(lia)) as (AH & ACE & AHI & _). unfold AAPP_HI in AHI. unfold AIMG_TOP in AH.
    pose proof (aapp_bounds _ _ CAP ltac:(lia)) as (CH0 & CCE & CHI & _). unfold AAPP_HI in CHI. unfold AIMG_TOP in CH0.
    pose proof (aapp_not_shadowland _ _ AAP) as NSA. pose proof (aapp_not_shadowland _ _ CAP) as NSC. unfold ALOWSH_LO, AHI_LO in NSA, NSC.
    unfold bio_cells, bio_hdr1, wz in BA. cbn [firstn bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BA.
    unfold b64ctx_cs_cells, wz in BC. cbn [firstn] in BC.
    pose proof (ACONST_shbase _ AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof METH as MT. unfold METH_b64, O_METH_BREAD, A_b64_method, P_b64_new, wz in MT. norm_addr MT.
    assert (IN : In (0x5e75e0, 112, 112) aglobals) by in_nth.
    pose proof (ACONST_global_addressable m _ 112 112 AC IN ltac:(lia)) as ADmt.
    assert (ACCmt : accessible m 0x5e75e0 112) by (eapply addressable_accessible; [exact ADmt| lia| lia| unfold AAPP_HI; lia]).
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + 112); (C, C + 2568)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ASHADOW_BASE \/ AHI_LO <= fst iv) [(bv_unsigned sp + -128, bv_unsigned sp); (A, A + 112); (C, C + 2568)]) by nsw_tac.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACCC (C + 32). st1.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. step. step. unfold P_BIO_set_data. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. step. st1. st1. step. step. ub_dead. step. ubal_any. step. if_lit. step. step. step.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (A + 64). clear ACC. st1. st1. st1. step. release_frame FR ST (bv_unsigned sp + -112). step.
    (* [comment removed for export] *)
    step. step. step. step. unfold P_BIO_set_init. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. step. st1. st1. step. step. ub_dead. step. ubal_any. step. if_lit. step. step. step.
    zstep. zstep. zstep. reacc ACCA MU NSW. ck8_check ACC (A + 40). clear ACC. st1. st1. st1. step. release_frame FR ST (bv_unsigned sp + -112). step.
    (* [comment removed for export] *)
    step. step. st1. st1. st1. st1. st1. step. release_frame F2 ST (bv_unsigned sp + -64). step.
    (* [comment removed for export] *)
    step. if_lit.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCmt1 : accessible mx 0x5e75e0 112) by (eapply accessible_across2; [exact ACCmt| exact MU| exact NSW]) end.
    change (6190560 + 72) with 6190632 in *. unfold sh. rewrite ASHADOW_BASE_val.
    replace (2147450880 + 6190632 / 8) with (Z.shiftr 6190632 3 + 2147450880) by reflexivity.
    ck8_load_lit ACCmt1 6190632. step. if_false_by (ck1_bnez_false 0 eq_refl). st1. step. if_true.
    step. do 7 st1. step. release_frame F1 ST (bv_unsigned sp). step.
    finish. all: unfold bio_cells, abn_R, b64f_bio, b64ctx_cs_cells, wz; cbn [firstn app bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
      bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc]; unfold A_b64_method; try assumption.
  Qed.
End S.
