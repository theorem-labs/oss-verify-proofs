(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1
  ECH_AKit ECH_AsKit ECH_AC1_malloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma skipn_nth_cons : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  induction l as [|y l IH]; intros i x Hn; [destruct i; discriminate|].
  destruct i as [|i]; cbn in Hn; [injection Hn as ->; reflexivity|].
  change (skipn (S i) (y :: l)) with (skipn i l). change (skipn (S (S i)) (y :: l)) with (skipn (S i) l). apply IH. exact Hn.
Qed.
Lemma strnlen_at_zero : forall bs i b, nth_error bs i = Some b -> bv_unsigned b = 0 -> strnlen (skipn i bs) = 0%nat.
Proof. intros bs i b Hn Hb. rewrite (skipn_nth_cons bs i b Hn). cbn. rewrite Hb. reflexivity. Qed.
Lemma strnlen_at_nz : forall bs i b, nth_error bs i = Some b -> bv_unsigned b <> 0 -> strnlen (skipn i bs) = S (strnlen (skipn (S i) bs)).
Proof.
  intros bs i b Hn Hb. rewrite (skipn_nth_cons bs i b Hn). cbn. destruct (Z.eqb_spec (bv_unsigned b) 0); [lia| reflexivity].
Qed.
Lemma strnlen_skipn_le : forall bs i, (strnlen (skipn i bs) + i <= length bs + 0)%nat \/ (length bs < i)%nat.
Proof.
  intros bs i. destruct (Nat.le_gt_cases i (length bs)) as [L|L]; [left| right; exact L].
  pose proof (strnlen_le (skipn i bs)) as K. rewrite length_skipn in K. lia.
Qed.
Lemma bytes_at_firstn : forall m a bs n, bytes_at asegs m a bs -> bytes_at asegs m a (firstn n bs).
Proof. intros m a bs n HB. rewrite <- (firstn_skipn n bs) in HB. apply bytes_at_app in HB. exact (proj1 HB). Qed.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition AMD_RA1 : Z := R_CRYPTO_memdup_CRYPTO_malloc.    (* [comment removed for export] *)
  Definition AMD_RA2 : Z := R_CRYPTO_memdup_asan_memcpy.     (* [comment removed for export] *)
  Definition ASD_RA1 : Z := R_CRYPTO_strndup_CRYPTO_malloc.   (* [comment removed for export] *)
  Definition ASD_RA2 : Z := R_CRYPTO_strndup_asan_memcpy.    (* [comment removed for export] *)
  Definition ASD_LOOP : Z := 0x1ef598.
  Definition ASD_LJ : Z := 0x1ef5a8.                          (* [comment removed for export] *)
  Definition ASD_LX : Z := 0x1ef5d8.                          (* [comment removed for export] *)
  Definition ASD_ST : Z := 0x1ef61c.                          (* [comment removed for export] *)
  Definition ASHB : Z := 0x7fff8000.                          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition sd_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition amd1_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
      (F : bvmap 5 word) (fc : bv 32) (D n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j,
      ms' = MS (mkR (Z_to_bv 64 AMD_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 n)
                   (Z_to_bv 64 n) a2 a3 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells asegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra).

  Lemma amd_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (D n lo : Z),
      0 < D < 2^64 -> 1 <= n < 0x7ffffffe ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      evt asegs (amd1_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc D n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HD HN ST CEIL LO MI. acb. unfold P_CRYPTO_memdup, P_CRYPTO_malloc.
    pose proof (aword_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    do 8 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 4 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 4 step. unfold amd1_post, AMD_RA1, R_CRYPTO_memdup_CRYPTO_malloc. finish.
    lazymatch goal with FR : rw_cells _ _ _ [CB 8 _; _; _; _; _; _] |- _ => exact FR end.
  Qed.

  (* [comment removed for export] *)
  Lemma amd_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A D n : Z),
      0 < A < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 AMD_RA2) sp gp tp t0 t1 t2 s0x (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 D) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                                         (Z_to_bv 64 A) (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 AASAN_MEMCPY) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AMD_RA1) sp gp tp t0 t1 t2 s0x (Z_to_bv 64 n) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2x (Z_to_bv 64 D) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMD_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until n. intros HA MI. unfold AMD_RA1, AMD_RA2, R_CRYPTO_memdup_CRYPTO_malloc, R_CRYPTO_memdup_asan_memcpy, AASAN_MEMCPY.
    replace (ret_pc (Z_to_bv 64 0x1ef738)) with (Z_to_bv 64 0x1ef738) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma amd_seg3 :
    forall (sp gp tp t0 t1 t2 s0x s1x a0x a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word) (s3v : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (j : list byte),
      0 < A < 2^64 ->
      rw_cells asegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (ret_pc ra) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AMD_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1x a0x a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 A) s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AMD_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HA FR MI. unfold AMD_RA2, R_CRYPTO_memdup_asan_memcpy.
    replace (ret_pc (Z_to_bv 64 0x1ef74c)) with (Z_to_bv 64 0x1ef74c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. unfold cm_frame in FR.
    do 9 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma asd_loop : forall (k : nat) (i : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (sa : Z) (bs : list byte),
      Z.to_nat (zlength bs - i) = k -> 0 <= i < zlength bs ->
      bytes_at asegs m sa bs -> accessible m sa (zlength bs) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists t0' a0' a1' a7',
                   ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2 a3
                                 (Z_to_bv 64 (sa + (i + Z.of_nat (strnlen (skipn (Z.to_nat i) bs))))) (Z_to_bv 64 (sa + zlength bs)) (Z_to_bv 64 (-1)) a7'
                                 s2 s3 (Z_to_bv 64 ASHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 ASD_LX) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sa + i)) (Z_to_bv 64 (zlength bs - i)) a2 a3 (Z_to_bv 64 (sa + i)) (Z_to_bv 64 (sa + zlength bs)) (Z_to_bv 64 (-1)) a7
                 s2 s3 (Z_to_bv 64 ASHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASD_LOOP) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until bs; intros HK HI BS ACC MI; [unfold zlength in *; lia|].
    unfold ASD_LOOP, ASD_LX, ASHB in *.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *. pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    pose proof (abyte_range b) as BR.
    (* [comment removed for export] *)
    assert (KJ : forall (v : Z) (t0v : word),
      evt asegs (fun ms' => exists t0' a0' a1' a7',
                   ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2 a3
                                 (Z_to_bv 64 (sa + (i + Z.of_nat (strnlen (skipn (Z.to_nat i) bs))))) (Z_to_bv 64 (sa + Z.of_nat (length bs))) (Z_to_bv 64 (-1)) a7'
                                 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0x1ef5d8) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0v t1 t2 s0 s1 (Z_to_bv 64 (sa + i)) (Z_to_bv 64 (Z.of_nat (length bs) - i)) a2 a3 (Z_to_bv 64 (sa + i)) (Z_to_bv 64 (sa + Z.of_nat (length bs)))
                 (Z_to_bv 64 (-1)) (Z_to_bv 64 v) s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASD_LJ) fc None m (seg_rom asegs))).
    { intros v t0v. unfold ASD_LJ.
      pose proof (u8ro_read asegs m sa bs i b _ BS NTH ltac:(lia) eq_refl) as RD.
      step. zstep. if_cases K0; zify_cond K0.
      - (* [comment removed for export] *)
        rewrite (strnlen_at_zero bs (Z.to_nat i) b NTH K0). replace (sa + (i + Z.of_nat 0)) with (sa + i) by lia.
        apply evt_done. eexists _, _, _, _. reflexivity.
      - rewrite (strnlen_at_nz bs (Z.to_nat i) b NTH K0).
        step. if_cases KU; zify_cond KU. { exfalso. revert KU. rewrite ?unsigned_lit by lia. clear - HI BB AHI. lia. } clear KU.
        zstep. zstep. zstep. step. if_cases K1; zify_cond K1.
        + (* [comment removed for export] *)
          replace (Z.of_nat (length bs) - i + -1) with (Z.of_nat (length bs) - (i + 1)) by lia.
          replace (sa + i + 1) with (sa + (i + 1)) by lia.
          replace (sa + (i + Z.of_nat (S (strnlen (skipn (S (Z.to_nat i)) bs))))) with
                  (sa + ((i + 1) + Z.of_nat (strnlen (skipn (Z.to_nat (i + 1)) bs)))) by (replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; lia).
          eapply IH; [lia| | exact BS| exact ACC| exact MI]. revert K1. rewrite ?unsigned_lit by lia. lia.
        + (* [comment removed for export] *)
          step. step.
          assert (E : i + 1 = Z.of_nat (length bs)) by (revert K1; rewrite ?unsigned_lit by lia; lia).
          pose proof (strnlen_skipn_le bs (S (Z.to_nat i))) as SL.
          replace (sa + (i + Z.of_nat (S (strnlen (skipn (S (Z.to_nat i)) bs))))) with (sa + Z.of_nat (length bs)) by lia.
          apply evt_done. eexists _, _, _, _. reflexivity. }
    cbv delta [mkR] in KJ.
    (* [comment removed for export] *)
    zstep. zstep.
    ck1_load ACC (sa + i) v V1 V2 Hk.
    pose proof (KJ v) as KJv.
    ck1_branch_blt (sa + i) v V1 V2 Hk KJv.
  Qed.

  (* [comment removed for export] *)
  Definition asd1_post (sp gp tp t0 t1 t2 a2 a3 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (sa : Z) (k : nat) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 (t0' a4' a5' a6' a7' : word),
      ms' = MS (mkR (Z_to_bv 64 ASD_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1 t2 sp (Z_to_bv 64 sa)
                   (Z_to_bv 64 (Z.of_nat k + 1)) a2 a3 a3 a4' a5' a6' a7' s2 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 ASHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells asegs m1 (bv_unsigned sp + -48) (sd_frame s4 s3 s2 s1 s0 ra).

  Lemma asd_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sa lo : Z) (bs : list byte),
      0 < sa < 2^64 -> zlength bs < 2^31 ->
      bytes_at asegs m sa bs -> accessible m sa (zlength bs) -> sa + zlength bs <= aceil ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      evt asegs (asd1_post sp gp tp t0 t1 t2 a2 a3 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s3 s4 F fc sa (strnlen bs) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 (zlength bs)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_strndup) fc None m (seg_rom asegs)).
  Proof.
    intros until bs. intros HS HL BS ACC OFF GSB SHB ST CEIL LO MI. acb. unfold P_CRYPTO_strndup, P_CRYPTO_malloc. unfold zlength in *.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof (aword_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (strnlen_le bs) as SNL. pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    pose proof BS as BS'. clear BS. change (id (bytes_at asegs m sa bs)) in BS'.
    pose proof ACC as ACC'. clear ACC. change (id (accessible m sa (Z.of_nat (length bs)))) in ACC'.
    do 8 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (BS : bytes_at asegs mx sa bs) by (unfold id in BS'; eapply bytes_at_transport; [exact BS'| exact MU| cbn; lia]);
      assert (ACC : accessible mx sa (Z.of_nat (length bs)))
        by (unfold id in ACC'; eapply accessible_transport; [exact ACC'| exact MU|]; intros x Hx; assert (Qx : x <= aceil) by lia;
            pose proof (sh_mono x aceil Qx); assert (Qc : 0 <= aceil < AAPP_HI) by (unfold AAPP_HI; lia); pose proof (sh_below_aceil aceil Qc); cbn; lia);
      rename mx into m0 end.
    clear BS' ACC'.
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    assert (FIN : forall t0' a0' a1' a5' a6' a7',
      evt asegs (asd1_post sp gp tp t0 t1 t2 a2 a3 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s3 s4 F fc sa (strnlen bs) lo m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1 t2 sp (Z_to_bv 64 sa)
                 a0' a1' a2 a3 (Z_to_bv 64 (sa + Z.of_nat (strnlen bs))) a5' a6' a7' s2 s3 (Z_to_bv 64 ASHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASD_LX) fc None m0 (seg_rom asegs))).
    { intros t0' a0' a1' a5' a6' a7'. unfold ASD_LX, ASHB. zstep.
      first [ replace (sa + Z.of_nat (strnlen bs) - sa) with (Z.of_nat (strnlen bs)) by lia
            | replace (sa + Z.of_nat (strnlen bs) + - sa) with (Z.of_nat (strnlen bs)) by lia ].
      zstep. do 3 step. unfold asd1_post, ASD_RA1, R_CRYPTO_strndup_CRYPTO_malloc, ASHB, P_CRYPTO_malloc. finish. }
    cbv delta [mkR] in FIN. unfold ASHB, ASD_LX in FIN.
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (E0 : bs = []) by (destruct bs; [reflexivity| cbn [length] in K0; lia]).
      subst bs. cbn [strnlen] in FIN. replace (sa + Z.of_nat 0%nat) with sa in FIN by lia. apply FIN.
    - zstep. step. step. step.
      eapply evt_cut.
      { replace (Z_to_bv 64 (Z.of_nat (length bs))) with (Z_to_bv 64 (zlength bs - 0)) by (unfold zlength; f_equal; lia).
        replace (Z_to_bv 64 sa) with (Z_to_bv 64 (sa + 0)) by (f_equal; lia).
        replace (Z_to_bv 64 (sa + Z.of_nat (length bs))) with (Z_to_bv 64 (sa + zlength bs)) by reflexivity.
        eapply (asd_loop (Z.to_nat (Z.of_nat (length bs))) 0); [unfold zlength; lia| unfold zlength; lia| exact BS| exact ACC| exact MI]. }
      intros ms' (t0' & a0' & a1' & a7' & ->). change (Z.to_nat 0) with 0%nat. cbn [skipn].   (* [comment removed for export] *)
      replace (sa + (0 + Z.of_nat (strnlen bs))) with (sa + Z.of_nat (strnlen bs)) by lia. replace (sa + 0) with sa by lia.
      unfold zlength. apply FIN.
  Qed.

  (* [comment removed for export] *)
  Lemma asd_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A sa : Z) (k : nat),
      0 < A < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ASD_RA2) sp gp tp t0 t1 t2 s0x (Z_to_bv 64 sa) (Z_to_bv 64 A) (Z_to_bv 64 sa) (Z_to_bv 64 (Z.of_nat k)) a3 a4 a5 a6 a7
                                         (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat k)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 AASAN_MEMCPY) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ASD_RA1) sp gp tp t0 t1 t2 s0x (Z_to_bv 64 sa) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2x (Z_to_bv 64 (Z.of_nat k)) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ASD_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until k. intros HA MI. unfold ASD_RA1, ASD_RA2, R_CRYPTO_strndup_CRYPTO_malloc, R_CRYPTO_strndup_asan_memcpy, AASAN_MEMCPY.
    replace (ret_pc (Z_to_bv 64 0x1ef5ec)) with (Z_to_bv 64 0x1ef5ec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma asd_seg3 :
    forall (sp gp tp t0 t1 t2 s0x a0x a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word) (s1x : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (k : nat) (z : list byte),
      0 < A -> A + Z.of_nat k + 1 < AAPP_HI ->
      rw_cells asegs m (bv_unsigned sp + -48) (sd_frame s4 s3 s2 s1 s0 ra) ->
      rw_cells asegs m (A + Z.of_nat k) [CB 1 z] -> accessible m (A + Z.of_nat k) 1 ->
      (A + Z.of_nat k + 1 <= bv_unsigned sp + -48 \/ bv_unsigned sp <= A + Z.of_nat k) ->
      (sh (A + Z.of_nat k) + 1 <= A + Z.of_nat k \/ A + Z.of_nat k + 1 <= sh (A + Z.of_nat k)) ->
      sh (A + Z.of_nat k) + 1 <= bv_unsigned sp + -48 ->
      mem_inv asegs m ->
      evt asegs (fun ms' => exists (a1' a2' : word) m',
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m' (seg_rom asegs)
                   /\ munch [(A + Z.of_nat k, A + Z.of_nat k + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                   /\ rw_cells asegs m' (A + Z.of_nat k) [C1 (b8 0)])
        (MS (mkR (Z_to_bv 64 ASD_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1x a0x a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 ASHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ASD_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until z. intros HA HK FR NUL ACC DJ SDJ SLO MI. unfold ASD_RA2, R_CRYPTO_strndup_asan_memcpy, ASHB. unfold AAPP_HI in HK.
    replace (ret_pc (Z_to_bv 64 0x1ef600)) with (Z_to_bv 64 0x1ef600) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. unfold sd_frame in FR.
    pose proof (munch_refl [(A + Z.of_nat k, A + Z.of_nat k + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. rewrite zb_lxor_ones by lia. step. if_cases KU; zify_cond KU. { exfalso. revert KU. rewrite ?unsigned_lit by lia. clear - HA HK. intros KU. lia. } clear KU.
    zstep. set (Q := A + Z.of_nat k) in *.
    (* [comment removed for export] *)
    assert (KS : forall (a1v a2v : word),
      evt asegs (fun ms' => exists (a1' a2' : word) m',
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m' (seg_rom asegs)
                   /\ munch [(Q, Q + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' Q [C1 (b8 0)])
        (MS (mkR (Z_to_bv 64 0x1ef600) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 Q) a1v a2v a3 a4 a5 a6 a7
                 (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASD_ST) fc None m (seg_rom asegs))).
    { intros a1v a2v. unfold ASD_ST. st1. subst Q. do 10 step. finish. }
    cbv delta [mkR] in KS.
    (* [comment removed for export] *)
    zstep. zstep.
    ck1_load ACC Q v V1 V2 Hk.
    pose proof (fun a2v : word => KS (Z_to_bv 64 v) a2v) as KSv. cbv beta in KSv.
    ck1_branch_blt Q v V1 V2 Hk KSv.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Local Ltac cm_pre HP KREL AUX ST ERR MI AC CW MF IM GM MU WM :=
    lazymatch goal with
    | |- as_RHEAP _ _ _ _ => eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM| exact CW]
    | |- as_AKREL _ _ _ => exact KREL
    | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX| exact MU| exact WM| exact CW]
    | |- stk _ _ _ _ => exact ST
    | |- rw_cells _ _ _ [C4 _] => eapply errno_across; [exact ERR| exact MU| exact WM| unfold ATP; cbn; lia]
    | |- mem_inv _ _ => exact MI
    | |- _ = Z_to_bv 64 ATP => reflexivity
    | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU| exact WM|];
                     constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]
    | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU| exact WM| unfold A_mem_inited; cbn; lia| exact MF]
    | |- IMPL_mem _ => eapply IMPL_across; [exact MU| exact WM| unfold A_malloc_impl; cbn; lia| exact IM]
    | |- GOT_mem _ => eapply GOT_across; [exact MU| exact WM| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
    | |- _ => first [assumption | lia | unfold CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK; lia | match goal with |- ?G => idtac "LEFT:" G end]
    end.

  Lemma acmemdup_spec : cmemdup_stmt H.
  Proof.
    unfold cmemdup_stmt. intros until CH.
    intros VIS A0 A1 HN BS HBIN HBLO HBHI HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL ACC MF IM GM.
    unfold CMEMDUP_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_malloc, AMALLOC_STACK in LO. acb. subst a0 a1 tp.
    rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    destruct bD as [[pD AD] nD]. cbn [blk_addr blk_size fst snd] in HBLO, HBHI.
    pose proof (ah_blocks H HH _ _ _ _ HP HBIN) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). cbn [blk_addr blk_size fst snd] in *. unfold AIMG_TOP in D4.
    pose proof (aapp_bounds AD nD D7 D3) as (DB1 & DB2 & DB3 & DB4 & DB5). unfold AAPP_HI in DB3.
    pose proof (sh_aapp_range AD nD D7 D3) as (DS1 & DS2 & DS3). unfold AHI_LO in DS3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply amd_seg1; [lia| lia| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (XP1 : xpres H LB (bv_unsigned sp) memflag_foot m m1).
    { eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (BS1 : bytes_at asegs m1 D bs) by (eapply bytes_at_transport; [exact BS| exact MU1| cbn; lia]).
    assert (ACC1 : accessible m1 D (Z.of_nat (length bs))).
    { eapply accessible_transport; [exact ACC| exact MU1|]. intros x Hx. assert (Qx : x <= aceil) by lia. pose proof (sh_mono x aceil Qx). cbn. lia. }
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold cm_frame in FR2.
      change ([CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + 32) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    (* [comment removed for export] *)
    pose proof (acmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (ah_seq H HH).
    { eapply CM with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (n := Z.of_nat (length bs)) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| reflexivity| ..]; rewrite ?unsigned_lit by lia.
      all: lazymatch goal with
           | |- as_chain _ _ _ _ => exact CH1
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_cmemdup; intros x Hx; exact Hx
           | |- _ => cm_pre HP KREL1 AUX ST1 ERR MI1 AC CW MF IM GM MU1 WM1
           end. }
    intros [msF2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & ADDR & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4.
    pose proof (aapp_bounds A (Z.of_nat (length bs)) BR7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    (* [comment removed for export] *)
    assert (XCR : xclient_range H LB (bv_unsigned sp + -48) memflag_foot D (Z.of_nat (length bs))).
    { split; [right; right; left; exists (pD, AD, nD); split; [exact HBIN| cbn; lia]|].
      unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor]. }
    eapply (xpres_bytes_at H _ _ _ _ _ _ _ XP2) in BS1; [| exact XCR].
    assert (ACC2 : accessible m2 D (Z.of_nat (length bs))).
    { assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in DS1.
      destruct ACC1 as (Q0 & Q1 & QA). split; [exact Q0|]. split; [exact Q1|]. intros x Hx. destruct (QA x Hx) as (vx & V1 & RD & OK).
      exists vx. split; [exact V1|]. split; [| exact OK]. unfold mrd in *.
      assert (SX1 : sh AD <= sh x) by (apply sh_mono; lia). assert (SX2 : sh x <= sh aceil) by (apply sh_mono; lia).
      destruct (XP2 (sh x) ltac:(lia)) as [E _].
      { split; [| unfold memflag_foot, A_mem_inited; cbn; lia].
        right; right; right; left. exists (pD, AD, nD). split; [exact HBIN|]. cbn [blk_addr blk_size fst snd].
        assert (D8 : AD mod 8 = 0) by (clear - D2; Z.div_mod_to_equations; lia).
        pose proof (sh_rel_lt AD x nD D8 ltac:(lia)). rewrite (sh_rel AD x D8) by lia. unfold nsh. lia. }
      rewrite E. exact RD. }
    assert (FOUT : forall a, aclient_addr H LB (bv_unsigned sp + -48) a -> A <= a < A + Z.of_nat (length bs) -> False) by (intros a0' C0' R0'; eapply (afresh_outside H HH); [exact HEAP2| | exact C0'| exact R0']; lia).
    assert (SEP : D + Z.of_nat (length bs) <= A \/ A + Z.of_nat (length bs) <= D).
    { destruct (Z.lt_ge_cases D A) as [L|L].
      - left. destruct (Z.le_gt_cases (D + Z.of_nat (length bs)) A) as [L2|L2]; [exact L2|]. exfalso.
        apply (FOUT A); [| lia]. right; right; left. exists (pD, AD, nD). split; [exact HBIN| cbn; lia].
      - right. destruct (Z.le_gt_cases (A + Z.of_nat (length bs)) D) as [L2|L2]; [exact L2|]. exfalso.
        apply (FOUT D); [| lia]. right; right; left. exists (pD, AD, nD). split; [exact HBIN| cbn; lia]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply amd_seg2; [lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3|..].
    { eapply (asan_memcpy_specZ H HH) with (lo := lo) (src := bs); try eassumption; try lia.
      - eapply addressable_accessible; [exact ADDR| lia| lia| unfold AAPP_HI; lia].
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HEAP2 (or_intror HBIN))| lia| lia| lia| lia| lia].
      - exact (ah_blk_shvis H HH _ _ _ _ _ _ HEAP2 (or_introl eq_refl)).
      - eapply aapp_in_app_mem; [exact D7| lia| lia].
      - eapply aapp_in_app_mem; [exact BR7| lia| lia].
      - eapply aconst_ok_aapp; [exact BR7| lia| lia]. }
    intros msF4 mo4 KREL4 MP4 PO. unfold amove_post in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & VIS4 & MU3 & WM3 & MI3 & ST3 & BLK3 & BS3 & AC3).
    assert (CW3 : Forall (aclient_write_ok H ((p, A, Z.of_nat (length bs)) :: LB)) [(A, A + Z.of_nat (length bs)); (bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48)]).
    { constructor; [| constructor; [left; cbn; lia| constructor]]. right; right; left. exists (p, A, Z.of_nat (length bs)). split; [left; reflexivity| cbn; lia]. }
    assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra)).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact FR1| exact MU3| exact WM3|]. cbn. lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL4| exact VIS4| eapply amd_seg3; [lia| exact FR3| exact MI3]|].
    intros msF5 mo5 KREL5 MP5 VIS5.
    unfold cmemdup_post. cbn [cfg_ms cfg_model]. unfold zlength.
    exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m3, errv2, A, p, s'.
    split; [exact VIS5|]. split; [exact KREL5|].
    split; [eapply (ah_mpres_trans H HH); [| exact MP5]; eapply (ah_mpres_trans H HH); [| exact MP4]; eapply (ah_mpres_trans H HH); [| exact MP3];
            eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI3|]. split; [exact AC3|].
    split. { unfold cm_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
    split. { rewrite unsigned_lit by (unfold ATP; lia). eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]. }
    split. { eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| exact CW3]. }
    split.
    { eapply xpres_trans; [exact XP1|]. eapply xpres_trans.
      - eapply (xpres_weaken H LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto].
      - eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|].
        constructor; [right; left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3| exact CW3]. }
    split. { replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) in BLK3 by lia. exact BLK3. }
    split. { eapply addressable_transport; [exact ADDR| exact MU3| exact WM3|].
             pose proof (sh_aapp_range A (Z.of_nat (length bs)) BR7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3.
             assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1.
             cbn. destruct BR7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    split; [eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]|].
    exact AL2.
  Qed.

  Lemma acstrndup_spec : cstrndup_stmt H.
  Proof.
    unfold cstrndup_stmt. intros until CH.
    intros VIS A0 HS A1 HL BS HBIN HBLO HBHI HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL ACC MF IM GM.
    unfold CSTRNDUP_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_malloc, AMALLOC_STACK in LO. acb. subst a0 a1 tp.
    rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    destruct bS as [[pD AD] nD]. cbn [blk_addr blk_size fst snd] in HBLO, HBHI.
    pose proof (ah_blocks H HH _ _ _ _ HP HBIN) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). cbn [blk_addr blk_size fst snd] in *. unfold AIMG_TOP in D4.
    pose proof (aapp_bounds AD nD D7 D3) as (DB1 & DB2 & DB3 & DB4 & DB5). unfold AAPP_HI in DB3.
    pose proof (sh_aapp_range AD nD D7 D3) as (DS1 & DS2 & DS3). unfold AHI_LO in DS3.
    pose proof (strnlen_le bs) as KL. set (k := strnlen bs) in *.
    pose proof (ACONST_shbase m AC) as [GSB SHB].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply asd_seg1 with (lo := lo); [exact HS| unfold zlength; lia| exact BS| exact ACC| unfold zlength; lia| exact GSB| exact SHB| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & t0' & a4' & a5' & a6' & a7' & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1). subst k. set (k := strnlen bs) in *.
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -48, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (XP1 : xpres H LB (bv_unsigned sp) memflag_foot m m1).
    { eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (BS1 : bytes_at asegs m1 S bs) by (eapply bytes_at_transport; [exact BS| exact MU1| cbn; lia]).
    assert (ACC1 : accessible m1 S (Z.of_nat (length bs))).
    { eapply accessible_transport; [exact ACC| exact MU1|]. intros x Hx. assert (Qx : x <= aceil) by lia. pose proof (sh_mono x aceil Qx). cbn. lia. }
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold sd_frame in FR2.
      change ([C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + 32) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    (* [comment removed for export] *)
    pose proof (acmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (ah_seq H HH).
    { eapply CM with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (n := Z.of_nat k + 1) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| reflexivity| ..]; rewrite ?unsigned_lit by lia.
      all: lazymatch goal with
           | |- as_chain _ _ _ _ => exact CH1
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_cstrndup; intros x Hx; exact Hx
           | |- _ <= as_AL _ _ => pose proof (ah_costs H HH) as (_ & CMO & _); pose proof (CMO (Z.of_nat k + 1) (Z.of_nat (length bs) + 1) ltac:(lia)); lia
           | |- _ => cm_pre HP KREL1 AUX ST1 ERR MI1 AC CW MF IM GM MU1 WM1
           end. }
    intros [msF2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & ADDR & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4.
    pose proof (aapp_bounds A (Z.of_nat k + 1) BR7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    pose proof (sh_aapp_range A (Z.of_nat k + 1) BR7 ltac:(lia)) as (AS1 & AS2 & AS3). unfold AHI_LO in AS3.
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in DS1, AS1.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    assert (XCR : xclient_range H LB (bv_unsigned sp + -48) memflag_foot S (Z.of_nat (length bs))).
    { split; [right; right; left; exists (pD, AD, nD); split; [exact HBIN| cbn; lia]|].
      unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor]. }
    eapply (xpres_bytes_at H _ _ _ _ _ _ _ XP2) in BS1; [| exact XCR].
    assert (ACC2 : accessible m2 S (Z.of_nat (length bs))).
    { destruct ACC1 as (Q0 & Q1 & QA). split; [exact Q0|]. split; [exact Q1|]. intros x Hx. destruct (QA x Hx) as (vx & V1 & RD & OK).
      exists vx. split; [exact V1|]. split; [| exact OK]. unfold mrd in *.
      assert (SX1 : sh AD <= sh x) by (apply sh_mono; lia). assert (SX2 : sh x <= sh aceil) by (apply sh_mono; lia).
      destruct (XP2 (sh x) ltac:(lia)) as [E _].
      { split; [| unfold memflag_foot, A_mem_inited; cbn; lia].
        right; right; right; left. exists (pD, AD, nD). split; [exact HBIN|]. cbn [blk_addr blk_size fst snd].
        assert (D8 : AD mod 8 = 0) by (clear - D2; Z.div_mod_to_equations; lia).
        pose proof (sh_rel_lt AD x nD D8 ltac:(lia)). rewrite (sh_rel AD x D8) by lia. unfold nsh. lia. }
      rewrite E. exact RD. }
    assert (FOUT : forall a, aclient_addr H LB (bv_unsigned sp + -48) a -> A <= a < A + (Z.of_nat k + 1) -> False) by (intros a0' C0' R0'; eapply (afresh_outside H HH); [exact HEAP2| | exact C0'| exact R0']; lia).
    assert (SEP : S + Z.of_nat k <= A \/ A + Z.of_nat k <= S).
    { destruct (Nat.eq_dec k 0) as [K0|K0]; [lia|].
      destruct (Z.lt_ge_cases S A) as [L|L].
      - left. destruct (Z.le_gt_cases (S + Z.of_nat k) A) as [L2|L2]; [exact L2|]. exfalso.
        apply (FOUT A); [| lia]. right; right; left. exists (pD, AD, nD). split; [exact HBIN| cbn; lia].
      - right. destruct (Z.le_gt_cases (A + Z.of_nat k) S) as [L2|L2]; [exact L2|]. exfalso.
        apply (FOUT S); [| lia]. right; right; left. exists (pD, AD, nD). split; [exact HBIN| cbn; lia]. }
    pose proof (rw_cells_bound _ _ _ _ BLK) as BKB. cbn [cells_size csize Nat.add] in BKB.
    destruct (rw_cells_CB_split asegs _ A (Z.to_nat (Z.of_nat k + 1)) k junk BLK ltac:(lia)) as [BK BZ]. clear BLK.
    replace (Z.to_nat (Z.of_nat k + 1) - k)%nat with 1%nat in BZ by lia.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply asd_seg2; [lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3|..].
    { eapply (asan_memcpy_specZ H HH) with (lo := lo) (src := firstn k bs); try eassumption; try lia.
      - apply bytes_at_firstn. exact BS1.
      - rewrite length_firstn. lia.
      - rewrite Nat2Z.id. exact BK.
      - eapply accessible_sub; [exact ACC2| lia| lia| lia].
      - eapply addressable_accessible; [exact ADDR| lia| lia| unfold AAPP_HI; lia].
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HEAP2 (or_intror HBIN))| lia| lia| lia| lia| lia].
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ HEAP2 (or_introl eq_refl))| lia| lia| lia| lia| lia].
      - eapply aapp_in_app_mem; [exact D7| lia| lia].
      - eapply aapp_in_app_mem; [exact BR7| lia| lia].
      - eapply aconst_ok_aapp; [exact BR7| lia| lia]. }
    intros msF4 mo4 KREL4 MP4 PO. unfold amove_post in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & VIS4 & MU3 & WM3 & MI3 & ST3 & BLK3 & BS3 & AC3).
    rewrite Nat2Z.id in BLK3.
    apply (rw_cells_transport asegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
    apply (rw_cells_transport asegs _ m2 m3 _ _ BZ) in MU3 as BZ3; [| exact WM3| cbn; lia].
    assert (ADDR3 : addressable m3 A (Z.of_nat k + 1)).
    { eapply addressable_transport; [exact ADDR| exact MU3| exact WM3|]. cbn. destruct BR7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    assert (ACC3 : accessible m3 (A + Z.of_nat k) 1) by (eapply addressable_accessible; [exact ADDR3| lia| lia| unfold AAPP_HI; lia]).
    assert (SHX : sh (A + Z.of_nat k) + 1 <= A + Z.of_nat k \/ A + Z.of_nat k + 1 <= sh (A + Z.of_nat k)).
    { pose proof (sh_mono A (A + Z.of_nat k) ltac:(lia)). assert (QA : A + Z.of_nat k <= aceil) by lia. pose proof (sh_mono (A + Z.of_nat k) aceil QA).
      destruct BR7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    assert (SHLO : sh (A + Z.of_nat k) + 1 <= bv_unsigned sp + -48).
    { assert (QA : A + Z.of_nat k <= aceil) by lia. pose proof (sh_mono (A + Z.of_nat k) aceil QA). lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL4| exact VIS4| eapply asd_seg3; [lia| unfold AAPP_HI; lia| exact FR3| exact BZ3| exact ACC3| lia| exact SHX| exact SHLO| exact MI3]|].
    intros msF5 mo5 KREL5 MP5 (a1' & a2' & m4 & VIS5 & MU4 & WM4 & MI4 & NUL4).
    assert (MU34 : munch [(A, A + Z.of_nat k + 1); (bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48)] m2 m4).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]; intros x Hx; cbn in Hx |- *; lia. }
    pose proof (wmono_trans asegs _ _ _ WM3 WM4) as WM34.
    assert (CW3 : Forall (aclient_write_ok H ((p, A, Z.of_nat k + 1) :: LB)) [(A, A + Z.of_nat k + 1); (bv_unsigned sp + -48 - 4096, bv_unsigned sp + -48)]).
    { constructor; [| constructor; [left; cbn; lia| constructor]]. right; right; left. exists (p, A, Z.of_nat k + 1). split; [left; reflexivity| cbn; lia]. }
    unfold cstrndup_post. cbn [cfg_ms cfg_model]. cbv zeta. subst k.
    exists v0, v1, v2, a1', a2', d3, d4, d5, d6, d7, v3, v4, v5, v6, m4, errv2, A, p, s'.
    split; [exact VIS5|]. split; [exact KREL5|].
    split; [eapply (ah_mpres_trans H HH); [| exact MP5]; eapply (ah_mpres_trans H HH); [| exact MP4]; eapply (ah_mpres_trans H HH); [| exact MP3];
            eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI4|].
    split. { eapply ACONST_frame; [exact AC3| exact MU4| exact WM4|]. constructor; [| constructor]. eapply aconst_ok_aapp; [exact BR7| cbn; lia| cbn; lia]. }
    split. { apply (rw_cells_transport asegs _ m3 m4 _ _ FR3) in MU4 as FR4; [| exact WM4| cbn; lia].
             apply (stk_transport_disjoint asegs _ m3 m4 _ _ ST3) in MU4 as ST4; [| exact WM4| cbn; lia].
             unfold sd_frame in FR4. release_frame FR4 ST4 (bv_unsigned sp). exact ST4. }
    split. { rewrite unsigned_lit by (unfold ATP; lia). eapply errno_across; [exact ERR2| exact MU34| exact WM34| unfold ATP; cbn; lia]. }
    split. { eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU34| exact WM34| exact CW3]. }
    split.
    { eapply xpres_trans; [exact XP1|]. eapply xpres_trans.
      - eapply (xpres_weaken H LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto].
      - eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU34| exact WM34|].
        constructor; [right; left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU34| exact WM34| exact CW3]. }
    split.
    { apply (rw_cells_transport asegs _ m3 m4 _ _ BLK3) in MU4 as BLK4; [| exact WM4| cbn; lia].
      change [CB (strnlen bs) (firstn (strnlen bs) bs); C1 (b8 0)] with ([CB (strnlen bs) (firstn (strnlen bs) bs)] ++ [C1 (b8 0)]).
      apply rw_cells_app. cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact BLK4| exact NUL4]. }
    split. { eapply addressable_transport; [exact ADDR3| exact MU4| exact WM4|]. cbn. destruct BR7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    split; [eapply MEMFLAG_across; [exact MU34| exact WM34| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU34| exact WM34| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    split; [eapply GOT_across; [exact MU34| exact WM34| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]|].
    exact AL2.
  Qed.
End W.
