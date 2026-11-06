(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_malloc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
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

Lemma bytes_at_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof. intros m a bs n HB. rewrite <- (firstn_skipn n bs) in HB. apply bytes_at_app in HB. exact (proj1 HB). Qed.
Lemma big1_mono : forall a b, a <= b -> big1 a <= big1 b.
Proof. intros a b L. unfold big1. destruct (Z.ltb_spec BIGB a); destruct (Z.ltb_spec BIGB b); lia. Qed.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition MD_RA : Z := 0xde10c.           (* [comment removed for export] *)
  Definition MD_T1 : Z := 0x27912c.          (* [comment removed for export] *)
  Definition SD_RA1 : Z := 0xde038.          (* [comment removed for export] *)
  Definition SD_RA2 : Z := 0xde050.          (* [comment removed for export] *)

  Definition md_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition md1_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
      (F : bvmap 5 word) (fc : bv 32) (D n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 MD_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 n)
                   (Z_to_bv 64 n) a2 a3 a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom rsegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -32)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -32) (md_frame s2 s1 s0 ra).

  Lemma md_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (D n lo : Z),
      0 < D < 2^64 -> 1 <= n < 0x7ffffffc ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m ->
      evt rsegs (md1_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 F fc D n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros HD HN ST CEIL LO MI. hcb. unfold P_CRYPTO_memdup, P_CRYPTO_malloc.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    do 6 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 4 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 4 step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma md_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A D n : Z),
      0 < A < 2^64 ->
      rw_cells rsegs m (bv_unsigned sp + -32) (md_frame s2 s1 s0 ra) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 MD_T1) t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 D) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_memcpy) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 MD_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 n) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 MD_RA)) fc None m (seg_rom rsegs)).
  Proof.
    intros until n. intros HA FR MI. unfold MD_RA, MD_T1, P_memcpy.
    replace (ret_pc (Z_to_bv 64 0xde10c)) with (Z_to_bv 64 0xde10c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold md_frame in FR.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 9 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sd_loop : forall (k : nat) (i : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (sa : Z) (bs : list byte),
      Z.to_nat (zlength bs - i) = k -> 0 <= i < zlength bs ->
      bytes_at rsegs m sa bs -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists a1' a5',
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sa + (i + Z.of_nat (strnlen (skipn (Z.to_nat i) bs))))) a1' a2 a3
                                 (Z_to_bv 64 (sa + zlength bs)) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 0xde024) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sa + i)) (Z_to_bv 64 (zlength bs - i)) a2 a3 (Z_to_bv 64 (sa + zlength bs)) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xde00c) fc None m (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros until bs; intros HK HI BS MI; [unfold zlength in *; lia|].
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs m sa bs i b _ BS NTH ltac:(lia) eq_refl) as RD.
    step. zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      rewrite (strnlen_at_zero bs (Z.to_nat i) b NTH K0). replace (sa + (i + Z.of_nat 0)) with (sa + i) by lia.
      apply evt_done. eexists _, _. reflexivity.
    - rewrite (strnlen_at_nz bs (Z.to_nat i) b NTH K0).
      zstep. zstep. step. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        replace (Z.of_nat (length bs) - i + -1) with (Z.of_nat (length bs) - (i + 1)) by lia.
        replace (sa + i + 1) with (sa + (i + 1)) by lia.
        replace (sa + (i + Z.of_nat (S (strnlen (skipn (S (Z.to_nat i)) bs))))) with
                (sa + ((i + 1) + Z.of_nat (strnlen (skipn (Z.to_nat (i + 1)) bs)))) by (replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia; lia).
        eapply IH; [lia| | exact BS| exact MI]. revert K1. rewrite ?unsigned_lit by lia. lia.
      + (* [comment removed for export] *)
        step.
        assert (E : i + 1 = Z.of_nat (length bs)) by (revert K1; rewrite ?unsigned_lit by lia; lia).
        pose proof (strnlen_skipn_le bs (S (Z.to_nat i))) as SL.
        replace (sa + (i + Z.of_nat (S (strnlen (skipn (S (Z.to_nat i)) bs))))) with (sa + Z.of_nat (length bs)) by lia.
        apply evt_done. eexists _, _. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition sd1_post (sp gp tp t0 t1 t2 a2 a3 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
      (F : bvmap 5 word) (fc : bv 32) (sa : Z) (k : nat) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j a4' a5',
      ms' = MS (mkR (Z_to_bv 64 SD_RA1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 sa)
                   (Z_to_bv 64 (Z.of_nat k + 1)) a2 a3 a3 a4' a5' a6 a7 s2 (Z_to_bv 64 (Z.of_nat k)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom rsegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra).

  Lemma sd_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (sa lo : Z) (bs : list byte),
      0 < sa < 2^64 -> zlength bs < 2^31 ->
      bytes_at rsegs m sa bs -> (sa + zlength bs <= lo \/ bv_unsigned sp <= sa) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (sd1_post sp gp tp t0 t1 t2 a2 a3 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc sa (strnlen bs) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 (zlength bs)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_strndup) fc None m (seg_rom rsegs)).
  Proof.
    intros until bs. intros HS HL BS OFF ST CEIL LO MI. hcb. unfold P_CRYPTO_strndup, P_CRYPTO_malloc. unfold zlength in *.
    pose proof (word_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (strnlen_le bs) as SNL.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    pose proof BS as BS'. clear BS. change (id (bytes_at rsegs m sa bs)) in BS'.
    do 7 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (BS : bytes_at rsegs mx sa bs) by (unfold id in BS'; eapply bytes_at_transport; [exact BS'| exact MU| cbn; unfold zlength in *; lia]);
      rename mx into m0 end.
    clear BS'.
    (* [comment removed for export] *)
    assert (FIN : forall a1' a4' a5',
      evt rsegs (sd1_post sp gp tp t0 t1 t2 a2 a3 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc sa (strnlen bs) lo m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 sa)
                 (Z_to_bv 64 (sa + Z.of_nat (strnlen bs))) a1' a2 a3 a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xde024) fc None m0 (seg_rom rsegs))).
    { intros a1' a4' a5'. zstep. replace (sa + Z.of_nat (strnlen bs) + - sa) with (Z.of_nat (strnlen bs)) by lia.
      zstep. do 3 step. finish. exact FR. }
    cbv delta [mkR] in FIN.
    step. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (E0 : bs = []) by (destruct bs; [reflexivity| cbn [length] in K0; lia]).
      subst bs. cbn [strnlen Z.of_nat] in FIN. replace (sa + 0) with sa in FIN by lia. apply FIN.
    - zstep. step.
      eapply evt_cut.
      { replace (Z_to_bv 64 (Z.of_nat (length bs))) with (Z_to_bv 64 (zlength bs - 0)) by (unfold zlength; f_equal; lia).
        replace (Z_to_bv 64 sa) with (Z_to_bv 64 (sa + 0)) by (f_equal; lia).
        eapply (sd_loop (Z.to_nat (Z.of_nat (length bs))) 0); [unfold zlength; lia| unfold zlength; lia| exact BS| exact MI]. }
      intros ms' (a1' & a5' & ->). cbn [Z.to_nat skipn]. replace (sa + (0 + Z.of_nat (strnlen bs))) with (sa + Z.of_nat (strnlen bs)) by lia.
      replace (sa + 0) with sa by lia. apply FIN.
  Qed.

  (* [comment removed for export] *)
  Lemma sd_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A sa : Z) (k : nat),
      0 < A < 2^64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 SD_RA2) sp gp tp t0 t1 t2 s0x (Z_to_bv 64 sa) (Z_to_bv 64 A) (Z_to_bv 64 sa) (Z_to_bv 64 (Z.of_nat k)) a3 a4 a5 a6 a7
                                         (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat k)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_memcpy) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 SD_RA1) sp gp tp t0 t1 t2 s0x (Z_to_bv 64 sa) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2x (Z_to_bv 64 (Z.of_nat k)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 SD_RA1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until k. intros HA MI. unfold SD_RA1, SD_RA2, P_memcpy.
    replace (ret_pc (Z_to_bv 64 0xde038)) with (Z_to_bv 64 0xde038) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 5 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sd_seg3 :
    forall (sp gp tp t0 t1 t2 s0x a0x a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A sa : Z) (k : nat) (j z : list byte),
      0 < A -> A + Z.of_nat k + 1 < 2^64 ->
      rw_cells rsegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) ->
      rw_cells rsegs m (A + Z.of_nat k) [CB 1 z] ->
      (A + Z.of_nat k + 1 <= bv_unsigned sp + -48 \/ bv_unsigned sp <= A + Z.of_nat k) ->
      mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m',
                   ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (ret_pc ra) fc None m' (seg_rom rsegs)
                   /\ munch [(A + Z.of_nat k, A + Z.of_nat k + 1)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                   /\ rw_cells rsegs m' (A + Z.of_nat k) [C1 (b8 0)])
        (MS (mkR (Z_to_bv 64 SD_RA2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 sa) a0x a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat k)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 SD_RA2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until z. intros HA HK FR NUL DJ MI. unfold SD_RA2.
    replace (ret_pc (Z_to_bv 64 0xde050)) with (Z_to_bv 64 0xde050) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold cm_frame in FR.
    pose proof (munch_refl [(A + Z.of_nat k, A + Z.of_nat k + 1)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. set (Q := A + Z.of_nat k) in *. st1. subst Q.
    do 9 step. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport rsegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  (* [comment removed for export] *)
  Local Ltac cm_pre HP AUX ERR MF IM GM MU WM :=
    lazymatch goal with
    | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU| exact WM|]; constructor; [left; cbn; lia| constructor]
    | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]; unfold RAUXV_CELL; constructor; [cbn; lia| constructor]
    | |- rw_cells _ _ _ _ => subst; rewrite ?errno_RATP in *; errno_across ERR MU WM
    | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU| exact WM| unfold A_mem_inited; cbn; lia| exact MF]
    | |- IMPL_mem _ => eapply IMPL_across; [exact MU| exact WM| unfold A_malloc_impl; cbn; lia| exact IM]
    | |- GOT_mem _ => eapply GOT_across; [exact MU| exact WM| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
    | _ => lia
    end.

  Lemma cmemdup_spec : cmemdup_stmt H.
  Proof.
    unfold cmemdup_stmt. intros until errv.
    intros A0 A1 HN BS [CR CX] HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM.
    unfold CMEMDUP_STACK, CMALLOC_STACK, FR_CRYPTO_memdup, FR_CRYPTO_malloc, RMALLOC_STACK in LO. hcb. subst a0 a1.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rclient_range_off_frame _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ lo HP CR CEIL ltac:(lia)) as OFF.
    assert (DPOS : 0 < D).
    { destruct CR as [K|[K|(b & Hb & K1 & K2)]]; [lia| lia|].
      destruct (HH_RHEAP_block_range H HH _ _ _ _ HP Hb) as (R1 & _). lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply md_seg1; [lia| lia| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    eapply bytes_at_transport in BS; [| exact MU1| cbn; lia].
    (* [comment removed for export] *)
    pose proof (cmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (sr_seq H HH).
    { eapply CM with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (n := Z.of_nat (length bs)); rewrite ?unsigned_lit by lia; try reflexivity; try eassumption.
      all: try (unfold CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: cm_pre HP AUX ERR MF IM GM MU1 WM1. }
    intros [ms2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    eapply (xpres_bytes_at' _ _ _ _ _ _ _ XP2) in BS; [| eapply rclient_range_SP_mono; [exact CR| lia]| exact CX].
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ _ _ _ HEAP2 CR ltac:(lia) ltac:(lia)) as SEP.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply md_seg2; [lia| exact FR1| exact MI2]|].
    intros ms3 ->.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply memcpy_spec; rewrite ?unsigned_lit by lia; [exact BS| lia| exact BLK| lia| exact MI2]|].
    intros ms4 PO. unfold memcpy_post in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & BLK3 & BS3).
    rewrite !unsigned_lit in MU3 by lia. rewrite !unsigned_lit in BLK3 by lia. rewrite Nat2Z.id in BLK3.
    apply (sr_done H HH). unfold cmemdup_post. cbn [cfg_ms cfg_model]. unfold zlength.
    exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m3, errv2, A, p, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|].
    split. { unfold md_frame in FR1. release_frame FR1 ST2 (bv_unsigned sp).
             eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. subst tp. rewrite errno_RATP. unfold RERRNO. cbn. lia. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    split.
    { eapply xpres_trans; [exact XP1|]. eapply xpres_trans.
      - eapply (xpres_weaken LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto].
      - eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right. exists (p, A, Z.of_nat (length bs)). split; [left; reflexivity| cbn; lia]. }
    split; [exact BLK3|].
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2].
  Qed.

  Lemma cstrndup_spec : cstrndup_stmt H.
  Proof.
    unfold cstrndup_stmt. intros until errv.
    intros A0 HS A1 HL BS [CR CX] HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM.
    unfold CSTRNDUP_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_malloc, RMALLOC_STACK in LO. hcb. subst a0 a1.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rclient_range_off_frame _ (HH_RHEAP_block_range H HH) _ _ _ _ _ _ lo HP CR CEIL ltac:(lia)) as OFF.
    pose proof (strnlen_le bs) as KL. set (k := strnlen bs) in *.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply sd_seg1 with (lo := lo); [exact HS| unfold zlength; lia| exact BS| unfold zlength; lia| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & j & a4' & a5' & -> & MU1 & WM1 & MI1 & ST1 & FR1). subst k. set (k := strnlen bs) in *.
    assert (XP1 : xpres LB (bv_unsigned sp) memflag_foot m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    eapply bytes_at_transport in BS; [| exact MU1| cbn; lia].
    (* [comment removed for export] *)
    pose proof (cmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    pose proof (big1_mono (Z.of_nat k + 1) (Z.of_nat (length bs) + 1) ltac:(lia)) as BM.
    eapply (sr_seq H HH).
    { eapply CM with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (n := Z.of_nat k + 1); rewrite ?unsigned_lit by lia; try reflexivity; try eassumption.
      all: try (unfold CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: cm_pre HP AUX ERR MF IM GM MU1 WM1. }
    intros [ms2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    eapply (xpres_bytes_at' _ _ _ _ _ _ _ XP2) in BS; [| eapply rclient_range_SP_mono; [exact CR| lia]| exact CX].
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ _ _ _ HEAP2 CR ltac:(lia) ltac:(lia)) as SEP.
    pose proof (rw_cells_bound _ _ _ _ BLK) as BKB. cbn [cells_size csize Nat.add] in BKB.
    destruct (rw_cells_CB_split rsegs _ A (Z.to_nat (Z.of_nat k + 1)) k junk BLK ltac:(lia)) as [BK BZ]. clear BLK.
    replace (Z.to_nat (Z.of_nat k + 1) - k)%nat with 1%nat in BZ by lia.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply sd_seg2; [lia| exact MI2]|].
    intros ms3 ->.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply memcpy_spec with (src := firstn k bs); rewrite ?unsigned_lit by lia|].
    { apply bytes_at_firstn. exact BS. }
    { rewrite length_firstn. lia. }
    { rewrite Nat2Z.id. exact BK. }
    { lia. }
    { exact MI2. }
    intros ms4 PO. unfold memcpy_post in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & BLK3 & BS3).
    rewrite !unsigned_lit in MU3 by lia. rewrite !unsigned_lit in BLK3 by lia. rewrite Nat2Z.id in BLK3.
    apply (rw_cells_transport rsegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
    apply (rw_cells_transport rsegs _ m2 m3 _ _ BZ) in MU3 as BZ3; [| exact WM3| cbn; lia].
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply sd_seg3; [lia| lia| exact FR3| exact BZ3| lia| exact MI3]|].
    intros ms5 (m4 & -> & MU4 & WM4 & MI4 & NUL4).
    assert (MU34 : munch [(A, A + Z.of_nat k + 1)] m2 m4).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU4]]; intros x Hx; cbn in Hx |- *; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM3 WM4) as WM34.
    apply (sr_done H HH). unfold cstrndup_post. cbn [cfg_ms cfg_model]. subst k.
    do 14 eexists. exists m4, errv2, A, p, s'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI4|].
    split. { apply (rw_cells_transport rsegs _ m3 m4 _ _ FR3) in MU4 as FR4; [| exact WM4| cbn; lia].
             apply (stk_transport_disjoint rsegs _ m2 m4 _ _ ST2) in MU34 as ST4; [| exact WM34| cbn; lia].
             unfold cm_frame in FR4. release_frame FR4 ST4 (bv_unsigned sp). exact ST4. }
    split. { eapply rw_cells_transport; [exact ERR2| exact MU34| exact WM34|]. subst tp. rewrite errno_RATP. unfold RERRNO. cbn. lia. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU34| exact WM34|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    split.
    { eapply xpres_trans; [exact XP1|]. eapply xpres_trans.
      - eapply (xpres_weaken LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto].
      - eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU34| exact WM34|]. constructor; [right; left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU34| exact WM34|]. constructor; [| constructor]. right; right. exists (p, A, Z.of_nat (strnlen bs) + 1). split; [left; reflexivity| cbn; lia]. }
    split.
    { apply (rw_cells_transport rsegs _ m3 m4 _ _ BLK3) in MU4 as BLK4; [| exact WM4| cbn; lia].
      change [CB (strnlen bs) (firstn (strnlen bs) bs); C1 (b8 0)] with ([CB (strnlen bs) (firstn (strnlen bs) bs)] ++ [C1 (b8 0)]).
      apply rw_cells_app. cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact BLK4| exact NUL4]. }
    split; [eapply MEMFLAG_across; [exact MU34| exact WM34| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU34| exact WM34| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    eapply GOT_across; [exact MU34| exact WM34| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2].
  Qed.
End W.
