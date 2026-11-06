(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_strlen ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState
     ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C1_dup ECH_C5_stmt ECH_C5_small ECH_C5_new ECH_C5_push ECH_C12_stmt ECH_C12_vpmfree.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AS_R1 : Z := 0x1e18e8.   Definition AS_R2 : Z := 0x1e190c.   Definition AS_R6 : Z := 0x1e1988.   Definition AS_R10 : Z := 0x1e19d0.
Definition VPMC_FILE : Z := 0x3713c.
Definition as_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition hosts_fresh (id did : bptr) : skrep :=
  mkSK [] 0 0 1 P_buffer_cmp P_sk_X509_BUFFER_cmp_thunk P_sk_X509_BUFFER_freefunc_thunk P_sk_X509_BUFFER_copy_thunk id did.
Lemma hosts_fresh_eq : forall id did,
  sk_with_thunk (sk_with_thunk (sk_with_thunk (sk_fresh P_buffer_cmp id did) O_SK_CMPTH P_sk_X509_BUFFER_cmp_thunk)
                               O_SK_COPYTH P_sk_X509_BUFFER_copy_thunk) O_SK_FREETH P_sk_X509_BUFFER_freefunc_thunk
  = hosts_fresh id did.
Proof. intros. reflexivity. Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma as_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ph name L lo : Z),
      0 <= ph < 2^64 -> 0 <= name < 2^64 -> 0 <= L < 2^64 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AS_R1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1
                       (Z_to_bv 64 16) (Z_to_bv 64 VPMC_FILE) (Z_to_bv 64 59) a3 a4 a5 a6 a7
                       (Z_to_bv 64 ph) (Z_to_bv 64 name) (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -48) (as_frame s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ph) (Z_to_bv 64 name) (Z_to_bv 64 L) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_add_string_to_buffer_stack) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros PHR NR LR ST CEIL LO MI. unfold P_add_string_to_buffer_stack, P_CRYPTO_zalloc, AS_R1, VPMC_FILE.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 48%nat ST.
    do 17 step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma as_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A1 name L : Z),
      0 < A1 < 2^64 -> 0 <= name < 2^64 -> 0 <= L < 2^64 ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 AS_R2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A1)
                       (Z_to_bv 64 name) (Z_to_bv 64 L) (Z_to_bv 64 VPMC_FILE) (Z_to_bv 64 62) a4 a5 a6 a7
                       s2 (Z_to_bv 64 name) (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_strndup) fc None m (seg_rom rsegs))
        (MS (mkR (Z_to_bv 64 AS_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A1) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 name) (Z_to_bv 64 L) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AS_R1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until L. intros A1R NR LR. unfold AS_R1, AS_R2, VPMC_FILE, P_CRYPTO_strndup.
    replace (ret_pc (Z_to_bv 64 0x1e18e8)) with (Z_to_bv 64 0x1e18e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    do 8 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma as_seg3 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a A1 A2 lo : Z) (ns slack : list byte),
      0 < A1 -> A1 + XBUF_SIZE <= lo -> (A1 + XBUF_SIZE <= 0x10000 \/ 0x311000 <= A1) ->
      0 < A2 -> A2 + zlength ns + 1 <= lo ->
      0 < a -> a + VPM_SIZE <= lo ->
      (A1 + XBUF_SIZE <= a \/ a + VPM_SIZE <= A1) ->
      rw_cells rsegs m A1 [C8 (wz 0); C8 (wz 0)] -> rw_cells rsegs m a (vpm_cells_h 0) ->
      bytes_at rsegs m A2 (ns ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) ns -> (- (A2 + zlength ns + 1)) mod 8 <= zlength slack ->
      1 <= zlength ns <= 255 ->
      IMPL_mem m -> GOT_mem m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 AS_R6) sp gp tp u0 u1 u2 s0 (Z_to_bv 64 A1)
                       (Z_to_bv 64 P_buffer_cmp) b1 b2 b3 b4 b5 b6 b7
                       (Z_to_bv 64 (a + O_VPM_HOSTS)) (Z_to_bv 64 0) (Z_to_bv 64 VPMC_FILE) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_OPENSSL_sk_new) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (A1, A1 + XBUF_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ rw_cells rsegs m1 A1 [C8 (wz A2); C8 (wz (zlength ns))] /\ rw_cells rsegs m1 a (vpm_cells_h 0)
          /\ IMPL_mem m1 /\ GOT_mem m1)
        (MS (mkR (Z_to_bv 64 AS_R2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A1) (Z_to_bv 64 A2) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (a + O_VPM_HOSTS)) s2x (Z_to_bv 64 (zlength ns)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AS_R2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until slack. intros A1P A1L A1OFF A2P A2L AP AL DJ XB BLK STR NONUL PAD LR IM GM ST CEIL LO MI.
    unfold AS_R2, AS_R6, VPMC_FILE, P_buffer_cmp, P_OPENSSL_sk_new, O_VPM_HOSTS.
    replace (ret_pc (Z_to_bv 64 0x1e190c)) with (Z_to_bv 64 0x1e190c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold wz in XB. unfold vpm_cells_h, wz in BLK. unfold XBUF_SIZE, VPM_SIZE in *. unfold zlength in *.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.
    pose proof (bytes_at_bound _ _ _ _ STR) as STRB. rewrite length_app in STRB. cbn [length] in STRB.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (A1, A1 + 16)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0). step. step.
    eapply evt_cut.
    { pose proof strlen_spec as Q; hnf in Q; eapply Q with (str := ns) (slack := slack); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
            replace c with false by (symmetry; rewrite bv_eqb_refl; reflexivity); cbv iota | _ => idtac end.
    step. st1. st1. step. step. step. do 6 step.
    eapply evt_cut.
    { pose proof cfree_null_evt_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ unfold IMPL_mem, A_malloc_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; assumption
              | unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; assumption ]. }
    land MU WM.
    match goal with K : IMPL_mem ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      unfold IMPL_mem, A_malloc_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz in K end.
    match goal with K : GOT_mem ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz in K end.
    (* [comment removed for export] *)
    do 5 step.
    eapply evt_cut.
    { pose proof cfree_null_evt_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ unfold IMPL_mem, A_malloc_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; assumption
              | unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; assumption ]. }
    land MU WM.
    (* [comment removed for export] *)
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. try if_lit.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
            replace c with false by (symmetry; rewrite bv_eqb_refl; reflexivity); cbv iota | _ => idtac end.
    do 3 step.
    finish.
    all: try (unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; assumption).
  Qed.

  (* [comment removed for export] *)
  Lemma as_seg4 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (A1 st lo : Z) (id did : bptr),
      SKobj LB m st (sk_fresh P_buffer_cmp id did) -> st + SK_SIZE <= lo -> 0 <= A1 < 2^64 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 AS_R10) sp gp tp u0 u1 u2 s0 (Z_to_bv 64 A1)
                       (Z_to_bv 64 st) (Z_to_bv 64 A1) b2 b3 b4 b5 b6 b7
                       s2 (Z_to_bv 64 st) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (st, st + SK_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ SKobj LB m1 st (hosts_fresh id did))
        (MS (mkR (Z_to_bv 64 AS_R6) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A1) (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7
                 s2 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AS_R6)) fc None m (seg_rom rsegs)).
  Proof.
    intros until did. intros SO BL A1R ST CEIL LO MI.
    unfold AS_R6, AS_R10, P_OPENSSL_sk_push.
    replace (ret_pc (Z_to_bv 64 0x1e1988)) with (Z_to_bv 64 0x1e1988) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof SO as SO'. destruct SO' as (_ & POS & _).
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (st, st + SK_SIZE)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold SK_SIZE in MU. unfold SK_SIZE in BL.
    assert (BEL : SK_below st (sk_fresh P_buffer_cmp id did) lo) by (split; [unfold SK_SIZE; lia| left; reflexivity]).
    (* [comment removed for export] *)
    do 5 step.
    eapply evt_cut.
    { pose proof skset_cmp_thunks_spec as Q; hnf in Q; eapply Q with (lo := lo) (LB := LB); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold P_sk_X509_BUFFER_cmp_thunk; lia); try lia. }
    intros ms_ PO_; unfold SK_SIZE in PO_; revert ms_ PO_.
    land MU WM.
    (* [comment removed for export] *)
    do 4 step.
    eapply evt_cut.
    { pose proof skset_copy_thunks_spec as Q; hnf in Q; eapply Q with (lo := lo) (LB := LB); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold P_sk_X509_BUFFER_copy_thunk; lia); try lia. }
    intros ms_ PO_; unfold SK_SIZE in PO_; revert ms_ PO_.
    land MU WM.
    (* [comment removed for export] *)
    do 4 step.
    eapply evt_cut.
    { pose proof skset_thunks_spec as Q; hnf in Q; eapply Q with (lo := lo) (LB := LB); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold P_sk_X509_BUFFER_freefunc_thunk; lia); try lia. }
    intros ms_ PO_; unfold SK_SIZE in PO_; revert ms_ PO_.
    land MU WM.
    (* [comment removed for export] *)
    step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    do 3 step.
    finish. all: rewrite <- hosts_fresh_eq; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma as_seg5 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s1x : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a st lo : Z),
      0 < a -> a + VPM_SIZE <= lo -> (a + VPM_SIZE <= 0x10000 \/ 0x311000 <= a) -> 0 <= st < 2^64 ->
      rw_cells rsegs m a (vpm_cells_h 0) ->
      rw_cells rsegs m (bv_unsigned sp + -48) (as_frame s4 s3 s2 s1 s0 ra) ->
      stk rsegs m lo (bv_unsigned sp + -48) -> hceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR ra sp gp tp u0 u1 u2 s0 s1
                       (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (ret_pc ra) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (a, a + VPM_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ rw_cells rsegs m1 a (vpm_cells_h st))
        (MS (mkR (Z_to_bv 64 AS_R10) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1x
                 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (a + O_VPM_HOSTS)) (Z_to_bv 64 st) (Z_to_bv 64 VPMC_FILE)
                 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AS_R10)) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros AP AL AOFF STR BLK FR ST CEIL LO MI.
    unfold AS_R10, VPMC_FILE, O_VPM_HOSTS.
    replace (ret_pc (Z_to_bv 64 0x1e19d0)) with (Z_to_bv 64 0x1e19d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold vpm_cells_h, wz in BLK. unfold VPM_SIZE in *. unfold as_frame in FR.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 136)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    step. try if_lit. step. st1. step. step. step. do 4 step.
    eapply evt_cut.
    { pose proof skset_thunks_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    do 3 step.
    eapply evt_cut.
    { pose proof sk_pop_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. step. step. try if_lit. step.
    step. do 6 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.

Lemma strnlen_full : forall ns, ~ In (Z_to_bv 8 0) ns -> strnlen ns = length ns.
Proof.
  induction ns as [|b ns IH]; intros NI; [reflexivity|]. cbn [strnlen length].
  destruct (bv_unsigned b =? 0) eqn:E.
  - exfalso. apply NI. left. apply Z.eqb_eq in E. apply bv_eq. rewrite E. reflexivity.
  - f_equal. apply IH. intros K. apply NI. right. exact K.
Qed.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let SLACK : RHEAP_slack_law H := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  Definition ADDSTR_BYTES (ns : list byte) : Z := XBUF_SIZE + (zlength ns + 1) + SK_SIZE + 32.

  Definition addstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (a : Z) (ns : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (st : Z) (K : skrep) (X : xbufrep) (NB : list block),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m m'
      /\ hs_RHEAP H s' (NB ++ LB) m'
      /\ rw_cells rsegs m' a (vpm_cells_h st) /\ HOSTS (NB ++ LB) m' st (Some (K, [X])) /\ xb_len X = zlength ns
      /\ Permutation (blocks_HOSTS st (Some (K, [X]))) NB
      /\ Z.of_nat (length NB) = 4 /\ lb_bytes NB = ADDSTR_BYTES ns /\ lb_big NB = 0
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition addstr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (a name v lo B : Z) (pa pn : bptr) (ns : list byte) (errv : word),
      a0 = Z_to_bv 64 (a + O_VPM_HOSTS) -> a1 = Z_to_bv 64 name -> a2 = Z_to_bv 64 (zlength ns) ->
      rw_cells rsegs m a (vpm_cells_h 0) -> In (pa, a, VPM_SIZE) LB ->
      In (pn, name, zlength ns + 1) LB -> bytes_at rsegs m name ns -> ~ In (Z_to_bv 8 0) ns -> 1 <= zlength ns <= 255 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + ADDSTR_BYTES ns <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 4 <= hs_LIVE_CNT_MAX H -> lb_big LB <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - ADDSTR_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (addstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a ns lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_add_string_to_buffer_stack) fc None m (seg_rom rsegs)) mo).

  Local Ltac errno_across ERR MU WM :=
    eapply (rw_cells_transport rsegs _ _ _ _ _ ERR MU WM); unfold RERRNO; hcb; cbn; lia.

  (* [comment removed for export] *)
  Lemma xpres_drop_fresh2 : forall s6 s8 (LB LBx LB2 LB3 : list block) m6 m8 m m' SP X p1' A1' n1 p2' A2' n2,
    hs_RHEAP H s6 ((p1', A1', n1) :: LB2) m6 -> hs_RHEAP H s8 ((p2', A2', n2) :: LB3) m8 ->
    (forall b, In b LB -> In b LB2) -> (forall b, In b LB -> In b LB3) -> (forall b, In b LB -> In b LBx) -> hceil <= SP ->
    xpres LBx SP (X ++ [(A1', A1' + n1); (A2', A2' + n2)]) m m' -> xpres LB SP X m m'.
  Proof.
    intros s6 s8 LB LBx LB2 LB3 m6 m8 m m' SP X p1' A1' n1 p2' A2' n2 H6 H8 S2 S3 SX CE XP.
    assert (MONO : forall L L' q, (forall b, In b L -> In b L') -> rclient_addr L SP q -> rclient_addr L' SP q).
    { intros L L' q SUB [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right]. exists b. split; [apply SUB; exact Hb| exact R]. }
    eapply xpres_reLB; [exact XP|]. intros q Hq C NX. split; [eapply MONO; [exact SX| exact C]|].
    rewrite rin_ivs_app. intros [K|K]; [exact (NX K)|]. cbn in K.
    pose proof (HH_fresh_outside H HH _ _ _ _ _ _ SP q H6 CE (MONO _ _ _ S2 C)) as O1.
    pose proof (HH_fresh_outside H HH _ _ _ _ _ _ SP q H8 CE (MONO _ _ _ S3 C)) as O2.
    lia.
  Qed.

  Lemma addstr_spec : addstr_stmt.
  Proof.
    unfold addstr_stmt. intros until errv.
    intros A0 A1 A2 BLK PIN NIN BS NONUL LR HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP MF IM GM RAE. subst a0 a1 a2.
    unfold ADDSTR_STACK, FR_add_string_to_buffer_stack, CSTRNDUP_STACK, SKNEW_STACK, SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK,
      CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, RREALLOC_STACK, FR_sk_new, FR_sk_insert, FR_sk_reserve,
      CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK in LO.
    unfold ADDSTR_BYTES, XBUF_SIZE, SK_SIZE in BUD.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (bytes_at_bound _ _ _ _ BS) as BSB. unfold zlength in *. set (L := Z.of_nat (length ns)) in *.
    pose proof (HB _ PIN) as PBL. cbn [blk_addr blk_size fst snd] in PBL. unfold VPM_SIZE in PBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP PIN) as PBR. cbn [blk_addr blk_size fst snd] in PBR. unfold VPM_SIZE in PBR.
    destruct PBR as (PPOS & _ & _ & _ & POFF). box POFF.
    pose proof (HB _ NIN) as NBL. cbn [blk_addr blk_size fst snd] in NBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP NIN) as NBR. cbn [blk_addr blk_size fst snd] in NBR. destruct NBR as (NPOS & _ & _ & _ & NOFF). box NOFF.
    subst tp. rewrite errno_RATP in ERR.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply as_seg1 with (lo := lo); [unfold O_VPM_HOSTS; lia| lia| unfold L; lia| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (XP1 : xpres LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. constructor; [left; cbn; lia| constructor]. }
    apply (rw_cells_transport rsegs _ m m1 _ _ BLK) in MU1 as BLK1; [| exact WM1| cbn; lia].
    (* [comment removed for export] *)
    pose proof (czalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (sr_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 16) (size := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: try first [exact KREL| exact ST1| exact CEIL| exact MI1].
      all: lazymatch goal with
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]
           | |- lb_bytes _ + _ <= _ => lia
           | |- lb_big _ + _ <= _ => rewrite big1_small by (unfold BIGB; lia); lia
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; constructor; [cbn; lia| constructor]
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; errno_across ERR MU1 WM1
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           end. }
    clear CZ. intros [ms2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A1 & p1 & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & BR1 & HEAP2 & XB2 & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2. change (16 * 1) with 16 in BR1, HEAP2, XB2.
    pose proof BR1 as (A1P & _ & _ & A1C & A1OFF). box A1OFF.
    set (LB1 := (p1, A1, 16) :: LB) in *.
    assert (SUB01 : forall b, In b LB -> In b LB1) by (intros b Hb; right; exact Hb).
    assert (XB2' : rw_cells rsegs m2 A1 [C8 (wz 0); C8 (wz 0)]).
    { eapply rw_cells_recut; [exact XB2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -48) (as_frame s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact FR1| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. }
    assert (BLK2 : rw_cells rsegs m2 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2); [exact BLK1| | unfold memflag_foot, A_mem_inited; constructor; [blia1 POFF| constructor]].
      right; right. exists (pa, a, VPM_SIZE). split; [exact PIN| cbn; unfold VPM_SIZE; lia]. }
    assert (BS2 : bytes_at rsegs m2 name ns).
    { eapply (xpres_bytes_at' _ _ _ _ _ _ _ XP2).
      - eapply bytes_at_transport; [exact BS| exact MU1| cbn; lia].
      - right; right. exists (pn, name, L + 1). split; [exact NIN| cbn; lia].
      - unfold memflag_foot, A_mem_inited; constructor; [blia1 NOFF| constructor]. }
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) a VPM_SIZE HEAP2
                  ltac:(right; right; exists (pa, a, VPM_SIZE); split; [exact PIN| cbn; lia]) ltac:(lia) ltac:(unfold VPM_SIZE; lia)) as DJ1.
    unfold VPM_SIZE in DJ1. box DJ1.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply as_seg2; unfold L; lia|].
    intros ms3 ->.
    (* [comment removed for export] *)
    pose proof (cstrndup_spec H HH) as SD. unfold cstrndup_stmt in SD.
    eapply (sr_seq H HH).
    { eapply SD with (lo := lo) (B := B) (LB := LB1) (s := s2') (v := 1) (bs := ns); unfold zlength; fold L; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HEAP2| exact KREL2| exact BS2| exact AUX2| exact ST2| exact CEIL| exact MI2| exact MF2| exact IM2| exact GM2].
      all: try (unfold L in *; lia).
      all: lazymatch goal with
           | |- xclient_range _ _ _ _ _ =>
               split; [right; right; exists (pn, name, L + 1); split; [apply SUB01; exact NIN| cbn; lia]|];
               unfold memflag_foot, A_mem_inited; constructor; [blia1 NOFF| constructor]
           | |- lb_bytes _ + _ <= _ => unfold LB1; rewrite lb_bytes_cons; cbn [blk_size snd]; unfold L; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB1; cbn [length]; lia
           | |- lb_big _ + _ <= _ => unfold LB1; rewrite lb_big_cons; cbn [blk_size snd]; rewrite !big1_small by (unfold BIGB, L; lia); lia
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR2
           | |- _ <= bv_unsigned _ + -48 - _ => unfold CSTRNDUP_STACK, CMALLOC_STACK, FR_CRYPTO_strndup, FR_CRYPTO_malloc, RMALLOC_STACK; lia
           | |- _ => idtac
           end. }
    clear SD. intros [ms4 mo4] PO. unfold cstrndup_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & errv4 & A2 & p2 & s4' &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & BR2 & HEAP4 & CP4 & MF4 & IM4 & GM4).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST4, XP4 by lia. rewrite errno_RATP in ERR4.
    pose proof (strnlen_full ns NONUL) as SL.
    cbv zeta in BR2, HEAP4, CP4. rewrite ?SL in BR2. rewrite ?SL in HEAP4. rewrite ?SL, ?firstn_all in CP4. fold L in BR2, HEAP4.
    pose proof BR2 as (A2P & _ & _ & A2C & A2OFF). box A2OFF.
    set (LB2 := (p2, A2, L + 1) :: LB1) in *.
    assert (SUB12 : forall b, In b LB1 -> In b LB2) by (intros b Hb; right; exact Hb).
    assert (XB4 : rw_cells rsegs m4 A1 [C8 (wz 0); C8 (wz 0)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact XB2'| | unfold memflag_foot, A_mem_inited; constructor; [blia1 A1OFF| constructor]].
      right; right. exists (p1, A1, 16). split; [left; reflexivity| cbn; lia]. }
    assert (BLK4 : rw_cells rsegs m4 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact BLK2| | unfold memflag_foot, A_mem_inited; constructor; [blia1 POFF| constructor]].
      right; right. exists (pa, a, VPM_SIZE). split; [apply SUB01; exact PIN| cbn; unfold VPM_SIZE; lia]. }
    assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -48) (as_frame s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP4); [exact FR2| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. }
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) a VPM_SIZE HEAP4
                  ltac:(right; right; exists (pa, a, VPM_SIZE); split; [apply SUB01; exact PIN| cbn; lia]) ltac:(lia) ltac:(unfold VPM_SIZE; lia)) as DJ2.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) A1 16 HEAP4
                  ltac:(right; right; exists (p1, A1, 16); split; [left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ3.
    unfold VPM_SIZE in DJ2. box DJ2. box DJ3.
    (* [comment removed for export] *)
    pose proof (SLACK _ _ _ _ _ _ HEAP4 ltac:(left; reflexivity)) as SLK.
    destruct (wr_at_bytes_off_image _ _ _ SLK ltac:(apply Z.mod_pos_bound; lia) ltac:(pose proof (Z.mod_pos_bound (- (A2 + (L + 1))) 8); blia1 A2OFF))
      as (slack & SLL & SLB). clear SLK.
    assert (STR4 : bytes_at rsegs m4 A2 (ns ++ Z_to_bv 8 0 :: slack)).
    { replace (ns ++ Z_to_bv 8 0 :: slack) with ((ns ++ [b8 0]) ++ slack) by (unfold b8; rewrite <- app_assoc; reflexivity).
      apply (proj2 (bytes_at_app rsegs m4 A2 (ns ++ [b8 0]) slack)). split.
      - pose proof (proj2 (proj1 CP4)) as CPB. cbn [cells_bytes cbytes app] in CPB. exact CPB.
      - rewrite length_app. cbn [length]. replace (A2 + Z.of_nat (length ns + 1)) with (A2 + (L + 1)) by (unfold L; lia). exact SLB. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply as_seg3 with (lo := lo) (a := a) (A1 := A1) (A2 := A2) (ns := ns) (slack := slack);
      unfold XBUF_SIZE, VPM_SIZE, zlength; fold L; rewrite ?unsigned_lit by lia;
      try first [exact XB4| exact BLK4| exact STR4| exact NONUL| exact IM4| exact GM4| exact ST4| exact CEIL| exact MI4]; try first [blia1 A1OFF| blia1 DJ1| unfold L in *; lia]|].
    intros ms5 (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & XB5 & BLK5 & IM5 & GM5).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU5, ST5 by lia. unfold XBUF_SIZE in MU5. unfold zlength in XB5. fold L in XB5.
    assert (HP5 : hs_RHEAP H s4' LB2 m5).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP4| exact MU5| exact WM5|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (p1, A1, 16). split; [apply SUB12; left; reflexivity| cbn; lia]. }
    assert (AUX5 : hs_rauxv_ok H m5 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5|]. unfold RAUXV_CELL.
      apply Forall_cons; [cbn; lia|]. apply Forall_cons; [blia1 A1OFF| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m4 m5 _ _ ERR4) in MU5 as ERR5; [| exact WM5| unfold RERRNO; blia1 A1OFF].
    apply (rw_cells_transport rsegs _ m4 m5 _ _ FR4) in MU5 as FR5; [| exact WM5| cbn; lia].
    assert (MF5 : MEMFLAG m5 1) by (eapply MEMFLAG_across; [exact MU5| exact WM5| unfold A_mem_inited; blia1 A1OFF| exact MF4]).
    assert (XP5 : xpres LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m4 m5).
    { eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU5| exact WM5|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (sknew_spec H HH) as SN. unfold sknew_stmt, sknew_stmt_gen in SN.
    eapply (sr_seq H HH).
    { eapply SN with (lo := lo) (B := B) (LB := LB2) (s := s4') (c := P_buffer_cmp) (v := 1); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact HP5| exact KREL4| exact AUX5| exact ST5| exact CEIL| exact MI5].
      all: try (split; [reflexivity| unfold P_buffer_cmp; lia]).
      all: try (unfold SKNEW_STACK, FR_sk_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia).
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => unfold LB2, LB1; rewrite !lb_bytes_cons; cbn [blk_size snd]; unfold SK_SIZE, L; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB2, LB1; cbn [length]; lia
           | |- lb_big _ <= _ => unfold LB2, LB1; rewrite !lb_big_cons; cbn [blk_size snd]; rewrite !big1_small by (unfold BIGB, L; lia); lia
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR5
           | |- C1env _ _ => split; [exact MF5| split; [exact IM5| exact GM5]]
           | |- bv_unsigned _ + -48 <= _ => lia
           | |- _ => idtac
           end. }
    clear SN. intros [ms6 mo6] PO. unfold sknew_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (x0 & x1 & x2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m6 & errv6 & st & id & did & s6' &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & XP6 & STP & HEAP6 & SO6 & (MF6 & IM6 & GM6)).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST6, XP6 by lia. rewrite errno_RATP in ERR6.
    set (LB3 := (id, st, SK_SIZE) :: LB2) in *.
    assert (HB6 := HH_blocks_below H HH _ _ _ HEAP6).
    pose proof (HB6 _ ltac:(left; reflexivity)) as STBL. cbn [blk_addr blk_size fst snd] in STBL. unfold SK_SIZE in STBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HEAP6 ltac:(left; reflexivity)) as STBR. cbn [blk_addr blk_size fst snd] in STBR. unfold SK_SIZE in STBR.
    destruct STBR as (_ & _ & _ & _ & STOFF). box STOFF.
    assert (SUB23 : forall b, In b LB2 -> In b LB3) by (intros b Hb; right; exact Hb).
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) a VPM_SIZE HEAP6
                  ltac:(right; right; exists (pa, a, VPM_SIZE); split; [apply SUB12, SUB01; exact PIN| cbn; lia]) ltac:(lia) ltac:(unfold VPM_SIZE; lia)) as DJ4.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) A1 16 HEAP6
                  ltac:(right; right; exists (p1, A1, 16); split; [apply SUB12; left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ5.
    unfold VPM_SIZE, SK_SIZE in DJ4, DJ5. box DJ4. box DJ5.
    assert (XB6 : rw_cells rsegs m6 A1 [C8 (wz A2); C8 (wz L)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact XB5| | unfold memflag_foot, A_mem_inited; constructor; [blia1 A1OFF| constructor]].
      right; right. exists (p1, A1, 16). split; [apply SUB12; left; reflexivity| cbn; lia]. }
    assert (BLK6 : rw_cells rsegs m6 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact BLK5| | unfold memflag_foot, A_mem_inited; constructor; [blia1 POFF| constructor]].
      right; right. exists (pa, a, VPM_SIZE). split; [apply SUB12, SUB01; exact PIN| cbn; unfold VPM_SIZE; lia]. }
    assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -48) (as_frame s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP6); [exact FR5| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply as_seg4 with (lo := lo) (LB := LB3); rewrite ?unsigned_lit by lia;
      [exact SO6| unfold SK_SIZE; lia| lia| exact ST6| exact CEIL| lia| exact MI6]|].
    intros ms7 (y0 & y1 & y2 & f2 & f3 & f4 & f5 & f6 & f7 & y3 & y4 & y5 & y6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & SO7).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU7, ST7 by lia. unfold SK_SIZE in MU7.
    assert (HP7 : hs_RHEAP H s6' LB3 m7).
    { eapply (HH_RHEAP_frame H HH); [exact HEAP6| exact MU7| exact WM7|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (id, st, SK_SIZE). split; [left; reflexivity| cbn; unfold SK_SIZE; lia]. }
    assert (AUX7 : hs_rauxv_ok H m7 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX6| exact MU7| exact WM7|]. unfold RAUXV_CELL.
      apply Forall_cons; [cbn; lia|]. apply Forall_cons; [blia1 STOFF| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m6 m7 _ _ ERR6) in MU7 as ERR7; [| exact WM7| unfold RERRNO; blia1 STOFF].
    apply (rw_cells_transport rsegs _ m6 m7 _ _ FR6) in MU7 as FR7; [| exact WM7| cbn; lia].
    apply (rw_cells_transport rsegs _ m6 m7 _ _ XB6) in MU7 as XB7; [| exact WM7| blia1 DJ5].
    apply (rw_cells_transport rsegs _ m6 m7 _ _ BLK6) in MU7 as BLK7; [| exact WM7| blia1 DJ4].
    assert (MF7 : MEMFLAG m7 1) by (eapply MEMFLAG_across; [exact MU7| exact WM7| unfold A_mem_inited; blia1 STOFF| exact MF6]).
    assert (IM7 : IMPL_mem m7) by (eapply IMPL_across; [exact MU7| exact WM7| unfold A_malloc_impl; blia1 STOFF| exact IM6]).
    assert (GM7 : GOT_mem m7) by (eapply GOT_across; [exact MU7| exact WM7| unfold A_got_CRYPTO_malloc; blia1 STOFF| exact GM6]).
    assert (XP7 : xpres LB2 (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m6 m7).
    { eapply (xpres_of_munch_fresh H HH); [exact HEAP6| lia| exact MU7| exact WM7|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; unfold SK_SIZE; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (skpush_spec H HH (proj1 (proj2 HX))) as PS. unfold skpush_stmt in PS.
    eapply (sr_seq H HH).
    { eapply PS with (lo := lo) (B := B) (LB := LB3) (s := s6') (a := st) (p := A1) (v := 1) (K := hosts_fresh id did); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact SO7| exact HP7| exact KREL6| exact AUX7| exact ST7| exact CEIL| exact MI7].
      all: lazymatch goal with
           | |- 0 < _ < _ => lia
           | |- sk_push_nocmp _ => right; left; reflexivity
           | |- sk_cap _ <= SK_CAP_MAX => cbn; unfold SK_CAP_MAX; lia
           | |- lb_bytes _ + _ <= _ => unfold SKPUSH_COST, sk_grow, LB3, LB2, LB1; cbn [sk_cap hosts_fresh]; rewrite !lb_bytes_cons; cbn [blk_size snd]; unfold SK_SIZE, L; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold LB3, LB2, LB1; cbn [length]; lia
           | |- lb_big _ + _ <= _ => unfold sk_grow, LB3, LB2, LB1; cbn [sk_cap hosts_fresh]; rewrite !lb_big_cons; cbn [blk_size snd]; rewrite !big1_small by (unfold BIGB, SK_SIZE, L; lia); lia
           | |- _ <= bv_unsigned _ + -48 - SKPUSH_STACK =>
               unfold SKPUSH_STACK, SKRESERVE_STACK, CARRAY_STACK, CREALLOC_ARRAY_STACK, CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, RREALLOC_STACK,
                 FR_sk_insert, FR_sk_reserve, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, RMALLOC_STACK; lia
           | |- rw_cells _ _ _ _ => rewrite errno_RATP; exact ERR7
           | |- C1env _ _ => split; [exact MF7| split; [exact IM7| exact GM7]]
           | |- bv_unsigned _ + -48 <= _ => lia
           | |- _ => idtac
           end. }
    clear PS. intros [ms8 mo8] PO. unfold skpush_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m8 & errv8 & s8' & LB4 & K' & data' & cap' & did' &
                    -> & KREL8 & MP8 & MI8 & ST8 & ERR8 & AUX8 & KEQ & PLB & HEAP8 & SO8 & XP8 & (v8 & (MF8 & IM8 & GM8) & VLE)).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST8, XP8 by lia. rewrite errno_RATP in ERR8.
    assert (V8 : v8 = 1) by (destruct MF8 as (fb8 & _ & _ & V01); lia). subst v8.
    destruct PLB as [(N1 & _)|[(_ & CAP4 & LB4E)|(C4 & _)]];
      [exfalso; unfold sk_num, sk_cap, hosts_fresh, zlength in N1; cbn in N1; lia| | exfalso; unfold sk_cap, hosts_fresh in C4; cbn in C4; lia].
    assert (ECAP : cap' = 4) by (rewrite KEQ in CAP4; unfold sk_cap, sk_after_push in CAP4; cbn in CAP4; exact CAP4). subst cap'.
    assert (EDAT : sk_data K' = data') by (rewrite KEQ; reflexivity).
    assert (EDID : sk_did K' = did') by (rewrite KEQ; reflexivity).
    rewrite EDAT, EDID in LB4E. subst LB4.
    assert (SFE : SK_foot st K' = [(st, st + SK_SIZE); (data', data' + 32)]) by (rewrite KEQ; reflexivity). rewrite SFE in XP8. clear SFE.
    assert (HB8 := HH_blocks_below H HH _ _ _ HEAP8).
    pose proof (HB8 _ ltac:(left; reflexivity)) as DBL. cbn [blk_addr blk_size fst snd] in DBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HEAP8 ltac:(left; reflexivity)) as DBR. cbn [blk_addr blk_size fst snd] in DBR.
    destruct DBR as (DPOS & _ & _ & _ & DOFF). box DOFF.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) a VPM_SIZE HEAP8
                  ltac:(right; right; exists (pa, a, VPM_SIZE); split; [apply SUB23, SUB12, SUB01; exact PIN| cbn; lia]) ltac:(lia) ltac:(unfold VPM_SIZE; lia)) as DJ6.
    pose proof (HH_fresh_disjoint_client H HH _ _ _ _ _ _ (bv_unsigned sp) A1 16 HEAP8
                  ltac:(right; right; exists (p1, A1, 16); split; [apply SUB23, SUB12; left; reflexivity| cbn; lia]) ltac:(lia) ltac:(lia)) as DJ7.
    unfold VPM_SIZE in DJ6. box DJ6. box DJ7.
    assert (XB8 : rw_cells rsegs m8 A1 [C8 (wz A2); C8 (wz L)]).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact XB7| |].
      - right; right. exists (p1, A1, 16). split; [right; apply SUB23, SUB12; left; reflexivity| cbn; lia].
      - unfold memflag_foot, A_mem_inited, SK_SIZE. apply Forall_cons; [blia1 A1OFF|]. apply Forall_cons; [blia1 DJ5|]. apply Forall_cons; [blia1 DJ7| apply Forall_nil]. }
    assert (BLK8 : rw_cells rsegs m8 a (vpm_cells_h 0)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact BLK7| |].
      - right; right. exists (pa, a, VPM_SIZE). split; [right; apply SUB23, SUB12, SUB01; exact PIN| cbn; unfold VPM_SIZE; lia].
      - unfold memflag_foot, A_mem_inited, SK_SIZE. apply Forall_cons; [blia1 POFF|]. apply Forall_cons; [blia1 DJ4|]. apply Forall_cons; [blia1 DJ6| apply Forall_nil]. }
    assert (FR8 : rw_cells rsegs m8 (bv_unsigned sp + -48) (as_frame s4 s3 s2 s1 s0 ra)).
    { eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP8); [exact FR7| left; cbn; lia|].
      unfold memflag_foot, A_mem_inited, SK_SIZE. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (XP08 : xpres LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m7 m8).
    { eapply (xpres_drop_fresh2 _ _ LB ((did', data', 32) :: LB3) LB2 LB3); [exact HEAP6| exact HEAP8| | | | lia|].
      - intros b Hb. apply SUB12, SUB01. exact Hb.
      - intros b Hb. apply SUB23, SUB12, SUB01. exact Hb.
      - intros b Hb. right. apply SUB23, SUB12, SUB01. exact Hb.
      - eapply xpres_weaken; [exact XP8| lia| auto|]. intros q Hq. rewrite !rin_ivs_app in *. cbn in Hq |- *. unfold SK_SIZE. tauto. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL8| eapply as_seg5 with (lo := lo) (a := a) (st := st);
      [lia| unfold VPM_SIZE; lia| unfold VPM_SIZE; blia1 POFF| lia| exact BLK8| exact FR8| exact ST8| exact CEIL| lia| exact MI8]|].
    intros ms9 (k0 & k1 & k2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & k3 & k4 & k5 & k6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & BLK9).
    unfold VPM_SIZE in MU9.
    assert (XP9 : xpres ((did', data', 32) :: LB3) (bv_unsigned sp) [(a, a + 136)] m8 m9).
    { eapply xpres_of_munch; [exact MU9| exact WM9| | exact HB8]. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; intros q Hq; lia| apply Forall_nil]. }
    apply (sr_done H HH). unfold addstr_post. cbn [cfg_ms cfg_model].
    exists k0, k1, k2, h1, h2, h3, h4, h5, h6, h7, k3, k4, k5, k6, m9, errv8, s8', st, K', (mkXB A2 L p1 p2),
           [(did', data', 32); (id, st, SK_SIZE); (p2, A2, L + 1); (p1, A1, 16)].
    split; [reflexivity|]. split; [exact KREL8|].
    split; [eapply (mpres_trans H HH); [exact MP2| eapply (mpres_trans H HH); [exact MP4| eapply (mpres_trans H HH); [exact MP6| exact MP8]]]|].
    split; [exact MI9|]. split; [exact ST9|].
    split; [rewrite errno_RATP; eapply rw_cells_transport; [exact ERR8| exact MU9| exact WM9| unfold RERRNO; blia1 POFF]|].
    split. { eapply (HH_rauxv_frame H HH); [exact AUX8| exact MU9| exact WM9|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [blia1 POFF| apply Forall_nil]. }
    split.
    { eapply xpres_trans; [exact XP1|]. eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| auto| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP4| lia| exact SUB01| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans; [exact XP5|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP6| lia| intros b Hb; apply SUB12, SUB01; exact Hb| intros q Hq; apply rin_ivs_app; left; exact Hq]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP7| lia| intros b Hb; apply SUB12, SUB01; exact Hb| auto]|].
      eapply xpres_trans; [exact XP08|].
      eapply xpres_weaken; [exact XP9| lia| intros b Hb; right; apply SUB23, SUB12, SUB01; exact Hb| intros q Hq; apply rin_ivs_app; right; unfold VPM_SIZE; exact Hq]. }
    split.
    { cbn [app]. unfold LB3, LB2, LB1 in HEAP8. eapply (HH_RHEAP_frame H HH); [exact HEAP8| exact MU9| exact WM9|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (pa, a, VPM_SIZE).
      split; [right; right; right; right; exact PIN| cbn; unfold VPM_SIZE; lia]. }
    split; [exact BLK9|].
    split.
    { cbn [app HOSTS]. unfold LB3, LB2, LB1 in SO8. split; [exact STP|]. split.
      - eapply (SKobj_frameX ((did', data', 32) :: (id, st, SK_SIZE) :: (p2, A2, L + 1) :: (p1, A1, 16) :: LB)); [exact SO8| intros b Hb; exact (SKobj_owned _ _ _ _ _ SO8 Hb)| exact XP9|].
        intros b Hb. unfold blocks_SK in Hb. rewrite KEQ in Hb. cbn in Hb. unfold SK_SIZE.
        destruct Hb as [<-|[<-|[]]]; cbn [blk_addr blk_size fst snd]; unfold SK_SIZE; (apply Forall_cons; [| apply Forall_nil]); [blia1 DJ4| blia1 DJ6].
      - rewrite KEQ. cbn [sk_elems sk_after_push hosts_fresh app length]. split; [reflexivity|].
        constructor; [| constructor]. unfold XBUFobj. cbn [xb_data xb_len xb_id xb_did].
        split; [eapply rw_cells_transport; [exact XB8| exact MU9| exact WM9| blia1 DJ1]|].
        split; [right; right; right; left; reflexivity|]. split; [lia|]. split; [unfold L; lia|]. right; right; left; reflexivity. }
    split; [reflexivity|].
    split.
    { unfold blocks_HOSTS, blocks_SK. rewrite KEQ. cbn -[Z.add Z.mul]. unfold SK_SIZE.
      replace (8 * 4) with 32 by reflexivity.
      eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_skip. apply perm_swap. }
    split; [reflexivity|]. split; [unfold ADDSTR_BYTES; rewrite !lb_bytes_cons; cbn [blk_size snd lb_bytes fold_right]; unfold XBUF_SIZE, SK_SIZE, zlength; fold L; lia|].
    split; [rewrite !lb_big_cons; cbn [blk_size snd lb_big fold_right]; rewrite !big1_small by (unfold BIGB, SK_SIZE, L; lia); reflexivity|].
    split; [eapply MEMFLAG_across; [exact MU9| exact WM9| unfold A_mem_inited; blia1 POFF| exact MF8]|].
    split; [eapply IMPL_across; [exact MU9| exact WM9| unfold A_malloc_impl; blia1 POFF| exact IM8]|].
    eapply GOT_across; [exact MU9| exact WM9| unfold A_got_CRYPTO_malloc; blia1 POFF| exact GM8].
  Qed.
End W.
