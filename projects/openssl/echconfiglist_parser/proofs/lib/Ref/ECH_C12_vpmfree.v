(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState
     ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C5_stmt ECH_C5_small ECH_C5_popfree ECH_C12_stmt ECH_C12_xbuf.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition VF_R1 : Z := 0x1e1560.     (* [comment removed for export] *)
Definition VF_R2 : Z := 0x1e1570.     (* [comment removed for export] *)
Definition VF_R3 : Z := 0x1e15d8.     (* [comment removed for export] *)
Definition VF_T1 : Z := 0xde5fc.
Definition VPM_FILE : Z := 0x3713c.
Definition vf_frame (j : list byte) (s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition vpm_cells_h (h : Z) : list cell :=
  [CB 36 (zeros 36); C4 (wz 0); C8 (wz 18446744073709551615); C8 (wz 0); C8 (wz h); C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Lemma vpm_cells_h_eq : forall V, vpm_cells V = vpm_cells_h (vp_hosts V).
Proof. intros V. reflexivity. Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma vf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p h lo : Z),
      rw_cells rsegs m p (vpm_cells_h h) -> 0 < p -> p + VPM_SIZE <= lo -> 0 <= h < 2^64 -> GOT_x509vpm m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 j,
          ms' = MS (mkR (Z_to_bv 64 VF_R1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 sp (Z_to_bv 64 p)
                       (Z_to_bv 64 h) (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) b2 b3 b4 b5 b6 b7
                       (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -48) (vf_frame j s3 s2 s1 s0 ra)
          /\ rw_cells rsegs m1 p (vpm_cells_h h) /\ GOT_x509vpm m1)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_X509_VERIFY_PARAM_free) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros BLK POS BL HR GG ST CEIL LO MI.
    unfold P_X509_VERIFY_PARAM_free, P_OPENSSL_sk_set_thunks, P_sk_X509_BUFFER_freefunc_thunk, VF_R1.
    unfold vpm_cells_h, wz in BLK. unfold VPM_SIZE in *. unfold GOT_x509vpm, A_got_ASN1_OBJECT_free, P_ASN1_OBJECT_free, wz in GG.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    carve_frame 48%nat ST.
    do 8 step. do 4 step.
    eapply evt_cut.
    { pose proof sk_pop_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    do 5 step.
    finish. all: try exact FR.
    all: unfold GOT_x509vpm, A_got_ASN1_OBJECT_free, P_ASN1_OBJECT_free, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma vf_seg1n :
    forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 VF_R2) sp gp tp u0 u1 u2 s0 s1
                       (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 P_buffer_free) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 VF_R2) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 VF_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI.
    unfold P_sk_X509_BUFFER_freefunc_thunk, VF_R1, VF_R2, P_buffer_free.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { pose proof skset_thunks_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    do 4 step.
    eapply evt_cut.
    { pose proof sk_pop_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma vf_seg1s :
    forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (h lo : Z) (K : skrep),
      SKobj LB m h K -> SK_below h K lo ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 VF_R2) sp gp tp u0 u1 u2 s0 s1
                       (Z_to_bv 64 h) (Z_to_bv 64 P_buffer_free) b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 P_buffer_free) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (h, h + SK_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ SKobj LB m1 h (sk_with_thunk K O_SK_FREETH P_sk_X509_BUFFER_freefunc_thunk))
        (MS (mkR (Z_to_bv 64 VF_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom rsegs)).
  Proof.
    intros until K. intros SO BEL ST CEIL LO MI.
    unfold VF_R1, VF_R2, P_buffer_free.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (h, h + SK_SIZE)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold SK_SIZE in MU.
    eapply evt_cut.
    { pose proof skset_thunks_spec as Q; hnf in Q; eapply Q with (lo := lo) (LB := LB) (K := K); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold P_sk_X509_BUFFER_freefunc_thunk; lia); try lia. }
    intros ms_ PO_; unfold SK_SIZE in PO_; revert ms_ PO_.
    land MU WM.
    do 4 step.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma vf_seg2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p h lo : Z) (j : list byte),
      rw_cells rsegs m p (vpm_cells_h h) -> 0 < p -> p + VPM_SIZE <= lo -> (p + VPM_SIZE <= 0x10000 \/ 0x311000 <= p) ->
      rw_cells rsegs m (bv_unsigned sp + -48) (vf_frame j s3 s2 s1 s0 ra) ->
      IMPL_mem m -> GOT_mem m ->
      stk rsegs m lo (bv_unsigned sp + -48) -> hceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR ra sp gp tp u0 (Z_to_bv 64 VF_T1) u2 s0 s1
                       (Z_to_bv 64 p) (Z_to_bv 64 VPM_FILE) (Z_to_bv 64 378) b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (p, p + VPM_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ rw_cells rsegs m1 p (vpm_cells_h 0) /\ IMPL_mem m1 /\ GOT_mem m1)
        (MS (mkR (Z_to_bv 64 VF_R2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) (Z_to_bv 64 P_buffer_free) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VF_R2) fc None m (seg_rom rsegs)).
  Proof.
    intros until j. intros BLK POS BL OFF FR IM GM ST CEIL LO MI.
    unfold VF_R2, VF_T1, VPM_FILE, P_sk_X509_BUFFER_freefunc_thunk, P_buffer_free, P_CRYPTO_free.
    unfold vpm_cells_h, wz in BLK. unfold VPM_SIZE in *. unfold vf_frame in FR.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (p, p + 136)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    step. st1. step. step.
    eapply evt_cut.
    { pose proof skset_thunks_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    step. step.
    eapply evt_cut.
    { pose proof sk_pop_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. st1. step. step.
    eapply evt_cut.
    { pose proof skset_thunks_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    step. step.
    eapply evt_cut.
    { pose proof sk_pop_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. st1. step. step.
    eapply evt_cut.
    { pose proof skset_thunks_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    step. step.
    eapply evt_cut.
    { pose proof sk_pop_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. st1. do 6 step.
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
    do 3 step. do 5 st1. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; assumption.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XB.
  Context {HCEIL : HeapCeil}.
  Lemma XBUFobj_LB_mono : forall LB LB' m p X, XBUFobj LB m p X -> (forall b, In b LB -> In b LB') -> XBUFobj LB' m p X.
  Proof. intros LB LB' m p X (HC & HIN & DP & LP & DIN) SUB. split; [exact HC|]. split; [apply SUB; exact HIN|]. split; [exact DP|]. split; [exact LP| apply SUB; exact DIN]. Qed.

  Lemma XBUFs_owned : forall LB m ps bs b,
    Forall2 (fun p X => XBUFobj LB m p X) ps bs -> In b (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine ps bs))) -> In b LB.
  Proof.
    intros LB m ps bs b F2. induction F2 as [|p X ps' bs' E F IH]; cbn [concat map combine fst snd]; [intros []|].
    intros Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (IH Hb)].
    exact (XBUFobj_owned_law LB m p X E b Hb).
  Qed.

  Lemma XBUFs_frame : forall LB LB1 LB' SP m m' ps bs,
    Forall2 (fun p X => XBUFobj LB m p X) ps bs ->
    (forall b, In b (concat (map (fun px => blocks_XBUF (fst px) (snd px)) (combine ps bs))) -> In b LB1) ->
    (forall b, In b LB1 -> In b LB') ->
    xpres LB1 SP [] m m' -> (forall b, In b LB1 -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => XBUFobj LB' m' p X) ps bs.
  Proof.
    intros LB LB1 LB' SP m m' ps bs F2. induction F2 as [|p X ps' bs' E F IH]; intros KEEP SUB XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP.
    constructor.
    - eapply XBUFobj_LB_mono; [| exact SUB]. eapply XBUFobj_frame_law; [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply KEEP. apply in_or_app. left. exact Hb.
    - apply IH; [| exact SUB| exact XP| exact BEL]. intros b Hb. apply KEEP. apply in_or_app. right. exact Hb.
  Qed.

  Lemma blocks_SK_with_thunk : forall a K w f, blocks_SK a (sk_with_thunk K w f) = blocks_SK a K.
  Proof. intros. reflexivity. Qed.
  Lemma sk_elems_with_thunk : forall K w f, sk_elems (sk_with_thunk K w f) = sk_elems K.
  Proof. intros. reflexivity. Qed.
  Lemma sk_free_thunk_set : forall K f, sk_free_thunk (sk_with_thunk K O_SK_FREETH f) = f.
  Proof. intros. reflexivity. Qed.
End XB.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma vpmfree_spec : vpmfree_stmt H.
  Proof.
    unfold vpmfree_stmt, efree_stmt_at. intros until errv.
    intros A0 VO ND HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM GG RAE. subst a0.
    unfold VPMFREE_STACK, FR_X509_VERIFY_PARAM_free, SKPOPFREE_STACK, XBUFFREE_STACK, FR_buffer_free, FR_sk_pop_free, CFREE_STACK, RFREE_STACK in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBL : forall q L b, In b (hs_lb_remove H q L) -> In b L) by (intros q L b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
    destruct VO as (VC & VIN & HO). rewrite vpm_cells_h_eq in VC.
    pose proof (HB _ VIN) as PBL. cbn [blk_addr blk_size fst snd] in PBL. unfold VPM_SIZE in PBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP VIN) as BRP. cbn [blk_addr blk_size fst snd] in BRP. unfold VPM_SIZE in BRP.
    destruct BRP as (POS & _ & _ & _ & OFF).
    assert (HR : 0 <= vp_hosts x < 2^64).
    { revert HO. unfold HOSTS. destruct (vp_hosts_o x) as [[K bs]|]; intros HO; [| lia].
      destruct HO as (HP0 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (HB _ KIN) as KBL. cbn [blk_addr blk_size fst snd] in KBL. unfold SK_SIZE in KBL. lia. }
    subst tp. rewrite errno_RATP in ERR.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply vf_seg1 with (lo := lo); [exact VC| exact POS| unfold VPM_SIZE; lia| exact HR| exact GG| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (u0 & u1 & u2 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1 & GG1).
    assert (XP1 : xpres LB (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    (* [comment removed for export] *)
    assert (MID : hs_SR H (fun c => exists (w0 w1 w2 c0 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 : word) m2 sx2 LB2,
                 cfg_ms c = MS (mkR (Z_to_bv 64 VF_R2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) w0 w1 w2 sp (Z_to_bv 64 p)
                                    c0 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) (Z_to_bv 64 P_buffer_free)
                                    s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                               F (Z_to_bv 64 VF_R2) fc None m2 (seg_rom rsegs)
                 /\ hs_KREL H sx2 (cfg_model c) /\ hs_MPRES H mo (cfg_model c) /\ mem_inv rsegs m2 /\ stk rsegs m2 lo (bv_unsigned sp + -48)
                 /\ rw_cells rsegs m2 RERRNO [C4 errv] /\ hs_rauxv_ok H m2 B
                 /\ hs_RHEAP H sx2 LB2 m2 /\ In (vp_id x, p, VPM_SIZE) LB2
                 /\ Permutation (blocks_HOSTS (vp_hosts x) (vp_hosts_o x) ++ LB2) LB
                 /\ (forall b, In b LB2 -> In b LB)
                 /\ xpres LB2 (bv_unsigned sp) [] m m2 /\ IMPL_mem m2 /\ GOT_mem m2 /\ GOT_x509vpm m2
                 /\ rw_cells rsegs m2 (bv_unsigned sp + -48) (vf_frame j s3 s2 s1 s0 ra)
                 /\ rw_cells rsegs m2 p (vpm_cells_h (vp_hosts x)))
             (mkCfg (MS (mkR (Z_to_bv 64 VF_R1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 p)
                       (Z_to_bv 64 (vp_hosts x)) (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) b2 b3 b4 b5 b6 b7
                       (Z_to_bv 64 P_sk_X509_BUFFER_freefunc_thunk) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                    F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m1 (seg_rom rsegs)) mo)).
    { revert HO ND. unfold HOSTS, blocks_VPM, blocks_HOSTS. destruct (vp_hosts_o x) as [[K bs]|]; intros HO ND.
      - (* [comment removed for export] *)
        destruct HO as (HPOS & SO & LEN & F2).
        set (h := vp_hosts x) in *.
        set (EB := concat (map (fun px : Z * xbufrep => blocks_XBUF (fst px) (snd px)) (combine (sk_elems K) bs))) in *.
        pose proof SO as SO0. destruct SO0 as (_ & _ & KIN & KNC & KCAP & _ & _ & KDAT).
        pose proof (HB _ KIN) as KBL. cbn [blk_addr blk_size fst snd] in KBL. unfold SK_SIZE in KBL.
        pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP KIN) as KBR. cbn [blk_addr blk_size fst snd] in KBR. unfold SK_SIZE in KBR.
        destruct KBR as (_ & _ & _ & _ & KOFF).
        assert (NDT : List.NoDup (map blk_id (blocks_SK h K ++ EB))).
        { cbn [map] in ND. inversion ND; subst. assumption. }
        assert (PK : blk_id (vp_id x, p, VPM_SIZE) <> blk_id (sk_id K, h, SK_SIZE)).
        { eapply nodup_ids_cons_ne; [exact ND|]. apply in_or_app. left. left. reflexivity. }
        cbn [blk_id fst snd] in PK.
        pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP VIN KIN PK) as DPK. cbn [blk_addr blk_size fst snd] in DPK. unfold VPM_SIZE, SK_SIZE in DPK.
        assert (SO1 : SKobj LB m1 h K).
        { eapply (SKobj_frame LB LB); [exact SO| intros b Hb; eapply SKobj_owned; [exact SO| exact Hb]| exact XP1]. }
        assert (BEL : SK_below h K lo).
        { split; [unfold SK_SIZE; lia|]. destruct KDAT as [[C0 _]|(_ & _ & _ & DIN & _)]; [left; exact C0| right].
          pose proof (HB _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL. lia. }
        eapply (sr_evt_krel H HH); [exact KREL| eapply vf_seg1s with (lo := lo) (LB := LB) (K := K); rewrite ?unsigned_lit by lia;
                                     [exact SO1| exact BEL| exact ST1| exact CEIL| lia| exact MI1]|].
        intros ms5 (w0 & w1 & w2 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & SO5).
        rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU5, ST5 by lia. unfold SK_SIZE in MU5.
        assert (XPh : xpres (hs_lb_remove H (sk_id K) LB) (bv_unsigned sp + -48) [] m1 m5).
        { eapply (xpres_of_munch_block H HH) with (hb := (sk_id K, h, SK_SIZE)); [exact HP1| exact KIN| lia| exact MU5| exact WM5|].
          cbn [blk_addr blk_size blk_id fst snd]. unfold SK_SIZE.
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
        assert (HP5 : hs_RHEAP H s LB m5).
        { eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU5| exact WM5|].
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (sk_id K, h, SK_SIZE). split; [exact KIN| cbn; unfold SK_SIZE; lia]. }
        assert (AUX5 : hs_rauxv_ok H m5 B).
        { eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU5| exact WM5|]. unfold RAUXV_CELL.
          apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
        apply (rw_cells_transport rsegs _ m1 m5 _ _ ERR1) in MU5 as ERR5; [| exact WM5| unfold RERRNO; cbn; lia].
        assert (IM5 : IMPL_mem m5) by (eapply IMPL_across; [exact MU5| exact WM5| unfold A_malloc_impl; cbn; lia| exact IM1]).
        assert (GM5 : GOT_mem m5) by (eapply GOT_across; [exact MU5| exact WM5| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM1]).
        assert (GG5 : GOT_x509vpm m5) by (eapply GOT_x509vpm_across; [exact MU5| exact WM5| unfold A_got_ASN1_OBJECT_free; cbn; lia| exact GG1]).
        apply (rw_cells_transport rsegs _ m1 m5 _ _ FR1) in MU5 as FR5; [| exact WM5| cbn; lia].
        apply (rw_cells_transport rsegs _ m1 m5 _ _ VC1) in MU5 as VC5; [| exact WM5| cbn; lia].
        assert (F25 : Forall2 (fun q X => XBUFobj LB m5 q X) (sk_elems K) bs).
        { eapply (XBUFs_frame LB (hs_lb_remove H (sk_id K) LB) LB (bv_unsigned sp) m m5); [exact F2| | exact (SUBL _ _)| |].
          - intros b Hb. fold EB in Hb.
            apply (proj2 (proj2 (proj2 (lb_remove_exact H HH _ _ _ _ (HH_RHEAP_blocks_nodup H HH _ _ _ HP) KIN)) b)).
            split; [eapply XBUFs_owned; [exact F2| exact Hb]|].
            intros E. eapply (nodup_ids_app_ne (blocks_SK h K) EB); [exact NDT| left; reflexivity| exact Hb| symmetry; exact E].
          - eapply xpres_trans; [eapply xpres_weaken; [exact XP1| lia| exact (SUBL _ _)| auto]|].
            eapply xpres_weaken; [exact XPh| lia| auto| auto].
          - intros b Hb. pose proof (HB b (SUBL _ _ _ Hb)). lia. }
        (* [comment removed for export] *)
        pose proof (popfree_hosts_spec H HH) as PF. unfold popfree_hosts_stmt, skpopfree_stmt_gen in PF.
        specialize (PF (xbuffree_spec H HH) XBUFobj_frame_law XBUFobj_owned_law GOT_x509vpm_frame ltac:(unfold P_buffer_free; lia) ltac:(reflexivity)).
        eapply (sr_seq H HH).
        { eapply PF with (a := h) (K := sk_with_thunk K O_SK_FREETH P_sk_X509_BUFFER_freefunc_thunk) (xs := bs) (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv);
            rewrite ?blocks_SK_with_thunk, ?sk_elems_with_thunk, ?sk_free_thunk_set, ?unsigned_lit, ?errno_RATP by lia; try reflexivity.
          all: try first [exact SO5| exact LEN| exact F25| exact NDT| exact HP5| exact KREL| exact AUX5| exact ST5| exact CEIL| exact ERR5| exact MI5| exact IM5| exact GM5| exact GG5].
          all: try (unfold is_sk_freefunc_thunk; right; right; reflexivity).
          all: unfold SKPOPFREE_STACK, XBUFFREE_STACK, FR_buffer_free, FR_sk_pop_free, CFREE_STACK, RFREE_STACK, VF_R2; try lia.
          all: rewrite unsigned_lit by lia; reflexivity. }
        intros [ms3 mo3] PO. unfold skpopfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c0' & c1' & c2' & c3' & c4' & c5' & c6' & c7' & v3 & v4 & v5 & v6 & m3 & s3' & LB3 &
                        -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & PERM3 & HP3 & XP3 & IM3 & GM3 & GG3).
        rewrite ?blocks_SK_with_thunk, ?sk_elems_with_thunk in PERM3. fold EB in PERM3.
        rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST3, XP3 by lia. rewrite errno_RATP in ERR3.
        replace (ret_pc (Z_to_bv 64 VF_R2)) with (Z_to_bv 64 VF_R2) by (symmetry; apply ret_pc_even; [unfold VF_R2; lia| reflexivity]).
        assert (SUB3 : forall b, In b LB3 -> In b LB) by (intros b Hb; eapply Permutation_in; [exact PERM3| apply in_or_app; right; apply in_or_app; right; exact Hb]).
        pose proof PERM3 as P3. rewrite app_assoc in P3.
        assert (VIN3 : In (vp_id x, p, VPM_SIZE) LB3).
        { eapply perm_in_rest; [exact P3| exact VIN|]. intros Kb. apply (nodup_ids_cons_ne _ _ _ ND Kb). reflexivity. }
        assert (SUBR : forall b, In b LB3 -> In b (hs_lb_remove H (sk_id K) LB)).
        { eapply (perm_rest_sub_remove H HH); [exact HP1| exact P3|]. apply in_or_app. left. left. reflexivity. }
        pose proof (HH_blocks_below H HH _ _ _ HP3) as HB3.
        apply (sr_done H HH). cbn [cfg_ms cfg_model].
        exists v0, v1, v2, c0', c1', c2', c3', c4', c5', c6', c7', v3, v4, v5, v6, m3, s3', LB3.
        split; [reflexivity|]. split; [exact KREL3|]. split; [exact MP3|]. split; [exact MI3|]. split; [exact ST3|].
        split; [exact ERR3|]. split; [exact AUX3|]. split; [exact HP3|]. split; [exact VIN3|].
        split; [first [exact P3| rewrite app_assoc; exact P3| rewrite <- app_assoc; exact P3]|]. split; [exact SUB3|].
        split.
        { eapply xpres_trans; [eapply xpres_weaken; [exact XP1| lia| exact SUB3| auto]|].
          eapply xpres_trans; [eapply xpres_weaken; [exact XPh| lia| exact SUBR| auto]|].
          eapply xpres_weaken; [exact XP3| lia| auto| auto]. }
        split; [exact IM3|]. split; [exact GM3|]. split; [exact GG3|].
        split. { eapply xpres_rw_cells'; [exact XP3| exact FR5| left; cbn; lia| constructor]. }
        eapply xpres_rw_cells'; [exact XP3| exact VC5| | constructor].
        right; right. exists (vp_id x, p, VPM_SIZE). split; [exact VIN3|]. cbn [blk_addr blk_size fst snd cells_size csize vpm_cells_h Nat.add]. unfold VPM_SIZE. lia.
      - (* [comment removed for export] *)
        rewrite HO in *.
        eapply (sr_evt_krel H HH); [exact KREL| eapply vf_seg1n with (lo := lo); rewrite ?unsigned_lit by lia; [exact ST1| exact CEIL| lia| exact MI1]|].
        intros ms2 (w0 & w1 & w2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
        rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU2, ST2 by lia.
        apply (sr_done H HH). cbn [cfg_ms cfg_model].
        exists w0, w1, w2, (Z_to_bv 64 0), c1, c2, c3, c4, c5, c6, c7, w3, w4, w5, w6, m2, s, LB.
        split; [reflexivity|]. split; [exact KREL|]. split; [apply (mpres_refl H HH)|]. split; [exact MI2|]. split; [exact ST2|].
        split; [eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2| unfold RERRNO; cbn; lia]|].
        split. { eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU2| exact WM2|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
        split. { eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU2| exact WM2|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [exact VIN|]. cbn [blocks_HOSTS app]. split; [apply Permutation_refl|]. split; [auto|].
        assert (XP2 : xpres LB (bv_unsigned sp) [] m1 m2).
        { eapply xpres_of_munch; [exact MU2| exact WM2| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [eapply xpres_trans; [exact XP1| exact XP2]|].
        split; [eapply IMPL_across; [exact MU2| exact WM2| unfold A_malloc_impl; cbn; lia| exact IM1]|].
        split; [eapply GOT_across; [exact MU2| exact WM2| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM1]|].
        split; [eapply GOT_x509vpm_across; [exact MU2| exact WM2| unfold A_got_ASN1_OBJECT_free; cbn; lia| exact GG1]|].
        split; [eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn; lia]|].
        eapply rw_cells_transport; [exact VC1| exact MU2| exact WM2| cbn; lia]. }
    eapply (sr_seq H HH); [exact MID|].
    intros [ms2 mo2] PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m2 & sx2 & LB2 &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HP2 & VIN2 & PERM2 & SUB2 & XP2 & IM2 & GM2 & GG2 & FR2 & VC2).
    pose proof (HH_blocks_below H HH _ _ _ HP2) as HB2.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply vf_seg2 with (lo := lo) (h := vp_hosts x);
      [exact VC2| exact POS| unfold VPM_SIZE; lia| unfold VPM_SIZE; exact OFF| exact FR2| exact IM2| exact GM2| exact ST2| exact CEIL| lia| exact MI2]|].
    intros ms3 (u0' & u2' & d3 & d4 & d5 & d6 & d7 & u3' & u4' & u5' & u6' & m3 & -> & MU3 & WM3 & MI3 & ST3 & VC3 & IM3 & GM3).
    unfold VPM_SIZE in MU3.
    assert (HP3 : hs_RHEAP H sx2 LB2 m3).
    { eapply (HH_RHEAP_frame H HH); [exact HP2| exact MU3| exact WM3|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (vp_id x, p, VPM_SIZE). split; [exact VIN2| cbn; unfold VPM_SIZE; lia]. }
    assert (AUX3 : hs_rauxv_ok H m3 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL.
      apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m2 m3 _ _ ERR2) in MU3 as ERR3; [| exact WM3| unfold RERRNO; cbn; lia].
    assert (GG3 : GOT_x509vpm m3) by (eapply GOT_x509vpm_across; [exact MU3| exact WM3| unfold A_got_ASN1_OBJECT_free; cbn; lia| exact GG2]).
    assert (XP3 : xpres (hs_lb_remove H (vp_id x) LB2) (bv_unsigned sp) [] m2 m3).
    { eapply (xpres_of_munch_block H HH) with (hb := (vp_id x, p, VPM_SIZE)); [exact HP2| exact VIN2| lia| exact MU3| exact WM3|].
      cbn [blk_addr blk_size blk_id fst snd]. unfold VPM_SIZE.
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB2) (s := sx2) (p := vp_id x) (n := VPM_SIZE); try reflexivity.
      all: try first [exact HP3| exact KREL2| exact VIN2| exact AUX3| exact SPB| exact ST3| exact CEIL| exact MI3| exact IM3| exact GM3| exact RAE].
      all: first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR3]. }
    intros [ms4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m4 & s4' &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & HEAP4 & IM4 & GM4).
    rewrite errno_RATP in ERR4.
    unfold efree_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, e0, e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m4, s4', (hs_lb_remove H (vp_id x) LB2).
    split; [reflexivity|]. split; [exact KREL4|]. split; [eapply (mpres_trans H HH); [exact MP2| exact MP4]|]. split; [exact MI4|]. split; [exact ST4|].
    split; [rewrite errno_RATP; exact ERR4|]. split; [exact AUX4|].
    split.
    { unfold blocks_VPM. cbn [app]. eapply Permutation_trans; [| exact PERM2].
      eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
      eapply (lb_remove_perm H HH); [exact HP2| exact VIN2]. }
    split; [exact HEAP4|].
    split.
    { eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| exact (SUBL _ _)| auto]|].
      eapply xpres_trans; [exact XP3| exact XP4]. }
    split; [exact IM4|]. split; [exact GM4|].
    eapply GOT_x509vpm_xpres; [exact XP4| constructor| exact GG3].
  Qed.
End W.
