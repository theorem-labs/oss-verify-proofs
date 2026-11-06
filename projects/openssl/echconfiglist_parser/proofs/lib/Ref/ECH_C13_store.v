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
     ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C5_stmt ECH_C5_small ECH_C5_popfree ECH_C13_stmt ECH_C13_small ECH_C13_ext ECH_C13_entry.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SF_R1 : Z := 0x26c258.     (* [comment removed for export] *)
Definition SF_R2 : Z := 0x26c268.     (* [comment removed for export] *)
Definition SF_R3 : Z := 0x26c284.     (* [comment removed for export] *)
Definition SF_T1 : Z := 0xdf2a4.
(* [comment removed for export] *)
Definition store_cells_h (h : Z) : list cell := [C8 (wz h); C8 (wz 0); C8 (wz 0)].
(* [comment removed for export] *)
Definition blocks_ENTRIES {HCEIL : HeapCeil} (P : Z) (xs : option (skrep * list entrep)) : list block :=
  match xs with
  | None => []
  | Some (K, es) => blocks_SK P K ++ concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K) es))
  end.
Lemma blocks_STORE_eq {HCEIL : HeapCeil} : forall a S,
  blocks_STORE a S = (es_id S, a, STORE_SIZE) :: blocks_ENTRIES (es_entries S) (es_entries_o S).
Proof. intros a [h [[K es]|] i]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XN.
  Context {HCEIL : HeapCeil}.
  Lemma ENTRYobj_LB_mono : forall LB LB' m p X, ENTRYobj LB m p X -> (forall b, In b LB -> In b LB') -> ENTRYobj LB' m p X.
  Proof.
    intros LB LB' m p X (HC & HIN & O1 & O2 & O3 & O4 & XS) SUB. split; [exact HC|]. split; [apply SUB; exact HIN|].
    split; [eapply ofield_LB_mono; eauto|]. split; [eapply ofield_LB_mono; eauto|].
    split; [eapply ofield_LB_mono; eauto|]. split; [eapply ofield_LB_mono; eauto|].
    revert XS. unfold EXTS. destruct (en_exts_o X) as [[K es]|]; intros XS; [| exact XS].
    destruct XS as (X1 & SO & LEN & F2). split; [exact X1|]. split; [eapply SKobj_LB_mono; eauto|]. split; [exact LEN|].
    clear - F2 SUB. induction F2 as [|q E qs Es HE HF IH]; constructor; [eapply EXTobj_LB_mono; eauto| exact IH].
  Qed.

  Lemma ENTRYs_owned : forall LB m ps es b,
    Forall2 (fun p X => ENTRYobj LB m p X) ps es -> In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> In b LB.
  Proof.
    intros LB m ps es b F2. induction F2 as [|p X ps' es' E F IH]; cbn [concat map combine fst snd]; [intros []|].
    intros Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (IH Hb)].
    exact (ENTRYobj_owned_law LB m p X E b Hb).
  Qed.

  Lemma ENTRYs_frame : forall LB LB1 LB' SP m m' ps es,
    Forall2 (fun p X => ENTRYobj LB m p X) ps es ->
    (forall b, In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> In b LB1) ->
    (forall b, In b LB1 -> In b LB') ->
    xpres LB1 SP [] m m' ->
    (forall b, In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => ENTRYobj LB' m' p X) ps es.
  Proof.
    intros LB LB1 LB' SP m m' ps es F2. induction F2 as [|p X ps' es' E F IH]; intros KEEP SUB XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP, BEL.
    constructor.
    - eapply ENTRYobj_LB_mono; [| exact SUB]. eapply ENTRYobj_frame_law; [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply in_or_app. left. exact Hb.
    - apply IH; [| exact SUB| exact XP|]; intros b Hb; [apply KEEP| apply BEL]; apply in_or_app; right; exact Hb.
  Qed.

  Lemma ENTRIES_keep : forall LB LB' SP m m' P xs,
    ENTRIES LB m P xs -> (forall b, In b (blocks_ENTRIES P xs) -> In b LB') -> xpres LB' SP [] m m' ->
    (forall b, In b (blocks_ENTRIES P xs) -> blk_addr b + blk_size b <= SP) -> ENTRIES LB' m' P xs.
  Proof.
    intros LB LB' SP m m' P xs XS KEEP XP BEL. revert XS KEEP BEL. unfold ENTRIES, blocks_ENTRIES.
    destruct xs as [[K es]|]; intros XS KEEP BEL; [| exact XS].
    destruct XS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply SKobj_frame; [exact SO| intros b Hb; apply KEEP; apply in_or_app; left; exact Hb| exact XP].
    - split; [exact LEN|]. eapply (ENTRYs_frame LB LB' LB' SP m m'); [exact F2| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| auto| exact XP|].
      intros b Hb. apply BEL. apply in_or_app. right. exact Hb.
  Qed.
  Lemma ENTRIES_owned : forall LB m P xs b, ENTRIES LB m P xs -> In b (blocks_ENTRIES P xs) -> In b LB.
  Proof.
    intros LB m P xs b. unfold ENTRIES, blocks_ENTRIES. destruct xs as [[K es]|]; intros XS Hb; [| destruct Hb].
    destruct XS as (_ & SO & _ & F2). apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [eapply SKobj_owned; eauto| eapply ENTRYs_owned; eauto].
  Qed.
End XN.

(* [comment removed for export] *)
Section LAWS.
  Context {HCEIL : HeapCeil}.

  Lemma STOREobj_owned_law : EP_owned storerep STOREobj blocks_STORE.
  Proof.
    unfold EP_owned. intros LB m p x (HC & HIN & ENS) b Hb.
    rewrite blocks_STORE_eq in Hb. destruct Hb as [<-|Hb]; [exact HIN|].
    eapply ENTRIES_owned; [exact ENS| exact Hb].
  Qed.

  Lemma STOREobj_frame_law : EP_frame storerep STOREobj blocks_STORE.
  Proof.
    unfold EP_frame. intros LB LB' m m' p x SP SO KEEP XP BEL.
    pose proof SO as (HC & HIN & ENS).
    rewrite blocks_STORE_eq in KEEP, BEL.
    unfold STOREobj. split.
    { eapply xpres_rw_cells'; [exact XP| exact HC| | constructor].
      right; right. exists (es_id x, p, STORE_SIZE). split; [apply KEEP; left; reflexivity|].
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold STORE_SIZE. lia. }
    split; [apply KEEP; left; reflexivity|].
    eapply ENTRIES_keep; [exact ENS| intros b Hb; apply KEEP; right; exact Hb| exact XP| intros b Hb; apply BEL; right; exact Hb].
  Qed.
End LAWS.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma s_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p h lo : Z),
      rw_cells rsegs m p (store_cells_h h) -> 0 < p -> p + STORE_SIZE <= lo -> 0 <= h < 2^64 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 SF_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 p)
                       (Z_to_bv 64 h) (Z_to_bv 64 P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)
          /\ rw_cells rsegs m1 p (store_cells_h h))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_ECHSTORE_free) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros BLK POS BL HR ST CEIL LO MI.
    unfold P_OSSL_ECHSTORE_free, P_OPENSSL_sk_set_thunks, P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk, SF_R1.
    unfold store_cells_h, wz in BLK. unfold STORE_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    carve_frame 32%nat ST.
    do 7 step. step. do 4 step. finish.
    all: unfold store_cells_h, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma s_seg2n :
    forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      GOT_echfree m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 ra',
          ms' = MS (mkR ra' sp gp tp u0 u1 u2 s0 s1
                       (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 SF_R2) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp) /\ GOT_echfree m1)
        (MS (mkR (Z_to_bv 64 SF_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros GG ST CEIL LO MI.
    unfold P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk, SF_R1, SF_R2. unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz in GG.
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
    all: unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma s_seg2s :
    forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (h lo : Z) (K : skrep),
      SKobj LB m h K -> SK_below h K lo -> GOT_echfree m -> (h + SK_SIZE <= 0x10000 \/ 0x311000 <= h) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 ra',
          ms' = MS (mkR ra' sp gp tp u0 u1 u2 s0 s1
                       (Z_to_bv 64 h) (Z_to_bv 64 P_ossl_echstore_entry_free) b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (h, h + SK_SIZE)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ SKobj LB m1 h (sk_with_thunk K O_SK_FREETH P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk) /\ GOT_echfree m1 /\ ra' = Z_to_bv 64 SF_R2)
        (MS (mkR (Z_to_bv 64 SF_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 h) (Z_to_bv 64 P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom rsegs)).
  Proof.
    intros until K. intros SO BEL GG HOFF ST CEIL LO MI.
    unfold SF_R1, SF_R2, P_OPENSSL_sk_pop_free. unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz in GG |- *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (h, h + SK_SIZE)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold SK_SIZE in MU, HOFF.
    eapply evt_cut.
    { pose proof skset_thunks_spec as Q; hnf in Q; eapply Q with (lo := lo) (LB := LB) (K := K); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk; lia); try lia. }
    intros ms_ PO_; unfold skset_post, SK_SIZE in PO_; revert ms_ PO_.
    land MU WM.
    do 4 step.
    finish.
    all: try reflexivity; unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma s_seg3 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 rax : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (p h lo : Z),
      rw_cells rsegs m p (store_cells_h h) -> 0 < p -> p + STORE_SIZE <= lo ->
      rw_cells rsegs m (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra) ->
      IMPL_mem m -> GOT_mem m ->
      stk rsegs m lo (bv_unsigned sp + -32) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR ra sp gp tp u0 (Z_to_bv 64 SF_T1) u2 s0 s1
                       (Z_to_bv 64 p) (Z_to_bv 64 ECHS_FILE) (Z_to_bv 64 679) b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp + -32)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ rw_cells rsegs m1 p (store_cells_h h) /\ IMPL_mem m1 /\ GOT_mem m1)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
                 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SF_R2) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros BLK POS BL FR IM GM ST CEIL LO MI.
    unfold SF_R2, SF_T1, ECHS_FILE, P_CRYPTO_free.
    unfold store_cells_h, wz in BLK. unfold STORE_SIZE in *. unfold ef_frame in FR.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp + -32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    step. do 6 step.
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
    do 3 step. do 4 st1. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; assumption.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma storefree_spec : storefree_stmt H.
  Proof.
    unfold storefree_stmt, efree_stmt_at. intros until errv.
    intros A0 SO ND HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM GG RAE. subst a0.
    unfold STOREFREE_STACK, FR_OSSL_ECHSTORE_free, SKPOPFREE_STACK, ENTRYFREE_STACK, EXTFREE_STACK, FR_ossl_echstore_entry_free,
      FR_ossl_echext_free, FR_sk_pop_free, CFREE_STACK, RFREE_STACK, FR_EVP_PKEY_free in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    assert (SUBL : forall q L b, In b (hs_lb_remove H q L) -> In b L) by (intros q L b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
    pose proof SO as (SC & SIN & ENS). change (rw_cells rsegs m p (store_cells_h (es_entries x))) in SC.
    pose proof (HB _ SIN) as PBL. cbn [blk_addr blk_size fst snd] in PBL. unfold STORE_SIZE in PBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP SIN) as PBR. cbn [blk_addr blk_size fst snd] in PBR. unfold STORE_SIZE in PBR.
    destruct PBR as (POS & _ & _ & _ & POFF). box POFF.
    rewrite blocks_STORE_eq in ND.
    set (BX := blocks_ENTRIES (es_entries x) (es_entries_o x)) in *.
    assert (OWN : forall b, In b ((es_id x, p, STORE_SIZE) :: BX) -> In b LB).
    { intros b Hb. apply (STOREobj_owned_law LB m p x SO). rewrite blocks_STORE_eq. exact Hb. }
    assert (BELx : forall b, In b BX -> blk_addr b + blk_size b <= hceil) by (intros b Hb; apply HB; apply OWN; right; exact Hb).
    assert (RXS : 0 <= es_entries x < 2^64).
    { revert ENS. unfold ENTRIES. destruct (es_entries_o x) as [[K es]|]; intros ENS; [| lia].
      destruct ENS as (X1 & SKO & _). destruct SKO as (_ & _ & KIN & _). pose proof (HB _ KIN) as KB. cbn [blk_addr blk_size fst snd] in KB. unfold SK_SIZE in KB. lia. }
    subst tp. rewrite errno_RATP in ERR.
    pose proof ND as ND0. cbn [map] in ND0. inversion ND0 as [|i0 l0 NI NDt]; subst i0 l0. clear ND0.
    assert (NOTHD : forall Fr, (forall b, In b Fr -> In b BX) -> ~ In (es_id x, p, STORE_SIZE) Fr).
    { intros Fr SUB K. apply NI. rewrite in_map_iff. exists (es_id x, p, STORE_SIZE). split; [reflexivity| apply SUB; exact K]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply s_seg1 with (lo := lo); [exact SC| exact POS| unfold STORE_SIZE; lia| exact RXS| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SC1).
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (GG1 : GOT_echfree m1) by (eapply GOT_echfree_across; [exact MU1| exact WM1| unfold A_got_ossl_echext_free; cbn; lia| exact GG]).
    assert (XP1 : xpres LB (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (ENS1 : ENTRIES LB m1 (es_entries x) (es_entries_o x)).
    { eapply ENTRIES_keep; [exact ENS| intros b Hb; eapply ENTRIES_owned; [exact ENS| exact Hb]| exact XP1|].
      intros b Hb. pose proof (BELx b Hb). lia. }
    (* [comment removed for export] *)
    assert (MID : hs_SR H (fun c => exists (rax2 w0 w1 w2 c0 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 : word) m6 st6 LB6,
                 cfg_ms c = MS (mkR rax2 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 RATP) w0 w1 w2 sp (Z_to_bv 64 p)
                                    c0 c1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                               F (Z_to_bv 64 SF_R2) fc None m6 (seg_rom rsegs)
                 /\ hs_KREL H st6 (cfg_model c) /\ hs_MPRES H mo (cfg_model c) /\ mem_inv rsegs m6 /\ stk rsegs m6 lo (bv_unsigned sp + -32)
                 /\ rw_cells rsegs m6 RERRNO [C4 errv] /\ hs_rauxv_ok H m6 B
                 /\ hs_RHEAP H st6 LB6 m6 /\ In (es_id x, p, STORE_SIZE) LB6
                 /\ Permutation (BX ++ LB6) LB /\ (forall b, In b LB6 -> In b LB)
                 /\ xpres LB6 (bv_unsigned sp) [] m m6 /\ IMPL_mem m6 /\ GOT_mem m6 /\ GOT_echfree m6
                 /\ rw_cells rsegs m6 (bv_unsigned sp + -32) (ef_frame s2 s1 s0 ra)
                 /\ rw_cells rsegs m6 p (store_cells_h (es_entries x)))
             (mkCfg (MS (mkR (Z_to_bv 64 SF_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 p)
                       (Z_to_bv 64 (es_entries x)) (Z_to_bv 64 P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m1 (seg_rom rsegs)) mo)).
    { pose proof ENS1 as EN'. unfold ENTRIES in EN'.
      destruct (es_entries_o x) as [[K es]|] eqn:EXO; rewrite ?EXO in EN'.
      - (* [comment removed for export] *)
        destruct EN' as (HPOS & SKO & LEN & F2).
        set (h := es_entries x) in *.
        set (EB := concat (map (fun px : Z * entrep => blocks_ENTRY (fst px) (snd px)) (combine (sk_elems K) es))) in *.
        assert (BXE : BX = blocks_SK h K ++ EB) by (unfold BX, blocks_ENTRIES; rewrite ?EXO; reflexivity).
        pose proof NDt as NDX. rewrite BXE in NDX.
        pose proof SKO as SO0. destruct SO0 as (_ & _ & KIN & KNC & KCAP & _ & _ & KDAT).
        pose proof (HB _ KIN) as KBL. cbn [blk_addr blk_size fst snd] in KBL. unfold SK_SIZE in KBL.
        pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP1 KIN) as KBR. cbn [blk_addr blk_size fst snd] in KBR. unfold SK_SIZE in KBR.
        destruct KBR as (_ & _ & _ & _ & KOFF).
        assert (PK : blk_id (es_id x, p, STORE_SIZE) <> blk_id (sk_id K, h, SK_SIZE)).
        { intros E. apply NI. rewrite in_map_iff. exists (sk_id K, h, SK_SIZE). split; [symmetry; exact E|].
          rewrite BXE. apply in_or_app. left. left. reflexivity. }
        cbn [blk_id fst snd] in PK.
        pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP1 SIN KIN PK) as DPK. cbn [blk_addr blk_size fst snd] in DPK. unfold STORE_SIZE, SK_SIZE in DPK.
        assert (BEL : SK_below h K lo).
        { split; [unfold SK_SIZE; lia|]. destruct KDAT as [[C0 _]|(_ & _ & _ & DIN & _)]; [left; exact C0| right].
          pose proof (HB _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL. lia. }
        eapply (sr_evt_krel H HH); [exact KREL| eapply s_seg2s with (lo := lo) (LB := LB) (K := K); rewrite ?unsigned_lit by lia;
                                     [exact SKO| exact BEL| exact GG1| unfold SK_SIZE; exact KOFF| exact ST1| exact CEIL| lia| exact MI1]|].
        intros ms6a (y0 & y1 & y2 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6a & rax6 & -> & MU6a & WM6a & MI6a & ST6a & SO6a & GG6a & ->).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in MU6a, ST6a by lia. unfold SK_SIZE in MU6a.
        box KOFF. box DPK.
        assert (XPh : xpres (hs_lb_remove H (sk_id K) LB) (bv_unsigned sp + -32) [] m1 m6a).
        { eapply (xpres_of_munch_block H HH) with (hb := (sk_id K, h, SK_SIZE)); [exact HP1| exact KIN| lia| exact MU6a| exact WM6a|].
          cbn [blk_addr blk_size blk_id fst snd]. unfold SK_SIZE.
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; lia| apply Forall_nil]. }
        assert (HP6a : hs_RHEAP H s LB m6a).
        { eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU6a| exact WM6a|].
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil]. right; right. exists (sk_id K, h, SK_SIZE). split; [exact KIN| cbn; unfold SK_SIZE; lia]. }
        assert (AUX6a : hs_rauxv_ok H m6a B).
        { eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU6a| exact WM6a|]. unfold RAUXV_CELL.
          apply Forall_cons; [cbn; lia|]. apply Forall_cons; [blia1 KOFF| apply Forall_nil]. }
        apply (rw_cells_transport rsegs _ m1 m6a _ _ ERR1) in MU6a as ERR6a; [| exact WM6a| unfold RERRNO; blia1 KOFF].
        assert (IM6a : IMPL_mem m6a) by (eapply IMPL_across; [exact MU6a| exact WM6a| unfold A_malloc_impl; blia1 KOFF| exact IM1]).
        assert (GM6a : GOT_mem m6a) by (eapply GOT_across; [exact MU6a| exact WM6a| unfold A_got_CRYPTO_malloc; blia1 KOFF| exact GM1]).
        apply (rw_cells_transport rsegs _ m1 m6a _ _ FR1) in MU6a as FR6a; [| exact WM6a| cbn; lia].
        apply (rw_cells_transport rsegs _ m1 m6a _ _ SC1) in MU6a as SC6a; [| exact WM6a| unfold store_cells_h; blia1 DPK].
        assert (F26a : Forall2 (fun q X => ENTRYobj LB m6a q X) (sk_elems K) es).
        { eapply (ENTRYs_frame LB (hs_lb_remove H (sk_id K) LB) LB (bv_unsigned sp + -32) m1 m6a); [exact F2| | exact (SUBL _ _)| exact XPh|].
          - intros b Hb. fold EB in Hb.
            apply (proj2 (proj2 (proj2 (lb_remove_exact H HH _ _ _ _ (HH_RHEAP_blocks_nodup H HH _ _ _ HP1) KIN)) b)).
            split; [eapply ENTRYs_owned; [exact F2| exact Hb]|].
            intros E. eapply (nodup_ids_app_ne (blocks_SK h K) EB); [exact NDX| left; reflexivity| exact Hb| symmetry; exact E].
          - intros b Hb. fold EB in Hb.
            assert (HbX : In b BX) by (rewrite BXE; apply in_or_app; right; exact Hb).
            pose proof (BELx b HbX). lia. }
        (* [comment removed for export] *)
        pose proof (popfree_entries_spec H HH) as PF. unfold popfree_entries_stmt, skpopfree_stmt_gen in PF.
        specialize (PF (entryfree_spec H HH) ENTRYobj_frame_law ENTRYobj_owned_law GOT_echfree_frame ltac:(unfold P_ossl_echstore_entry_free; lia) ltac:(reflexivity)).
        eapply (sr_seq H HH).
        { eapply PF with (a := h) (K := sk_with_thunk K O_SK_FREETH P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk) (xs := es) (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv);
            rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk, ?e_sk_free_thunk_set, ?unsigned_lit, ?errno_RATP by lia; try reflexivity.
          all: try first [exact SO6a| exact LEN| exact F26a| exact NDX| exact HP6a| exact KREL| exact AUX6a| exact ST6a| exact CEIL| exact ERR6a| exact MI6a| exact IM6a| exact GM6a| exact GG6a].
          all: try (unfold is_sk_freefunc_thunk; right; left; reflexivity).
          all: unfold SKPOPFREE_STACK, ENTRYFREE_STACK, EXTFREE_STACK, FR_ossl_echstore_entry_free, FR_ossl_echext_free, FR_sk_pop_free,
                 CFREE_STACK, RFREE_STACK, FR_EVP_PKEY_free, SF_R2; try lia.
          all: rewrite unsigned_lit by lia; reflexivity. }
        clear PF. intros [ms6 mo6] PO. unfold skpopfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & c0' & c1' & c2' & c3' & c4' & c5' & c6' & c7' & v3 & v4 & v5 & v6 & m6 & st6 & LB6 &
                        -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & PERM6 & HP6 & XP6 & IM6 & GM6 & GG6).
        rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk in PERM6. fold EB in PERM6.
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST6, XP6 by lia. rewrite errno_RATP in ERR6.
        replace (ret_pc (Z_to_bv 64 SF_R2)) with (Z_to_bv 64 SF_R2) by (symmetry; apply ret_pc_even; [unfold SF_R2; lia| reflexivity]).
        pose proof PERM6 as P6. rewrite app_assoc in P6.
        assert (SUB6 : forall b, In b LB6 -> In b LB) by (intros b Hb; eapply Permutation_in; [exact P6| apply in_or_app; right; exact Hb]).
        assert (SIN6 : In (es_id x, p, STORE_SIZE) LB6).
        { eapply perm_in_rest; [exact P6| exact SIN|]. apply NOTHD. intros b Hb. rewrite BXE. exact Hb. }
        assert (SUBR : forall b, In b LB6 -> In b (hs_lb_remove H (sk_id K) LB)).
        { eapply (perm_rest_sub_remove H HH); [exact HP1| exact P6|]. apply in_or_app. left. left. reflexivity. }
        apply (sr_done H HH). cbn [cfg_ms cfg_model].
        exists (Z_to_bv 64 SF_R2), v0, v1, v2, c0', c1', c2', c3', c4', c5', c6', c7', v3, v4, v5, v6, m6, st6, LB6.
        split; [reflexivity|]. split; [exact KREL6|]. split; [exact MP6|]. split; [exact MI6|]. split; [exact ST6|].
        split; [exact ERR6|]. split; [exact AUX6|]. split; [exact HP6|]. split; [exact SIN6|].
        split; [rewrite BXE; first [exact P6| rewrite app_assoc; exact P6| rewrite <- app_assoc; exact P6]|]. split; [exact SUB6|].
        split.
        { eapply xpres_trans; [eapply xpres_weaken; [exact XP1| lia| exact SUB6| auto]|].
          eapply xpres_trans; [eapply xpres_weaken; [exact XPh| lia| exact SUBR| auto]|].
          eapply xpres_weaken; [exact XP6| lia| auto| auto]. }
        split; [exact IM6|]. split; [exact GM6|]. split; [exact GG6|].
        split; [eapply xpres_rw_cells'; [exact XP6| exact FR6a| left; cbn; lia| constructor]|].
        eapply xpres_rw_cells'; [exact XP6| exact SC6a| | constructor].
        right; right. exists (es_id x, p, STORE_SIZE). split; [exact SIN6|].
        unfold store_cells_h. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold STORE_SIZE. lia.
      - (* [comment removed for export] *)
        assert (BXE : BX = []) by (unfold BX, blocks_ENTRIES; rewrite ?EXO; reflexivity).
        rewrite EN' in *.
        eapply (sr_evt_krel H HH); [exact KREL| eapply s_seg2n with (lo := lo); rewrite ?unsigned_lit by lia; [exact GG1| exact ST1| exact CEIL| lia| exact MI1]|].
        intros ms6 (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6 & rax6 & -> & MU6 & WM6 & MI6 & ST6 & GG6).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in MU6, ST6 by lia.
        apply (sr_done H HH). cbn [cfg_ms cfg_model].
        exists rax6, y0, y1, y2, (Z_to_bv 64 0), c1, c2, c3, c4, c5, c6, c7, y3, y4, y5, y6, m6, s, LB.
        split; [reflexivity|]. split; [exact KREL|]. split; [apply (mpres_refl H HH)|]. split; [exact MI6|]. split; [exact ST6|].
        split; [eapply rw_cells_transport; [exact ERR1| exact MU6| exact WM6| unfold RERRNO; cbn; lia]|].
        split. { eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU6| exact WM6|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
        split. { eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU6| exact WM6|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [exact SIN|]. rewrite BXE. cbn [app]. split; [apply Permutation_refl|]. split; [auto|].
        split. { eapply xpres_trans; [exact XP1|]. eapply xpres_of_munch; [exact MU6| exact WM6| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [eapply IMPL_across; [exact MU6| exact WM6| unfold A_malloc_impl; cbn; lia| exact IM1]|].
        split; [eapply GOT_across; [exact MU6| exact WM6| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM1]|].
        split; [exact GG6|].
        split; [eapply rw_cells_transport; [exact FR1| exact MU6| exact WM6| cbn; lia]|].
        eapply rw_cells_transport; [exact SC1| exact MU6| exact WM6| unfold store_cells_h; cbn; lia]. }
    eapply (sr_seq H HH); [exact MID|].
    intros [ms6 mo6] PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (rax2 & k0 & k1 & k2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & k3 & k4 & k5 & k6 & m6 & st6 & LB6 &
                    -> & KREL6 & MP6 & MI6 & ST6 & ERR6 & AUX6 & HP6 & SIN6 & PERMX & SUB6 & XPM & IM6 & GM6 & GG6 & FR6 & SC6).
    pose proof (HH_blocks_below H HH _ _ _ HP6) as HB6.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply s_seg3 with (lo := lo) (h := es_entries x);
      [exact SC6| exact POS| unfold STORE_SIZE; lia| exact FR6| exact IM6| exact GM6| exact ST6| exact CEIL| lia| exact MI6]|].
    intros ms7 (u0' & u2' & d3 & d4 & d5 & d6 & d7 & u3' & u4' & u5' & u6' & m7 & -> & MU7 & WM7 & MI7 & ST7 & SC7 & IM7 & GM7).
    assert (HP7 : hs_RHEAP H st6 LB6 m7).
    { eapply (HH_RHEAP_frame H HH); [exact HP6| exact MU7| exact WM7|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX7 : hs_rauxv_ok H m7 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX6| exact MU7| exact WM7|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    apply (rw_cells_transport rsegs _ m6 m7 _ _ ERR6) in MU7 as ERR7; [| exact WM7| unfold RERRNO; cbn; lia].
    assert (GG7 : GOT_echfree m7) by (eapply GOT_echfree_across; [exact MU7| exact WM7| unfold A_got_ossl_echext_free; cbn; lia| exact GG6]).
    assert (XP7 : xpres LB6 (bv_unsigned sp) [] m6 m7).
    { eapply xpres_of_munch; [exact MU7| exact WM7| | exact HB6]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB6) (s := st6) (p := es_id x) (n := STORE_SIZE); try reflexivity.
      all: try first [exact HP7| exact KREL6| exact SIN6| exact AUX7| exact SPB| exact ST7| exact CEIL| exact MI7| exact IM7| exact GM7| exact RAE].
      all: first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR7]. }
    intros [ms8 mo8] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m8 & st8 &
                    -> & KREL8 & MP8 & MI8 & ST8 & ERR8 & AUX8 & XP8 & HEAP8 & IM8 & GM8).
    rewrite errno_RATP in ERR8.
    unfold efree_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, e0, e1, e2, e3, e4, e5, e6, e7, z3, z4, z5, z6, m8, st8, (hs_lb_remove H (es_id x) LB6).
    split; [reflexivity|]. split; [exact KREL8|].
    split; [eapply (mpres_trans H HH); [exact MP6| exact MP8]|].
    split; [exact MI8|]. split; [exact ST8|]. split; [rewrite errno_RATP; exact ERR8|]. split; [exact AUX8|].
    split.
    { rewrite blocks_STORE_eq. fold BX. cbn [app]. eapply Permutation_trans; [| exact PERMX].
      eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
      eapply (lb_remove_perm H HH); [exact HP6| exact SIN6]. }
    split; [exact HEAP8|].
    split.
    { eapply xpres_trans; [eapply xpres_weaken; [exact XPM| lia| exact (SUBL _ _)| auto]|].
      eapply xpres_trans; [eapply xpres_weaken; [exact XP7| lia| exact (SUBL _ _)| auto]| exact XP8]. }
    split; [exact IM8|]. split; [exact GM8|].
    eapply GOT_echfree_xpres; [exact XP8| constructor| exact GG7].
  Qed.
End W.
