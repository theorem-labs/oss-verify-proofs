(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_Rostr ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_C4
     ECH_C5_stmt ECH_C5_small ECH_C5_new ECH_C5_push ECH_C6_stmt ECH_C7_stmt ECH_C9_stmt ECH_C10_stmt ECH_C13_stmt ECH_C13_small ECH_C13_ext ECH_C13_entry ECH_C13_store
     ECH_C14_stmt ECH_KitSeg ECH_LibMid F_time ECH_C14_bio2buf ECH_C14_ladder ECH_C14_ladloop ECH_C14_tail ECH_C14_b2b ECH_C14_fcc ECH_C14_dec ECH_C14_decexts
     ECH_C14_flat_seg ECH_C14_fmt ECH_C14_flatten.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis CERTO3 : egs_fresh_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let HRE : realloc_sr_stmt H := proj1 (proj2 HX).
  Let STATICS : statics_of_RHEAP H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word).
  Hypotheses (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo)
             (MBO : MEMBIO LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (DS : bytes_at rsegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : hs_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : hs_KREL H s mo)
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H)
             (BUDG : lb_big (mid_errblocks M ++ LB) + mid_big M + DECODE_BIG <= hs_LIVE_BIG_MAX H)
             (AUX : hs_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk rsegs m lo (bv_unsigned sp)) (CEIL : hceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M)
             (ERR : rw_cells rsegs m (errno_addr tp) [C4 errv]) (MI : mem_inv rsegs m) (TP : tp = Z_to_bv 64 RATP) (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Hypothesis PAYS : 1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S.

  (* [comment removed for export] *)
  Local Notation L0c := (L0 LB M).
  Local Notation SPc := (SP' sp).
  Local Notation RBPc := (RBP sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation XFc := (XF M st mb R).

  Hypothesis TIME : time_sr_stmt H.
  Let EGS : egs_stmt H := proj1 (proj2 (C4_spec H HX CERTO3)).
  Local Notation RCFACTS := (rc_facts H HX ra sp tp a0 a1 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).
  (* [comment removed for export] *)
  Local Notation DWKG p A nA pbin Bb nB bs R' jt TB BT := (dwkG H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation BTFREE p A nA pbin Bb nB bs R' jt bt TB BT := (btfree_stmt H ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation RPES p A nA pbin Bb nB bs R' jt bt TB BT := (rp_entry_stmt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation FWK := (fwk H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B R ds).

  (* [comment removed for export] *)
  Hypothesis RPE : forall (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (jt : list byte) (bt : Z) (TB : list block) (BT : mem -> Prop),
      1 <= mb_len R <= nA /\ nA <= 512 * 3 ->
      0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      mb_static R R' -> mb_pos R' = mb_len R ->
      0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 /\ lb_big TB <= 1 ->
      (forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
          BT m1 -> xpres L SP X m1 m2 -> (forall b, In b TB -> In b L) -> hceil <= SP ->
          Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) TB) X -> BT m2) ->
      RPES p A nA pbin Bb nB bs R' jt bt TB BT.
  (* [comment removed for export] *)
  Hypothesis B64K : rp_b64K H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds.

  (* [comment removed for export] *)
  Lemma rw_CB_bytes_at : forall m0 A0' n bs0, rw_cells rsegs m0 A0' [CB n bs0] -> bytes_at rsegs m0 A0' bs0.
  Proof. clear. intros m0 A0' n bs0 [[WF BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA. exact BA. Qed.

  (* [comment removed for export] *)
  Lemma btfree_null : forall p A nA pbin Bb nB bs R' jt, BTFREE p A nA pbin Bb nB bs R' jt 0 [] (fun _ => True).
  Proof using HH.
    intros p A nA pbin Bb nB bs R' jt. unfold btfree_stmt.
    intros NB S' M' LE fr j3 m1 mo1 s1' ra0 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 Q DW RAR RAE2 K.
    pose proof DW as (HP1 & KREL1 & MP1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv1 ERR1] & MI1 & ST1 & AUX1 & _).
    eapply (sr_evt_krel H HH); [exact KREL1| eapply bio_free_all_null; exact MI1|]. intros ms2 ->.
    eapply K; [| exact KREL1| exact MP1| exact MI1| exact ST1| exact ERR1| exact AUX1| apply xpres_refl].
    unfold drest in HP1. cbn [app] in HP1. exact HP1.
  Qed.

  (* [comment removed for export] *)
  Lemma dwk_init : forall p A nA pbin Bb nB bs R' j0 j2 rb TB (BT : mem -> Prop) m' mo' s',
      FWK ((pbin, Bb, nB) :: TB) p A nA R' j0 j2 rb m' mo' s' -> bytes_at rsegs m' Bb bs -> BT m' -> mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      DWKG p A nA pbin Bb nB bs R' (le8 rb ++ firstn 2040 j2) TB BT [] [] S M [] [CB 88 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)] (skipn 2040 j2) m' mo' s'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX.
    intros until s'. intros FW BS BT1 LMAX.
    pose proof FW as (HP1 & KREL1 & MP1 & MBO1 & MST & POS & NA1 & NA2 & DSm1 & DSA1 & FRlo & RB1 & FRhi & ERR1 & LM1 & MI1 & ST1 & AUX1 & XA1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    pose proof SO as (SC0 & SIN0 & _).
    (* [comment removed for export] *)
    assert (SC1 : rw_cells rsegs m' st [C8 (wz (es_entries S)); C8 (wz 0); C8 (wz 0)]).
    { eapply xpres_rw_cells'; [exact XA1| exact SC0| right; right; exists (es_id S, st, STORE_SIZE); split; [exact SIN0| cbn; unfold STORE_SIZE; clear; lia]|].
      unfold MEMBIO_foot. destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _).
      assert (D1 : blk_addr (es_id S, st, STORE_SIZE) + blk_size (es_id S, st, STORE_SIZE) <= blk_addr (mb_id R, mb, BIO_SIZE) \/ blk_addr (mb_id R, mb, BIO_SIZE) + blk_size (mb_id R, mb, BIO_SIZE) <= blk_addr (es_id S, st, STORE_SIZE)).
      { eapply (HH_RHEAP_blocks_disjoint H HH); [exact HP| apply in_or_app; right; exact SIN0| apply in_or_app; right; exact I1|].
        exact (nodup_ids_app_ne [(es_id S, st, STORE_SIZE)] _ _ _ NDsm (or_introl eq_refl) (or_introl eq_refl)). }
      assert (D3 : blk_addr (es_id S, st, STORE_SIZE) + blk_size (es_id S, st, STORE_SIZE) <= blk_addr (mb_bmid R, mb_bm R, BUFMEM_SIZE) \/ blk_addr (mb_bmid R, mb_bm R, BUFMEM_SIZE) + blk_size (mb_bmid R, mb_bm R, BUFMEM_SIZE) <= blk_addr (es_id S, st, STORE_SIZE)).
      { eapply (HH_RHEAP_blocks_disjoint H HH); [exact HP| apply in_or_app; right; exact SIN0| apply in_or_app; right; exact I3|].
        exact (nodup_ids_app_ne [(es_id S, st, STORE_SIZE)] _ _ _ NDsm (or_introl eq_refl) ltac:(right; right; left; reflexivity)). }
      cbn [blk_addr blk_size fst snd] in D1, D3. apply Forall_cons; [cbn; unfold STORE_SIZE in *; clear - D1; lia|]. apply Forall_cons; [cbn; unfold STORE_SIZE in *; clear - D3; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof FRhi as FRhi'. pose proof (proj1 (rw_cells_app rsegs m' _ [CB 2128 j2] SAVESc) FRhi') as [FJ FS].
    pose proof FJ as [[WFJ _] _]. cbn [cells_wf cell_wf csize length] in WFJ. destruct WFJ as [LJ _].
    pose proof (rw_cells_split_CB rsegs m' _ [] 2128 j2 [] [2040%nat; 88%nat] FJ ltac:(reflexivity)) as FJ2. cbn [mk_CB_cells app] in FJ2.
    pose proof (proj1 (rw_cells_app rsegs m' _ [CB 2040 (firstn 2040 j2)] [CB 88 (firstn 88 (skipn 2040 j2))]) FJ2) as [FJa FJb].
    cbn [cells_size csize Nat.add] in FJb, FS.
    assert (FT : rw_cells rsegs m' RBPc [CB 2048 (le8 rb ++ firstn 2040 j2)]).
    { eapply rw_cells_recut.
      - apply (proj2 (rw_cells_app rsegs m' RBPc [C8 rb] [CB 2040 (firstn 2040 j2)])). split; [exact RB1|]. cbn [cells_size csize Nat.add]. unfold RBP.
        replace (bv_unsigned sp + -2240 + 8) with (bv_unsigned sp + -2232) by (clear; lia). exact FJa.
      - cbn [cells_wf cell_wf csize]. rewrite length_app, firstn_length_le by (rewrite LJ; clear; lia). split; [reflexivity| exact I].
      - cbn [cells_bytes cbytes app]. rewrite ?app_nil_r. reflexivity. }
    assert (F3 : rw_cells rsegs m' (SPc + O_F3) [CB 88 (skipn 2040 j2)]).
    { rewrite firstn_all2 in FJb by (rewrite length_skipn, LJ; clear; lia). unfold SP', O_F3.
      replace (bv_unsigned sp + -2352 + 2160) with (bv_unsigned sp + -2232 + Z.of_nat 2040) by (clear; lia). exact FJb. }
    assert (F4 : rw_cells rsegs m' (SPc + O_SAVES) SAVESc).
    { unfold SP', O_SAVES. replace (bv_unsigned sp + -2352 + 2248) with (bv_unsigned sp + -2232 + Z.of_nat 2128) by (clear; lia). exact FS. }
    (* [comment removed for export] *)
    pose proof LM as (_ & _ & _ & _ & EX0 & _ & _ & FIT & _).
    assert (LEN16 : length (es_slots (mid_E M)) = 16%nat) by (destruct (mid_err M) as [|c0]; cbn [ERRX] in EX0; [rewrite EX0; reflexivity| exact (proj1 EX0)]).
    destruct (errst_fits_bounds _ LEN16 FIT) as (EC0 & EB0 & EG0).
    unfold dwkG. repeat match goal with |- _ /\ _ => split end.
    - eapply PERM; [exact HP1|]. unfold drest, L0. cbn [app].
      rewrite (app_assoc (mid_errblocks M) TB). apply Permutation_cons_app. apply Permutation_elt. rewrite <- app_assoc. apply Permutation_app_swap_app.
    - exact KREL1.
    - exact MP1.
    - cbn [app]. exact LM1.
    - unfold mid_step. repeat split; [exact MF1| intros b0 K0; exact K0| intros c0 K0; exact K0| intros K0; exact K0].
    - exists [], []. cbn [app]. split; [apply Permutation_refl|]. split; [destruct (mid_ctx M); reflexivity| destruct (mid_err M); reflexivity].
    - reflexivity.
    - exact EC0.
    - exact EB0.
    - exact EG0.
    - cbn. clear. lia.
    - cbn. clear. lia.
    - cbn. clear. lia.
    - cbn [app]. unfold STOREobj. split; [exact SC1|]. split; [exact SIN0|]. unfold ENTRIES. rewrite SEO. exact SE.
    - reflexivity.
    - unfold blocks_STORE. rewrite SEO. apply Permutation_refl.
    - unfold blocks_STORE. rewrite SEO. cbn. constructor; [intros []| constructor].
    - intros K0 es0 EQ0. rewrite SEO in EQ0. discriminate EQ0.
    - exact MBO1.
    - exact DSm1.
    - exact BS.
    - exact BT1.
    - exact FRlo.
    - exact FT.
    - exact F3.
    - exact F4.
    - exact ERR1.
    - exact MI1.
    - exact ST1.
    - exact AUX1.
    - eapply xpres_weaken; [exact XA1| clear; lia| intros b Hb; exact Hb| intros q Hq; unfold XF; apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq].
    - unfold dnb. cbn. unfold DECODE_CNT, DECODE_BYTES, DECODE_BIG. clear. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dloop_budget : forall nA nB TB,
    0 <= nA <= 512 * 3 -> 0 <= nB < OSSL_ECH_MAX_ECHCONFIG_LEN -> Z.of_nat (length TB) <= 7 -> lb_bytes TB <= 3072 -> lb_big TB <= 1 ->
       lb_bytes TB + nB + nA + lb_bytes LB + errph_bytes (mid_err M) + ERRSTR_BYTES + DLOOP_BYTES <= hs_LIVE_MAX H
    /\ Z.of_nat (length TB) + 2 + Z.of_nat (length LB) + errph_cnt (mid_err M) + ERRSTR_CNT + DLOOP_CNT <= hs_LIVE_CNT_MAX H
    /\ lb_big TB + big1 nB + big1 nA + lb_big LB + errph_big (mid_err M) + DLOOP_BIG <= hs_LIVE_BIG_MAX H.
  Proof using BUD BUDC BUDG HP HH.
    intros nA nB TB NA NB TL TBY TG.
    assert (EN0 : 0 <= lb_bytes (mid_errblocks M)).
    { apply lb_bytes_nonneg. apply Forall_forall. intros b Hb. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & K0 & _). exact K0. }
    pose proof (lb_big_nonneg (mid_errblocks M)) as EG0. pose proof (ctxph_nonneg3 (mid_ctx M)) as (CN1 & CN2 & CN3).
    rewrite (big1_small nB) by (unfold OSSL_ECH_MAX_ECHCONFIG_LEN, BIGB in *; clear - NB; lia). rewrite (big1_small nA) by (unfold BIGB; clear - NA; lia).
    revert BUD BUDC BUDG. unfold mid_bytes, mid_cnt, mid_big. rewrite lb_bytes_app, length_app, lb_big_app, Nat2Z.inj_add.
    unfold OSSL_ECH_MAX_ECHCONFIG_LEN, DECODE_BYTES, DECODE_CNT, DECODE_BIG, ERRSTR_BYTES, ERRSTR_CNT, DLOOP_BYTES, DLOOP_CNT, DLOOP_BIG in *.
    clear - NA NB TL TBY TG EN0 EG0 CN1 CN2 CN3. intros. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_dec0 : rp_decK0 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL PAYS NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX CERTO3 TIME RPE.
    unfold rp_decK0. intros p A nA R' j0 j2 rb m' mo' s' pbin Bb rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s10w s11w u3 u4 u5 u6 LR FW BIN.
    pose proof FW as (_ & _ & _ & _ & MST & POS & NA1 & NA2 & _).
    pose proof (rw_CB_bytes_at _ _ _ _ BIN) as BS. pose proof DSL as DSL1. unfold zlength in DSL1.
    destruct (dloop_budget nA (mb_len R) [] ltac:(clear - NA1 NA2; lia) ltac:(clear - LR; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as (B1 & B2 & B3).
    cbn [lb_bytes lb_big length fold_right Z.of_nat] in B1, B2, B3.
    replace (Z_to_bv 64 (mb_len R) : word) with (Z_to_bv 64 (zlength ds) : word) by (rewrite DSL; reflexivity).
    eapply (rp_flat H HX CERTO3 ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M x st mb lo B S R ds errv
              A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE PAYS
              p A nA pbin Bb (mb_len R) ds R' (le8 rb ++ firstn 2040 j2) 0 [] (fun _ => True)).
    - clear - NA1 NA2. lia.
    - unfold zlength. rewrite DSL1. clear - LR DSL1. unfold OSSL_ECH_MAX_ECHCONFIG_LEN in *. lia.
    - exact MST.
    - exact POS.
    - cbn. clear. lia.
    - intros. exact I.
    - exact TIME.
    - apply RPE; [clear - NA1 NA2; lia| unfold zlength; rewrite DSL1; clear - LR DSL1; unfold OSSL_ECH_MAX_ECHCONFIG_LEN in *; lia| exact MST| exact POS| cbn; clear; lia| intros; exact I].
    - apply btfree_null.
    - cbn [lb_bytes lb_big length fold_right Z.of_nat]. exact B1.
    - cbn [lb_bytes lb_big length fold_right Z.of_nat]. exact B2.
    - cbn [lb_bytes lb_big length fold_right Z.of_nat]. exact B3.
    - eapply dwk_init; [exact FW| exact BS| exact I| clear - LR; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem readcfg_main :
    hs_SR H POSTc (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom rsegs)) mo).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL PAYS NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX CERTO3 TIME RPE B64K.
    eapply (rp_b2b H HX CERTO3). all: try eassumption.
    eapply (rp_fmt H HX CERTO3). all: try eassumption.
    exact rp_dec0.
  Qed.
End RC.

(* [comment removed for export] *)
Section CLOSE.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis CERTO3 : egs_fresh_stmt H.
  Hypothesis TIME : time_sr_stmt H.
  Hypothesis RPE : forall (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState)
      (LIB LB : list block) (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word)
      (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (jt : list byte) (bt : Z) (TB : list block) (BT : mem -> Prop),
      a0 = Z_to_bv 64 st -> a1 = Z_to_bv 64 mb ->
      STOREobj LB m st S -> es_entries S = 0 -> es_entries_o S = None -> st + STORE_SIZE <= lo ->
      MEMBIO LB m mb R -> mb_pos R = 0 -> mb_nread R = 0 -> MEMBIO_below mb R lo -> MEMBIO_sep mb R ->
      bytes_at rsegs m (mb_buf R) ds -> zlength ds = mb_len R ->
      (1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD) ->
      List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)) ->
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b') ->
      hs_RHEAP H s (mid_errblocks M ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H ->
      lb_big (mid_errblocks M ++ LB) + mid_big M + DECODE_BIG <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - READCFG_STACK M ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP -> bv_unsigned ra mod 2 = 0 ->
      1 <= mb_len R <= nA /\ nA <= 512 * 3 ->
      0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      mb_static R R' -> mb_pos R' = mb_len R ->
      0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 /\ lb_big TB <= 1 ->
      (forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
          BT m1 -> xpres L SP X m1 m2 -> (forall b, In b TB -> In b L) -> hceil <= SP ->
          Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) TB) X -> BT m2) ->
      rp_entry_stmt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT.
  Hypothesis B64K : forall (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState)
      (LIB LB : list block) (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word),
      a0 = Z_to_bv 64 st -> a1 = Z_to_bv 64 mb ->
      STOREobj LB m st S -> es_entries S = 0 -> es_entries_o S = None -> st + STORE_SIZE <= lo ->
      MEMBIO LB m mb R -> mb_pos R = 0 -> mb_nread R = 0 -> MEMBIO_below mb R lo -> MEMBIO_sep mb R ->
      bytes_at rsegs m (mb_buf R) ds -> zlength ds = mb_len R ->
      (1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD) ->
      (1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S) ->
      List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)) ->
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b') ->
      hs_RHEAP H s (mid_errblocks M ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H ->
      lb_big (mid_errblocks M ++ LB) + mid_big M + DECODE_BIG <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - READCFG_STACK M ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP -> bv_unsigned ra mod 2 = 0 ->
      rp_b64K H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds.

  Theorem readcfg_spec : readcfg_stmt H.
  Proof using HX CERTO3 TIME RPE B64K.
    unfold readcfg_stmt. intros.
    eapply (readcfg_main H HX CERTO3); try eassumption.
    - intros. eapply RPE; eassumption.
    - eapply B64K; eassumption.
  Qed.
End CLOSE.
