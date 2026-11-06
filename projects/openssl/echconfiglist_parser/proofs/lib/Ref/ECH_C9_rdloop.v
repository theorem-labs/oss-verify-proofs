(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_B64 ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C7_read ECH_C7_rd2 ECH_C9_rdfacts ECH_C9_rdseg
     ECH_C8_small ECH_C8_blockA ECH_C8_update ECH_C8_final.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mset (M : membio) (pos fl nr : Z) : membio :=
  mkMB (mb_buf M) (mb_len M) pos fl (mb_numf M) nr (mb_next M) (mb_prev M) (mb_bb M) (mb_bm M) (mb_rp M)
       (mb_id M) (mb_bbid M) (mb_bmid M) (mb_rpid M).
Lemma mb_after_read_mset : forall M pos fl nr n,
  mb_after_read (mset M pos fl nr) n = mset M (pos + n) (Z.land fl (Z.lnot BIO_FLAGS_RETRY_MASK)) (nr + n).
Proof. intros. reflexivity. Qed.
Lemma mset_self : forall M, mset M (mb_pos M) (mb_flags M) (mb_nread M) = M.
Proof. intros M. destruct M. reflexivity. Qed.

Lemma le4_wz_of_bytes : forall bs, length bs = 4%nat -> le4 (wz (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le4, wz.
  assert (B : 0 <= bytes_le_to_Z bs < 2^64).
  { pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
    change (2 ^ (8 * Z.of_nat 4)) with (2^32) in B. lia. }
  rewrite unsigned_lit by lia. rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma rw_cells_CB_bytes_at : forall segs m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs /\ length bs = n.
Proof.
  intros segs m A n bs [[WF B] W]. cbn in WF. destruct WF as [L _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. split; assumption.
Qed.

(* [comment removed for export] *)
Section HC.
  Context {HCEIL : HeapCeil}.
  Lemma ENCCTX_CB92 : forall LB m a d p, ENCCTX LB m a d p ->
    (exists old, rw_cells rsegs m a [CB 92 old]) /\ In (p, a, ENCCTX_SIZE) LB /\ rblock_range a ENCCTX_SIZE /\ (length d < 64)%nat.
  Proof.
    intros LB m a d p (raw & line & L & MD & RC & LN & IN & RB & DI).
    split; [| split; [exact IN| split; [exact RB| apply DI]]].
    exists (cells_bytes [C4 (wz (zlength d)); CB 80 raw; C4 (wz line); C4 (wz 0)]).
    eapply rw_cells_recut; [exact RC| | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity].
    cbn -[cells_bytes]. split; [| exact I]. pose proof (cells_bytes_length [C4 (wz (zlength d)); CB 80 raw; C4 (wz line); C4 (wz 0)]) as E.
    cbn [cells_size csize Nat.add] in E. apply E. cbn. repeat split; auto.
  Qed.

  Lemma ENCCTX_transport : forall W m m' LB a d p,
    munch W m m' -> wmono rsegs m m' -> disjoint_from W a 92 -> ENCCTX LB m a d p -> ENCCTX LB m' a d p.
  Proof.
    intros W m m' LB a d p MU WM DJ (raw & line & L & MD & RC & LN & IN & RB & DI).
    exists raw, line. split; [exact L|]. split; [exact MD|]. split; [| exact (conj LN (conj IN (conj RB DI)))].
    eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. exact DJ.
  Qed.

  Lemma MEMBIO_transport : forall W m m' LB a M,
    munch W m m' -> wmono rsegs m m' ->
    disjoint_from W a BIO_SIZE -> disjoint_from W (mb_bb M) BIOBUFMEM_SIZE ->
    disjoint_from W (mb_bm M) BUFMEM_SIZE -> disjoint_from W (mb_rp M) BUFMEM_SIZE ->
    MEMBIO LB m a M -> MEMBIO LB m' a M.
  Proof.
    intros W m m' LB a M MU WM D1 D2 D3 D4 (H1 & H2 & H3 & H4 & REST).
    split; [| split; [| split; [| split; [| exact REST]]]].
    - eapply rw_cells_transport; [exact H1| exact MU| exact WM| exact D1].
    - eapply rw_cells_transport; [exact H2| exact MU| exact WM| exact D2].
    - eapply rw_cells_transport; [exact H3| exact MU| exact WM| exact D3].
    - eapply rw_cells_transport; [exact H4| exact MU| exact WM| exact D4].
  Qed.

  (* [comment removed for export] *)
  Lemma dmod_init : (length (@nil Z) = 0%nat \/ Nat.modulo (length (@nil Z)) 4 <> 0%nat).
  Proof. left. reflexivity. Qed.

  Lemma decode_final_rv_cases : forall d, decode_final_rv d = 1 \/ decode_final_rv d = -1.
  Proof.
    intros d. unfold decode_final_rv. destruct (Nat.eqb (length d) 0); [left; reflexivity|].
    destruct (decodeblock_ret d (-1) <? 0); [right| left]; reflexivity.
  Qed.
End HC.

(* [comment removed for export] *)
Definition rdframe_pre (ctx mb a vout voutl vret : Z) (j16 : list byte) : list cell :=
  [C8 (Z_to_bv 64 (ctx + 1542)); C8 (Z_to_bv 64 vout); C8 (Z_to_bv 64 voutl); C8 (Z_to_bv 64 (ctx + 1542)); C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 a);
   C8 (Z_to_bv 64 vret); CB 16 j16; C8 (Z_to_bv 64 (ctx + 40))].
Definition rdframe_suf (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) : list cell :=
  [C8 q11; C8 q10; C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra].
Section FR.
  Context {HCEIL : HeapCeil}.
  Lemma rdframe_split_num : forall m spx ctx mb a vout voutl vret j16 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra,
    rw_cells rsegs m spx (rdframe ctx mb a vout voutl vret j16 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
       rw_cells rsegs m spx (rdframe_pre ctx mb a vout voutl vret j16 ++ [CB 4 (firstn 4 j8)])
    /\ rw_cells rsegs m (spx + 84) [C4 (wz (bytes_le_to_Z (skipn 4 j8)))]
    /\ rw_cells rsegs m (spx + 88) (rdframe_suf q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
    /\ length (firstn 4 j8) = 4%nat.
  Proof.
    intros. pose proof H as W. destruct W as [[WF _] _]. cbn in WF.
    assert (L8 : length j8 = 8%nat) by tauto.
    assert (E : rw_cells rsegs m spx ((rdframe_pre ctx mb a vout voutl vret j16 ++ [CB 4 (firstn 4 j8)]) ++ [C4 (wz (bytes_le_to_Z (skipn 4 j8)))]
                                       ++ rdframe_suf q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)).
    { eapply rw_cells_recut; [exact H| |].
      - cbn. rewrite length_firstn. repeat split; try tauto. lia.
      - unfold rdframe, rdframe_pre, rdframe_suf. cbn [cells_bytes cbytes app].
        rewrite le4_wz_of_bytes by (rewrite length_skipn; lia).
        rewrite <- (firstn_skipn 4 j8) at 3. first [rewrite !app_assoc; reflexivity | rewrite <- !app_assoc; reflexivity]. }
    apply rw_cells_app in E. destruct E as [E1 E]. apply rw_cells_app in E. destruct E as [E2 E3].
    revert E2 E3. rewrite cells_size_app. cbn [cells_size csize app Nat.add]. intros E2 E3.
    replace (spx + Z.of_nat 84 + Z.of_nat 4) with (spx + 88) in E3 by lia.
    replace (spx + Z.of_nat 84) with (spx + 84) in E2 by lia.
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. rewrite length_firstn. lia.
  Qed.
  Lemma rdframe_join_num : forall m spx ctx mb a vout voutl vret j16 j8a v q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra,
    rw_cells rsegs m spx (rdframe_pre ctx mb a vout voutl vret j16 ++ [CB 4 j8a]) -> length j8a = 4%nat ->
    rw_cells rsegs m (spx + 84) [C4 v] ->
    rw_cells rsegs m (spx + 88) (rdframe_suf q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra) ->
    rw_cells rsegs m spx (rdframe ctx mb a vout voutl vret j16 (j8a ++ le4 v) q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra).
  Proof.
    intros until qra. intros E1 L E2 E3.
    assert (E : rw_cells rsegs m spx ((rdframe_pre ctx mb a vout voutl vret j16 ++ [CB 4 j8a]) ++ [C4 v] ++ rdframe_suf q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)).
    { apply (proj2 (rw_cells_app rsegs m spx _ _)). split; [exact E1|]. rewrite cells_size_app. cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app rsegs m _ [C4 v] _)). split; [replace (spx + Z.of_nat 84) with (spx + 84) by lia; exact E2|]. cbn [cells_size csize Nat.add].
      replace (spx + Z.of_nat 84 + Z.of_nat 4) with (spx + 88) by lia. exact E3. }
    eapply rw_cells_recut; [exact E| |].
    - pose proof E1 as W. destruct W as [[WF _] _]. cbn in WF. cbn -[le4]. rewrite length_app, L, length_le4. cbn. tauto.
    - unfold rdframe, rdframe_pre, rdframe_suf. cbn [cells_bytes cbytes app]. first [reflexivity | rewrite !app_assoc; reflexivity | rewrite <- !app_assoc; reflexivity].
  Qed.
End FR.

(* [comment removed for export] *)
Ltac mbnum MB :=
  let T := fresh "MBt" in
  pose proof MB as T; unfold MEMBIO in T;
  cbn [mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset] in T;
  let MBP := fresh "MBP" in let MBL := fresh "MBL" in let MBB0 := fresh "MBB0" in let MBBH := fresh "MBBH" in
  let MBF := fresh "MBF" in let MBN := fresh "MBN" in let MBN2 := fresh "MBN2" in
  destruct T as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MBP & MBL & MBB0 & MBBH & MBF & _ & _ & _ & MBN & MBN2 & _ & _).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zapZ := repeat match goal with x := _ : Z |- _ => subst x end.
Ltac unhide_for_goal :=
    repeat match goal with
    | H : hidden (_ <= ?y \/ _ <= ?x) |- ?G =>
        match G with context [y] => match G with context [x] => unhide H end end
    end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia_clean :=
    repeat match goal with H : hidden _ |- _ => clear H end;
    repeat match goal with H : rw_cells _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H | H : MEMBIO _ _ _ _ |- _ => clear H
                         | H : ENCCTX _ _ _ _ _ |- _ => clear H | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H
                         | H : stk _ _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
                         | H : @eq nat _ _ |- _ => clear H | H : (_ <= _)%nat |- _ => clear H | H : (_ < _)%nat |- _ => clear H
                         | H : @eq (list _) _ _ |- _ => clear H | H : In _ _ |- _ => clear H end;
    Zify.zify; xlia zchecker.
Ltac djak := zapZ; unhide_for_goal; lia_clean.
Ltac djsk := cbn [disjoint_from cells_size csize length map app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ rdhdr rdframe rdframe_pre rdframe_suf bio_cells buf_cells];
    unfold BIO_SIZE, BUFMEM_SIZE, BIOBUFMEM_SIZE, B64CTX_SIZE, ENCCTX_SIZE;
    repeat lazymatch goal with |- _ /\ _ => split end; try exact I; djak.
Ltac dja := zapZ; repeat match goal with H : ?A \/ ?B |- _ => hide H end; unhide_for_goal; lia_clean.
Ltac djs := cbn [disjoint_from cells_size csize length map app Nat.add Z.of_nat Pos.of_succ_nat Pos.succ rdhdr rdframe rdframe_pre rdframe_suf bio_cells buf_cells];
    unfold BIO_SIZE, BUFMEM_SIZE, BIOBUFMEM_SIZE, B64CTX_SIZE, ENCCTX_SIZE;
    repeat lazymatch goal with |- _ /\ _ => split end; try exact I; dja.
(* [comment removed for export] *)
Ltac carryh MU WM :=
    lazymatch type of MU with
    | munch ?W ?ma ?mb =>
        repeat match goal with
        | H : rw_cells ?segs ma ?A ?cs |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A (Z.of_nat (cells_size cs))) by djs;
                    apply (fun HH => @rw_cells_transport segs W ma mb A cs HH MU WM D) in H; clear D
                  | change (ECH_Kit.stale (rw_cells segs ma A cs)) in H ]
        | H : bytes_at ?segs ma ?A ?bs |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A (Z.of_nat (length bs))) by djs;
                    apply (fun HH => @bytes_at_transport segs W ma mb A bs HH MU D) in H; clear D
                  | change (ECH_Kit.stale (bytes_at segs ma A bs)) in H ]
        | H : stk ?segs ma ?l ?h |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W l (h - l)) by djs;
                    apply (fun HH => @stk_transport_disjoint segs W ma mb l h HH MU WM D) in H; clear D
                  | change (ECH_Kit.stale (stk segs ma l h)) in H ]
        | H : ENCCTX ?LBx ma ?A ?d ?p |- _ =>
            first [ let D := fresh in assert (D : disjoint_from W A 92) by djs;
                    apply (fun HH => @ENCCTX_transport _ W ma mb LBx A d p MU WM D HH) in H; clear D
                  | change (ECH_Kit.stale (ENCCTX LBx ma A d p)) in H ]
        | H : MEMBIO ?LBx ma ?A ?M |- _ =>
            first [ let D1 := fresh in let D2 := fresh in let D3 := fresh in let D4 := fresh in
                    assert (D1 : disjoint_from W A BIO_SIZE) by (unfold BIO_SIZE; djs);
                    assert (D2 : disjoint_from W (mb_bb M) BIOBUFMEM_SIZE) by (cbn [mb_bb mset]; unfold BIOBUFMEM_SIZE; djs);
                    assert (D3 : disjoint_from W (mb_bm M) BUFMEM_SIZE) by (cbn [mb_bm mset]; unfold BUFMEM_SIZE; djs);
                    assert (D4 : disjoint_from W (mb_rp M) BUFMEM_SIZE) by (cbn [mb_rp mset]; unfold BUFMEM_SIZE; djs);
                    apply (fun HH => @MEMBIO_transport _ W ma mb LBx A M MU WM D1 D2 D3 D4 HH) in H; clear D1 D2 D3 D4
                  | change (ECH_Kit.stale (MEMBIO LBx ma A M)) in H ]
        | H : B64TAB ma |- _ => clear H
        | H : mem_inv _ ma |- _ => clear H
        end;
        repeat match goal with H : ECH_Kit.stale _ |- _ => clear H end
    end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RD.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Variables (sp gp tp : word) (q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m0 : mem) (LB : list block) (a mb lo out0 outl0 : Z) (R : b64frep) (M0 : membio) (txt : list byte).
  Local Notation ctx := (bf_ctx R).
  Local Notation enc := (bf_enc R).
  Local Notation sp' := (bv_unsigned sp + -192).
  Local Notation TXT := (map bv_unsigned txt).
  (* [comment removed for export] *)
  Definition WL : list (Z * Z) :=
    [(lo, bv_unsigned sp); (out0, out0 + outl0); (ctx, ctx + 2566); (enc, enc + 92); (mb, mb + 128); (mb_bm M0, mb_bm M0 + 32)].

  (* [comment removed for export] *)
  Hypothesis APB : B64F_apart a R.
  Hypothesis BLW : B64F_below a R lo.
  Hypothesis RBa : rblock_range a BIO_SIZE.
  Hypothesis RBc : rblock_range ctx B64CTX_SIZE.
  Hypothesis RBe : rblock_range enc 92.
  Hypothesis FLR : 0 <= bf_flags R < 2^31.
  Hypothesis NONL : Z.land (bf_flags R) BIO_FLAGS_BASE64_NO_NL = BIO_FLAGS_BASE64_NO_NL.
  Hypothesis INe : In (bf_eid R, enc, ENCCTX_SIZE) LB.
  Hypothesis MBW : MEMBIO_below mb M0 lo.
  Hypothesis MSP : MEMBIO_sep mb M0.
  Hypothesis MRB : rblock_range mb BIO_SIZE /\ rblock_range (mb_bb M0) BIOBUFMEM_SIZE /\ rblock_range (mb_bm M0) BUFMEM_SIZE /\ rblock_range (mb_rp M0) BUFMEM_SIZE.
  Hypothesis MLEN : 0 <= mb_len M0 < 2^31.
  Hypothesis TL : zlength txt = mb_len M0.
  Hypothesis X1 : Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M0)) (blocks_B64F a R).
  Hypothesis X2 : Forall (fun b => mb_buf M0 + mb_len M0 <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M0) (blocks_B64F a R).
  Hypothesis X3 : Forall (fun b => out0 + outl0 <= blk_addr b \/ blk_addr b + blk_size b <= out0) (blocks_MEMBIO mb M0).
  Hypothesis X4 : mb_buf M0 + mb_len M0 <= out0 \/ out0 + outl0 <= mb_buf M0.
  Hypothesis X5 : out0 + outl0 <= A_mem_buf_method + O_METH_BREAD \/ A_mem_buf_method + O_METH_BREAD + 64 <= out0.
  Hypothesis X6 : Forall (fun b => out0 + outl0 <= blk_addr b \/ blk_addr b + blk_size b <= out0) (blocks_B64F a R).
  Hypothesis OUTW : out0 + outl0 <= lo \/ bv_unsigned sp <= out0.
  Hypothesis OUT0 : 0 < out0.
  Hypothesis OUTE : out0 + outl0 <= 2^64.
  Hypothesis OUTL0 : 0 < outl0 < 2^31.
  Hypothesis CEIL : hceil <= lo.
  Hypothesis LOS : lo <= bv_unsigned sp + -192 - Z.max BIOREAD_STACK (Z.max DECUPDATE_STACK (Z.max DECFINAL_STACK (Z.max DECINIT_STACK 16))).
  Hypothesis METH0 : METH_mem m0.
  (* [comment removed for export] *)
  Variable B0 : biorep.
  Hypothesis AH0 : rw_cells rsegs m0 a (bio_cells B0).
  Hypothesis BF0 : 0 <= bio_flags B0 < 2^31.
  Hypothesis BNL : Z.land (bio_flags B0) BIO_FLAGS_BASE64_NO_NL = BIO_FLAGS_BASE64_NO_NL.

  (* [comment removed for export] *)
  Local Ltac facts :=
    let T := fresh in
    pose proof X1 as T; unfold blocks_B64F, blocks_MEMBIO in T; rewrite !Forall_cons_iff, !Forall_nil_iff in T;
    destruct T as ((hA_M & hA_BB & hA_BM & hA_RP & _) & (hC_M & hC_BB & hC_BM & hC_RP & _) & (hE_M & hE_BB & hE_BM & hE_RP & _) & _);
    pose proof X2 as T; unfold blocks_B64F in T; rewrite !Forall_cons_iff, !Forall_nil_iff in T; destruct T as (hP_A & hP_C & hP_E & _);
    pose proof X3 as T; unfold blocks_MEMBIO in T; rewrite !Forall_cons_iff, !Forall_nil_iff in T; destruct T as (hO_M & hO_BB & hO_BM & hO_RP & _);
    pose proof X6 as T; unfold blocks_B64F in T; rewrite !Forall_cons_iff, !Forall_nil_iff in T; destruct T as (hO_A & hO_C & hO_E & _);
    pose proof APB as T; unfold B64F_apart in T; destruct T as (hAC & hAE & hCE);
    pose proof MSP as T; unfold MEMBIO_sep, MEMBIO_apart in T;
    destruct T as ((hM_BB & hM_BM & hM_RP & hBB_BM & hBB_RP & hBM_RP) & hP_M & hP_BB & hP_BM & hP_RP);
    pose proof X4 as hX4; pose proof X5 as hX5; pose proof OUTW as hOUTW;
    assert (hOUTW2 : out0 + outl0 + 208 <= bv_unsigned sp \/ bv_unsigned sp <= out0) by (pose proof LOS; lia);
    cbn [blk_addr blk_size fst snd] in hA_M, hA_BB, hA_BM, hA_RP, hC_M, hC_BB, hC_BM, hC_RP, hE_M, hE_BB, hE_BM, hE_RP, hP_A, hP_C, hP_E,
      hO_M, hO_BB, hO_BM, hO_RP, hO_A, hO_C, hO_E;
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, O_METH_BREAD, A_mem_buf_method in
      hA_M, hA_BB, hA_BM, hA_RP, hC_M, hC_BB, hC_BM, hC_RP, hE_M, hE_BB, hE_BM, hE_RP, hP_A, hP_C, hP_E,
      hO_M, hO_BB, hO_BM, hO_RP, hO_A, hO_C, hO_E, hAC, hAE, hCE, hM_BB, hM_BM, hM_RP, hBB_BM, hBB_RP, hBM_RP, hP_M, hP_BB, hP_BM, hP_RP, hX5;
    repeat match goal with H : _ \/ _ |- _ => hide H end.
  (* [comment removed for export] *)
  Local Ltac nums :=
    hcb; pose proof (word_range sp) as SPR;
    pose proof BLW as hBLW; unfold B64F_below, BIO_SIZE, B64CTX_SIZE in hBLW;
    pose proof MBW as hMBW; unfold MEMBIO_below, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in hMBW;
    pose proof RBc as hRBc; unfold rblock_range, B64CTX_SIZE in hRBc; destruct hRBc as (hRBc1 & _ & _ & hRBc3 & hRBc4);
    pose proof RBe as hRBe; unfold rblock_range in hRBe; destruct hRBe as (hRBe1 & _ & _ & hRBe3 & hRBe4);
    pose proof RBa as hRBa; unfold rblock_range, BIO_SIZE in hRBa; destruct hRBa as (hRBa1 & _ & _ & hRBa3 & hRBa4);
    pose proof MRB as hMRB; unfold rblock_range, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in hMRB;
    destruct hMRB as ((hM1 & _ & _ & hM3 & hM4) & (hBB1 & _ & _ & hBB3 & hBB4) & (hBM1 & _ & _ & hBM3 & hBM4) & (hRP1 & _ & _ & hRP3 & hRP4));
    hide hRBc4; hide hRBe4; hide hRBa4; hide hM4; hide hBB4; hide hBM4; hide hRP4;
    pose proof LOS as hLOS;
    assert (hLOSr : lo <= bv_unsigned sp + -192 - BIOREAD_STACK) by (clear - hLOS; lia);
    assert (hLOSu : lo <= bv_unsigned sp + -192 - DECUPDATE_STACK) by (clear - hLOS; lia);
    assert (hLOSf : lo <= bv_unsigned sp + -192 - DECFINAL_STACK) by (clear - hLOS; lia);
    assert (hLOSi : lo <= bv_unsigned sp + -192 - DECINIT_STACK) by (clear - hLOS; lia);
    assert (hLOS16 : lo <= bv_unsigned sp + -192 - 16) by (clear - hLOS; lia);
    clear hLOS;
    pose proof TL as hTL; unfold zlength in hTL.
  (* [comment removed for export] *)
  Local Ltac subtac := clear X4 X5 OUTW; intros x Hx; unfold WL in Hx; cbn [outside MEMBIO_foot ENCCTX_foot mb_bm mset] in Hx |- *;
    unfold BIO_SIZE, BUFMEM_SIZE, ENCCTX_SIZE in Hx |- *;
    pose proof LOS as L; assert (L16 : lo <= bv_unsigned sp + -192 - 16) by (clear - L; lia); clear L;
    pose proof BLW as BL; unfold B64F_below, BIO_SIZE, B64CTX_SIZE in BL;
    pose proof MBW as MW; unfold MEMBIO_below, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in MW; pose proof (word_range sp) as SPR; lia.
  Lemma subW_nil : sub_fp [] WL.  Proof. intros x Hx. exact I. Qed.
  Lemma subW_head : sub_fp [(sp', bv_unsigned sp)] WL.  Proof. subtac. Qed.
  Lemma subW_read : sub_fp ((lo, sp') :: (ctx + 1542, ctx + 1542 + 1024) :: [(mb, mb + BIO_SIZE); (mb_bm M0, mb_bm M0 + BUFMEM_SIZE)]) WL.  Proof. subtac. Qed.
  Lemma subW_d1 : sub_fp [(sp' - 16, sp'); (ctx, ctx + 40)] WL.  Proof. subtac. Qed.
  Lemma subW_du : sub_fp ((lo, sp') :: [(ctx + 40, ctx + 40 + 1502); (ctx, ctx + 4); (enc, enc + ENCCTX_SIZE)]) WL.  Proof. subtac. Qed.
  Lemma subW_hdr : sub_fp [(ctx, ctx + 40)] WL.  Proof. subtac. Qed.
  Lemma subW_mc : forall o i, out0 <= o -> o + i <= out0 + outl0 -> sub_fp [(o, o + i)] WL.  Proof. intros o i H1 H2. subtac. Qed.
  Lemma subW_mcl : sub_fp [(sp', bv_unsigned sp); (ctx, ctx + 40)] WL.  Proof. subtac. Qed.
  Lemma subW_eof1 : sub_fp [(sp' - 16, sp')] WL.  Proof. subtac. Qed.
  Lemma subW_df : sub_fp ((lo, sp') :: [(sp' + 84, sp' + 84 + 4)]) WL.  Proof. subtac. Qed.
  Lemma subW_di : sub_fp ((lo, sp') :: ENCCTX_foot enc) WL.  Proof. subtac. Qed.
  (* [comment removed for export] *)
  Local Ltac extw MU WM MUc WMc :=
    lazymatch type of MU with munch ?Wl ?mz ?ma =>
    lazymatch type of MUc with munch ?Wc ma ?mb =>
      let T := fresh "MUx" in
      assert (T : munch Wl mz mb)
        by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUc];
            first [ apply subW_nil | apply subW_head | apply subW_read | apply subW_d1 | apply subW_du | apply subW_hdr | apply subW_mcl
                  | apply subW_eof1 | apply subW_df | apply subW_di | apply subW_mc; unfold zlength in *; lia ]);
      clear MU MUc; rename T into MU;
      let T2 := fresh "WMx" in pose proof (wmono_trans _ _ _ _ WM WMc) as T2; clear WM WMc; rename T2 into WM
    end end.

  (* [comment removed for export] *)
  Definition HINV (m : mem) (used : nat) (d acc : list Z) (fl nr c vout voutl : Z) (jb jt jo j16 j8 : list byte) : Prop :=
       rw_cells rsegs m sp' (rdframe ctx mb a vout voutl (zlength acc) j16 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
    /\ rw_cells rsegs m ctx (rdhdr 0 0 0 c enc)
    /\ rw_cells rsegs m (ctx + 40) [CB 1502 jb] /\ rw_cells rsegs m (ctx + 1542) [CB 1024 jt]
    /\ ENCCTX LB m enc d (bf_eid R)
    /\ MEMBIO LB m mb (mset M0 (Z.of_nat used) fl nr)
    /\ bytes_at rsegs m (mb_buf M0) txt
    /\ rw_cells rsegs m out0 [CB (length acc) (map b8 acc); CB (Z.to_nat outl0 - length acc) jo]
    /\ B64TAB m /\ mem_inv rsegs m /\ stk rsegs m lo sp'
    /\ munch WL m0 m /\ wmono rsegs m0 m.

  (* [comment removed for export] *)
  Definition HEADMS (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 : word) (outlc outc : Z) (m : mem) : machine_state :=
    MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 sp (Z_to_bv 64 outlc) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 outc) (Z_to_bv 64 a) (Z_to_bv 64 ctx) (Z_to_bv 64 mb) (Z_to_bv 64 0) (Z_to_bv 64 1024) s8
             (Z_to_bv 64 (ctx + 1542)) s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 RD_HEAD) fc None m (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition EXITQ (res : b64r_res) : machine_state -> Prop := fun ms' =>
    exists m' (rcf c' vout' voutl' fl' nr' bl' bo' : Z) (d' : list Z) (jb' jt' jo' j16' j8' : list byte)
           (ra' t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
         ms' = MS (mkR ra' (Z_to_bv 64 sp') gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 a) s4 s5 (Z_to_bv 64 rcf) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RD_EXIT) fc None m' (seg_rom rsegs)
      /\ br_rv res = (if zlength (br_out res) =? 0 then rcf else zlength (br_out res))
      /\ (rcf = 0 \/ rcf = -1) /\ (c' <= 0 \/ 0 < zlength (br_out res)) /\ - 2^31 <= c' < 2^31
      /\ zlength (br_out res) <= outl0 /\ (br_used res <= length txt)%nat /\ 0 <= fl' < 2^31
      /\ rw_cells rsegs m' sp' (rdframe ctx mb a vout' voutl' (zlength (br_out res)) j16' j8' q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
      /\ rw_cells rsegs m' ctx (rdhdr bl' bo' 0 c' enc)
      /\ rw_cells rsegs m' (ctx + 40) [CB 1502 jb'] /\ rw_cells rsegs m' (ctx + 1542) [CB 1024 jt']
      /\ ENCCTX LB m' enc d' (bf_eid R)
      /\ MEMBIO LB m' mb (mset M0 (Z.of_nat (br_used res)) fl' nr')
      /\ bytes_at rsegs m' (mb_buf M0) txt
      /\ rw_cells rsegs m' out0 [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl0 - length (br_out res)) jo']
      /\ B64TAB m' /\ mem_inv rsegs m' /\ stk rsegs m' lo sp'
      /\ munch WL m0 m' /\ wmono rsegs m0 m'.

  (* [comment removed for export] *)
  Definition READQ (used : nat) (d acc : list Z) (c : Z) (n : Z) : machine_state -> Prop := fun ms' =>
    exists m1 (fl nr : Z) (jb jt jo j16 j8 : list byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 : word),
         ms' = MS (mkR (Z_to_bv 64 RD_RA_READ) (Z_to_bv 64 sp') gp tp t0 t1 t2 sp (Z_to_bv 64 (outl0 - zlength acc)) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (out0 + zlength acc)) (Z_to_bv 64 a) (Z_to_bv 64 ctx) (Z_to_bv 64 mb) (Z_to_bv 64 0) (Z_to_bv 64 1024) s8
                       (Z_to_bv 64 (ctx + 1542)) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RD_RA_READ) fc None m1 (seg_rom rsegs)
      /\ n = Z.min 1024 (zlength txt - Z.of_nat used) /\ 0 <= fl < 2^31 /\ Z.land fl 8 = 0
      /\ rw_cells rsegs m1 sp' (rdframe ctx mb a (out0 + zlength acc) (outl0 - zlength acc) (zlength acc) j16 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
      /\ rw_cells rsegs m1 ctx (rdhdr 0 0 0 c enc)
      /\ rw_cells rsegs m1 (ctx + 40) [CB 1502 jb]
      /\ rw_cells rsegs m1 (ctx + 1542) [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn used txt)); CB (1024 - Z.to_nat n) jt]
      /\ ENCCTX LB m1 enc d (bf_eid R)
      /\ MEMBIO LB m1 mb (mset M0 (Z.of_nat used + n) fl nr)
      /\ bytes_at rsegs m1 (mb_buf M0) txt
      /\ rw_cells rsegs m1 out0 [CB (length acc) (map b8 acc); CB (Z.to_nat outl0 - length acc) jo]
      /\ B64TAB m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo sp'
      /\ munch WL m0 m1 /\ wmono rsegs m0 m1.

  (* [comment removed for export] *)
  Definition DUQ (used : nat) (d acc : list Z) (c : Z) (n : Z) : machine_state -> Prop := fun ms' =>
    let data := firstn (Z.to_nat n) (skipn used txt) in
    let r := decode_update d (map bv_unsigned data) in
    exists m3 (fl nr : Z) (jb jt jo j16 j8 : list byte) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
         ms' = MS (mkR (Z_to_bv 64 RD_RA_DU) (Z_to_bv 64 sp') gp tp t0 t1 t2 sp (Z_to_bv 64 0) (Z_to_bv 64 (dr_rv r)) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 n) (Z_to_bv 64 a) (Z_to_bv 64 ctx) (Z_to_bv 64 mb) (Z_to_bv 64 0) (Z_to_bv 64 1024) (Z_to_bv 64 n)
                       (Z_to_bv 64 (ctx + 1542)) s10 (Z_to_bv 64 n) t3 t4 t5 t6)
                  F (Z_to_bv 64 RD_RA_DU) fc None m3 (seg_rom rsegs)
      /\ n = Z.min 1024 (zlength txt - Z.of_nat used) /\ length data = Z.to_nat n /\ 0 <= fl < 2^31 /\ (length (dr_out r) <= 1502)%nat
      /\ rw_cells rsegs m3 sp' (rdframe ctx mb a (out0 + zlength acc) (outl0 - zlength acc) (zlength acc) j16 j8 q11 q10 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra)
      /\ rw_cells rsegs m3 ctx (rdhdr (zlength (dr_out r)) 0 0 c enc)
      /\ rw_cells rsegs m3 (ctx + 40) [CB (length (dr_out r)) (map b8 (dr_out r)); CB (1502 - length (dr_out r)) jb]
      /\ rw_cells rsegs m3 (ctx + 1542) [CB (Z.to_nat n) data] /\ rw_cells rsegs m3 (ctx + 1542 + n) [CB (1024 - Z.to_nat n) jt]
      /\ ENCCTX LB m3 enc (dr_d r) (bf_eid R)
      /\ MEMBIO LB m3 mb (mset M0 (Z.of_nat used + n) fl nr)
      /\ bytes_at rsegs m3 (mb_buf M0) txt
      /\ rw_cells rsegs m3 out0 [CB (length acc) (map b8 acc); CB (Z.to_nat outl0 - length acc) jo]
      /\ mem_inv rsegs m3 /\ stk rsegs m3 lo sp'
      /\ munch WL m0 m3 /\ wmono rsegs m0 m3.

  (* [comment removed for export] *)
  Definition TRIPQ (used : nat) (d acc : list Z) (n : Z) : machine_state -> Prop := fun ms' =>
    let chunk := firstn 1024 (skipn used TXT) in
    let r := decode_update d chunk in
    let used' := (used + length chunk)%nat in
    let i := Z.min (zlength (dr_out r)) (outl0 - zlength acc) in
    let acc' := acc ++ firstn (Z.to_nat i) (dr_out r) in
       (dr_rv r < 0 /\ EXITQ (mkBR (if zlength acc =? 0 then 0 else zlength acc) acc used') ms')
    \/ (0 <= dr_rv r /\ i = outl0 - zlength acc /\ EXITQ (mkBR (zlength acc + i) acc' used') ms')
    \/ (0 <= dr_rv r /\ i < outl0 - zlength acc
        /\ (length (dr_d r) = 0%nat \/ Nat.modulo (length (dr_d r)) 4 <> 0%nat)
        /\ exists m' fl' nr' jb' jt' jo' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 : word),
             ms' = HEADMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 (outl0 - zlength acc') (out0 + zlength acc') m'
          /\ exists j16 j8, HINV m' used' (dr_d r) acc' fl' nr' (dr_rv r) (out0 + zlength acc) (outl0 - zlength acc) jb' jt' jo' j16 j8).

  (* [comment removed for export] *)
  Lemma rd_pre : forall (used : nat) (d acc : list Z) (m : mem) (fl nr c vout voutl : Z) (jb jt jo j16 j8 : list byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 : word),
    (used <= length txt)%nat -> zlength acc < outl0 -> 0 < c < 2^31 ->
    HINV m used d acc fl nr c vout voutl jb jt jo j16 j8 ->
    evt rsegs (READQ used d acc c (Z.min 1024 (zlength txt - Z.of_nat used)))
      (HEADMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 (outl0 - zlength acc) (out0 + zlength acc) m).
  Proof.
    intros until t6. intros USED ACC C HI.
    destruct HI as (FR & HD & BUF & TMP & ENC & MB & TXTB & OUTB & TAB & MI & ST & MU & WM).
    nums. facts. mbnum MB. unfold HEADMS. unfold zlength in *.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply rd_head; try exact FR; try exact HD; try exact ST; try exact MI.
      all: unfold B64CTX_SIZE; clear - C ACC OUTL0 OUT0 OUTE hRBc1 hBLW hLOS16 SPR; lia. }
    cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HD1).
    carryh MU1 WM1. extw MU WM MU1 WM1.
    (* [comment removed for export] *)
    pose proof (@bioread_body HCEIL) as BRM. unfold bioread_mem_stmt in BRM.
    assert (METH1 : METH_mem m1).
    { unfold METH_mem in METH0 |- *. eapply rw_cells_transport; [exact METH0| exact MU| exact WM|].
      unfold WL. unfold A_mem_buf_method, O_METH_BREAD. unhide hX5. unhide hRBc4. unhide hRBe4. unhide hM4. unhide hBM4. djsk. }
    eapply evt_cut.
    { eapply BRM with (a := mb) (out := bf_ctx R + 1542) (outl := 1024) (R := mset M0 (Z.of_nat used) fl nr) (ds := txt) (junk := jt) (lo := lo) (LB := LB);
        clear BRM; try reflexivity; try exact MB; try exact ST1; try exact MI1; try exact METH1; try exact TXTB; try exact TMP; try exact MBW; try exact MSP; try exact CEIL.
      all: rewrite ?unsigned_lit by (clear - SPR hLOS16 hRBc1 hBLW; lia).
      all: try exact ST1; try exact hLOSr; try (cbn [mb_buf mb_len mset]; first [exact TXTB | exact hTL]).
      1: clear; lia.
      (* [comment removed for export] *)
      unfold memrd_out. cbn [mb_buf mb_len mset]. unfold blocks_MEMBIO. cbn [mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset].
      split; [clear - hBLW; lia|]. split; [clear - hRBc1; lia|]. split; [clear -hBLW SPR hLOS16; lia|].
      split. { unhide hC_M. unhide hC_BB. unhide hC_BM. unhide hC_RP. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
               apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
               cbn [blk_addr blk_size fst snd]; clear - hC_M hC_BB hC_BM hC_RP; lia. }
      split; [unhide hP_C; clear - hP_C; lia|].
      unhide hRBc4. unfold A_mem_buf_method, O_METH_BREAD. clear - hRBc4. lia. }
    cbv beta. intros ms2 PO. unfold memrd_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & jt' & -> & MU2 & WM2 & MI2 & ST2 & MB2 & TXTB2 & TMP2 & _).
    rewrite ?unsigned_lit in MU2 by (clear - SPR hLOS16 hRBc1 hBLW; lia). rewrite ?unsigned_lit in ST2 by (clear - SPR hLOS16 hRBc1 hBLW; lia).
    cbn [mb_buf mset] in TXTB2. clear TXTB MI1.
    unfold MEMBIO_foot in MU2. cbn [mb_bm mset] in MU2.
    carryh MU2 WM2. extw MU WM MU2 WM2.
    set (n := mb_rdn (mset M0 (Z.of_nat used) fl nr) 1024) in *.
    assert (EN : n = Z.min 1024 (Z.of_nat (length txt) - Z.of_nat used)).
    { subst n. unfold mb_rdn, mb_avail. cbn [mb_len mb_pos mset]. clear - hTL. lia. }
    clearbody n. subst n.
    rewrite mb_after_read_mset in MB2. unfold mb_take in TMP2. cbn [mb_pos mset] in TMP2. rewrite Nat2Z.id in TMP2.
    assert (NB : 0 <= Z.min 1024 (Z.of_nat (length txt) - Z.of_nat used) <= Z.of_nat (length txt) - Z.of_nat used) by (clear - USED; lia).
    rewrite length_firstn, length_skipn, Nat.min_l in TMP2 by (clear - NB USED; lia).
    change (Z.to_nat 1024) with 1024%nat in TMP2.
    mbnum MB2.
    replace (ret_pc (Z_to_bv 64 RD_RA_READ)) with (Z_to_bv 64 RD_RA_READ) by (symmetry; apply ret_pc_even; [unfold RD_RA_READ; clear; lia| reflexivity]).
    apply evt_done. unfold READQ.
    eexists m2, _, _, jb, _, jo, j16, j8. eexists _, _, _, _, _, _, _, _, _, _, s8, s10, s11, _, _, _, _.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact MBF0|]. split; [apply land_lnot15_8|].
    split; [exact FR1|]. split; [exact HD1|]. split; [exact BUF|]. split; [exact TMP2|]. split; [exact ENC|].
    split; [exact MB2|]. split; [exact TXTB2|]. split; [exact OUTB|].
    split; [exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI2)|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact MU| exact WM].
  Qed.

  Lemma rd_trip_eof : forall (used : nat) (d acc : list Z) (c : Z) ms,
    (used = length txt)%nat -> zlength acc < outl0 -> (length d = 0%nat \/ Nat.modulo (length d) 4 <> 0%nat) ->
    READQ used d acc c 0 ms ->
    evt rsegs (EXITQ (mkBR (if zlength acc =? 0 then (if decode_final_rv d <? 0 then -1 else 0) else zlength acc) acc used)) ms.
  Proof.
    intros used d acc c ms USED ACC DMOD RQ. unfold READQ in RQ.
    destruct RQ as (m1 & fl & nr & jb & jt & jo & j16 & j8 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s10 & s11 & t3 & t4 & t5 & t6
                    & -> & EN & FLR1 & FL8 & FR & HD & BUF & TMP & ENC & MB & TXTB & OUTB & TAB & MI & ST & MU & WM).
    nums. facts. rewrite Z.add_0_r in MB. mbnum MB. unfold zlength in *.
    (* [comment removed for export] *)
    pose proof MB as MBc. unfold MEMBIO in MBc. destruct MBc as (NBC & _).
    eapply evt_cut.
    { eapply rd_eof1 with (NB := membio_bio (mset M0 (Z.of_nat used) fl nr));
        try exact FR; try exact HD; try exact ST; try exact MI; try exact NBC; try exact CEIL.
      all: cbn [bio_flags membio_bio mb_flags mset]; try exact FLR1; try exact FL8.
      all: unfold B64CTX_SIZE, BIO_SIZE; clear - hRBc1 hBLW hMBW hM1 hLOS16 SPR; lia. }
    cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & ST2 & NBC2 & FR2 & HD2). clear FR HD ST NBC.
    carryh MU2 WM2. extw MU WM MU2 WM2.
    (* [comment removed for export] *)
    destruct (rdframe_split_num _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR2) as (FRa & NUM & FRb & L4). clear FR2.
    pose proof (@decfinal_spec HCEIL) as DFS. unfold decfinal_stmt in DFS.
    eapply evt_cut.
    { eapply DFS with (a := bf_enc R) (outlp := bv_unsigned sp + -192 + 84) (d := d) (p := bf_eid R) (lo := lo) (LB := LB); clear DFS;
        try reflexivity; try exact ENC; try exact NUM; try exact DMOD; try exact CEIL.
      all: rewrite ?unsigned_lit by (clear - SPR hLOS16 hRBc1 hBLW; lia).
      all: try exact ST2; try exact MI2; try exact hLOSf; try exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI2).
      1: f_equal; clear; lia.
      all: unfold ENCCTX_SIZE; clear - hBLW hLOS16 SPR; lia. }
    cbv beta. intros ms3 PO. unfold c8_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & -> & MU3 & WM3 & MI3 & ST3 & ENC3 & NUM3 & _).
    rewrite ?unsigned_lit in MU3 by (clear - SPR hLOS16 hRBc1 hBLW; lia). rewrite ?unsigned_lit in ST3 by (clear - SPR hLOS16 hRBc1 hBLW; lia).
    clear ENC NUM MI2.
    carryh MU3 WM3. extw MU WM MU3 WM3.
    pose proof (rdframe_join_num _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRa L4 NUM3 FRb) as FR3. clear FRa NUM3 FRb.
    replace (ret_pc (Z_to_bv 64 RD_RA_DF)) with (Z_to_bv 64 RD_RA_DF) by (symmetry; apply ret_pc_even; [unfold RD_RA_DF; clear; lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof (decode_final_rv_cases d) as RVC.
    eapply evt_cut.
    { eapply rd_eof2; try exact FR3; try exact HD2; try exact ST3; try exact MI3.
      1: clear - RVC; lia.
      all: unfold B64CTX_SIZE; clear - hRBc1 hBLW hLOS16 SPR; lia. }
    cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & HD4). clear FR3 HD2 ST3.
    carryh MU4 WM4. extw MU WM MU4 WM4.
    (* [comment removed for export] *)
    destruct (ENCCTX_CB92 _ _ _ _ _ ENC3) as ((old & ENCB) & _ & _ & _).
    pose proof (@decinit_spec HCEIL) as DIS. unfold decinit_stmt in DIS.
    eapply evt_cut.
    { eapply DIS with (a := bf_enc R) (p := bf_eid R) (lo := lo) (LB := LB); clear DIS;
        try reflexivity; try exact ENCB; try exact INe; try exact RBe.
      all: rewrite ?unsigned_lit by (clear - SPR hLOS16 hRBc1 hBLW; lia).
      all: try exact ST4; try exact MI4; try exact hLOSi.
      all: unfold ENCCTX_SIZE; clear - hBLW; lia. }
    cbv beta. intros ms5 PO. unfold c8_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m5 & -> & -> & MU5 & WM5 & MI5 & ST5 & ENC5 & _).
    rewrite ?unsigned_lit in MU5 by (clear - SPR hLOS16 hRBc1 hBLW; lia). rewrite ?unsigned_lit in ST5 by (clear - SPR hLOS16 hRBc1 hBLW; lia).
    clear ENC3 ENCB MI4. unfold ENCCTX_foot in MU5.
    carryh MU5 WM5. extw MU WM MU5 WM5.
    replace (ret_pc (Z_to_bv 64 RD_RA_DI2)) with (Z_to_bv 64 RD_RA_DI2) by (symmetry; apply ret_pc_even; [unfold RD_RA_DI2; clear; lia| reflexivity]).
    (* [comment removed for export] *)
    set (rc := if decode_final_rv d <? 0 then -1 else 0) in *.
    assert (RC : rc = -1 \/ rc = 0) by (subst rc; destruct (decode_final_rv d <? 0); [left|right]; reflexivity).
    eapply evt_cut.
    { eapply rd_eof3; try exact FR4; try exact HD4; try exact ST5; try exact MI5.
      1: exact RC.
      all: unfold B64CTX_SIZE; clear - hRBc1 hBLW hLOS16 SPR; lia. }
    cbv beta. intros ms6 (m6 & -> & MU6 & WM6 & MI6 & ST6 & FR6 & HD6). clear FR4 HD4 ST5.
    carryh MU6 WM6. extw MU WM MU6 WM6.
    assert (TMP' : rw_cells rsegs m6 (bf_ctx R + 1542) [CB 1024 jt]).
    { eapply rw_cells_recut; [exact TMP| | cbn; rewrite app_nil_r; reflexivity].
      destruct TMP as [[WF _] _]. cbn in WF |- *. tauto. }
    clear TMP.
    apply evt_done. unfold EXITQ. cbn [br_rv br_out br_used].
    exists m6, rc, rc, (out0 + Z.of_nat (length acc)), (outl0 - Z.of_nat (length acc)), fl, nr, 0, 0, (@nil Z), jb, jt, jo, j16, (firstn 4 j8 ++ le4 (wz 0)).
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s10, s11, _, _, _, _.
    split; [reflexivity|].
    split; [reflexivity|].
    split; [clear - RC; lia|]. split; [left; clear - RC; lia|]. split; [clear - RC; lia|].
    split; [unfold zlength; clear - ACC; lia|]. split; [clear - USED; lia|]. split; [exact FLR1|].
    split; [exact FR6|]. split; [exact HD6|]. split; [exact BUF|]. split; [exact TMP'|]. split; [exact ENC5|].
    split; [exact MB|]. split; [exact TXTB|]. split; [exact OUTB|].
    split; [exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI6)|]. split; [exact MI6|]. split; [exact ST6|]. split; [exact MU| exact WM].
  Qed.

  Lemma rd_trip_du : forall (used : nat) (d acc : list Z) (c n : Z) ms,
    (used < length txt)%nat -> zlength acc < outl0 -> 0 < n -> 0 < c < 2^31 ->
    READQ used d acc c n ms ->
    evt rsegs (DUQ used d acc c n) ms.
  Proof.
    intros used d acc c n ms USED ACC NPOS C RQ. unfold READQ in RQ.
    destruct RQ as (m1 & fl & nr & jb & jt & jo & j16 & j8 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s10 & s11 & t3 & t4 & t5 & t6
                    & -> & EN & FLR1 & FL8 & FR & HD & BUF & TMP & ENC & MB & TXTB & OUTB & TAB & MI & ST & MU & WM).
    nums. facts. mbnum MB. unfold zlength in *.
    set (data := firstn (Z.to_nat n) (skipn used txt)) in *.
    assert (NB : 0 < n <= 1024 /\ n <= Z.of_nat (length txt) - Z.of_nat used) by (clear - EN NPOS USED; lia).
    assert (LD : length data = Z.to_nat n) by (subst data; rewrite length_firstn, length_skipn; clear - NB; lia).
    hide EN.
    (* [comment removed for export] *)
    assert (AH : rw_cells rsegs m1 a (bio_cells B0)).
    { eapply rw_cells_transport; [exact AH0| exact MU| exact WM|]. unfold WL. djs. }
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply rd_data1 with (B := B0) (n := n); try exact AH; try exact FR; try exact HD; try exact ST; try exact MI; try exact CEIL; try exact BF0; try exact BNL.
      all: try (unhide hAC; exact hAC).
      all: unfold B64CTX_SIZE, BIO_SIZE; clear - NB hRBc1 hRBa1 hBLW hLOS16 SPR; lia. }
    cbv beta. intros ms2 (m2 & t0' & t1' & t2' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU2 & WM2 & MI2 & ST2 & AH2 & FR2 & HD2). clear FR HD ST AH.
    carryh MU2 WM2. extw MU WM MU2 WM2.
    (* [comment removed for export] *)
    unfold rdhdr in HD2. change (rw_cells rsegs m2 ctx ([C4 (wz 0)] ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0); C8 (wz enc)])) in HD2.
    apply (proj1 (rw_cells_app rsegs m2 ctx _ _)) in HD2. destruct HD2 as [HD0 HDR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HDR.
    change (rw_cells rsegs m2 (ctx + 1542) ([CB (Z.to_nat n) data] ++ [CB (1024 - Z.to_nat n) jt])) in TMP.
    apply (proj1 (rw_cells_app rsegs m2 _ _ _)) in TMP. destruct TMP as [TMPd TMPj]. cbn [cells_size csize Nat.add] in TMPj.
    replace (bf_ctx R + 1542 + Z.of_nat (Z.to_nat n + 0)) with (bf_ctx R + 1542 + n) in TMPj by (clear - NB; lia).
    destruct (rw_cells_CB_bytes_at _ _ _ _ _ TMPd) as [DATAB _].
    destruct (ENCCTX_CB92 _ _ _ _ _ ENC) as (_ & _ & _ & DL).
    pose proof (@decupdate_spec HCEIL) as DUS. unfold decupdate_stmt in DUS.
    eapply evt_cut.
    { eapply DUS with (a := bf_enc R) (out := bf_ctx R + 40) (outlp := bf_ctx R) (inp_a := bf_ctx R + 1542) (inl := n) (outsz := 1502) (ov := 0)
                      (d := d) (inp := data) (junk := jb) (p := bf_eid R) (lo := lo) (LB := LB); clear DUS;
        try reflexivity; try exact ENC; try exact DATAB; try exact BUF; try exact HD0; try exact CEIL.
      all: rewrite ?unsigned_lit by (clear - SPR hLOS16 hRBc1 hBLW; lia).
      all: try exact ST2; try exact MI2; try exact hLOSu; try exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI2).
      all: unfold ENCCTX_SIZE, du_outcap, zlength; unhide hCE; clear - hCE NB LD DL hRBc1 hBLW hLOS16 SPR; lia. }
    cbv beta. intros ms3 PO. unfold c8_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & -> & -> & MU3 & WM3 & MI3 & ST3 & ENC3
                    & (jb' & BUF3 & HD03 & DATAB3 & _ & LEN3)).
    rewrite ?unsigned_lit in MU3 by (clear - SPR hLOS16 hRBc1 hBLW; lia). rewrite ?unsigned_lit in ST3 by (clear - SPR hLOS16 hRBc1 hBLW; lia).
    clear ENC BUF HD0 DATAB MI2.
    carryh MU3 WM3. extw MU WM MU3 WM3.
    set (r := decode_update d (map bv_unsigned data)) in *.
    assert (HD3 : rw_cells rsegs m3 (bf_ctx R) (rdhdr (zlength (dr_out r)) 0 0 c (bf_enc R))).
    { unfold rdhdr. change (rw_cells rsegs m3 (bf_ctx R) ([C4 (wz (zlength (dr_out r)))] ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 2); C4 (wz 1); C4 (wz c); C4 (wz 0); C8 (wz (bf_enc R))])).
      apply (proj2 (rw_cells_app rsegs m3 _ _ _)). split; [exact HD03|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact HDR. }
    clear HD03 HDR.
    replace (ret_pc (Z_to_bv 64 RD_RA_DU)) with (Z_to_bv 64 RD_RA_DU) by (symmetry; apply ret_pc_even; [unfold RD_RA_DU; clear; lia| reflexivity]).
    apply evt_done. unfold DUQ. cbv zeta. fold data. fold r.
    exists m3, fl, nr, jb', jt, jo, j16, j8. eexists _, _, _, _, _, _, _, _, _, _, s10, _, _, _, _.
    split; [reflexivity|]. split; [unhide EN; exact EN|]. split; [exact LD|]. split; [exact FLR1|]. split; [clear - LEN3; exact LEN3|].
    split; [exact FR2|]. split; [exact HD3|]. split; [exact BUF3|]. split; [exact TMPd|]. split; [exact TMPj|].
    split; [exact ENC3|]. split; [exact MB|]. split; [exact TXTB|]. split; [exact OUTB|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact MU| exact WM].
  Qed.

  Lemma rd_trip_data : forall (used : nat) (d acc : list Z) (c n : Z) ms,
    (used < length txt)%nat -> zlength acc < outl0 -> 0 < n -> 0 < c < 2^31 ->
    READQ used d acc c n ms ->
    evt rsegs (TRIPQ used d acc n) ms.
  Proof.
    intros used d acc c n ms USED ACC NPOS C RQ.
    eapply evt_cut; [eapply rd_trip_du; eauto|]. cbv beta. intros ms3 DQ. unfold DUQ in DQ. cbv zeta in DQ.
    destruct DQ as (m3 & fl & nr & jb & jt & jo & j16 & j8 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s10 & t3 & t4 & t5 & t6
                    & -> & EN & LD & FLR1 & LEN3 & FR & HD & BUF & TMPd & TMPj & ENC & MB & TXTB & OUTB & MI & ST & MU & WM).
    nums. facts. mbnum MB. unfold zlength in *.
    set (data := firstn (Z.to_nat n) (skipn used txt)) in *. set (r := decode_update d (map bv_unsigned data)) in *.
    assert (NB : 0 < n <= 1024 /\ n <= Z.of_nat (length txt) - Z.of_nat used) by (clear - EN NPOS USED; lia).
    assert (CH : firstn 1024 (skipn used TXT) = map bv_unsigned data).
    { subst data. rewrite skipn_map, firstn_map. f_equal.
      destruct (Nat.le_gt_cases 1024 (length txt - used)) as [GE|LT].
      - f_equal. clear - GE EN. lia.
      - rewrite firstn_all2 by (rewrite length_skipn; clear - LT; lia).
        replace (Z.to_nat n) with (length (skipn used txt)) by (rewrite length_skipn; clear - LT EN; lia). symmetry. apply firstn_all. }
    clear EN. unfold TRIPQ. cbv zeta. rewrite !CH. fold r. rewrite length_map, LD. unfold zlength.
    pose proof (decode_update_rv d (map bv_unsigned data)) as KRV. fold r in KRV.
    destruct (Z.lt_ge_cases (dr_rv r) 0) as [KN|KP].
    - (* [comment removed for export] *)
      eapply evt_cut.
      { eapply rd_du_neg; try exact FR; try exact HD; try exact ST; try exact MI.
        all: unfold B64CTX_SIZE; clear - KN KRV hRBc1 hBLW hLOS16 SPR; lia. }
      cbv beta. intros ms4 (m4 & a1x & -> & MU4 & WM4 & MI4 & ST4 & FR4 & HD4). clear FR HD ST.
      carryh MU4 WM4. extw MU WM MU4 WM4.
      apply evt_done. left. split; [exact KN|].
      (* [comment removed for export] *)
      assert (BUF' : rw_cells rsegs m4 (bf_ctx R + 40) [CB 1502 (map b8 (dr_out r) ++ jb)]).
      { eapply rw_cells_recut; [exact BUF| | cbn; rewrite !app_nil_r, ?app_assoc; reflexivity].
        destruct BUF as [[WF _] _]. cbn in WF |- *. rewrite length_app, length_map. split; [| exact I]. clear - WF LEN3. lia. }
      pose proof (rw_cells_CB_join _ _ _ _ _ _ _ TMPd ltac:(rewrite Z2Nat.id by (clear - NB; lia); exact TMPj)) as TMP'.
      replace (Z.to_nat n + (1024 - Z.to_nat n))%nat with 1024%nat in TMP' by (clear - NB; lia).
      unfold EXITQ. cbn [br_rv br_out br_used].
      exists m4, 0, (dr_rv r), (out0 + Z.of_nat (length acc)), (outl0 - Z.of_nat (length acc)), fl, nr, 0, 0, (dr_d r), (map b8 (dr_out r) ++ jb), (data ++ jt), jo, j16, j8.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s10, _, _, _, _, _.
      split; [reflexivity|].
      split; [unfold zlength; reflexivity|].
      split; [left; reflexivity|]. split; [left; clear - KN; lia|]. split; [clear - KN KRV; lia|].
      split; [unfold zlength; clear - ACC; lia|]. split; [clear - NB USED; lia|]. split; [exact FLR1|].
      split; [exact FR4|]. split; [exact HD4|]. split; [exact BUF'|]. split; [exact TMP'|]. split; [exact ENC|].
      split; [replace (Z.of_nat (used + Z.to_nat n)) with (Z.of_nat used + n) by (clear - NB; lia); exact MB|].
      split; [exact TXTB|]. split; [exact OUTB|].
      split; [exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI4)|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact MU| exact WM].
    - (* [comment removed for export] *)
      set (bl := Z.of_nat (length (dr_out r))) in *.
      set (outc := out0 + Z.of_nat (length acc)) in *. set (outlc := outl0 - Z.of_nat (length acc)) in *.
      assert (BLB : 0 <= bl <= 1502) by (clear - LEN3; lia).
      eapply evt_cut.
      { eapply rd_du_pos; try exact FR; try exact HD; try exact ST; try exact MI.
        all: unfold B64CTX_SIZE; zapZ; clear - KP KRV LEN3 ACC OUTL0 OUT0 OUTE hRBc1 hBLW hLOS16 SPR; lia. }
      cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & HD4). clear FR HD ST.
      carryh MU4 WM4. extw MU WM MU4 WM4.
      set (i := Z.min bl outlc) in *.
      assert (IB : 0 <= i <= bl /\ i <= outlc /\ 0 < outlc) by (zapZ; clear - LEN3 ACC; lia).
      assert (Ei1 : bl < outlc -> i = bl) by (zapZ; clear; lia). assert (Ei2 : outlc <= bl -> i = outlc) by (zapZ; clear; lia).
      clearbody i.
      (* [comment removed for export] *)
      pose proof BUF as BUFc. change (rw_cells rsegs m4 (bf_ctx R + 40) ([CB (length (dr_out r)) (map b8 (dr_out r))] ++ [CB (1502 - length (dr_out r)) jb])) in BUFc.
      apply (proj1 (rw_cells_app rsegs m4 _ _ _)) in BUFc. destruct BUFc as [BUFo _].
      destruct (rw_cells_CB_split _ _ _ _ (Z.to_nat i) _ BUFo ltac:(clear - IB; zapZ; lia)) as [SRCc _]. clear BUFo.
      destruct (rw_cells_CB_bytes_at _ _ _ _ _ SRCc) as [SRC LS]. clear SRCc.
      pose proof OUTB as OUTc. change (rw_cells rsegs m4 out0 ([CB (length acc) (map b8 acc)] ++ [CB (Z.to_nat outl0 - length acc) jo])) in OUTc.
      apply (proj1 (rw_cells_app rsegs m4 _ _ _)) in OUTc. destruct OUTc as [OUTa OUTr]. cbn [cells_size csize Nat.add] in OUTr.
      replace (out0 + Z.of_nat (length acc + 0)) with outc in OUTr by (zapZ; clear; lia).
      destruct (rw_cells_CB_split _ _ _ _ (Z.to_nat i) _ OUTr ltac:(clear - IB ACC; zapZ; lia)) as [DST OUTz]. clear OUTr OUTB.
      rewrite Z2Nat.id in OUTz by (clear - IB; lia).
      eapply evt_cut.
      { eapply memcpy_spec with (src := firstn (Z.to_nat i) (map b8 (dr_out r))) (junk := firstn (Z.to_nat i) jo);
          rewrite ?unsigned_lit by (clear - IB BLB OUT0 OUTE ACC OUTL0 hRBc1 hRBc3 HCEILB; zapZ; lia).
        - exact SRC.
        - rewrite LS. reflexivity.
        - exact DST.
        - unhide hO_C. clear - hO_C IB ACC BLB. zapZ. lia.
        - exact MI4. }
      cbv beta. intros ms5 PO. unfold memcpy_post in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & -> & MU5 & WM5 & MI5 & DST5 & SRC5).
      rewrite ?unsigned_lit in MU5 by (clear - IB BLB OUT0 OUTE ACC OUTL0; zapZ; lia).
      rewrite ?unsigned_lit in DST5 by (clear - IB BLB OUT0 OUTE ACC OUTL0; zapZ; lia).
      rewrite ?unsigned_lit in SRC5 by (clear - IB BLB OUT0 OUTE ACC OUTL0 hRBc1 hRBc3 HCEILB; zapZ; lia).
      clear SRC DST MI4.
      carryh MU5 WM5. extw MU WM MU5 WM5.
      replace (ret_pc (Z_to_bv 64 RD_RA_MC)) with (Z_to_bv 64 RD_RA_MC) by (symmetry; apply ret_pc_even; [unfold RD_RA_MC; clear; lia| reflexivity]).
      (* [comment removed for export] *)
      set (acc' := acc ++ firstn (Z.to_nat i) (dr_out r)) in *.
      assert (LA : length acc' = (length acc + Z.to_nat i)%nat).
      { subst acc'. rewrite length_app, length_firstn. clear - IB. zapZ. lia. }
      assert (OUTacc : rw_cells rsegs m5 out0 [CB (length acc') (map b8 acc')]).
      { subst acc'. rewrite map_app, <- firstn_map. replace (length (acc ++ firstn (Z.to_nat i) (dr_out r))) with (length acc + Z.to_nat i)%nat.
        eapply rw_cells_CB_join; [exact OUTa|]. replace (out0 + Z.of_nat (length acc)) with outc by (zapZ; clear; lia). exact DST5. }
      clear OUTa DST5 SRC5. rewrite LA in OUTacc.
      (* [comment removed for export] *)
      replace (Z.of_nat used + n) with (Z.of_nat (used + Z.to_nat n)) in MB by (clear - NB; lia).
      (* [comment removed for export] *)
      assert (BUF' : rw_cells rsegs m5 (bf_ctx R + 40) [CB 1502 (map b8 (dr_out r) ++ jb)]).
      { eapply rw_cells_recut; [exact BUF| | cbn; rewrite !app_nil_r, ?app_assoc; reflexivity].
        destruct BUF as [[WF _] _]. cbn in WF |- *. rewrite length_app, length_map. split; [| exact I]. clear - WF LEN3. lia. }
      pose proof (rw_cells_CB_join _ _ _ _ _ _ _ TMPd ltac:(rewrite Z2Nat.id by (clear - NB; lia); exact TMPj)) as TMP'.
      replace (Z.to_nat n + (1024 - Z.to_nat n))%nat with 1024%nat in TMP' by (clear - NB; lia).
      clear BUF TMPd TMPj.
      destruct (Z.lt_ge_cases bl outlc) as [PART|FULL].
      + (* [comment removed for export] *)
        pose proof (Ei1 PART) as Ei. clear Ei1 Ei2.
        eapply evt_cut.
        { eapply rd_mc_loop; try exact FR4; try exact ST4; try exact MI5.
          all: try (rewrite Ei; exact HD4).
          all: unfold B64CTX_SIZE; generalize Ei; zapZ; clear - PART KP KRV LEN3 ACC OUTL0 OUT0 OUTE hRBc1 hBLW hLOS16 SPR; intros Ei; lia. }
        cbv beta. intros ms6 (m6 & a0x & -> & MU6 & WM6 & MI6 & ST6 & FR6 & HD6). clear FR4 HD4 ST4.
        carryh MU6 WM6. extw MU WM MU6 WM6.
        apply evt_done. right. right.
        split; [exact KP|]. split; [clear - PART Ei; zapZ; lia|].
        split. { subst r. apply decode_update_d; [| exact KP]. intros E. apply (f_equal (@length Z)) in E. rewrite length_map, LD in E. cbn in E. clear - E NB. lia. }
        exists m6, fl, nr, (map b8 (dr_out r) ++ jb), (data ++ jt), (skipn (Z.to_nat i) jo).
        eexists _, _, _, _, a0x, _, _, _, _, _, _, _, _, s10, _, _, _, _, _.
        split.
        { unfold HEADMS. unfold zlength. rewrite LA, Nat2Z.inj_add, Z2Nat.id by (clear - IB; lia).
          replace (outl0 - (Z.of_nat (length acc) + i)) with (outlc - i) by (zapZ; clear; lia).
          replace (out0 + (Z.of_nat (length acc) + i)) with (outc + i) by (zapZ; clear; lia). reflexivity. }
        exists j16, j8. unfold HINV. unfold zlength. rewrite LA, Nat2Z.inj_add, Z2Nat.id by (clear - IB; lia).
        split; [exact FR6|]. split; [exact HD6|]. split; [exact BUF'|]. split; [exact TMP'|]. split; [exact ENC|].
        split. { replace (used + length (map bv_unsigned data))%nat with (used + Z.to_nat n)%nat by (rewrite length_map, LD; reflexivity). exact MB. }
        split; [exact TXTB|].
        split. { change (rw_cells rsegs m6 out0 ([CB (length acc + Z.to_nat i) (map b8 acc')] ++ [CB (Z.to_nat outl0 - (length acc + Z.to_nat i)) (skipn (Z.to_nat i) jo)])).
                 apply (proj2 (rw_cells_app rsegs m6 out0 _ _)). split; [exact OUTacc|]. cbn [cells_size csize Nat.add].
                 replace (out0 + Z.of_nat (length acc + Z.to_nat i + 0)) with (outc + i) by (zapZ; clear - IB; lia).
                 replace (Z.to_nat outl0 - (length acc + Z.to_nat i))%nat with (Z.to_nat outl0 - length acc - Z.to_nat i)%nat by (clear; lia). exact OUTz. }
        split; [exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI6)|]. split; [exact MI6|]. split; [exact ST6|]. split; [exact MU| exact WM].
      + (* [comment removed for export] *)
        pose proof (Ei2 FULL) as Ei. clear Ei1 Ei2.
        clearbody acc'. subst i.
        eapply evt_cut.
        { eapply rd_mc_done; try exact FR4; try exact ST4; try exact MI5; try exact HD4.
          all: unfold B64CTX_SIZE; zapZ; clear - FULL KP KRV LEN3 ACC OUTL0 OUT0 OUTE hRBc1 hBLW hLOS16 SPR; lia. }
        cbv beta. intros ms6 (m6 & a0x & -> & MU6 & WM6 & MI6 & ST6 & FR6 & HD6). clear FR4 HD4 ST4.
        carryh MU6 WM6. extw MU WM MU6 WM6.
        apply evt_done. right. left.
        split; [exact KP|]. split; [clear - FULL; zapZ; lia|].
        unfold EXITQ. cbn [br_rv br_out br_used]. unfold zlength.
        rewrite !LA, !Nat2Z.inj_add, !(Z2Nat.id outlc) by (clear - IB; lia).
        exists m6, 0, (dr_rv r), outc, outlc, fl, nr, (if bl =? outlc then 0 else bl), (if bl =? outlc then 0 else outlc), (dr_d r),
               (map b8 (dr_out r) ++ jb), (data ++ jt), (skipn (Z.to_nat outlc) jo), j16, j8.
        eexists _, _, _, _, _, a0x, _, _, _, _, _, _, _, _, _, _, _, _, _, s10, _, _, _, _, _.
        split; [reflexivity|].
        split. { replace (Z.of_nat (length acc) + outlc =? 0) with false by (symmetry; apply Z.eqb_neq; clear - IB; zapZ; lia). reflexivity. }
        split; [left; reflexivity|]. split; [right; clear - IB; zapZ; lia|]. split; [clear - KP KRV; lia|].
        split; [clear - IB ACC; zapZ; lia|]. split; [clear - NB USED; lia|]. split; [exact FLR1|].
        split; [exact FR6|]. split; [exact HD6|]. split; [exact BUF'|]. split; [exact TMP'|]. split; [exact ENC|].
        split; [rewrite <- Nat2Z.inj_add; exact MB|]. split; [exact TXTB|].
        split. { change (rw_cells rsegs m6 out0 ([CB (length acc + Z.to_nat outlc) (map b8 acc')] ++ [CB (Z.to_nat outl0 - (length acc + Z.to_nat outlc)) (skipn (Z.to_nat outlc) jo)])).
                 apply (proj2 (rw_cells_app rsegs m6 out0 _ _)). split; [exact OUTacc|]. cbn [cells_size csize Nat.add].
                 replace (out0 + Z.of_nat (length acc + Z.to_nat outlc + 0)) with (outc + outlc) by (zapZ; clear - IB; lia).
                 replace (Z.to_nat outl0 - (length acc + Z.to_nat outlc))%nat with (Z.to_nat outl0 - length acc - Z.to_nat outlc)%nat by (clear; lia). exact OUTz. }
        split; [exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI6)|]. split; [exact MI6|]. split; [exact ST6|]. split; [exact MU| exact WM].
  Qed.

  Lemma rd_loop : forall (fuel used : nat) (d acc : list Z) (m : mem) (fl nr c vout voutl : Z) (jb jt jo j16 j8 : list byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 : word),
    (S (length txt - used) <= fuel)%nat -> (used <= length txt)%nat ->
    zlength acc < outl0 -> (length d = 0%nat \/ Nat.modulo (length d) 4 <> 0%nat) -> 0 < c < 2^31 ->
    HINV m used d acc fl nr c vout voutl jb jt jo j16 j8 ->
    evt rsegs (EXITQ (b64r_loop fuel (skipn used TXT) d (zlength acc) (outl0 - zlength acc) acc used))
      (HEADMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 s11 t3 t4 t5 t6 (outl0 - zlength acc) (out0 + zlength acc) m).
  Proof.
    induction fuel as [|fuel IH]; intros until t6; intros FUEL USED ACC DMOD C HI; [lia|].
    assert (LT : length TXT = length txt) by (apply length_map).
    destruct (Nat.eq_dec used (length txt)) as [EOFc|DATAc].
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply rd_pre; eauto|]. cbv beta. intros ms' RQ.
      replace (Z.min 1024 (zlength txt - Z.of_nat used)) with 0 in RQ by (unfold zlength; lia).
      replace (skipn used TXT) with (@nil Z) by (symmetry; apply skipn_all2; lia).
      rewrite b64r_loop_eof by lia.
      eapply rd_trip_eof; eauto.
    - (* [comment removed for export] *)
      eapply evt_cut; [eapply rd_pre; eauto|]. cbv beta. intros ms' RQ.
      eapply evt_cut; [eapply rd_trip_data; [| | | | exact RQ]; unfold zlength in *; lia|]. cbv beta. intros ms2 TQ.
      assert (NE : skipn used TXT <> []).
      { intros E. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. clear - E LT DATAc USED. lia. }
      rewrite b64r_loop_trip by first [lia| exact NE].
      unfold TRIPQ in TQ. cbv zeta in TQ |- *. unfold zlength in TQ |- *.
      set (chunk := firstn 1024 (skipn used TXT)) in *. set (r := decode_update d chunk) in *.
      pose proof (decode_update_rv d chunk) as KRV. fold r in KRV.
      destruct TQ as [(NEG & EX)|[(POS & FULL & EX)|(POS & PART & DMOD' & m' & fl' & nr' & jb' & jt' & jo' & ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s8' & s10' & s11' & t3' & t4' & t5' & t6' & -> & j16' & j8' & HI')]].
      + replace (dr_rv r <? 0) with true by (symmetry; apply Z.ltb_lt; exact NEG). apply evt_done. exact EX.
      + replace (dr_rv r <? 0) with false by (symmetry; apply Z.ltb_ge; exact POS).
        rewrite FULL. rewrite FULL in EX.
        destruct (dr_rv r =? 0).
        * replace (Z.of_nat (length acc) + (outl0 - Z.of_nat (length acc)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          apply evt_done. exact EX.
        * rewrite b64r_loop_outl_le0 by (clear - FUEL USED DATAc; lia). apply evt_done. exact EX.
      + replace (dr_rv r <? 0) with false by (symmetry; apply Z.ltb_ge; exact POS).
        set (i := Z.min (Z.of_nat (length (dr_out r))) (outl0 - Z.of_nat (length acc))) in *.
        set (acc' := acc ++ firstn (Z.to_nat i) (dr_out r)) in *.
        assert (IB : 0 <= i <= Z.of_nat (length (dr_out r))) by (unfold i in *; lia).
        assert (LA : Z.of_nat (length acc') = Z.of_nat (length acc) + i).
        { unfold acc'. rewrite length_app, length_firstn. clear - IB. lia. }
        rewrite <- !LA. replace (outl0 - Z.of_nat (length acc) - i) with (outl0 - Z.of_nat (length acc')) by lia.
        clearbody i acc'.
        destruct (Z.eq_dec (dr_rv r) 0) as [K0|K1].
        * (* [comment removed for export] *)
          rewrite K0, Z.eqb_refl. rewrite K0 in HI'.
          destruct HI' as (FR & HD & BUF & TMP & ENC & MB & TXTB & OUTB & TAB & MI & ST & MU & WM).
          hcb. pose proof (word_range sp) as SPR. unfold HEADMS.
          eapply evt_cut.
          { eapply rd_head_exit; [ | | | | | exact FR| exact HD| exact ST| |exact MI].
            1: lia. 1: unfold zlength in *; lia. 1: unfold zlength in *; lia.
            all: unfold B64F_below, B64CTX_SIZE in BLW; destruct RBc as (? & ? & ? & ? & ?); try lia.
            all: match goal with |- ?G => idtac "HX:" G end. all: fail. }
          cbv beta. intros ms3 (m3 & a0x & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HD3).
          apply evt_done. unfold EXITQ. cbn [br_rv br_out br_used].
          exists m3, 0, 0, (out0 + zlength acc'), (outl0 - zlength acc'), fl', nr', 0, 0, (dr_d r), jb', jt', jo', j16', j8'.
          eexists ra', t0', t1', t2', _, a0x, a1', a2', a3', a4', a5', a6', a7', _, _, _, _, s8', _, s10', s11', t3', t4', t5', t6'.
          split; [reflexivity|].
          split; [unfold zlength; destruct (Z.of_nat (length acc') =? 0); reflexivity|].
          split; [left; reflexivity|]. split; [left; lia|]. split; [lia|].
          split; [unfold zlength in *; lia|].
          split.
          { unfold chunk. rewrite length_firstn, length_skipn, LT. lia. }
          assert (FLR' : 0 <= fl' < 2^31).
          { mbnum MB. exact MBF. }
          split; [exact FLR'|].
          split; [exact FR3|]. split; [exact HD3|].
          (* [comment removed for export] *)
          assert (DJc : forall A n, A + n <= lo -> 0 <= n -> disjoint_from [(bv_unsigned sp + -192, bv_unsigned sp)] A n).
          { intros A n HA Hn. cbn. split; [lia| exact I]. }
          unfold B64F_below, B64CTX_SIZE, BIO_SIZE in BLW. unfold MEMBIO_below, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in MBW.
          split; [eapply rw_cells_transport; [exact BUF| exact MU3| exact WM3| apply DJc; cbn; lia]|].
          split; [eapply rw_cells_transport; [exact TMP| exact MU3| exact WM3| apply DJc; cbn; lia]|].
          split; [eapply ENCCTX_transport; [exact MU3| exact WM3| apply DJc; lia| exact ENC]|].
          split; [eapply MEMBIO_transport; [exact MU3| exact WM3| | | | | exact MB]; apply DJc; cbn; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; lia|].
          mbnum MB. pose proof TL as TL'; unfold zlength in TL'.
          split; [eapply bytes_at_transport; [exact TXTB| exact MU3|]; apply DJc; lia|].
          split; [eapply rw_cells_transport; [exact OUTB| exact MU3| exact WM3|]; cbn [cells_size csize Nat.add]; cbn; split; [| exact I];
                 unfold zlength in *; lia|].
          split; [exact (ECH_C8_blockA.B64TAB_of_mem_inv _ MI3)|].
          split; [exact MI3|]. split; [exact ST3|].
          split; [| exact (wmono_trans _ _ _ _ WM WM3)].
          eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU3].
          intros xa Hxa. unfold WL in Hxa. cbn [outside] in Hxa |- *. clear - Hxa LOS. lia.
        * (* [comment removed for export] *)
          assert (K1' : dr_rv r = 1) by lia. rewrite K1'. change (1 =? 0) with false. cbv iota.
          assert (USED' : (used + length chunk <= length txt)%nat).
          { unfold chunk. rewrite length_firstn, length_skipn, LT. lia. }
          replace (skipn 1024 (skipn used TXT)) with (skipn (used + length chunk) TXT).
          2:{ rewrite skipn_skipn. unfold chunk. rewrite length_firstn, length_skipn.
              destruct (Nat.le_gt_cases (length TXT - used) 1024) as [LE|GT].
              - rewrite Nat.min_r by lia. rewrite !skipn_all2 by lia. reflexivity.
              - rewrite Nat.min_l by lia. f_equal. lia. }
          eapply IH; [ | | | exact DMOD' | | exact HI']; [ | exact USED' | unfold zlength; lia | lia].
          unfold chunk. rewrite length_firstn, length_skipn, LT. clear - FUEL DATAc USED. lia.
  Qed.
End RD.
