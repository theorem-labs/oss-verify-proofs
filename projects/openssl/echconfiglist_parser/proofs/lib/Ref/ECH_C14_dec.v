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
     ECH_LibState ECH_LibFrame ECH_Rostr ECH_C1_stmt ECH_C3_stmt ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_C4 ECH_C5_stmt
     ECH_C6_stmt ECH_C7_stmt ECH_C9_stmt ECH_C10_stmt ECH_C13_stmt ECH_C13_ext ECH_C13_entry ECH_C13_store ECH_C14_stmt ECH_KitSeg ECH_LibMid F_time
     ECH_C14_bio2buf ECH_C14_ladder ECH_C14_ladloop ECH_C14_tail ECH_C14_b2b ECH_C14_fcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition DF_DEC : Z := 0x26c9f4.    (* [comment removed for export] *)
Definition DF_HDR : Z := 0x26ca7c.    (* [comment removed for export] *)
Definition DF_LOOP : Z := 0x26cae4.   (* [comment removed for export] *)
Definition DF_OK : Z := 0x26cec4.     (* [comment removed for export] *)
Definition DF_ADV : Z := 0x26cf68.    (* [comment removed for export] *)
Definition DF_DONE : Z := 0x26cf8c.   (* [comment removed for export] *)
Definition DF_TA : Z := 0x26cff0.     (* [comment removed for export] *)
Definition DF_TZ : Z := 0x26d028.     (* [comment removed for export] *)
Definition DF_TY : Z := 0x26d040.     (* [comment removed for export] *)
Definition DF_TX : Z := 0x26d078.     (* [comment removed for export] *)
Definition A_ECHS_FUNC_D1 : Z := 0x2e4c6.   (* [comment removed for export] *)
Definition A_ECHS_FUNC_DF : Z := 0x30e53.   (* [comment removed for export] *)
Definition R_ECH_DECODE_ERROR : Z := 426.   (* [comment removed for export] *)
Definition ECH_VERSION : Z := 0xfe0d.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition O_PUBLENP : Z := 8.    (* [comment removed for export] *)
Definition O_REASON : Z := 16.    (* [comment removed for export] *)
Definition O_PUBP : Z := 24.      (* [comment removed for export] *)
Definition O_CONT : Z := 32.      (* [comment removed for export] *)
Definition O_REM2 : Z := 40.      (* [comment removed for export] *)
Definition O_KEMLO : Z := 48.     (* [comment removed for export] *)
Definition O_VERS : Z := 56.      (* [comment removed for export] *)
Definition O_FILE : Z := 64.      (* [comment removed for export] *)
Definition O_REM1 : Z := 72.      (* [comment removed for export] *)
Definition O_ELEN : Z := 80.      (* [comment removed for export] *)
Definition O_F3 : Z := 2160.      (* [comment removed for export] *)
Definition O_SAVES : Z := 2248.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENTRY_BYTES (rem : Z) : Z := 20 * rem + 2048.   (* [comment removed for export] *)
Definition ENTRY_CNT (rem : Z) : Z := (2 * rem) / 5 + 16.  (* [comment removed for export] *)
Definition ENTRY_BIG (rem : Z) : Z := 2 + rem / 1024.      (* [comment removed for export] *)
Definition ENTRY_KEPT (elen : Z) : Z := 13 * elen + 512.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section K3.
  Context {HCEIL : HeapCeil}.

  Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> exists w : word, le8 w = bs.
  Proof.
    intros bs L. exists (le_bytes_to_word bs). unfold le8, word_to_le_bytes, le_bytes_to_word.
    rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
    change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by (cbn in B; clear - B B0; lia). rewrite <- L. apply Z_to_le_bytes_to_Z.
  Qed.

  (* [comment removed for export] *)
  Lemma CB_words : forall (n : nat) m A (j : list byte) post,
    rw_cells rsegs m A (CB (8 * n) j :: post) -> exists ws : list word, length ws = n /\ rw_cells rsegs m A (map C8 ws ++ post).
  Proof.
    induction n as [|n IH]; intros m A j post RC; pose proof RC as [[WF _] _]; cbn [cells_wf cell_wf csize length] in WF; destruct WF as [LJ WFP].
    - exists []. split; [reflexivity|]. cbn [map app]. destruct j; [| cbn in LJ; lia].
      eapply rw_cells_recut; [exact RC| exact WFP| reflexivity].
    - replace (8 * S n)%nat with (8 + 8 * n)%nat in RC by lia.
      pose proof (rw_cells_split_CB rsegs m A [] (8 + 8 * n) j post [8%nat; (8 * n)%nat] RC ltac:(cbn [sum_nat]; lia)) as RC2. cbn [mk_CB_cells app] in RC2.
      destruct (le8_of_bytes (firstn 8 j) ltac:(rewrite firstn_length; lia)) as [w Hw].
      pose proof (proj1 (rw_cells_app rsegs m A [CB 8 (firstn 8 j)] (CB (8 * n) (firstn (8 * n) (skipn 8 j)) :: post)) RC2) as [R1 R2].
      cbn [cells_size csize Nat.add] in R2.
      destruct (IH m _ _ post R2) as (ws & LW & RW).
      exists (w :: ws). split; [cbn [length]; lia|]. cbn [map app].
      apply (proj2 (rw_cells_app rsegs m A [C8 w] (map C8 ws ++ post))). split.
      + eapply rw_cells_recut; [exact R1| cbn [cells_wf]; split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite !app_nil_r, Hw; reflexivity].
      + cbn [cells_size csize Nat.add]. exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma dec_stack : forall M M', mid_step M M' ->
       DECEXTS_STACK M' + 2352 <= READCFG_STACK M /\ FCC_STACK M' + 2352 <= READCFG_STACK M /\ RAISE_STACK (mid_err M') + 2352 <= READCFG_STACK M
    /\ SKPUSH_STACK + 2352 <= READCFG_STACK M /\ ENTRYFREE_STACK + 2352 <= READCFG_STACK M /\ CZALLOC_STACK + 2352 <= READCFG_STACK M
    /\ CARRAY_STACK + 2352 <= READCFG_STACK M /\ CMEMDUP_STACK + 2352 <= READCFG_STACK M /\ PKMEMDUP_STACK + 2352 <= READCFG_STACK M
    /\ PKSTRNDUP_STACK + 2352 <= READCFG_STACK M /\ SKNEW_STACK + 2352 <= READCFG_STACK M /\ TIME_STACK + 2352 <= READCFG_STACK M
    /\ BIOFREEALL_STACK + 2352 <= READCFG_STACK M /\ CFREE_STACK + 2352 <= READCFG_STACK M /\ 11136 <= READCFG_STACK M.
  Proof.
    intros [f c e E v] [f' c' e' E' v'] (_ & _ & SE & _). cbn [mid_ctx mid_err] in SE. unfold READCFG_STACK, DECEXTS_STACK, FCC_STACK, mid_stack. cbn [mid_ctx mid_err].
    destruct e' as [|k'].
    - destruct e as [|k]; [| discriminate (SE k eq_refl)]. destruct c as [|x]; vm_compute; repeat split; discriminate.
    - destruct e as [|k]; destruct c as [|x]; vm_compute; repeat split; discriminate.
  Qed.
End K3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section OBJX.
  Context {HCEIL : HeapCeil}.
  Lemma ENTRYs_frameX : forall L0 SP X m m' ps es,
    Forall2 (fun p E => ENTRYobj L0 m p E) ps es -> xpres L0 SP X m m' ->
    (forall b, In b (concat (map (fun px => blocks_ENTRY (fst px) (snd px)) (combine ps es))) -> avoids X (blk_addr b) (blk_size b)) ->
    Forall2 (fun p E => ENTRYobj L0 m' p E) ps es.
  Proof.
    intros L0 SP X m m' ps es F2. induction F2 as [|p E ps' es' HE F IH]; intros XP K; [constructor|].
    cbn [concat map combine fst snd] in K. constructor.
    - eapply ENTRYobj_frameX; [exact HE| exact XP|]. intros b Hb. apply K. apply in_or_app. left. exact Hb.
    - apply IH; [exact XP|]. intros b Hb. apply K. apply in_or_app. right. exact Hb.
  Qed.
  Lemma STOREobj_frameX : forall L0 SP X m m' a S', STOREobj L0 m a S' -> xpres L0 SP X m m' ->
    (forall b, In b (blocks_STORE a S') -> avoids X (blk_addr b) (blk_size b)) -> STOREobj L0 m' a S'.
  Proof.
    intros L0 SP X m m' a S' (HC & HIN & ENS) XP K. rewrite blocks_STORE_eq in K.
    pose proof (K _ ltac:(left; reflexivity)) as A0. cbn [blk_addr blk_size fst snd] in A0.
    unfold STOREobj. split.
    { eapply xpres_rw_cells'; [exact XP| exact HC| |].
      - right; right. exists (es_id S', a, STORE_SIZE). split; [exact HIN|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold STORE_SIZE. lia.
      - cbn [cells_size csize Nat.add]. eapply Forall_impl; [| exact A0]. cbn beta. intros [u v] Q. cbn in Q |- *. unfold STORE_SIZE in Q. lia. }
    split; [exact HIN|].
    revert ENS K. unfold ENTRIES, blocks_ENTRIES. destruct (es_entries_o S') as [[K0 es]|]; intros ENS K; [| exact ENS].
    destruct ENS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply SKobj_frameX; [exact SO| intros b Hb; eapply SKobj_owned; [exact SO| exact Hb]| exact XP|].
      intros b Hb. apply K. right. apply in_or_app. left. exact Hb.
    - split; [exact LEN|]. eapply ENTRYs_frameX; [exact F2| exact XP|]. intros b Hb. apply K. right. apply in_or_app. right. exact Hb.
  Qed.
  Lemma STOREobj_LB_mono : forall LB LB' m a S', STOREobj LB m a S' -> (forall b, In b LB -> In b LB') -> STOREobj LB' m a S'.
  Proof.
    intros LB LB' m a S' (HC & HIN & ENS) SUB. split; [exact HC|]. split; [apply SUB; exact HIN|].
    revert ENS. unfold ENTRIES. destruct (es_entries_o S') as [[K es]|]; intros ENS; [| exact ENS].
    destruct ENS as (X1 & SO & LEN & F2). split; [exact X1|]. split; [eapply SKobj_LB_mono; eauto|]. split; [exact LEN|].
    clear - F2 SUB. induction F2 as [|q E qs Es HE HF IH]; constructor; [eapply ENTRYobj_LB_mono; eauto| exact IH].
  Qed.
End OBJX.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
  Local Notation L0c := (L0 LB M).
  Local Notation SPc := (SP' sp).
  Local Notation RBPc := (RBP sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation XFc := (XF M st mb R).

  (* [comment removed for export] *)
  Variables (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (jt : list byte) (bt : Z) (TB : list block).
  Variable BT : mem -> Prop.
  Hypotheses (NAR : 1 <= mb_len R <= nA /\ nA <= 512 * 3)                 (* [comment removed for export] *)
             (NBR : 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN)
             (MST : mb_static R R') (POS : mb_pos R' = mb_len R)
             (BTR : 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 /\ lb_big TB <= 1)
             (BT_frame : forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
                 BT m1 -> xpres L SP X m1 m2 -> (forall b, In b TB -> In b L) -> hceil <= SP ->
                 Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) TB) X ->
                 BT m2).

  (* [comment removed for export] *)
  Definition dframe (w0 w1 w3 w4 w5 w6 w9 w10 : word) : list cell :=
    [C8 w0; C8 w1; C8 (wz R_INTERNAL_ERROR); C8 w3; C8 w4; C8 w5; C8 w6; C8 (wz ECH_VERSION); C8 (wz A_ECHS_FILE_RP); C8 w9; C8 w10;
     C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 0)].
  (* [comment removed for export] *)
  Definition drest (Lx NB LE : list block) : list block := Lx ++ NB ++ TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB.

  (* [comment removed for export] *)
  Definition dnb (NB : list block) : Prop := Z.of_nat (length NB) <= DECODE_CNT /\ lb_bytes NB <= DECODE_BYTES /\ lb_big NB <= DECODE_BIG.

  (* [comment removed for export] *)
  Definition dwkG (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (fr : list cell) (j3 : list byte)
      (m' : mem) (mo' : Model) (s' : PState) : Prop :=
       hs_RHEAP H s' (mid_errblocks M' ++ drest Lx NB LE) m' /\ hs_KREL H s' mo' /\ hs_MPRES H mo mo'
    (* [comment removed for export] *)
    /\ LIBMID (LE ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LE /\ mid_ctx M' = mid_ctx M
    /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES /\ lb_big (mid_errblocks M') = 0
    /\ Z.of_nat (length LE) + errph_cnt (mid_err M') <= errph_cnt (mid_err M)
    /\ lb_bytes LE + errph_bytes (mid_err M') <= errph_bytes (mid_err M) /\ lb_big LE + errph_big (mid_err M') <= errph_big (mid_err M)
    (* [comment removed for export] *)
    /\ STOREobj (NB ++ LE ++ LB) m' st S' /\ es_id S' = es_id S /\ Permutation (blocks_STORE st S') ((es_id S, st, STORE_SIZE) :: NB)
    /\ List.NoDup (map blk_id (blocks_STORE st S'))
    /\ (forall K es, es_entries_o S' = Some (K, es) -> sk_comp K = 0 /\ sk_cap K <= 2 * Z.of_nat (length (sk_elems K)) + 4)
    (* [comment removed for export] *)
    /\ MEMBIO LB m' mb R' /\ bytes_at rsegs m' (mb_buf R) ds /\ bytes_at rsegs m' Bb bs /\ BT m'
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' SPc fr /\ rw_cells rsegs m' RBPc [CB 2048 jt]
    /\ rw_cells rsegs m' (SPc + O_F3) [CB 88 j3] /\ rw_cells rsegs m' (SPc + O_SAVES) SAVESc
    (* [comment removed for export] *)
    /\ (exists errv', rw_cells rsegs m' RERRNO [C4 errv']) /\ mem_inv rsegs m' /\ stk rsegs m' lo SPc /\ hs_rauxv_ok H m' B
    /\ xpres LB (bv_unsigned sp) XFc m m'
    /\ dnb NB.

  (* [comment removed for export] *)
  Definition dwk (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w4 w5 w6 w9 w10 : word) (j3 : list byte)
      (m' : mem) (mo' : Model) (s' : PState) : Prop :=
       hs_RHEAP H s' (mid_errblocks M' ++ drest Lx NB LE) m' /\ hs_KREL H s' mo' /\ hs_MPRES H mo mo'
    (* [comment removed for export] *)
    /\ LIBMID (LE ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LE /\ mid_ctx M' = mid_ctx M
    /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES /\ lb_big (mid_errblocks M') = 0
    /\ Z.of_nat (length LE) + errph_cnt (mid_err M') <= errph_cnt (mid_err M)
    /\ lb_bytes LE + errph_bytes (mid_err M') <= errph_bytes (mid_err M) /\ lb_big LE + errph_big (mid_err M') <= errph_big (mid_err M)
    (* [comment removed for export] *)
    /\ STOREobj (NB ++ LE ++ LB) m' st S' /\ es_id S' = es_id S /\ Permutation (blocks_STORE st S') ((es_id S, st, STORE_SIZE) :: NB)
    /\ List.NoDup (map blk_id (blocks_STORE st S'))
    /\ (forall K es, es_entries_o S' = Some (K, es) -> sk_comp K = 0 /\ sk_cap K <= 2 * Z.of_nat (length (sk_elems K)) + 4)
    (* [comment removed for export] *)
    /\ MEMBIO LB m' mb R' /\ bytes_at rsegs m' (mb_buf R) ds /\ bytes_at rsegs m' Bb bs /\ BT m'
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' SPc (dframe w0 w1 w3 w4 w5 w6 w9 w10) /\ rw_cells rsegs m' RBPc [CB 2048 jt]
    /\ rw_cells rsegs m' (SPc + O_F3) [CB 88 j3] /\ rw_cells rsegs m' (SPc + O_SAVES) SAVESc
    (* [comment removed for export] *)
    /\ (exists errv', rw_cells rsegs m' RERRNO [C4 errv']) /\ mem_inv rsegs m' /\ stk rsegs m' lo SPc /\ hs_rauxv_ok H m' B
    /\ xpres LB (bv_unsigned sp) XFc m m'
    /\ dnb NB.
  Lemma dwk_G : forall Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s',
    dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' = dwkG Lx NB S' M' LE (dframe w0 w1 w3 w4 w5 w6 w9 w10) j3 m' mo' s'.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition dbud (Lr : list block) (M' : libmid) (hb hc hg : Z) : Prop :=
       lb_bytes Lr + errph_bytes (mid_err M') + ERRSTR_BYTES + hb <= hs_LIVE_MAX H
    /\ Z.of_nat (length Lr) + errph_cnt (mid_err M') + ERRSTR_CNT + hc <= hs_LIVE_CNT_MAX H
    /\ lb_big Lr + errph_big (mid_err M') + hg <= hs_LIVE_BIG_MAX H.

  (* [comment removed for export] *)
  Definition dK_tailA : Prop :=
    forall (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w4 w5 w6 w9 w10 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (ee line : Z) (E : entrep)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s10w u3 u4 u5 u6 : word),
      dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' ->
      ENTRYobj (drest Lx NB LE) m' ee E -> Permutation (blocks_ENTRY ee E) Lx -> 0 <= line < 2^31 ->
      dbud (drest Lx NB LE) M' ERRDEBUG_BYTES 2 0 ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w (Z_to_bv 64 ee) s8w s9w s10w (Z_to_bv 64 line) u3 u4 u5 u6)
                             F (Z_to_bv 64 DF_TA) fc None m' (seg_rom rsegs)) mo').

  (* [comment removed for export] *)
  Definition dK_tailZ : Prop :=
    forall (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w4 w5 w6 w9 w10 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (ee : Z) (E : entrep)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s10w s11w u3 u4 u5 u6 : word),
      dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' ->
      ENTRYobj (drest Lx NB LE) m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
      dbud (drest Lx NB LE) M' ERRDEBUG_BYTES 2 0 ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w (Z_to_bv 64 ee) s8w s9w s10w s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 DF_TZ) fc None m' (seg_rom rsegs)) mo').

  (* [comment removed for export] *)
  Definition dK_ok (cur rem : Z) (NB : list block) (S' : storerep) : Prop :=
    forall (NBe : list block) (M' : libmid) (LE : list block) (w0 w1 w3 w5 w6 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (ee elen : Z) (E : entrep) (rows : list (Z * Z * Z)) (ps : bptr) (sn : Z) (pn : bptr) (ns : list byte)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s8w s9w s11w u3 u4 u5 u6 : word),
      dwk NBe NB S' M' LE w0 w1 w3 (Z_to_bv 64 (cur + 4)) w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m' mo' s' ->
      19 <= elen -> 4 + elen <= rem ->                     (* [comment removed for export] *)
      ENTRYobj (drest NBe NB LE) m' ee E -> Permutation (blocks_ENTRY ee E) NBe -> en_loadtime E = 0 -> en_forretry E = 0 ->
      1 <= en_nsuites E < 2^31 -> en_suites_o E = Some (ps, sn) -> rw_cells rsegs m' (en_suites E) (suite_cells rows) ->
      zlength rows = en_nsuites E -> 6 * en_nsuites E <= sn -> Forall row_ok rows ->
      en_pname_o E = Some (pn, zlength ns + 1) -> bytes_at rsegs m' (en_pname E) (ns ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) ns -> 1 <= zlength ns <= 255 ->
      5 * Z.of_nat (length NBe) <= 2 * (elen + 4) -> lb_bytes NBe <= ENTRY_KEPT elen -> lb_big NBe <= elen / 600 ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w s5w s6w (Z_to_bv 64 ee) s8w s9w (Z_to_bv 64 cur) s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 DF_OK) fc None m' (seg_rom rsegs)) mo').

  (* [comment removed for export] *)
  Definition dK_skip (cur rem : Z) (NB : list block) (S' : storerep) : Prop :=
    forall (M' : libmid) (LE : list block) (w0 w1 w3 w4 w5 w6 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState) (elen : Z)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word),
      dwk [] NB S' M' LE w0 w1 w3 w4 w5 w6 (Z_to_bv 64 (rem - 4)) (Z_to_bv 64 elen) j3 m' mo' s' ->
      0 <= elen -> 4 + elen <= rem ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) s4w (Z_to_bv 64 (cur + 4)) s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 DF_ADV) fc None m' (seg_rom rsegs)) mo').

  (* [comment removed for export] *)
  Definition rp_entry_stmt : Prop :=
    forall (cur rem : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w0 w1 w3 w4 w5 w6 w9 w10 : word) (j3 : list byte)
           (m' : mem) (mo' : Model) (s' : PState)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5w s6w s7w s8w s9w s11w u3 u4 u5 u6 : word),
      dwk [] NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' ->
      Bb + 2 <= cur -> 1 <= rem -> cur + rem <= Bb + zlength bs ->
      dbud (drest [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) (ENTRY_BIG rem) ->
      dK_ok cur rem NB S' -> dK_skip cur rem NB S' -> dK_tailA -> dK_tailZ ->
      hs_SR H POSTc (mkCfg (MS (mkR rax (Z_to_bv 64 SPc) gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 bt) (Z_to_bv 64 Bb) (Z_to_bv 64 rem) s5w s6w s7w s8w s9w (Z_to_bv 64 cur) s11w u3 u4 u5 u6)
                             F (Z_to_bv 64 DF_LOOP) fc None m' (seg_rom rsegs)) mo').

  Local Ltac img_static := unfold RERRNO, A_malloc_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD, A_mem_inited; cbn; lia.
  Local Notation RCFACTS := (rc_facts H HX ra sp tp a0 a1 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).

  (* [comment removed for export] *)
  Lemma drest_app : forall Lx NB LE, drest Lx NB LE = Lx ++ drest [] NB LE.
  Proof. clear. intros. reflexivity. Qed.
  Lemma drest_sub : forall Lx NB LE,
       (forall b, In b LB -> In b (drest Lx NB LE)) /\ (forall b, In b (drest [] NB LE) -> In b (drest Lx NB LE))
    /\ (forall b, In b LE -> In b (drest Lx NB LE)) /\ (forall b, In b NB -> In b (drest Lx NB LE)) /\ (forall b, In b TB -> In b (drest Lx NB LE))
    /\ In (pbin, Bb, nB) (drest Lx NB LE) /\ In (p, A, nA) (drest Lx NB LE) /\ (forall b, In b Lx -> In b (drest Lx NB LE))
    /\ (forall b, In b (NB ++ LE ++ LB) -> In b (drest [] NB LE)) /\ (forall b, In b (LE ++ LIB) -> In b (drest [] NB LE)).
  Proof using SUBL.
    clear - SUBL. intros Lx NB LE. unfold drest.
    repeat split; try (intros b0 Hb0; pose proof (SUBL b0) as SB0);
      rewrite ?in_app_iff in *; cbn [In] in *; rewrite ?in_app_iff in *; cbn [In] in *; tauto.
  Qed.

  Lemma dwkG_heap_facts : forall Lx NB S' M' LE fr j3 m' mo' s',
    dwkG Lx NB S' M' LE fr j3 m' mo' s' ->
       (forall b, In b (mid_errblocks M' ++ drest Lx NB LE) -> blk_addr b + blk_size b <= hceil)
    /\ List.NoDup (map blk_id (mid_errblocks M' ++ drest Lx NB LE))
    /\ (forall b b', In b (mid_errblocks M' ++ drest Lx NB LE) -> In b' (mid_errblocks M' ++ drest Lx NB LE) -> blk_id b <> blk_id b' ->
           blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b)
    /\ (forall b, In b (mid_errblocks M' ++ drest Lx NB LE) -> rblock_range (blk_addr b) (blk_size b))
    /\ idsdisj Lx (drest [] NB LE) /\ idsdisj (mid_errblocks M') (drest Lx NB LE).
  Proof using HH.
    intros until s'. intros DW. pose proof DW as (HP' & _).
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP') as ND.
    split; [exact (HH_blocks_below H HH _ _ _ HP')|]. split; [exact ND|].
    split; [intros b b' Hb Hb' NE; exact (HH_RHEAP_blocks_disjoint H HH _ _ _ b b' HP' Hb Hb' NE)|].
    split; [intros b Hb; exact (HH_RHEAP_block_range H HH _ _ _ _ HP' Hb)|].
    destruct (nd_app _ _ ND) as [D1 ND1]. rewrite drest_app in ND1. destruct (nd_app _ _ ND1) as [D2 _]. split; [exact D2| exact D1].
  Qed.

  Lemma dwk_heap_facts : forall Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s',
    dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' ->
       (forall b, In b (mid_errblocks M' ++ drest Lx NB LE) -> blk_addr b + blk_size b <= hceil)
    /\ List.NoDup (map blk_id (mid_errblocks M' ++ drest Lx NB LE))
    /\ (forall b b', In b (mid_errblocks M' ++ drest Lx NB LE) -> In b' (mid_errblocks M' ++ drest Lx NB LE) -> blk_id b <> blk_id b' ->
           blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b)
    /\ (forall b, In b (mid_errblocks M' ++ drest Lx NB LE) -> rblock_range (blk_addr b) (blk_size b))
    /\ idsdisj Lx (drest [] NB LE) /\ idsdisj (mid_errblocks M') (drest Lx NB LE).
  Proof using HH.
    intros until s'. intros DW. exact (dwkG_heap_facts _ _ _ _ _ _ _ _ _ _ DW).
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_of_munch_drest : forall Lx NB LE M' s' m1 m2 W,
    hs_RHEAP H s' (mid_errblocks M' ++ drest Lx NB LE) m1 -> munch W m1 m2 -> wmono rsegs m1 m2 ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    xpres (drest [] NB LE) (bv_unsigned sp) [] m1 m2.
  Proof using HH CEIL LO ST SUBL.
    intros Lx NB LE M' s' m1 m2 W HP1 MU WM FW. hcb. pose proof (readcfg_stack_lo M) as STK0.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP1) as ND. destruct (nd_app _ _ ND) as [_ ND1]. rewrite drest_app in ND1. destruct (nd_app _ _ ND1) as [D2 _].
    pose proof (HH_blocks_below H HH _ _ _ HP1) as HB.
    eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros a Ha [HC _].
    clear MU WM. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K.
    split; [| apply IH; eapply Forall_inv_tail; exact FW].
    destruct K as [[K1 K2]|(b & Hb & K1 & K2)].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [clear - HC K2; lia| clear - HC K1 CEIL HCEILB; lia|].
      pose proof (HB b ltac:(apply in_or_app; right; apply (proj1 (proj2 (drest_sub Lx NB LE))); exact Hb)) as E. clear - E Hr K1 CEIL. lia.
    - pose proof (client_outside_block H HH _ _ _ b (drest [] NB LE) (bv_unsigned sp) a HP1
                    ltac:(apply in_or_app; right; rewrite drest_app; apply in_or_app; left; exact Hb)
                    ltac:(intros b' Hb'; apply in_or_app; right; apply (proj1 (proj2 (drest_sub Lx NB LE))); exact Hb')
                    ltac:(intros c c' Hc Hc'; destruct Hc as [<-|[]]; exact (D2 _ _ Hb Hc'))
                    ltac:(clear - CEIL LO STK0; lia) HC) as O.
      clear - O K1 K2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mb_blocks_LB' : forall b, In b (blocks_MEMBIO mb R') -> In b LB.
  Proof using MBO MST.
    intros b Hb. rewrite (mb_static_blocks mb R R' MST) in Hb.
    destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma dwkG_w : forall Lx NB S' M' LE fr j3 m1 mo1 s1' m2 W (fr' : list cell) (j3' : list byte),
    dwkG Lx NB S' M' LE fr j3 m1 mo1 s1' ->
    munch W m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= SPc) \/ (SPc <= fst iv /\ snd iv <= SPc + 112) \/ (SPc + O_F3 <= fst iv /\ snd iv <= SPc + O_SAVES)
                              \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    rw_cells rsegs m2 SPc (fr') -> rw_cells rsegs m2 (SPc + O_F3) [CB 88 j3'] ->
    dwkG Lx NB S' M' LE fr' j3' m2 mo1 s1'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame.
    intros until j3'. intros DW MU WM MI2 ST2 FWW FR0' FR3'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & [errv1 ERR1] & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (dwkG_heap_facts _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (drest_sub Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (drest_sub [] NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    hcb. pose proof (word_range sp) as SPR. pose proof DSL as DSL1. unfold zlength in DSL1.
    assert (FW' : Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W).
    { eapply Forall_impl; [| exact FWW]. cbn beta. intros iv [K|[K|[K|K]]]; [left| left| left| right; exact K]; unfold SP', O_F3, O_SAVES in *; clear - K LO STK0; lia. }
    pose proof (xpres_of_munch_drest Lx NB LE M' s1' m1 m2 W HP1 MU WM FW') as XP.
    assert (DJ : forall a n, a + n <= hceil -> (forall b, In b Lx -> a + n <= blk_addr b \/ blk_addr b + blk_size b <= a) -> disjoint_from W a n).
    { intros a n Hh Hb. clear - FWW Hh Hb CEIL LO STK0. unfold SP', O_F3, O_SAVES in *. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FWW) as K. cbn in K.
      split; [| apply IH; eapply Forall_inv_tail; exact FWW].
      destruct K as [K|[K|[K|(b & Hb0 & K1 & K2)]]]; [lia| lia| lia| pose proof (Hb b Hb0); lia]. }
    assert (DJS : forall a n, (SPc + 112 <= a /\ a + n <= SPc + O_F3) \/ SPc + O_SAVES <= a -> disjoint_from W a n).
    { intros a n Ha. assert (HBL : forall b, In b Lx -> blk_addr b + blk_size b <= hceil) by (intros b Hb; apply HB; apply in_or_app; right; apply SLX; exact Hb).
      clear - FWW Ha HBL CEIL LO STK0. unfold SP', O_F3, O_SAVES in *. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FWW) as K. cbn in K.
      split; [| apply IH; eapply Forall_inv_tail; exact FWW].
      destruct K as [K|[K|[K|(b & Hb0 & K1 & K2)]]]; [lia| lia| lia| pose proof (HBL b Hb0); lia]. }
    assert (OFFX : forall b a n, In b Lx -> IMG_LO <= a -> a + n <= IMG_HI -> a + n <= blk_addr b \/ blk_addr b + blk_size b <= a).
    { intros b a n Hb H1 H2. pose proof (BRS b ltac:(apply in_or_app; right; apply SLX; exact Hb)) as (_ & _ & _ & _ & O). unfold IMG_LO, IMG_HI in *. clear - O H1 H2. lia. }
    unfold dwkG. repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU| exact WM|]. eapply Forall_impl; [| exact FWW]. cbn beta.
      intros iv [K|[K|[K|(b & Hb & K1 & K2)]]]; [left| left| left| right; right; exists b; split; [apply in_or_app; right; apply SLX; exact Hb| split; assumption]];
        unfold SP', O_F3 in *; clear - K CEIL LO STK0; lia.
    - eapply (LIBMID_xpres0 (LE ++ LIB) (drest [] NB LE) (bv_unsigned sp)); [exact LM1| exact XP| exact SLL0].
    - eapply (STOREobj_frame_law (NB ++ LE ++ LB) (NB ++ LE ++ LB) m1 m2 st S' (bv_unsigned sp)); [exact SO1| intros b Hb; exact (STOREobj_owned_law _ _ _ _ SO1 b Hb)| |].
      + eapply xpres_weaken; [exact XP| clear; lia| exact S3| intros q Hq; exact Hq].
      + intros b Hb. pose proof (HB b ltac:(apply in_or_app; right; apply S0; apply S3; exact (STOREobj_owned_law _ _ _ _ SO1 b Hb))). clear - H0 CEIL LO STK0. lia.
    - eapply (MEMBIO_frame0 LB LB (bv_unsigned sp)); [exact MBO1| exact mb_blocks_LB'| eapply xpres_weaken; [exact XP| clear; lia| exact SLB0| intros q Hq; exact Hq]].
    - destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN _]].
      eapply xpres_bytes_at'; [exact XP| exact DSm1| right; right; exists (pD, mb_buf R, mb_len R); split; [apply SLB0; exact PIN| cbn; rewrite DSL1; clear; lia]| apply Forall_nil].
    - eapply xpres_bytes_at'; [exact XP| exact DSb1| right; right; exists (pbin, Bb, nB); split; [exact IB0| cbn; unfold zlength in NBR; clear - NBR; lia]| apply Forall_nil].
    - eapply (BT_frame (drest [] NB LE) (bv_unsigned sp) []); [exact BT1| exact XP| exact STB0| clear - CEIL LO STK0; lia| apply Forall_nil].
    - eapply rw_cells_transport; [exact FR2| exact MU| exact WM| apply DJS; left; unfold RBP, SP', O_F3; cbn; clear; lia].
    - eapply rw_cells_transport; [exact FR4| exact MU| exact WM| apply DJS; right; clear; lia].
    - exists errv1. eapply rw_cells_transport; [exact ERR1| exact MU| exact WM| apply DJ; [clear - HCEILB; img_static| intros b Hb; apply (OFFX b); [exact Hb| unfold IMG_LO; img_static| unfold IMG_HI; img_static]]].
    - eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU| exact WM|]. eapply Forall_impl; [| exact FWW]. cbn beta.
      intros iv [K|[K|[K|(b & Hb & K1 & K2)]]]; unfold RAUXV_CELL, SP', O_F3, O_SAVES in *;
        [clear - K CEIL HCEILB SPB LO STK0; lia| clear - K CEIL HCEILB SPB LO STK0; lia| clear - K CEIL HCEILB SPB LO STK0; lia|].
      pose proof (HB b ltac:(apply in_or_app; right; apply SLX; exact Hb)) as E. pose proof (OFFX b RAUXV_CELL 8 Hb ltac:(unfold IMG_LO, RAUXV_CELL; clear; lia) ltac:(unfold IMG_HI, RAUXV_CELL; clear; lia)) as O.
      unfold RAUXV_CELL in O. clear - K1 K2 E O CEIL HCEILB SPB LO STK0. lia.
    - eapply xpres_trans; [exact XA1|]. eapply xpres_weaken; [exact XP| clear; lia| exact SLB0| intros q Hq; destruct Hq].
  Qed.

  Lemma dwk_w : forall Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' m2 W (v0 v1 v3 v4 v5 v6 v9 v10 : word) (j3' : list byte),
    dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' ->
    munch W m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= SPc) \/ (SPc <= fst iv /\ snd iv <= SPc + 112) \/ (SPc + O_F3 <= fst iv /\ snd iv <= SPc + O_SAVES)
                              \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    rw_cells rsegs m2 SPc (dframe v0 v1 v3 v4 v5 v6 v9 v10) -> rw_cells rsegs m2 (SPc + O_F3) [CB 88 j3'] ->
    dwk Lx NB S' M' LE v0 v1 v3 v4 v5 v6 v9 v10 j3' m2 mo1 s1'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame.
    intros until j3'. intros DW MU WM MI2 ST2 FWW FR0' FR3'.
    apply (dwkG_w Lx NB S' M' LE (dframe w0 w1 w3 w4 w5 w6 w9 w10) j3 m1 mo1 s1' m2 W (dframe v0 v1 v3 v4 v5 v6 v9 v10) j3'); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma dwkG_x : forall Lx Lx' NB S' M' LE fr j3 m1 mo1 s1' m2 mo2 s2',
    dwkG Lx NB S' M' LE fr j3 m1 mo1 s1' ->
    xpres (drest [] NB LE) SPc [] m1 m2 ->
    hs_RHEAP H s2' (mid_errblocks M' ++ drest Lx' NB LE) m2 -> hs_KREL H s2' mo2 -> hs_MPRES H mo mo2 ->
    (exists errv', rw_cells rsegs m2 RERRNO [C4 errv']) -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    dwkG Lx' NB S' M' LE fr j3 m2 mo2 s2'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame.
    intros until s2'. intros DW XP HP2 KREL2 MP2 ERR2 MI2 ST2 AUX2.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & _ & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (dwkG_heap_facts _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (drest_sub Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (drest_sub [] NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    hcb. pose proof (word_range sp) as SPR. pose proof DSL as DSL1. unfold zlength in DSL1.
    unfold dwkG. repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply (LIBMID_xpres0 (LE ++ LIB) (drest [] NB LE) SPc); [exact LM1| exact XP| exact SLL0].
    - eapply (STOREobj_frame_law (NB ++ LE ++ LB) (NB ++ LE ++ LB) m1 m2 st S' SPc); [exact SO1| intros b Hb; exact (STOREobj_owned_law _ _ _ _ SO1 b Hb)| |].
      + eapply xpres_weaken; [exact XP| clear; lia| exact S30| intros q Hq; exact Hq].
      + intros b Hb. pose proof (HB b ltac:(apply in_or_app; right; apply S0; apply S30; exact (STOREobj_owned_law _ _ _ _ SO1 b Hb))). unfold SP'. clear - H0 CEIL LO STK0. lia.
    - eapply (MEMBIO_frame0 LB LB SPc); [exact MBO1| exact mb_blocks_LB'| eapply xpres_weaken; [exact XP| clear; lia| exact SLB0| intros q Hq; exact Hq]].
    - destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN _]].
      eapply xpres_bytes_at'; [exact XP| exact DSm1| right; right; exists (pD, mb_buf R, mb_len R); split; [apply SLB0; exact PIN| cbn; rewrite DSL1; clear; lia]| apply Forall_nil].
    - eapply xpres_bytes_at'; [exact XP| exact DSb1| right; right; exists (pbin, Bb, nB); split; [exact IB0| cbn; unfold zlength in NBR; clear - NBR; lia]| apply Forall_nil].
    - eapply (BT_frame (drest [] NB LE) SPc []); [exact BT1| exact XP| exact STB0| unfold SP'; clear - CEIL LO STK0; lia| apply Forall_nil].
    - eapply xpres_rw_cells'; [exact XP| exact FR0| left; clear; lia| apply Forall_nil].
    - eapply xpres_rw_cells'; [exact XP| exact FR2| left; unfold RBP, SP'; clear; lia| apply Forall_nil].
    - eapply xpres_rw_cells'; [exact XP| exact FR3| left; unfold O_F3; clear; lia| apply Forall_nil].
    - eapply xpres_rw_cells'; [exact XP| exact FR4| left; unfold O_SAVES; clear; lia| apply Forall_nil].
    - eapply xpres_trans; [exact XA1|]. eapply xpres_weaken; [exact XP| unfold SP'; clear; lia| exact SLB0| intros q Hq; destruct Hq].
  Qed.

  Lemma dwk_x : forall Lx Lx' NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' m2 mo2 s2',
    dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' ->
    xpres (drest [] NB LE) SPc [] m1 m2 ->
    hs_RHEAP H s2' (mid_errblocks M' ++ drest Lx' NB LE) m2 -> hs_KREL H s2' mo2 -> hs_MPRES H mo mo2 ->
    (exists errv', rw_cells rsegs m2 RERRNO [C4 errv']) -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    dwk Lx' NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m2 mo2 s2'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame.
    intros until s2'. intros DW XP HP2 KREL2 MP2 ERR2 MI2 ST2 AUX2.
    apply (dwkG_x Lx Lx' NB S' M' LE (dframe w0 w1 w3 w4 w5 w6 w9 w10) j3 m1 mo1 s1' m2 mo2 s2'); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma drest_ids : forall E' Lx NB LE, List.NoDup (map blk_id (E' ++ drest Lx NB LE)) ->
       idsdisj E' (drest Lx NB LE) /\ idsdisj Lx (drest [] NB LE) /\ idsdisj NB (TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)
    /\ idsdisj TB ((pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) /\ idsdisj [(pbin, Bb, nB)] ((p, A, nA) :: LE ++ LB) /\ idsdisj [(p, A, nA)] (LE ++ LB) /\ idsdisj LE LB.
  Proof.
    clear. intros E' Lx NB LE ND. unfold drest in ND.
    destruct (nd_app _ _ ND) as [D0 ND0]. destruct (nd_app _ _ ND0) as [D1 ND1]. destruct (nd_app _ _ ND1) as [D2 ND2]. destruct (nd_app _ _ ND2) as [D3 ND3].
    destruct (nd_app [(pbin, Bb, nB)] _ ND3) as [D4 ND4]. destruct (nd_app [(p, A, nA)] _ ND4) as [D5 ND5]. destruct (nd_app _ _ ND5) as [D6 _].
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma dwkG_es : forall Lx NB S' M' LE fr j3 m' mo' s' c,
    dwkG Lx NB S' M' LE fr j3 m' mo' s' -> mid_err M' = ErrReady c -> In (ec_es c) (LE ++ LIB) /\ blk_size (ec_es c) = ERRST_SIZE.
  Proof using CTX.
    intros until c. intros DW EQ. pose proof DW as (_ & _ & _ & LM1 & _ & _ & CTX1 & _).
    destruct LM1 as (_ & _ & _ & EPm & _). rewrite CTX1, CTX, EQ in EPm. cbn [ERRPH_mid ERRPH] in EPm. destruct EPm as [_ CH].
    pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). split; [exact I5| exact Z5].
  Qed.

  Lemma dwk_es : forall Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' c,
    dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m' mo' s' -> mid_err M' = ErrReady c -> In (ec_es c) (LE ++ LIB) /\ blk_size (ec_es c) = ERRST_SIZE.
  Proof using CTX.
    intros until c. intros DW EQ. exact (dwkG_es _ _ _ _ _ _ _ _ _ _ c DW EQ).
  Qed.

  (* [comment removed for export] *)
  Lemma dwkG_libX : forall Lx Lx' NB S' M' M'' LE LEn fr j3 m1 mo1 s1' m2 mo2 s2' X (fr' : list cell) j3',
    dwkG Lx NB S' M' LE fr j3 m1 mo1 s1' ->
    LIBMID (LEn ++ LE ++ LIB) m2 M'' -> mid_step M' M'' -> mid_newlib_ok M' M'' LEn -> mid_ctx M'' = mid_ctx M' ->
    Z.of_nat (length (mid_errblocks M'')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M'') <= ERRSTR_BYTES -> lb_big (mid_errblocks M'') = 0 ->
    xpres (drest Lx NB LE) SPc (X ++ ERR_X ++ errph_foot (mid_err M')) m1 m2 ->
    Forall (fun iv : Z * Z => (SPc <= fst iv /\ snd iv <= SPc + 112) \/ (SPc + O_F3 <= fst iv /\ snd iv <= SPc + O_SAVES)
                              \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) \/ iv = (A_vdso_func, A_vdso_func + 8)) X ->
    hs_RHEAP H s2' (mid_errblocks M'' ++ drest Lx' NB (LEn ++ LE)) m2 -> hs_KREL H s2' mo2 -> hs_MPRES H mo mo2 ->
    (exists errv', rw_cells rsegs m2 RERRNO [C4 errv']) -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    rw_cells rsegs m2 SPc (fr') -> rw_cells rsegs m2 (SPc + O_F3) [CB 88 j3'] ->
    dwkG Lx' NB S' M'' (LEn ++ LE) fr' j3' m2 mo2 s2'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame.
    intros until j3'. intros DW LM2 STP2 NEW2 CTX2 EC2 EB2 EG2 XP FX HP2 KREL2 MP2 ERR2 MI2 ST2 AUX2 FR0' FR3'.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP & NEW & CTX1 & EC & EB & EG & LC & LBY & LG & SO1 & SID & SPM & SND & SKI & MBO1 & DSm1 & DSb1 & BT1
                      & FR0 & FR2 & FR3 & FR4 & _ & MI1 & ST1 & AUX1 & XA1 & DNB1).
    destruct (dwkG_heap_facts _ _ _ _ _ _ _ _ _ _ DW) as (HB & ND & DISJ & BRS & D2 & D1).
    destruct (drest_ids _ _ _ _ ND) as (_ & _ & DNB & DTB & DBIN & DLBUF & DLE).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA).
    pose proof (drest_sub Lx NB LE) as (SLB & S0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (drest_sub [] NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    hcb. pose proof (word_range sp) as SPR. pose proof DSL as DSL1. unfold zlength in DSL1.
    (* [comment removed for export] *)
    assert (AV : forall b, In b (drest Lx NB LE) -> ~ In b Lx -> (forall l, In l (LE ++ LIB) -> blk_id l <> blk_id b) ->
                 avoids (X ++ ERR_X ++ errph_foot (mid_err M')) (blk_addr b) (blk_size b)).
    { intros b Hb NLX NLIB. pose proof (HB b ltac:(apply in_or_app; right; exact Hb)) as E. pose proof (BRS b ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & O).
      unfold avoids. apply Forall_app. split; [| apply Forall_app; split].
      - eapply Forall_impl; [| exact FX]. cbn beta. intros iv [K|[K|[(b' & Hb' & K1 & K2)| ->]]]; [unfold SP' in K; clear - K E CEIL LO STK0; lia| unfold SP', O_F3 in K; clear - K E CEIL LO STK0; lia| | cbn [fst snd]; unfold A_vdso_func; clear - O; lia].
        assert (NE : blk_id b' <> blk_id b).
        { intros EQ. apply NLX. rewrite <- (nodup_id_inj _ b' b ND ltac:(apply in_or_app; right; apply SLX; exact Hb') ltac:(apply in_or_app; right; exact Hb) EQ). exact Hb'. }
        pose proof (DISJ b' b ltac:(apply in_or_app; right; apply SLX; exact Hb') ltac:(apply in_or_app; right; exact Hb) NE). clear - H0 K1 K2. lia.
      - apply avoid_of_img; [apply img_ERR_X| unfold IMG_LO, IMG_HI; clear - O; lia].
      - destruct (mid_err M') as [|c] eqn:EQ; [apply Forall_nil|]. cbn [errph_foot]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        destruct (dwkG_es _ _ _ _ _ _ _ _ _ _ c DW EQ) as [I5 Z5].
        pose proof (DISJ (ec_es c) b ltac:(apply in_or_app; right; apply S0; apply SLL; exact I5) ltac:(apply in_or_app; right; exact Hb) (NLIB _ I5)) as D. rewrite Z5 in D. clear - D. lia. }
    (* [comment removed for export] *)
    pose proof SO as (_ & SINB & _).
    assert (NLX : forall b, In b (drest [] NB LE) -> ~ In b Lx) by (intros b Hb K; exact (D2 _ _ K Hb eq_refl)).
    assert (INR : forall l, In l (LE ++ LIB) -> In l (TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)).
    { intros l Hl. apply in_or_app; right; right; right. apply in_app_or in Hl. destruct Hl as [Hl|Hl]; apply in_or_app; [left; exact Hl| right; exact (SUBL _ Hl)]. }
    assert (NLIBst : forall b, In b (blocks_STORE st S') -> forall l, In l (LE ++ LIB) -> blk_id l <> blk_id b).
    { intros b Hb l Hl. pose proof (Permutation_in _ SPM Hb) as [<-|HbN].
      - apply in_app_or in Hl. destruct Hl as [Hl|Hl]; [exact (DLE _ _ Hl SINB)| exact (DJ6 _ _ Hl (or_introl eq_refl))].
      - intros EQ. exact (DNB _ _ HbN (INR _ Hl) (eq_sym EQ)). }
    assert (NLIBmb : forall b, In b (blocks_MEMBIO mb R') -> forall l, In l (LE ++ LIB) -> blk_id l <> blk_id b).
    { intros b Hb l Hl. apply in_app_or in Hl. destruct Hl as [Hl|Hl]; [exact (DLE _ _ Hl (mb_blocks_LB' _ Hb))|].
      rewrite (mb_static_blocks mb R R' MST) in Hb. exact (DJ6 _ _ Hl (or_intror Hb)). }
    assert (NLIBtb : forall b, In b TB -> forall l, In l (LE ++ LIB) -> blk_id l <> blk_id b).
    { intros b Hb l Hl EQ. apply in_app_or in Hl. destruct Hl as [Hl|Hl].
      - exact (DTB _ _ Hb ltac:(right; right; apply in_or_app; left; exact Hl) (eq_sym EQ)).
      - exact (DTB _ _ Hb ltac:(right; right; apply in_or_app; right; exact (SUBL _ Hl)) (eq_sym EQ)). }
    assert (NLIBbin : forall l, In l (LE ++ LIB) -> blk_id l <> blk_id (pbin, Bb, nB)).
    { intros l Hl EQ. apply in_app_or in Hl. destruct Hl as [Hl|Hl].
      - exact (DBIN _ _ (or_introl eq_refl) ltac:(right; apply in_or_app; left; exact Hl) (eq_sym EQ)).
      - exact (DBIN _ _ (or_introl eq_refl) ltac:(right; apply in_or_app; right; exact (SUBL _ Hl)) (eq_sym EQ)). }
    (* [comment removed for export] *)
    assert (AVS : forall a n, (SPc + 112 <= a /\ a + n <= SPc + O_F3) \/ SPc + O_SAVES <= a -> avoids (X ++ ERR_X ++ errph_foot (mid_err M')) a n).
    { intros a n Ha. unfold avoids. apply Forall_app. split; [| apply Forall_app; split].
      - eapply Forall_impl; [| exact FX]. cbn beta. intros iv [K|[K|[(b' & Hb' & K1 & K2)| ->]]]; [unfold SP', O_F3, O_SAVES in *; clear - K Ha; lia| unfold SP', O_F3, O_SAVES in *; clear - K Ha; lia| | cbn [fst snd]; unfold A_vdso_func, IMG_HI, SP', O_F3, O_SAVES in *; clear - Ha CEIL HCEILB LO STK0; lia].
        pose proof (HB b' ltac:(apply in_or_app; right; apply SLX; exact Hb')) as E. unfold SP', O_F3, O_SAVES in *. clear - E K1 K2 Ha CEIL LO STK0. lia.
      - apply avoid_of_img; [apply img_ERR_X| right; unfold IMG_HI, SP', O_F3, O_SAVES in *; clear - Ha CEIL HCEILB LO STK0; lia].
      - destruct (mid_err M') as [|c] eqn:EQ; [apply Forall_nil|]. cbn [errph_foot]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        destruct (dwkG_es _ _ _ _ _ _ _ _ _ _ c DW EQ) as [I5 Z5].
        pose proof (HB (ec_es c) ltac:(apply in_or_app; right; apply S0; apply SLL; exact I5)) as E. rewrite Z5 in E. right. unfold SP', O_F3, O_SAVES in *. clear - E Ha CEIL LO STK0. lia. }
    (* [comment removed for export] *)
    assert (LEN : Z.of_nat (length LEn) + errph_cnt (mid_err M'') <= errph_cnt (mid_err M')
               /\ lb_bytes LEn + errph_bytes (mid_err M'') <= errph_bytes (mid_err M') /\ lb_big LEn + errph_big (mid_err M'') <= errph_big (mid_err M')).
    { destruct NEW2 as (LA & LE2 & PM & CA & CE). rewrite CTX1, CTX in CA. destruct STP2 as (_ & _ & SE2 & _).
      subst LA. cbn [app] in PM.
      destruct (mid_err M') as [|c1] eqn:E1; destruct (mid_err M'') as [|c2] eqn:E2.
      - rewrite CE in PM. apply Permutation_sym in PM. apply Permutation_nil in PM. subst LEn. cbn. clear. lia.
      - cbn [errph_delta] in CE. destruct CE as (Q1 & Q2 & Q3 & _). rewrite (Permutation_length PM), (lb_bytes_perm _ _ PM), (lb_big_perm _ _ PM).
        cbn [errph_cnt errph_bytes errph_big]. unfold ERRINIT_BIG in *. clear - Q1 Q2 Q3. lia.
      - discriminate (SE2 c1 eq_refl).
      - rewrite CE in PM. apply Permutation_sym in PM. apply Permutation_nil in PM. subst LEn. cbn. clear. lia. }
    destruct LEN as (LEc & LEb & LEg).
    unfold dwkG. repeat match goal with |- _ /\ _ => split end; try assumption.
    - rewrite <- app_assoc. exact LM2.
    - exact (mid_step_trans' _ _ _ STP STP2).
    - exact (mid_newlib_ok_trans _ _ _ _ _ STP NEW STP2 NEW2).
    - rewrite CTX2. exact CTX1.
    - rewrite length_app, Nat2Z.inj_add. clear - LC LEc. lia.
    - rewrite lb_bytes_app. clear - LBY LEb. lia.
    - rewrite lb_big_app. clear - LG LEg. lia.
    - eapply STOREobj_LB_mono; [eapply (STOREobj_frameX (NB ++ LE ++ LB) SPc); [exact SO1| |]|].
      + eapply xpres_weaken; [exact XP| clear; lia| intros b Hb; apply S0; apply S3; exact Hb| intros q Hq; exact Hq].
      + intros b Hb. apply AV; [apply S0; apply S3; exact (STOREobj_owned_law _ _ _ _ SO1 b Hb)| apply NLX; apply S3; exact (STOREobj_owned_law _ _ _ _ SO1 b Hb)| exact (NLIBst b Hb)].
      + intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left; apply in_or_app; right; exact Hb| right; exact Hb].
    - eapply (MEMBIO_frameA LB LB SPc); [exact MBO1| exact mb_blocks_LB'| eapply xpres_weaken; [exact XP| clear; lia| exact SLB| intros q Hq; exact Hq]|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk.
      exact (proj1 (Forall_forall _ _) (AV bk (SLB _ (mb_blocks_LB' _ Hbk)) (NLX _ (proj1 (drest_sub [] NB LE) _ (mb_blocks_LB' _ Hbk))) (NLIBmb _ Hbk)) iv Hiv).
    - destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN PNL]].
      eapply xpres_bytes_at'; [exact XP| exact DSm1| right; right; exists (pD, mb_buf R, mb_len R); split; [apply SLB; exact PIN| cbn; rewrite DSL1; clear; lia]|].
      rewrite DSL1. pose proof (AV (pD, mb_buf R, mb_len R) (SLB _ PIN) (NLX _ (proj1 (drest_sub [] NB LE) _ PIN))) as K. cbn [blk_addr blk_size blk_id fst snd] in K. apply K.
      intros l Hl. apply in_app_or in Hl. destruct Hl as [Hl|Hl]; [exact (DLE _ _ Hl PIN)| exact (PNL _ Hl)].
    - pose proof (AV (pbin, Bb, nB) IB (NLX _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (drest_sub [] NB LE)))))))) NLIBbin) as K. cbn [blk_addr blk_size fst snd] in K.
      eapply xpres_bytes_at'; [exact XP| exact DSb1| right; right; exists (pbin, Bb, nB); split; [exact IB| cbn; unfold zlength in NBR; clear - NBR; lia]|].
      eapply avoids_sub; [exact K| clear; lia| unfold zlength in NBR; clear - NBR; lia].
    - eapply (BT_frame (drest Lx NB LE) SPc); [exact BT1| exact XP| exact STB| unfold SP'; clear - CEIL LO STK0; lia|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk.
      exact (proj1 (Forall_forall _ _) (AV bk (STB _ Hbk) (NLX _ (proj1 (proj2 (proj2 (proj2 (proj2 (drest_sub [] NB LE))))) _ Hbk)) (NLIBtb _ Hbk)) iv Hiv).
    - eapply xpres_rw_cells'; [exact XP| exact FR2| left; unfold RBP, SP'; clear; lia| apply AVS; left; unfold RBP, SP', O_F3; cbn [cells_size csize Nat.add]; clear; lia].
    - eapply xpres_rw_cells'; [exact XP| exact FR4| left; unfold O_SAVES; clear; lia| apply AVS; right; clear; lia].
    - (* [comment removed for export] *)
      eapply xpres_trans; [exact XA1|]. intros a Ha [HC HXF]. apply XP; [exact Ha|]. split.
      + destruct HC as [HC|[HC|(b & Hb & Hr)]]; [left; unfold SP'; clear - HC; lia| right; left; exact HC| right; right; exists b; split; [apply SLB; exact Hb| exact Hr]].
      + intros K. apply rin_ivs_app in K. destruct K as [K|K].
        * (* [comment removed for export] *)
          pose proof (proj1 (Forall_forall _ _) FX) as FXa.
          clear - K FXa HC HXF HB SLX SLB SLB0 DISJ NLX CEIL LO STK0 HCEILB D2 BRS. induction X as [|iv X IH]; [destruct K|]. cbn [rin_ivs] in K.
          destruct K as [K|K]; [| apply IH; [exact K| intros y Hy; apply FXa; right; exact Hy]].
          destruct (FXa iv (or_introl eq_refl)) as [W|[W|[(b' & Hb' & W1 & W2)|Wv]]].
          -- destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [unfold SP' in *; clear - K W HC; lia| unfold SP' in *; clear - K W HC CEIL LO STK0 HCEILB; lia|].
             pose proof (HB b ltac:(apply in_or_app; right; apply SLB; exact Hb)) as E. unfold SP' in *. clear - K W E Hr CEIL LO STK0. lia.
          -- destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [unfold SP', O_F3, O_SAVES in *; clear - K W HC LO STK0; lia| unfold SP', O_F3, O_SAVES in *; clear - K W HC CEIL LO STK0 HCEILB; lia|].
             pose proof (HB b ltac:(apply in_or_app; right; apply SLB; exact Hb)) as E. unfold SP', O_F3 in *. clear - K W E Hr CEIL LO STK0. lia.
          -- pose proof (HB b' ltac:(apply in_or_app; right; apply SLX; exact Hb')) as E. pose proof (BRS b' ltac:(apply in_or_app; right; apply SLX; exact Hb')) as (_ & _ & _ & _ & O).
             destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [clear - K W1 W2 E HC CEIL LO STK0; lia| clear - K W1 W2 O HC; lia|].
             assert (NE : blk_id b' <> blk_id b) by (intros EQ; exact (D2 _ _ Hb' (SLB0 _ Hb) EQ)).
             pose proof (DISJ b' b ltac:(apply in_or_app; right; apply SLX; exact Hb') ltac:(apply in_or_app; right; apply SLB; exact Hb) NE) as DD. clear - K W1 W2 Hr DD. lia.
          -- apply HXF. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; left. subst iv. unfold VDSO_X. cbn [rin_ivs fst snd]. left. exact K.
        * apply rin_ivs_app in K. destruct K as [K|K]; [apply HXF; unfold XF; apply rin_ivs_app; right; apply rin_ivs_app; right; apply rin_ivs_app; left; exact K|].
          destruct (mid_err M') as [|c] eqn:EQ; [destruct K|]. cbn [errph_foot rin_ivs fst snd] in K. destruct K as [K|[]].
          destruct (dwkG_es _ _ _ _ _ _ _ _ _ _ c DW EQ) as [I5 Z5].
          destruct (mid_err M) as [|c0] eqn:EQ0.
          -- (* [comment removed for export] *)
             assert (IE : In (ec_es c) LE).
             { destruct NEW as (LA & LE2 & PM & CA & CE). rewrite CTX in CA. cbn in CA. subst LA. cbn [app] in PM. rewrite ?EQ0, ?EQ in CE. cbn [errph_delta] in CE.
               destruct CE as (_ & _ & _ & FA). eapply Permutation_in; [apply Permutation_sym; exact PM|].
               exact (proj1 (Forall_forall _ _) FA (ec_es c) ltac:(unfold chain_blocks; cbn [In]; tauto)). }
             pose proof (HB (ec_es c) ltac:(apply in_or_app; right; apply SLE; exact IE)) as E. rewrite Z5 in E.
             pose proof (BRS (ec_es c) ltac:(apply in_or_app; right; apply SLE; exact IE)) as (_ & _ & _ & _ & O). rewrite Z5 in O.
             destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [clear - K E HC CEIL LO STK0; lia| clear - K O HC HCEILB E; lia|].
             pose proof (DISJ (ec_es c) b ltac:(apply in_or_app; right; apply SLE; exact IE) ltac:(apply in_or_app; right; apply SLB; exact Hb) (DLE _ _ IE Hb)) as DD.
             rewrite Z5 in DD. clear - K Hr DD. lia.
          -- destruct STP as (_ & _ & SE0 & _). rewrite EQ0, EQ in SE0. pose proof (SE0 c0 eq_refl) as EE. injection EE as <-.
             apply HXF. unfold XF. rewrite EQ0. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; right. cbn [errph_foot rin_ivs fst snd]. left. exact K.
  Qed.

  Lemma dwk_libX : forall Lx Lx' NB S' M' M'' LE LEn w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' m2 mo2 s2' X (v0 v1 v3 v4 v5 v6 v9 v10 : word) j3',
    dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' ->
    LIBMID (LEn ++ LE ++ LIB) m2 M'' -> mid_step M' M'' -> mid_newlib_ok M' M'' LEn -> mid_ctx M'' = mid_ctx M' ->
    Z.of_nat (length (mid_errblocks M'')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M'') <= ERRSTR_BYTES -> lb_big (mid_errblocks M'') = 0 ->
    xpres (drest Lx NB LE) SPc (X ++ ERR_X ++ errph_foot (mid_err M')) m1 m2 ->
    Forall (fun iv : Z * Z => (SPc <= fst iv /\ snd iv <= SPc + 112) \/ (SPc + O_F3 <= fst iv /\ snd iv <= SPc + O_SAVES)
                              \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) \/ iv = (A_vdso_func, A_vdso_func + 8)) X ->
    hs_RHEAP H s2' (mid_errblocks M'' ++ drest Lx' NB (LEn ++ LE)) m2 -> hs_KREL H s2' mo2 -> hs_MPRES H mo mo2 ->
    (exists errv', rw_cells rsegs m2 RERRNO [C4 errv']) -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    rw_cells rsegs m2 SPc (dframe v0 v1 v3 v4 v5 v6 v9 v10) -> rw_cells rsegs m2 (SPc + O_F3) [CB 88 j3'] ->
    dwk Lx' NB S' M'' (LEn ++ LE) v0 v1 v3 v4 v5 v6 v9 v10 j3' m2 mo2 s2'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame.
    intros until j3'. intros DW LM2 STP2 NEW2 CTX2 EC2 EB2 EG2 XP FX HP2 KREL2 MP2 ERR2 MI2 ST2 AUX2 FR0' FR3'.
    apply (dwkG_libX Lx Lx' NB S' M' M'' LE LEn (dframe w0 w1 w3 w4 w5 w6 w9 w10) j3 m1 mo1 s1' m2 mo2 s2' X (dframe v0 v1 v3 v4 v5 v6 v9 v10) j3'); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma dwk_lib : forall Lx Lx' NB S' M' M'' LE LEn w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' m2 mo2 s2' X (v0 v1 v3 v4 v5 v6 v9 v10 : word) j3',
    dwk Lx NB S' M' LE w0 w1 w3 w4 w5 w6 w9 w10 j3 m1 mo1 s1' ->
    LIBMID (LEn ++ LE ++ LIB) m2 M'' -> mid_step M' M'' -> mid_newlib_ok M' M'' LEn -> mid_ctx M'' = mid_ctx M' ->
    Z.of_nat (length (mid_errblocks M'')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M'') <= ERRSTR_BYTES -> lb_big (mid_errblocks M'') = 0 ->
    xpres (drest Lx NB LE) SPc (X ++ ERR_X ++ errph_foot (mid_err M')) m1 m2 ->
    Forall (fun iv : Z * Z => (SPc <= fst iv /\ snd iv <= SPc + 112) \/ (SPc + O_F3 <= fst iv /\ snd iv <= SPc + O_SAVES)
                              \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) X ->
    hs_RHEAP H s2' (mid_errblocks M'' ++ drest Lx' NB (LEn ++ LE)) m2 -> hs_KREL H s2' mo2 -> hs_MPRES H mo mo2 ->
    (exists errv', rw_cells rsegs m2 RERRNO [C4 errv']) -> mem_inv rsegs m2 -> stk rsegs m2 lo SPc -> hs_rauxv_ok H m2 B ->
    rw_cells rsegs m2 SPc (dframe v0 v1 v3 v4 v5 v6 v9 v10) -> rw_cells rsegs m2 (SPc + O_F3) [CB 88 j3'] ->
    dwk Lx' NB S' M'' (LEn ++ LE) v0 v1 v3 v4 v5 v6 v9 v10 j3' m2 mo2 s2'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX NAR NBR MST POS BTR BT_frame.
    intros until j3'. intros DW LM2 STP2 NEW2 CTX2 EC2 EB2 EG2 XP FX. eapply dwk_libX; try eassumption.
    eapply Forall_impl; [| exact FX]. cbn beta. intros iv [K|[K|K]]; [left; exact K| right; left; exact K| right; right; left; exact K].
  Qed.
End RC.
