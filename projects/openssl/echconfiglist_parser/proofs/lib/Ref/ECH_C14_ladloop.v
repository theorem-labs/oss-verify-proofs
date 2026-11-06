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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep
     ECH_LibState ECH_C1_stmt ECH_C1_malloc ECH_C1_realloc ECH_C6_stmt ECH_C7_stmt ECH_C7_rd ECH_C7_rd2 ECH_C14_stmt ECH_KitSeg ECH_C14_bio2buf ECH_C14_ladder.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mb_static (R R' : membio) : Prop :=
  mb_buf R' = mb_buf R /\ mb_len R' = mb_len R /\ mb_bb R' = mb_bb R /\ mb_bm R' = mb_bm R /\ mb_rp R' = mb_rp R
  /\ mb_id R' = mb_id R /\ mb_bbid R' = mb_bbid R /\ mb_bmid R' = mb_bmid R /\ mb_rpid R' = mb_rpid R.
Lemma mb_static_refl : forall R, mb_static R R.
Proof. intros R. unfold mb_static. repeat split; reflexivity. Qed.
Lemma mb_static_read : forall R R' n, mb_static R R' -> mb_static R (mb_after_read R' n).
Proof. intros R R' n S. unfold mb_static, mb_after_read, mb_advance in *. cbn. exact S. Qed.
Lemma mb_static_blocks : forall a R R', mb_static R R' -> blocks_MEMBIO a R' = blocks_MEMBIO a R.
Proof. intros a R R' (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9). unfold blocks_MEMBIO. congruence. Qed.
Lemma mb_static_foot : forall a R R', mb_static R R' -> MEMBIO_foot a R' = MEMBIO_foot a R.
Proof. intros a R R' (S1 & S2 & S3 & S4 & _). unfold MEMBIO_foot. congruence. Qed.
Lemma mb_static_below : forall a R R' lo, mb_static R R' -> MEMBIO_below a R lo -> MEMBIO_below a R' lo.
Proof. intros a R R' lo (S1 & S2 & S3 & S4 & S5 & _) BL. unfold MEMBIO_below in *. rewrite S3, S4, S5. exact BL. Qed.
Lemma mb_static_apart : forall a R R', mb_static R R' -> MEMBIO_apart a R -> MEMBIO_apart a R'.
Proof. intros a R R' (S1 & S2 & S3 & S4 & S5 & _) AP. unfold MEMBIO_apart in *. rewrite S3, S4, S5. exact AP. Qed.
Lemma mb_static_sep : forall a R R', mb_static R R' -> MEMBIO_sep a R -> MEMBIO_sep a R'.
Proof.
  intros a R R' ST SE. destruct SE as (AP & E1 & E2 & E3 & E4). split; [exact (mb_static_apart a R R' ST AP)|].
  destruct ST as (S1 & S2 & S3 & S4 & S5 & _). rewrite S1, S2, S3, S4, S5. exact (conj E1 (conj E2 (conj E3 E4))).
Qed.
Lemma mb_after_read_pos : forall R n, mb_pos (mb_after_read R n) = mb_pos R + n.
Proof. reflexivity. Qed.
Lemma mb_after_read_len : forall R n, mb_len (mb_after_read R n) = mb_len R.
Proof. reflexivity. Qed.

Lemma firstn_app_skipn : forall (l : list byte) a b, firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof.
  intros l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity| rewrite IH; reflexivity].
Qed.

Definition LAD_STACK : Z := Z.max BIOREADEX_STACK (Z.max BIOEOF_STACK CREALLOC_STACK).

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let HRE : realloc_sr_stmt H := proj1 (proj2 HX).

  (* [comment removed for export] *)
  Variables (sp gp : word) (F : bvmap 5 word) (fc : bv 32) (mb lo B : Z) (R : membio) (ds : list byte) (LB Lh : list block) (m0 : mem) (mo0 : Model).
  Let SP' : Z := bv_unsigned sp + -2352.
  Let RBP : Z := bv_unsigned sp + -2240.
  Let XW : list (Z * Z) := (bv_unsigned sp + -2240, bv_unsigned sp + -2232) :: MEMBIO_foot mb R.
  Hypothesis MBB : MEMBIO_below mb R lo.
  Hypothesis MBS : MEMBIO_sep mb R.
  Hypothesis DSL : zlength ds = mb_len R.
  Hypothesis SUBLB : forall b, In b LB -> In b Lh.
  Hypothesis PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB.
  Hypothesis BUDB : lb_bytes Lh + 512 * 65 <= hs_LIVE_MAX H.
  Hypothesis BUDC : Z.of_nat (length Lh) + 2 <= hs_LIVE_CNT_MAX H.
  Hypothesis BUDG : lb_big Lh + 2 <= hs_LIVE_BIG_MAX H.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis CEIL : hceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 2352 - LAD_STACK.

  (* [comment removed for export] *)
  Definition LAD (k : Z) (m : mem) (s : PState) (p : bptr) (A : Z) (R' : membio) : Prop :=
       hs_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m
    /\ MEMBIO LB m mb R' /\ mb_static R R' /\ mb_pos R' = 512 * k /\ 512 * k < mb_len R
    /\ bytes_at rsegs m (mb_buf R) ds
    /\ bytes_at rsegs m A (firstn (Z.to_nat (512 * k)) ds)
    /\ (exists junk, rw_cells rsegs m (A + 512 * k) [CB 512 junk])
    /\ (exists rb, rw_cells rsegs m RBP [C8 (wz rb)])
    /\ (exists errv, rw_cells rsegs m RERRNO [C4 errv])
    /\ METH_mem m /\ IMPL_mem m /\ GOT_mem m
    /\ mem_inv rsegs m /\ stk rsegs m lo SP' /\ hs_rauxv_ok H m B
    /\ xpres Lh SP' XW m0 m.

  (* [comment removed for export] *)
  Definition lad_doneK (Q : config -> Prop) : Prop :=
    forall (k n : Z) (m : mem) (mo : Model) (s : PState) (p : bptr) (A : Z) (R' : membio) (junk : list byte)
           (s7v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      0 <= k <= 31 -> n = mb_len R - 512 * k -> 1 <= n <= 512 ->
      hs_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m -> hs_KREL H s mo -> hs_MPRES H mo0 mo ->
      MEMBIO LB m mb R' -> mb_static R R' -> mb_pos R' = mb_len R ->
      bytes_at rsegs m (mb_buf R) ds -> bytes_at rsegs m A ds -> rw_cells rsegs m (A + mb_len R) [CB (Z.to_nat (512 * (k + 1) - mb_len R)) junk] ->
      rw_cells rsegs m RBP [C8 (wz n)] -> (exists errv, rw_cells rsegs m RERRNO [C4 errv]) ->
      METH_mem m -> IMPL_mem m -> GOT_mem m -> mem_inv rsegs m -> stk rsegs m lo SP' -> hs_rauxv_ok H m B ->
      xpres Lh SP' XW m0 m ->
      hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 LD_RD) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 mb) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 RBP) (Z_to_bv 64 1) (Z_to_bv 64 (32 - k)) s7v
                                 (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 (512 * k)) (Z_to_bv 64 (- (512 * k))) t3 t4 t5 t6)
                            F (Z_to_bv 64 LD_RD) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  Definition lad_capK (Q : config -> Prop) : Prop :=
    forall (m : mem) (mo : Model) (s : PState) (p : bptr) (A rv : Z) (R' : membio)
           (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8v s9v s10v s11v t3 t4 t5 t6 : word),
      hs_RHEAP H s ((p, A, 512 * 33) :: Lh) m -> hs_KREL H s mo -> hs_MPRES H mo0 mo ->
      MEMBIO LB m mb R' -> mb_static R R' -> mb_pos R' = 512 * 32 -> 512 * 32 < mb_len R ->
      bytes_at rsegs m (mb_buf R) ds -> (exists rb, rw_cells rsegs m RBP [C8 (wz rb)]) -> (exists errv, rw_cells rsegs m RERRNO [C4 errv]) ->
      METH_mem m -> IMPL_mem m -> GOT_mem m -> mem_inv rsegs m -> stk rsegs m lo SP' -> hs_rauxv_ok H m B ->
      xpres Lh SP' XW m0 m ->
      hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 LD_RC) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                                 (Z_to_bv 64 mb) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 RBP) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 A)
                                 s8v s9v s10v s11v t3 t4 t5 t6)
                            F (ret_pc (Z_to_bv 64 LD_RC)) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  Definition lad_entry (k : Z) (m : mem) (A : Z) (s7v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 RP_R3) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 mb) (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 512) (Z_to_bv 64 RBP) a4 a5 a6 a7
            (Z_to_bv 64 mb) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 RBP) (Z_to_bv 64 1) (Z_to_bv 64 (32 - k)) s7v
            (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 (512 * k)) (Z_to_bv 64 (- (512 * k))) t3 t4 t5 t6)
       F (Z_to_bv 64 P_BIO_read_ex) fc None m (seg_rom rsegs).

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma lad_head_facts : forall s p A n m,
    hs_RHEAP H s ((p, A, n) :: Lh) m ->
    rblock_range A n /\ A + n <= hceil /\ ~ In p (map blk_id Lh)
    /\ (forall b, In b Lh -> A + n <= blk_addr b \/ blk_addr b + blk_size b <= A)
    /\ (forall b, In b Lh -> blk_addr b + blk_size b <= hceil).
  Proof.
    intros s p A n m HP.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (or_introl eq_refl)) as BR. cbn [blk_addr blk_size fst snd] in BR.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND. cbn [map blk_id fst snd] in ND.
    assert (NI : ~ In p (map blk_id Lh)) by (inversion ND; assumption).
    split; [exact BR|]. split; [destruct BR as (_ & _ & _ & B4 & _); exact B4|]. split; [exact NI|]. split.
    - intros b Hb. pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ (p, A, n) b HP (or_introl eq_refl) (or_intror Hb)) as D.
      cbn [blk_addr blk_size blk_id fst snd] in D. apply D. intros E. apply NI. rewrite E. apply in_map. exact Hb.
    - intros b Hb. exact (HH_blocks_below H HH _ _ _ HP b (or_intror Hb)).
  Qed.

  (* [comment removed for export] *)
  Local Ltac img_static := unfold RERRNO, A_malloc_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD; cbn; lia.
  Local Ltac unf_stk_in H := unfold LAD_STACK, BIOREADEX_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, BIOCTRL_STACK, MEMCTRL_STACK, MEMREAD_STACK,
      BIOACC_STACK, CREALLOC_STACK, RREALLOC_STACK, RMALLOC_STACK, FR_BIO_set_data, FR_bio_read_intern, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
      FR_BIO_eof, FR_CRYPTO_realloc in H.
  Local Ltac unf_stk := unfold LAD_STACK, BIOREADEX_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, BIOCTRL_STACK, MEMCTRL_STACK, MEMREAD_STACK,
      BIOACC_STACK, CREALLOC_STACK, RREALLOC_STACK, RMALLOC_STACK, FR_BIO_set_data, FR_bio_read_intern, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
      FR_BIO_eof, FR_CRYPTO_realloc.

  (* [comment removed for export] *)
  Lemma lad_read : forall k m mo s p A R' (s7v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Q : config -> Prop),
    0 <= k <= 31 -> LAD k m s p A R' -> hs_KREL H s mo ->
    (forall m2 (R2 : membio) (n : Z) (junk' : list byte) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
       n = Z.min 512 (mb_len R - 512 * k) -> R2 = mb_after_read R' n ->
       hs_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m2 -> MEMBIO LB m2 mb R2 ->
       bytes_at rsegs m2 (mb_buf R) ds -> bytes_at rsegs m2 A (firstn (Z.to_nat (512 * k)) ds) ->
       rw_cells rsegs m2 (A + 512 * k) [CB (Z.to_nat n) (mb_take R' ds n); CB (Z.to_nat 512 - Z.to_nat n) junk'] ->
       rw_cells rsegs m2 RBP [C8 (wz n)] -> (exists errv, rw_cells rsegs m2 RERRNO [C4 errv]) ->
       METH_mem m2 -> IMPL_mem m2 -> GOT_mem m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SP' -> hs_rauxv_ok H m2 B ->
       xpres Lh SP' XW m0 m2 ->
       hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 LD_R1) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A)
                                  (Z_to_bv 64 (mem_ctrl_rv R2 BIO_CTRL_EOF)) b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 mb) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 RBP) (Z_to_bv 64 1) (Z_to_bv 64 (32 - k)) s7v
                                  (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 (512 * k)) (Z_to_bv 64 (- (512 * k))) u3 u4 u5 u6)
                             F (ret_pc (Z_to_bv 64 LD_R1)) fc None m2 (seg_rom rsegs)) mo)) ->
    hs_SR H Q (mkCfg (lad_entry k m A s7v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6) mo).
  Proof.
    intros k m mo s p A R' s7v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Q KR INV KREL KONT.
    destruct INV as (HP & MBO & MST & POS & KL & DS & PRE & [junk JK] & [rb RB] & [errv ERR] & ME & IM & GM & MI & ST & AUX & XP).
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unf_stk_in LO.
    destruct (lad_head_facts _ _ _ _ _ HP) as (BR & BH & NIP & DISJ & BEL).
    pose proof BR as (B1 & B2 & B3 & B4 & B5).
    pose proof MST as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
    pose proof MBO as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & _).
    rewrite S1, S2, S3, S4, S5, S6, S7, S8, S9 in *.
    pose proof (DISJ _ (SUBLB _ I1)) as D1. pose proof (DISJ _ (SUBLB _ I2)) as D2. pose proof (DISJ _ (SUBLB _ I3)) as D3. pose proof (DISJ _ (SUBLB _ I4)) as D4.
    pose proof (BEL _ (SUBLB _ I1)) as E1. pose proof (BEL _ (SUBLB _ I2)) as E2. pose proof (BEL _ (SUBLB _ I3)) as E3. pose proof (BEL _ (SUBLB _ I4)) as E4.
    cbn [blk_addr blk_size fst snd] in D1, D2, D3, D4, E1, E2, E3, E4.
    pose proof RB1 as (_ & _ & _ & _ & O1). pose proof RB3 as (_ & _ & _ & _ & O3). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    assert (L1 : 1 <= mb_len R) by lia. destruct (PAYL L1) as [pD PIN].
    pose proof (DISJ _ (SUBLB _ PIN)) as DP. cbn [blk_addr blk_size fst snd] in DP.
    unfold zlength in DSL.
    assert (PREL : length (firstn (Z.to_nat (512 * k)) ds) = Z.to_nat (512 * k)) by (rewrite firstn_length; lia).
    (* [comment removed for export] *)
    assert (MO1 : memrd_out mb R' (A + 512 * k) 512 lo SP').
    { unfold memrd_out. rewrite (mb_static_blocks mb R R' MST), S1, S2. unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      split; [left; clear - BH KR CEIL; lia|]. split; [clear - B1 KR; lia|]. split; [clear - BH KR HCEILB; lia|].
      split; [apply Forall_cons; [cbn; clear - D1 KR; lia|]; apply Forall_cons; [cbn; clear - D2 KR; lia|];
             apply Forall_cons; [cbn; clear - D3 KR; lia|]; apply Forall_cons; [cbn; clear - D4 KR; lia|]; apply Forall_nil|].
      split; [clear - DP KR; lia| unfold A_mem_buf_method, O_METH_BREAD; clear - B5 B3 KR; lia]. }
    assert (MO2 : memrd_out mb R' RBP 8 lo SP').
    { unfold memrd_out, RBP, SP'. rewrite (mb_static_blocks mb R R' MST), S1, S2. unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE.
      split; [right; clear; lia|]. split; [clear - LO LO0; lia|]. split; [clear - SPR; lia|].
      split; [apply Forall_cons; [cbn; clear - E1 CEIL LO; lia|]; apply Forall_cons; [cbn; clear - E2 CEIL LO; lia|];
             apply Forall_cons; [cbn; clear - E3 CEIL LO; lia|]; apply Forall_cons; [cbn; clear - E4 CEIL LO; lia|]; apply Forall_nil|].
      split; [clear - BUFH CEIL LO; lia| unfold A_mem_buf_method, O_METH_BREAD; clear - LO CEIL HCEILB; lia]. }
    pose proof bioreadex_mem_spec as RD. unfold bioreadex_mem_stmt, readintern_mem_stmt_at in RD.
    unfold lad_entry.
    eapply (sr_evt_krel H HH); [exact KREL| |].
    { eapply RD with (lo := lo) (LB := LB) (a := mb) (out := A + 512 * k) (outl := 512) (rbp := RBP) (rbv := rb) (R := R') (ds := ds) (junk := junk); clear RD;
        try reflexivity.
      all: try first [exact MBO| exact ME| exact JK| exact RB| exact MI| exact CEIL].
      all: lazymatch goal with
           | |- 0 < 512 < _ => clear; lia
           | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST| exact MBB]
           | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST| exact MBS]
           | |- bytes_at _ _ _ _ => rewrite S1; exact DS
           | |- Z.of_nat (length ds) = _ => rewrite S2; exact DSL
           | |- memrd_out _ _ _ 512 _ _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); exact MO1
           | |- memrd_out _ _ _ 8 _ _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); exact MO2
           | |- _ + 8 <= _ \/ _ => right; unfold RBP; clear - BH CEIL LO KR; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); exact ST
           | |- lo <= _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); unf_stk; unfold SP'; clear - LO; lia
           | |- _ mod 2 = 0 => unfold RP_R3; rewrite unsigned_lit by (clear; lia); reflexivity
           end. }
    intros ms1 PO. unfold memrd_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & junk1 & -> & MU1 & WM1 & MI1 & ST1 & MBO1 & DS1 & OUT1 & RBc1).
    rewrite (unsigned_lit SP') in MU1, ST1 by (unfold SP'; lia).
    rewrite (mb_static_foot mb R R' MST) in MU1. unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU1.
    cbn [mb_buf mb_after_read mb_advance] in DS1. rewrite S1 in DS1.
    (* [comment removed for export] *)
    unfold mb_rdn, mb_avail in *. rewrite S2, POS in *.
    set (n := Z.min 512 (mb_len R - 512 * k)) in *.
    assert (NR : 1 <= n <= 512) by (subst n; lia).
    assert (TKL : length (mb_take R' ds n) = Z.to_nat n).
    { unfold mb_take. rewrite firstn_length, length_skipn, POS. clear - NR KL KR DSL. lia. }
    rewrite TKL in OUT1.
    replace (rd_ok n) with 1 by (unfold rd_ok; replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    (* [comment removed for export] *)
    assert (HP1 : hs_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; right; exists (p, A, 512 * (k + 1)); split; [left; reflexivity| cbn; lia]|].
      apply Forall_cons; [left; cbn; unfold RBP; lia|].
      apply Forall_cons; [right; right; exists (mb_id R, mb, 128); split; [right; apply SUBLB; exact I1| cbn; lia]|].
      apply Forall_cons; [right; right; exists (mb_bmid R, mb_bm R, 32); split; [right; apply SUBLB; exact I3| cbn; lia]| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL, RBP.
      clear - SPB CEIL HCEILB LO KR BH O1 O3 E1 E3 B5. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
    assert (PRE1 : bytes_at rsegs m1 A (firstn (Z.to_nat (512 * k)) ds)).
    { eapply bytes_at_transport; [exact PRE| exact MU1|]. rewrite PREL. unfold RBP. clear - BH CEIL HCEILB LO KR D1 D3. cbn. lia. }
    assert (ERR1 : rw_cells rsegs m1 RERRNO [C4 errv]) by (eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| unfold RBP; clear - CEIL HCEILB LO KR B5 O1 O3; img_static]).
    assert (ME1 : METH_mem m1) by (unfold METH_mem in *; eapply rw_cells_transport; [exact ME| exact MU1| exact WM1| unfold RBP; clear - CEIL HCEILB LO KR B5 O1 O3; img_static]).
    assert (IM1 : IMPL_mem m1) by (unfold IMPL_mem in *; eapply rw_cells_transport; [exact IM| exact MU1| exact WM1| unfold RBP; clear - CEIL HCEILB LO KR B5 O1 O3; img_static]).
    assert (GM1 : GOT_mem m1) by (unfold GOT_mem in *; eapply rw_cells_transport; [exact GM| exact MU1| exact WM1| unfold RBP; clear - CEIL HCEILB LO KR B5 O1 O3; img_static]).
    assert (XP1 : xpres Lh SP' XW m0 m1).
    { eapply xpres_trans; [exact XP|].
      pose proof (xpres_of_munch_block H HH s _ m m m1 SP' XW _ (p, A, 512 * (k + 1)) HP (or_introl eq_refl) ltac:(unfold SP'; lia) MU1 WM1) as K.
      cbn [blk_id blk_addr blk_size fst snd] in K. rewrite (proj1 (HH_lb_remove H HH)) in K by exact NIP. apply K.
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; lia|].
      apply Forall_cons; [right; right; intros a Ha; cbn in Ha; unfold XW, RBP; cbn [rin_ivs fst snd]; left; lia|].
      apply Forall_cons; [right; right; intros a Ha; cbn in Ha; unfold XW, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; cbn [rin_ivs fst snd]; right; left; lia|].
      apply Forall_cons; [right; right; intros a Ha; cbn in Ha; unfold XW, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE; cbn [rin_ivs fst snd]; right; right; left; lia| apply Forall_nil]. }
    clear MU1 WM1 HP AUX PRE ERR ME IM GM MI ST XP MBO JK RB DS.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 RP_R3)) with (Z_to_bv 64 RP_R3) by (symmetry; apply ret_pc_even; [unfold RP_R3; lia| reflexivity]).
    eapply (sr_evt_krel H HH); [exact KREL| eapply ld_seg1; [reflexivity| exact MI1]|]. intros ms2 ->.
    (* [comment removed for export] *)
    pose proof (mb_static_read R R' n MST) as MST1.
    pose proof bioeof_mem_spec as EF. unfold bioeof_mem_stmt in EF.
    eapply (sr_evt_krel H HH); [exact KREL| |].
    { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := mb_after_read R' n); clear EF; try reflexivity.
      all: try first [exact MBO1| exact ME1| exact MI1| exact CEIL].
      all: lazymatch goal with
           | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST1| exact MBB]
           | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST1| exact MBS]
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact ST1
           | |- lo <= _ => rewrite unsigned_lit by lia; unf_stk; unfold SP'; clear - LO; lia
           | |- _ mod 2 = 0 => unfold LD_R1; rewrite unsigned_lit by lia; reflexivity
           end. }
    intros ms3 PO. unfold memctrl_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & MBO2).
    rewrite (unsigned_lit SP') in MU2, ST2 by (unfold SP'; lia).
    (* [comment removed for export] *)
    eapply (KONT m2 (mb_after_read R' n) n junk1); clear KONT.
    - reflexivity.
    - reflexivity.
    - eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU2| exact WM2|]. apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil].
    - exact MBO2.
    - eapply bytes_at_transport; [exact DS1| exact MU2|]. rewrite DSL. clear - BUFH CEIL; cbn; lia.
    - eapply bytes_at_transport; [exact PRE1| exact MU2|]. rewrite PREL. clear - BH CEIL KR; cbn; lia.
    - eapply rw_cells_transport; [exact OUT1| exact MU2| exact WM2|]. clear - BH CEIL KR NR; cbn. lia.
    - eapply rw_cells_transport; [exact RBc1| exact MU2| exact WM2|]. unfold RBP. clear; cbn; lia.
    - exists errv. eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2| clear - CEIL HCEILB; img_static].
    - unfold METH_mem in *; eapply rw_cells_transport; [exact ME1| exact MU2| exact WM2| clear - CEIL HCEILB; img_static].
    - unfold IMPL_mem in *; eapply rw_cells_transport; [exact IM1| exact MU2| exact WM2| clear - CEIL HCEILB; img_static].
    - unfold GOT_mem in *; eapply rw_cells_transport; [exact GM1| exact MU2| exact WM2| clear - CEIL HCEILB; img_static].
    - exact MI2.
    - exact ST2.
    - eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU2| exact WM2|]. unfold RAUXV_CELL. clear - SPB CEIL HCEILB LO; apply Forall_cons; [cbn; lia| apply Forall_nil].
    - eapply xpres_trans; [exact XP1|]. eapply xpres_of_munch; [exact MU2| exact WM2| | exact BEL]. apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma lad_done : forall k m2 mo s p A R' (n : Z) (junk' : list byte) (s7v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (Q : config -> Prop),
    0 <= k <= 31 -> n = mb_len R - 512 * k -> 1 <= n <= 512 ->
    hs_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m2 -> hs_KREL H s mo -> hs_MPRES H mo0 mo ->
    MEMBIO LB m2 mb (mb_after_read R' n) -> mb_static R R' -> mb_pos R' = 512 * k ->
    bytes_at rsegs m2 (mb_buf R) ds -> bytes_at rsegs m2 A (firstn (Z.to_nat (512 * k)) ds) ->
    rw_cells rsegs m2 (A + 512 * k) [CB (Z.to_nat n) (mb_take R' ds n); CB (Z.to_nat 512 - Z.to_nat n) junk'] ->
    rw_cells rsegs m2 RBP [C8 (wz n)] -> (exists errv, rw_cells rsegs m2 RERRNO [C4 errv]) ->
    METH_mem m2 -> IMPL_mem m2 -> GOT_mem m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SP' -> hs_rauxv_ok H m2 B ->
    xpres Lh SP' XW m0 m2 -> lad_doneK Q ->
    hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 LD_R1) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A)
                               (Z_to_bv 64 (mem_ctrl_rv (mb_after_read R' n) BIO_CTRL_EOF)) b1 b2 b3 b4 b5 b6 b7
                               (Z_to_bv 64 mb) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 RBP) (Z_to_bv 64 1) (Z_to_bv 64 (32 - k)) s7v
                               (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 (512 * k)) (Z_to_bv 64 (- (512 * k))) u3 u4 u5 u6)
                          F (ret_pc (Z_to_bv 64 LD_R1)) fc None m2 (seg_rom rsegs)) mo).
  Proof.
    intros k m2 mo s p A R' n junk' s7v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Q KR NEQ NR HP KREL MP MBO MST POS DS PRE OUT RBc [errv ERR] ME IM GM MI ST AUX XP KD.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unf_stk_in LO.
    destruct (lad_head_facts _ _ _ _ _ HP) as (BR & BH & NIP & DISJ & BEL).
    pose proof MST as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
    pose proof (mb_static_read R R' n MST) as MST1.
    pose proof MBO as MB0. destruct MB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BUFP & BUFH & _).
    cbn [mb_buf mb_len mb_after_read mb_advance] in BUFP, BUFH. rewrite S1, S2 in BUFH.
    unfold zlength in DSL.
    assert (PREL : length (firstn (Z.to_nat (512 * k)) ds) = Z.to_nat (512 * k)) by (rewrite firstn_length; clear - KR NEQ NR DSL; lia).
    assert (RV : mem_ctrl_rv (mb_after_read R' n) BIO_CTRL_EOF = 1).
    { unfold mem_ctrl_rv, mb_avail. cbn [mb_len mb_pos mb_after_read mb_advance]. rewrite S2, POS.
      replace (mb_len R - (512 * k + n) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    rewrite RV.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 LD_R1)) with (Z_to_bv 64 LD_R1) by (symmetry; apply ret_pc_even; [unfold LD_R1; lia| reflexivity]).
    eapply (sr_evt_krel H HH); [exact KREL| eapply ld_seg2_eof; [reflexivity| clear; lia| exact MI]|]. intros ms3 ->.
    (* [comment removed for export] *)
    pose proof bioeof_mem_spec as EF. unfold bioeof_mem_stmt in EF.
    eapply (sr_evt_krel H HH); [exact KREL| |].
    { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := mb_after_read R' n); clear EF; try reflexivity.
      all: try first [exact MBO| exact ME| exact MI| exact CEIL].
      all: lazymatch goal with
           | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST1| exact MBB]
           | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST1| exact MBS]
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); exact ST
           | |- lo <= _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); unf_stk; unfold SP'; clear - LO; lia
           | |- _ mod 2 = 0 => unfold LD_RD; rewrite unsigned_lit by (clear; lia); reflexivity
           end. }
    intros ms4 PO. unfold memctrl_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & MBO3).
    rewrite (unsigned_lit SP') in MU3, ST3 by (unfold SP'; lia). rewrite RV.
    replace (ret_pc (Z_to_bv 64 LD_RD)) with (Z_to_bv 64 LD_RD) by (symmetry; apply ret_pc_even; [unfold LD_RD; lia| reflexivity]).
    (* [comment removed for export] *)
    apply (rw_cells_transport rsegs _ m2 m3 _ _ OUT) in MU3 as OUT3; [| exact WM3| clear - BH CEIL KR NR; cbn; lia].
    apply (proj1 (rw_cells_app rsegs m3 _ [CB (Z.to_nat n) (mb_take R' ds n)] [CB (Z.to_nat 512 - Z.to_nat n) junk'])) in OUT3.
    destruct OUT3 as [DATA JK3]. cbn [cells_size csize Nat.add] in JK3.
    apply rw_cells_bytes_at in DATA. cbn [cells_bytes cbytes app] in DATA. rewrite app_nil_r in DATA.
    apply (bytes_at_transport rsegs _ m2 m3 _ _ PRE) in MU3 as PRE3; [| rewrite PREL; clear - BH CEIL KR; cbn; lia].
    assert (ALL : bytes_at rsegs m3 A ds).
    { pose proof (proj2 (bytes_at_app rsegs m3 A (firstn (Z.to_nat (512 * k)) ds) (mb_take R' ds n))) as J. rewrite PREL in J.
      replace (A + Z.of_nat (Z.to_nat (512 * k))) with (A + 512 * k) in J by (clear - KR; lia).
      specialize (J (conj PRE3 DATA)). unfold mb_take in J. rewrite POS, firstn_app_skipn in J.
      replace (Z.to_nat (512 * k) + Z.to_nat n)%nat with (length ds) in J by (clear - KR NR NEQ DSL; lia).
      rewrite firstn_all in J. exact J. }
    unfold lad_doneK in KD.
    eapply (KD k n m3 mo s p A (mb_after_read R' n) junk'); clear KD.
    all: try first [exact KR| exact NEQ| exact NR| exact KREL| exact MP| exact MBO3| exact MST1| exact ALL| exact MI3| exact ST3].
    - eapply (HH_RHEAP_frame H HH); [exact HP| exact MU3| exact WM3|]. apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil].
    - cbn [mb_pos mb_after_read mb_advance]. rewrite POS. clear - NEQ; lia.
    - eapply bytes_at_transport; [exact DS| exact MU3|]. rewrite DSL. clear - BUFH CEIL; cbn; lia.
    - replace (A + mb_len R) with (A + 512 * k + Z.of_nat (Z.to_nat n + 0)) by (clear - NEQ NR; lia).
      replace (Z.to_nat (512 * (k + 1) - mb_len R)) with (Z.to_nat 512 - Z.to_nat n)%nat by (clear - NEQ NR KR; lia). exact JK3.
    - eapply rw_cells_transport; [exact RBc| exact MU3| exact WM3|]. unfold RBP. clear; cbn; lia.
    - exists errv. eapply rw_cells_transport; [exact ERR| exact MU3| exact WM3| clear - CEIL HCEILB; img_static].
    - unfold METH_mem in *; eapply rw_cells_transport; [exact ME| exact MU3| exact WM3| clear - CEIL HCEILB; img_static].
    - unfold IMPL_mem in *; eapply rw_cells_transport; [exact IM| exact MU3| exact WM3| clear - CEIL HCEILB; img_static].
    - unfold GOT_mem in *; eapply rw_cells_transport; [exact GM| exact MU3| exact WM3| clear - CEIL HCEILB; img_static].
    - eapply (HH_rauxv_frame H HH); [exact AUX| exact MU3| exact WM3|]. unfold RAUXV_CELL. clear - SPB CEIL HCEILB LO; apply Forall_cons; [cbn; lia| apply Forall_nil].
    - eapply xpres_trans; [exact XP|]. eapply xpres_of_munch; [exact MU3| exact WM3| | exact BEL]. apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma lad_grow : forall k m2 mo s p A R' (n : Z) (junk' : list byte) (s7v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (Q : config -> Prop),
    0 <= k <= 31 -> n = 512 -> 512 * k + 512 < mb_len R ->
    hs_RHEAP H s ((p, A, 512 * (k + 1)) :: Lh) m2 -> hs_KREL H s mo -> hs_MPRES H mo0 mo ->
    MEMBIO LB m2 mb (mb_after_read R' n) -> mb_static R R' -> mb_pos R' = 512 * k ->
    bytes_at rsegs m2 (mb_buf R) ds -> bytes_at rsegs m2 A (firstn (Z.to_nat (512 * k)) ds) ->
    rw_cells rsegs m2 (A + 512 * k) [CB (Z.to_nat n) (mb_take R' ds n); CB (Z.to_nat 512 - Z.to_nat n) junk'] ->
    rw_cells rsegs m2 RBP [C8 (wz n)] -> (exists errv, rw_cells rsegs m2 RERRNO [C4 errv]) ->
    METH_mem m2 -> IMPL_mem m2 -> GOT_mem m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo SP' -> hs_rauxv_ok H m2 B ->
    xpres Lh SP' XW m0 m2 ->
    (forall m4 mo4 s4 (p' : bptr) (A' : Z) (v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 : word),
       LAD (k + 1) m4 s4 p' A' (mb_after_read R' n) -> hs_KREL H s4 mo4 -> hs_MPRES H mo0 mo4 ->
       hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 LD_R3) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) v0 v1 v2 sp (Z_to_bv 64 (512 * k + 512)) (Z_to_bv 64 0) c1 c2 c3 c4 c5 c6 c7
                                  (Z_to_bv 64 mb) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 RBP) (Z_to_bv 64 1) (Z_to_bv 64 (32 - k)) (Z_to_bv 64 A')
                                  (Z_to_bv 64 (A' + 512 * k + 512)) (Z_to_bv 64 (- (512 * k + 512))) (Z_to_bv 64 (A' + 512 * k)) (Z_to_bv 64 (- (512 * k + 512))) v3 v4 v5 v6)
                             F (ret_pc (Z_to_bv 64 LD_R3)) fc None m4 (seg_rom rsegs)) mo4)) ->
    hs_SR H Q (mkCfg (MS (mkR (Z_to_bv 64 LD_R1) (Z_to_bv 64 SP') gp (Z_to_bv 64 RATP) u0 u1 u2 sp (Z_to_bv 64 A)
                               (Z_to_bv 64 (mem_ctrl_rv (mb_after_read R' n) BIO_CTRL_EOF)) b1 b2 b3 b4 b5 b6 b7
                               (Z_to_bv 64 mb) (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 RBP) (Z_to_bv 64 1) (Z_to_bv 64 (32 - k)) s7v
                               (Z_to_bv 64 (A + 512 * k)) (Z_to_bv 64 (- (512 * k))) (Z_to_bv 64 (512 * k)) (Z_to_bv 64 (- (512 * k))) u3 u4 u5 u6)
                          F (ret_pc (Z_to_bv 64 LD_R1)) fc None m2 (seg_rom rsegs)) mo).
  Proof.
    intros k m2 mo s p A R' n junk' s7v u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Q KR NEQ KL HP KREL MP MBO MST POS DS PRE OUT RBc [errv ERR] ME IM GM MI ST AUX XP KONT.
    subst n.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unf_stk_in LO.
    destruct (lad_head_facts _ _ _ _ _ HP) as (BR & BH & NIP & DISJ & BEL).
    pose proof BR as (B1 & B2 & B3 & B4 & B5).
    pose proof MST as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
    set (R2 := mb_after_read R' 512) in *.
    pose proof (mb_static_read R R' 512 MST) as MST1. change (mb_static R R2) in MST1.
    pose proof MBO as MB0. destruct MB0 as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & _).
    pose proof MST1 as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9). rewrite T1, T2, T3, T4, T5, T6, T7, T8, T9 in *.
    pose proof (BEL _ (SUBLB _ I1)) as E1. pose proof (BEL _ (SUBLB _ I2)) as E2. pose proof (BEL _ (SUBLB _ I3)) as E3. pose proof (BEL _ (SUBLB _ I4)) as E4.
    cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4.
    pose proof RB1 as (_ & _ & _ & _ & O1). pose proof RB3 as (_ & _ & _ & _ & O3). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    assert (L1 : 1 <= mb_len R) by (clear - KR KL; lia). destruct (PAYL L1) as [pD PIN].
    pose proof (BEL _ (SUBLB _ PIN)) as EP. cbn [blk_addr blk_size fst snd] in EP.
    unfold zlength in DSL.
    assert (PREL : length (firstn (Z.to_nat (512 * k)) ds) = Z.to_nat (512 * k)) by (rewrite firstn_length; clear - KR KL DSL; lia).
    assert (RV : mem_ctrl_rv R2 BIO_CTRL_EOF = 0).
    { unfold mem_ctrl_rv, mb_avail. subst R2. cbn [mb_len mb_pos mb_after_read mb_advance]. rewrite S2, POS.
      replace (mb_len R - (512 * k + 512) =? 0) with false by (symmetry; apply Z.eqb_neq; clear - KL; lia). reflexivity. }
    rewrite RV.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app rsegs m2 _ [CB (Z.to_nat 512) (mb_take R' ds 512)] [CB (Z.to_nat 512 - Z.to_nat 512) junk'])) in OUT.
    destruct OUT as [DATA _]. apply rw_cells_bytes_at in DATA. cbn [cells_bytes cbytes app] in DATA. rewrite app_nil_r in DATA.
    assert (OBS : bytes_at rsegs m2 A (firstn (Z.to_nat (512 * (k + 1))) ds)).
    { pose proof (proj2 (bytes_at_app rsegs m2 A (firstn (Z.to_nat (512 * k)) ds) (mb_take R' ds 512))) as J. rewrite PREL in J.
      replace (A + Z.of_nat (Z.to_nat (512 * k))) with (A + 512 * k) in J by (clear - KR; lia).
      specialize (J (conj PRE DATA)). unfold mb_take in J. rewrite POS, firstn_app_skipn in J.
      replace (Z.to_nat (512 * k) + Z.to_nat 512)%nat with (Z.to_nat (512 * (k + 1))) in J by (clear - KR; lia). exact J. }
    assert (OBSL : length (firstn (Z.to_nat (512 * (k + 1))) ds) = Z.to_nat (512 * (k + 1))) by (rewrite firstn_length; clear - KR KL DSL; lia).
    clear PRE DATA.
    (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 LD_R1)) with (Z_to_bv 64 LD_R1) by (symmetry; apply ret_pc_even; [unfold LD_R1; lia| reflexivity]).
    eapply (sr_evt_krel H HH); [exact KREL| eapply ld_seg2_grow with (K := 512 * k); [clear - KR; lia| clear - KR; lia| exact RBc| exact MI]|]. intros ms3 ->.
    (* [comment removed for export] *)
    pose proof (crealloc_spec H HH HRE) as RA. unfold crealloc_stmt, crealloc_stmt_gen in RA.
    eapply (sr_seq H HH).
    { eapply RA with (lo := lo) (B := B) (LB := (p, A, 512 * (k + 1)) :: Lh) (s := s) (p := p) (A := A) (old := 512 * (k + 1)) (num := 512 * k + 1024) (size := 1)
                     (obs := firstn (Z.to_nat (512 * (k + 1))) ds) (errv := errv); clear RA; try reflexivity.
      all: try first [exact HP| exact KREL| exact OBS| exact AUX| exact ST| exact CEIL| exact MI| exact IM| exact GM].
      all: lazymatch goal with
           | |- 1 <= _ < RMMAP_THRESHOLD => unfold RMMAP_THRESHOLD; clear - KR; lia
           | |- In _ _ => left; f_equal; clear - KR; lia
           | |- zlength _ = _ => unfold zlength; rewrite OBSL; clear - KR; lia
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_cons; cbn [blk_size snd]; clear - BUDB KR; lia
           | |- Z.of_nat (length _) + _ <= _ => cbn [length]; clear - BUDC; lia
           | |- lb_big _ + _ <= _ => rewrite lb_big_cons; cbn [blk_size snd]; pose proof (big1_range (512 * (k + 1))) as G1; pose proof (big1_range ((512 * k + 1024) * 1)) as G2; clear - BUDG G1 G2; lia
           | |- bv_unsigned _ <= B => rewrite unsigned_lit by (clear - SPR LO LO0; lia); unfold SP'; clear - SPB; lia
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); exact ST
           | |- lo <= _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); unf_stk; unfold SP'; clear - LO; lia
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR
           | |- _ => idtac
           end.
      }
    clear RA. intros [ms4 mo4] PO. unfold crealloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & errv3 & A' & junk3 & p' & s3 &
                    -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3 & XP3 & BR3 & HP3 & NEW3 & IM3 & GM3).
    rewrite (proj1 (HH_lb_remove H HH)) in XP3, HP3 by exact NIP.
    rewrite (unsigned_lit SP') in ST3, XP3 by (unfold SP'; lia). rewrite errno_RATP in ERR3.
    replace ((512 * k + 1024) * 1) with (512 * (k + 1 + 1)) in BR3, HP3, NEW3 by (clear - KR; lia).
    rewrite Z.min_l in NEW3 by (clear - KR; lia). rewrite firstn_firstn, Nat.min_id in NEW3.
    replace (512 * (k + 1 + 1) - 512 * (k + 1)) with 512 in NEW3 by (clear - KR; lia).
    apply (proj1 (rw_cells_app rsegs m3 _ [CB (Z.to_nat (512 * (k + 1))) (firstn (Z.to_nat (512 * (k + 1))) ds)] [CB (Z.to_nat 512) junk3])) in NEW3.
    destruct NEW3 as [PRE3 JK3]. cbn [cells_size csize Nat.add] in JK3.
    replace (A' + Z.of_nat (Z.to_nat (512 * (k + 1)) + 0)) with (A' + 512 * (k + 1)) in JK3 by (clear - KR; lia).
    apply rw_cells_bytes_at in PRE3. cbn [cells_bytes cbytes app] in PRE3. rewrite app_nil_r in PRE3.
    pose proof BR3 as (C1 & C2 & C3 & C4 & C5).
    replace (ret_pc (Z_to_bv 64 LD_R2)) with (Z_to_bv 64 LD_R2) by (symmetry; apply ret_pc_even; [unfold LD_R2; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (MBO3 : MEMBIO LB m3 mb R2).
    { eapply (MEMBIO_frame0 LB LB SP'); [exact MBO| | eapply xpres_weaken; [exact XP3| clear; lia| exact SUBLB| intros q Hq; exact Hq]].
      intros b Hb. rewrite (mb_static_blocks mb R R2 MST1) in Hb. unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in Hb.
      destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
    assert (DS3 : bytes_at rsegs m3 (mb_buf R) ds).
    { eapply xpres_bytes_at'; [exact XP3| exact DS| | apply Forall_nil]. right; right. exists (pD, mb_buf R, mb_len R). split; [exact (SUBLB _ PIN)| cbn; rewrite DSL; clear; lia]. }
    assert (RBc3 : rw_cells rsegs m3 RBP [C8 (wz 512)]).
    { eapply xpres_rw_cells'; [exact XP3| exact RBc| left; unfold RBP, SP'; cbn; clear; lia| apply Forall_nil]. }
    assert (ME3 : METH_mem m3).
    { unfold METH_mem in *. eapply xpres_rw_cells'; [exact XP3| exact ME| | apply Forall_nil].
      right; left. unfold A_mem_buf_method, O_METH_BREAD, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. clear. lia. }
    assert (XPm3 : xpres Lh SP' XW m0 m3).
    { eapply xpres_trans; [exact XP|]. eapply xpres_weaken; [exact XP3| clear; lia| intros b Hb; exact Hb| intros q Hq; destruct Hq]. }
    clear XP3 MBO DS RBc ME IM GM AUX ST MI XP ERR.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL3| eapply ld_seg3 with (K := 512 * k) (A' := A'); [reflexivity| clear - C1 C4 HCEILB KR; lia| clear - KR; lia| clear - C4 HCEILB KR; lia| exact MI3]|].
    intros ms5 ->.
    (* [comment removed for export] *)
    pose proof bioeof_mem_spec as EF. unfold bioeof_mem_stmt in EF.
    eapply (sr_evt_krel H HH); [exact KREL3| |].
    { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := R2); clear EF; try reflexivity.
      all: try first [exact MBO3| exact ME3| exact MI3| exact CEIL].
      all: lazymatch goal with
           | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST1| exact MBB]
           | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST1| exact MBS]
           | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); exact ST3
           | |- lo <= _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); unf_stk; unfold SP'; clear - LO; lia
           | |- _ mod 2 = 0 => unfold LD_R3; rewrite unsigned_lit by (clear; lia); reflexivity
           end. }
    intros ms6 PO. unfold memctrl_post in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & MBO4).
    rewrite (unsigned_lit SP') in MU4, ST4 by (unfold SP'; lia). rewrite RV.
    destruct (lad_head_facts _ _ _ _ _ HP3) as (_ & BH3 & _ & _ & _).
    eapply (KONT m4 mo4 s3 p' A'); clear KONT; [| exact KREL3| eapply (mpres_trans H HH); [exact MP| exact MP3]].
    unfold LAD. split; [| split; [exact MBO4| split; [exact MST1| split; [subst R2; cbn [mb_pos mb_after_read mb_advance]; rewrite POS; clear; lia| split; [clear - KL; lia|]]]]].
    - eapply (HH_RHEAP_frame H HH); [exact HP3| exact MU4| exact WM4|]. apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil].
    - split; [eapply bytes_at_transport; [exact DS3| exact MU4|]; rewrite DSL; clear - BUFH CEIL; cbn; lia|].
      split; [eapply bytes_at_transport; [exact PRE3| exact MU4|]; rewrite OBSL; clear - BH3 CEIL KR; cbn; lia|].
      split; [exists junk3; eapply rw_cells_transport; [exact JK3| exact MU4| exact WM4| clear - BH3 CEIL KR; cbn; lia]|].
      split; [exists 512; eapply rw_cells_transport; [exact RBc3| exact MU4| exact WM4| unfold RBP; clear; cbn; lia]|].
      split; [exists errv3; eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4| clear - CEIL HCEILB; img_static]|].
      split; [unfold METH_mem in *; eapply rw_cells_transport; [exact ME3| exact MU4| exact WM4| clear - CEIL HCEILB; img_static]|].
      split; [unfold IMPL_mem in *; eapply rw_cells_transport; [exact IM3| exact MU4| exact WM4| clear - CEIL HCEILB; img_static]|].
      split; [unfold GOT_mem in *; eapply rw_cells_transport; [exact GM3| exact MU4| exact WM4| clear - CEIL HCEILB; img_static]|].
      split; [exact MI4|]. split; [exact ST4|].
      split; [eapply (HH_rauxv_frame H HH); [exact AUX3| exact MU4| exact WM4|]; unfold RAUXV_CELL; clear - SPB CEIL HCEILB LO; apply Forall_cons; [cbn; lia| apply Forall_nil]|].
      eapply xpres_trans; [exact XPm3|]. eapply xpres_of_munch; [exact MU4| exact WM4| | exact BEL]. apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil].
  Qed.
  (* [comment removed for export] *)
  Lemma lad_loop : forall (fuel : nat) (k : Z) m mo s p A R' (s7v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Q : config -> Prop),
    Z.of_nat fuel = 32 - k -> 0 <= k <= 31 ->
    LAD k m s p A R' -> hs_KREL H s mo -> hs_MPRES H mo0 mo ->
    lad_doneK Q -> lad_capK Q ->
    hs_SR H Q (mkCfg (lad_entry k m A s7v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6) mo).
  Proof.
    induction fuel as [|fuel IH]; intros k m mo s p A R' s7v t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Q FUEL KR INV KREL MP KD KC; [exfalso; clear - FUEL KR; lia|].
    pose proof INV as (HP0 & _ & MST & POS & KL & _).
    eapply lad_read; [exact KR| exact INV| exact KREL|].
    intros m2 R2 n junk' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 NEQ R2EQ HP MBO DS PRE OUT RBc ERR ME IM GM MI ST AUX XP. subst R2.
    destruct (Z_le_gt_dec (mb_len R) (512 * k + 512)) as [LAST|MORE].
    - (* [comment removed for export] *)
      assert (NE : n = mb_len R - 512 * k) by (rewrite NEQ; clear - LAST KL; lia).
      eapply lad_done; try eassumption. clear - LAST KL NE; lia.
    - (* [comment removed for export] *)
      assert (NE : n = 512) by (rewrite NEQ; clear - MORE; lia). clear NEQ. subst n.
      eapply lad_grow; try eassumption; [reflexivity| clear - MORE; lia|].
      intros m4 mo4 s4 p' A' v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 INV4 KREL4 MP4.
      pose proof INV4 as (HP4 & MBO4 & MST4 & POS4 & KL4 & DS4 & PRE4 & [junk4 JK4] & RB4 & ERR4 & ME4 & IM4 & GM4 & MI4 & ST4 & AUX4 & XP4).
      hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST4 as [? _]; assumption). unf_stk_in LO.
      destruct (lad_head_facts _ _ _ _ _ HP4) as (_ & _ & _ & _ & BEL).
      replace (ret_pc (Z_to_bv 64 LD_R3)) with (Z_to_bv 64 LD_R3) by (symmetry; apply ret_pc_even; [unfold LD_R3; lia| reflexivity]).
      destruct (Z.eq_dec k 31) as [CAP|NCAP].
      + (* [comment removed for export] *)
        rewrite CAP. change (32 - 31) with 1.
        eapply (sr_evt_krel H HH); [exact KREL4| eapply ld_seg4_cap; [reflexivity| exact MI4]|]. intros ms5 ->.
        pose proof bioeof_mem_spec as EF. unfold bioeof_mem_stmt in EF.
        eapply (sr_evt_krel H HH); [exact KREL4| |].
        { eapply EF with (lo := lo) (LB := LB) (a := mb) (R := mb_after_read R' 512); clear EF; try reflexivity.
          all: try first [exact MBO4| exact ME4| exact MI4| exact CEIL].
          all: lazymatch goal with
               | |- MEMBIO_below _ _ _ => eapply mb_static_below; [exact MST4| exact MBB]
               | |- MEMBIO_sep _ _ => eapply mb_static_sep; [exact MST4| exact MBS]
               | |- stk _ _ _ _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); exact ST4
               | |- lo <= _ => rewrite unsigned_lit by (clear - SPR LO LO0; lia); unf_stk; unfold SP'; clear - LO; lia
               | |- _ mod 2 = 0 => unfold LD_RC; rewrite unsigned_lit by (clear; lia); reflexivity
               end. }
        intros ms6 PO. unfold memctrl_post in PO.
        destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & MBO5).
        rewrite (unsigned_lit SP') in MU5, ST5 by (unfold SP'; lia).
        pose proof MBO4 as MB0. destruct MB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BUFP & BUFH & _).
        cbn [mb_buf mb_len mb_after_read mb_advance] in BUFH. destruct MST as (S1 & S2 & _). rewrite S1, S2 in BUFH. unfold zlength in DSL.
        destruct (lad_head_facts _ _ _ _ _ HP4) as (_ & BH4 & _ & _ & _).
        unfold lad_capK in KC. rewrite CAP in HP4, KL4, POS4. change (512 * (31 + 1 + 1)) with (512 * 33) in HP4.
        eapply (KC m5 mo4 s4 p' A' _ (mb_after_read R' 512)); clear KC KD IH.
        all: try first [exact KREL4| exact MP4| exact MBO5| exact MST4| exact MI5| exact ST5].
        * eapply (HH_RHEAP_frame H HH); [exact HP4| exact MU5| exact WM5|]. apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil].
        * cbn [mb_pos mb_after_read mb_advance]. rewrite POS, CAP. reflexivity.
        * clear - KL4; lia.
        * eapply bytes_at_transport; [exact DS4| exact MU5|]. rewrite DSL. clear - BUFH CEIL; cbn; lia.
        * destruct RB4 as [rb RB]. exists rb. eapply rw_cells_transport; [exact RB| exact MU5| exact WM5| unfold RBP; clear; cbn; lia].
        * destruct ERR4 as [errv ERR5]. exists errv. eapply rw_cells_transport; [exact ERR5| exact MU5| exact WM5| clear - CEIL HCEILB; img_static].
        * unfold METH_mem in *; eapply rw_cells_transport; [exact ME4| exact MU5| exact WM5| clear - CEIL HCEILB; img_static].
        * unfold IMPL_mem in *; eapply rw_cells_transport; [exact IM4| exact MU5| exact WM5| clear - CEIL HCEILB; img_static].
        * unfold GOT_mem in *; eapply rw_cells_transport; [exact GM4| exact MU5| exact WM5| clear - CEIL HCEILB; img_static].
        * eapply (HH_rauxv_frame H HH); [exact AUX4| exact MU5| exact WM5|]. unfold RAUXV_CELL. clear - SPB CEIL HCEILB LO; apply Forall_cons; [cbn; lia| apply Forall_nil].
        * eapply xpres_trans; [exact XP4|]. eapply xpres_of_munch; [exact MU5| exact WM5| | exact BEL]. apply Forall_cons; [left; cbn; clear - CEIL; lia| apply Forall_nil].
      + (* [comment removed for export] *)
        eapply (sr_evt_krel H HH); [exact KREL4| eapply ld_seg4 with (c := 32 - k); [reflexivity| clear - KR NCAP; lia| unf_stk; clear - LO LO0; lia| exact MI4]|].
        intros ms5 ->.
        replace (32 - k - 1) with (32 - (k + 1)) by (clear; lia).
        replace (A' + 512 * k + 512) with (A' + 512 * (k + 1)) by (clear; lia).
        replace (512 * k + 512) with (512 * (k + 1)) by (clear; lia).
        replace (Z_to_bv 64 (bv_unsigned sp + -2240)) with (Z_to_bv 64 RBP) by reflexivity.
        eapply (IH (k + 1)); [clear - FUEL; lia| clear - KR NCAP; lia| exact INV4| exact KREL4| exact MP4| exact KD| exact KC].
  Qed.
End W.
