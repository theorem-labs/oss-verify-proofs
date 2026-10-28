(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocCover AllocDcv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import S2B2BStmt U.S0B2BDStmt U.S0TRInv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac GlueAlloc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTablesB2B. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0_glueE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_glueE S0F_glueDefs.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_split : forall m A cs1 cs2,
  rw_cells s0segs m A (cs1 ++ cs2) -> rw_cells s0segs m A cs1 /\ rw_cells s0segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[WF BA] WR].
  apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in BA. apply (proj1 (bytes_at_app _ _ _ _ _)) in BA. destruct BA as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in WR. cps_destruct WR as (A1 & A2 & WW).
  split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]); intros i Hi.
  - apply WW. lia.
  - replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply WW. lia.
Qed.

Lemma bytes_at_func : forall m A l1 l2, bytes_at s0segs m A l1 -> bytes_at s0segs m A l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  (intros m A l1 l2; cps_intros (_ & _ & H1); cps_intros (_ & _ & H2); intros L). apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- H1, <- H2 by lia. reflexivity.
  - rewrite !(proj2 (nth_error_None _ _)) by lia. reflexivity.
Qed.

Lemma outside_Forall : forall (l : list (Z * Z)) a, Forall (fun iv => ~ (fst iv <= a < snd iv)) l -> outside l a.
Proof.
  induction l as [|[lo' hi'] l IH]; intros a H; cbn; [exact I|].
  apply Forall_cons_iff in H as [H1 H2]. cbn in H1. split; [lia| apply IH; exact H2].
Qed.

Lemma le8_inj : forall a b : word, le8 a = le8 b -> a = b.
Proof. intros a b E. rewrite <- (le_bytes_to_word_le8 a), <- (le_bytes_to_word_le8 b), E. reflexivity. Qed.

Lemma app8_split : forall (a b : word) (r1 r2 : list byte), le8 a ++ r1 = le8 b ++ r2 -> a = b /\ r1 = r2.
Proof.
  intros a b r1 r2 E.
  pose proof (f_equal (firstn 8) E) as E1. rewrite !firstn_app, !length_le8, !Nat.sub_diag, !firstn_O, !app_nil_r in E1.
  rewrite !firstn_all2 in E1 by (rewrite length_le8; lia).
  pose proof (f_equal (skipn 8) E) as E2. rewrite !skipn_app, !length_le8, !Nat.sub_diag in E2.
  rewrite !skipn_all2 in E2 by (rewrite length_le8; lia). cbn [skipn app] in E2.
  split; [apply le8_inj; exact E1| exact E2].
Qed.

(* [comment removed for export] *)
Lemma strm_tail_agree : forall W m m' A b b',
  rw_cells s0segs m A (STRM_CELLS b) -> munch W m m' -> wmono s0segs m m' -> (forall x, A + 56 <= x < A + 80 -> outside W x) ->
  rw_cells s0segs m' A (STRM_CELLS b') ->
  bs_bzalloc b' = bs_bzalloc b /\ bs_bzfree b' = bs_bzfree b /\ bs_opaque b' = bs_opaque b.
Proof.
  intros W m m' A b b' H MU WM D H'.
  pose proof (proj1 (proj1 H)) as WF. cbn in WF. pose proof (proj1 (proj1 H')) as WF'. cbn in WF'.
  change (rw_cells s0segs m A ([C8 (Z_to_bv 64 (bs_src b + (bs_len b - bs_ai b))); C4 (Z_to_bv 64 (bs_ai b)); C4 (bs_til b); C4 (bs_tih b); CB 4 (bs_q1 b);
     C8 (Z_to_bv 64 (bs_dst b + (bs_dlen b - bs_av b))); C4 (Z_to_bv 64 (bs_av b)); C4 (bs_tol b); C4 (bs_toh b); CB 4 (bs_q2 b);
     C8 (Z_to_bv 64 (bs_S b))] ++ [C8 (bs_bzalloc b); C8 (bs_bzfree b); C8 (bs_opaque b)])) in H.
  apply rw_cells_split in H. destruct H as [_ H]. cbn [cells_size csize Nat.add] in H.
  change (rw_cells s0segs m' A ([C8 (Z_to_bv 64 (bs_src b' + (bs_len b' - bs_ai b'))); C4 (Z_to_bv 64 (bs_ai b')); C4 (bs_til b'); C4 (bs_tih b'); CB 4 (bs_q1 b');
     C8 (Z_to_bv 64 (bs_dst b' + (bs_dlen b' - bs_av b'))); C4 (Z_to_bv 64 (bs_av b')); C4 (bs_tol b'); C4 (bs_toh b'); CB 4 (bs_q2 b');
     C8 (Z_to_bv 64 (bs_S b'))] ++ [C8 (bs_bzalloc b'); C8 (bs_bzfree b'); C8 (bs_opaque b')])) in H'.
  apply rw_cells_split in H'. destruct H' as [_ H']. cbn [cells_size csize Nat.add] in H'.
  apply (pres_rw_cells (outside W) m m') in H; [| apply pres_of_munch; assumption | cbn; intros x Hx; apply D; lia].
  pose proof (proj2 (proj1 H)) as B1. pose proof (proj2 (proj1 H')) as B2. cbn [cells_bytes cbytes app] in B1, B2.
  rewrite app_nil_r in B1, B2.
  pose proof (bytes_at_func _ _ _ _ B2 B1 ltac:(rewrite !app_length, !length_le8; reflexivity)) as E.
  apply app8_split in E as [E1 E]. apply app8_split in E as [E2 E]. apply app8_split in E as [E3 _].
  split; [exact E1|]. split; [exact E2| exact E3].
Qed.

(* [comment removed for export] *)
Lemma cwo_block : forall LBx b l h, In b LBx -> blk_addr b <= l -> h <= blk_addr b + blk_size b -> client_write_ok S0_layout LBx (l, h).
Proof. intros. right; right. exists b. cbn. auto. Qed.



Section Tail.
  Context (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI).
  Hypothesis FREEV : alloc_freev_law s0segs S0_layout AI AC.
  Let L := S0_layout.

  (* [comment removed for export] *)
  Variables (lo B dst dn dl src len small : Z) (srcZ : list Z) (db : list byte) (kcr : nat) (LB : list ablock) (pD : bid)
            (g1 sv ra0 spw gp tp s0e s1e s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : word -> option byte) (MD0 : Model) (K : TSet).
  Local Notation usp := (bv_unsigned spw).
  Hypothesis TP : tp = Z_to_bv 64 (al_tp L).
  Hypothesis GEOM : alloc_ceiling <= lo /\ lo <= usp - 16384 /\ usp mod 16 = 0 /\ usp + 48 <= 2 ^ 47 /\ usp <= B.
  Hypothesis DSTF : In (pD, dst, dn) LB /\ 0 <= len < 2 ^ 27 /\ 0 <= dn < 2 ^ 27.
  Hypothesis DLF : usp <= dl /\ dl + 4 <= 2 ^ 64 /\ dl mod 4 = 0 /\ dl + 4 <= B.
  Hypothesis BLKS : forall b, In b LB -> block_ok L (blk_addr b) (blk_size b).
  Hypothesis HK : forall ms' MD',
    b2bD_post AI AC S0DI ra0 spw gp tp s0e s1e s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 F fc LB m0 MD0 dst dn dl srcZ small lo B g1 sv kcr ms' MD' ->
    realizes s0segs (mkCfg ms' MD') K.

  (* [comment removed for export] *)
  Definition Pcl (a : Z) : Prop := client_addr L LB usp a /\ ~ b2bD_out dst dn dl a.

  Lemma geom_facts : alloc_ceiling <= lo /\ lo <= usp - 16384 /\ usp + 48 <= 2 ^ 47 /\ usp <= B /\
                     0 < dst /\ dst + dn <= alloc_ceiling /\ (dst + dn <= 0x10000 \/ 0x66000 <= dst) /\ 0 <= dn.
  Proof.
    pose proof GEOM as G. bz_ceil. cps_destruct DSTF as (IN & LEN & DN).
    cps_pose (BLKS _ IN) as (B1 & B2 & B3 & B4 & B5). cbn [blk_addr blk_size fst snd] in *.
    bz_ceil. unfold L, S0_layout in B5; cbn [al_img_lo al_img_hi] in B5. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma Pcl_outside : forall W a, Forall (fun iv => lo <= fst iv /\ snd iv <= usp) W -> 0 <= a < 2 ^ 64 -> Pcl a -> outside W a.
  Proof.
    intros W a HW Ha [CA _]. pose proof geom_facts as G.
    assert (R : ~ (lo <= a < usp)).
    { destruct CA as [C|[C|(b & Hb & Hr)]]; [lia| |].
      - unfold L, S0_layout in C; cbn [al_rw_lo al_img_hi] in C. lia.
      - cps_pose (BLKS _ Hb) as (_ & _ & _ & B4 & _). bz_ceil. lia. }
    induction W as [|[l h] W IH]; cbn; [exact I|]. apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2.
    split; [lia| apply IH; exact HW].
  Qed.

  Lemma pres_munch_Pcl : forall W m m', munch W m m' -> wmono s0segs m m' ->
    Forall (fun iv => lo <= fst iv /\ snd iv <= usp) W -> pres Pcl m m'.
  Proof.
    intros W m m' MU WM HW. eapply pres_mono; [| apply pres_of_munch; [exact MU| exact WM]].
    intros a Ha HP. apply Pcl_outside; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma pres_heap_Pcl : forall LBx SP m m', heap_pres s0segs L LBx SP m m' -> SP <= usp ->
    (forall b, In b LB -> In b LBx) -> pres Pcl m m'.
  Proof.
    clear TP GEOM DSTF DLF BLKS HK.   (* [comment removed for export] *)
    intros LBx SP m m' HP HS HL. eapply pres_mono; [| apply pres_of_heap_pres; exact HP].
    intros a Ha [CA _]. destruct CA as [C|[C|(b & Hb & Hr)]]; [left; lia| right; left; exact C| right; right].
    exists b. split; [apply HL; exact Hb| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Definition TM (m : word -> option byte) (b : bzs) (h : dsh) (d : dsm) (dlv : Z) (j8 : list byte) (raE : Z) (xs0 xs1 : word) : Prop :=
    rw_cells s0segs m (usp + -128) (STRM_CELLS b) /\
    rw_cells s0segs m (usp + -48) (SAVES s4e s3e s2e s1e s0e ra0) /\
    rw_cells s0segs m (usp + -160) [CB 8 j8; C8 xs1; C8 xs0; C8 (Z_to_bv 64 raE)] /\
    rw_cells s0segs m (bs_S b) (HEAD_CELLS h) /\ rw_cells s0segs m (bs_S b + 3152) (MID_CELLS d) /\
    rw_cells s0segs m dl [C4 (Z_to_bv 64 dlv)] /\ rw_cells s0segs m dst [CB (Z.to_nat dn) db] /\
    rw_cells s0segs m 0x33178 [CB CRC_BYTES crc_table_bytes] /\ rw_cells s0segs m 0x335b0 [CB RNUMS_BYTES rnums_table_bytes] /\
    b2bD_got s0segs S0DI m g1 sv.

  (* [comment removed for export] *)
  Lemma TM_pres : forall (Q : Z -> Prop) m m' b h d dlv j8 raE xs0 xs1,
    pres Q m m' -> bzs_wf b ->
    (forall a, usp - 160 <= a < usp -> Q a) ->
    (forall a, bs_S b <= a < bs_S b + 64144 -> Q a) ->
    (forall a, dl <= a < dl + 4 -> Q a) -> (forall a, dst <= a < dst + dn -> Q a) ->
    (forall a, 0x32000 <= a < 0x440f0 -> Q a) ->
    TM m b h d dlv j8 raE xs0 xs1 -> TM m' b h d dlv j8 raE xs0 xs1.
  Proof.
    (intros Q m m' b h d dlv j8 raE xs0 xs1 PR BWF QF QS QD QB QI; cps_intros (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & [G1 G2])).
    pose proof geom_facts as G. cps_destruct BWF as (Q1 & Q2 & AIr & AVr & LENr & DLENr).
    pose proof (proj1 (proj1 (proj1 T4))) as HWF. cbn in HWF. (* [comment removed for export] *)
    unfold b2bD_got in *. cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI] in *.
    Ltac tmp PR T Q := eapply pres_rw_cells; [exact PR | exact T | unfold SAVES, CRC_BYTES, RNUMS_BYTES; cbn [cells_size csize Nat.add length bd_got bd_stderrp bd_crc bd_rnums S0DI]; intros a Ha; apply Q; lia].
    split; [tmp PR T1 QF|]. split; [unfold SAVES in *; tmp PR T2 QF|]. split; [tmp PR T3 QF|].
    split. { eapply pres_rw_cells; [exact PR | exact T4 |]. cbn [cells_size csize Nat.add length]. intros a Ha; apply QS; lia. }
    split; [tmp PR T5 QS|]. split; [tmp PR T6 QD|].
    split. { eapply pres_rw_cells; [exact PR | exact T7 |]. cbn [cells_size csize Nat.add]. intros a Ha; apply QB; lia. }
    split; [tmp PR T8 QI|]. split; [tmp PR T9 QI|]. split; [tmp PR G1 QI| tmp PR G2 QI].
  Qed.

  Lemma cwo_stack : forall LBx l h, alloc_ceiling <= l -> client_write_ok L LBx (l, h).
  Proof. intros. left. cbn. assumption. Qed.
  (* [comment removed for export] *)
  Ltac aux_fp := repeat (apply Forall_cons; [cbn [fst snd al_static S0_layout]; split; [lia | unfold S0_static; intros; lia] |]); apply Forall_nil.

  Lemma b2b_pres_of_Pcl : forall m', pres Pcl m0 m' -> b2bD_pres s0segs L LB usp dst dn dl m0 m'.
  Proof. intros m' PR a Ha C O. exact (PR a Ha (conj C O)). Qed.

  Lemma crange_img : forall LBx SP A n, 0x32000 <= A -> A + n <= 0x440f0 -> client_range L LBx SP A n.
  Proof.
    intros LBx SP A n H1 H2. right; left. unfold L, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp].
    split; [lia|]. split; [lia|]. split; [intros; lia| lia].
  Qed.

  Lemma img_client : forall LBx SP a, 0x32000 <= a < 0x440f0 -> client_addr L LBx SP a.
  Proof.
    intros LBx SP a Ha. right; left. unfold L, S0_layout, errno_cell, S0_private; cbn [al_rw_lo al_img_hi al_private al_tp]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition rcF (raE : Z) (xs0 xs1 a0 : word) : Prop :=
    (raE = 0x1600c -> a0 = Z_to_bv 64 0) /\ (raE = 0x16034 -> a0 = xs1) /\
    (raE = 0x16024 -> xs0 = Z_to_bv 64 0 -> a0 = Z_to_bv 64 (-7)) /\ (raE = 0x16024 -> xs0 = Z_to_bv 64 1 -> a0 = Z_to_bv 64 (-8)).
  Definition RESF (raE : Z) (xs0 xs1 : word) (dlv : Z) : Prop :=
    forall (m' : word -> option byte) (a0 : word),
      rw_cells s0segs m' dst [CB (Z.to_nat dn) db] -> rcF raE xs0 xs1 a0 ->
      exists rc, a0 = Z_to_bv 64 rc /\ b2bD_result s0segs rc dst dn srcZ small m' dlv.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fin_cps : forall (m : word -> option byte) (MD : Model) (s : ai_AS AI) (pS : bid) (S : Z) (b : bzs) (h : dsh) (d : dsm)
      (dlv : Z) (j8 : list byte) (raE raR : Z) (xs0 xs1 errv : word)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ai_inv AI s ((pS, S, 64144) :: LB) m MD -> ac_vm AC kcr s MD -> ~ In pS (map blk_id LB) ->
    vm_only MD0 MD -> ai_aux AI m B -> rw_cells s0segs m (errno_cell L) [C4 errv] -> mem_inv s0segs m ->
    stk s0segs m lo (usp + -160) ->
    TM m b h d dlv j8 raE xs0 xs1 -> bzs_wf b -> bs_S b = S -> bs_bzfree b = Z_to_bv 64 0x13e3c -> bs_opaque b = Z_to_bv 64 0 ->
    (raE = 0x1600c \/ raE = 0x16024 \/ raE = 0x16034) -> 0 <= dlv <= dn ->
    (raE = 0x16024 -> xs0 = Z_to_bv 64 0 \/ xs0 = Z_to_bv 64 1) -> RESF raE xs0 xs1 dlv ->
    pres Pcl m0 m ->
    realizes s0segs (mkCfg (inEnd 0x15dec raR spw gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src)
                                  s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m) MD) K.
  Proof.
    intros until t6. intros INV VMC NIP VMO AUX ERR MI ST TMm BWF BS BF BO RAE DLV X01 RES PR.
    pose proof geom_facts as G. pose proof (u64_range spw) as Uspw.
    destruct (ai_inv_model AI INV) as [Hh Hl].
    cps_pose (ai_inv_blocks AI (b := (pS, S, 64144)) INV ltac:(left; reflexivity)) as (S1 & S2 & S3 & S4 & S5).
    cbn [blk_addr blk_size fst snd] in S1, S2, S3, S4, S5. bz_ceil.
    cps_destruct TMm as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & GOT).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs (fun ms => exists a2', ms = inEnd 0x293c4 0x15dfc spw gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 S) a2' a3 a4 a5 a6 a7
                                   (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m));
      [exact Hh | exact Hl | |].
    { eapply glueE5; [exact T1 | exact BS | exact BF | exact BO | lia | exact MI |].
      intros a2'. apply evt_done. exists a2'. reflexivity. }
    intros ms' [a2' ->]. unfold inEnd.
    (* [comment removed for export] *)
    eapply FREEV with (s := s) (LB := (pS, S, 64144) :: LB) (k := kcr) (p := pS) (A := S) (n := 64144) (lo := lo) (B := B) (errv := errv);
      rewrite ?unsigned_lit by lia;
      [exact INV | exact VMC | left; reflexivity | exact AUX | lia | exact ST | lia | cbn [al_stack L S0_layout]; lia | exact ERR | exact MI
      | exact TP | reflexivity |].
    intros s' m' MD' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 INV' VMO' VMC' MI' ST' ERR' AUX' HP.
    rewrite ?unsigned_lit in HP by lia. rewrite (lb_remove_head pS S 64144 LB NIP) in INV', HP.
    rewrite ret_pc_lit by (lia || reflexivity).
    destruct (ai_inv_model AI INV') as [Hh' Hl'].
    pose proof (pres_heap_Pcl _ _ _ _ HP ltac:(lia) ltac:(auto)) as PR1.
    assert (C1 : rw_cells s0segs m' (usp + -128) (STRM_CELLS b)).
    { eapply heap_pres_rw_cells; [exact HP | exact T1 | left; cbn; lia]. }
    assert (C3 : rw_cells s0segs m' (usp + -160) [CB 8 j8; C8 xs1; C8 xs0; C8 (Z_to_bv 64 raE)]).
    { eapply heap_pres_rw_cells; [exact HP | exact T3 | left; cbn; lia]. }
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs); [exact Hh' | exact Hl' | |].
    { eapply (glueE6 raE _ spw) with (lo := lo); [exact C1 | exact C3 | exact ST' | lia | lia | exact MI' | lia | destruct RAE as [->|[->| ->]]; reflexivity |].
      intros m'' C1' ST'' MU WM MI''. apply evt_done.
      (* [comment removed for export] *)
      instantiate (1 := fun ms => exists m'', ms = MS (mkR (Z_to_bv 64 raE) (Z_to_bv 64 (usp + -128)) gp tp y0 y1 y2 xs0 xs1 (Z_to_bv 64 0) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                          (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6) F (Z_to_bv 64 raE) fc None m'' (seg_rom s0segs)
                       /\ munch [(usp + -160, usp + -128); (usp + -80, usp + -72)] m' m'' /\ wmono s0segs m' m'' /\ mem_inv s0segs m''
                       /\ stk s0segs m'' lo (usp + -128)
                       /\ rw_cells s0segs m'' (usp + -128) (STRM_CELLS (BZS (bs_src b) (bs_len b) (bs_ai b) (bs_til b) (bs_tih b) (bs_q1 b) (bs_dst b) (bs_dlen b) (bs_av b)
                                  (bs_tol b) (bs_toh b) (bs_q2 b) 0 (bs_bzalloc b) (bs_bzfree b) (bs_opaque b)))).
      exists m''. repeat (split; [first [reflexivity | assumption]|]). exact C1'. }
    (intros ms2; cps_intros (m'' & -> & MU & WM & MI'' & ST'' & C1'')).
    (* [comment removed for export] *)
    assert (C2 : rw_cells s0segs m'' (usp + -48) (SAVES s4e s3e s2e s1e s0e ra0)).
    { eapply rw_cells_transport; [ | exact MU | exact WM | unfold SAVES; cbn; lia].
      eapply heap_pres_rw_cells; [exact HP | exact T2 | left; unfold SAVES; cbn; lia]. }
    eapply (evt_realizes s0segs); [exact Hh' | exact Hl' | |].
    { eapply (glueTF raE spw) with (lo := lo); [exact RAE | exact X01 | exact C1'' | exact C2 | exact ST'' | lia | lia | exact MI'']. }
    (intros ms3; cps_intros (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & -> & ST3 & RC3)).
    (* [comment removed for export] *)
    assert (T7' : rw_cells s0segs m'' dst [CB (Z.to_nat dn) db]).
    { eapply rw_cells_transport; [ | exact MU | exact WM | cbn; lia].
      eapply heap_pres_rw_cells; [exact HP | exact T7 | right; right; exists (pD, dst, dn); split; [exact (proj1 DSTF)| cbn; lia]]. }
    cps_destruct (RES m'' za0 T7' RC3) as (rc & Erc & RESm).
    apply HK. unfold b2bD_post.
    exists z0, z1, z2, za0, za1, za2, za3, za4, za5, za6, za7, z3, z4, z5, z6, errv, m'', s', rc, dlv.
    split; [reflexivity|].
    split; [exact Erc|].
    split. { eapply (ai_inv_frame AI); [exact INV' | exact MU | exact WM |]. apply Forall_cons; [apply cwo_stack; lia|]. apply Forall_cons; [apply cwo_stack; lia| apply Forall_nil]. }
    split; [exact VMC'|].
    split; [eapply vm_only_trans; [exact VMO | exact VMO']|].
    split; [exact MI''|].
    split; [exact ST3|].
    split. { eapply rw_cells_transport; [exact ERR' | exact MU | exact WM | unfold errno_cell, L, S0_layout; cbn; lia]. }
    split. { eapply (ai_aux_frame AI); [exact AUX' | exact MU | exact WM | aux_fp]. }
    split. { apply b2b_pres_of_Pcl. eapply pres_trans; [exact PR|]. eapply pres_trans; [exact PR1|].
             eapply pres_munch_Pcl; [exact MU | exact WM |]. repeat constructor; cbn; lia. }
    split. { eapply rw_cells_transport; [ | exact MU | exact WM | cbn; lia]. eapply heap_pres_rw_cells; [exact HP | exact T6 | left; cbn; lia]. }
    split; [exact DLV|].
    split. { unfold b2bD_tabs. cbn [bd_crc bd_rnums S0DI]. split.
             - eapply rw_cells_transport; [ | exact MU | exact WM | unfold CRC_BYTES; cbn; lia].
               eapply heap_pres_rw_cells; [exact HP | | apply crange_img; unfold CRC_BYTES; cbn; lia].
               unfold CRC_BYTES in T8. rewrite <- bz_crc_table_bytes_eq in T8. exact T8.
             - eapply rw_cells_transport; [ | exact MU | exact WM | unfold RNUMS_BYTES; cbn; lia].
               eapply heap_pres_rw_cells; [exact HP | | apply crange_img; unfold RNUMS_BYTES; cbn; lia].
               unfold RNUMS_BYTES in T9. rewrite <- bz_rnums_table_bytes_eq in T9. exact T9. }
    split.
    { destruct GOT as [GO1 GO2]. unfold b2bD_got in *. cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI] in *. split.
      - eapply rw_cells_transport; [ | exact MU | exact WM | cbn; lia].
        eapply heap_pres_rw_cells; [exact HP | exact GO1 | apply crange_img; cbn; lia].
      - eapply rw_cells_transport; [ | exact MU | exact WM | cbn; lia].
        eapply heap_pres_rw_cells; [exact HP | exact GO2 | apply crange_img; cbn; lia]. }
    exact RESm.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma free_mid : forall (site next : Z) (m : word -> option byte) (MD : Model) (s : ai_AS AI) (LBc : list ablock)
      (pS : bid) (S : Z) (pX : bid) (X nX : Z) (b : bzs) (h : dsh) (d : dsm) (dlv : Z) (j8 : list byte) (raE : Z) (xs0 xs1 errv : word)
      (raX : Z) (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ((site = 0x15db4 /\ next = 0x15dc4) \/ (site = 0x15dc8 /\ next = 0x15dd8) \/ (site = 0x15ddc /\ next = 0x15dec)) ->
    ai_inv AI s LBc m MD -> ac_vm AC kcr s MD -> In (pX, X, nX) LBc ->
    In (pS, S, 64144) (lb_remove pX LBc) -> (forall b0, In b0 LB -> In b0 (lb_remove pX LBc)) ->
    vm_only MD0 MD -> ai_aux AI m B -> rw_cells s0segs m (errno_cell L) [C4 errv] -> mem_inv s0segs m ->
    stk s0segs m lo (usp + -160) ->
    TM m b h d dlv j8 raE xs0 xs1 -> bzs_wf b -> bs_S b = S -> bs_bzfree b = Z_to_bv 64 0x13e3c -> bs_opaque b = Z_to_bv 64 0 ->
    pres Pcl m0 m ->
    (forall (m' : word -> option byte) (MD' : Model) (s' : ai_AS AI) (y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
        ai_inv AI s' (lb_remove pX LBc) m' MD' -> ac_vm AC kcr s' MD' -> vm_only MD0 MD' -> ai_aux AI m' B -> rw_cells s0segs m' (errno_cell L) [C4 errv] ->
        mem_inv s0segs m' -> stk s0segs m' lo (usp + -160) -> TM m' b h d dlv j8 raE xs0 xs1 -> pres Pcl m0 m' ->
        realizes s0segs (mkCfg (inEnd next next spw gp tp y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src)
                                      s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 S F fc m') MD') K) ->
    realizes s0segs (mkCfg (inEnd site raX spw gp tp t0 t1 t2 a0 (Z_to_bv 64 X) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src)
                                  s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m) MD) K.
  Proof.
    intros until t6. intros SITE INV VMC INX INS INLB VMO AUX ERR MI ST TMm BWF BS BF BO PR HKf.
    pose proof geom_facts as G. pose proof (u64_range spw) as Uspw.
    destruct (ai_inv_model AI INV) as [Hh Hl].
    cps_pose (ai_inv_blocks AI (b := (pX, X, nX)) INV INX) as (X1 & X2 & X3 & X4 & X5).
    cbn [blk_addr blk_size fst snd] in X1, X2, X3, X4, X5. bz_ceil.
    pose proof TMm as (T1 & _).
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs (fun ms => exists a2', ms = inEnd 0x293c4 next spw gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 X) a2' a3 a4 a5 a6 a7
                                   (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m));
      [exact Hh | exact Hl | |].
    { unfold inEnd. eapply (glueE_free site next); [exact SITE | exact T1 | exact BF | exact BO | lia | exact MI |].
      intros a2'. apply evt_done. exists a2'. reflexivity. }
    intros ms' [a2' ->]. unfold inEnd.
    (* [comment removed for export] *)
    eapply FREEV with (s := s) (LB := LBc) (k := kcr) (p := pX) (A := X) (n := nX) (lo := lo) (B := B) (errv := errv);
      rewrite ?unsigned_lit by lia;
      [exact INV | exact VMC | exact INX | exact AUX | lia | exact ST | lia | cbn [al_stack L S0_layout]; lia | exact ERR | exact MI
      | exact TP | reflexivity |].
    intros s' m' MD' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 INV' VMO' VMC' MI' ST' ERR' AUX' HP.
    rewrite ?unsigned_lit in ST' by lia. rewrite ?unsigned_lit in HP by lia.
    assert (NX : 0 <= next < 2 ^ 64 /\ next mod 2 = 0) by (destruct SITE as [[_ ->]|[[_ ->]|[_ ->]]]; (split; [lia| reflexivity])).
    rewrite ret_pc_lit by (exact (proj1 NX) || exact (proj2 NX)).
    apply HKf with (s' := s'); try assumption.
    - eapply vm_only_trans; [exact VMO | exact VMO'].
    - eapply (TM_pres (client_addr L (lb_remove pX LBc) (usp - 160))); [apply pres_of_heap_pres; exact HP | exact BWF | | | | | | exact TMm].
      + intros a Ha. left. lia.
      + intros a Ha. right; right. exists (pS, S, 64144). split; [exact INS| cbn; lia].
      + intros a Ha. left. lia.
      + intros a Ha. right; right. exists (pD, dst, dn). split; [apply INLB; exact (proj1 DSTF)| cbn; lia].
      + intros a Ha. apply img_client. exact Ha.
    - eapply pres_trans; [exact PR|]. eapply pres_heap_Pcl; [exact HP | lia | exact INLB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma skips_e4 : forall (ra : Z) (m : word -> option byte) (d : dsm) (S : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) Q,
    rw_cells s0segs m (S + 3152) (MID_CELLS d) -> sm_ll16 d = 0 -> sm_ll4 d = 0 -> 0 < S -> S + 64144 < 2 ^ 64 -> mem_inv s0segs m ->
    evt s0segs Q (inEnd 0x15dec ra spw gp tp t0 t1 t2 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m) ->
    evt s0segs Q (inEnd 0x15dc4 ra spw gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m).
  Proof.
    intros until Q. intros MIDc L16 L4 S0 SHI MI HQ.
    apply (glueE_load 0x15dc4) with (d := d); [left; reflexivity | exact MIDc | exact S0 | exact SHI | exact MI |]. cbn [Z.eqb Pos.eqb]. rewrite L16.
    apply (glueE_skip 0x15dc8 0x15dd8); [right; left; split; reflexivity | exact MI |].
    apply (glueE_load 0x15dd8) with (d := d); [right; reflexivity | exact MIDc | exact S0 | exact SHI | exact MI |]. cbn [Z.eqb Pos.eqb]. rewrite L4.
    apply (glueE_skip 0x15ddc 0x15dec); [right; right; split; reflexivity | exact MI |]. exact HQ.
  Qed.

  Lemma skips_f8 : forall (ra : Z) (m : word -> option byte) (d : dsm) (S : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) Q,
    rw_cells s0segs m (S + 3152) (MID_CELLS d) -> sm_ll4 d = 0 -> 0 < S -> S + 64144 < 2 ^ 64 -> mem_inv s0segs m ->
    evt s0segs Q (inEnd 0x15dec ra spw gp tp t0 t1 t2 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m) ->
    evt s0segs Q (inEnd 0x15dd8 ra spw gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m).
  Proof.
    intros until Q. intros MIDc L4 S0 SHI MI HQ.
    apply (glueE_load 0x15dd8) with (d := d); [right; reflexivity | exact MIDc | exact S0 | exact SHI | exact MI |]. cbn [Z.eqb Pos.eqb]. rewrite L4.
    apply (glueE_skip 0x15ddc 0x15dec); [right; right; split; reflexivity | exact MI |]. exact HQ.
  Qed.

  Lemma mid_cps : forall (c : bcfg) (m : word -> option byte) (MD : Model) (s : ai_AS AI) (pS : bid) (S : Z) (b : bzs) (h : dsh) (d : dsm)
      (dlv : Z) (j8 : list byte) (raE : Z) (xs0 xs1 errv : word)
      (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ai_inv AI s (cfg_extra c ++ (pS, S, 64144) :: LB) m MD -> ac_vm AC kcr s MD -> ~ In pS (map blk_id LB) ->
    sm_tt d = cfg_tt c -> sm_ll16 d = cfg_l16 c -> sm_ll4 d = cfg_l4 c ->
    vm_only MD0 MD -> ai_aux AI m B -> rw_cells s0segs m (errno_cell L) [C4 errv] -> mem_inv s0segs m ->
    stk s0segs m lo (usp + -160) ->
    TM m b h d dlv j8 raE xs0 xs1 -> bzs_wf b -> bs_S b = S -> bs_bzfree b = Z_to_bv 64 0x13e3c -> bs_opaque b = Z_to_bv 64 0 ->
    (raE = 0x1600c \/ raE = 0x16024 \/ raE = 0x16034) -> 0 <= dlv <= dn ->
    (raE = 0x16024 -> xs0 = Z_to_bv 64 0 \/ xs0 = Z_to_bv 64 1) -> RESF raE xs0 xs1 dlv ->
    pres Pcl m0 m ->
    realizes s0segs (mkCfg (inEnd 0x15db4 raE spw gp tp t0 t1 t2 a0 (Z_to_bv 64 (cfg_tt c)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src)
                                  s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m) MD) K.
  Proof.
    intros until t6. intros INV VMC NIP ETT EL16 EL4 VMO AUX ERR MI ST TMm BWF BS BF BO RAE DLV X01 RES PR.
    pose proof geom_facts as G. pose proof (u64_range spw) as Uspw.
    destruct (ai_inv_model AI INV) as [Hh Hl].
    pose proof (ai_inv_nodup AI INV) as ND.
    assert (SIN : In (pS, S, 64144) (cfg_extra c ++ (pS, S, 64144) :: LB)) by (apply in_or_app; right; left; reflexivity).
    cps_pose (ai_inv_blocks AI (b := (pS, S, 64144)) INV SIN) as (S1 & S2 & S3 & S4 & S5).
    cbn [blk_addr blk_size fst snd] in S1, S2, S3, S4, S5. bz_ceil.
    cps_pose TMm as (_ & _ & _ & _ & T5 & _).
    destruct c as [| bt | b4 b6 | b6 | b4]; cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 app] in *.
    - (* [comment removed for export] *)
      eapply (evt_realizes s0segs (fun ms => ms = inEnd 0x15dec raE spw gp tp t0 t1 t2 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m));
        [exact Hh | exact Hl | |].
      { apply (glueE_skip 0x15db4 0x15dc4); [left; split; reflexivity | exact MI |].
        eapply skips_e4; [rewrite <- BS; exact T5 | exact EL16 | exact EL4 | lia | lia | exact MI | apply evt_done; reflexivity]. }
      intros ms' ->. eapply fin_cps; eassumption.
    - (* [comment removed for export] *)
      rewrite (ablock_eta bt) in INV, ND |- *. cbn [blk_id blk_addr blk_size fst snd] in ND.
      apply nodup_cons_inv in ND as [NI1 ND].
      eapply (free_mid 0x15db4 0x15dc4) with (pS := pS) (pX := blk_id bt) (nX := blk_size bt); try eassumption.
      + left. split; reflexivity.
      + left. reflexivity.
      + rewrite lb_remove_head by exact NI1. left. reflexivity.
      + intros b0 Hb0. rewrite lb_remove_head by exact NI1. right. exact Hb0.
      + intros m' MD' s' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 INV' VMC' VMO' AUX' ERR' MI' ST' TM' PR'.
        rewrite lb_remove_head in INV' by exact NI1.
        destruct (ai_inv_model AI INV') as [Hh' Hl']. cps_pose TM' as (_ & _ & _ & _ & T5' & _).
        eapply (evt_realizes s0segs (fun ms => ms = inEnd 0x15dec 0x15dc4 spw gp tp y0 y1 y2 ya0 (Z_to_bv 64 0) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 S F fc m'));
          [exact Hh' | exact Hl' | |].
        { eapply skips_e4; [rewrite <- BS; exact T5' | exact EL16 | exact EL4 | lia | lia | exact MI' | apply evt_done; reflexivity]. }
        intros ms' ->. eapply fin_cps; eassumption.
    - (* [comment removed for export] *)
      rewrite (ablock_eta b6), (ablock_eta b4) in INV, ND. cbn [blk_id blk_addr blk_size fst snd] in ND.
      apply nodup_cons_inv in ND as [NI4 ND]. apply nodup_cons_inv in ND as [NI6 ND]. cbn [map blk_id fst snd In] in NI4.
      pose proof (ai_inv_blocks AI (b := (blk_id b6, blk_addr b6, blk_size b6)) INV ltac:(right; left; reflexivity)) as (X1 & _).
      cbn [blk_addr fst snd] in X1.
      eapply (evt_realizes s0segs (fun ms => ms = inEnd 0x15dc8 raE spw gp tp t0 t1 t2 a0 (Z_to_bv 64 (blk_addr b6)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m));
        [exact Hh | exact Hl | |].
      { apply (glueE_skip 0x15db4 0x15dc4); [left; split; reflexivity | exact MI |].
        apply (glueE_load 0x15dc4) with (d := d); [left; reflexivity | rewrite <- BS; exact T5 | lia | lia | exact MI |]. cbn [Z.eqb Pos.eqb]. rewrite EL16.
        apply evt_done; reflexivity. }
      intros ms' ->.
      eapply (free_mid 0x15dc8 0x15dd8) with (pS := pS) (pX := blk_id b6) (nX := blk_size b6); try eassumption.
      + right; left. split; reflexivity.
      + right; left. reflexivity.
      + rewrite lb_remove_cons_other by (cbn; intros E; apply NI4; left; symmetry; exact E). rewrite lb_remove_head by exact NI6. right; left; reflexivity.
      + intros b0 Hb0. rewrite lb_remove_cons_other by (cbn; intros E; apply NI4; left; symmetry; exact E). rewrite lb_remove_head by exact NI6. right; right; exact Hb0.
      + intros m' MD' s' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 INV' VMC' VMO' AUX' ERR' MI' ST' TM' PR'.
        rewrite lb_remove_cons_other in INV' by (cbn; intros E; apply NI4; left; symmetry; exact E). rewrite lb_remove_head in INV' by exact NI6.
        destruct (ai_inv_model AI INV') as [Hh' Hl']. cps_pose TM' as (_ & _ & _ & _ & T5' & _).
        eapply (evt_realizes s0segs (fun ms => ms = inEnd 0x15ddc 0x15dd8 spw gp tp y0 y1 y2 ya0 (Z_to_bv 64 (blk_addr b4)) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 S F fc m'));
          [exact Hh' | exact Hl' | |].
        { apply (glueE_load 0x15dd8) with (d := d); [right; reflexivity | rewrite <- BS; exact T5' | lia | lia | exact MI' |]. cbn [Z.eqb Pos.eqb]. rewrite EL4.
          apply evt_done; reflexivity. }
        intros ms' ->.
        eapply (free_mid 0x15ddc 0x15dec) with (pS := pS) (pX := blk_id b4) (nX := blk_size b4); try eassumption.
        * right; right. split; reflexivity.
        * left. reflexivity.
        * rewrite lb_remove_head by (cbn; intros [E|E]; [apply NI4; right; left; exact E | apply NI4; right; right; exact E]). left; reflexivity.
        * intros b0 Hb0. rewrite lb_remove_head by (cbn; intros [E|E]; [apply NI4; right; left; exact E | apply NI4; right; right; exact E]). right; exact Hb0.
        * intros m'' MD'' s'' z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 INV'' VMC'' VMO'' AUX'' ERR'' MI'' ST'' TM'' PR''.
          rewrite lb_remove_head in INV'' by (cbn; intros [E|E]; [apply NI4; right; left; exact E | apply NI4; right; right; exact E]).
          eapply fin_cps; eassumption.
    - (* [comment removed for export] *)
      rewrite (ablock_eta b6) in INV, ND. cbn [blk_id blk_addr blk_size fst snd] in ND.
      apply nodup_cons_inv in ND as [NI6 ND].
      pose proof (ai_inv_blocks AI (b := (blk_id b6, blk_addr b6, blk_size b6)) INV ltac:(left; reflexivity)) as (X1 & _).
      cbn [blk_addr fst snd] in X1.
      eapply (evt_realizes s0segs (fun ms => ms = inEnd 0x15dc8 raE spw gp tp t0 t1 t2 a0 (Z_to_bv 64 (blk_addr b6)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m));
        [exact Hh | exact Hl | |].
      { apply (glueE_skip 0x15db4 0x15dc4); [left; split; reflexivity | exact MI |].
        apply (glueE_load 0x15dc4) with (d := d); [left; reflexivity | rewrite <- BS; exact T5 | lia | lia | exact MI |]. cbn [Z.eqb Pos.eqb]. rewrite EL16.
        apply evt_done; reflexivity. }
      intros ms' ->.
      eapply (free_mid 0x15dc8 0x15dd8) with (pS := pS) (pX := blk_id b6) (nX := blk_size b6); try eassumption.
      + right; left. split; reflexivity.
      + left. reflexivity.
      + rewrite lb_remove_head by exact NI6. left; reflexivity.
      + intros b0 Hb0. rewrite lb_remove_head by exact NI6. right; exact Hb0.
      + intros m' MD' s' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 INV' VMC' VMO' AUX' ERR' MI' ST' TM' PR'.
        rewrite lb_remove_head in INV' by exact NI6.
        destruct (ai_inv_model AI INV') as [Hh' Hl']. cps_pose TM' as (_ & _ & _ & _ & T5' & _).
        eapply (evt_realizes s0segs (fun ms => ms = inEnd 0x15dec 0x15dd8 spw gp tp y0 y1 y2 ya0 (Z_to_bv 64 0) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 S F fc m'));
          [exact Hh' | exact Hl' | |].
        { eapply skips_f8; [rewrite <- BS; exact T5' | exact EL4 | lia | lia | exact MI' | apply evt_done; reflexivity]. }
        intros ms' ->. eapply fin_cps; eassumption.
    - (* [comment removed for export] *)
      rewrite (ablock_eta b4) in INV, ND. cbn [blk_id blk_addr blk_size fst snd] in ND.
      apply nodup_cons_inv in ND as [NI4 ND].
      pose proof (ai_inv_blocks AI (b := (blk_id b4, blk_addr b4, blk_size b4)) INV ltac:(left; reflexivity)) as (X1 & _).
      cbn [blk_addr fst snd] in X1.
      eapply (evt_realizes s0segs (fun ms => ms = inEnd 0x15ddc raE spw gp tp t0 t1 t2 a0 (Z_to_bv 64 (blk_addr b4)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m));
        [exact Hh | exact Hl | |].
      { apply (glueE_skip 0x15db4 0x15dc4); [left; split; reflexivity | exact MI |].
        apply (glueE_load 0x15dc4) with (d := d); [left; reflexivity | rewrite <- BS; exact T5 | lia | lia | exact MI |]. cbn [Z.eqb Pos.eqb]. rewrite EL16.
        apply (glueE_skip 0x15dc8 0x15dd8); [right; left; split; reflexivity | exact MI |].
        apply (glueE_load 0x15dd8) with (d := d); [right; reflexivity | rewrite <- BS; exact T5 | lia | lia | exact MI |]. cbn [Z.eqb Pos.eqb]. rewrite EL4.
        apply evt_done; reflexivity. }
      intros ms' ->.
      eapply (free_mid 0x15ddc 0x15dec) with (pS := pS) (pX := blk_id b4) (nX := blk_size b4); try eassumption.
      + right; right. split; reflexivity.
      + left. reflexivity.
      + rewrite lb_remove_head by exact NI4. left; reflexivity.
      + intros b0 Hb0. rewrite lb_remove_head by exact NI4. right; exact Hb0.
      + intros m' MD' s' y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 INV' VMC' VMO' AUX' ERR' MI' ST' TM' PR'.
        rewrite lb_remove_head in INV' by exact NI4.
        eapply fin_cps; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition atD4 (raE : Z) (b : bzs) (h : dsh) (d : dsm) (dlv : Z) (m : word -> option byte) (S : Z)
      (t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state -> Prop :=
    fun ms => exists (a0' a2' : word) (m' : word -> option byte) (j8 : list byte) (t0' a1' s0v s1v : word),
      ms = inEnd 0x15db4 raE spw gp tp t0' t1 t2 a0' (Z_to_bv 64 (sm_tt d)) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 S F fc m'
      /\ TM m' b h d dlv j8 raE s0v s1v /\ stk s0segs m' lo (usp + -160)
      /\ munch [(usp + -160, usp + -128); (dl, dl + 4)] m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
      /\ (raE = 0x16024 -> s0v = Z_to_bv 64 0 \/ s0v = Z_to_bv 64 1) /\ RESF raE s0v s1v dlv.

  Lemma tail_cps : forall (c : bcfg) (rc : Z) (m : word -> option byte) (MD : Model) (s : ai_AS AI) (pS : bid) (S : Z) (b : bzs) (h : dsh) (d : dsm)
      (xs1 errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ai_inv AI s (cfg_extra c ++ (pS, S, 64144) :: LB) m MD -> ac_vm AC kcr s MD -> ~ In pS (map blk_id LB) ->
    sm_tt d = cfg_tt c -> sm_ll16 d = cfg_l16 c -> sm_ll4 d = cfg_l4 c ->
    vm_only MD0 MD -> ai_aux AI m B -> rw_cells s0segs m (errno_cell L) [C4 errv] -> mem_inv s0segs m ->
    stk s0segs m lo (usp + -128) ->
    rw_cells s0segs m (usp + -128) (STRM_CELLS b) -> rw_cells s0segs m (usp + -48) (SAVES s4e s3e s2e s1e s0e ra0) ->
    rw_cells s0segs m (bs_S b) (HEAD_CELLS h) -> rw_cells s0segs m (bs_S b + 3152) (MID_CELLS d) ->
    rw_cells s0segs m dl [C4 (Z_to_bv 64 dn)] -> rw_cells s0segs m dst [CB (Z.to_nat dn) db] ->
    rw_cells s0segs m 0x33178 [CB CRC_BYTES crc_table_bytes] -> rw_cells s0segs m 0x335b0 [CB RNUMS_BYTES rnums_table_bytes] ->
    b2bD_got s0segs S0DI m g1 sv ->
    bzs_wf b -> bs_S b = S -> bs_bzfree b = Z_to_bv 64 0x13e3c -> bs_opaque b = Z_to_bv 64 0 -> bs_dlen b = dn -> sh_strm h = usp - 128 ->
    (* [comment removed for export] *)
    (forall m', rw_cells s0segs m' dst [CB (Z.to_nat dn) db] ->
        (rc mod 2 ^ 64 = 0 -> b2bD_result s0segs (if bs_av b =? 0 then BZ_OUTBUFF_FULL else BZ_UNEXPECTED_EOF) dst dn srcZ small m' dn)
        /\ (rc mod 2 ^ 64 = 4 -> b2bD_result s0segs BZ_OK dst dn srcZ small m' (dn - bs_av b))
        /\ (rc mod 2 ^ 64 <> 0 -> rc mod 2 ^ 64 <> 4 -> b2bD_result s0segs rc dst dn srcZ small m' dn)) ->
    pres Pcl m0 m ->
    realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x15fe4) (Z_to_bv 64 (usp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 dl) xs1
                                    (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x15fe4) fc None m (seg_rom s0segs)) MD) K.
  Proof.
    intros until t6. intros INV VMC NIP ETT EL16 EL4 VMO AUX ERR MI ST C1 C2 C4 C5 C6 C7 C8 C9 GOT BWF BS BF BO BDL HS RES3 PR.
    pose proof geom_facts as G. pose proof (u64_range spw) as Uspw. cps_pose DLF as (D1 & D2 & D3 & D4).
    destruct (ai_inv_model AI INV) as [Hh Hl].
    assert (SIN : In (pS, S, 64144) (cfg_extra c ++ (pS, S, 64144) :: LB)) by (apply in_or_app; right; left; reflexivity).
    cps_pose (ai_inv_blocks AI (b := (pS, S, 64144)) INV SIN) as (S1 & S2 & S3 & S4 & S5).
    cbn [blk_addr blk_size fst snd] in S1, S2, S3, S4, S5. bz_ceil.
    cps_pose BWF as (Q1 & Q2 & AIr & AVr & LENr & DLENr). rewrite BS in C4, C5.
    (* [comment removed for export] *)
    assert (SEG : exists raE dlv, (raE = 0x1600c \/ raE = 0x16024 \/ raE = 0x16034) /\ 0 <= dlv <= dn /\
              evt s0segs (atD4 raE b h d dlv m S t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                  (MS (mkR (Z_to_bv 64 0x15fe4) (Z_to_bv 64 (usp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 dl) xs1
                           (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x15fe4) fc None m (seg_rom s0segs))).
    { destruct (Z.eq_dec (rc mod 2 ^ 64) 0) as [R0|R0].
      - (* [comment removed for export] *)
        exists 0x16024, dn. split; [right; left; reflexivity|]. split; [lia|].
        replace (Z_to_bv 64 rc) with (Z_to_bv 64 0) by (apply Z_to_bv_eqm; rewrite R0; reflexivity).
        eapply glueD0F; [exact C1 | exact BWF | exact MI |]. intros t0' a1'.
        eapply (glueE1 0x16024 spw) with (lo := lo); [exact C1 | exact BS | exact C4 | exact HS | exact C5
          | lia | lia | zlia | zlia | exact ST | lia | lia | exact MI | lia |].
        intros a0' a2' m' j8 FRE C1' C4' C5' ST' MU WM MI'. apply evt_done. unfold atD4.
        exists a0', a2', m', j8, t0', a1', (Z_to_bv 64 (if bs_av b =? 0 then 1 else 0)), xs1. split; [reflexivity|].
        split. { unfold TM. rewrite <- BS in C4', C5'. repeat match goal with |- _ /\ _ => split end; try (first [assumption | eassumption]).
                 - eapply rw_cells_transport; [exact C2 | exact MU | exact WM | unfold SAVES; cbn; lia].
                 - eapply rw_cells_transport; [exact C6 | exact MU | exact WM | cbn; lia].
                 - eapply rw_cells_transport; [exact C7 | exact MU | exact WM | cbn; lia].
                 - eapply rw_cells_transport; [exact C8 | exact MU | exact WM | unfold CRC_BYTES; cbn; lia].
                 - eapply rw_cells_transport; [exact C9 | exact MU | exact WM | unfold RNUMS_BYTES; cbn; lia].
                 - destruct GOT as [GO1 GO2]. split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; lia]). }
        split; [exact ST'|]. split; [|split; [exact WM| split; [exact MI'| split]]].
        { intros x Hx. apply MU. cbn in Hx |- *. tauto. }
        { intros _. destruct (bs_av b =? 0); [right| left]; reflexivity. }
        { (intros mq aq DBq; cps_intros (_ & _ & Q7 & Q8)). cps_destruct (RES3 mq DBq) as (RA & _ & _).
          destruct (Z.eqb_spec (bs_av b) 0) as [E|E].
          - exists BZ_OUTBUFF_FULL. split; [exact (Q8 eq_refl eq_refl)| exact (RA R0)].
          - exists BZ_UNEXPECTED_EOF. split; [exact (Q7 eq_refl eq_refl)| exact (RA R0)]. }
      - destruct (Z.eq_dec (rc mod 2 ^ 64) 4) as [R4|R4].
        + (* [comment removed for export] *)
          exists 0x1600c, (dn - bs_av b). split; [left; reflexivity|]. split; [lia|].
          replace (Z_to_bv 64 rc) with (Z_to_bv 64 4) by (apply Z_to_bv_eqm; rewrite R4; reflexivity).
          eapply glueD4; [exact C1 | exact BWF | exact MI | exact C6 | lia | lia | lia |]. intros t0' a1' m1 C6' C1x MU1 WM1 MI1.
          eapply (glueE1 0x1600c spw) with (lo := lo);
           [exact C1x | exact BS | | exact HS | | lia | lia | zlia | zlia | | lia | lia | exact MI1 | lia |].
          { eapply rw_cells_transport; [exact C4 | exact MU1 | exact WM1 | cbn; lia]. }
          { eapply rw_cells_transport; [exact C5 | exact MU1 | exact WM1 | cbn; lia]. }
          { eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 | cbn; lia]. }
          intros a0' a2' m' j8 FRE C1' C4' C5' ST' MU WM MI'. apply evt_done. unfold atD4.
          exists a0', a2', m', j8, t0', a1', (Z_to_bv 64 dl), (Z_to_bv 64 4). split; [reflexivity|].
          split. { unfold TM. rewrite <- BS in C4', C5'. repeat match goal with |- _ /\ _ => split end; try (first [assumption | eassumption]).
                   - eapply rw_cells_transport; [| exact MU | exact WM | unfold SAVES; cbn; lia].
                     eapply rw_cells_transport; [exact C2 | exact MU1 | exact WM1 | unfold SAVES; cbn; lia].
                   - eapply rw_cells_transport; [exact C6' | exact MU | exact WM | cbn; lia].
                   - eapply rw_cells_transport; [| exact MU | exact WM | cbn; lia].
                     eapply rw_cells_transport; [exact C7 | exact MU1 | exact WM1 | cbn; lia].
                   - eapply rw_cells_transport; [| exact MU | exact WM | unfold CRC_BYTES; cbn; lia].
                     eapply rw_cells_transport; [exact C8 | exact MU1 | exact WM1 | unfold CRC_BYTES; cbn; lia].
                   - eapply rw_cells_transport; [| exact MU | exact WM | unfold RNUMS_BYTES; cbn; lia].
                     eapply rw_cells_transport; [exact C9 | exact MU1 | exact WM1 | unfold RNUMS_BYTES; cbn; lia].
                   - destruct GOT as [GO1 GO2]. split.
                     + eapply rw_cells_transport; [| exact MU | exact WM | cbn; lia]. eapply rw_cells_transport; [exact GO1 | exact MU1 | exact WM1 | cbn; lia].
                     + eapply rw_cells_transport; [| exact MU | exact WM | cbn; lia]. eapply rw_cells_transport; [exact GO2 | exact MU1 | exact WM1 | cbn; lia]. }
          split; [exact ST'|]. split; [| split; [eapply wmono_trans; [exact WM1| exact WM]| split; [exact MI'| split]]].
          { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU]]; intros x Hx; cbn in Hx |- *; tauto. }
          { intros X; exfalso; clear -X; lia. }
          { (intros mq aq DBq; cps_intros (Q0 & _ & _ & _)). cps_destruct (RES3 mq DBq) as (_ & RB & _).
            exists BZ_OK. split; [exact (Q0 eq_refl)| exact (RB R4)]. }
        + (* [comment removed for export] *)
          exists 0x16034, dn. split; [right; right; reflexivity|]. split; [lia|].
          eapply glueDx; [exact MI | exact R0 | exact R4 |]. intros a0x.
          eapply (glueE1 0x16034 spw) with (lo := lo); [exact C1 | exact BS | exact C4 | exact HS | exact C5
            | lia | lia | zlia | zlia | exact ST | lia | lia | exact MI | lia |].
          intros a0' a2' m' j8 FRE C1' C4' C5' ST' MU WM MI'. apply evt_done. unfold atD4.
          exists a0', a2', m', j8, t0, a0x, (Z_to_bv 64 dl), (Z_to_bv 64 rc). split; [reflexivity|].
          split. { unfold TM. rewrite <- BS in C4', C5'. repeat match goal with |- _ /\ _ => split end; try (first [assumption | eassumption]).
                   - eapply rw_cells_transport; [exact C2 | exact MU | exact WM | unfold SAVES; cbn; lia].
                   - eapply rw_cells_transport; [exact C6 | exact MU | exact WM | cbn; lia].
                   - eapply rw_cells_transport; [exact C7 | exact MU | exact WM | cbn; lia].
                   - eapply rw_cells_transport; [exact C8 | exact MU | exact WM | unfold CRC_BYTES; cbn; lia].
                   - eapply rw_cells_transport; [exact C9 | exact MU | exact WM | unfold RNUMS_BYTES; cbn; lia].
                   - destruct GOT as [GO1 GO2]. split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; lia]). }
          split; [exact ST'|]. split; [|split; [exact WM| split; [exact MI'| split]]].
          { intros x Hx. apply MU. cbn in Hx |- *. tauto. }
          { intros X; exfalso; clear -X; lia. }
          { (intros mq aq DBq; cps_intros (_ & Q1' & _ & _)). cps_destruct (RES3 mq DBq) as (_ & _ & RC).
            exists rc. split; [exact (Q1' eq_refl)| exact (RC R0 R4)]. } }
    (* [comment removed for export] *)
    cps_destruct SEG as (raE & dlv & RAE & DLV & SEGe).
    eapply (evt_realizes s0segs); [exact Hh | exact Hl | exact SEGe |].
    (intros ms'; cps_intros (a0' & a2' & m' & j8 & t0' & a1' & s0v & s1v & -> & TM' & ST' & MU & WM & MI' & X01 & RES)). unfold inEnd. rewrite ETT.
    eapply (mid_cps c) with (s := s) (pS := pS) (errv := errv); try eassumption.
    - eapply (ai_inv_frame AI); [exact INV | exact MU | exact WM |].
      apply Forall_cons; [apply cwo_stack; lia|]. apply Forall_cons; [apply cwo_stack; lia| apply Forall_nil].
    - eapply (ai_aux_frame AI); [exact AUX | exact MU | exact WM | aux_fp].
    - eapply rw_cells_transport; [exact ERR | exact MU | exact WM | unfold errno_cell, L, S0_layout; cbn; lia].
    - eapply pres_trans; [exact PR|]. eapply pres_mono; [| apply pres_of_munch; [exact MU| exact WM]].
      intros a Ha [CA NO]. unfold b2bD_out in NO. cbn. split; [| split; [lia| exact I]].
      destruct CA as [C|[C|(b0 & Hb0 & Hr)]]; [lia| unfold L, S0_layout in C; cbn [al_rw_lo al_img_hi] in C; lia|].
      cps_pose (BLKS _ Hb0) as (_ & _ & _ & B4 & _). bz_ceil. lia.
  Qed.
End Tail.

End ACeilS1.
