(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module paths, module names, addresses and numbers changed; 1202 of its 1379 lines of code are new or changed and 1532 lines of the source are left out. *)
(* Segment F16 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A, libreac v1.9.0): the cut-to-cut range
   0x821d0 .. 0x8229c (slot-plan-asan section 2 row F16), with the instrumented-check blocks shown not reached or
   passed.  From the entry cut Inv_A821d0_at (the head of the inner byte-sum loop on its first turn; the turn closes
   a record, so the fragment class of the turn is FgClose; t0 = n, the length of the FIRST state) the segment:
     - runs the loop 0x821d0-0x821f4 pll + 5 times (pll = f_pll = fg_T - 13).  Each turn loads the shadow byte at
       (a >> 3) + 0x7fff8000 of the record byte a = fragb fr + 15 + i and compares it with 0; the record's 72
       bytes are addressable and 8-aligned, so every shadow byte is 0 (shadow0_72, through AsanRTFacts.meta8) and
       the slow path 0x821fc / the error call at 0x82c28 is not reached.  The byte is added to a1 (f16_loop, by
       induction on the down-counter a4);
     - 0x82208-0x8220c: a1 is the record's 15-offset window sum, 0 mod 128 because the turn's class is FgClose
       (sum_closes, from RcFrag.fg_close's recsum conjunct), so `bnez a0,82bf4` is not taken;
     - 0x82210-0x82290 (v1.9): the first-fragment address check.  [A+104] = have = 1 (FI with frag_ok and
       fg_keep), so `beqz a0,82bf4` is not taken.  The inlined joined_byte (first, blk, i) for i = 9 / 10 reads
       first.body[i] through [A+56] = fr + 2889 / [A+48] = fr + 2890 when i < n (t0), else blk[9 + i - n] at
       s6 + (18 - n) / s6 + (19 - n) (s6 = blk = phi + 18); each read has an instrumented check (fast path, or the
       slow paths 0x829d8 / 0x829e4 back into the block), which passes because the byte is addressable (first's
       35 bytes, FSb; the frame's block, HB).  The 16-bit value (byte 9 << 8 | byte 10) equals the u16 the
       fragment call left at [A+256] = fr + 256: the fragment's address is the joined record's bytes 17 / 18, which
       are joined_byte 9 / 10 of the FIRST state (jb_join, by FI), so `bne a0,a1,82bf4` is not taken;
     - 0x82294-0x82298: a0 = [A+144] = fr + 2688 (the identity buffer) and the call of reac_identity_ingest
       (Section Hypothesis HING).  The callee writes only [sp - 32, sp) and the 38 identity bytes, and returns
       fst (ING ..) in {0, 1} (neither pointer is 0), which the exit carries as 0 <= a0 < 2 ^ 63.  The identity
       buffer holds ID1 g j on entry (IFS2, push 12), so after the call it holds the ingest of ID1 g j at the
       fragment's address and payload, which is the identity of turn S j (t_ID_S_ingest): the exit's IFS3.
   FRA is rebuilt across the call by Tac_slot.sl_fr_cl on both frame arms (real: Contract.a_laws_store; side:
   Tac_fs.a_fs_ok_store_AH), with the write set [(sp - 32, sp); (fr + 2688, fr + 2726)]; ENT moves with
   Tac_slot.ent_store and Tac_slot.ent_mat (push 5c).  The cut bodies carry no mem_inv: the ingest contract has
   no mem_inv premise, and its post's `mem_inv m -> mem_inv m'` is fed FRA's own mem_inv.
   The entry cut Inv_A821d0_at, the exit cut Inv_A8229c_at (F17's entry) and the bundle F17CARRY with the record
   invariant's two halves rec_inv0 / rec_parse are A/Prog/SlotInv.v's. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentLib RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv bcmp_wrap_c
  reac_identity_ingest_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot Tac_b5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Local Notation memcmp_model := SF.memcmp_model.


(* ===== pure model lemmas (stage A) ===== *)

(* engine load helpers (as F20.v) *)
Lemma rd1 : forall m a v, b8 m a v -> ov_read_bytes rsegs m (wa a) 1 = Some [Z_to_bv 8 v].
Proof.
  intros m a v H. unfold b8 in H.
  pose proof (bytes_at_ov_read rsegs m a [Z_to_bv 8 v] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (cbn; lia). exact HH.
Qed.
Lemma rd2 : forall m a v, u16 m a v -> ov_read_bytes rsegs m (wa a) 2 = Some (le2 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold u16 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 2 H ltac:(rewrite length_le2; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite length_le2; lia).
  exact HH.
Qed.
Lemma rd8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold q64 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite length_le8; lia).
  exact HH.
Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.
Lemma eqb_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.
Lemma zx16_lit : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma zxb_lit : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus; cbn; lia. Qed.

Lemma bat_nonneg : forall bs i, 0 <= bat bs i.
Proof. intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. Qed.

Lemma bat_lt : forall bs i, bat bs i < 256.
Proof. intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). unfold bv_modulus in *. cbn in *. lia. Qed.

Lemma ret1_close : forall c, fg_ret c = 1 -> c = FgClose.
Proof. intros c H. destruct c; cbn [fg_ret] in H; try discriminate; reflexivity. Qed.

Lemma trf1_cls : forall inp j, t_rf inp j = 1 ->
  fcls (t_len inp j) (t_FG inp j) (t_g inp j) = FgClose.
Proof. intros inp j H. unfold t_rf, fg_rf in H. apply ret1_close. exact H. Qed.

Lemma cls_close_inv : forall len st g,
  fcls len st g = FgClose -> fg_fr len g = true /\ fg_keep st g = true /\ fg_close st g = true /\ bat g 19 <> 1.
Proof.
  intros len st g H. unfold fcls, fg_class in H.
  destruct (negb (fg_fr len g)) eqn:Efr; [cbn in H; discriminate|].
  destruct (bat g 19 =? 1) eqn:E19; [cbn in H; discriminate|].
  destruct (negb (fg_keep st g)) eqn:Ek; [cbn in H; discriminate|].
  destruct (negb (fg_close st g)) eqn:Ec; [cbn in H; discriminate|].
  apply Bool.negb_false_iff in Efr, Ek, Ec. apply Z.eqb_neq in E19. repeat split; try assumption.
Qed.

Lemma tFGf_close : forall inp j, t_rf inp j = 1 ->
  t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j)).
Proof. intros inp j H. unfold t_FGf, fg_st. rewrite (trf1_cls inp j H). reflexivity. Qed.

Lemma frT14 : forall st g, fg_close st g = true -> 14 <= fg_T st g.
Proof. intros st g H. unfold fg_close in H. rewrite !andb_true_iff in H. apply Z.leb_le. tauto. Qed.
Lemma closeT64 : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof. intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H. apply Z.leb_le. tauto. Qed.
Lemma keep_hf : forall st g, fg_keep st g = true -> fg_hf st <> 0.
Proof. intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H. destruct H as ((H & _) & _).
  apply Bool.negb_true_iff, Z.eqb_neq in H. exact H. Qed.
Lemma fr_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof. intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (((((((((((_ & _) & _) & _) & _) & _) & _) & _) & _) & Hlo) & Hhi) & _).
  apply Z.leb_le in Hlo, Hhi. lia. Qed.

Lemma join_len : forall st g, length st = 72%nat -> length g = 50%nat ->
  0 <= fg_lf st -> 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> length (fg_join st g) = 72%nat.
Proof.
  intros st g HL HG Hlf Hn HT. unfold fg_join, fg_body, fg_T in *.
  rewrite !length_app. unfold bsl. rewrite !length_firstn, !length_skipn, HL, HG. lia.
Qed.
Lemma nth_err_firstn : forall (n i : nat) (l : list byte), (i < n)%nat ->
  nth_error (firstn n l) i = nth_error l i.
Proof.
  induction n as [|n IH]; intros [|i] [|a l] H; cbn; try lia; try reflexivity.
  apply IH. lia.
Qed.
Lemma ba_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H2). split; [exact H0|].
  split; [rewrite firstn_length; lia|].
  intros i Hi. rewrite firstn_length in Hi. rewrite nth_err_firstn by lia. apply H2. lia.
Qed.
Lemma memcmp_firstn : forall n k (l r : list byte), (n <= k)%nat ->
  SF.memcmp_model (firstn k l) (firstn k r) n = SF.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros k l r H; cbn [SF.memcmp_model]; [reflexivity|].
  destruct k as [|k]; [lia|].
  destruct l as [|a l]; destruct r as [|b r]; cbn [firstn SF.memcmp_model]; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH; lia | reflexivity].
Qed.
Lemma bsl_len_le : forall bs k n, (length (RF.bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold RF.bsl. rewrite firstn_length. apply Nat.le_min_l. Qed.

(* psum helpers *)
Lemma psum_nonneg : forall bs n, 0 <= psum bs n.
Proof. intros bs n. induction n as [|n IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 8 (nth n bs (Z_to_bv 8 0))). lia. Qed.
Lemma psum_bound : forall bs n, psum bs n <= 256 * Z.of_nat n.
Proof. intros bs n. induction n as [|n IH]; cbn [psum]; [lia|].
  pose proof (bv_unsigned_in_range 8 (nth n bs (Z_to_bv 8 0))) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
Lemma psum_ext : forall l1 l2 n, (forall i, (i < n)%nat -> nth i l1 (Z_to_bv 8 0) = nth i l2 (Z_to_bv 8 0)) ->
  psum l1 n = psum l2 n.
Proof. intros l1 l2 n. induction n as [|n IH]; intros H; cbn [psum]; [reflexivity|].
  rewrite (IH (fun i Hi => H i (ltac:(lia)))). rewrite (H n ltac:(lia)). reflexivity. Qed.

(* self-contained nth helpers *)
Lemma nthfn : forall (i n : nat) (l : list byte), (i < n)%nat -> nth i (firstn n l) (Z_to_bv 8 0) = nth i l (Z_to_bv 8 0).
Proof.
  intros i n l. revert i l. induction n as [|n IH]; intros i l Hi; [lia|].
  destruct l as [|a l]; cbn [firstn]; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [nth]; [reflexivity|]. apply IH. lia.
Qed.
Lemma nth_sk : forall (m i : nat) (l : list byte), nth i (skipn m l) (Z_to_bv 8 0) = nth (m + i) l (Z_to_bv 8 0).
Proof.
  induction m as [|m IH]; intros i l.
  - reflexivity.
  - destruct l as [|a l].
    + cbn [skipn]. rewrite !nth_overflow by (cbn; lia). reflexivity.
    + cbn [skipn plus nth]. apply IH.
Qed.
Lemma firstn1_skipn : forall (n : nat) (l : list byte), (n < length l)%nat ->
  firstn 1 (skipn n l) = [nth n l (Z_to_bv 8 0)].
Proof.
  induction n as [|n IH]; intros [|a l] HL; cbn in HL; try lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.
Lemma nth_clear_hi : forall (j : nat) (st : list byte), (7 <= j)%nat -> (6 <= length st)%nat ->
  nth j (fg_clear st) (Z_to_bv 8 0) = nth j st (Z_to_bv 8 0).
Proof.
  intros j st Hj HL. unfold fg_clear.
  rewrite app_nth2; rewrite firstn_length; [|rewrite Nat.min_l by lia; lia].
  rewrite Nat.min_l by lia.
  rewrite app_nth2; cbn [length]; [|lia].
  rewrite nth_sk. f_equal. lia.
Qed.

(* skipn 15 commutes with fg_clear *)
Lemma skipn15_clear : forall st : list byte, (6 <= length st)%nat ->
  skipn 15 (fg_clear st) = skipn 15 st.
Proof.
  intros st HL. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite !length_skipn. unfold fg_clear. rewrite !length_app, firstn_length, length_skipn. cbn [length].
    rewrite Nat.min_l by lia. lia.
  - intros i Hi. rewrite length_skipn in Hi. rewrite !nth_sk. apply nth_clear_hi; lia.
Qed.

Lemma close_recsum : forall st g, fg_close st g = true ->
  recsum (bsl (fg_join st g) 15 (fg_T st g - 8)) = 0.
Proof. intros st g H. unfold fg_close in H. rewrite !andb_true_iff in H.
  destruct H as (_ & Hz). apply Z.eqb_eq. exact Hz. Qed.

Lemma bat_join_lo : forall st g i, 0 <= i -> i < 8 + fg_lf st -> (Z.to_nat i < length st)%nat ->
  bat (fg_join st g) i = bat st i.
Proof.
  intros st g i H0 Hlf HL. unfold bat, fg_join.
  assert (Hlen : (Z.to_nat i < length (firstn (Z.to_nat (8 + fg_lf st)) st))%nat).
  { rewrite firstn_length. apply Nat.min_glb_lt; [|exact HL]. apply Z2Nat.inj_lt; lia. }
  rewrite app_nth1 by exact Hlen. rewrite nthfn; [reflexivity| apply Z2Nat.inj_lt; lia].
Qed.

(* the core: recsum of the 15-offset window, in psum form *)
Lemma sum_core : forall (X : list byte) (K : nat), length X = 72%nat -> (K <= 56)%nat ->
  psum (firstn K (skipn 15 X)) (length (firstn K (skipn 15 X))) mod 128 = 0 ->
  psum (skipn 15 X) K mod 128 = 0 /\ psum (skipn 15 X) K <= 14336.
Proof.
  intros X K HLX HK Hrec.
  assert (HlenB : length (firstn K (skipn 15 X)) = K) by (rewrite firstn_length, length_skipn, HLX; lia).
  rewrite HlenB in Hrec.
  assert (Hpf : psum (firstn K (skipn 15 X)) K = psum (skipn 15 X) K)
    by (apply psum_ext; intros i Hi; apply nthfn; exact Hi).
  rewrite Hpf in Hrec. split; [exact Hrec|].
  pose proof (psum_bound (skipn 15 X) K). lia.
Qed.

(* the loop sum closes mod 128 and is small, from fg_close's recsum conjunct *)
Lemma sum_closes : forall inp j, t_rf inp j = 1 ->
  psum (skipn 15 (t_FGf inp j)) (Z.to_nat (fg_T (t_FG inp j) (t_g inp j) - 8)) mod 128 = 0
  /\ psum (skipn 15 (t_FGf inp j)) (Z.to_nat (fg_T (t_FG inp j) (t_g inp j) - 8)) <= 14336.
Proof.
  intros inp j Hrf.
  pose proof (trf1_cls inp j Hrf) as Hcls.
  destruct (cls_close_inv _ _ _ Hcls) as (Hfr & Hkeep & Hclose & _).
  pose proof (F13.t_FG_length inp j) as HLst. pose proof (F13.t_g_length inp j) as HLg.
  pose proof (fr_n _ _ Hfr) as Hn. pose proof (closeT64 _ _ Hkeep) as HT64. pose proof (frT14 _ _ Hclose) as HT14.
  assert (Hlf0 : 0 <= fg_lf (t_FG inp j)) by apply bat_nonneg.
  pose proof (join_len _ _ HLst HLg Hlf0 Hn HT64) as HLX.
  rewrite (tFGf_close inp j Hrf). rewrite skipn15_clear by (rewrite HLX; lia).
  apply sum_core; [exact HLX | |].
  - apply (Nat.le_trans _ (Z.to_nat 56)); [apply Z2Nat.inj_le; lia | lia].
  - pose proof (close_recsum _ _ Hclose) as Hrec. unfold recsum, bsl in Hrec.
    change (Z.to_nat 15) with 15%nat in Hrec. exact Hrec.
Qed.


(* loop + shadow (verified earlier, inlined) *)
Ltac ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (unsigned_lit X) by lia end.
Lemma eqb0_false : forall v, 0 < v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof. intros v Hv. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal bv_unsigned) in HC. rewrite !unsigned_lit in HC by lia. lia. Qed.

Section D.
Context {fx : FPState}.

Lemma f16_loop : forall (k i : nat) (ra0 sp gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bs : list byte),
  0 <= p -> p + Z.of_nat (i + k) + 8 < 2 ^ 64 -> (1 <= k)%nat ->
  (forall q, (q < i + k)%nat -> ov_read_bytes rsegs m (wa (p + Z.of_nat q)) 1 = Some [nth q bs (Z_to_bv 8 0)]) ->
  (forall q, (q < i + k)%nat -> ov_read_bytes rsegs m (wa (Z.shiftr (p + Z.of_nat q) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0]) ->
  evt rsegs
    (fun ms' => exists a6' : word,
       ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + Z.of_nat (i + k))) (Z_to_bv 64 (psum bs (i + k)))
                     a2 a3 (Z_to_bv 64 0) (Z_to_bv 64 (p + Z.of_nat (i + k))) a6' a7
                     s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                Fr (Z_to_bv 64 0x82208) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
             a2 a3 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (p + Z.of_nat i)) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i ra0 sp gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    Fr fc m p bs Hp Hb Hk HRD HSH; [lia|].
  pose proof (HRD i ltac:(lia)) as RDi. pose proof (HSH i ltac:(lia)) as SHi.
  step. step. ush. step. step. if_false.
  step. change (zxb (nth i bs (Z_to_bv 8 0))) with (Z_to_bv 64 (bv_unsigned (nth i bs (Z_to_bv 8 0)))).
  step. step. step. step. step.
  clear RDi SHi.
  destruct k as [|k].
  - if_false. step.
    apply evt_done. exists (Z_to_bv 64 (bv_unsigned (nth i bs (Z_to_bv 8 0)))).
    replace (p + Z.of_nat i + 1) with (p + Z.of_nat (i + 1)) by lia.
    replace (psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0))) with (psum bs (i + 1))
      by (rewrite Nat.add_1_r; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat 1 + -1)) with (Z_to_bv 64 0) by (f_equal; lia). reflexivity.
  - assert (Hne : negb (bv_eqb (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) (Z_to_bv 64 0)) = true).
    { apply Bool.negb_true_iff. apply eqb0_false. split; [lia|]. rewrite Nat2Z.inj_succ in *. lia. }
    rewrite Hne; cbv iota.
    replace (p + Z.of_nat i + 1) with (p + Z.of_nat (i + 1)) by lia.
    replace (psum bs i + bv_unsigned (nth i bs (Z_to_bv 8 0))) with (psum bs (i + 1))
      by (rewrite Nat.add_1_r; reflexivity).
    replace (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) with (Z_to_bv 64 (Z.of_nat (S k)))
      by (f_equal; rewrite Nat2Z.inj_succ; lia).
    replace (i + S (S k))%nat with ((i + 1) + S k)%nat by lia.
    apply IH.
    + exact Hp.
    + replace ((i + 1) + S k)%nat with (i + S (S k))%nat by lia. exact Hb.
    + lia.
    + intros q Hq. apply HRD. lia.
    + intros q Hq. apply HSH. lia.
Qed.

Lemma shadow0_72 : forall m base q,
  addressable m base 72 -> base mod 8 = 0 -> 0 <= q < 72 ->
  ov_read_bytes rsegs m (wa (Z.shiftr (base + q) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m base q AD Hbase Hq.
  assert (Hdiv : 0 <= q / 8 < 9) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (ADg : addressable m (base + 8 * (q / 8)) 8)
    by (apply (addressable_sub m base 72 (8 * (q / 8)) 8 AD); lia).
  assert (L : Z.shiftr (base + 8 * (q / 8)) 3 = Z.shiftr (base + q) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    assert (Hb8 : base = (base / 8) * 8) by (pose proof (Z.div_mod base 8 ltac:(lia)); lia).
    rewrite (Z.mul_comm 8 (q / 8)), Z.div_add by lia.
    rewrite Hb8 at 2. rewrite (Z.add_comm (base / 8 * 8) q), Z.div_add by lia. lia. }
  destruct (meta8 m (base + 8 * (q / 8)) ADg) as (RO & _).
  rewrite L in RO.
  pose proof (cells_at_read rsegs m (Z.shiftr (base + q) 3 + ASAN_K) [C1 (Z_to_bv 8 0)] 0%nat
                (C1 (Z_to_bv 8 0)) RO eq_refl) as H.
  cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
Qed.

End D.


(* ===== v1.9: the tail 0x82210 .. 0x82298 (have check, the inlined joined_byte of FIRST bytes 9 / 10 with
   their instrumented checks, the 16-bit address compare), as continuation lemmas over the next state ===== *)

(* subw / slli 32 / srli 32 of a small difference, then add: the inlined joined_byte offset (0x82224-0x82234,
   0x8225c-0x8226c). *)
Lemma f16_zsub : forall S6 c n, 0 <= n <= c -> c < 2 ^ 31 ->
  Z_to_bv 64 (S6 + Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64
     (bv_swrap 32 (c - bv_unsigned (Z_to_bv 64 n))))) 32))) 32) = Z_to_bv 64 (S6 + (c - n)).
Proof.
  intros S6 c n Hn Hc. f_equal. f_equal.
  rewrite (unsigned_lit n) by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with 2147483648; lia).
  rewrite (unsigned_lit (c - n)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit ((c - n) * 2 ^ 32)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma f16_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma f16_sxb_eqb0 : forall b : byte, bv_eqb (sxb b) (Z_to_bv 64 0) = (bv_signed b =? 0).
Proof.
  intros b. unfold sxb. apply RcAsanLib.rc_eqb0_signed. pose proof (RcAsanLib.rc_byte_signed b). lia.
Qed.

(* the slow path's `bge (X land 7), k`: not taken when X mod 8 < k *)
Lemma f16_bge_slow : forall X (b : byte), 0 <= X < 2 ^ 64 -> X mod 8 < bv_signed b ->
  bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 X)) 7)) (sxb b) = true.
Proof.
  intros X b HX Hk. unfold sxb. rewrite (unsigned_lit X) by lia. rewrite RcAsanLib.rc_land7.
  pose proof (Z.mod_pos_bound X 8 ltac:(lia)). pose proof (RcAsanLib.rc_byte_signed b).
  rewrite RcAsanLib.rc_lts_signed by lia. apply Z.ltb_lt. exact Hk.
Qed.

Section T.
Context {fx : FPState}.

(* 0x82284 .. 0x82298: the low byte, the 16-bit join, the compare with the fragment's address (equal: not
   taken) and the identity buffer pointer for the ingest call. *)
Lemma f16_p284 : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA id X2 : Z) (ch cl : byte),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
  FA = 256 * bv_unsigned ch + bv_unsigned cl ->
  q64 m (A + 144) id ->
  (forall a4 : word, evt rsegs Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 id) (Z_to_bv 64 FA) a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82298) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb ch) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82284) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA id X2 ch cl HA0 HA HX2 RDl HFA H144 K.
  pose proof (rd8 m (A + 144) id H144) as RD144.
  pose proof (f16_byte_range ch) as Rh. pose proof (f16_byte_range cl) as Rl.
  (* 0x82284 lbu a4,0(a4) ; 0x82288 slli a0,a0,8 ; 0x8228c or a0,a0,a4 *)
  step. step. step.
  unfold zxb.
  rewrite ?(unsigned_lit (bv_unsigned ch)) by lia.
  rewrite ?(unsigned_lit (bv_unsigned cl)) by lia.
  rewrite ?(unsigned_lit (Z.shiftl (bv_unsigned ch) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite ?(Z.lor_comm (Z.shiftl (bv_unsigned ch) 8) (bv_unsigned cl)).
  rewrite ?(lor_shiftl8_add (bv_unsigned cl) (bv_unsigned ch)) by lia.
  replace (bv_unsigned cl + 256 * bv_unsigned ch) with FA by lia.
  (* 0x82290 bne a0,a1 : equal, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x82294 ld a0,144(s1) *)
  step.
  apply K.
Qed.

(* 0x82270 .. 0x82284: the instrumented check of the low byte's address X2 (fast path, or the slow path
   0x829e4 .. 0x829ec back to 0x82284) and the high byte load at X1. *)
Lemma f16_p270 : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA X1 X2 : Z) (b2 ch : byte),
  0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
  (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
  ov_read_bytes rsegs m (wa X1) 1 = Some [ch] ->
  (forall a5' a6' : word, evt rsegs Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (zxb ch) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5' a6' a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82284) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 (Z_to_bv 64 X2) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82270) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t0 t1 t2 s0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA X1 X2 b2 ch HX1 HX2 RS Hck RDh K.
  (* 0x82270 srli a5,a4,3 ; 0x82274 add a5,a5,s10 ; 0x82278 lb a5,0(a5) ; 0x8227c lbu a0,0(a0) *)
  step. step. rewrite ?(unsigned_lit X2) by lia. step. step.
  (* 0x82280 bnez a5 *)
  step. rewrite f16_sxb_eqb0.
  destruct (Z.eqb_spec (bv_signed b2) 0) as [K0|K0].
  - cbn [negb]. cbv iota. apply K.
  - cbn [negb]. cbv iota.
    (* 0x829e4 andi a6,a4,7 ; 0x829e8 bge a6,a5 (not taken: X2 mod 8 < k) ; 0x829ec j 82284 *)
    step. step.
    rewrite (f16_bge_slow X2 b2) by (lia || (destruct Hck; lia)). cbn [negb]. cbv iota.
    step. apply K.
Qed.

(* 0x82250 .. 0x82270: the low byte's address, joined_byte (first, blk, 10): [A+48] = first + 10 when
   10 < n, else s6 + (19 - n) = blk + 9 + 10 - n. *)
Lemma f16_p250 : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA X1 n S6 P48 : Z),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
  q64 m (A + 48) P48 ->
  (forall a5' : word, evt rsegs Q
     (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3
              (Z_to_bv 64 (if 10 <? n then P48 else S6 + (19 - n))) a5' a6 a7
              s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82270) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82250) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA X1 n S6 P48 HA0 HA Hn HS0 HS HP H48 K.
  pose proof (rd8 m (A + 48) P48 H48) as RD48.
  (* 0x82250 ld a4,48(s1) ; 0x82254 li a5,10 ; 0x82258 bltu a5,t0 *)
  step. step. step.
  replace (bv_ltu (Z_to_bv 64 10) (Z_to_bv 64 n)) with (10 <? n)
    by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; reflexivity).
  revert K. destruct (Z.ltb_spec 10 n) as [Hlt|Hge]; intros K; cbv iota in K |- *.
  - apply K.
  -
    (* 0x8225c li a4,19 ; subw a4,a4,t0 ; slli a4,a4,32 ; srli a4,a4,32 ; add a4,s6,a4 *)
    step. step. step. step. step.
    rewrite (f16_zsub S6 19 n) by lia.
    apply K.
Qed.

(* 0x82238 .. 0x82250: the instrumented check of the high byte's address X1 (fast path, or the slow path
   0x829d8 .. 0x829e0 back to 0x82250), with the fragment's address FA = [[A+256]] loaded on the way. *)
Lemma f16_p238 : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A FA P256 X1 : Z) (b1 : byte),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= X1 < 2 ^ 64 -> 0 <= FA < 65536 -> 0 <= P256 < 2 ^ 64 ->
  q64 m (A + 256) P256 -> u16 m P256 FA ->
  ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
  (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
  (forall a4' a5' : word, evt rsegs Q
     (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) (Z_to_bv 64 FA) a2 a3 a4' a5' a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82250) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X1) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82238) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A FA P256 X1 b1 HA0 HA HX1 HFA HP H256 HU RS Hck K.
  pose proof (rd8 m (A + 256) P256 H256) as RD256. pose proof (rd2 m P256 FA HU) as RDFA.
  (* 0x82238 srli a1,a0,3 ; 0x8223c add a1,a1,s10 ; 0x82240 lb a4,0(a1) ; 0x82244 ld a1,256(s1) ;
     0x82248 lhu a1,0(a1) *)
  step. step. rewrite ?(unsigned_lit X1) by lia. step. step. step.
  rewrite (zx16_lit FA) by lia.
  (* 0x8224c bnez a4 *)
  step. rewrite f16_sxb_eqb0.
  destruct (Z.eqb_spec (bv_signed b1) 0) as [K0|K0].
  - cbn [negb]. cbv iota. apply K.
  - cbn [negb]. cbv iota.
    (* 0x829d8 andi a5,a0,7 ; 0x829dc bge a5,a4 (not taken) ; 0x829e0 j 82250 *)
    step. step.
    rewrite (f16_bge_slow X1 b1) by (lia || (destruct Hck; lia)). cbn [negb]. cbv iota.
    step. apply K.
Qed.

(* 0x82210 .. 0x82238: have = [A+104] <> 0 (not taken), and the high byte's address, joined_byte (first,
   blk, 9): [A+56] = first + 9 when 9 < n, else s6 + (18 - n) = blk + 9 + 9 - n. *)
Lemma f16_p210 : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A vh n S6 P56 : Z),
  0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 18 < 2 ^ 64 -> 0 <= P56 < 2 ^ 64 ->
  0 < vh < 2 ^ 64 ->
  q64 m (A + 104) vh -> q64 m (A + 56) P56 ->
  (forall a1' : word, evt rsegs Q
     (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A)
              (Z_to_bv 64 (if 9 <? n then P56 else S6 + (18 - n))) a1' a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
         Fr (Z_to_bv 64 0x82238) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x82210) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A vh n S6 P56 HA0 HA Hn HS0 HS HP Hvh H104 H56 K.
  pose proof (rd8 m (A + 104) vh H104) as RD104. pose proof (rd8 m (A + 56) P56 H56) as RD56.
  (* 0x82210 ld a0,104(s1) ; 0x82214 beqz a0 (have <> 0: not taken) *)
  step. step.
  replace (bv_eqb (Z_to_bv 64 vh) (Z_to_bv 64 0)) with false
    by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  cbv iota.
  (* 0x82218 ld a0,56(s1) ; 0x8221c li a1,9 ; 0x82220 bltu a1,t0 *)
  step. step. step.
  replace (bv_ltu (Z_to_bv 64 9) (Z_to_bv 64 n)) with (9 <? n)
    by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; reflexivity).
  revert K. destruct (Z.ltb_spec 9 n) as [Hlt|Hge]; intros K; cbv iota in K |- *.
  - apply K.
  -
    (* 0x82224 li a0,18 ; subw a0,a0,t0 ; slli a0,a0,32 ; srli a0,a0,32 ; add a0,s6,a0 *)
    step. step. step. step. step.
    rewrite (f16_zsub S6 18 n) by lia.
    apply K.
Qed.

End T.


(* f16_evt: the run 0x821d0 -> 0x8229c (loop, sum check, the v1.9 tail lemmas above, ingest call). *)
Section E.
Context {fx : FPState}.

Lemma f16_evt :
  forall (ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 : Z) (K : nat) (rec idb pb : list byte)
         (b1 b2 ch cl : byte),
    reac_identity_ingest_contract ->
    Z.of_nat K = pll + 5 -> (1 <= K <= 57)%nat ->
    0 <= fb -> fb mod 8 = 0 -> fb + 100 < 2 ^ 64 ->
    addressable m fb 72 -> bytes_at rsegs m fb rec -> length rec = 72%nat ->
    psum (skipn 15 rec) K mod 128 = 0 -> psum (skipn 15 rec) K < 2 ^ 64 ->
    q64 m (A + 104) vh -> 0 < vh < 2 ^ 64 ->
    q64 m (A + 56) P56 -> q64 m (A + 48) P48 -> 0 <= P56 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
    0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 ->
    X1 = (if 9 <? n then P56 else S6 + (18 - n)) -> X2 = (if 10 <? n then P48 else S6 + (19 - n)) ->
    0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
    (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
    ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
    (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
    ov_read_bytes rsegs m (wa X1) 1 = Some [ch] -> ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
    FA = 256 * bv_unsigned ch + bv_unsigned cl -> 0 <= FA < 65536 ->
    q64 m (A + 256) P256 -> u16 m P256 FA -> 0 <= P256 < 2 ^ 64 -> q64 m (A + 144) id ->
    0 <= A -> A + 416 <= 2 ^ 64 ->
    0 <= id < 2 ^ 64 -> 0 <= pll < 2 ^ 64 -> id <> 0 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat pll ->
    (0 < pll -> fb + 19 <> 0 -> bytes_at rsegs m (fb + 19) pb) ->
    (id <> 0 -> 0 < pll -> fb + 19 <> 0 -> (fb + 19) + pll <= id \/ id + 38 <= fb + 19) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < pll -> fb + 19 <> 0 ->
       (fb + 19) + pll <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= fb + 19) ->
    asan_cells m -> shadow_rw m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < pll -> fb + 19 <> 0 -> addressable m (fb + 19) pll) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    evt rsegs
      (reac_identity_ingest_post (Z_to_bv 64 0x8229c) sp gp tp s0 (Z_to_bv 64 A) s2 s3 s4 s5 (Z_to_bv 64 S6)
         s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 Fr fc m lo id FA (fb + 19) pll idb pb)
      (MS (mkR ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (fb + 15)) (Z_to_bv 64 0)
               (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) (Z_to_bv 64 (Z.of_nat K)) (Z_to_bv 64 (fb + 15)) a6 a7
               s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t1 t2 s0 a6 a7 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
    A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl
    HING HK HKb Hfb0 Hfb8 Hfbb ADr BAr Lr Hsum Hsumb
    H104 Hvh H56 H48 HP56 HP48 Hn HS0 HS19 EX1 EX2 HX1 HX2 RS1 Hck1 RS2 Hck2 RDh RDl HFAe HFAb
    H256 HU HP256b H144 HA0 HAb Hidb Hpllb Hidnz
    Hidcells Lpb Hpb Hdjp Hstk Hlo Hdji Hdjps HAC HSW Hadi Hadp Hout.
  (* ---- the loop 0x821d0 .. 0x821f4, from turn 0 ---- *)
  replace (Z_to_bv 64 (fb + 15)) with (Z_to_bv 64 ((fb + 15) + Z.of_nat 0)) by (f_equal; lia).
  replace (Z_to_bv 64 0) with (Z_to_bv 64 (psum (skipn 15 rec) 0)) by reflexivity.
  eapply evt_cut.
  { apply (f16_loop K 0 ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (fb + 19))
             (Z_to_bv 64 pll) a6 a7 s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m
             (fb + 15) (skipn 15 rec)).
    - lia.
    - lia.
    - lia.
    - intros q Hq.
      pose proof (bytes_at_read rsegs m fb rec (15 + Z.of_nat q) 1 BAr ltac:(lia) ltac:(rewrite Lr; lia)) as RD.
      replace (fb + 15 + Z.of_nat q) with (fb + (15 + Z.of_nat q)) by lia.
      rewrite RD. f_equal. rewrite nth_sk.
      replace (Z.to_nat (15 + Z.of_nat q)) with (15 + q)%nat by lia.
      apply firstn1_skipn. rewrite Lr. lia.
    - intros q Hq. replace (fb + 15 + Z.of_nat q) with (fb + (15 + Z.of_nat q)) by lia.
      apply shadow0_72; [exact ADr | exact Hfb8 | lia]. }
  intros ms1 (a6x & ->).
  (* ---- at 0x82208: andi a0,a1,127 ; bnez a0,82bf4 (not taken: the sum closes) ---- *)
  replace (0 + K)%nat with K by lia.
  step.
  pose proof (psum_nonneg (skipn 15 rec) K) as Hpn.
  rewrite (unsigned_lit (psum (skipn 15 rec) K)) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  rewrite Hsum.
  step. if_false.
  (* ---- 0x82210 .. 0x82298: the v1.9 tail ---- *)
  apply (f16_p210 _ ra0 sp gp tp t1 t2 s0 _ _ (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) _ _ a6x a7
           s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A vh n S6 P56 HA0 HAb Hn HS0 ltac:(lia) HP56 Hvh
           H104 H56).
  intros x1. rewrite <- EX1.
  apply (f16_p238 _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 x1 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) _ _ a6x a7
           s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA P256 X1 b1
           HA0 HAb HX1 HFAb HP256b H256 HU RS1 Hck1).
  intros x4 x5.
  apply (f16_p250 _ ra0 sp gp tp t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) x4 x5 a6x a7
           s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA X1 n S6 P48 HA0 HAb Hn HS0 HS19 HP48 H48).
  intros y5. rewrite <- EX2.
  apply (f16_p270 _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) y5 a6x a7
           s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA X1 X2 b2 ch HX1 HX2 RS2 Hck2 RDh).
  intros z5 z6.
  apply (f16_p284 _ ra0 sp gp tp (Z_to_bv 64 n) t1 t2 s0 (Z_to_bv 64 (fb + 19)) (Z_to_bv 64 pll) z5 z6 a7
           s2 s3 s4 s5 (Z_to_bv 64 S6) s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m A FA id X2 ch cl HA0 HAb HX2 RDl HFAe
           H144).
  intros w4.
  (* 0x82298 jal reac_identity_ingest *)
  step.
  unfold reac_identity_ingest_contract in HING.
  eapply HING; try reflexivity; try assumption; try lia.
Qed.

(* the same run with the register slots given by equations, so it unifies against Regs6ss.mkR_of regs *)
Lemma f16_evt' :
  forall (ra0 sp gp tp t0v t1 t2 s0 s1v a0v a1v a2v a3v a4v a5v a6 a7 s2 s3 s4 s5 s6v s7 s8 s9 s10v s11
          t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 : Z) (K : nat) (rec idb pb : list byte)
         (b1 b2 ch cl : byte),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 (fb + 15) -> a1v = Z_to_bv 64 0 ->
    a2v = Z_to_bv 64 (fb + 19) -> a3v = Z_to_bv 64 pll -> a4v = Z_to_bv 64 (Z.of_nat K) ->
    a5v = Z_to_bv 64 (fb + 15) -> s10v = Z_to_bv 64 ASAN_K -> t0v = Z_to_bv 64 n -> s6v = Z_to_bv 64 S6 ->
    reac_identity_ingest_contract ->
    Z.of_nat K = pll + 5 -> (1 <= K <= 57)%nat ->
    0 <= fb -> fb mod 8 = 0 -> fb + 100 < 2 ^ 64 ->
    addressable m fb 72 -> bytes_at rsegs m fb rec -> length rec = 72%nat ->
    psum (skipn 15 rec) K mod 128 = 0 -> psum (skipn 15 rec) K < 2 ^ 64 ->
    q64 m (A + 104) vh -> 0 < vh < 2 ^ 64 ->
    q64 m (A + 56) P56 -> q64 m (A + 48) P48 -> 0 <= P56 < 2 ^ 64 -> 0 <= P48 < 2 ^ 64 ->
    0 <= n < 2 ^ 64 -> 0 <= S6 -> S6 + 19 < 2 ^ 64 ->
    X1 = (if 9 <? n then P56 else S6 + (18 - n)) -> X2 = (if 10 <? n then P48 else S6 + (19 - n)) ->
    0 <= X1 < 2 ^ 64 -> 0 <= X2 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (Z.shiftr X1 3 + ASAN_K)) 1 = Some [b1] ->
    (bv_signed b1 = 0 \/ X1 mod 8 < bv_signed b1) ->
    ov_read_bytes rsegs m (wa (Z.shiftr X2 3 + ASAN_K)) 1 = Some [b2] ->
    (bv_signed b2 = 0 \/ X2 mod 8 < bv_signed b2) ->
    ov_read_bytes rsegs m (wa X1) 1 = Some [ch] -> ov_read_bytes rsegs m (wa X2) 1 = Some [cl] ->
    FA = 256 * bv_unsigned ch + bv_unsigned cl -> 0 <= FA < 65536 ->
    q64 m (A + 256) P256 -> u16 m P256 FA -> 0 <= P256 < 2 ^ 64 -> q64 m (A + 144) id ->
    0 <= A -> A + 416 <= 2 ^ 64 ->
    0 <= id < 2 ^ 64 -> 0 <= pll < 2 ^ 64 -> id <> 0 ->
    (id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m id [CB 38 idb]) ->
    length pb = Z.to_nat pll ->
    (0 < pll -> fb + 19 <> 0 -> bytes_at rsegs m (fb + 19) pb) ->
    (id <> 0 -> 0 < pll -> fb + 19 <> 0 -> (fb + 19) + pll <= id \/ id + 38 <= fb + 19) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_IDENTITY_INGEST_FRAME <= bv_unsigned sp ->
    (id <> 0 -> id + 38 <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= id) ->
    (0 < pll -> fb + 19 <> 0 ->
       (fb + 19) + pll <= bv_unsigned sp - REAC_IDENTITY_INGEST_FRAME \/ bv_unsigned sp <= fb + 19) ->
    asan_cells m -> shadow_rw m ->
    (id <> 0 -> addressable m id 38) ->
    (0 < pll -> fb + 19 <> 0 -> addressable m (fb + 19) pll) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside (reac_identity_ingest_W (bv_unsigned sp) id) x) ->
    evt rsegs
      (reac_identity_ingest_post (Z_to_bv 64 0x8229c) sp gp tp s0 (Z_to_bv 64 A) s2 s3 s4 s5 (Z_to_bv 64 S6)
         s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 Fr fc m lo id FA (fb + 19) pll idb pb)
      (MS (mkR ra0 sp gp tp t0v t1 t2 s0 s1v a0v a1v a2v a3v a4v a5v a6 a7
               s2 s3 s4 s5 s6v s7 s8 s9 s10v s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0v t1 t2 s0 s1v a0v a1v a2v a3v a4v a5v a6 a7 s2 s3 s4 s5 s6v s7 s8 s9 s10v s11
    t3 t4 t5 t6 Fr fc m A fb pll FA id lo vh n S6 P56 P48 P256 X1 X2 K rec idb pb b1 b2 ch cl
    -> -> -> -> -> -> -> -> -> ->.
  apply f16_evt.
Qed.

End E.


(* extra model lemmas for seg_F16 *)
Lemma t_FGf_length : forall inp j, length (t_FGf inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FGf, fg_st, fcls.
  apply (F13.fg_next_length 1 1 1 1 1); [apply F13.t_FG_length | apply F13.t_g_length].
Qed.

(* v1.9 joined_byte (SlotModel): byte 8 + i of the record the closing fragment call joined is joined_byte of the
   turn's FIRST state at i, for every i below the joined length T = lf + n of the closing frame (the record's
   address bytes 17 / 18 are i = 9 / 10, and a closing record has T >= 14).  The FIRST state equals the
   reassembly state's FIRST part by FI (byte 6 = 1). *)
Lemma jb_join : forall st g s i, length st = 72%nat -> length g = 50%nat -> FI st s -> bat st 6 = 1 ->
  0 <= i < fg_T st g -> fg_T st g <= 64 -> 1 <= fg_n g <= 22 ->
  bat (fg_join st g) (8 + i) = joined_byte s g i.
Proof.
  intros st g s i HL HG HFI H6 Hi HT Hn.
  destruct (HFI H6) as (_ & En & Eb).
  unfold joined_byte. rewrite En, Eb.
  pose proof (bat_nonneg st 7) as Hlf0.
  unfold fg_T, fg_lf, fg_n in *.
  destruct (Z.ltb_spec i (bat st 7)) as [Hlt|Hge].
  - rewrite (bat_join_lo st g (8 + i)) by (unfold fg_lf; rewrite ?HL; lia).
    unfold bat at 1 2. f_equal. rewrite nthfn by lia. rewrite nth_sk. f_equal. lia.
  - unfold bat at 1, fg_join, fg_lf.
    rewrite app_nth2 by (rewrite firstn_length, HL; lia).
    rewrite firstn_length, HL.
    rewrite app_nth1 by (unfold fg_body, bsl, fg_n; rewrite firstn_length, length_skipn, HG; lia).
    unfold fg_body, bsl, fg_n. rewrite nthfn by lia. rewrite nth_sk.
    change (bat g (27 + i - bat st 7)) with (bv_unsigned (nth (Z.to_nat (27 + i - bat st 7)) g (Z_to_bv 8 0))).
    f_equal. f_equal. lia.
Qed.

(* Push 12: on the fragment-ingest edge (t_rf j = 1) the identity of turn S j is the ingest of ID1 g j at the
   fragment's address and payload (SlotModel fg_id). *)
Lemma t_ID_S_ingest : forall g j, t_rf (g_in g) j = 1 ->
  t_ID (g_in g) (S j) = snd (ING (ID1 g j) (fg_addr (t_FG (g_in g) j) (t_g (g_in g) j))
                                  (f_pl (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j))).
Proof.
  intros g j H. rewrite F13.t_ID_S1. unfold fg_id.
  replace (fg_rf (flen g j) (t_FG (g_in g) j) (t_g (g_in g) j) =? 1) with true; [reflexivity|].
  symmetry. apply Z.eqb_eq. exact H.
Qed.

Section P.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* A spill read through s1 = A (as F20.v's sl_spill_at). *)
Lemma sl_spill_at : forall regs m A off v, rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 ->
  0 <= off -> off + 8 <= 416 -> spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA Ho0 Ho (A' & H9' & Hq).
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. cbn in Hq1.
    unfold rg in H9, H9'. rewrite H9 in H9'. apply (f_equal bv_unsigned) in H9'.
    rewrite (MState.unsigned_lit A) in H9' by lia. rewrite Z_to_bv_unsigned in H9'.
    unfold bv_wrap, bv_modulus in H9'. change (2 ^ Z.of_N 64) with (2 ^ 64) in H9'.
    pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)). lia. }
  subst A'. exact Hq.
Qed.

End P.


Ltac fold_sp2 regs :=
  match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) end.

Lemma mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
  (getr regs 31).
Proof. reflexivity. Qed.

Ltac subst_slot H := let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HING : reac_identity_ingest_contract.

(* The entry at 0x821d0 is the official Inv_A821d0_at of A/Prog/SlotInv.v (aslot push 11B); the exit at 0x8229c
   is the official F17 entry Inv_A8229c_at at turn j.  F16 reaches it only when the turn closes a record
   (FgClose), so the frame has at least 50 bytes here; t_8819 is not fixed by that, so the compare operands come
   from F17CARRY's `t_8819 = true ->` group. *)
Lemma seg_F16 : forall j : nat,
  Hat B APIf ra (Inv_A8229c_at B APIf ra) j -> Hat B APIf ra (Inv_A821d0_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLV & Hrf &
    R10 & R15 & R11 & R12 & R13 & R14 & HbRec & HaRec & HfragOK & HFS & HU256 & HIdB & HaId &
    A & H9 & H208 & H256 & H144 & HCARRY & HIFS2 & R5).
  subst c. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  (* push 12: the identity buffer holds ID1 g j (IFS2's IDb1), so that is the ingest's idb *)
  clear HIdB.
  unfold IFS2, IDb1 in HIFS2. destruct HIFS2 as ((HbId & HidOK) & HFG1 & HFS1).
  unfold IDBe in HbId.
  assert (LId : length (ID1 g j) = 38%nat) by apply F13.ID1_length.
  set (idb := ID1 g j) in *.
  (* ---- the model side: the turn closes a record ---- *)
  pose proof (trf1_cls (g_in g) j Hrf) as Hcls.
  destruct (cls_close_inv _ _ _ Hcls) as (Hfr & Hkeep & Hclose & _).
  pose proof (F13.t_FG_length (g_in g) j) as HLst. pose proof (F13.t_g_length (g_in g) j) as HLg.
  pose proof (fr_n _ _ Hfr) as Hn. pose proof (closeT64 _ _ Hkeep) as HT64.
  pose proof (frT14 _ _ Hclose) as HT14.
  assert (Hlf0 : 0 <= fg_lf (t_FG (g_in g) j)) by apply bat_nonneg.
  pose proof (join_len _ _ HLst HLg Hlf0 Hn HT64) as HLX.
  (* the class passed fg_fr, whose first conjunct is 50 <= len: the record facts of F17CARRY hold *)
  assert (Hlen50 : 50 <= flen g j).
  { unfold fg_fr in Hfr. rewrite !andb_true_iff in Hfr.
    destruct Hfr as (Hf1 & _). repeat (destruct Hf1 as (Hf1 & _)). apply Z.leb_le in Hf1. unfold flen. exact Hf1. }
  (* push 14B: the entry's heap list is hb1 phi (AC.a_size (flen g j)), which is hb1 phi (flen g j) here *)
  assert (Easz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  rewrite Easz in HFRA, HENT.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA)
    as (Hplace & HfrA & Hfsmeta & Hfrwr).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hselq & Hfr24q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof HRT as (HAC0 & HSW0 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HA2b : 0 <= A2 < 2 ^ 64) by lia.
  destruct HCARRY as (Cs7 & Cs6 & Cs8 & Cs18 & Cs20 & H232 & H192 & H136 & H120 & H176 & H152 & HW240 & H50 &
    Hcmp).
  assert (HAr : -232 <= A /\ A + 240 <= 2 ^ 64).
  { unfold q64, bytes_at in H232. destruct H232 as (Ha0 & Ha1 & _).
    rewrite length_le8 in Ha1. cbn in Ha1. lia. }
  assert (HA2 : A2 = A).
  { pose proof (rg_eq64 regs 9 A2 A Hr9 H9) as Hm.
    revert Hm. change (2 ^ 64) with 18446744073709551616 in *.
    intros Hm. Z.div_mod_to_equations. lia. }
  subst A2.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH)).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in H9; rewrite H9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HfrA.
  (* the frame body is app memory above GT, on both arms *)
  assert (Hframe : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - intros a Ha. destruct (Hreal a Ha) as (Hlo2 & Hhi2).
      split; [right; unfold APPMEM_END, HIGHMEM_BEG in *; lia | unfold AC.GT, HIGHMEM_BEG in *; lia].
    - intros a Ha. destruct (Hfs a Ha) as (FSa & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (lw_fs_place (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem md FSa HAH Hw HFSr) as LWr1.
      pose proof (lwf_gt _ _ _ _ LWr1) as HG.
      pose proof (lwf_end _ _ _ _ LWr1) as Hend.
      pose proof (lwf_app _ _ _ _ LWr1) as Happ2.
      split; [exact (Happ2 a ltac:(lia)) | lia]. }
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; apply (Hframe a Ha)).
  assert (HGT : AC.GT <= fr) by (apply (Hframe fr ltac:(lia))).
  assert (Hfrb : 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1, H2. lia. }
  destruct (H50 Hlen50) as ((rb & Hrb & Lrb) & Hgb & Hpb & HRI).
  destruct (sum_closes (g_in g) j Hrf) as (Hsum0 & Hsumb0).
  (* ---- the FIRST state (v1.9 FSb: [A+104] have, [A+112] n, the body at fr + 2880, FI) ---- *)
  destruct HFS as (Hsp104 & Hsp112 & Hbody & Hadd35 & HFI).
  assert (HAq : 0 <= A /\ A + 416 <= 2 ^ 64) by lia.
  pose proof (sl_spill_at regs mem A 104 _ H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp104) as H104.
  assert (Hbat6 : bat (t_FG (g_in g) j) 6 = 1).
  { pose proof (keep_hf _ _ Hkeep) as Hhf. unfold fg_hf in Hhf.
    destruct HfragOK as ([H0|H1] & _); [exfalso; apply Hhf; exact H0 | exact H1]. }
  destruct (HFI Hbat6) as (Hhave1 & Hneq & Hbeq).
  (* [A+56] = first + 9 and [A+48] = first + 10, the two byte pointers P12 leaves in FLC (v1.9) *)
  pose proof HFLSI as HFLSI0. destruct HFLSI0 as (_ & _ & _ & _ & _ & HFLC0).
  unfold FLC in HFLC0. destruct HFLC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S56 & S48).
  pose proof (sl_spill_at regs mem A 56 _ H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56) as H56.
  pose proof (sl_spill_at regs mem A 48 _ H9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S48) as H48.
  (* s6 = blk = phi + 18 on a long frame *)
  assert (Ebig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact Hlen50).
  rewrite Ebig in Cs6.
  pose proof HRI as HRI0. destruct HRI0 as (Hphi0 & Hphi50 & _ & _ & Hphiapp & _).
  assert (Hphib : phi + 50 <= APPMEM_END) by (pose proof (Hphiapp (phi + 49) ltac:(lia)) as Ha;
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  (* the FIRST length n = byte 7 of the reassembly state, and the body's length is n *)
  set (n := fs_n (fst_at (g_in g) j)) in *.
  assert (Hnb : 0 <= n < 256) by (rewrite Hneq; split; [apply bat_nonneg | apply bat_lt]).
  assert (HnT : n <= 63) by (rewrite Hneq; unfold fg_T, fg_lf, fg_n in *; lia).
  assert (Lbody : length (fs_body (fst_at (g_in g) j)) = Z.to_nat n).
  { rewrite Hbeq, Hneq. rewrite firstn_length, length_skipn, HLst. rewrite <- Hneq. lia. }
  (* the two address bytes of the inlined joined_byte (first, blk, 9 / 10), their addresses and checks *)
  set (X1 := if 9 <? n then fr + 2889 else phi + 18 + (18 - n)).
  set (X2 := if 10 <? n then fr + 2890 else phi + 18 + (19 - n)).
  assert (HX1b : 0 <= X1 < 2 ^ 64) by (unfold X1; destruct (Z.ltb_spec 9 n); unfold APPMEM_END in *; lia).
  assert (HX2b : 0 <= X2 < 2 ^ 64) by (unfold X2; destruct (Z.ltb_spec 10 n); unfold APPMEM_END in *; lia).
  assert (HAd1 : addressable mem X1 1).
  { unfold X1. destruct (Z.ltb_spec 9 n) as [Hlt|Hge].
    - replace (fr + 2889) with (fr + 2880 + 9) by lia.
      apply (addressable_sub mem (fr + 2880) 35 9 1 Hadd35); lia.
    - destruct HHB as (_ & Hphiad). replace (phi + 18 + (18 - n)) with (phi + (36 - n)) by lia.
      apply (addressable_sub mem phi (AC.a_size (flen g j)) (36 - n) 1 Hphiad); unfold AC.a_size; lia. }
  assert (HAd2 : addressable mem X2 1).
  { unfold X2. destruct (Z.ltb_spec 10 n) as [Hlt|Hge].
    - replace (fr + 2890) with (fr + 2880 + 10) by lia.
      apply (addressable_sub mem (fr + 2880) 35 10 1 Hadd35); lia.
    - destruct HHB as (_ & Hphiad). replace (phi + 18 + (19 - n)) with (phi + (37 - n)) by lia.
      apply (addressable_sub mem phi (AC.a_size (flen g j)) (37 - n) 1 Hphiad); unfold AC.a_size; lia. }
  destruct (Tac_b5.sl_shadow1 mem X1 HAd1) as (b1 & RS1 & Hck1 & _).
  destruct (Tac_b5.sl_shadow1 mem X2 HAd2) as (b2 & RS2 & Hck2 & _).
  assert (HR1 : exists ch, ov_read_bytes rsegs mem (wa X1) 1 = Some [ch] /\
                  bv_unsigned ch = joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 9).
  { unfold X1, joined_byte. fold n. destruct (Z.ltb_spec 9 n) as [Hlt|Hge].
    - pose proof (bytes_at_read rsegs mem (fr + 2880) (fs_body (fst_at (g_in g) j)) 9 1 Hbody ltac:(lia)
                    ltac:(rewrite Lbody; lia)) as RD.
      change (Z.to_nat 9) with 9%nat in RD. rewrite (firstn1_skipn 9 _ ltac:(rewrite Lbody; lia)) in RD.
      replace (fr + 2880 + 9) with (fr + 2889) in RD by lia.
      eexists; split; [exact RD | reflexivity].
    - pose proof (bytes_at_read rsegs mem phi (t_g (g_in g) j) (36 - n) 1 Hgb ltac:(lia)
                    ltac:(rewrite HLg; lia)) as RD.
      rewrite (firstn1_skipn (Z.to_nat (36 - n)) _ ltac:(rewrite HLg; lia)) in RD.
      replace (phi + (36 - n)) with (phi + 18 + (18 - n)) in RD by lia.
      eexists; split; [exact RD|]. first [reflexivity | unfold bat; f_equal; f_equal; lia]. }
  assert (HR2 : exists cl, ov_read_bytes rsegs mem (wa X2) 1 = Some [cl] /\
                  bv_unsigned cl = joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 10).
  { unfold X2, joined_byte. fold n. destruct (Z.ltb_spec 10 n) as [Hlt|Hge].
    - pose proof (bytes_at_read rsegs mem (fr + 2880) (fs_body (fst_at (g_in g) j)) 10 1 Hbody ltac:(lia)
                    ltac:(rewrite Lbody; lia)) as RD.
      change (Z.to_nat 10) with 10%nat in RD. rewrite (firstn1_skipn 10 _ ltac:(rewrite Lbody; lia)) in RD.
      replace (fr + 2880 + 10) with (fr + 2890) in RD by lia.
      eexists; split; [exact RD | reflexivity].
    - pose proof (bytes_at_read rsegs mem phi (t_g (g_in g) j) (37 - n) 1 Hgb ltac:(lia)
                    ltac:(rewrite HLg; lia)) as RD.
      rewrite (firstn1_skipn (Z.to_nat (37 - n)) _ ltac:(rewrite HLg; lia)) in RD.
      replace (phi + (37 - n)) with (phi + 18 + (19 - n)) in RD by lia.
      eexists; split; [exact RD|]. first [reflexivity | unfold bat; f_equal; f_equal; lia]. }
  destruct HR1 as (ch & RDh & Ech). destruct HR2 as (cl & RDl & Ecl).
  (* ---- the address the check compares: the fragment's address is the joined record's bytes 17 / 18, which
     are joined_byte 9 / 10 of the FIRST state (jb_join) ---- *)
  assert (HFAeq : fg_addr (t_FG (g_in g) j) (t_g (g_in g) j) = 256 * bv_unsigned ch + bv_unsigned cl).
  { rewrite Ech, Ecl. unfold fg_addr.
    rewrite <- (jb_join _ _ _ 9 HLst HLg HFI Hbat6 ltac:(lia) HT64 Hn).
    rewrite <- (jb_join _ _ _ 10 HLst HLg HFI Hbat6 ltac:(lia) HT64 Hn).
    reflexivity. }
  assert (HFAb : 0 <= fg_addr (t_FG (g_in g) j) (t_g (g_in g) j) < 65536).
  { rewrite HFAeq. pose proof (f16_byte_range ch). pose proof (f16_byte_range cl). lia. }
  (* ---- the ingest arguments ---- *)
  assert (Hidcells : rw_cells rsegs mem (fr + 2688) [CB 38 idb]).
  { split.
    - split; [cbn; split; [exact LId | exact I]|].
      cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HbId.
    - split; [lia|]. split; [cbn [cells_size csize]; lia|].
      intros i Hi. cbn [cells_size csize] in Hi. apply Hfrwr. unfold fragb in *. lia. }
  assert (Hpll : 1 <= f_pll (t_FG (g_in g) j) (t_g (g_in g) j) <= 51)
    by (unfold f_pll; lia).
  assert (HbRec19 : bytes_at rsegs mem (fragb fr + 19)
            (firstn (Z.to_nat (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))) (skipn 19 (t_FGf (g_in g) j)))).
  { pose proof HbRec as HB. rewrite <- (firstn_skipn 19 (t_FGf (g_in g) j)) in HB.
    apply bytes_at_app in HB. destruct HB as (_ & HB).
    rewrite firstn_length, t_FGf_length in HB. cbn [Nat.min] in HB.
    change (Z.of_nat 19) with 19 in HB. apply ba_firstn. exact HB. }
  (* ---- run 0x821d0 .. 0x8229c ---- *)
  set (FA := fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)) in *.
  set (pll := f_pll (t_FG (g_in g) j) (t_g (g_in g) j)) in *.
  set (pb := firstn (Z.to_nat pll) (skipn 19 (t_FGf (g_in g) j))) in *.
  set (W := reac_identity_ingest_W (AC.aspZ regs) (fr + 2688)).
  assert (Hsp : AC.aspZ regs = sp) by exact Haspz.
  assert (HoutW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            outside W x).
  { intros x Hx. subst W. unfold reac_identity_ingest_W, REAC_IDENTITY_INGEST_FRAME.
    cbn [outside]. rewrite Hsp. split; [|split; [|exact I]].
    - destruct Hx as [Hg|[Hc|Hs]].
      + unfold GOT_CELL_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
      + unfold CELL_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
      + intros Hin. apply (app_not_shadow x); [|exact Hs].
        unfold app_mem. right. unfold APPMEM_END, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - destruct Hx as [Hg|[Hc|Hs]].
      + unfold GOT_CELL_K, AC.GT in *. lia.
      + unfold CELL_K, AC.GT in *. lia.
      + intros Hin. apply (app_not_shadow x); [|exact Hs]. apply Happ. lia. }
  apply (F13.sl_run_lib regs (Z_to_bv 64 0x821d0) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x8229c /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\
       getr R0 24 = getr regs 24 /\ getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\
       getr R0 20 = getr regs 20 /\
       getr R0 10 = Z_to_bv 64 (ingest_ret (fr + 2688) FA (fragb fr + 19) pll idb pb) /\
       munch W mem mem' /\ wmono rsegs mem mem' /\ (mem_inv rsegs mem -> mem_inv rsegs mem') /\
       stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
       (ingest_refused (fr + 2688) (fragb fr + 19) pll = false ->
          rw_cells rsegs mem' (fr + 2688) [CB 38 (snd (ING idb FA pb))]))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f16_evt' with (A := A) (fb := fragb fr) (pll := pll) (FA := FA) (id := fr + 2688)
        (lo := AC.aspZ regs - FN_STACK) (vh := fs_have (fst_at (g_in g) j)) (n := n) (S6 := phi + 18)
        (P56 := fr + 2889) (P48 := fr + 2890) (P256 := fr + 256) (X1 := X1) (X2 := X2)
        (K := Z.to_nat (pll + 5)) (rec := t_FGf (g_in g) j) (idb := idb) (pb := pb)
        (b1 := b1) (b2 := b2) (ch := ch) (cl := cl).
      - unfold rg in H9; exact H9.
      - unfold rg in R10; exact R10.
      - unfold rg in R11; exact R11.
      - unfold rg in R12; exact R12.
      - unfold rg in R13; exact R13.
      - rewrite Z2Nat.id by lia. unfold rg in R14; exact R14.
      - unfold rg in R15; exact R15.
      - unfold rg in Hr26; exact Hr26.
      - unfold rg in R5; exact R5.
      - unfold rg in Cs6; exact Cs6.
      - exact HING.
      - rewrite Z2Nat.id by lia. reflexivity.
      - split; [apply (Nat.le_trans 1 (Z.to_nat 1)); [cbn; lia | apply Z2Nat.inj_le; lia]
               | apply (Nat.le_trans _ (Z.to_nat 57)); [apply Z2Nat.inj_le; lia | cbn; lia]].
      - unfold fragb in *; lia.
      - unfold fragb. pose proof Hfrm as Hm32. Z.div_mod_to_equations. lia.
      - unfold fragb in *; lia.
      - exact HaRec.
      - exact HbRec.
      - apply t_FGf_length.
      - replace (Z.to_nat (pll + 5)) with (Z.to_nat (fg_T (t_FG (g_in g) j) (t_g (g_in g) j) - 8))
          by (f_equal; unfold pll, f_pll; lia). exact Hsum0.
      - replace (Z.to_nat (pll + 5)) with (Z.to_nat (fg_T (t_FG (g_in g) j) (t_g (g_in g) j) - 8))
          by (f_equal; unfold pll, f_pll; lia). lia.
      - exact H104.
      - lia.
      - exact H56.
      - exact H48.
      - lia.
      - lia.
      - lia.
      - lia.
      - unfold APPMEM_END in *; lia.
      - reflexivity.
      - reflexivity.
      - exact HX1b.
      - exact HX2b.
      - exact RS1.
      - exact Hck1.
      - exact RS2.
      - exact Hck2.
      - exact RDh.
      - exact RDl.
      - exact HFAeq.
      - exact HFAb.
      - exact H256.
      - exact HU256.
      - lia.
      - exact H144.
      - lia.
      - lia.
      - unfold fragb in *; lia.
      - unfold pll, f_pll in *; lia.
      - unfold AC.GT in *; lia.
      - intros _. split; [pose proof Hfrm as Hm32; Z.div_mod_to_equations; lia | exact Hidcells].
      - unfold pb. rewrite firstn_length, length_skipn, t_FGf_length. lia.
      - intros _ _. exact HbRec19.
      - intros _ _ _. right. unfold fragb in *; lia.
      - fold_sp2 regs. exact Hwstk.
      - fold_sp2 regs. unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - intros _. fold_sp2 regs. unfold REAC_IDENTITY_INGEST_FRAME.
        destruct (Hplace 32 ltac:(unfold FN_STACK; lia)) as [Hd|Hd];
          [left; unfold AC.aspZ in *; lia | right; unfold AC.aspZ in *; lia].
      - intros _ _. fold_sp2 regs. unfold REAC_IDENTITY_INGEST_FRAME, fragb, pll, f_pll in *.
        destruct (Hplace 32 ltac:(unfold FN_STACK; lia)) as [Hd|Hd];
          [left; unfold AC.aspZ in *; lia | right; unfold AC.aspZ in *; lia].
      - exact HAC0.
      - exact HSW0.
      - intros _. exact HaId.
      - intros _ _. apply (addressable_sub mem (fragb fr) 72 19 pll HaRec); unfold pll, f_pll in *; lia.
      - fold_sp2 regs. exact HoutW. }
    { intros ms' Hpost.
      unfold reac_identity_ingest_post in Hpost.
      destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
        & E & MU & WM & MI & ST & _ & HRW).
      replace (ret_pc (Z_to_bv 64 533148)) with (Z_to_bv 64 533148) in E
        by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
      eexists _, (Z_to_bv 64 0x8229c), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [unfold rg in H9; rewrite H9; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [unfold rg in Cs6; rewrite Cs6; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [unfold rg in Hr26; rewrite Hr26; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      match type of ST with context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST end.
      split; [exact MU|].
      split; [exact WM|]. split; [exact MI|].
      split; [exact ST|].
      exact HRW. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E21 & E22 & E23 & E24 & E26 & E18 & E20 & E10 & MU & WM & MI & ST &
       HRW)
      Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (ingest_ret (fr + 2688) FA (fragb fr + 19) pll idb pb))
      by (rewrite Hreg; exact E10).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (Hnr : ingest_refused (fr + 2688) (fragb fr + 19) pll = false).
    { unfold ingest_refused. apply Bool.orb_false_iff. split.
      - apply Z.eqb_neq. unfold AC.GT in *. lia.
      - apply Bool.andb_false_iff. right. apply Z.eqb_neq. unfold fragb, AC.GT in *. lia. }
    assert (Hv0 : 0 <= ingest_ret (fr + 2688) FA (fragb fr + 19) pll idb pb < 2 ^ 63).
    { unfold ingest_ret. rewrite Hnr.
      destruct (ING_ret idb FA pb) as [H0|H1]; rewrite ?H0, ?H1; lia. }
    assert (HOW : forall x, (x < AC.aspZ regs - 32 \/ AC.aspZ regs <= x) ->
              (x < fr + 2688 \/ fr + 2726 <= x) -> outside W x).
    { intros x H1 H2. subst W. unfold reac_identity_ingest_W, REAC_IDENTITY_INGEST_FRAME.
      cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    assert (HOWfr : forall x, fr <= x < fr + 2688 -> outside W x).
    { intros x Hx. apply HOW; [|lia].
      destruct (Hplace 32 ltac:(unfold FN_STACK; lia)) as [Hd|Hd]; unfold AC.aspZ in *; lia. }
    assert (HOWfr2 : forall x, fr + 2726 <= x < fr + FRAME_BYTES -> outside W x).
    { intros x Hx. apply HOW; [|lia].
      destruct (Hplace 32 ltac:(unfold FN_STACK; lia)) as [Hd|Hd]; unfold AC.aspZ in *; lia. }
    (* the spill area at and above A + 16 (v1.9: FRA's window is [A + 16, A + 32)) is above the callee's window
       (sp <= A) and above the frame (fr + 3136 <= A), so the run misses it *)
    assert (HOWA : forall x, A + 16 <= x -> outside W x).
    { intros x Hx. apply HOW; [right; unfold AC.aspZ in *; lia | right; lia]. }
    assert (Hallapp : all_app W).
    { subst W. unfold reac_identity_ingest_W, REAC_IDENTITY_INGEST_FRAME. cbn [all_app].
      split; [|split; [|exact I]].
      - intros a Ha. unfold app_mem. right.
        unfold APPMEM_END, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
      - intros a Ha. apply Happ. lia. }
    assert (Hrtdj : rt_disjoint W).
    { subst W. unfold reac_identity_ingest_W, REAC_IDENTITY_INGEST_FRAME, rt_disjoint,
        RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN, AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *.
      cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
    (* ro_agree of mem': the run writes only its own window and the identity buffer, both above 6283264 *)
    assert (HroM : ro_agree rsegs mem').
    { apply (RoAdapt.ro_agree_munch W mem mem' Hro MU). intros x Hx.
      apply RoAdapt.ro_addr_false_w.
      destruct (Z_lt_le_dec (bv_unsigned x) 6283264) as [Hl|Hl]; [|exact Hl].
      exfalso. apply Hx. apply HOW; left; unfold AC.GT, AC.aspZ, HIGHMEM_BEG, AF.SLOT_STACK in *; lia. }
    assert (Hmeta : meta_kept mem mem') by (apply (munch_meta _ mem mem' MU Hallapp)).
    (* every byte the call wrote is readable afterwards *)
    assert (Hrdpost : forall x, ~ outside W x -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx.
      assert (HI : (AC.aspZ regs - 32 <= x < AC.aspZ regs) \/ (fr + 2688 <= x < fr + 2726)).
      { destruct (Z_lt_le_dec x (AC.aspZ regs - 32)) as [H1|H1];
        destruct (Z_lt_le_dec x (AC.aspZ regs)) as [H2|H2];
        destruct (Z_lt_le_dec x (fr + 2688)) as [H3|H3];
        destruct (Z_lt_le_dec x (fr + 2726)) as [H4|H4];
        try (exfalso; apply Hx; apply HOW; lia); try (left; lia); try (right; lia). }
      destruct HI as [Hst|Hid].
      - destruct ST as (_ & _ & HS). destruct (HS x ltac:(unfold FN_STACK in *; lia)) as (_ & b & Hb).
        exists b. exact Hb.
      - destruct (HRW Hnr) as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
        apply (F13.ba_rd mem' (fr + 2688) (snd (ING idb FA pb)) x Hb).
        rewrite (ING_length idb FA pb LId). unfold ID_SIZE. lia. }
    (* the frame's shadow bytes are shadow addresses, which the (app) write set misses *)
    assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
    { intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
      pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
      replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
      unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
    assert (Hshout : forall x, in_shadow x -> outside W x).
    { intros x Hx. apply HoutW. right. right. exact Hx. }
    assert (Hwmon : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
      by (intros q Hq Hw; exact (WM (Z_to_bv 64 q) Hw)).
    assert (HAHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem' md /\
                     (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)
                                  (hb1 phi (flen g j) ++ g_H g) mem' md q <->
                                AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)
                                  (hb1 phi (flen g j) ++ g_H g) mem md q) /\
                     AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                       = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                     AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                       = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs HFSREC]]]].
      - assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g)
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns. apply MU. rewrite MState.unsigned_lit by exact Hq.
          destruct (Z_lt_le_dec q (AC.aspZ regs - 32)) as [H1|H1];
          destruct (Z_lt_le_dec q (AC.aspZ regs)) as [H2|H2];
          destruct (Z_lt_le_dec q (fr + 2688)) as [H3|H3];
          destruct (Z_lt_le_dec q (fr + 2726)) as [H4|H4];
          try (apply HOW; lia);
          exfalso; apply Hns; right; left;
          first [ specialize (Hreal q ltac:(lia)); unfold APPMEM_END in *; lia
                | unfold APPMEM_END, FN_STACK, AC.aspZ in *; lia ]. }
        pose proof (lw_store (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH Hmc Hwmon) as LWr2.
        pose proof (lws_ah _ _ _ _ _ LWr2) as HAH2.
        pose proof (lws_own _ _ _ _ _ LWr2) as Hown2.
        pose proof (lws_lo _ _ _ _ _ LWr2) as Hstk2.
        pose proof (lws_hi _ _ _ _ _ LWr2) as Hhi2.
        split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2].
      - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
        pose proof (lw_fs_place (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem md FSc HAH HwFSc HFScr) as LWr3.
        pose proof (lwf_gt _ _ _ _ LWr3) as HFSgt.
        pose proof (lwf_end _ _ _ _ LWr3) as HFSend.
        pose proof (lwf_app _ _ _ _ LWr3) as HFSapp.
        pose proof (Hfsmeta FSc HwFSc HFScr) as HFSmeta.
        assert (Hstore : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g)
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FSc <= q < FSc + AC.FS_SIZE) ->
                  ~ (exists b, FSc <= b < FSc + AC.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns Hnfs _Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
          destruct (Z_lt_le_dec q (AC.aspZ regs - 32)) as [H1|H1];
          destruct (Z_lt_le_dec q (AC.aspZ regs)) as [H2|H2];
          destruct (Z_lt_le_dec q (fr + 2688)) as [H3|H3];
          destruct (Z_lt_le_dec q (fr + 2726)) as [H4|H4];
          try (apply HOW; lia);
          first [ exfalso; apply Hnfs; lia
                | exfalso; apply Hns; right; left; unfold APPMEM_END, FN_STACK, AC.aspZ in *; lia ]. }
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  (exists b, mbyte rsegs mem' q = Some b)).
        { intros q Hq Hb.
          destruct (F13.outside_dec W q) as [Ho|Ho].
          - unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - destruct (Hrdpost q Ho) as (b & Hb2). unfold mrd, mbyte, wa in *.
            destruct (mem' (Z_to_bv 64 q)) as [b'|] eqn:Em; [exists b'; reflexivity|].
            exists b. exact Hb2. }
        destruct (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _ W
                    (hb1 phi (flen g j) ++ g_H g) mem mem' md FSc
                    LAWS HAH HwFSc HFScr ltac:(unfold APPMEM_END in *; lia) MU Hwmon Hpres
                    ltac:(intros q Hq; pose proof (Tac_fs.fs_meta_below FSc q Hq) as HB';
                          apply HOW; [left | left]; unfold AC.FS_SIZE, AC.aspZ, AF.SLOT_STACK in *; lia)
                    Hstore)
          as (HAH2 & Hown2 & Hstk2 & Hhi2).
        split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2]. }
    destruct HAHSTK as (HAH' & Hown' & HSTK' & HSTKH').
    assert (HSTKW : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (F13.stk_keep W mem mem' (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | exact MU | exact WM |].
      intros x Hx Ho. exact (Hrdpost x Ho). }
    (* rebuild FRA at mem' (Tac_slot.sl_fr_cl), then move it to regs' / md'; mem_inv of mem' is FRA's own
       mem_inv of mem carried over the ingest run's post (the contract has no mem_inv premise) *)
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs mem' md).
    { apply (Tac_slot.sl_fr_cl B APIf ra empty FF g fr (hb1 phi (flen g j)) regs regs mem mem' md W
               HFRA MU WM HroM Hallapp Hrtdj HAH' HSTK'); try reflexivity.
      - intros x Hx. apply HOW; [left; unfold AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *; lia
                                | left; unfold AC.GT in *; lia].
      - intros x Hx. apply HOWfr. lia.
      - intros A' HA' HA'b x Hx. apply HOWA.
        assert (EA' : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in H9; rewrite <- HA'; exact H9).
          apply (f_equal (bv_unsigned (n := 64))) in E.
          rewrite !MState.unsigned_lit in E by lia. exact E. }
        subst A'. lia.
      - intros x Hx. apply HOWA. lia.
      - intros x Hx. apply Hshout. apply HshIS. exact Hx.
      - intros A' HA' HA'b x Hx. apply HOWA.
        assert (EA' : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in H9; rewrite <- HA'; exact H9).
          apply (f_equal (bv_unsigned (n := 64))) in E.
          rewrite !MState.unsigned_lit in E by lia. exact E. }
        subst A'. lia.
      - exact HSTKW.
      - intros HR. eapply Tac_slot.fsrec_munch_lo with (W := W); [exact HR | exact HAH | exact MU | |].
        + intros x Hx. apply HOW; left; unfold AC.GT, AC.aspZ, HIGHMEM_BEG, AF.SLOT_STACK in *; lia.
        + intros x Hxa Hxf Hxs. apply HOW; [left; unfold AF.SLOT_STACK, AC.aspZ in *; lia |].
          destruct (Z_lt_le_dec x (fr + 2688)) as [Hl|Hl]; [left; lia | right; lia]. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md').
    { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs' mem' md md' HFRA');
        [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
    (* ENT: the ingest call wrote only its own 32 stack bytes, inside the slot window below the entry sp, and
       the 38-byte identity buffer inside the frame, so no byte the entry relation speaks of changed; then the
       model step of sl_run_lib. *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
              outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/
              (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx.
      destruct (Z_lt_le_dec x (fr + 2688)) as [H3|H3]; [|destruct (Z_lt_le_dec x (fr + 2726)) as [H4|H4]].
      - destruct (Z_lt_le_dec x (AC.aspZ regs - 32)) as [H1|H1].
        + left. apply HOW; [left; lia | left; lia].
        + destruct (Z_lt_le_dec x (AC.aspZ regs)) as [H2|H2].
          * right; left. unfold AC.aspZ in *. lia.
          * left. apply HOW; [right; lia | left; lia].
      - right; right; left. lia.
      - destruct (Z_lt_le_dec x (AC.aspZ regs - 32)) as [H1|H1].
        + left. apply HOW; [left; lia | right; lia].
        + destruct (Z_lt_le_dec x (AC.aspZ regs)) as [H2|H2].
          * right; left. unfold AC.aspZ in *. lia.
          * left. apply HOW; [right; lia | right; lia]. }
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { apply (Tac_slot.ent_store B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md W HENT HFRA MU HWcases
               HSTK' HSTKH').
      intros a Hia Ho. exact (proj2 (Hown' a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md')
      by exact (Tac_slot.ent_mat APIf g (hb1 phi (flen g j)) mem' md md' HENT' Hmat).
    (* ---- the exit cut at 0x8229c ---- *)
    assert (Hin : In (phi, flen g j) (hb1 phi (flen g j) ++ g_H g))
      by (unfold hb1; cbn; left; reflexivity).
    pose proof (lw_blocks (APIf rc) _ mem md phi (flen g j) HAH Hin) as LWr4.
    pose proof (lwb_align _ _ _ _ _ _ LWr4) as Hal16.
    pose proof (lwb_low _ _ _ _ _ _ LWr4) as Hph4096.
    pose proof (lwb_end _ _ _ _ _ _ LWr4) as Hbelow.
    pose proof (lwb_byte_not_fs _ _ _ _ _ _ LWr4) as Hblkb.
    (* Hphi0 / Hphi50 / Hphiapp are already in context (taken from HRI with the FIRST-state facts above) *)
    pose proof HRI as HRI2.
    destruct HRI2 as (_ & _ & Hflen50 & Htk & _ & _).
    (* a live block of the heap list ends below stklo (below the callee's window) and is off the side stack,
       so it misses the identity buffer inside the frame too *)
    assert (Hblkout : forall q n x, In (q, n) (hb1 phi (flen g j) ++ g_H g) -> q <= x < q + n -> outside W x).
    { intros q nq x Hinq Hx.
      pose proof (lw_blocks (APIf rc) _ mem md q nq HAH Hinq) as LWr5.
      pose proof (lwb_end _ _ _ _ _ _ LWr5) as Hend.
      pose proof (lwb_byte_not_fs _ _ _ _ _ _ LWr5) as Hb.
      apply HOW.
      - left. unfold AF.SLOT_STACK, AC.aspZ in *. lia.
      - destruct (Z_lt_le_dec x (fr + 2688)) as [Hl|Hl]; [left; lia|].
        destruct (Z_lt_le_dec x (fr + 2726)) as [Hh|Hh]; [|right; lia].
        exfalso. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
        + pose proof (Hreal x ltac:(lia)) as (Hlo2 & _). lia.
        + exact (Hb x ltac:(lia) (Hfs x ltac:(lia))). }
    assert (HOWphi : forall x, phi <= x < phi + flen g j -> outside W x)
      by (intros x Hx; exact (Hblkout phi (flen g j) x Hin Hx)).
    assert (Hq64 : forall a v, (forall x, a <= x < a + 8 -> outside W x) -> q64 mem a v -> q64 mem' a v).
    { intros a v Hout Hq. unfold q64 in *.
      eapply fl_bytes; [exact Hq | exact MU | rewrite length_le8; exact Hout]. }
    assert (Hu16 : forall a v, (forall x, a <= x < a + 2 -> outside W x) -> u16 mem a v -> u16 mem' a v).
    { intros a v Hout Hq. unfold u16 in *.
      eapply fl_bytes; [exact Hq | exact MU | rewrite length_le2; exact Hout]. }
    assert (Hb8 : forall a v, (forall x, a <= x < a + 1 -> outside W x) -> b8 mem a v -> b8 mem' a v).
    { intros a v Hout Hq. unfold b8 in *.
      eapply fl_bytes; [exact Hq | exact MU | cbn [length]; exact Hout]. }
    (* push 15: F17CARRY carries rec_inv as rec_inv0 (under 50 <= flen) and rec_parse (on the 8819 arm) *)
    assert (HRI' : rec_inv0 g j fr phi A mem').
    { destruct HRI as (P0 & P50 & Pfl & Ptk & Papp & P192 & Pblk & P34 & P248 & P280).
      unfold rec_inv0.
      split; [exact P0|]. split; [exact P50|]. split; [exact Pfl|]. split; [exact Ptk|].
      split; [exact Papp|].
      split; [apply (Hq64 (A + 200)); [intros x Hx; apply HOWA; lia | exact P192]|].
      split.
      { eapply fl_bytes; [exact Pblk | exact MU |]. intros x Hx. apply HOWphi.
        pose proof (bsl_len_le (t_g (g_in g) j) 18 32) as BL. unfold t_blk in Hx.
        change (Z.to_nat 32) with 32%nat in BL. lia. }
      split.
      { eapply fl_bytes; [exact P34 | exact MU |]. intros x Hx. apply HOWphi.
        pose proof (bsl_len_le (t_g (g_in g) j) 34 6) as BL.
        change (Z.to_nat 6) with 6%nat in BL. lia. }
      split; [apply (Hq64 (A + 248)); [intros x Hx; apply HOWA; lia | exact P248]|].
      apply (Hq64 (A + 280)); [intros x Hx; apply HOWA; lia | exact P280]. }
    assert (HRP' : rec_parse g j fr phi mem -> rec_parse g j fr phi mem').
    { intros (field16 & v14 & v15 & v16 & v17 & Pf16 & Pb14 & Pb15 & Pb16 & Pb17 &
        Rv14 & Rv15 & Rv16 & Rv17 & Ps14 & Ps15 & Ps16 & Ps17 & Peq1 & Peq2).
      exists field16, v14, v15, v16, v17.
      split; [apply (Hu16 (fr + 176 + 20)); [intros x Hx; apply HOWfr; lia | exact Pf16]|].
      split; [apply (Hb8 (phi + 14)); [intros x Hx; apply HOWphi; lia | exact Pb14]|].
      split; [apply (Hb8 (phi + 15)); [intros x Hx; apply HOWphi; lia | exact Pb15]|].
      split; [apply (Hb8 (phi + 16)); [intros x Hx; apply HOWphi; lia | exact Pb16]|].
      split; [apply (Hb8 (phi + 17)); [intros x Hx; apply HOWphi; lia | exact Pb17]|].
      split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
      split; [apply (Hb8 (Z.shiftr (phi + 14) 3 + ASAN_K));
              [intros x Hx; apply Hshout; replace x with (Z.shiftr (phi + 14) 3 + ASAN_K) by lia;
               rewrite Z.shiftr_div_pow2 by lia;
               exact (shadow_of_app (phi + 14) (Hphiapp (phi + 14) ltac:(lia))) | exact Ps14]|].
      split; [apply (Hb8 (Z.shiftr (phi + 15) 3 + ASAN_K));
              [intros x Hx; apply Hshout; replace x with (Z.shiftr (phi + 15) 3 + ASAN_K) by lia;
               rewrite Z.shiftr_div_pow2 by lia;
               exact (shadow_of_app (phi + 15) (Hphiapp (phi + 15) ltac:(lia))) | exact Ps15]|].
      split; [apply (Hb8 (Z.shiftr (phi + 16) 3 + ASAN_K));
              [intros x Hx; apply Hshout; replace x with (Z.shiftr (phi + 16) 3 + ASAN_K) by lia;
               rewrite Z.shiftr_div_pow2 by lia;
               exact (shadow_of_app (phi + 16) (Hphiapp (phi + 16) ltac:(lia))) | exact Ps16]|].
      split; [apply (Hb8 (Z.shiftr (phi + 17) 3 + ASAN_K));
              [intros x Hx; apply Hshout; replace x with (Z.shiftr (phi + 17) 3 + ASAN_K) by lia;
               rewrite Z.shiftr_div_pow2 by lia;
               exact (shadow_of_app (phi + 17) (Hphiapp (phi + 17) ltac:(lia))) | exact Ps17]|].
      split; [exact Peq1 | exact Peq2]. }
    pose proof (F13.t_phi_len g j) as Hpl.
    assert (HspK : forall off v, 24 <= off -> off + 8 <= 416 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Ho1 Ho2 Hs. eapply F13.spill_keep;
        [exact Hs | exact H9 | lia | lia | lia | lia | exact Fr9 | exact MU |].
      intros x Hx. apply HOWA. lia. }
    (* the official F17 entry (SlotInv.Inv_A8229c_at, push 6c8) at turn j *)
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [rewrite Easz; exact HFRA''|].
    split; [rewrite Easz; exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      eapply addressable_kept; [exact Hphiad | exact Hmeta]. }
    split.
    { destruct HFLSI as ((HPRO & F128 & Fstk & F144 & Fid17) & F216 & F224 & F248 & (Fin1 & Fin2 & Fin3) &
        HFLC).
      split.
      { split.
        { eapply F13.pro_keep; [exact HPRO | exact H9 | lia | lia | exact Fr9 | exact MU | exact Hmeta | |].
          - intros x Hx. apply HOWA. lia.
          - intros Hgn0 x Hx. apply (Hblkout (g_p g) (g_n g) x); [|exact Hx].
            apply in_or_app. right. apply Fin1. exact Hgn0. }
        split; [apply HspK; [lia | lia | exact F128]|].
        split.
        { apply (F13.stk_keep W mem mem' fr (fr + FRAME_BYTES)); [exact Fstk | exact MU | exact WM |].
          intros x Hx Ho. exact (Hrdpost x Ho). }
        split; [apply HspK; [lia | lia | exact F144]|].
        eapply addressable_kept; [exact Fid17 | exact Hmeta]. }
      split; [apply HspK; [lia | lia | exact F216]|].
      split; [apply HspK; [lia | lia | exact F224]|].
      split; [apply HspK; [lia | lia | exact F248]|].
      split.
      { split; [exact Fin1|].
        split; [eapply addressable_kept; [exact Fin2 | exact Hmeta]|].
        eapply fl_bytes; [exact Fin3 | exact MU |].
        intros x Hx. apply (Hblkout (g_p g) (g_n g) x); [|unfold g_n, nlen; lia].
        apply in_or_app. right. apply Fin1. unfold g_n, nlen in *. lia. }
      (* push 14D / 14E: FLC *)
      eapply F13.flc_keep; [exact HFLC | exact H9 | lia | lia | exact Fr9 | exact MU | exact Hmeta |].
      intros x Hx. apply HOWA. lia. }
    split.
    { destruct HLK as (Hj' & Hs5j & HOURb). split; [exact Hj'|]. split.
      - unfold rg in *. rewrite Fr21. exact Hs5j.
      - unfold OURb in *. eapply fl_bytes; [exact HOURb | exact MU |].
        rewrite OUR_length. intros x Hx. apply HOWfr. lia. }
    split; [unfold rg in *; rewrite Fr23; exact Cs7|].
    split; [unfold rg in *; rewrite Fr22, Ebig; exact Cs6|].
    split.
    { intros _. split.
      - destruct HHB as (_ & Hphiad).
        assert (Had : addressable mem' phi (AC.a_size (flen g j)))
          by (eapply addressable_kept; [exact Hphiad | exact Hmeta]).
        pose proof (addressable_sub mem' phi (AC.a_size (flen g j)) 0 50 Had ltac:(lia) ltac:(lia)
                      ltac:(unfold AC.a_size; lia)) as Hsub.
        replace (phi + 0) with phi in Hsub by lia. exact Hsub.
      - exists (firstn 38 rb). split; [|rewrite firstn_length; lia].
        eapply fl_bytes; [apply ba_firstn; exact Hrb | exact MU |].
        rewrite firstn_length. intros x Hx. apply HOWphi. lia. }
    split.
    { exists (ingest_ret (fr + 2688) FA (fragb fr + 19) pll idb pb).
      split; [unfold rg; exact Fr10 | exact Hv0]. }
    split.
    { exists A.
      split; [unfold rg; rewrite Fr9; unfold rg in H9; exact H9|].
      split; [apply (Hq64 (A + 232)); [intros x Hx; apply HOWA; lia | exact H232]|].
      split; [apply (Hq64 (A + 200)); [intros x Hx; apply HOWA; lia | exact H192]|].
      split; [apply (Hq64 (A + 136)); [intros x Hx; apply HOWA; lia | exact H136]|].
      split; [apply (Hq64 (A + 120)); [intros x Hx; apply HOWA; lia | exact H120]|].
      split; [apply (Hq64 (A + 176)); [intros x Hx; apply HOWA; lia | exact H176]|].
      split; [intros a Ha; unfold APPMEM_END, HIGHMEM_BEG, AF.SLOT_STACK in *; lia|].
      split.
      { destruct HW240 as (w240 & H240 & Hwb & Hwt & Hwf). exists w240.
        split; [apply (Hq64 (A + 240)); [intros x Hx; apply HOWA; lia | exact H240]|].
        split; [exact Hwb|]. split; [exact Hwt | exact Hwf]. }
      split; [unfold rg in *; rewrite Fr24; exact Cs8|].
      split.
      { intros _. split; [exact HRI'|].
        split; [rewrite HaspEq; left; unfold BCMP_WRAP_K, AF.SLOT_STACK, AC.aspZ in *; lia|].
        left; unfold AC.aspZ in *; lia. }
      intros Ht. destruct (Hcmp Ht) as (HRP & (ls & rs & HL56 & Hbls & Lls & Hbrs & Lrs & Hmm1 & Had186) &
        (ls2 & rs2 & HL48 & Hbls2 & Lls2 & Hbrs2 & Lrs2 & Hmm2 & Had180)).
      split; [exact (HRP' HRP)|].
      split.
      { exists (firstn 6 ls), (firstn 6 rs).
        split; [apply (Hq64 (A + 72)); [intros x Hx; apply HOWA; lia | exact HL56]|].
        split; [eapply fl_bytes; [apply ba_firstn; exact Hbls | exact MU |
                  rewrite firstn_length; intros x Hx; apply HOWfr; lia]|].
        split; [rewrite firstn_length; lia|].
        split; [eapply fl_bytes; [apply ba_firstn; exact Hbrs | exact MU |
                  rewrite firstn_length; intros x Hx; apply HOWphi; lia]|].
        split; [rewrite firstn_length; lia|].
        split; [rewrite memcmp_firstn by lia; exact Hmm1|].
        eapply addressable_kept; [exact Had186 | exact Hmeta]. }
      { exists (firstn 6 ls2), (firstn 6 rs2).
        split; [apply (Hq64 (A + 64)); [intros x Hx; apply HOWA; lia | exact HL48]|].
        split; [eapply fl_bytes; [apply ba_firstn; exact Hbls2 | exact MU |
                  rewrite firstn_length; intros x Hx; apply HOWfr; lia]|].
        split; [rewrite firstn_length; lia|].
        split; [eapply fl_bytes; [apply ba_firstn; exact Hbrs2 | exact MU |
                  rewrite firstn_length; intros x Hx; apply HOWphi; lia]|].
        split; [rewrite firstn_length; lia|].
        split; [rewrite memcmp_firstn by lia; exact Hmm2|].
        eapply addressable_kept; [exact Had180 | exact Hmeta]. } }
    split; [unfold rg in *; rewrite Fr18; exact Cs18|].
    split.
    { intros _. split.
      - eapply fl_bytes; [exact Hgb | exact MU |]. rewrite F13.t_g_length. intros x Hx. apply HOWphi. lia.
      - split; [|exact Hpl].
        eapply fl_bytes; [exact Hpb | exact MU |]. intros x Hx. apply HOWphi. lia. }
    split; [apply HspK; [lia | lia | exact H152]|].
    destruct HRI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P280').
    split; [unfold spill; exists A; split; [unfold rg; rewrite Fr9; unfold rg in H9; exact H9 | exact P280']|].
    (* push 12: IFS3 at 0x8229c. The ingest wrote snd (ING (ID1 g j) FA pb) at fr + 2688, the identity of turn
       S j; the fragment record (t_FG (S j), IFS2's) and the four spills are outside the call's write set. *)
    (* push 13A: s4 = 1 - sum_ok (F17CARRY's), which the ingest call keeps (callee-saved) *)
    split; [|unfold rg; rewrite Fr20; unfold rg in Cs20; exact Cs20].
    unfold IFS3. split; [|split].
    + unfold IDj, IDb, IDBe. rewrite (t_ID_S_ingest g j Hrf).
      destruct (HRW Hnr) as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      split; [exact Hb | apply RcIdentLib.ING_id_ok; [exact LId | exact HidOK]].
    + unfold FGj, FGb in *. destruct HFG1 as (HG1 & HGok). split; [|exact HGok].
      eapply F13.fgbe_keep; [exact HG1 | apply F13.t_FG_length | exact MU |].
      intros x Hx. apply HOWfr2. lia.
    + eapply F13.fsj_keep; [exact HFS1 | exact H9 | lia | lia | exact Fr9 | exact MU | exact Hmeta | |].
      * intros x Hx. apply HOWA. lia.
      * intros x Hx. apply HOWfr2. lia.
Qed.

End S.
