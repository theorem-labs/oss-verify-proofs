(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSmB CmpHmKit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsGm BzCSmF1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCFactsSmB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_app2 : forall segs m A pre post,
  rw_cells segs m A (pre ++ post) <-> rw_cells segs m A pre /\ rw_cells segs m (A + Z.of_nat (cells_size pre))%Z post.
Proof.
  intros segs m A pre post. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    rewrite (cells_bytes_length pre W1) in B2.
    rewrite Nat2Z.inj_add in WR. apply wr_at_app in WR; [|lia|lia]. destruct WR as [R1 R2].
    split; [ split; [ split; [exact W1 | exact B1] | exact R1 ] | split; [ split; [exact W2 | exact B2] | exact R2 ] ].
  - intros [[[W1 B1] R1] [[W2 B2] R2]].
    rewrite (cells_bytes_length pre W1). rewrite Nat2Z.inj_add.
    split; [ split; [ split; [exact W1 | exact W2] | split; [exact B1 | exact B2] ] |].
    apply wr_at_app; [lia|lia|]. split; [exact R1 | exact R2].
Qed.

(* [comment removed for export] *)
Fixpoint ex_words (n : nat) (k : list word -> Prop) : Prop :=
  match n with O => k [] | S n' => exists w : word, ex_words n' (fun ws => k (w :: ws)) end.
Lemma ex_words_mono : forall n (k k' : list word -> Prop), (forall ws, k ws -> k' ws) -> ex_words n k -> ex_words n k'.
Proof.
  induction n as [|n IH]; intros k k' Hk H; cbn in *; [apply Hk; exact H|].
  destruct H as [w H]. exists w. eapply IH; [| exact H]. intros ws Hws. apply Hk. exact Hws.
Qed.
(* [comment removed for export] *)
Lemma u8arr_C8s : forall n segs m A bs, u8arr segs m A bs -> length bs = (8 * n)%nat ->
  ex_words n (fun ws => rw_cells segs m A (map C8 ws)).
Proof.
  induction n as [|n IH]; intros segs m A bs H L.
  - cbn. destruct bs; [| cbn in L; lia]. destruct H as [Hb Hw]. split; [split; [exact I| exact Hb]| exact Hw].
  - rewrite <- (firstn_skipn 8 bs) in H. apply (proj1 (u8arr_app segs m A _ _)) in H. destruct H as [H1 H2].
    rewrite length_firstn in H2. replace (Z.of_nat (Nat.min 8 (length bs))) with 8%Z in H2 by lia.
    pose proof (rw_cells_of_u8arr segs m A _ H1) as C1. rewrite length_firstn in C1.
    replace (Nat.min 8 (length bs)) with 8%nat in C1 by lia.
    apply (rw_cells_CB8_C8 segs m A [] _ []) in C1. cbn [app] in C1.
    cbn. eexists. eapply ex_words_mono; [| eapply IH; [exact H2| rewrite length_skipn; lia]].
    intros ws Hws. cbn [map]. change (C8 ?w :: map C8 ws) with ([C8 w] ++ map C8 ws).
    apply (proj2 (rw_cells_app2 segs m A _ _)). split; [exact C1| exact Hws].
Qed.
(* [comment removed for export] *)
Lemma u8arr_of_cells : forall segs m A cs, rw_cells segs m A cs ->
  u8arr segs m A (cells_bytes cs) /\ length (cells_bytes cs) = cells_size cs.
Proof.
  intros segs m A cs H. pose proof (rw_cells_merge segs m A [] cs [] ltac:(rewrite app_nil_r; exact H)) as M. cbn [app] in M.
  split; [exact (u8arr_of_rw_cells segs m A _ _ M)|]. apply cells_bytes_length. exact (proj1 (proj1 H)).
Qed.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition sm_slots3 (cx : cctx) (e : est) (usp : Z) (sv w24 w56 : word) (iter : Z) : list cell :=
  let E := c_E cx in let A1 := c_A1 cx in let A := sm_alpha e in let nG := smA_ng e in
  [C8 (Z_to_bv 64 37450); C8 (Z_to_bv 64 (E + 128)); C8 w24; C8 (Z_to_bv 64 A); C8 sv; C8 (Z_to_bv 64 (E + 38998)); C8 w56;
   C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (nG - 1)); C8 (Z_to_bv 64 (4 * A)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG));
   C8 (Z_to_bv 64 nG); C8 (Z_to_bv 64 iter); C8 (Z_to_bv 64 (A1 + 2)); C8 (Z_to_bv 64 (E + 51648 + 16 * A)); C8 (Z_to_bv 64 (E + 37708));
   C8 (Z_to_bv 64 (E + 51640)); C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (usp + 616 + 4 * nG));
   C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (E + 45448))].
Lemma smA_slots3_eq : forall cx e usp sv w24 w56, smA_slots3 cx e usp sv w24 w56 = sm_slots3 cx e usp sv w24 w56 0.
Proof. reflexivity. Qed.
Lemma smB_slots3_eq : forall cx e usp sv w24 w56, smB_slots3 cx e usp sv w24 w56 = sm_slots3 cx e usp sv w24 w56 4.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zx16_lit : forall x, 0 <= x < 65536 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
End ACeilS2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zb8_store2 ARR i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le2 ?w)) _) =>
    lazymatch type of ARR with u8arr ?segs m ?A (zb8 ?a ?n) =>
      let H := fresh "ARRw" in
      pose proof (zb8_write2 segs m A a n i w ARR ltac:(lia) ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
    end end.
Section ACeilS3. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma wr16_mod : forall a o v, wr16 a o (v mod 65536) = wr16 a o v.
Proof.
  intros a o v. unfold wr16. f_equal; [f_equal|].
  - change 65536 with (256 * 256). rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add by lia. apply Z.mod_mod. lia.
  - symmetry. change 65536 with (256 * 256). rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm 256), Z.div_add by lia. rewrite (Z.div_small (v mod 256) 256) by (apply Z.mod_pos_bound; lia).
    rewrite Z.add_0_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rd16_wr16_same_mod : forall a o v, rd16 (wr16 a o v) o = v mod 65536.
Proof. intros a o v. rewrite <- (wr16_mod a o v). apply rd16_wr16_same. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition COSTREL (cb c : zarr) (n : Z) : Prop := zbok cb /\ forall t, 0 <= t < n -> rd16 cb (2 * t) = zget c t.
Lemma COSTREL_zero : forall c0 n, n <= 6 -> COSTREL znew (zero6 c0) n.
Proof.
  intros c0 n Hn. split; [apply zbok_znew|]. intros t Ht. unfold zero6. rewrite zfill0_get.
  replace ((0 <=? t) && (t <? 0 + Z.of_nat 6))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
  unfold rd16. rewrite !zget_znew. reflexivity.
Qed.
Lemma COSTREL_set : forall cb c n t v, COSTREL cb c n -> 0 <= t < n ->
  COSTREL (wr16 cb (2 * t) v) (zset c t (v mod 65536)) n.
Proof.
  intros cb c n t v [OK R] Ht. split; [apply zbok_wr16; exact OK|]. intros t' Ht'.
  rewrite zget_zset. destruct (Z.eqb_spec t' t) as [->|NE].
  - apply rd16_wr16_same_mod.
  - rewrite rd16_wr16_other by lia. apply R. exact Ht'.
Qed.
(* [comment removed for export] *)
Lemma cost_zero_cells : forall segs m A,
  rw_cells segs m A [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] -> u8arr segs m A (zb8 znew 12).
Proof.
  intros segs m A H. pose proof (rw_cells_merge segs m A [] _ [] ltac:(rewrite app_nil_r; exact H)) as M. cbn [app cells_size csize Nat.add] in M.
  apply (zb8_init segs m A 12 _ M ltac:(lia)).
  intros k b Hk.
  assert (cells_bytes [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] = repeat (Z_to_bv 8 0) 12) as E by (vm_compute; reflexivity).
  rewrite E in Hk. apply nth_error_In in Hk. apply repeat_spec in Hk. exact Hk.
Qed.
(* [comment removed for export] *)
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  assert (R : (0 <= bytes_le_to_Z bs < 2^32)%Z).
  { rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as X.
    rewrite length_map, L in X. change (256 ^ Z.of_nat 4)%Z with (2^32)%Z in X. lia. }
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. rewrite Z.mod_small by lia.
  rewrite <- L. apply MuslStr.Z_to_le_bytes_to_Z.
Qed.
(* [comment removed for export] *)
Lemma rw_cells_CB4_C4 : forall segs m A pre bs post,
  rw_cells segs m A (pre ++ CB 4 bs :: post) -> rw_cells segs m A (pre ++ C4 (le_bytes_to_word bs) :: post).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 [W2 W3]]. cbn in W2.
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le4_of_bytes by exact W2. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.
(* [comment removed for export] *)
Lemma cost_cells_of_junk : forall segs m A (bs : list byte), u8arr segs m A bs -> length bs = 12%nat ->
  exists w1 w2, rw_cells segs m A [C8 w1; C4 w2].
Proof.
  intros segs m A bs U L. pose proof (rw_cells_of_u8arr segs m A bs U) as C. rewrite L in C.
  pose proof (rw_cells_split_CB segs m A [] 12 bs [] [8;4]%nat C eq_refl) as S. cbn [mk_CB_cells app] in S.
  apply (rw_cells_CB8_C8 segs m A []) in S. cbn [app] in S.
  lazymatch type of S with rw_cells _ _ _ (?c1 :: _) => apply (rw_cells_CB4_C4 segs m A [c1]) in S; cbn [app] in S end.
  lazymatch type of S with rw_cells _ _ _ [C8 ?w1; C4 ?w2] => exists w1, w2; exact S end.
Qed.

(* [comment removed for export] *)
Lemma swrap16_cases : forall c, 0 <= c < 65536 -> bv_swrap 16 c = c \/ bv_swrap 16 c = c - 65536.
Proof.
  intros c Hc. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 16) with 32768 by reflexivity. replace (bv_modulus 16) with 65536 by reflexivity.
  destruct (Z.lt_ge_cases c 32768) as [L|L].
  - left. rewrite Z.mod_small by lia. lia.
  - right. replace (c + 32768) with ((c - 32768) + 1 * 65536) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sx16_plus_mod : forall c l, 0 <= c < 65536 -> 0 <= l ->
  (bv_unsigned (sx16 (Z_to_bv 64 c)) + l) mod 65536 = (c + l) mod 65536.
Proof.
  intros c l Hc Hl. unfold sx16. rewrite (unsigned_lit c) by lia. rewrite unsigned_lit_wrap.
  change (2^64) with 18446744073709551616.
  destruct (swrap16_cases c Hc) as [E|E]; rewrite E.
  - rewrite (Z.mod_small c) by lia. reflexivity.
  - replace ((c - 65536) mod 18446744073709551616) with (c - 65536 + 18446744073709551616) by (Z.div_mod_to_equations; lia).
    replace (c - 65536 + 18446744073709551616 + l) with (c + l + 281474976710655 * 65536) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma cost_upd_mod : forall c l, 0 <= c < 65536 -> 0 <= l ->
  (bv_unsigned (Z_to_bv 64 (bv_unsigned (sx16 (Z_to_bv 64 c)) + l))) mod 65536 = (c + l) mod 65536.
Proof.
  intros c l Hc Hl. rewrite unsigned_lit_wrap. change (2^64) with (65536 * 281474976710656).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 65536), Z.mod_add by lia. rewrite Z.mod_mod by lia.
  apply sx16_plus_mod; assumption.
Qed.

(* [comment removed for export] *)
Lemma seqz_mod64 : forall d, - 9223372036854775808 <= d < 9223372036854775808 ->
  (d mod 18446744073709551616 <? 1) = (d =? 0).
Proof.
  intros d Hd. destruct (Z.eqb_spec d 0) as [->|NE].
  - reflexivity.
  - apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma COSTREL_fast6 : forall c S0 S1 S2, 0 <= S0 -> 0 <= S1 -> 0 <= S2 ->
  COSTREL (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 znew 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536))
          (zset (zset (zset (zset (zset (zset (zero6 c) 0 (Z.land (S0 mod 4294967296) 65535)) 1 (Z.shiftr (S0 mod 4294967296) 16))
                2 (Z.land (S1 mod 4294967296) 65535)) 3 (Z.shiftr (S1 mod 4294967296) 16))
                4 (Z.land (S2 mod 4294967296) 65535)) 5 (Z.shiftr (S2 mod 4294967296) 16)) 6.
Proof.
  intros c S0 S1 S2 H0 H1 H2. split. { repeat apply zbok_wr16. apply zbok_znew. }
  intros t Ht. rewrite !fast_half_lo, !fast_half_hi by lia.
  assert (T : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5) by lia.
  destruct T as [->|[->|[->|[->|[->| ->]]]]]; cbn [Z.mul];
    repeat (rewrite rd16_wr16_other by lia); rewrite rd16_wr16_same_mod;
    repeat (rewrite zget_zset_other by lia); rewrite zget_zset_same; rewrite ?Z.mod_mod by lia; reflexivity.
Qed.

Lemma COSTREL_le : forall cb c n n', COSTREL cb c n -> n' <= n -> COSTREL cb c n'.
Proof. intros cb c n n' [OK R] H. split; [exact OK|]. intros t Ht. apply R. lia. Qed.

End ACeilS3.
